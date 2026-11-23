import DynExpr.NodeUtils.Nodes

namespace DynExpr.NodeUtils

/-- Finite initialized active node structure with enough traversal fuel,
independently of constant collection (src/Node.jl:75-91, src/NodeUtils.jl:99-116). -/
def Traversable (g : Graph T) : Nat → Addr → Prop
  | 0, _ => False
  | fuel + 1, root => ∃ c, g.cells root = some c ∧ c.children.length = c.degree ∧
      (c.degree = 0 → c.constant = true → ∃ v, c.val = some v) ∧
      ∀ child ∈ c.children, Traversable g fuel child

/-- Every selected ref points to an initialized scalar value. -/
def ValidRefs (g : Graph T) (refs : List Addr) : Prop :=
  ∀ a ∈ refs, ∃ c v, g.cells a = some c ∧ c.val = some v

private theorem validRefs_append {g : Graph T} {as bs : List Addr}
    (ha : ValidRefs g as) (hb : ValidRefs g bs) : ValidRefs g (as ++ bs) := by
  intro a h
  rcases List.mem_append.mp h with h | h
  · exact ha a h
  · exact hb a h

private theorem foldlM_exists (f : S → A → Jl S) (P : S → Prop) (xs : List A)
    (step : ∀ a ∈ xs, ∀ s, P s → ∃ s', f s a = .ok s' ∧ P s') :
    ∀ s, P s → ∃ s', xs.foldlM f s = .ok s' ∧ P s' := by
  induction xs with
  | nil => intro s hs; exact ⟨s,rfl,hs⟩
  | cons a as ih =>
      intro s hs
      obtain ⟨mid,hm,hpm⟩ := step a (by simp) s hs
      obtain ⟨last,hl,hpl⟩ := ih (fun b hb => step b (by simp [hb])) mid hpm
      exact ⟨last,by simp only [List.foldlM_cons, hm, bindOk]; exact hl,hpl⟩

/-- Totality of the sharing-aware and plain constant-ref traversal on initialized
finite structures (src/NodeUtils.jl:102-104, src/base.jl:127-155). -/
theorem constantRefs_success (g : Graph T) (sharing : Bool) (fuel : Nat) :
    ∀ root seen, Traversable g fuel root →
      ∃ refs visited, constantRefs g sharing fuel root seen = .ok (refs,visited) ∧ ValidRefs g refs := by
  induction fuel with
  | zero => intro root seen ht; exact False.elim ht
  | succ fuel ih =>
      intro root seen ht
      obtain ⟨c,hc,_hlen,hval,hkids⟩ := ht
      by_cases hs : sharing = true ∧ root ∈ seen
      · exact ⟨[],seen,by simp [constantRefs,hs,Pure.pure,Except.pure],by simp [ValidRefs]⟩
      · let visited := if sharing then root :: seen else seen
        have hr : g.read root = .ok c := by simp [Heap.read,hc]
        by_cases hd : c.degree = 0
        · by_cases hv : c.constant = true
          · obtain ⟨v,hv'⟩ := hval hd hv
            refine ⟨[root],visited,?_,?_⟩
            · simp [constantRefs,hs,hr,bindOk,hd,hv,visited,Pure.pure,Except.pure]
            · intro a ha; simp only [List.mem_singleton] at ha; subst a
              exact ⟨c,v,hc,hv'⟩
          · refine ⟨[],visited,?_,by simp [ValidRefs]⟩
            simp [constantRefs,hs,hr,bindOk,hd,hv,visited,Pure.pure,Except.pure]
        · let step := fun (state : List Addr × List Addr) child => do
            let (refs,next) ← constantRefs g sharing fuel child state.2
            pure (state.1 ++ refs,next)
          have hstep : ∀ child ∈ c.children, ∀ state, ValidRefs g state.1 →
              ∃ next, step state child = .ok next ∧ ValidRefs g next.1 := by
            intro child hchild state hout
            obtain ⟨refs,next,hr,hrefs⟩ := ih child state.2 (hkids child hchild)
            exact ⟨(state.1 ++ refs,next),by simp [step,hr,bindOk,Pure.pure,Except.pure],
              validRefs_append hout hrefs⟩
          obtain ⟨last,hl,hvalid⟩ := foldlM_exists step (fun s => ValidRefs g s.1)
            c.children hstep ([],visited) (by simp [ValidRefs])
          refine ⟨last.1,last.2,?_,hvalid⟩
          simpa [constantRefs,hs,hr,bindOk,hd,step,visited] using hl

/-- Ref reads are total whenever every input ref has an initialized value. -/
theorem readValues_success (g : Graph T) (refs : List Addr) (hr : ValidRefs g refs) :
    ∃ values, readValues g refs = .ok values := by
  induction refs with
  | nil => exact ⟨[],rfl⟩
  | cons a refs ih =>
      obtain ⟨c,v,hc,hv⟩ := hr a (by simp)
      obtain ⟨values,hvalues⟩ := ih (fun b hb => hr b (by simp [hb]))
      exact ⟨v :: values,by simp [readValues,Heap.read,hc,hv,hvalues,bindOk,mapOk]⟩

/-- Numeric scalar getter success for all initialized finite input graphs.
Sharing is an arbitrary option; NoAlias is the plain Node input contract. -/
def ScalarGetterSuccess : Prop := ∀ (T : Type) (g : Graph T) sharing fuel root,
  Traversable g fuel root → (sharing = false → Graph.NoAlias g root) →
    ∃ values refs, getScalarConstants g sharing fuel root = .ok (values,refs)

theorem scalarGetterSuccess_proven : ScalarGetterSuccess := by
  intro T g sharing fuel root ht _hna
  obtain ⟨refs,visited,hrefs,hvalid⟩ := constantRefs_success g sharing fuel root [] ht
  obtain ⟨values,hvalues⟩ := readValues_success g refs hvalid
  exact ⟨values,refs,by simp [getScalarConstants,hrefs,hvalues,bindOk,mapOk]⟩

example : Traversable ((Heap.empty.alloc (constantCell (1 : Nat))).2) 1 0 ∧
    Graph.NoAlias ((Heap.empty.alloc (constantCell (1 : Nat))).2) 0 := by
  constructor
  · exact ⟨constantCell 1,rfl,rfl,by intro _ _; exact ⟨1,rfl⟩,by simp [constantCell]⟩
  · exact Graph.noAlias_ofTree Heap.empty (.const 1)

def ConstantsRoundtrip : Prop := ∀ (g : Graph Nat) sharing fuel root,
  Traversable g fuel root → Graph.NoAlias g root →
    ∃ values refs, getScalarConstants g sharing fuel root = .ok (values,refs) ∧
      setScalarConstants g values refs = .ok g

theorem constantsRoundtrip_proven : ConstantsRoundtrip := by
  intro g sharing fuel root ht hna
  obtain ⟨values,refs,hget⟩ := scalarGetterSuccess_proven Nat g sharing fuel root ht (fun _ => hna)
  exact ⟨values,refs,hget,scalarGetterRestore_proven g sharing fuel root values refs hna hget⟩

def SharedCounting : Prop := ∀ (T : Type) (g : Graph T) fuel root,
  Traversable g fuel root → Graph.Acyclic g root →
    ∃ values refs, getScalarConstants g true fuel root = .ok (values,refs) ∧
      sharedConstantCount g fuel root = .ok values.length ∧ values.length = refs.length

theorem sharedCounting_proven : SharedCounting := by
  intro T g fuel root ht ha
  obtain ⟨values,refs,hget⟩ := scalarGetterSuccess_proven T g true fuel root ht (by simp)
  exact ⟨values,refs,hget,sharedCountCorrect_proven T g fuel root values refs ha hget⟩

private theorem foldlM_preserves (f : S → A → Jl S) (P : S → Prop) (xs : List A)
    (step : ∀ a ∈ xs, ∀ s s', P s → f s a = .ok s' → P s') :
    ∀ s s', P s → xs.foldlM f s = .ok s' → P s' := by
  induction xs with
  | nil =>
      intro s s' hs hr
      have he : s = s' := by simpa [List.foldlM, Pure.pure, Except.pure] using hr
      subst s'
      exact hs
  | cons a as ih =>
      intro s s' hs hr
      cases hm : f s a with
      | error e => simp only [List.foldlM_cons,hm,bindError,reduceCtorEq] at hr
      | ok mid =>
          simp only [List.foldlM_cons,hm,bindOk] at hr
          exact ih (fun b hb => step b (by simp [hb])) mid s' (step a (by simp) s mid hs hm) hr

private theorem child_reachable {g : Graph T} {root child target : Addr} {c : Cell T}
    (hc : g.cells root = some c) (hm : child ∈ c.children)
    (hr : Graph.Reachable g child target) : Graph.Reachable g root target := by
  have position : ∀ xs : List Addr, child ∈ xs → ∃ i : Nat, xs[i]? = some child := by
    intro xs
    induction xs with
    | nil => simp
    | cons a as ih =>
        intro h
        rcases List.mem_cons.mp h with he | h
        · subst a; exact ⟨0,rfl⟩
        · obtain ⟨i,hi⟩ := ih h; exact ⟨i + 1,by simpa using hi⟩
  obtain ⟨i,hi⟩ := position c.children hm
  obtain ⟨path,hpath⟩ := hr
  exact ⟨i :: path,Graph.Path.cons hc hi hpath⟩

def SourceConstants (g : Graph T) (root : Addr) (refs : List Addr) : Prop :=
  ∀ a ∈ refs, Graph.Reachable g root a ∧
    ∃ c, g.cells a = some c ∧ c.degree = 0 ∧ c.constant = true

theorem constantRefs_sourceConstants (g : Graph T) (sharing : Bool) (fuel : Nat) :
    ∀ root seen refs visited, constantRefs g sharing fuel root seen = .ok (refs,visited) →
      SourceConstants g root refs := by
  induction fuel with
  | zero => intro root seen refs visited h; simp [constantRefs] at h
  | succ fuel ih =>
      intro root seen refs visited h
      by_cases hs : sharing = true ∧ root ∈ seen
      · simp [constantRefs,hs] at h
        obtain ⟨rfl,_⟩ := h
        simp [SourceConstants]
      · cases hc : g.cells root with
        | none => simp [constantRefs,hs,Heap.read,hc,bindError] at h
        | some c =>
          have hr : g.read root = .ok c := by simp [Heap.read,hc]
          by_cases hd : c.degree = 0
          · by_cases hv : c.constant = true
            · simp [constantRefs,hs,hr,bindOk,hd,hv,Pure.pure,Except.pure] at h
              obtain ⟨rfl,_⟩ := h
              intro a ha
              have he : a = root := by simpa using ha
              subst a
              exact ⟨⟨[],Graph.Path.nil root⟩,c,hc,hd,hv⟩
            · simp [constantRefs,hs,hr,bindOk,hd,hv,Pure.pure,Except.pure] at h
              obtain ⟨rfl,_⟩ := h
              simp [SourceConstants]
          · let f := fun (state : List Addr × List Addr) child => do
              let (found,next) ← constantRefs g sharing fuel child state.2
              pure (state.1 ++ found,next)
            have step : ∀ child ∈ c.children, ∀ state next, SourceConstants g root state.1 →
                f state child = .ok next → SourceConstants g root next.1 := by
              intro child hchild state next hout hnext
              cases hv : constantRefs g sharing fuel child state.2 with
              | error e => simp [f,hv,mapError] at hnext
              | ok result =>
                  simp [f,hv,bindOk,Pure.pure,Except.pure] at hnext
                  subst next
                  intro a ha
                  rcases List.mem_append.mp ha with ha | ha
                  · exact hout a ha
                  · obtain ⟨hre,hcell⟩ := ih child state.2 result.1 result.2 hv a ha
                    exact ⟨child_reachable hc hchild hre,hcell⟩
            have hfold : c.children.foldlM f ([],if sharing then root :: seen else seen) =
                .ok (refs,visited) := by
              simpa [constantRefs,hs,hr,bindOk,hd,f] using h
            exact foldlM_preserves f (fun state => SourceConstants g root state.1) c.children
              step _ _ (by simp [SourceConstants]) hfold

end DynExpr.NodeUtils
