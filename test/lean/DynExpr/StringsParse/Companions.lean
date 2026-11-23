import DynExpr.StringsParse.GeneralStrings
import DynExpr.StringsParse.GeneralOwnership

namespace DynExpr.StringsParse.General
set_option maxHeartbeats 400000
set_option maxRecDepth 3000

/-- Feature names are injective when the supplied names are unique and cover
all valid feature indices, src/Strings.jl:95-103. -/
def CompleteFeatureNames : Prop := ∀ names i j,
  names.Nodup → 1 ≤ i → i ≤ names.length → 1 ≤ j → j ≤ names.length →
  stringVariable i (some names) = stringVariable j (some names) → i = j

theorem completeFeatureNames : CompleteFeatureNames := by
  intro names i j hn hi hij hj hjl he
  have hii : i - 1 < names.length := by omega
  have hjj : j - 1 < names.length := by omega
  have hz1 : i ≠ 0 := by omega
  have hz2 : j ≠ 0 := by omega
  simp only [stringVariable, hz1, hz2, ↓reduceIte, List.getElem?_eq_getElem hii,
    List.getElem?_eq_getElem hjj, Option.getD_some] at he
  have h1 := List.Nodup.idxOf_getElem hn (i - 1) hii
  have h2 := List.Nodup.idxOf_getElem hn (j - 1) hjj
  rw [he] at h1
  omega

example : (["alpha", "beta"] : List String).Nodup ∧ 1 ≤ (1 : Nat) ∧ 1 ≤ (2 : Nat) ∧
  2 ≤ (["alpha", "beta"] : List String).length := by decide

/-- Every nonempty input to strip_brackets succeeds, including arbitrary
rendered text and the smallest bracket pair (), src/Strings.jl:71-77. -/
def NonemptyStrip : Prop := ∀ text, text.isEmpty = false →
  stripBrackets text = .ok (stripOnce text)

theorem nonemptyStrip : NonemptyStrip := by
  intro text h
  simp only [stripBrackets, h, Bool.false_eq_true, ↓reduceIte, stripOnce]
  by_cases hc : (text.toList.head? == some '(' && text.toList.getLast? == some ')') = true
  · rw [if_pos hc, if_pos hc]
  · rw [if_neg hc, if_neg hc]
example : "()".isEmpty = false := rfl

/-- Type-compatible prebuilt inputs honor the request with their tree unchanged;
`convert` returns a same-family node itself, src/Parse.jl:594-595. -/
def CompatibleNodeType : Prop := ∀ cfg tree,
  parseExpression cfg (.node cfg.nodeType tree) = .ok ⟨cfg.nodeType, tree⟩

theorem compatibleNodeType : CompatibleNodeType := by
  intro cfg tree
  unfold parseExpression normalize
  rfl
example : parseExpression parseCfg (.node parseCfg.nodeType (.feature 1)) =
  .ok ⟨parseCfg.nodeType, .feature 1⟩ := rfl

theorem cachedName_fst (cache : List (Nat × String)) (key : Nat) (render : String) :
    (cachedName cache key render).1 =
      ((cache.find? (fun p => p.1 == key)).map Prod.snd).getD render := by
  unfold cachedName
  split
  · rename_i p hp
    simp [hp]
  · rename_i hp
    simp [hp]

/-- For every cache content, a non-singleton callable is rendered afresh, and a
singleton callable keeps its display whenever every cached entry at its
`objectid` holds that display, src/Strings.jl:46-52. -/
def CollisionFreeCache : Prop := ∀ (cache : List (Nat × String)) (op : OpObject),
  (op.singleton = false → (getOpName cache op).1 = op.name) ∧
  ((∀ p ∈ cache, p.1 = op.objectId → p.2 = op.name) → (getOpName cache op).1 = op.name)

theorem collisionFreeCache : CollisionFreeCache := by
  intro cache op
  refine ⟨fun h => by simp [getOpName, h], fun h => ?_⟩
  unfold getOpName
  split
  · rw [cachedName_fst]
    cases hf : cache.find? (fun p => p.1 == op.objectId) with
    | none => rfl
    | some p =>
      have hm := List.mem_of_find?_eq_some hf
      have hk := List.find?_some hf
      simp only [Option.map_some, Option.getD_some]
      exact h p hm (by simpa using hk)
  · rfl

example : ∀ p ∈ ([(0, "f"), (1, "g")] : List (Nat × String)), p.1 = 1 → p.2 = "g" := by
  decide

/-- The cache after any run of earlier calls only holds names that singleton
callables print for their own `objectid`. -/
private theorem getOpName_inv (singletonName : Nat → String) (cache : List (Nat × String))
    (op : OpObject) (hc : ∀ p ∈ cache, p.2 = singletonName p.1)
    (ho : op.singleton = true → op.name = singletonName op.objectId) :
    ∀ p ∈ (getOpName cache op).2, p.2 = singletonName p.1 := by
  unfold getOpName
  split
  · rename_i hs
    unfold cachedName
    split
    · exact hc
    · intro p hp
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · exact ho hs
      · exact hc p hp
  · exact hc

private theorem runOpNames_inv (singletonName : Nat → String) :
    ∀ (calls : List OpObject) (cache : List (Nat × String)),
      (∀ p ∈ cache, p.2 = singletonName p.1) →
      (∀ c ∈ calls, c.singleton = true → c.name = singletonName c.objectId) →
      ∀ p ∈ calls.foldl (fun cache op => (getOpName cache op).2) cache, p.2 = singletonName p.1 := by
  intro calls
  induction calls with
  | nil => intro cache hc _; exact hc
  | cons c cs ih =>
    intro cache hc hcs
    simp only [List.foldl_cons]
    exact ih _ (getOpName_inv singletonName cache c hc (hcs c (by simp)))
      (fun d hd => hcs d (by simp [hd]))

/-- After every sequence of earlier `get_op_name` calls on the process-wide cache,
every queried callable gets its own name, given that singleton callables with
the same `objectid` are one object and so print one name (Q44),
src/Strings.jl:44-66. -/
def CacheDisplayPreserved : Prop := ∀ (singletonName : Nat → String) (calls : List OpObject)
    (op : OpObject),
  (∀ c ∈ op :: calls, c.singleton = true → c.name = singletonName c.objectId) →
  (getOpName (runOpNames calls) op).1 = op.name

theorem cacheDisplayPreserved : CacheDisplayPreserved := by
  intro singletonName calls op h
  have hinv := runOpNames_inv singletonName calls [] (by simp) (fun c hc => h c (by simp [hc]))
  cases hs : op.singleton
  · exact (collisionFreeCache (runOpNames calls) op).1 hs
  · refine (collisionFreeCache (runOpNames calls) op).2 (fun p hp hk => ?_)
    rw [hinv p hp, hk, ← h op (by simp) hs]

example : ∀ c ∈ ([⟨0, true, "f"⟩, ⟨0, true, "f"⟩, ⟨1, false, "g"⟩] : List OpObject),
    c.singleton = true → c.name = (fun _ : Nat => "f") c.objectId := by
  decide

end DynExpr.StringsParse.General
