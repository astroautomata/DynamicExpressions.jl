import DynExpr.StringsParse.Parse

namespace DynExpr.StringsParse

mutual
  def treeDecEq (t u : Tree Scalar) : Decidable (t = u) := by
    cases t with
    | const a =>
      cases u with
      | const b =>
        exact if h : a = b then isTrue (by cases h; rfl)
          else isFalse (by intro e; exact h (Tree.const.inj e))
      | feature _ | branch _ _ => exact isFalse (by intro h; cases h)
    | feature a =>
      cases u with
      | feature b =>
        exact if h : a = b then isTrue (by cases h; rfl)
          else isFalse (by intro e; exact h (Tree.feature.inj e))
      | const _ | branch _ _ => exact isFalse (by intro h; cases h)
    | branch a as =>
      cases u with
      | branch b bs =>
        if h : a = b then
          match forestDecEq as bs with
          | isTrue e => exact isTrue (by cases h; cases e; rfl)
          | isFalse e => exact isFalse (by intro q; exact e (Tree.branch.inj q).2)
        else exact isFalse (by intro q; exact h (Tree.branch.inj q).1)
      | const _ | feature _ => exact isFalse (by intro h; cases h)
  def forestDecEq (ts us : List (Tree Scalar)) : Decidable (ts = us) := by
    cases ts with
    | nil =>
      cases us with
      | nil => exact isTrue rfl
      | cons _ _ => exact isFalse (by intro h; cases h)
    | cons t ts =>
      cases us with
      | nil => exact isFalse (by intro h; cases h)
      | cons u us =>
        match treeDecEq t u with
        | isTrue h =>
          match forestDecEq ts us with
          | isTrue e => exact isTrue (by cases h; cases e; rfl)
          | isFalse e => exact isFalse (by intro q; exact e (List.cons.inj q).2)
        | isFalse h => exact isFalse (by intro q; exact h (List.cons.inj q).1)
end

instance : DecidableEq (Tree Scalar) := treeDecEq

deriving instance DecidableEq for ParsedNode

instance [DecidableEq α] : DecidableEq (Jl α) := fun x y =>
  match x, y with
  | .ok a, .ok b => if h : a = b then isTrue (by cases h; rfl)
      else isFalse (by intro e; exact h (Except.ok.inj e))
  | .error a, .error b => if h : a = b then isTrue (by cases h; rfl)
      else isFalse (by intro e; exact h (Except.error.inj e))
  | .ok _, .error _ | .error _, .ok _ => isFalse (by intro h; cases h)

mutual
  def surfaceDecEq (s t : Surface) : Decidable (s = t) := by
    cases s <;> cases t <;> try (apply isFalse; intro h; cases h; done)
    · rename_i a b
      exact if h : a = b then isTrue (by cases h; rfl)
        else isFalse (by intro e; exact h (Surface.literal.inj e))
    · rename_i a b
      exact if h : a = b then isTrue (by cases h; rfl)
        else isFalse (by intro e; exact h (Surface.symbol.inj e))
    · rename_i name args otherName otherArgs
      if h : name = otherName then
        match surfaceListDecEq args otherArgs with
        | isTrue e => exact isTrue (by cases h; cases e; rfl)
        | isFalse e => exact isFalse (by intro q; exact e (Surface.call.inj q).2)
      else exact isFalse (by intro q; exact h (Surface.call.inj q).1)
    · rename_i f args otherF otherArgs
      if h : f = otherF then
        match surfaceListDecEq args otherArgs with
        | isTrue e => exact isTrue (by cases h; cases e; rfl)
        | isFalse e => exact isFalse (by intro q; exact e (Surface.dotCall.inj q).2)
      else exact isFalse (by intro q; exact h (Surface.dotCall.inj q).1)
    · rename_i tag tree otherTag otherTree
      if h : tag = otherTag then
        match treeDecEq tree otherTree with
        | isTrue e => exact isTrue (by cases h; cases e; rfl)
        | isFalse e => exact isFalse (by intro q; exact e (Surface.node.inj q).2)
      else exact isFalse (by intro q; exact h (Surface.node.inj q).1)
    · exact isTrue rfl
    · rename_i a b
      exact if h : a = b then isTrue (by cases h; rfl)
        else isFalse (by intro e; exact h (Surface.unsupported.inj e))
  def surfaceListDecEq (ss ts : List Surface) : Decidable (ss = ts) := by
    cases ss with
    | nil =>
      cases ts with
      | nil => exact isTrue rfl
      | cons _ _ => exact isFalse (by intro h; cases h)
    | cons s ss =>
      cases ts with
      | nil => exact isFalse (by intro h; cases h)
      | cons t ts =>
        match surfaceDecEq s t with
        | isTrue h =>
          match surfaceListDecEq ss ts with
          | isTrue e => exact isTrue (by cases h; cases e; rfl)
          | isFalse e => exact isFalse (by intro q; exact e (List.cons.inj q).2)
        | isFalse h => exact isFalse (by intro q; exact h (List.cons.inj q).1)
end

instance : DecidableEq Surface := surfaceDecEq

end DynExpr.StringsParse
