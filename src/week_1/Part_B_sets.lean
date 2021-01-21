import tactic

-- Let `Ω` be a "big underlying set" and let `X` and `Y` and `Z` be subsets

variables (Ω : Type) (X Y Z : set Ω) (a b c x y z : Ω)

/-
* `→` ("implies" -- type with `\l`)
* `¬` ("not" -- type with `\not` or `\n`)
* `∧` ("and" -- type with `\and` or `\an`)
* `↔` ("iff" -- type with `\iff` or `\lr`)
* `∨` ("or" -- type with `\or` or `\v`
-/

namespace xena

/-!

# subsets

Let's think about `X ⊆ Y`. Typeset `⊆` with `\sub` or `\ss`
-/

-- `X ⊆ Y` is the same as `∀ a, a ∈ X → a ∈ Y` , by definition.

lemma subset_def : X ⊆ Y ↔ ∀ a, a ∈ X → a ∈ Y :=
begin
  -- true by definition
  refl
end

lemma subset_refl : X ⊆ X :=
begin
  sorry,
end

lemma subset_trans (hXY : X ⊆ Y) (hYZ : Y ⊆ Z) : X ⊆ Z :=
begin
  -- If you start with `rw subset_def at *` then you
  -- will have things like `hYZ : ∀ (a : Ω), a ∈ Y → a ∈ Z`
  -- You need to think of `hYZ` as a function, which has two
  -- inputs: first a term `a` of type `Ω`, and second a proof `haY` that `a ∈ Y`.
  -- It then produces one output `haZ`, a proof that `a ∈ Z`.
  -- You can also think of it as an implication:
  -- "if a is in Ω, and if a ∈ Y, then a ∈ Z". Because it's an implication,
  -- you can `apply hYZ`. This is a really useful skill!
  sorry
end

/-!

# Equality of sets

Two sets are equal if and only if they have the same elements.
The name of this theorem is `set.ext_iff`.
-/

example : X = Y ↔ (∀ a, a ∈ X ↔ a ∈ Y) :=
begin
  exact set.ext_iff
end

-- In practice, you often have a goal `⊢ X = Y` and you want to reduce
-- it to `a ∈ X ↔ a ∈ Y` for an arbitary `a : Ω`. This can be done with
-- the `ext` tactic. 


lemma subset.antisymm (hXY : X ⊆ Y) (hYX : Y ⊆ X) : X = Y :=
begin
  -- start with `ext a`,
  sorry
end

/-!

### Unions and intersections

Type `\cup` or `\un` for `∪`, and `\cap` or `\i` for `∩`

-/

lemma union_def : a ∈ X ∪ Y ↔ a ∈ X ∨ a ∈ Y :=
begin
  -- true by definition
  refl,
end

lemma inter_def : a ∈ X ∩ Y ↔ a ∈ X ∧ a ∈ Y :=
begin
  -- true by definition
  refl,
end


-- You can rewrite with those lemmas above if you're not comfortable with
-- assuming they're true by definition.

-- union lemmas

lemma union_self : X ∪ X = X :=
begin
  sorry
end

lemma subset_union_left : X ⊆ X ∪ Y :=
begin
  sorry
end

lemma subset_union_right : Y ⊆ X ∪ Y :=
begin
  sorry
end

lemma union_subset_iff : X ∪ Y ⊆ Z ↔ X ⊆ Z ∧ Y ⊆ Z :=
begin
  sorry
end

variable (W : set Ω)

lemma union_subset_union (hWX : W ⊆ X) (hYZ : Y ⊆ Z) : W ∪ Y ⊆ X ∪ Z :=
begin
  sorry
end

lemma union_subset_union_left (hXY : X ⊆ Y) : X ∪ Z ⊆ Y ∪ Z :=
begin
  sorry
end

-- etc etc

-- intersection lemmas

lemma inter_subset_left : X ∩ Y ⊆ X :=
begin
  sorry
end

-- don't forget `ext` to make progress with equalities of sets

lemma inter_self : X ∩ X = X :=
begin
  sorry
end

lemma inter_comm : X ∩ Y = Y ∩ X :=
begin
  sorry
end

lemma inter_assoc : X ∩ (Y ∩ Z) = (X ∩ Y) ∩ Z :=
begin
  sorry
end

/-!

### Forall and exists

-/

lemma not_exists_iff_forall_not : ¬ (∃ a, a ∈ X) ↔ ∀ b, ¬ (b ∈ X) :=
begin
  sorry,
end

example : ¬ (∀ a, a ∈ X) ↔ ∃ b, ¬ (b ∈ X) :=
begin
  sorry,
end

end xena

