import tactic

-- Let `Ω` be a "big underlying set" and let `X` and `Y` and `Z` be subsets

variables (Ω : Type) (X Y Z : set Ω) (a b c x y z : Ω)

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
  rw subset_def,
  intros a ha,
  exact ha,
end

lemma subset_trans (hXY : X ⊆ Y) (hYZ : Y ⊆ Z) : X ⊆ Z :=
begin
  rw subset_def at *,
  intros a ha,
  -- ⊢ a ∈ Z
  -- hYZ says: a ∈ Y → a ∈ Z. So... 
  apply hYZ,
  -- ⊢ a ∈ Y
  apply hXY,
  exact ha,
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
  ext a,
  split,
  { apply hXY },
  { apply hYX }
end

/-!

### Unions and intersections

Type `\cup` or `\un` for `∪`, and `\cap` or `\i` for `∩`

-/

lemma mem_union_iff : a ∈ X ∪ Y ↔ a ∈ X ∨ a ∈ Y :=
begin
  -- true by definition
  refl,
end

lemma mem_inter_iff : a ∈ X ∩ Y ↔ a ∈ X ∧ a ∈ Y :=
begin
  -- true by definition
  refl,
end


-- You can rewrite with those lemmas above if you're not comfortable with
-- assuming they're true by definition.

-- union lemmas
-- if you want to use `mem_union_iff` you should start with `ext`

lemma union_self : X ∪ X = X :=
begin
  ext a,
  rw mem_union_iff,
  split,
  { intro h,
    cases h with ha ha;
    exact ha },
  { intro ha,
    left,
    exact ha }
end

lemma subset_union_left : X ⊆ X ∪ Y :=
begin
  rw subset_def,
  intros a haX,
  rw mem_union_iff,
  left,
  assumption,
end

lemma subset_union_right : Y ⊆ X ∪ Y :=
begin
  -- don't need to rewrite subset_def or mem_union_iff
  -- as they're both true by definition
  intros a haY,
  right,
  assumption,
end

lemma union_subset_iff : X ∪ Y ⊆ Z ↔ X ⊆ Z ∧ Y ⊆ Z :=
begin
  -- NB Lean's simplifier `simp` solves this (and many others)
  -- as do the tactics `finish` and `tidy`
  -- We will talk a bit more about `simp` in week 2.
  split,
  { intro h,
    split,
    { intros a haX,
      apply h,
      left,
      assumption },
    { intros a haY,
      apply h,
      right,
      assumption },
  },
  { rintros ⟨hXZ, hYZ⟩ a (haX | haY),
    { exact hXZ haX },
    { exact hYZ haY } }
end

variable (W : set Ω)

lemma union_subset_union (hWX : W ⊆ X) (hYZ : Y ⊆ Z) : W ∪ Y ⊆ X ∪ Z :=
begin
  rintros a (haW | haY),
  { left,
    exact hWX haW },
  { right,
    exact hYZ haY }
end

lemma union_subset_union_left (hXY : X ⊆ Y) : X ∪ Z ⊆ Y ∪ Z :=
begin
  rintros a (haX | haZ),
  { left, 
    exact hXY haX },
  { right,
    assumption }
end

-- etc etc

-- intersection lemmas

lemma inter_subset_left : X ∩ Y ⊆ X :=
begin
  rintro a ⟨haX, haY⟩,
  assumption,
end

-- don't forget `ext` to make progress with equalities of sets

lemma inter_self : X ∩ X = X :=
begin
  ext a,
  split,
  { rintro ⟨ha, -⟩,
    assumption },
  { intro ha,
    exact ⟨ha, ha⟩ }
end

lemma inter_comm : X ∩ Y = Y ∩ X :=
begin
  ext a,
  split;
  { rintro ⟨h1, h2⟩,
    exact ⟨h2, h1⟩ }
end

lemma inter_assoc : X ∩ (Y ∩ Z) = (X ∩ Y) ∩ Z :=
begin
--  finish,
  -- tidy works too,
  ext a,
  split,
  { rintro ⟨hx, hy, hz⟩, -- try `rintro?` to see the syntax
    exact ⟨⟨hx, hy⟩, hz⟩ },
  { rintro ⟨⟨hx, hy⟩, hz⟩,
    exact ⟨hx, hy, hz⟩ },
end

/-!

### Forall and exists

-/

lemma not_exists_iff_forall_not : ¬ (∃ a, a ∈ X) ↔ ∀ b, ¬ (b ∈ X) :=
begin
  split,
  { intros h b hb,
    apply h,
    use b,
    assumption },
  { rintro h ⟨a, ha⟩,
    exact h a ha },
end



example : ¬ (∀ a, a ∈ X) ↔ ∃ b, ¬ (b ∈ X) :=
begin
  split,
  { -- you need classical logic to do this part
    -- `contrapose!` is a way of making progress
    -- `finish` does it completely.
    -- We use `by_contra`, which
    -- turns a goal `⊢ P` into 
    -- a hypothesis `h : ¬ P` and
    -- a goal of `false`
    intro h,
    by_contra hnX,
    apply h,
    intro a,
    by_contra hXa,
    apply hnX,
    use a, }, 
  { intro h,
    cases h with b hb,
    intro h,
    apply hb,
    apply h }
end

end xena

