import tactic

/-!

# Equivalence relations are the same as partitions

In this file we prove that there's a bijection between
the equivalence relations on a type, and the partitions of a type. 

Three sections:

1) partitions
2) equivalence classes
3) the proof

## Overview

Say `α` is a type, and `R : α → α → Prop` is a binary relation on `α`. 
The following things are already in Lean:

`reflexive R := ∀ (x : α), R x x`
`symmetric R := ∀ ⦃x y : α⦄, R x y → R y x`
`transitive R := ∀ ⦃x y z : α⦄, R x y → R y z → R x z`

`equivalence R := reflexive R ∧ symmetric R ∧ transitive R`

In the file below, we will define partitions of `α` and "build some
interface" (i.e. prove some propositions). We will define
equivalence classes and do the same thing.
Finally, we will prove that there's a bijection between
equivalence relations on `α` and partitions of `α`.

-/

/-

# 1) Partitions

We define a partition, and prove some lemmas about partitions. Some
I prove myself (not always using tactics) and some I leave for you.

## Definition of a partition

Let `α` be a type. A *partition* on `α` is defined to be
the following data:

1) A set C of subsets of α, called "blocks".
2) A hypothesis (i.e. a proof!) that all the blocks are non-empty.
3) A hypothesis that every term of type α is in one of the blocks.
4) A hypothesis that two blocks with non-empty intersection are equal.
-/

/-- The structure of a partition on a Type α. -/ 
@[ext] structure partition (α : Type) :=
(C : set (set α))
(Hnonempty : ∀ X ∈ C, (X : set α).nonempty)
(Hcover : ∀ a, ∃ X ∈ C, a ∈ X)
(Hdisjoint : ∀ X Y ∈ C, (X ∩ Y : set α).nonempty → X = Y)

/-

## Basic interface for partitions

Here's the way notation works. If `α` is a type (i.e. a set)
then a term `P` of type `partition α` is a partition of `α`,
that is, a set of disjoint nonempty subsets of `α` whose union is `α`.

The collection of sets underlying `P` is `P.C`, the proof that
they're all nonempty is `P.Hnonempty` and so on.

-/

namespace partition

-- let α be a type, and fix a partition P on α. Let X and Y be subsets of α.
variables {α : Type} {P : partition α} {X Y : set α}

/-- If X and Y are blocks, and a is in X and Y, then X = Y. -/
theorem eq_of_mem (hX : X ∈ P.C) (hY : Y ∈ P.C) {a : α} (haX : a ∈ X)
  (haY : a ∈ Y) : X = Y :=
-- Proof: follows immediately from the disjointness hypothesis.
P.Hdisjoint _ _ hX hY ⟨a, haX, haY⟩

/-- If a is in two blocks X and Y, and if b is in X,
  then b is in Y (as X=Y) -/
theorem mem_of_mem (hX : X ∈ P.C) (hY : Y ∈ P.C) {a b : α}
  (haX : a ∈ X) (haY : a ∈ Y) (hbX : b ∈ X) : b ∈ Y :=
begin
  -- you might want to start with `have hXY : X = Y`
  -- and prove it from the previous lemma
  have hXY : X = Y,
  { exact eq_of_mem hX hY haX haY },
  -- we have b ∈ X as an assumption, and the goal is b ∈ Y.
  rw ← hXY,
  -- The goal is now b ∈ X
  assumption,
end

/-- Every term of type `α` is in one of the blocks for a partition `P`. -/
theorem mem_block (a : α) : ∃ X : set α, X ∈ P.C ∧ a ∈ X :=
begin
  -- an interesting way to start is
  -- `obtain ⟨X, hX, haX⟩ := P.Hcover a,`
  obtain ⟨X, hX, haX⟩ := P.Hcover a,
  -- `use` is the tactic to make progress with an `∃` goal
  use X,
  -- instead of `split` I'll just prove both things at once
  exact ⟨hX, haX⟩,
end

end partition

/-

# 2) Equivalence classes.

We define equivalence classes and prove a few basic results about them.

-/

section equivalence_classes

/-!

## Definition of equivalence classes 

-/

-- Notation and variables for the equivalence class section:

-- let α be a type, and let R be a binary relation on R.
variables {α : Type} (R : α → α → Prop)

/-- The equivalence class of `a` is the set of `b` related to `a`. -/
def cl (a : α) :=
{b : α | R b a}

/-!

## Basic lemmas about equivalence classes

-/

/-- Useful for rewriting -- `b` is in the equivalence class of `a` iff
`b` is related to `a`. True by definition. -/
theorem mem_cl_iff {a b : α} : b ∈ cl R a ↔ R b a :=
begin
  -- true by definition
  refl
end

-- Assume now that R is an equivalence relation.
variables {R} (hR : equivalence R)
include hR

/-- x is in cl(x) -/
lemma mem_cl_self (a : α) :
  a ∈ cl R a :=
begin
  -- Note that `hR : equivalence R` is a package of three things.
  -- You can extract the things with
  -- `rcases hR with ⟨hrefl, hsymm, htrans⟩,` or
  -- `obtain ⟨hrefl, hsymm, htrans⟩ := hR,`
  obtain ⟨hrefl, hsymm, htrans⟩ := hR,
  rw mem_cl_iff, -- not necessary (the proof is `refl`) but let's do it anyway
  -- now use reflexivity of `R`.
  apply hrefl,
end

lemma cl_sub_cl_of_mem_cl {a b : α} :
  a ∈ cl R b →
  cl R a ⊆ cl R b :=
begin
  -- remember `set.subset_def` says `X ⊆ Y ↔ ∀ a, a ∈ X → a ∈ Y
  intro hab,
--  rw set.subset_def, -- not necessary because this is true by definition
  intros z hza,
  rw mem_cl_iff at hab hza ⊢,
  obtain ⟨hrefl, hsymm, htrans⟩ := hR,
  -- use transitivity of R to finish
  exact htrans hza hab,
end

lemma cl_eq_cl_of_mem_cl {a b : α} :
  a ∈ cl R b →
  cl R a = cl R b :=
begin
  intro hab,
  -- remember `set.subset.antisymm` says `X ⊆ Y → Y ⊆ X → X = Y`
  apply set.subset.antisymm,
  -- two goals now
  { -- first goal we proved already above
    exact cl_sub_cl_of_mem_cl hR hab},
  { -- second goal we can reduce to b ∈ cl R a, i.e. R b a
    apply cl_sub_cl_of_mem_cl hR,
    obtain ⟨hrefl, hsymm, htrans⟩ := hR,
    -- and we know R a b so let's use symmetry
    exact hsymm hab }
end

end equivalence_classes -- section

/-!

# 3) The theorem

Let `α` be a type (i.e. a collection of stucff).

There is a bijection between equivalence relations on `α` and
partitions of `α`.

We prove this by writing down constructions in each direction
and proving that the constructions are two-sided inverses of one another.
-/

open partition


example (α : Type) : {R : α → α → Prop // equivalence R} ≃ partition α :=
-- We define constructions (functions!) in both directions and prove that
-- one is a two-sided inverse of the other
{ -- Here is the first construction, from equivalence
  -- relations to partitions.
  -- Let R be an equivalence relation.
  to_fun := λ R, {
    -- Let C be the set of equivalence classes for R.
    C := { B : set α | ∃ x : α, B = cl R.1 x},
    -- I claim that C is a partition. We need to check the three
    -- hypotheses for a partition (`Hnonempty`, `Hcover` and `Hdisjoint`),
    -- so we need to supply three proofs.
    Hnonempty := begin
      cases R with R hR,
      -- If X is an equivalence class then X is nonempty.
      show ∀ (X : set α), (∃ (a : α), X = cl R a) → X.nonempty,
      -- let's assume X is the equivalence class of a
      rintros _ ⟨a, rfl⟩,
      -- we now have to prove that `cl R a` is nonempty,
      -- i.e. that there exists an element of `cl R a`. 
      -- In particular this goal is an `∃`. Let's use `a`.
      use a,
      -- let's change the goal to R a a
      rw mem_cl_iff, -- comment out this line and the proof still works
      obtain ⟨hrefl, hsymm, htrans⟩ := hR,
      -- apply reflexivity of R
      apply hrefl,
    end,
    Hcover := begin
      cases R with R hR,
      -- The equivalence classes cover α
      show ∀ (a : α), ∃ (X : set α) (H : ∃ (b : α), X = cl R b), a ∈ X,
      -- let a be in α
      intro a,
      -- the goal is to prove that a is in some equivalence class.
      -- Let's use the equivalence class of a!
      use cl R a,
      -- Our goal is now of the form `P ∧ Q`
      split,
      { -- this first goal: we need to prove there's b such that cl a = cl b.
        -- let's use a!
        use a
        -- Lean tries `refl` by itself and it works
      },
      { -- here we need to prove a ∈ cl R a, which by definition means
        -- that we need to prove `R a a`. Let's apply reflexivity of `R`.
        -- For a change I won't take `hR` apart, I'll just pull off the
        -- first term.
        apply hR.1 },
    end,
    Hdisjoint := begin
      cases R with R hR,
      -- If two equivalence classes overlap, they are equal.
      show ∀ (X Y : set α), (∃ (a : α), X = cl R a) →
        (∃ (b : α), Y = cl _ b) → (X ∩ Y).nonempty → X = Y,
      -- let X and Y be equivalence classes of a and b respectively.
      -- Let's assume also that c is in X and Y.
      rintros X Y ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨c, hca, hcb⟩,
      -- tidy up
      dsimp at *,
      -- we need to prove `cl R a = cl R b`. But we have proved a lemma
      -- here which is useful:
      apply cl_eq_cl_of_mem_cl hR,
      -- now we just have to rpove a ∈ cl R b, which is by definition
      -- R a b. Let's prove this by showing R a c and R c b
      -- and using transitivity. Let's start with transitivity.
      apply hR.2.2,
        -- ?m_1 is just Lean's way of writing an unknown variable.
        -- It's supposed to be `c`.
        change R a c, -- now it is `c`.
        -- Now we have two goals, `R a c` and `R c b`.
        -- Now let's use symmetry on the first goal.
        apply hR.2.1,
        -- now the first goal is `hca`
        exact hca,
      -- and the second is `hcb`
      exact hcb,
    end },
  -- Conversely, say P is an partition. 
  inv_fun := λ P, 
    -- Let's define a binary relation `R` thus:
    --  `R a b` iff *every* block containing `a` also contains `b`.
    -- Because only one block contains a, this will work,
    -- and it turns out to be a nice way of thinking about it. 
    ⟨λ a b, ∀ X ∈ P.C, a ∈ X → b ∈ X, begin
      -- I claim this is an equivalence relation.
    split,
    { -- It's reflexive
      show ∀ (a : α)
        (X : set α), X ∈ P.C → a ∈ X → a ∈ X,
      -- let a be in α and let X be a block such that a ∈ X
      intros a X hXC haX,
      -- now we have to prove a ∈ X but this is an assumption
      assumption,
    },
    split,
    { -- it's symmetric
      show ∀ (a b : α),
        (∀ (X : set α), X ∈ P.C → a ∈ X → b ∈ X) →
         ∀ (X : set α), X ∈ P.C → b ∈ X → a ∈ X,
      -- say a and b are in α, say X is a block, and
      -- let `h` be the hypothesis that b is in every block which a is in.
      intros a b h X hX hbX,
      -- let `Y` be a block which `a` is in.
      obtain ⟨Y, hY, haY⟩ := P.Hcover a,
      -- apply `h` to hypothesis `Y` and deduce that `b ∈ Y`
      specialize h Y hY haY,
      -- now a,b ∈ Y and b ∈ X so a ∈ X by a previous lemma
      exact mem_of_mem hY hX h hbX haY,
    },
    { -- it's transitive
      unfold transitive,
      show ∀ (a b c : α),
        (∀ (X : set α), X ∈ P.C → a ∈ X → b ∈ X) →
        (∀ (X : set α), X ∈ P.C → b ∈ X → c ∈ X) →
         ∀ (X : set α), X ∈ P.C → a ∈ X → c ∈ X,
      -- say a,b,c are in α, with `a ∈ X`, let `hbX` be the hypothesis that `b` is in
      -- every block which `a` is in, and let `hcX` be the hypothesis
      -- that `c` is in every block which `b` is in. 
      intros a b c hbX hcX X hX haX,
      -- Our goal is `c ∈ X`. 
      -- let's now use `hcX` to reduce it to `b ∈ X` 
      apply hcX, assumption,
      -- and now let's use `hbX` to reduce it to `a ∈ X`
      apply hbX, assumption,
      -- but this is an assumption!
      assumption,
    }
  end⟩,
  -- If you start with the equivalence relation, and then make the partition
  -- and a new equivalence relation, you get back to where you started.
  left_inv := begin
    rintro ⟨R, hR⟩,
    -- Tidying up the mess...
    suffices : (λ (a b : α), ∀ (c : α), a ∈ cl R c → b ∈ cl R c) = R,
      simpa,
    -- ... you have to prove two binary relations are equal.
    ext a b,
    -- so you have to prove an if and only if.
    show (∀ (c : α), a ∈ cl R c → b ∈ cl R c) ↔ R a b,
    -- this is an ↔ so we can split it into → and ←.
    split,
    { -- Assume ∀ c, a ∈ cl c → b ∈ cl c 
      intros hab,
      -- our goal is to prove R a b. Let's use symmetry
      apply hR.2.1,
      -- now let's use our assumption (with c = a, Lean guesses we mean this),
      apply hab,
      -- and now we have to prove a ∈ cl a, which is reflexivity
      apply hR.1,
    },
    { -- conversely, let's assume `R a b` and say `c` is arbitrary
      -- such that a ∈ cl c`
      intros hab c hac,
      -- we have to prove b ∈ cl c, i.e. that `R b c`. Let's use transitivity
      apply hR.2.2,
        -- now we have to prove R b ? and R ? c for some ?. Let's let ? be a.
        change R b a,
        -- R b a follows from symmetry and R a b
        apply hR.2.1,
        exact hab,
      -- and R a c follows from a ∈ cl c (which is the same thing)
      exact hac,
    }
  end,
  -- Similarly, if you start with the partition, and then make the
  -- equivalence relation, and then construct the corresponding partition 
  -- into equivalence classes, you have the same partition you started with.  
  right_inv := begin
    -- Let P be a partition
    intro P,
    -- It suffices to prove that a subset X is in the original partition
    -- if and only if it's in the one made from the equivalence relation.
    ext X,
    show (∃ (a : α), X = cl _ a) ↔ X ∈ P.C,
    dsimp only,
    -- the goal is a bit intimidating. It says that there exists an a
    -- such that X is the equivalence class of a for this new complicated
    -- equivalence relation, if and only if X is a block. This is an ↔ 
    -- goal. Let's prove both ways independently.
    split,
    { -- this way: assume X is the class of a for the equivalence relation
      -- we just made.
      rintro ⟨a, rfl⟩,
      -- We know P is a partition so let's take a block `X` containing `a`.
      obtain ⟨X, hX, haX⟩ := P.Hcover a,
      -- We know `X` is a block, i.e. `X ∈ P.C`. We're trying to prove
      -- that some strange equivalence class is in `P.C`. I claim that
      -- this class is `X`. So the proof should really be `hX`, except...
      convert hX,
      -- ... we have to prove that `X` is actually this messy class.
      -- How do we prove two sets are equal? We show that they have
      -- the same elements! So let's say `b` is in α.
      ext b,
      -- We need to show b is in the class of a iff b is in X.
      -- What does it mean for b to be in the equivalence class of a?
      rw mem_cl_iff,
      -- It means b and a are related, i.e. for every block,
      -- if b is in it then a is in it. Let's prove this iff by proving
      -- both directions.
      split,
      { -- assume a is in every block that b is in.
        intro haY,
        -- We know b is in a block, let's call it Y.
        obtain ⟨Y, hY, hbY⟩ := P.Hcover b,
        -- We know a is in every block that b is in, so a is in Y.
        specialize haY Y hY hbY,
        -- Now a ∈ X and a ∈ Y, so we must have X = Y. This means
        -- that our goal is technically proved by `hbY`
        convert hbY,
        -- except that we have to prove X = Y. But this is a previous lemma.
        exact eq_of_mem hX hY haX haY,
      },
      { -- Conversely, assume b ∈ X. We need to prove that a is in every
        -- block which b is in. So let Y be a random block which b is in.
        intros hbX Y hY hbY,
        -- We want to show a ∈ Y. 
        -- But we know a,b in X and b in Y so we're done by a previous
        -- lemma.
        apply mem_of_mem hX hY hbX hbY haX,
      }
    },
    { -- conversely, let's assume X is a block.
      intro hX,
      -- We need to prove that X is the equivalence class of some `a`.
      -- Well, each block is nonempty, so let's take `a` in `X`.
      rcases P.Hnonempty X hX with ⟨a, ha⟩,
      -- The claim is that X is the equivalence class of `a`.
      use a,
      -- We now need to show two sets are equal, so let's use extensionality
      -- i.e. prove they have the same elements. Say b is in α.
      ext b,
      -- We have to prove b ∈ X ↔ b ∈ the equivalence class. Let's prove
      -- each direction separately.
      split,
      { -- Say b ∈ X.
        intro hbX,
        -- Let's prove it's in the equivalence class. What does it
        -- mean to be in an equivalence class?
        rw mem_cl_iff,
        -- we need to show that `a` is in every block which `b` is in.
        -- So let `Y` be any block which `b` is in.
        intros Y hY hbY,
        -- Now a,b ∈ X and b ∈ Y so we can deduce a ∈ Y from a previous lemma.
        exact mem_of_mem hX hY hbX hbY ha,
      },
      { -- conversely, say b is in some equivalence class. What does this mean?
        rw mem_cl_iff,
        -- It means that `a` is in every block which `b` is in.
        intro haY,
        -- OK so b is in some block, let's call it `Y`.
        obtain ⟨Y, hY, hbY⟩ := P.Hcover b,
        -- This means `a` is in that block too.
        specialize haY Y hY hbY,
        -- and now a,b ∈ Y and a ∈ X so we can deduce b ∈ X from a previous lemma
        exact mem_of_mem hY hX haY ha hbY,
      }
    }
  end }
