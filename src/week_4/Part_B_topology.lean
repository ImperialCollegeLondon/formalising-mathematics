import topology.subset_properties -- compactness of subsets of top spaces
/-!

# Topology, the traditional way

Let's do some topology! In this file we prove that 

* the continuous image of a compact space is compact;
* A closed subset of a compact space is compact.

## Details

In fact we do a little more than this (but it's basically equivalent).
We do not work with compact topological spaces, we work with compact
subsets of topological spaces. What we will actually prove is this:

* If `f : X → Y` is a continuous map, and `S : set X` is a compact subset
(with the subspace topology), then `f '' S` (the image of `S` under `f`) is
compact (with the subspace topology).

* If `X` is a topological space, if `S` is a compact subset and if `C` is
a closed subset, then `S ∩ C` is a compact subset.

The original results are just the special case where `S` is `univ : set X`.
-/

-- Let X and Y by topological spaces, and let `f : X → Y` be a map.
variables (X Y : Type) [topological_space X] [topological_space Y] (f : X → Y)

-- I don't want to be typing `set.this` and `set.that` so let's open
-- the `set` namespace once and for all.
open set

/-!

## Compact subspaces

`is_compact` is a predicate on `set X`, if `X` is a topological space. 
In other words, `is_compact X` doesn't make sense, but if `S : set X`
then `is_compact S` does. The actual definition in mathlib involves
filters! But it is a theorem in mathlib that `is_compact S` is true if and only
if every collection of open subsets of `X` whose union contains `S`
has a finite subcollection whose union contains `S`. Unfortunately,
mathlib's version of this, `compact_iff_finite_subcover`, uses a slightly
wacky notion of finite subcover involving `finset X`, the type of finite
subsets of `X` (a completely different type to the type `set X`!).
We prove an easier-to-use version involving `finite Z`, the predicate
saying that `Z : set ι` is finite. You can ignore this.
-/
lemma compact_iff_finite_subcover'
  {α : Type} [topological_space α] {S : set α} :
  is_compact S ↔ (∀ {ι : Type} (U : ι → (set α)), (∀ i, is_open (U i)) →
    S ⊆ (⋃ i, U i) → (∃ (t : set ι), t.finite ∧ S ⊆ (⋃ i ∈ t, U i))) :=
begin
  rw compact_iff_finite_subcover,
  split,
  { intros hs ι U hU hsU,
    cases hs U hU hsU with F hF,
    use [(↑F : set ι), finset.finite_to_set F],
    exact hF },
  { intros hs ι U hU hsU,
    rcases hs U hU hsU with ⟨F, hFfin, hF⟩,
    use hFfin.to_finset,
    convert hF,
    ext,
    simp }  
end

/-!

## Continuous image of compact is compact

I would start with `rw compact_iff_finite_subcover' at hS ⊢,`

The proof that I recommend formalising is this. Say `S` is a compact
subset of `X`, and `f : X → Y` is continuous. We want to prove that
every cover of `f '' S` by open subsets of `Y` has a finite subcover.
So let's cover `f '' S` with opens `U i : set Y`, for `i : ι` and `ι` an index type.
Pull these opens back to `V i : set X` and observe that they cover `S`.
Choose a finite subcover corresponding to some `F : set ι` such that `F` is finite
(Lean writes this `h : F.finite`) and then check that the corresponding cover
of `f '' S` by the `U i` with `i ∈ F` is a finite subcover.

Good luck! Please ask questions (or DM me on discord if you don't want to 
ask publically). Also feel free to DM me if you manage to do it!
-/
lemma image_compact_of_compact (hf : continuous f) (S : set X) (hS : is_compact S) :
  is_compact (f '' S) :=
begin
  -- proof we formalise:
  -- (1) cover f''s with opens. Want finite subcover
  -- (2) pull back
  -- (3) finite subcover
  -- (4) push forward
  rw compact_iff_finite_subcover' at hS ⊢,
  -- Say we have a cover of `f '' S` by opens `U i` for `i : ι`.
  intro ι,
  intro U,
  intro hU,
  intro hcoverU,
  -- Define `T` to be `f '' S` -- why not?
  set T := f '' S with hT_def,
  -- Define `V i` to be the pullback of `U i`.
  set V : ι → set X := λ i, f ⁻¹' (U i) with hV_def,
  -- Let's check that the V's are open and cover `S`.
  specialize hS V _, swap,
  -- first let's check they're open.
  { intro i,
    rw hV_def, dsimp only,
    apply continuous.is_open_preimage hf _ (hU i) },
  specialize hS _, swap,
  -- Now let's check they cover `S`.
  { intros x hx,
    have hfx : f x ∈ T,
    { rw hT_def, 
      rw mem_image,
      use x,
      use hx },
    specialize hcoverU hfx,
    rw mem_Union at hcoverU ⊢,
    -- and now we could take everything apart and then re-assemble,
    -- but `x ∈ f⁻¹' U` and `f x ∈ U` are equal by definition!
    exact hcoverU -- abuse of definitional equality!
  },
  -- Now let's take a finite subset `F : set ι` such that the `V i` for `i ∈ F`
  -- cover S.
  rcases hS with ⟨F, hFfinite, hF⟩,
  -- I claim that this `F` gives us the finite subcover.
  use F,
  -- It's certainly finite.
  use hFfinite,
  -- Let's check it covers. Say `y : Y` is in `T`.
  rintros y ⟨x, hxs, rfl⟩,
  -- then `y = f x` for some `x : X`, and `x ∈ S`.
  rw subset_def at hF, -- this is definition so this line can be deleted.
  -- then x is in the union of the `V i` for `i ∈ F`.
  specialize hF x hxs,
  -- so it's in one of the `V i`
  rw mem_bUnion_iff at hF ⊢,
  -- and now we could take everything apart and then re-assemble,
  -- but `x ∈ f⁻¹' U` and `f x ∈ U` are equal by definition!
  exact hF,
end

/-

## Closed subset of a compact is compact.

This is a little trickier because given `U : ι → set X` we need
to produce `V : option ι → set X` at some point in the below
proof. We can make it using `option.rec`.

If `S` is compact and `C` is closed then we want to prove `S ∩ C` is compact.

Start with `rw compact_iff_finite_subcover' at hS ⊢,`.

Then given a cover `U : ι → set X`, define
`V : option ι → set X` like this:

`let V : option ι → set X := λ x, option.rec Cᶜ U x,`

-/
lemma closed_of_compact (S : set X) (hS : is_compact S)
  (C : set X) (hC : is_closed C) : is_compact (S ∩ C) :=
begin
  rw compact_iff_finite_subcover' at hS ⊢,
  intros ι U hUopen hSCcover,
  let V : option ι → set X := λ x, option.rec Cᶜ U x,
  specialize hS V _, swap,
  { intros i,
    cases i with i,
    { change is_open Cᶜ,
      rwa is_open_compl_iff },
    { change is_open (U i),
      apply hUopen } },
  specialize hS _, swap,
  { intro x,
    intro hxS,
    by_cases hxC : x ∈ C,
    { rw subset_def at hSCcover,
      specialize hSCcover x ⟨hxS, hxC⟩,
      rw mem_Union at ⊢ hSCcover,
      cases hSCcover with i hi,
      use (some i),
      exact hi },
    { rw mem_Union,
      use none } },
  rcases hS with ⟨F, hFfinite, hFcover⟩,
  use (some : ι → option ι) ⁻¹' F,
  split,
  { -- hard
    apply finite.preimage _ hFfinite,
    intros i hi j hj,
    exact option.some_inj.mp },
  rintros x ⟨hxS, hxC⟩,
  rw subset_def at hFcover,
  specialize hFcover x hxS,
  rw mem_bUnion_iff at hFcover ⊢,
  rcases hFcover with ⟨i, hiF, hxi⟩,
  cases i with i,
  { exfalso, 
    contradiction },
  use i,
  use hiF,
  exact hxi,
end

