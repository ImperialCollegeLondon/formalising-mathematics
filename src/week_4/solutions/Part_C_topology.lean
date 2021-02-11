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

-- Let X and Y be topological spaces, and let `f : X → Y` be a map.
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
saying that `Z : set ι` is finite. You can ignore this proof.
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

Useful theorems:

`continuous.is_open_preimage` -- preimage of an open set under a
continuous map is open.

`is_open_compl_iff` -- complement `Sᶜ` of `S` is open iff `S` is closed.

## Some useful tactics:

### `specialize`

`specialize` can be used with `_`. If you have a hypothesis

`hS : ∀ {ι : Type} (U : ι → set X), (∀ (i : ι), is_open (U i)) → ...`

and `U : ι → set X`, then

`specialize hS U` will change `hS` to 

`hS : (∀ (i : ι), is_open (U i)) → ...`

But what if you now want to prove `∀ i, is_open (U i)` so you can feed it
into `hS` as an input? You can put

`specialize hS _`

and then that goal will pop out. Unfortunately it pops out _under_ the
current goal! You can swap two goals with the `swap` tactic though :-)

### `change`

If your goal is `⊢ P` and `P` is definitionally equal to `Q`, then you
can write `change Q` and the goal will change to `Q`. Sometimes useful
because rewriting works up to syntactic equality, which is stronger
than definitional equality.

### `rwa`

`rwa h` just means `rw h, assumption`

### `contradiction`

If you have `h1 : P` and `h2 : ¬ P` as hypotheses, then you can prove any goal with
the `contradiction` tactic, which just does `exfalso, apply h2, exact h1`.

### `set`

Note : The `set` tactic is totally unrelated to the `set X` type of subsets of `X`!

The `set` tactic can be used to define things. For example
`set T := f '' S with hT_def,` will define `T` to be `f '' S`
and will also define `hT_def : T = f '' S`.

-/

#check is_open_compl_iff
lemma image_compact_of_compact (hf : continuous f) (S : set X) (hS : is_compact S) :
  is_compact (f '' S) :=
begin
  -- proof I recommend:
  -- (1) cover f''s with opens. Want finite subcover
  -- (2) pull back
  -- (3) finite subcover
  -- (4) push forward

  -- start by changing `is_compact` to something we can work with.
  rw compact_iff_finite_subcover' at hS ⊢,
  -- Define `T` to be `f '' S` -- why not?
  set T := f '' S with hT_def,
  -- Now `T = f '' S` and `hT_def` tells us that.
  -- Note that `set T := ...` is about the *tactic* `set`.

  -- OK let's go.
  -- Say we have a cover of `f '' S` by opens `U i` for `i : ι`.
  intro ι,
  intro U,
  intro hU,
  intro hcoverU,
  
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

For finiteness, if you have `F : set (option ι)` and `hF : F.finite`,
and you want `(some ⁻¹' F).finite`, then you can apply
`set.finite.preimage` and use `option.some_inj` to deal with the
injectivity.
-/
lemma closed_of_compact (S : set X) (hS : is_compact S)
  (C : set X) (hC : is_closed C) : is_compact (S ∩ C) :=
begin
  rw compact_iff_finite_subcover' at hS ⊢,
  -- take a cover of S ∩ C by a family U of opens indexed by ι
  intros ι U hUopen hSCcover,
  -- Now let's define a family V of opens by V = U plus 
  -- one extra set, Cᶜ. This family is indexed by `option ι`.
  let V : option ι → set X := λ x, option.rec Cᶜ U x,
  -- I claim that V is an open cover of the compact set S.
  specialize hS V _, swap,
  { -- First let's check that V i is always open
    intros i,
    -- two cases
    cases i with i,
    { -- Cᶜ is open 
      change is_open Cᶜ,
      rwa is_open_compl_iff },
    { -- U i are open
      change is_open (U i),
      apply hUopen } },
  specialize hS _, swap,
  { -- Now I claim they cover S
    intro x,
    intro hxS,
    -- if x ∈ S then it's either in C
    by_cases hxC : x ∈ C,
    { -- so it's hit by some U i
      rw subset_def at hSCcover,
      specialize hSCcover x ⟨hxS, hxC⟩,
      rw mem_Union at ⊢ hSCcover,
      cases hSCcover with i hi,
      use (some i),
      exact hi },
    { -- or it's not
      rw mem_Union,
      -- in which case it's in Cᶜ
      use none } },
  -- So the V's have a finite subcover.
  rcases hS with ⟨F, hFfinite, hFcover⟩,
  -- I claim that those V's which are U's are a finite subcover of S ∩ C
  use (some : ι → option ι) ⁻¹' F,
  split,
  { -- This cover is finite
    apply finite.preimage _ hFfinite,
    intros i hi j hj,
    exact option.some_inj.mp },
  -- and if x ∈ S ∩ C,
  rintros x ⟨hxS, hxC⟩,
  rw subset_def at hFcover,
  specialize hFcover x hxS,
  -- then it's in S
  rw mem_bUnion_iff at hFcover ⊢,
  -- so it's covered by the V's
  rcases hFcover with ⟨i, hiF, hxi⟩,
  -- and it's not in Cᶜ
  cases i with i,
  { contradiction },
  -- so it's in one of the U's.
  { use [i, hiF, hxi] },
end

