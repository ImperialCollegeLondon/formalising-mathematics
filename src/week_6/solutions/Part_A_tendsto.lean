import order.filter.basic

/-

# tendsto

If `X` and `Y` are types, `φ : X → Y` is a function,
and `F : filter X` and `G : filter Y` are filters, then

`filter.tendsto φ F G`

is a true-false statement, which is pronounced something like
"`F` tends to `G` along `φ`". Of course we will `open filter`
in this file, so you can just write `tendsto φ F G`, or if
you like the dot notation you can even write `F.tendsto φ G`.

## Geometric meaning of `tendsto`.

Let's start by thinking about the easy case where `F` and `G`
are actually subsets of `X` and `Y` (that is, principal filters,
associated to sets which we will also call `F` and `G`). In this case,
`tendsto φ F G` simply means "`φ` restricts to a function
from `F` to `G`", or in other words `∀ x ∈ F, φ(x) ∈ G`.

There are two other ways of writing this predicate. The first
involves pushing a set forward along a map. If `F` is a subset of `X`
then let `φ(F)` denote the image of `F` under `φ`, that
is, the subset `{y : Y | ∃ x : X, φ x = y}` of `Y`.
Then `tendsto φ F G` simply means `φ(F) ⊆ G`.

The second involves pulling a set back along a map. If `G` is a subset
of `Y` then let `φ⁻¹(G)` denote the preimage of `G` under `φ`,
that is, the subset `{x : X | φ x ∈ G}` of `Y`. Then `tendsto φ F G`
simply means `F ⊆ φ⁻¹(G)`. 

This is how it all works in the case of sets. What we need to
do today is to figure out how to push forward and pull back
filters along a map `φ`. Once we have done this, then we can
prove `φ(F) ≤ G ↔ F ≤ φ⁻¹(G)` and use either one of these
as our definition of `tendsto φ F G` -- it doesn't matter which.

## Digression : adjoint functors.

The discussion below is not needed to be able to do this week's
problems, but it might provide some helpful background for some.
Also note that anyone who still doens't like the word "type" can
literally just change it for the word "set" (and change "term of
type" to "element of set"), which is how arguments
of the below kind would appear in the traditional mathematical
literature.

Partially ordered types, such as the type of subsets of a fixed
type `X` or the type of filters on `X`, are actually very simple
examples of categories. In general if `P` is a partially ordered type
and `x,y` are terms of type `P` then the idea is that we can
define `Hom(x,y)` to have exactly one element if `x ≤ y` is true,
and no elements at all if `x ≤ y` is false. The structure/axioms for
a category are that `Hom(x,x)` is supposed to have an identity
element, which follows from reflexivity of `≤`, and that one can
compose morphisms, which follows from transitivity of `≤`.
Antisymmetry states that if two objects are isomorphic (i.e.,
in this case, if `Hom(x,y)` and `Hom(y,x)` are both nonempty),
then they are equal. If `φ : X → Y` is a map of types, then
pushing forward subsets and pulling back subsets are both
functors from `set X` to `set Y`, because `S ⊆ T → φ(S) ⊆ φ(T)`
and `U ⊆ V → φ⁻¹(U) ⊆ φ⁻¹(V)`. The statement that
`φ(S) ≤ U ↔ S ≤ φ⁻¹(U)` is simply the statement that these functors
are adjoint to each other. Today we will define pushforward and
pullback of filters, and show that they are also a pair of
adjoint functors, but we will not use this language. In fact there
is a special language for adjoint functors in this simple situation:
we will say that pushforward and pullback form a Galois connection.

-/

/-

## Warm-up: pushing forward and pulling back subsets.

Say `X` and `Y` are types, and `f : X → Y`.

-/

variables (X Y : Type) (f : X → Y)

/-

### images

In Lean, the image `f(S)` of a subset `S : set X` cannot
be denoted `f S`, because `f` expects an _element_ of `X` as
an input, not a subset of `X`, so we need new notation.

Notation : `f '' S` is the image of `S` under `f`. Let's
check this.

-/

example (S : set X) : f '' S = {y : Y | ∃ x : X, x ∈ S ∧ f x = y} :=
begin
  -- true by definition
  refl
end

/-

### preimages

In Lean, the preimage `f⁻¹(T)` of a subset `T : set Y` cannot
be denoted `f⁻¹ T` because `⁻¹` is the inverse notation in group
theory, so if anything would be a function from `Y` to `X`,
not a function on subsets of `Y`. 

Notation : `f ⁻¹' T` is the preimage of `T` under `f`. Let's
check this.

Pro shortcut: `\-'` for `⁻¹'` 

-/

example (T : set Y) : f ⁻¹' T = {x : X | f x ∈ T} :=
begin
  -- true by definition
  refl
end

/-

I claim that the following conditions on `S : set X` and `T : set Y`
are equivalent:

1) `f '' S ⊆ T`
2) `S ⊆ f⁻¹' T`

Indeed, they both say that `f` restricts to a function from `S` to `T`.
Let's check this. You might find

`mem_preimage : a ∈ f ⁻¹' s ↔ f a ∈ s`

and 

-/

open set

example (S : set X) (T : set Y) : f '' S ⊆ T ↔ S ⊆ f⁻¹' T :=
begin
  split,
  { intros h x hxS,
    -- rw subset_def at h,
    -- rw mem_preimage,
    apply h,
    use [x, hxS, rfl] },
  { rintros h - ⟨x, hxS, rfl⟩,
    exact h hxS }
end

/-

## Pushing forward filters.

Pushing forward is easy, so let's do that first.
It's called `filter.map` in Lean.

We define the pushforward filter `map f F` on `Y` to be the
obvious thing: a subset of `Y` is in the filter iff `f⁻¹(Y)`
is in `F`. Let's check this is a filter.  

Reminder of some helpful lemmas:

In `set`:
`mem_set_of_eq : a ∈ {x : α | p x} = p a` -- definitional

In `filter`:
`univ_mem_sets : univ ∈ F`
`mem_sets_of_superset : S ∈ F → S ⊆ T → T ∈ F`
`inter_mem_sets : S ∈ F → T ∈ F → S ∩ T ∈ F`

-/

open filter

-- this is called `F.map f` or `filter.map f F` 
-- or just `map f F` if `filter` is open.
example (F : filter X) : filter Y :=
{ sets := {T : set Y | f ⁻¹' T ∈ F },
  univ_sets := begin
--    rw mem_set_of_eq,
    exact univ_mem_sets,
  end,
  sets_of_superset := begin
    intros S T hS hST,
    --rw mem_set_of_eq at *,
    refine mem_sets_of_superset hS _,
    intros x hx,
    exact hST hx,
  end,
  inter_sets := begin
    intros S T,
    -- I am abusing definitional equality
    exact inter_mem_sets,
  end, }

-- this is `filter.mem_map` and it's true by definition.
example (F : filter X) (T : set Y) : T ∈ F.map f ↔ f ⁻¹' T ∈ F :=
begin
  -- true by definition
  refl
end

-- Let's check that map satisfies some basic functorialities.
-- Recall that if your goal is to check two filters are
-- equal then you can use the `ext` tactic.

-- pushing along the identity map id : X → X doesn't change the filter.
-- this is `filter.map_id` but see if you can prove it yourself.
example (F : filter X) : F.map id = F :=
begin
  ext S,
  refl,
end

-- pushing along g ∘ f is the same as pushing along f and then g
-- for some reason this isn't in mathlib, instead they have `map_map` which
-- has the equality the other way.
variables (Z : Type) (g : Y → Z)

-- this isn't in mathlib, but `filter.map_map` is the equality the other
-- way around. See if you can prove it yourself.
example (F : filter X) : F.map (g ∘ f) = (F.map f).map g :=
begin
  ext S,
  refl,
end

open_locale filter -- for 𝓟 notation

-- pushing the principal filter `𝓟 S` along `f` gives `𝓟 (f '' S)`
-- this is `filter.map_principal` but see if you can prove it yourself.
example (S : set X) : (𝓟 S).map f = 𝓟 (f '' S) :=
begin
  ext T,
--  rw mem_map,
--  rw mem_principal_sets,
--  rw mem_principal_sets,
  split,
  { rintro h y ⟨x, hx, rfl⟩,
    exact h hx },
  { rintro h x hx, 
    apply h,
    exact ⟨x, hx, rfl⟩ }
end

/-

## tendsto

The definition: if `f : X → Y` and `F : filter X` and `G : filter Y`
then `tendsto f F G : Prop := map f F ≤ G`. This is a definition (it
has type `Prop`), not the proof of a theorem. It is a true-false statement
attached to `f`, `F` and `G`, it's a bit like saying "f is continuous at x"
or something like that, it might be true and it might be false.

The mental model you might want to have of the definition is that
`tendsto f F G` means that the function `f` restricts to a function
from the generalized set `F` to the generalized set `G`.

-/

-- this is `filter.tendsto_def`
example (F : filter X) (G : filter Y) :
  tendsto f F G ↔ ∀ T : set Y, T ∈ G → f ⁻¹' T ∈ F :=
begin
  -- true by definition
  refl
end

-- Let's make a basic API for `tendsto`

-- this is `tendsto_id` but see if you can prove it yourself.
example (F : filter X) : tendsto id F F :=
begin
  intro S,
  exact id,
end

-- this is `tendsto.comp` but see if you can prove it yourself
example (F : filter X) (G : filter Y) (H : filter Z)
  (f : X → Y) (g : Y → Z)
  (hf : tendsto f F G) (hg : tendsto g G H) : tendsto (g ∘ f) F H :=
begin
  rintro S hS,
  specialize hg hS,
  specialize hf hg,
  exact hf,
end

-- I would recommend looking at the model answer to this one if
-- you get stuck.
lemma tendsto_comp_map (g : Y → Z) (F : filter X) (G : filter Z) :
  tendsto (g ∘ f) F G ↔ tendsto g (F.map f) G :=
begin
  refl, -- Both sides are the same, by definition. Think about it on paper!
end

/-

## Appendix : Pulling back filters

We don't use this in the next part.

Say `f : X → Y` and `G : filter Y`, and we want a filter on `X`. Let's make a
naive definition. We want a collection of subsets of `X` corresponding to the
filter obtained by pulling back `G` along `f`. When should `S : set X` be
in this filter? Perhaps it is when `f '' S ∈ G`. However, there is no reason
that the collection of `S` satisfying this property should be a filter
on `X`. For example, there is no reason to espect that `f '' univ ∈ G`
if `f` is not surjective. 

Here's a way of fixing this. Remember that our model of a filter `G` is some
kind of generalised notion of a set. If `T : set Y` then `T ∈ G` is supposed to
mean that the "set" `G` is a subset of `T`. So this should imply
that `f⁻¹(G) ⊆ f⁻¹(T)`. In particular, if `T ∈ G` and `f⁻¹(T) ⊆ S` then this
should mean `f⁻¹(G) ⊆ S` and hence `S ∈ f⁻¹(G)`. Let's try this and see if
it works.

Random useful lemmas (you might be getting to the point where you can
guess the names of the lemmas):

`subset_univ S : S ⊆ univ`
`subset.trans : A ⊆ B → B ⊆ C → A ⊆ C`
-/

-- this is called filter.comap
example (G : filter Y) : filter X :=
{ sets := {S : set X | ∃ T ∈ G, f ⁻¹' T ⊆ S},
  univ_sets := begin
    use univ,
    split,
    { exact univ_mem_sets },
    { exact subset_univ _ }
  end,
  sets_of_superset := begin
    rintros S T ⟨U, hUG, hUS⟩ hST,
    use [U, hUG],
    exact subset.trans hUS hST
  end,
  inter_sets := begin
    rintro S T ⟨U, hUG, hUS⟩ ⟨V, hVG, hVT⟩,
    use [U ∩ V, inter_mem_sets hUG hVG],
    rintro x ⟨hxU, hxV⟩,
    exact ⟨hUS hxU, hVT hxV⟩, 
  end }

-- Let's call this mem_comap
lemma mem_comap (f : X → Y) (G : filter Y) (S : set X) :
  S ∈ comap f G ↔ ∃ T ∈ G, f ⁻¹' T ⊆ S :=
begin
  -- true by definition
  refl
end

-- If you want to, you can check some preliminary properties of `comap`. 

-- this is comap_id
example (G : filter Y) : comap id G = G :=
begin
  ext S,
  rw mem_comap,
  split,
  { rintro ⟨T, hT, h⟩,
    exact mem_sets_of_superset hT h,
  },
  { intro hS,
    use [S, hS],
    refl }
end

-- this is comap_comap but the other way around
lemma comap_comp (H : filter Z) : comap (g ∘ f) H = comap f (comap g H) :=
begin
  ext S,
  simp only [mem_comap],
  split,
  { rintro ⟨U, hU, h⟩,
    use g ⁻¹' U,
    refine ⟨_, h⟩,
    rw mem_comap,
    use [U, hU] },
  { rintro ⟨T, ⟨U, hU, h2⟩, h⟩,
    use [U, hU],
    refine subset.trans _ h,
    intros x hx,
    exact h2 hx }
end

-- this is comap_principal. Remember `mem_principal_sets`!
example (T : set Y) : comap f (𝓟 T) = 𝓟 (f ⁻¹' T) :=
begin
  ext S,
--  rw mem_comap,
--  rw mem_principal_sets,
  split,
  { rintro ⟨U, hU, h⟩,
    refine subset.trans (λ x, _) h,
    apply hU },
  { intro h,
    exact ⟨T, mem_principal_self T, h⟩ }
end


-- This is the proof that `map f` and `comap f` are adjoint functors,
-- or in other words form a Galois connection. It is the "generalised set"
-- analogue of the assertion that if S is a subset of X and T is a subset of Y
-- then f(S) ⊆ T ↔ S ⊆ f⁻¹(T), these both being ways to say that `f` restricts
-- to a function from `S` to `T`.
lemma filter.galois_connection (F : filter X) (G : filter Y) : 
  map f F ≤ G ↔ F ≤ comap f G :=
begin
  split,
  { rintro h S ⟨T, hT, hTS⟩,
    rw le_def at h,
    exact mem_sets_of_superset (h T hT) hTS },
  { rintro h T hT,
    rw le_def at h,
    exact h (f ⁻¹' T) ⟨T, hT, subset.refl _⟩ },
end

-- indeed, `map f` and `comap f` form a Galois connection.
example : galois_connection (map f) (comap f) :=
filter.galois_connection X Y f 