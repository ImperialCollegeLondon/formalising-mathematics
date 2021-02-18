import order.filter.basic -- the basics

/-
# Filters

## Introduction

A topological space structure on a type `α` is a collection of subsets of `α`
(the open sets) satisfying some axioms. A filter is a similar kind of thing --
it's a collection of subsets of `α` satisfying some different axioms.

Before we go into the formal definition, let us start with the picture.
A filter on `α` is an extremely powerful generalisation of the concept
of a subset of `α`. If `S : set α` is a subset, then there is a principal
filter `𝓟 S` corresponding to `S` -- it is just the collection of all subsets
of `α` which contain `S`. However there may be other filters on `α`
corresponding to things which are a bit more general than subsets. For example
if `α` is a topological space and `x : α` then there is a filter `𝓝 x`
corresponding to "an infinitesimal neighbourhood of `x`" even if
there is no smallest open set containing `x`. As another example, if `α` has an
ordering then there is a filter of "neighbourhoods of infinity" on `α` even
though there might be no `∞` in `α`.

If `F` is a filter, then you can think of `F` as a generalised kind of
subset `F` of `α`, and you should think of `S ∈ F` as meaning `F ⊆ S`.
Keeping this in mind will help to motivate the axioms below. 

## Definition

Here's the formal definition. A filter on `α` is a collection `F` of subsets
of `α` satisfying the following three axioms:

1) `α ∈ F` (in Lean this is written `univ ∈ F` because a distinction is made
between the type `α` and the term `univ : set α` corresponding to `α`)

2) If `S ∈ F` and `S ⊆ T` then `T ∈ F` -- i.e. `F` is "upwards-closed",

3) If `A ∈ F` and `B ∈ F` then `A ∩ B ∈ F` -- i.e. `F` is closed under
binary intersections.

Note that (1) and (3) together imply (and are indeed equivalent to)
the statement that `F` is closed under all finite intersections,
i.e. the intersection of finitely many elements of `F` is in `F`. 

Here's the Lean definition:

```
structure filter (α : Type*) :=
(sets                   : set (set α))
(univ_sets              : set.univ ∈ sets)
(sets_of_superset {x y} : x ∈ sets → x ⊆ y → y ∈ sets)
(inter_sets {x y}       : x ∈ sets → y ∈ sets → x ∩ y ∈ sets)
```

In words, `filter α` is the type of filters on `α`, so to give a filter
on `α` is to give a term `F : filter α` of type `filter α`. To make a term
of type `filter α` you need to give a collection `sets` of subsets of `α`
and then three proofs of the three axioms.

A rather simple example of a filter is the filter of *all* subsets of `α`.
Those of you who have seen definitions of filters in other places (for
example in Bourbaki) might have seen an extra axiom in the definition of a
filter, saying that a filter is not allowed to be the collection of all
subsets of `α`. This turns out to be rather an unnatural axiom, it is like
demanding in ideal theory that if `R` is a ring then `R` is not allowed to be
an ideal of `R`. An advantage of such a definition of an ideal would be that
a maximal ideal of `R` would literally be a maximal element of the ideals
of `R`, but this advantage is outweighed by the disadvantage that the
definition then becomes much less functorial -- e.g. the image of an ideal
along a ring homomorphism might not be an ideal, you cannot in general add two
ideals etc). To preserve the functoriality of filters, mathlib does not have
this Bourbaki axiom as an axiom for filters. As a result there are two
"extreme" filters on `α`, namely the one which only contains
`univ` (note that this is forced by `univ_sets`), and then the one we mentioned
above, which contains all subsets of `α`. These two filters are called
`⊥` and `⊤`, although you might be surprised to find out which one is which!
The filter consisting of all subsets of `α` is the one corresponding to
the empty set, so it is `⊥`, and the one consisting of just `univ` is the
one corresponding to the whole of `α` so it is `⊤`.

## Notation, helpful tactics and helpful theorems

We are not going to build filters from first principles, we will be
using Lean's API for filters. 

Say `α : Type` and `F : filter α` and `S : set α`. The notation `S ∈ F` is
defined to mean `S ∈ F.sets`. 

The `ext` tactic can be used to reduce a goal `F = G` to a goal of
the form `∀ S, S ∈ F ↔ S ∈ G`.

The fields of the structure mention things like `S ∈ F.sets`, so the
axioms are restated with different names, but using the `S ∈ F` notation.
The lemmas corresponding to the definitions are:

`univ_mem_sets : univ ∈ F`
`mem_sets_of_superset : S ∈ F → S ⊆ T → T ∈ F`
`inter_mem_sets : S ∈ F → T ∈ F → S ∩ T ∈ F`

These lemmas in the `filter` namespace, i.e. their full names are
`filter.univ_mem_sets` etc. But we are about to say `open filter`
which means that you don't have to type this `filter.` thing in front of every
lemma you need about filters. In fact we'll also be using a bunch of
stuff about sets, like `set.inter_subset_left`, so why don't we `open set`
as well.
-/

open filter set

-- Variables!
-- let `α` be a type, let `F` be a filter on `α`, and let `S` and `T`
-- denote subsets of `α`.

variables (α : Type) (F : filter α) (S T : set α)

/-
Here's a lemma about filters: Two sets `S` and `T` are both in
a filter `F` iff their intersection is. See if you can deduce
it from the axioms of a filter.

For this one it's useful to know the following results (from the set namespace)
`inter_subset_left S T : S ∩ T ⊆ S`
and
`inter_subset_right S T : S ∩ T ⊆ S`
-/
example : S ∩ T ∈ F ↔ S ∈ F ∧ T ∈ F :=
begin
  sorry,
end

/-
The principal filter `𝓟 X` generated by `X : set α` is the subsets of `α`
which contain `X`. Prove that it's a filter.

Helpful for this exercise:
`mem_univ s : s ∈ univ`
`subset.trans : A ⊆ B → B ⊆ C → A ⊆ C`
`subset_inter : X ⊆ S → X ⊆ T → X ⊆ S ∩ T`
(note that you could probably prove those last two things directly yourself,
but we may as well use the interface for sets given that it's there)
`mem_set_of_eq : x ∈ {a : α | p a} = p x`
(this one is definitional, so you could use `change` instead, or just
not rewrite it at all)
-/

-- this is called `𝓟 X` in mathlib but let's just make it ourselves.
example (X : set α) : filter α :=
{ sets := {S : set α | X ⊆ S},
  univ_sets := begin
    sorry,
  end,
  sets_of_superset := begin
    sorry,
  end,
  inter_sets := begin
    sorry,
  end }

-- The notation for the principal filter generated by `X : set α` is `𝓟 X`.
-- This notation is in the "filter locale", which is just a posh way
-- of saying that you have to type

open_locale filter

-- in order to get the notation.

/-

## The order (≤) on filters

The following is unsurprising: the collection of all filters on `α` is
partially ordered. Perhaps more surprising: the order is the other way
around to what you think it should be! If `F` and `G` are filters
on `α`, then `F ≤ G` is defined to mean that `G.sets ⊆ F.sets`, i.e.
every set in the `G`-filter is also in the `F`-filter. Why is this?
Well, think about principal filters. If `S ⊆ T` are two subsets,
then `X ∈ 𝓟 T` implies `T ⊆ X`, so `S ⊆ X`, so `X ∈ 𝓟 S`. 
The smaller the set, the bigger the collection of sets in the filter.

Let's formalise this. Show that 𝓟 S ≤ 𝓟 T ↔ S ⊆ T.
Note that this is called `principal_mono` in mathlib but 
there's no harm in proving it yourself.

Some helpful lemmas:
`mem_principal_sets : T ∈ 𝓟 S ↔ S ⊆ T`
`mem_principal_self S : S ∈ 𝓟 S`
`le_def : F ≤ G ↔ ∀ (S : set α), S ∈ G → S ∈ F`
-/
example (S T : set α) : 𝓟 S ≤ 𝓟 T ↔ S ⊆ T :=
begin
  sorry,
end

-- Here's another useful lemma about principal filters.
-- It's called `le_principal_iff` in mathlib but why
-- not try proving it yourself?

example : F ≤ 𝓟 S ↔ S ∈ F :=
begin
  sorry,
end



/-

## Filters are a complete lattice

Just like it's possible to talk about the topological space generated
by a collection of subsets of `α` -- this is the smallest topology
for which the given subsets are all open -- it's also possible to talk
about the filter generated by a collection of subsets of `α`. One
can define it as the intersection of all the filters that contain your
given collection of subsets.

In order theory, given a partial order (like the partial order on filters)
you can start asking whether infs and sups exist. Filters are an example
where all these things exist (finite and infinite infs and sups) and they
satisfy a natural collection of axioms, making them into what is called a
*complete lattice*. One can prove this by showing that "filter generated by
these sets" and "underlying sets of a filter" are adjoint functors and then
using the theory of Galois insertions. I talked about this a bit when doing
subgroups, and won't talk about it again.

-/

/-

## Other examples of filters.

### `at_top` filter on a totally ordered set

Let `L` be a non-empty totally ordered set. Let's say that a subset `X` of `L` is
"big" if there exists `x : L` such for all `y ≥ x`, `y ∈ X`.

I claim that the big subsets are a filter. Check this. The mathematical idea
is that the "big subsets" are the neighbourhoods of `∞`, so the corresponding
filter is some representation of an infinitesimal neighbourhood of `∞`.

Implementation notes: `linear_order L` is the type of linear orders on `L`.
`e : L` is just an easy way of saying that `L` is nonempty.

Recall that `max x y` is the max of x and y in a `linear_order`, and
`le_max_left a b : a ≤ max a b` and similarly `le_max_right`. 
-/
def at_top (L : Type) [linear_order L] (e : L) : filter L :=
{ sets := {X : set L | ∃ x : L, ∀ y, x ≤ y → y ∈ X},
  univ_sets := begin
    sorry,
  end,
  sets_of_superset := begin
    sorry,
  end,
  inter_sets := begin
    sorry,
  end }

/-
 
### the cofinite filter

The _cofinite filter_ on a type `α` has as its sets the subsets `S : set α`
with the property that `Sᶜ`, the complement of `S`, is finite.
Let's show that these are a filter.

Things you might find helpful:

`compl_univ : univᶜ = ∅`
`finite_empty : finite ∅`
`compl_subset_compl : Xᶜ ⊆ Yᶜ ↔ Y ⊆ X`
`finite.subset : S.finite → ∀ {T : set α}, T ⊆ S → T.finite`
`compl_inter S T : (S ∩ T)ᶜ = Sᶜ ∪ Tᶜ`
`finite.union : S.finite → T.finite → (S ∪ T).finite`

NB if you are thinking "I could never use Lean by myself, I don't know
the names of all the lemmas so I have to rely on Kevin telling them all to
me" then what you don't realise is that I myself don't know the names
of all the lemmas either -- I am literally just guessing them and pressing
ctrl-space to check. Look at the names of the lemmas and begin to understand
that you can probably guess them yourself.
-/

def cofinite (α : Type) : filter α :=
{ sets := { S : set α | (Sᶜ).finite },
  univ_sets := begin
    sorry,
  end,
  sets_of_superset := begin
    sorry,
  end,
  inter_sets := begin
    sorry,
  end }

/-

### Exercises (to do on paper):

You don't need to be able to do these in order to move onto the topology part
of this workshop.

(1) prove that the cofinite filter on a finite type is the entire power set filter.
(2) prove that the cofinite filter on `ℕ` is equal to the `at_top` filter.
(3) Prove that the cofinite filter on `ℤ` is not equal to the `at_top` filter.
(4) Prove that the cofinite filter on `ℕ` is not principal.

You can try them in Lean but you will have to be a master of finiteness.
Here, for example, are some of the ideas you'll need to do (4) in Lean.
The proof uses a bunch of lemmas from the set API.

Here are some of the things I used:

`filter.ext_iff : F = G ↔ ∀ (S : set α), s ∈ F ↔ s ∈ G`

Facts about `S \ {a}` and other sets:

`diff_eq_compl_inter`, `compl_inter`, `compl_compl`, `finite_singleton`,
`mem_diff_singleton`.

I also needed the following two lemmas, which weren't in mathlib
so I had to prove them myself (my proof of the first one was longer;
thanks to Yakov Pechersky on Zulip for coming up with the one-linear)
-/

lemma infinite_of_finite_compl {α : Type} [infinite α] {s : set α}
  (hs : sᶜ.finite) : s.infinite :=
λ h, set.infinite_univ (by simpa using hs.union h)

lemma set.infinite.nonempty {α} {s : set α} (h : s.infinite) : ∃ a : α, a ∈ s :=
let a := set.infinite.nat_embedding s h 37 in ⟨a.1, a.2⟩

-- This is also convenient for rewriting purposes:
lemma mem_cofinite {S : set ℕ} : S ∈ cofinite ℕ ↔ Sᶜ.finite :=
begin
  -- true by definition
  refl
end

-- Here's a proof which I formalised: if natural_cofinite = 𝓟 S then S must
-- be cofinite and hence infinite and hence non-empty, but then if a ∈ S
-- then S \ {a} causes us problems as it's cofinite but doesn't contain `S`.
-- This is harder than anything else in this file and is not necessary
-- for the application to topological spaces in Part B so feel free
-- to skip it.
theorem cofinite_not_principal : ∀ S : set ℕ, cofinite ℕ ≠ 𝓟 S :=
begin
  sorry,
end
