import week_2.kb_solutions.Part_A_groups_solutions

/-!

## Subgroups

We define the structure `subgroup G`, whose terms are subgroups of `G`.
A subgroup of `G` is implemented as a subset of `G` closed under
`1`, `*` and `⁻¹`.

-/

namespace xena

/-- A subgroup of a group G is a subset containing 1
and closed under multiplication and inverse. -/
structure subgroup (G : Type) [group G] :=
(carrier : set G)
(one_mem' : (1 : G) ∈ carrier)
(mul_mem' {x y} : x ∈ carrier → y ∈ carrier → x * y ∈ carrier)
(inv_mem' {x} : x ∈ carrier → x⁻¹ ∈ carrier)

/-

At this point, here's what we have.

A term `H` of type `subgroup G`, written `H : subgroup G`, is a
*quadruple*. To give a term `H : subgroup G` is to give the following four things:
1) `H.carrier` (a subset of `G`),
2) `H.one_mem'` (a proof that `1 ∈ H.carrier`),
3) `H.mul_mem'` (a proof that `H` is closed under multiplication)
4) `H.inv_mem'` (a proof that `H` is closed under inverses).

Note in particular that Lean, being super-pedantic, *distinguishes* between
the subgroup `H` and the subset `H.carrier`. One is a subgroup, one is
a subset. When we get going we will start by setting up some infrastructure
so that this difference will be hard to notice.

Note also that if `x` is in the subgroup `H` of `H` then the _type_ of `x` is still `G`,
and `x ∈ carrier` is a Proposition. Note also that `x : carrier` doesn't
make sense (`carrier` is a term, not a type, rather counterintuitively).

-/

namespace subgroup

open xena.group

-- let G be a group and let H and K be subgroups
variables {G : Type} [group G] (H J K : subgroup G)

/-
This `h ∈ H.carrier` notation kind of stinks. I don't want to write `H.carrier`
everywhere, because I want to be able to identify the subgroup `H` with
its underlying subset `H.carrier`. Note that these things are not _equal_,
firstly because `H` contains the proof that `H.carrier` is a subgroup, and
secondly because these terms have different types! `H` has type `subgroup G`
and `H.carrier` has type `set G`. Let's start by sorting this out.
-/

-- If `x : G` and `H : subgroup G` then let's define the notation
-- `x ∈ H` to mean `x ∈ H.carrier`
instance : has_mem G (subgroup G) := ⟨λ m H, m ∈ H.carrier⟩

-- Let's also define a "coercion", a.k.a. an "invisible map"
-- from subgroups of `G` to subsets of `G`, sending `H` to `H.carrier`. 
-- The map is not completely invisible -- it's a little ↑. So
-- if you see `↑H` in the future, it means the subset `H.carrier` by definition.
instance : has_coe (subgroup G) (set G) := ⟨λ H, H.carrier⟩

-- `λ` is just computer science notation for ↦ (mapsto); so
-- `λ H, H.carrier` is the function `H ↦ H.carrier`.

-- Let's check we have this working, and also tell the simplifier that we
-- would rather talk about `g ∈ H` than any other way of saying it.

/-- `g` is in the underlying subset of `H` iff `g ∈ H`. -/
@[simp] lemma mem_carrier {g : G} : g ∈ H.carrier ↔ g ∈ H :=
begin
  -- true by definition
  refl
end

/-- `g` is in `H` considered as a subset of `G`, iff `g` is in `H` considered
as subgroup of `G`. -/
@[simp] lemma mem_coe {g : G} : g ∈ (↑H : set G) ↔ g ∈ H :=
begin
  -- true by definition
  refl
end

-- Now let's define theorems without the `'`s in, which use this
-- more natural notation

/-- A subgroup contains the group's 1. -/
theorem one_mem : (1 : G) ∈ H :=
begin
  apply H.one_mem',
end

/-- A subgroup is closed under multiplication. -/
theorem mul_mem {x y : G} : x ∈ H → y ∈ H → x * y ∈ H :=
begin
  apply H.mul_mem',
end

/-- A subgroup is closed under inverse -/
theorem inv_mem {x : G} : x ∈ H → x⁻¹ ∈ H :=
begin
  apply H.inv_mem',
end

/-

So here are the three theorems which you need to remember about subgroups.
Say `H : subgroup G`. Then:

`H.one_mem : (1 : G) ∈ H`
`H.mul_mem {x y : G} : x ∈ H → y ∈ H → x * y ∈ H`
`H.inv_mem {x : G} : x ∈ H → x⁻¹ ∈ H`

These now look like the way a mathematician would write things.

Now let's start to prove basic theorems about subgroups (or, as a the computer
scientists would say, make a basic _interface_ or _API_ for subgroups),
using this sensible notation.

Here's an example; let's prove `x ∈ H ↔ x⁻¹ ∈ H`. Let's put the more
complicated expression on the left hand side of the `↔` though, because then
we can make it a `simp` lemma.
-/

-- Remember that `xena.group.inv_inv x` is the statement that `x⁻¹⁻¹ = x`

@[simp] theorem inv_mem_iff {x : G} : x⁻¹ ∈ H ↔ x ∈ H := 
begin
  split,
  { intro h,
    rw ← xena.group.inv_inv x,
    apply H.inv_mem,
    assumption },
  { apply H.inv_mem },
end

-- We could prove a bunch more theorems here. Let's just do one more.
-- Let's show that if x and xy are in H then so is y.

theorem mem_of_mem_mul_mem {x y : G} (hx : x ∈ H) (hxy : x * y ∈ H) : y ∈ H :=
begin
  rw ← inv_mem_iff at hx,
  convert H.mul_mem hx hxy, -- I claim that this proof that x⁻¹ * (x * y) ∈ H is what we want
  -- so now it just remains to prove x⁻¹ * (x * y) = y, which we can do because of Knuth-Bendix
  simp,
end

/-
Subgroups are extensional objects (like most things in mathematics):
two subgroups are equal if they have the same underlying subset,
and also if they have the same underlying elements.
Let's prove variants of this triviality now. The first one is rather
un-mathematical: it takes a subgroup apart into its pieces. I'll see if
you can do the other two!
-/

/-- Two subgroups are equal if the underlying subsets are equal. -/
theorem ext' {H K : subgroup G} (h : H.carrier = K.carrier) : H = K :=
begin
  -- first take H and K apart
  cases H, -- H now broken up into its underlying 3-tuple.
  cases K,
  -- and now it must be obvious, so let's see if the simplifier can do it.
  simp * at *, -- it can!
end

-- here's a variant. You can prove it using `ext'`. 

/-- Two subgroups are equal if and only if the underlying subsets are equal. -/
theorem ext'_iff {H K : subgroup G} :
  H.carrier = K.carrier ↔ H = K :=
begin
  split,
  { exact ext' },
  { intro h,
    rw h, }
end

-- to do this next one, first apply the `ext'` theorem we just proved,
-- and then use the `ext` tactic (which works on sets)

/-- Two subgroups are equal if they have the same elements. -/
@[ext] theorem ext {H K : subgroup G} (h : ∀ x, x ∈ H ↔ x ∈ K) : H = K :=
begin
  -- first apply ext' to reduce to checking the carriers are equal
  apply ext',
  -- now use the ext tactic to reduce to checking the elements of
  -- the carriers are equal
  ext,
  -- and now this is by definition what h says
  apply h,
end

/-
We tagged that theorem with `ext`, so now the `ext` tactic works on subgroups
too: if you ever have a goal of proving that two subgroups are equal, you can
use the `ext` tactic to reduce to showing that they have the same elements.
-/

/-

## The lattice structure on subgroups

Subgroups of a group form what is known as a *lattice*. 
This is a partially ordered set with a sensible notion of
max and min. We partially order subgroups by saying `H ≤ K` if
`H.carrier ⊆ K.carrier`. Subgroups even have a good notion of an infinite
Sup and Inf (the Inf of a bunch of subgroups is just their intersection;
their Sup is the subgroup generated by their union).

This combinatorial structure (a partially ordered set with good
finite and infinite notions of Sup and Inf) is called a "complete lattice",
and Lean has this structure inbuilt into it. We will construct
a complete lattice structure on `subgroup G`.

We start by defining a relation ≤ on the type of subgroups of a group.
We say H ≤ K iff H.carrier ⊆ K.carrier .
-/

/-- If `H` and `K` are subgroups of `G`, we write `H ≤ K` to
  mean `H.carrier ⊆ K.carrier` -/
instance : has_le (subgroup G) := ⟨λ H K, H.carrier ⊆ K.carrier⟩

-- useful to restate the definition so we can `rw` it
lemma le_def : H ≤ K ↔ H.carrier ⊆ K.carrier :=
begin
  -- true by definition
  refl
end

-- another useful variant
lemma le_iff : H ≤ K ↔ ∀ g, g ∈ H → g ∈ K :=
begin
  -- true by definition
  refl,
end



-- Now let's check the axioms for a partial order.
-- These are not hard, they just reduce immediately to the
-- fact that ⊆ is a partial order
@[refl] lemma le_refl : H ≤ H :=
begin
  rw le_def,
  -- Lean knows ⊆ is reflexive so the sneaky `refl` which Lean tries after `rw` 
  -- has closed the goal!
end

lemma le_antisymm : H ≤ K → K ≤ H → H = K :=
begin
  rw [le_def, le_def, ← ext'_iff],
  -- now this is antisymmetry of ⊆, which Lean knows
  exact set.subset.antisymm,
end

@[trans] lemma le_trans : H ≤ J → J ≤ K → H ≤ K :=
begin
  rw [le_def, le_def, le_def],
  -- now this is transitivity of ⊆, which Lean knows
  exact set.subset.trans,
end

-- We've made `subgroup G` into a partial order!
instance : partial_order (subgroup G) :=
{ le := (≤),
  le_refl := le_refl,
  le_antisymm := le_antisymm,
  le_trans := le_trans }

/-


### intersections

Let's prove that the intersection of two subgroups is a subgroup. In Lean
this is a definition: given two subgroups, we define a new subgroup whose
underlying subset is the intersection of the subsets, and then prove
the axioms.
-/

/-- The intersection of two subgroups is also a subgroup -/
def inf (H K : subgroup G) : subgroup G :=
{ carrier := H.carrier ∩ K.carrier, -- the carrier is the intersection
  one_mem' := 
  begin
    -- recall that x ∈ Y ∩ Z is _by definition_ x ∈ Y ∧ x ∈ Z, so you can `split` this. 
    split,
    { exact H.one_mem },
    { exact K.one_mem },
  end,
  mul_mem' := 
  begin
    intros x y hx hy,
    cases hx with hxH hxK,
    cases hy with hyH hyK,
    split,
    { exact H.mul_mem hxH hyH },
    { exact K.mul_mem hxK hyK },
  end,
  inv_mem' :=
  begin
    rintro x ⟨hxH, hxK⟩, -- rintro does intro and cases all in one go
    exact ⟨H.inv_mem hxH, K.inv_mem hxK⟩, -- ⟨⟩ instead of split
  end }

-- Note that using "term mode" one can really compactify all this.
def inf_term_mode (H K : subgroup G) : subgroup G :=
{ carrier := H.carrier ∩ K.carrier,
  one_mem' := ⟨H.one_mem, K.one_mem⟩,
  mul_mem' := λ _ _ ⟨hhx, hkx⟩ ⟨hhy, hky⟩, 
  ⟨H.mul_mem hhx hhy, K.mul_mem hkx hky⟩,
  inv_mem' := λ x ⟨hhx, hhy⟩,
  ⟨H.inv_mem hhx, K.inv_mem hhy⟩}

-- Notation for `inf` in computer science circles is ⊓ .

instance : has_inf (subgroup G) := ⟨inf⟩

/-- The underlying set of the inf of two subgroups is just their intersection -/
lemma inf_def (H K : subgroup G) : (H ⊓ K : set G) = (H : set G) ∩ K :=
begin
  -- true by definition
  refl
end

/-

## Subgroup generated by a subset.

To do the sup of two subgroups is harder, because we don't just take
the union, we need to then look at the subgroup generated by this union
(e.g. the union of the x and y axes in ℝ² is not a subgroup). So we need
to have a machine to spit out the subgroup of `G` generated by a subset `S : set G`.

There are two completely different ways to do this. The first is a "top-down"
approach. We could define the subgroup generated by `S` to be the intersection of
all the subgroups of `G` that contain `S`. The second is a "bottom-up" approach.
We could define the subgroup generated by `S` "by induction" (or more precisely
by recursion), saying that `S` is in the subgroup, 1 is in the subgroup,
the product of two things in the subgroup is in the subgroup, the
inverse of something in the subgroup is in the subgroup, and that's it.
Both methods come out rather nicely in Lean. Let's do the first one.

We are going to be using a bunch of theorems about "bounded intersections",
a.k.a. `set.bInter`. We will soon get tired of writing `set.blah` so let's
`open set` so that we can skip it. 

-/

open set

/-

Here is the API for `set.bInter` (or `bInter`, as we can now call it):

Notation: `⋂` (type with `\I`)

If `X : set (subgroup G)`, i.e. if `X` is a set of subgroups of `G`, then

`⋂ K ∈ X, (K : set G)` means "take the intersection of the underlying subsets".

-- mem_bInter_iff says you're in the intersection iff you're in
-- all the things you're intersecting. Very useful for rewriting.
`mem_bInter_iff : (g ∈ ⋂ (K ∈ S), f K) ↔ (∀ K, K ∈ s → g ∈ f K)`

-- mem_bInter is just the one way implication. Very useful for `apply`ing.
`mem_bInter : (∀ K, K ∈ s → g ∈ f K) → (g ∈ ⋂ (K ∈ S), f K)`

-/
/- 
We will consider the closure of a set as the intersect of all subgroups
containing the set
-/

/-- The Inf of a set of subgroups of G is their intersection. -/
def Inf (X : set (subgroup G)) : subgroup G :=
{ carrier := ⋂ K ∈ X, (K : set G), -- carrier is the intersection of the underlying sets
  one_mem' := begin
    apply mem_bInter,
    intros H hH,
    apply H.one_mem,
  end,
  mul_mem' := begin
    intros x y hx hy,
    rw mem_bInter_iff at *,
    intros H hH,
    apply H.mul_mem,
    { apply hx,
      exact hH },
    { exact hy H hH }  
  end,
  inv_mem' := begin
    intros x hX,
    rw mem_bInter_iff at *,
    intros H hH,
    exact H.inv_mem (hX H hH),
  end,
}

-- again note that term mode can do this much more quickly
def Inf' (X : set (subgroup G)) : subgroup G :=
{ carrier := ⋂ t ∈ X, (t : set G),
  one_mem' := mem_bInter $ λ i h, i.one_mem,
  mul_mem' := λ x y hx hy, mem_bInter $ λ i h,
    i.mul_mem (by apply mem_bInter_iff.1 hx i h) 
    (by apply mem_bInter_iff.1 hy i h),
  inv_mem' := λ x hx, mem_bInter $ λ i h,
    i.inv_mem (by apply mem_bInter_iff.1 hx i h) }

/-- The *closure* of a subset `S` of `G` is the `Inf` of the subgroups of `G`
  which contain `S`. -/
def closure (S : set G) : subgroup G := Inf {H : subgroup G | S ⊆ H}

-- we can restate mem_bInter_iff using our new "closure" language:
lemma mem_closure_iff {S : set G} {x : G} : 
  x ∈ closure S ↔ ∀ H : subgroup G, S ⊆ H → x ∈ H := mem_bInter_iff

/- 
There is an underlying abstraction here, which you may not know about.
A "closure operator" in mathematics 

https://en.wikipedia.org/wiki/Closure_operator

is something mapping subsets of a set X to subsets of X, and satisfying three
axioms:

1) `subset_closure : S ⊆ closure S`
2) `closure_mono : (S ⊆ T) → (closure S ⊆ closure T)`
3) `closure_closure : closure (closure S) = closure S`

It works for closure in topological spaces, and it works here too.
It also works for algebraic closures of fields, and there are several
other places in mathematics where it shows up. This idea, of "abstracting"
and axiomatising a phenomenon which shows up in more than one place,
is really key in Lean.

Let's prove these three lemmas in the case where `X = G` and `closure S`
is the subgroup generated by `S`.

Here are some things you might find helpful.

Remember 
`mem_coe : g ∈ ↑H ↔ g ∈ H`
`mem_carrier : g ∈ H.carrier ↔ g ∈ H`

There's 
`mem_closure_iff : x ∈ closure S ↔ ∀ (H : subgroup G), S ⊆ ↑H → x ∈ H`
(`closure S` is a subgroup so you might need to use `mem_coe` or `mem_carrier` first)

For subsets there's
`subset.trans : X ⊆ Y → Y ⊆ Z → X ⊆ Z`

You might find `le_antisymm : H ≤ K → K ≤ H → H = K` from above useful
-/

/-
Reminder: X ⊆ Y means `∀ g, g ∈ X → g ∈ Y` and it's definitional,
so you can just start this with `intro g`.
-/
lemma subset_closure (S : set G) : S ⊆ closure S :=
begin
  intro g,
  intro hgS,
  rw [mem_coe, mem_closure_iff],
  intros H hH,
  apply hH,
  assumption
end

-- fancy term mode proof
lemma subset_closure' (S : set G) : S ⊆ closure S :=
λ s hs H ⟨y, hy⟩, by {rw [←hy, mem_Inter], exact λ hS, hS hs}

-- It's useful to know `subset.trans : X ⊆ Y → Y ⊆ Z → X ⊆ Z`
lemma closure_mono {S T : set G} (hST : S ⊆ T) : closure S ≤ closure T :=
begin
  intros x hx,
  rw [mem_carrier, mem_closure_iff] at *,
  intros H hTH,
  apply hx,
  exact subset.trans hST hTH,
end

-- not one of the axioms, but sometimes handy
lemma closure_le (S : set G) (H : subgroup G) : closure S ≤ H ↔ S ⊆ ↑H :=
begin
  split,
    { intro hSH,
      exact subset.trans (subset_closure S) hSH },
    { intros hSH g hg,
      rw [mem_carrier, mem_closure_iff] at hg,
      exact hg _ hSH }
end

-- You can start this one by applying `le_antisymm`,
lemma closure_closure (S : set G) : closure S = closure (closure S) :=
begin
  apply le_antisymm,
  { apply subset_closure },
  { rw closure_le,
    intros x hx,
    exact hx }, 
end

-- This shows that every subgroup is the closure of something, namely its
-- underlying subset. 
lemma closure_self {H : subgroup G} : closure ↑H = H :=
begin
  apply le_antisymm,
  { rw le_iff,
    intro g,
    rw mem_closure_iff,
    intro h,
    apply h,
    refl },
  { exact subset_closure H }
end

/-
Recall the second proposed construction of the subgroup closure of a subset `S`;
it is the smallest subgroup `H` of `G` such that `S ⊆ H` and which contains
`1` and is closed under `*` and `⁻¹`. This inductive constuction (which we
did not make) comes with a so-called "recursor": if we have a true/false
statement `p g` attached to each element `g` of G with the following properties:

1) `p s` is true for all `s ∈ S`,
2) `p 1` is true,
3) If `p x` and `p y` then `p (x * y)`,
4) If `p x` then `p x⁻¹`

Then `p` is true on all of `closure S`.

If we had made an inductive definition of `closure S` then this would have been true
by definition! We used another definition, so we will have to prove it
ourselves.
-/

/-- An induction principle for closures. -/
lemma closure_induction {p : G → Prop} {S : set G}
  (HS : ∀ x ∈ S, p x)
  (H1 : p 1)
  (Hmul : ∀ x y, p x → p y → p (x * y))
  (Hinv : ∀ x, p x → p x⁻¹) : 
  -- conclusion after colon
  ∀ x, x ∈ closure S → p x :=
begin
  -- the subset of G where `p` is true is a subgroup. Let's call it H
  let H : subgroup G :=
  { carrier := p, 
    one_mem' := H1, 
    mul_mem' := Hmul,
    inv_mem' := Hinv },
  -- The goal is just that closure S ≤ H, by definition.
  change closure S ≤ H,  
  -- Our hypothesis HS is just that S ⊆ ↑H, by definition
  change S ⊆ ↑H at HS, 
  -- So this is just closure_le in disguise
  rw closure_le,
  assumption,
end

-- this is even briefer in term mode:
lemma closure_induction' {p : G → Prop} {S : set G}
  (HS : ∀ x ∈ S, p x)
  (H1 : p 1)
  (Hmul : ∀ x y, p x → p y → p (x * y))
  (Hinv : ∀ x, p x → p x⁻¹) : 
  ∀ x, x ∈ closure S → p x :=
λ x h, (@closure_le _ _ _ ⟨p, H1, Hmul, Hinv⟩).2 HS h

/-
Finally we prove that the `closure` and `coe` maps form a `galois_insertion`.
This is another abstraction, it generalises `galois_connection`, which is
something that shows up all over the place (algebraic geometry, Galois theory etc).
See

https://en.wikipedia.org/wiki/Galois_connection

A partial order can be considered as a category, with Hom(A,B) having
one element if A ≤ B and no elements otherwise. A Galois connection between
two partial orders is just a pair of adjoint functors between the categories.
Adjointness in our case is `S ⊆ ↑H ↔ closure S ≤ H`. 

The reason it's an insertion and not just a connection is that if you start
with a subgroup, take the underlying subset, and then look at the subgroup
generated by that set, you get back to where you started. So it's like one
of the adjoint functors being a forgetful functor.
-/

def gi : galois_insertion (closure : set G → subgroup G) (coe : subgroup G → set G) :=
{ choice := λ S _, closure S,
  gc := closure_le,
  le_l_u := λ H, subset_closure (H : set G),
  choice_eq := λ _ _, rfl }

/-

One use of this abstraction is that now we can pull back the complete
lattice structure on `set G` to get a complete lattice structure on `subgroup G`. 
-/

instance : complete_lattice (subgroup G) :=
{.. galois_insertion.lift_complete_lattice gi}

/-

We just proved loads of lemmas about Infs and Sups of subgroups automatically,
and have access to a ton more because the `complete_lattice` structure in
Lean has a big API. See for example

https://leanprover-community.github.io/mathlib_docs/order/complete_lattice.html#complete_lattice

All those theorems are now true for subgroups. None are particularly hard to prove,
but the point is that we don't now have to prove any of them ourselves.
-/
end subgroup

end xena


/-

Further work: `bot` and `top` (would have to explain the
API for `singleton` and `univ`)

-/
