-- always import the tactics, we are mathematicians
import tactic
-- import the theory of G-module homomorphisms, for G a group
import algebra.group_action_hom

/-

# Introduction to G-modules in Lean

Let `G` be a group (with group law `*`) and let `M` be an abelian
group (with group law `+`). A `G`-action on `M` is just a group
homomorphism from `G` to the group automorphisms
of `M`, or in other words an action `•` of `G` on `M` (in the sense
of groups acting on sets/types) satisfying
the axiom `smul_add g m n : g • (m + n) = g • m + g • n`.

The goal of this workshop will be to set up a cohomology theory
for G-modules. We will just do H⁰ (G-invariant elements)
and H¹ (1-cocycles modulo coboundaries), but clearly one
could go on to 2-cocycles, n-cocycles etc.

### typeclass comments ("will it work for monoids/add_monoids?")

Note that the definition of G-module does not mention `g⁻¹` at all, so
we can even define it for monoids `G`, which we will. Loads
of the theory works for `G` a monoid in fact (certainly everything
we do in this workshop). But we use subtraction on `M` quite a
lot in practice when we get to `H¹` (e.g. the coboundary `g b - b`
needs subtraction) so I've assumed that `M` is an abelian group throughout for
pedagogical reasons (and because it solved some typeclass issue at some point).

The `G`-module structure on `M` is called `distrib_mul_action G M` in Lean.
-/

section distrib_mul_action_stuff

/- 

## The interface for G-modules, i.e. the theory of `•`

In Lean we learn about the typeclass `[distrib_mul_action G M]`, 
which gives us the notation `•` for an action of `G` on `M`,
and all the axioms.

Notation for this section:

Let `G` be a group. Let `M` be an abelian group and furthermore
assume `M` is a `G`-module. We use the usual notation `(g₁ * g₂) • (m₁ + m₂)`

-/

variables
  {G : Type} [monoid G] --`*`
  {M : Type} [add_comm_group M] --`+`
  [distrib_mul_action G M] --`•`

-- Let `g`'ish variables be elements of `G`, and let `m`ish variables be
-- elements of `M`.
variables (g g1 g2 g₁ g₂ : G) (m m1 m2 m₁ m₂ : M)

/-

### The interface for `•`

Below are the names of the theorem proofs which you will need
to know when manipulating an element of a fixed `G`-module,
for example the element `(g₁ * g₂) • (m₁ + m₂)`.

I have explained the names of the proofs in the form
of examples. The syntax for the examples is this:

`example : <Theorem statement> := <name of proof function> input1 input2 ...`

So these examples tell you the names of the proofs of the theorems.
The proofs are functions which need inputs, and the inputs are
the variables used in the theorem statement. I also mention
whether Lean's "rw-machine" (the `simp` tactic) knows about these theorems.

-/



example : g • (0 : M) = 0 := smul_zero g -- a simp lemma
example : g • (m₁ + m₂) = g • m₁ + g • m₂ := smul_add g m₁ m₂ -- a simp lemma 
example : g • (-m) = -(g • m) := smul_neg g m -- a simp lemma
example : (1 : G) • m = m := one_smul G m -- a simp lemma
-- at the time of writing, this is not a simp lemma.
example : g • (m₁ - m₂) = g • m₁ - g • m₂ := smul_sub g m₁ m₂
example : (g₁ * g₂) • m = g₁ • g₂ • m := mul_smul g₁ g₂ m -- not a simp lemma

end distrib_mul_action_stuff
/-

### Entirely optional digression on `simp`

Some of those lemmas above were "simp lemmas" (if you `#print one_smul`
you'll see it has a `@[simp]` tag). What makes a good simp lemma?

The most important rule is that, unless you really know what you're
doing, it should be of the form `A = B` or `A ↔ B`.

The second rule is that the right hand side should in some sense
be "simpler than" the left hand side.
so the lemma should say `A simplifies_to B`, indicating a flow towards
a solution.

For example `one_mul : 1 * a = a` is a `simp` lemma for groups (and
for monoids), because it is an equality, and the right hand side
is unarguably simpler than the left hand side. 

Later on we'll be making some of our own structures, and
we will want to train Lean's simplifier to use those structures. The better
you understand how the simplifier works on your structures, the easier you
will find it to type "mathematics as the mathematician thinks about it"
into Lean.

-/

/-

KB note to self: Some people think `smul_add`
`g • (m₁ + m₂) = g • m₁ + g • m₂`
is a good simp lemma. I should experiment with `simp` here perhaps
or maybe just ask how to do it.

should mul_smul be a simp lemma?

-/

/-

### The `simp` tactic

A lemma is, by definition, a `simp` lemma, if its proof term is tagged
with the `@[simp]` attribute (you can check a term's attributes with `#print`)

`simp` is an algorithm which will "follow its nose", doing
stuff like expanding out brackets automatically and tidying up.
It would tidy up by simplifying `g • 0` to `0` for example,
and it would expand out by changing `g • (m₁ + m₂)` to `g • m₁ + g • m₂`.
In general `simp` tries to rewrite equivalences, e.g. things of the
form `A = B` or `A ↔ B`, with in each case `B` the "simplified" or
"expanded out" version of `A`. The equivalences it rewrites
with are the ones in its database of a few thousand (*shrug?)
so-called "`simp` lemmas" For example, if `⇑0 : G → M` is the
zero function then `zero_val g : ⇑0 g = 0` would be a good `simp`
lemma, which is why it is tagged with the `@[simp]` attribute,
making it part of the database.

Note that `simp` does not have "ideas". It will never apply
commutativity or associativity, for example, for fear that
it might be a waste of time which would have to be undone later.
`simp` will solve `x + 0 = x` but it will not solve `m + n = n + m`,
because it is not so clear that the right hand side is any simpler
than the left hand side. problems like that you need `abel`.

To learn more about `simp`, check out the simp docs on
the leanprover-community website.
-- TODO when online -- add link to simp docs in API at leanprover-community website

## A note on `abel`

`abel` should be able to solve all problems in abelian groups
of the form ∀ a b c, a + (c + -b) = (a - b) + c etc.
Note however that it *cannot use hypotheses*. It will only
prove identities which are true in all abelian groups. 

-/
example (M : Type) [add_comm_group M] (a b c : M) :
  a + (c + -b) = (a - b) + c := by abel


/-

## @JoBo's homework -- the interface for sub-G-modules

Lean also has G-invariant subsets (`sub_mul_action G A`)
but not G-invariant subgroups, rather annoyingly. Hopefully
@jobo is going to make this stuff.

-/
section Jobo_homework

-- **TODO** copy post here
-- see KB post in live lean coding 11 Mar with API for
-- `sub_distrib_mul_action`

structure sub_distrib_mul_action
  (G : Type) [monoid G]
  (M : Type) [add_comm_group M] [distrib_mul_action G M]
:=
-- the subset
(to_set : set M)
-- the axioms (TODO)
(foo : ∀ (g : G), ∀ m ∈ to_set, (g * g) • m = (0 : M))

namespace sub_distrib_mul_action
variables {G : Type} [monoid G]
variables {M : Type} [add_comm_group M] [distrib_mul_action G M]
variables {N : Type} [add_comm_group N] [distrib_mul_action G N]

instance : has_coe (sub_distrib_mul_action G M) (set M) := ⟨to_set⟩

theorem ext_iff (A B : sub_distrib_mul_action G M) :
  A = B ↔ ∀ m : M, m ∈ (A : set M) ↔ m ∈ (B : set M) := sorry

end sub_distrib_mul_action

namespace distrib_mul_action_hom

variables {G : Type} [monoid G]
variables {M : Type} [add_comm_group M] [distrib_mul_action G M]
variables {N : Type} [add_comm_group N] [distrib_mul_action G N]

def ker (φ : M →+[G] N) :
  sub_distrib_mul_action G M := 
by { refine_struct {to_set := {m : M | φ m = 0}},
  try {repeat {sorry}} -- proofs missing
}

def range (φ : M →+[G] N) :
  sub_distrib_mul_action G N :=
by { refine_struct {to_set := set.range φ},
  try {repeat {sorry}} -- proofs missing
}
 
end distrib_mul_action_hom

/-
TODO

G-invariant subgroups are a complete lattice.

Proof could perhaps go via a Galois correspondence with either
G-invariant subsets or subgroups (or both?).

-/

end Jobo_homework

/-
## The interface for morphisms of G-modules, i.e. the theory of `→+[_]`

Lean uses notation `M →+[G] N` and name `distrib_mul_action_hom`,
but you don't need to remember the name, it should work in the 
background for you.

The type of G-module homs from `M` to `N`, i.e. the set
that a mathematician would call something like $$\Hom_G(M,N)$$,
is in Lean called `M →+[G] N`. The non-notation name for this function
type is `distrib_mul_action_hom G M N`, which is why you see this word in
namespaces or mentioned in sections.

Terms of this type are `G`-module morphisms from `M` to `N`.
So when we see `φ : M →+[G] N` it means that `φ` is a G-module hom
from `M` to `N`. We will often only be using `φ` only in terms of its
associated function `⇑φ : M → N`. `φ` itself is a package, consisting
of a function and a bunch of theorems about that function.

-/

namespace distrib_mul_action_hom

-- let's do the variables
variables 
-- let `G` be a group (or a monoid)
{G : Type} [monoid G]

{M : Type}  [add_comm_group M] [distrib_mul_action G M] -- let `M` be a `G`-module
{N : Type}  [add_comm_group N] [distrib_mul_action G N] -- let `N` be a `G`-module
(φ : M →+[G] N) -- let φ be a morphism of G-modules
(g : G) (m m₁ m₂ m1 m2 : M) -- random useful variable names

/-

### API for `M →+[G] N`

Here are the names of the proofs of the basic axioms for G-module
morphisms. The proofs are in the `→+[_]` namespace, so you can
write things like `φ.map_smul` to access them easily.

-/
example : φ (g • m) = g • (φ m) := φ.map_smul g m -- a simp lemma
example (m₁ m₂ : M) : φ (m₁ + m₂) = φ m₁ + φ m₂ := φ.map_add m₁ m₂ -- a simp lemma

example : φ (g • (m1 + m2)) = g • φ m1 + g • φ m2 :=
begin
  -- what will you rewrite? Will you rewrite at all?
  rw φ.map_smul,
  rw φ.map_add, 
  rw smul_add,
  -- or just `simp` will do it
  -- Moral : `simp` right now is being trained to "push functions further in"
  -- and this must be the `simp` normal form.
end
/-


## A G-module morphism is a pair of things

A G-module morphism `φ : M →+[G] N` is two things.
1) a function `⇑φ : M → N`
2) the dot notation system for `φ`, a database where
all the axioms and theorems for G-module homs as applied to `φ` are stored.

For example, the type of φ.map_smul is *actually* a theorem about `⇑φ`.

`φ.map_smul g m : ⇑φ (g • m) = g • ⇑φ m`


-/

example (φ : M →+[G] N) : φ 0 = 0 :=
begin
  -- library_search will take some time (I don't know why)
  -- but will eventually find the answer to this one. 
  -- But you can guess it quicker!
  -- what will you rewrite? Remember rewrite tries 
  -- `refl` afterwards (unlike NNG)
  rw φ.map_zero,
end

-- Can you solve it in term mode?
example : φ 0 = 0 := φ.map_zero
-- change `sorry` to the name of a tactic
example : φ 0 = 0 := by simp


/-

### Composition of G-module morphisms

You know how to compose functions, you just write `ψ (φ a)`
or whatever. Composition in the category of G-modules is
done with the `comp` method for `G`-module morphisms.

-/

-- let P be another G-module
variables {P : Type} [add_comm_monoid P] [distrib_mul_action G P]

-- Recall `φ : M →+[G] N` from earlier.
-- let ψ : N → P be another G-module morphism
variable (ψ : N →+[G] P) -- his is notation for `ψ : distrib_mul_action_hom G N P`

-- let's make function composition notation
local infixr ` ∘ ` := distrib_mul_action_hom.comp

-- how to compose G-module maps
example : M →+[G] P := ψ ∘ φ

-- You should think of φ and ψ as morphisms in the category
-- of `G`-modules. They are functions, but they also have
-- some extra category-theoretic baggage (proofs that they
-- are G-linear maps) which needs to be moved around.

-- KB NOTE TO SELF do we ever actually compose morphisms?
-- My definition of short exact sequence of G-modules
-- is "image = kernel" , which is highly category-theoretic.
-- and functional evaluation often takes place after that.

-- The important fact is that `(ψ ∘ φ) m = ψ (φ m)`, as
-- terms of type `P`. Rather nicely, this theorem is called
-- `ψ.comp_apply` but it is also a `simp` lemma, and 
-- furthermore true by definition
example (m : M) :
  (ψ ∘ φ) m = ψ (φ m) := ψ.comp_apply φ m -- and `rfl` works too and `by simp`


-- By the way, `squeeze_simp` is a version of `simp` which tells you 
-- which rewrites it did. Give it a try!
example :
  ψ.comp φ (g • (m₁ + m₂)) = g • (ψ (φ m₁) + ψ (φ m₂)) :=
begin
  simp,
end

end distrib_mul_action_hom

section exactness_stuff

/-

## Developing a basic API for exact sequences

This is relatively straightforward and a nice
beginner exercise.

-/
-- Let M, N and P be G-modules
variables {G M N P : Type}
  [monoid G] [add_comm_group M] [add_comm_group N] [add_comm_group P]
  [distrib_mul_action G M] [distrib_mul_action G N] [distrib_mul_action G P]

-- I don't know which definition is best. This is the slickest for sure.
definition is_exact (φ : M →+[G] N) (ψ : N →+[G] P) : Prop :=
φ.range = ψ.ker

@[simp] lemma is_exact.def0 (φ : M →+[G] N) (ψ : N →+[G] P) :
  is_exact φ ψ ↔ φ.range = ψ.ker := iff.rfl

@[simp] lemma is_exact.def (φ : M →+[G] N) (ψ : N →+[G] P) :
  is_exact φ ψ ↔ ∀ n : N, (∃ m : M, φ m = n) ↔ ψ n = 0 :=
begin
  rw is_exact.def0,
  rw sub_distrib_mul_action.ext_iff, 
  refl,
end

-- Switch your infoview filter onto "only props" to get the noise
-- out of the way.

-- this is the wrong way around, it should be removed.
lemma is_exact_def' (φ : M →+[G] N) (ψ : N →+[G] P) :
  is_exact φ ψ ↔ ψ.ker = φ.range :=
begin
  rw eq_comm,
  refl,
end

/-

## more than one "definition" of `is_exact`

Mathematicians have about three different ways of saying
a sequence is exact, and they're all "the definition".
That's why I proved the last few lemmas -- so we can use whichever
of the definitions is most use to us at the time. 

-/

/-

## Making an API for short exact sequences.
-/
open function

-- This will do for an internal definition. The user should
-- never have to think about that though.
def is_short_exact (φ : M →+[G] N) (ψ : N →+[G] P) : Prop :=
  is_exact φ ψ ∧ injective φ ∧ surjective ψ

-- We need to make a nice API for this, it's easy and fun.

variables (φ : M →+[G] N) (ψ : N →+[G] P)

-- useful for rewrites when we're making the API.
protected lemma is_short_exact_def :
  is_short_exact φ ψ ↔ is_exact φ ψ ∧ injective φ ∧ surjective ψ :=
-- true by definition
iff.rfl

-- I marked it protected because the end user should never have
-- to use this lemma in this repo.

-- Now the proper API
namespace is_short_exact

variables {φ} {ψ} (h : is_short_exact φ ψ)

include h
def injective : injective φ := --h.2.1
begin
  /- put your infoview filter onto only props.
     You see

     h: is_short_exact φ ψ
     ⊢ injective ⇑φ
  
     That's the question. You can take `h` apart
     with `cases`, and even more effectively with
     `rcases`.
  -/
  rcases h with ⟨_, _, _⟩,
  assumption
end


def surjective : surjective ψ := -- h.2.2
begin
  exact h.2.2
end

-- again we don't really want the user messing
-- with this internal function, it should be thought
-- of as "an abbreviation for several things".
protected def exact : is_exact φ ψ := h.1

--@[simp] lemma is_exact_def0 (φ : M →+[G] N) (ψ : N →+[G] P) :
--  is_exact φ ψ ↔ φ.range = ψ.ker

--@[simp] lemma is_exact_def (φ : M →+[G] N) (ψ : N →+[G] P) :
--  is_exact φ ψ ↔ ∀ n : N, (∃ m : M, φ m = n) ↔ ψ n = 0 :=

def exact_def : ∀ n : N, (∃ m : M, φ m = n) ↔ ψ n = 0 :=
begin
  rw ← is_exact.def,
  exact h.exact
end

def exact_def0 : φ.range = ψ.ker :=
begin
  rw ← is_exact.def0,
  -- different uses of word!
  exact h.exact,
end

-- now a noncomputable function defined by the axiom of choice,
-- a random splitting of the surjection ψ : P → N and hence a one-sided
-- inverse
noncomputable def inverse_ψ : P → N := λ p, classical.some (h.surjective p)

@[simp] lemma inverse_ψ_spec (p : P) : ψ (h.inverse_ψ p) = p :=
classical.some_spec (h.surjective p)

-- now the same sort of thing for the injection φ : M → N; this is
-- the map from the image of φ back to M.
noncomputable def inverse_φ (h : is_short_exact φ ψ) {n : N}
  (hn : ∃ m : M, φ m = n) : M :=
classical.some hn

@[simp]
lemma inverse_φ_def (h : is_short_exact φ ψ) {n : N} (hn : ∃ m : M, φ m = n) :
  φ (inverse_φ h hn) = n :=
classical.some_spec hn

-- injectivity implies it's independent of choice, but we used choice anyway
@[simp] lemma inverse_φ_spec (h : is_short_exact φ ψ) {n : N} {m : M} (hm : φ m = n) :
  h.inverse_φ ⟨m, hm⟩ = m :=
begin
  apply h.injective,
  rw hm,
  exact classical.some_spec ⟨m, hm⟩,
end

end is_short_exact

end exactness_stuff

/- 
# Coercions

Something which will come up again and again in this workshop is
the concept of a coercion. We have seen things which computer scientists
call `φ : M →+[G] N` and we call "functions", but to Lean they are
functions with baggage, which in this case is all the axioms and theorems
attached to the theory of G-module homomorphisms (for example
a proof of the theorem that `φ 0 = 0`). This means that `φ` itself is a
pair consisting of a function and a whole bunch of extra stuff, and
in particular `φ` is not a function (it's a function and more).
The actual function `M → N` is called `⇑φ` by Lean, but we can just
call it `φ` most of the time.

The system that makes this happen is called a coercion -- we coercing
`φ` to a function `⇑φ`. We will see other examples of coercions later.
-/
