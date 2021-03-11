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

### typeclass comments ("will it work for monoids/add_monoids?")

Note that the definition of G-module does not mention `g⁻¹` at all, so
we can even define it for monoids `G`, which we will. Loads
of the theory works for `G` a monoid. I've been working on `H¹(G,M)` today
and it all works for monoids. But we use subtraction on `M` quite a
lot in practice when we get to `H¹` (e.g. `g b - b`) so I've assumed
that `M` is an abelian group throughout for pedagogical reasons
(and because it solved some typeclass issue at some point).

-/

section distrib_mul_action

/- 

## The interface for G-modules, i.e. the theory of `•`

In Lean we define the `•` notation for a `G`-action on `M`
with the typeclass `[distrib_mul_action G M]`, which gives us the
notation and all the axioms.

Notation for this section:

Let `G` be a group (or just a monoid) (with notation `*`).
Let `M` be an abelian group (with notation `+`) and 
let `M` be a `G`-module (with notation `•`).

-/

variables {G M : Type}
  [monoid G] --`*`
  [add_comm_group M] --`+`
  [distrib_mul_action G M] --`•`

-- Let `g`'ish variables be elements of `G`, and let `m`ish variables be elements of `M`.
variables (g g₁ g₂ : G) (m m₁ m₂ : M)

/-

### The API for `•`

Below are the names of the theorems which you will need
to know when manipulating an element of a fixed `G`-module,
for example `(g₁ * g₂) • (m₁ + m₂)`.

They are written like this:

`example : Theorem_statement := theorem_proof_function input1 input2 ...`

So these examples tell you the names of the proofs of the theorems.
The proofs are functions which need inputs, and the inputs are
the variables used in the theorem statement.

-/

example : g • (0 : M) = 0 := smul_zero g -- a simp lemma
example : g • (m₁ + m₂) = g • m₁ + g • m₂ := smul_add g m₁ m₂ -- a simp lemma 
example : g • (-m) = -(g • m) := smul_neg g m -- a simp lemma
example : (1 : G) • m = m := one_smul G m -- a simp lemma
example : (g₁ * g₂) • m = g₁ • (g₂ • m) := mul_smul g₁ g₂ m -- not a simp lemma
example : g • (m₁ - m₂) = g • m₁ - g • m₂ := smul_sub g m₁ m₂ -- is it a simp lemma?

-- exercises.
-- You should use the `rewrite` tactic. Remember that Lean's
-- rewrite tactic tries `refl` for luck at the end (not like NNG)
example : (g₁ * g₂) • (m₁ + m₂) = g₁ • g₂ • m₁ + g₁ • g₂ • m₂ :=
begin
  sorry
end

example : (1 * 1 * 1 : G) • m = m :=
begin
  sorry
end 

/-

## The `simp` tactic

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


end distrib_mul_action

/-

## Advanced exercise

Lean also has G-invariant subsets (`sub_mul_action G A`)
but not G-invariant subgroups. It is well-understood how
to set these things up, both the definitions and the API
are standard, and one key theorem to aim for is that G-invariant subgroups
are a complete lattice, whose proof could perhaps go via a Galois
correspondence with G-invariant subsets or subgroups (or both?)

This would be a really cool project if someone wanted to try on a branch of
the course project this week. There's probably a ton of API
which could be done. If you are interested in submitting
some Lean work which you've done as a result of this workshop and
are happy to put on public display then
check out the README for how to submit it. The only rule is:
NO ERRORS!

Right now I am not using G-invariant subgroups in my development of H¹,
but things might change.

## The interface for morphisms of G-modules, i.e. the theory of `→+[_]`

Lean uses notation `M →+[G] N` and name `distrib_mul_action_hom`,
but you don't need to remember the name, it should work in the 
background for you.

The type of G-module homs from `M` to `N`, i.e. the set
that a mathematician would call something like $$\Hom_G(M,N)$$,
is in Lean called `M →+[G] N`. This is notation for the `distrib_mul_action_hom`
function, which is why you see this word in namespaces and
sections sometimes, but hopefully you will never need to type it yourself.

Terms of this type are `G`-module morphisms from `M` to `N`.
So when we see `φ : M →+[G] N` it means that `φ` is a G-module hom
from `M` to `N`. We will often only be seeing `φ` in terms of its
associated function `⇑φ : M → N`. `φ` itself is a package, consisting
of a function and a bunch of theorems about that function.

-/

namespace distrib_mul_action_hom

-- Let M and N be G-modules
variables 
-- G, A B are sets, or types, they're the same
{G M N : Type}
  [monoid G] -- `*` on G
  [add_comm_monoid M] [add_comm_monoid N] -- `+` on A and B
  [distrib_mul_action G M] [distrib_mul_action G N] -- `•` G-actions on A and B


/-

### API for `M →+[G] N`

Here are the names of the proofs of the basic axioms for G-module
morphisms.

-/
variables 
-- let φ be a morphism of G-modules
(φ : M →+[G] N)
-- random useful variable names
(g : G) (m m₁ m₂ : M) 

example : φ (g • m) = g • (φ m) := φ.map_smul g m -- a simp lemma
example (m₁ m₂ : M) : φ (m₁ + m₂) = φ m₁ + φ m₂ := φ.map_add m₁ m₂ -- a simp lemma

-- exercise
example : φ (g • (m₁ + m₂)) = g • φ m₁ + g • φ m₂ :=
begin
  -- what will you rewrite? Will you rewrite at all?
  sorry
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
  -- what will you rewrite?
  sorry
end

-- Can you solve it in term mode like in those earlier examples?
example : φ 0 = 0 := sorry

-- Can you change `sorry` to the name of a tactic?
example : φ 0 = 0 := by sorry

-- You know how to compose functions, you just write `ψ (φ a)`
-- or whatever. Composition in the category of G-modules is
-- done with the `comp` method for `G`-module morphisms.


-- let P be another G-module
variables {P : Type} [add_comm_monoid P] [distrib_mul_action G P]

-- how to compose G-module maps
example (φ : M →+[G] N) (ψ : N →+[G] P) : M →+[G] P := ψ.comp φ

-- the proof of the theorem that composition of G-module maps evaluate
-- in the expected way is called `ψ.comp_apply` but it is also true
-- by definition and a `simp` lemma
example (φ : M →+[G] N) (ψ : N →+[G] P) (m : M) :
  ψ.comp φ m = ψ (φ m) := ψ.comp_apply φ m -- and `rfl` works too and `by simp`

variable (ψ : N →+[G] P)

-- By the way, `squeeze_simp` is a version of `simp` which tells you 
-- which rewrites it did. Give it a try!
example :
  ψ.comp φ (g • (m₁ + m₂)) = g • (ψ (φ m₁) + ψ (φ m₂)) :=
begin
  sorry,
end

end distrib_mul_action_hom

section group

-- Let A and B be G-modules
variables {G A B C : Type}
  [monoid G] [add_comm_group A] [add_comm_group B] [add_comm_group C]
  [distrib_mul_action G A] [distrib_mul_action G B] [distrib_mul_action G C]

def is_exact (φ : A →+[G] B) (ψ : B →+[G] C) : Prop :=
∀ b : B, ψ b = 0 ↔ ∃ a : A, φ a = b   

lemma is_exact_def (φ : A →+[G] B) (ψ : B →+[G] C) :
  is_exact φ ψ ↔ ∀ b : B, ψ b = 0 ↔ ∃ a : A, φ a = b :=
iff.rfl

-- tricky exercise: `is_exact_def'`. 
-- you'll need to know a bit about the sets API to do this,
-- Switch your infoview filter onto "only props" to get the noise
-- out of the way.
lemma is_exact_def' (φ : A →+[G] B) (ψ : B →+[G] C) :
  is_exact φ ψ ↔ ψ ⁻¹' {c : C | c = 0} = set.range φ :=
begin
  sorry
end

/-

## more than one "definition" of `is_exact`

Mathematicians have about three different ways of saying
a sequence is exact, and they're all "the definition".
That's why I proved the last two lemmas -- so we can use whichever
of the definitions is most use to us at the time. 

-/

open function

def is_short_exact (φ : A →+[G] B) (ψ : B →+[G] C) : Prop :=
  is_exact φ ψ ∧ injective φ ∧ surjective ψ

variables (φ : A →+[G] B) (ψ : B →+[G] C)

-- useful for rewrites
lemma is_short_exact_def :
  is_short_exact φ ψ ↔ is_exact φ ψ ∧ injective φ ∧ surjective ψ :=
-- true by definition
iff.rfl

-- Get some practice pulling off sub-facts from this compound fact.
example : is_short_exact φ ψ → injective φ :=
begin
  sorry,
end

end group

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