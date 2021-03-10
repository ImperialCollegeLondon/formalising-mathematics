import tactic
import algebra.group_action_hom
import data.nat.prime
/-

# G-modules

Let `G` be a group (with group law `*`) and let `M` be an abelian
group (with group law `+`). A `G`-action on `M` is just a group
homomorphism from `G` to the group automorphisms
of `A`, or in other words an action `•` of `G` on `A` satisfying
the axiom `g • (a + b) = g • a + g • b`.

Note that this definition does not mention `g⁻¹` at all, so
we can even define it for monoids `G`, which we will.

-/

section G_module

-- Let `G` be a group (or just a monoid) and let `M` be a `G`-module.
variables {G M : Type} [monoid G] [add_comm_group M] [distrib_mul_action G M]

-- Let g and h be elements of `G`, and let `m` and `m'` be elements of `M`. 
variables (g h : G) (m m' : M)

-- Here is the API that you need to know -- the names of the axioms
-- and basic facts which will come up again and again. Note that many
-- of them are marked `@[simp]` -- if you are trying to prove an equality
-- in this workshop, give `simp` a go to see if it makes progress.
example : (g * h) • m = g • (h • m) := mul_smul g h m
example : g • (m + m') = g • m + g • m' := smul_add g m m' 
example : (1 : G) • m = m := one_smul G m
example : g • (0 : M) = 0 := smul_zero g
example : g • (-m) = -(g • m) := smul_neg g m
example : g • (m - m') = g • m - g • m' := smul_sub g m m'

-- example
#print smul_zero -- mentions "@[simp]" at the top

end G_module

/-

Lean also has G-invariant subsets (`sub_mul_action G A`)
but not G-invariant subgroups. It is well-understood how
to set these things up, both the definitions and the API
are standard, and one key theorem is that G-invariant subgroups
are a complete lattice, whose proof should go via a Galois
correspondence with G-invariant subsets.

I'm not sure we'll need them though.
We will _definitely_ need maps between G-modules though, so
let's talk about these next.

## Morphisms of G-modules

These are called `A →+[G] B`.

-/

section morphisms

-- Let A and B be G-modules

variables {G A B : Type}
  [monoid G] [add_comm_monoid A] [add_comm_monoid B]
  [distrib_mul_action G A] [distrib_mul_action G B]
-- Let `f` be a morphism of `G`-modules, i.e. an abelian group
-- homomorphism which commutes with the `G`-action.
  (f : A →+[G] B)
-- let `a` be an element of `A`.
  (a : A)

-- Now check this out!
example : B := f a

-- `a` is in `A` and we can apply `f` to get `f a` in `B`! 
-- That is not a big surprise to mathematicians!
-- But something funny is going on in Lean. 
-- Hover over the `#check` to see:

#check f a -- ⇑f a : B

-- What is this `⇑f`? The point is that in Lean a morphism
-- of G-modules is *not a function*. It is a term of another
-- kind of type, called a "bundled function type". To make
-- a term of this type you have to give Lean two things:
-- firstly, an *actual function*, and secondly *some proofs*
-- namely, the hypotheses that your function satisfies the
-- axioms. Bundled functions like `f : A →+[G] B`
-- are then not *literally* functions. Lean uses the notation `⇑f`
-- to mean "the underlying function", and it then offers
-- you an *interface* where the axioms for the function
-- are accessed via something called "dot notation". 
-- Because `f` is of the "G-module homomorphism type",
-- known for some unearly reason as `distrib_mul_action_hom`
-- in Lean, you can access theorems like `⇑f (x + y) = ⇑f x + ⇑f y`
-- (whose full name is `distrib_mul_action_hom.map_add`), by
-- simply writing `f.map_add` (this is called the dot notation trick).
-- The idea you should keep in mind is that `⇑f` is the
-- actual function and `f` is the package consisting of
-- the function and all of the axioms. But we are lazy and write
-- `f` a lot of the time when we mean `⇑f` because Lean lets us
-- do it. Pay close attention to the tactic state to see when
-- this trickery is happening.

-- Here is the API for `distrib_mul_action_hom`.

example (g : G) (a : A) : f (g • a) = g • (f a) := f.map_smul g a
example (a b : A) : f (a + b) = f a + f b := f.map_add a b
example : f 0 = 0 := f.map_zero -- can they guess? (sorry this out)

example : A →+[G] A := distrib_mul_action_hom.id G

variables {C : Type} [add_comm_monoid C] [distrib_mul_action G C]

example (φ : A →+[G] B) (ψ : B →+[G] C) : A →+[G] C := ψ.comp φ

example (φ : A →+[G] B) (ψ : B →+[G] C) (a : A) :
  ψ.comp φ a = ψ (φ a) := rfl

-- everything "obvious" can be proved from the axioms
-- and the cool thing is that they're all tagged with `simp`.
example (φ : A →+[G] B) (ψ : B →+[G] C) (a a' : A) (g : G) : 
  ψ.comp φ (g • (a + a')) = g • (ψ (φ a) + ψ (φ a')) :=
begin
  simp,   
end

-- is there anything here? Exactness!

end morphisms

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

open function

def is_short_exact (φ : A →+[G] B) (ψ : B →+[G] C) : Prop :=
  is_exact φ ψ ∧ injective φ ∧ surjective ψ

end group

/-

# Coercions

Something which will come up again and again today is the concept of a
coercion. 
-/