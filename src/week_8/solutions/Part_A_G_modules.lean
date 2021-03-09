import tactic
import algebra.group_action_hom
import data.nat.prime
/-

# G-modules

Let `A` be an abelian group (we will use the group law `+`) and
let `G` be a group (we will use the group law `*`). A `G`-action
on `A` is just a group homomorphism from `G` to the group automorphisms
of `A`, or in other words an action `•` of `G` on `A` satisfying
the axiom `g • (a + b) = g • a + g • b`.

-/

section G_module

-- we don't even need to assume `G` is a group and `A` is an additive 
-- abelian group, we can get away with `G` being a monoid and `A` an 
-- additive abelian monoid.
variables {G A : Type} [monoid G] [add_comm_monoid A] [distrib_mul_action G A]
  (g h : G) (a a' : A)

example : (g * h) • a = g • (h • a) := mul_smul g h a
example : g • (a + a') = g • a + g • a' := smul_add g a a' 
example : (1 : G) • a = a := one_smul G a
example : g • (0 : A) = 0 := smul_zero g

-- If `B` is an abelian group (rather than just a monoid)
-- then we have two more basic facts:
variables (B : Type) [add_comm_group B] [distrib_mul_action G B] (b b' : B)

example : g • (-b) = -(g • b) := smul_neg g b
example : g • (b - b') = g • b - g • b' := smul_sub g b b'

end G_module

/-

Lean also has G-invariant subsets (`sub_mul_action G A`)
but not G-invariant subgroups. I'm not sure we'll need them though.
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

example (f : A →+[G] B) (a : A) : B := f a

-- Now we need to restate some lemmas.

-- let `f` be a G-module hom from A to B.
variable (f : A →+[G] B)

example (g : G) (a : A) : f (g • a) = g • (f a) := f.map_smul g a
example (a b : A) : f (a + b) = f a + f b := f.map_add a b
example (a b : A) : f 0 = 0 := f.map_zero -- can they guess?

example : A →+[G] A := distrib_mul_action_hom.id G

variables {C : Type} [add_comm_monoid C] [distrib_mul_action G C]

example (φ : A →+[G] B) (ψ : B →+[G] C) : A →+[G] C := ψ.comp φ

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