import week_8.ideas.Z1

/-

## The map `φ.Z1 : Z1 G M →+ Z1 G N`.

Let `G` be a group. Or a monoid.

`Z1` is not just the construction of the group of cocycles
associated to a `G`-module `M`. `Z1` is a functor, which
means that we well as sending G-modules to abelian groups,
it also sends morphisms of `G`-modules to morphisms of abelian groups
(a new definition) and satisfies some theorems (the axioms
for a functor).

This file essentially all takes place in the `distrib_mul_hom`
namespace, because we are building more interface for `φ : M →+[G] N`. 
We access this interface via dot notation. For example
`φ.Z1` is the group homomorphism `Z1 G M → Z1 G N`. In fact
this is main definition of the file. 

### Definition of `φ.Z1 : Z1 G M →+ Z1 G N`



In this file we define the following function:
Given as input `φ : M →+[G] N` a G-module homomorphism, 
we define the ouput `φ.Z1`, a group homomorphism `Z1 G M → Z1 G N`.

This is a two step process: first we define the underlying function,
we then prove that it's a group homomorphism.


3) the proof that the construction sending `φ` to `φ.Z1` is
functorial, i.e. sends the identity `id : M →+[G] M` to the identity
and function composition to function composition. 
-/

namespace distrib_mul_action_hom

-- The Z1 construction is functorial in the module `M`. Let's construct
-- the relevant function, showing that if `φ : M →+[G] N` then
-- composition induces an additive group homomorphism `Z1 G M → Z1 G N`.
-- Just like `H0` we first define the auxiliary bare function, 
-- and then beef it up to an abelian group homomorphism.

variables {G M N : Type} [monoid G] 
  [add_comm_group M] [distrib_mul_action G M]
  [add_comm_group N] [distrib_mul_action G N]

-- note to self: if I change to Z1.coe_fn then I get a weird error
def Z1_coe_fn (φ : M →+[G] N) (f : Z1 G M) : Z1 G N :=
⟨λ g, φ (f g), begin
  -- need to prove that this function obtained by composing the cocycle
  -- f with the G-module homomorphism φ is also a cocycle.
  simp [←φ.map_smul, -map_smul, f.spec]
end⟩

@[norm_cast] 
lemma Z1_coe_fn_coe_comp (φ : M →+[G] N) (f : Z1 G M) (g : G) :
  (Z1_coe_fn φ f g : N) = φ (f g) := rfl

def Z1 (φ : M →+[G] N) : Z1 G M →+ Z1 G N :=
-- to make a term of type `X →+ Y` (a group homomorphism) from a function
-- `f : X → Y` and
-- a proof that it preserves addition we use the following constructor:
add_monoid_hom.mk' 
-- We now throw in the bare function
(Z1_coe_fn φ)
-- (or could try direct definition:)
-- (λ f, ⟨λ g, φ (f g), begin
--   -- need to prove that this function obtained by composing the cocycle
--   -- f with the G-module homomorphism φ is also a cocycle.
--   intros g h,
--   rw ←φ.map_smul,
--   rw f.spec,
--   simp,
-- end⟩)
-- and now the proof that it preserves addition
begin
  intros e f,
  ext g,
  simp [φ.Z1_coe_fn_coe_comp],
end

-- it's a functor
variables {P : Type} [add_comm_group P] [distrib_mul_action G P]

def map_comp (φ: M →+[G] N) (ψ : N →+[G] P) (z : _root_.Z1 G M) :
  (ψ.Z1) ((φ.Z1) z) = (ψ.comp φ).Z1 z :=
begin
  refl,
end

@[simp] lemma Z1_spec (φ : M →+[G] N) (a : _root_.Z1 G M) (g : G) : 
  φ.Z1 a g = φ (a g) := rfl

@[simp] lemma Z1_spec' (φ : M →+[G] N) (a : _root_.Z1 G M) (g : G) : 
  (φ.Z1 a : G → N) = (φ ∘ a) := rfl
end distrib_mul_action_hom
