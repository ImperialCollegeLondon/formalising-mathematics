import week_8.solutions.Part_A_G_modules

/-

# H⁰(G,M)

If G is a group and M is a G-module then H⁰(G,M) is the abelian group
of G-invariant elements of `M`. Let's define it first as a subgroup of `M`.

-/

/-- `H0 G M` is the type of G-invariant elements of M. -/
def H0_subgroup (G M : Type)
  [monoid G] [add_comm_group M] [distrib_mul_action G M] : add_subgroup M :=
{ carrier := {m | ∀ g : G, g • m = m },
  zero_mem' := begin
    exact smul_zero,
  end,
  add_mem' := begin
    intros a b ha hb g,
    rw [smul_add, ha, hb], -- then the sneaky refl closes the goal    
  end,
  neg_mem' := begin
    intros a ha g,
    rw [smul_neg, ha],
  end }

/-

This makes `H0_subgroup G M`, a term (an additive subgroup of `M`, and
hence a term of type `add_subgroup M`). But this is no good -- we want
to consider functions `H⁰(G,M) → H⁰(G,N)` so we need a *type* `H0 G M`.
We need to promote the term to a type. We do this by using Lean's
theory of subtypes, with notation `{ x // P x }` as oppposed to 
the set-theoretic `{ x | P x }`. 

-/

/-- Group cohomology `H⁰(G,M)` as a type. -/
def H0 (G M : Type)
  [monoid G] [add_comm_group M] [distrib_mul_action G M] : Type :=
{m : M // ∀ g : G, g • m = m }

/-
`H0 G M` is now a type, a so-called subtype of `M` but a type in its
own right.

So how does this work? A term `a` of type `H0 G M` is a *pair* consisting
of a term `m : M` and a proof `hm : ∀ g, g • m = m`. If you want to be
all "computer sciency" you can access the elements of this pair as
follows: `m` is just `a.1` or `a.val`, and `hm` is just `a.2`. 

I regard such vulgar computerscienceisms like `a.2` as "breaking the
interface". This is not how mathematicians think of things. We are
going to fix this by setting up another coercion, to be instead of `a.1`,
and writing a small API (one function) to be used instead of `a.2`. 

-/

-- let's make an API and prove stuff about `H0 G M` in the `H0` namespace.
namespace H0

-- let `G` be a group (or a monoid) and let `M` be a `G`-module.
variables {G M : Type}
  [monoid G] [add_comm_group M] [distrib_mul_action G M]

/-

## Boring infrastructure

We have made a new definition, `H0`, and now we make it easier
to use. Things we do here: 

* We want to get (for free) that `H0 G M` is a group.

* We want to be able to pass easily between terms of type `H0 G M`
  and terms of type `M`, so we set up a coercion.

* We want easy access to the proof that an element of `H0 G M` is
  G-invariant, and we can do this using dot notation `a.spec`.

* We want to know that two terms of type `H0 G M` are equal if
  and only if the corresponding terms of type `M` are equal.

* We want to know that things like 0 and addition coincide in `M`
  and `H0 G M`.


Let's start by making H⁰(G, M) a.k.a. `H0 G M` into a group. This is easy
because `H0 G M` is the type corresponding to the term `H0_subgroup G M`
which is a subgroup, hence a group.

-/

instance : add_comm_group (H0 G M) :=
add_subgroup.to_add_comm_group (H0_subgroup G M)

-- Now let's set up the coercion from `H0 G M` to `M`, which means
-- that if we have a term `a : H0 G M` then we will just be able to write
-- `a : M` to refer to the underlying element `m = a.val` of `M`.

instance : has_coe (H0 G M) M :=  ⟨λ a, a.val⟩ 

-- Lean will remind us that something funny (the coercion) is going on by 
-- writing `↑a : M` if `a : H0 G M`. So here `↑a` now means `a.val`.

@[simp] lemma coe_def (m : M) (hm : ∀(g : G), g • m = m) :
  ((⟨m, hm⟩ : H0 G M) : M) = m := rfl

-- We want to be able to have easy access to the assertion that if `a : H0 G M`
-- then the coerced `↑a : M` is `G`-invariant.

-- this is our nice interface
lemma spec (a : H0 G M) : ∀ (g : G), g • (a : M) = a :=
-- this is something we will now never see again
a.2

-- The idea now is that we should avoid `a.1` and `a.2` completely,
-- and use `a : M` or `↑a` for the element of the module, and `a.spec` for
-- the proof that it is `G`-invariant.

-- Let's now prove some useful ext lemmas:
lemma ext_iff (a b : H0 G M) : a = b ↔ (a : M) = b := 
begin
  split,
  { rintro rfl, refl },
  { ext }
end

-- Let's tell the simplifier how the group structure (addition, 0, negation
-- and subtraction) works with respect to the coercion.

@[simp] lemma coe_add (a b : H0 G M) :
  ((a + b : H0 G M) : M) = a + b := rfl

@[simp] lemma coe_zero : ((0 : H0 G M) : M) = 0 := rfl

@[simp] lemma coe_neg (a : H0 G M) :
  ((-a : H0 G M) : M) = -a := rfl

-- we'll never use it but what the heck, others might
@[simp] lemma coe_sub (a b : H0 G M) :
  ((a - b : H0 G M) : M) = a - b := rfl

/-

Now let's prove that a G-module map `φ : M →+[G] N` induces a natural
abelian group hom `H0_hom : H⁰(G,M) → H⁰(G,N)`. I would rather do this in
`φ`'s namespace, which is `distrib_mul_action_hom`, because then
I can write `φ.H0_hom` directly.

-/

end H0

namespace distrib_mul_action_hom

variables {G M N : Type}
  [monoid G] [add_comm_group M] [add_comm_group N]
  [distrib_mul_action G M] [distrib_mul_action G N]

-- Let's first define the group homomorphism `H0 G M →+ H0 G N` induced by `φ`.
-- Recall that the constructor of `H0 G N` needs as input a pair consisting
-- of `n : N` and `hn : ∀ g, g • n = n`, and we make the element of `H0 G N`
-- using the `⟨n, hn⟩` notation.

/- The function underlying the group homomorphism `H⁰(G,M) → H⁰(G,N)`
   induced by a `G`-equivariant group homomorphism `φ : M →+[G] N` -/
def H0_hom_underlying_function (φ : M →+[G] N) (a : H0 G M) : H0 G N :=
⟨φ a, begin
  -- use φ.map_smul and a.spec to solve this goal. Remember that
  -- `rw` doesn't work under binders, and ∀ is a binder.
  intro g,
  rw ←φ.map_smul,
  rw a.spec,
end⟩

/-- The group homomorphism  `H⁰(G,M) →+ H⁰(G,N)`
   induced by a `G`-equivariant group homomorphism `φ : M →+[G] N` -/
def H0_hom (φ : M →+[G] N) : H0 G M →+ H0 G N :=
-- to make a group homomorphism we need apply a constructor
add_monoid_hom.mk'
-- to the function we just made
(H0_hom_underlying_function φ)
-- and then prove that this function preserves addition.
begin
  unfold H0_hom_underlying_function,
  intros a b,
  ext,
  simp
end

/-
So now if `φ : M →+[G] N` is a G-module homomorphism, we can talk
about `φ.H0_hom : H0 G M →+ H0 G N`, an abelian group homomorphism 
from H⁰(G,M) to H⁰(G,N).

As ever, this is a definition so we need to make a little API.
Here is a handy fact:

Given a G-module map `φ : M →+[G] N`, The following diagram commutes:

        φ.H0_hom
H⁰(G,M) ---------> H⁰(G,N)
  |                   |
  | coercion ↑        | coercion ↑
  |                   |
  \/       φ          \/
  M ----------------> N
-/
@[simp] lemma H0_hom_coe_apply (φ : M →+[G] N) (a : H0 G M) :
(↑(φ.H0_hom a) : N) = φ ↑a := rfl

-- Let's prove H0_hom is functorial.
-- or is this just a waste of their time?
def H0_hom_id : H0_hom (distrib_mul_action_hom.id G : M →+[G] M) =
  add_monoid_hom.id _ :=
begin
  ext x,
  refl,
end

variables {P : Type} [add_comm_group P] [distrib_mul_action G P]

def H0_hom_comp (φ : M →+[G] N) (ψ : N →+[G] P) :
  H0_hom (ψ.comp φ) = ψ.H0_hom.comp φ.H0_hom := 
begin
  ext x,
  refl,
end

-- Now let's prove some exactness

open function

theorem H0_hom.left_exact (φ : M →+[G] N) (hφ : injective φ) : 
  injective φ.H0_hom :=
begin
  intros a b h,
  ext, 
  apply hφ,
  rw H0.ext_iff at h,
  -- next line not necessary as the proof of H0_hom_coe_apply is `rfl`
  rw [H0_hom_coe_apply, H0_hom_coe_apply] at h,
  exact h,
end

theorem H0_hom.middle_exact (φ : M →+[G] N) (hφ : injective φ)
  (ψ : N →+[G] P) (he : is_exact φ ψ) : 
  φ.H0_hom.range = ψ.H0_hom.ker :=
begin
  ext x,
  rw add_monoid_hom.mem_ker,
  rw [H0.ext_iff, H0.coe_zero],
  rw H0_hom_coe_apply,
  rw is_exact_def at he,
  rw he,
  rw add_monoid_hom.mem_range,
  split,
  { rintro ⟨a, rfl⟩,
    exact ⟨a, rfl⟩ },
  { rintro ⟨m, hmx⟩,
    -- I claim `m` is G-invariant
    have hm : ∀ (g : G), g • m = m,
    { intro g,
      apply hφ,
      rw [φ.map_smul, hmx],
      apply x.spec },
    let a : H0 G M := ⟨m, hm⟩,
    have ha : (a : M) = m := rfl,
    use a,
    ext,
    -- next line not necessary as both proofs are `rfl`
    rw [H0_hom_coe_apply, ha],
    exact hmx },
end

end distrib_mul_action_hom
