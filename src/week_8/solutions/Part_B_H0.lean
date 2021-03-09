import week_8.solutions.Part_A_G_modules

/-

# H⁰(G,M)

If G is a group and M is a G-module then H⁰(G,M) is the abelian group
of G-invariant elements of `M`. 

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

This makes `H0_submonoid G M`, a term (an additive subgroup of `M`, and
hence a term of type `add_subgroup M`). But we want to consider it as a type
in its own right. So let's beef it up.

-/

def H0 (G M : Type)
  [monoid G] [add_comm_group M] [distrib_mul_action G M] : Type :=
{m : M // ∀ g : G, g • m = m }

/-
`H0 G M` is now a type, a so-called subtype of `M` but a type in its
own right.

So how does this work? A term `a` of type `H0 G M` is a *pair* consisting
of a term `m : M` and a proof `hm : ∀ g, g • m = m`. Remember the following
important things:

`H0 G M` is a type, and if `a` is a term of this type, then `a` is not
a term of type `M`, it is a *pair*. The term of type `M` is called `a.val`
or `a.1`. The other term `a.2` of the pair is the *proof* that `a.1` is
G-invariant, i.e `a.2 : ∀ g, g • a.1 = a.1`. 

If you want to take `a` apart into its pieces `m` and `hm` then you
can do `cases a with m hm`. If there are still things like `⟨m, hm⟩.val`
left, you can get rid of them with `dsimp only`.

-/

-- let's make and prove stuff about `H0 G M` in the `H0` namespace.
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
-- that if we have a term `a : H0 G M` then, remembering that `a`
-- is actually a pair consisting of `a.val : M` and `a.2 : ∀ g, g • m = m`,
-- we want to be able to write `(a : M)` to mean `a.val : M`. 

instance : has_coe (H0 G M) M :=  ⟨λ a, a.val⟩ 

-- Lean will remind us that something funny (the coercion) is going on by 
-- writing `↑a : M` if `a : H0 G M`. So here `↑a` now means `a.val`.

@[simp] lemma coe_def (m : M) (hm : ∀(g : G), g • m = m) :
  ((⟨m, hm⟩ : H0 G M) : M) = m := rfl

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
-- Recall that `a` is a pair `a.1`, `a.2` with `a.1 = (a : M)` an element
-- of `M` and `a.2` a proof that it's `G`-invariant. And we need to come
-- up with a pair `b = ⟨b.1, b.2⟩` consisting of an element of `N` and
-- a proof that it too is `G`-invariant, plus a proof that this
-- construction commutes with addition.
def H0_hom (φ : M →+[G] N) : H0 G M →+ H0 G N :=
-- to make a group homomorphism we need to give a function and prove it 
-- preserves addition. Here's the constructor which does this: 
add_monoid_hom.mk'
-- We now need a function `H0 G M → H0 G N`, so say `a : H0 G M`.
-- Here's the element of `N`: just hit `a` (coerced to an element of `M`)
-- with `φ` (coerced to a function from `M` to `N`). 
begin
  -- the map is just `φ`
  refine (λ (a : H0 G M), (⟨φ a, _⟩ : H0 G N)),
  -- but we have to prove that if a is G-invariant then so is φ a
  -- in order to check this map is a well-defined map to `H0 G N`.
  -- I would recommend starting with `cases a with m hm` to take the pair
  -- apart and then `dsimp`.
  cases a with m hm,
  intro g,
  dsimp,
  rw [← φ.map_smul, hm],
end
-- and finally we need to prove that this map preserves addition.
begin
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
  simpa
end

theorem H0_hom.middle_exact (φ : M →+[G] N) (hφ : injective φ)
  (ψ : N →+[G] P) (he : is_exact φ ψ) : 
  φ.H0_hom.range = ψ.H0_hom.ker :=
begin
  ext x,
  rw add_monoid_hom.mem_ker,
  rw [H0.ext_iff, H0.coe_zero],
  rw H0_hom_coe_apply,
  unfold is_exact at he,
  rw he,
  split,
  { rintro ⟨⟨m, hm⟩, rfl⟩,
    exact ⟨m, rfl⟩ },
  { rintro ⟨m, hm⟩,
    refine ⟨⟨m, _⟩, _⟩,
    { intro g,
      apply hφ,
      rw map_smul,
      cases x with n hn,
      rw hm,
      exact hn g },
    { ext,
      exact hm } },
end

end distrib_mul_action_hom
