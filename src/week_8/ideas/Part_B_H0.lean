import week_8.ideas.Part_A_G_modules


/- 
-- move this?
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


/-

# Making the API for H⁰(G,M)

If `G` is a group and `M` is a G-module then H⁰(G,M), or `H0 G M`, is the abelian
group of G-invariant elements of `M`. We make the definition so we have
to make the interface too. We show that `H0 G M` is an abelian group,
define a coercion to `M` sending `m` to `↑m`, and define `m.spec` to be
the statement that `↑m` is G-invariant.

Let's start by giving a preliminary definition of H⁰ as an additive
subgroup of `M`.

-/

open set

/-- `H0 G M` is the type of G-invariant elements of M. -/
def H0_subgroup (G M : Type)
  [monoid G] [add_comm_group M] [distrib_mul_action G M] : add_subgroup M :=
{ carrier := {m | ∀ g : G, g • m = m },
  -- Need to check it's a subgroup.
  -- Axiom 1: zero in ("closed under `0`")
  zero_mem' := begin
    -- you can start with this
    rw mem_set_of_eq, -- says that `a ∈ { x | p x}` is the same as `p a`.
    -- can you take it from there?
    exact smul_zero,
  end,
  -- Axiom 2 : closed under `+`
  add_mem' := begin
    intros a b ha hb g,
    rw mem_set_of_eq at *, -- that's how I'd start
    rw [smul_add, ha, hb], -- then the sneaky refl closes the goal    
  end,
  -- Axiom 3 : closed under `-`
  neg_mem' := begin
    simp *,
  end }

/-

This makes `H0_subgroup G M`, a term (an additive subgroup of `M`, and
hence a term of type `add_subgroup M`). But this is no good -- we want
to consider functions `H⁰(G,M) → H⁰(G,N)` so we need a *type* `H0 G M`.
We need to promote the term to a type. We do this by using Lean's
theory of subtypes, with notation `{ x // P x }` (a type) as oppposed to 
the set-theoretic `{ x | P x }` (a term)

-/

/-- Group cohomology `H⁰(G,M)` as a type. -/
def H0 (G M : Type)
  [monoid G] [add_comm_group M] [distrib_mul_action G M] : Type :=
{m : M // ∀ g : G, g • m = m }

-- let's make an API and prove stuff about `H0 G M` in the `H0` namespace.
namespace H0

-- let `G` be a group (or a monoid) and let `M` be a `G`-module.
variables {G M : Type}
  [monoid G] [add_comm_group M] [distrib_mul_action G M]

/-
We have defined `H0 G M` to be a type, a so-called subtype of `M`,
but a type in its own right. It has terms of its own (unlike `S : set M`
or `A : add_subgroup M`)

So how does this work? A term `m` of type `H0 G M` is a *package* consisting
of a term `m.1 : M` and a proof `m.2 : ∀ g, g • m.1 = m.1`. We do not
want to use these internal computer science terms for this package
of information, we want a nice interface. Below we use coercion, to turn
a term `m : H0 G M` into a term `↑m : M`.  

-/

/-- set up coercion from `H⁰(G,M) to M`, sending `m` to `↑m` -/
instance : has_coe (H0 G M) M :=
-- this is the last time we see `m.1`
⟨λ m, m.1⟩

-- That's a definition, so we need to make a little API.

/-- If `a : M` then `↑⟨a, ha⟩ = a` -/
@[simp] lemma coe_def (a : M) (ha : ∀(g : G), g • a = a) :
  ((⟨a, ha⟩ : H0 G M) : M) = a := rfl

-- this is our nice interface
lemma spec (m : H0 G M) : ∀ (g : G), g • (m : M) = m :=
-- this is the last time we see `m.2`
m.2

/-

The idea now is that we should avoid `m.1` and `m.2` completely,
and use `m : M` or `↑m` for the element of the module, and `m.spec` for
the proof that it is `G`-invariant.

## Basic Infrastructure

We have made a new definition, `H0`, and now we need to make it easier
to use. Things we do here: 

* We want to get (for free) that `H0 G M` is a group (so we need to put
  this fact into the type class mechanism).

* We want to know that two terms of type `H0 G M` are equal if
  and only if the corresponding terms of type `M` are equal (so we want to
  prove an extensionality lemma).

* We want to know that things like 0 and addition coincide in `M`
  and `H0 G M` (the coercion is a group homomorphism)

Let's start by making H⁰(G, M) a.k.a. `H0 G M` into a group. This is easy
because `H0 G M` is the type corresponding to the term `H0_subgroup G M`
which is a subgroup, hence a group.

-/

-- tell type class inference that `H0 G M` is a group
instance : add_comm_group (H0 G M) :=
add_subgroup.to_add_comm_group (H0_subgroup G M)

-- Let's now prove an ext_iff lemma (useful for rewriting)
lemma ext_iff (m₁ m₂ : H0 G M) : m₁ = m₂ ↔ (m₁ : M) = (m₂ : M) := 
begin
  split,
  { rintro rfl, refl },
  { ext }
end

-- Let's tell the simplifier how the group structure (addition, 0, negation
-- and subtraction) works with respect to the coercion. All the proofs
-- are true by definition

@[simp] lemma coe_add (a b : H0 G M) :
  ((a + b : H0 G M) : M) = a + b := rfl

@[simp] lemma coe_zero : ((0 : H0 G M) : M) = 0 := rfl

@[simp] lemma coe_neg (a : H0 G M) :
  ((-a : H0 G M) : M) = -a := rfl

-- we'll never use it but what the heck, others might
@[simp] lemma coe_sub (a b : H0 G M) :
  ((a - b : H0 G M) : M) = a - b := rfl

-- try these
example (m₁ m₂ m₃ : H0 G M) : m₁ + (m₂ - m₁ + m₃) = m₃ + m₂ :=
begin
  -- which tactic?
  abel
end

example (g : G) (m : H0 G M) : g • (m + m : M) = m + m :=
begin
  -- can you help the simplifier?
  simp [m.spec g],
end




end H0

/-

## API for the interaction of G-module maps and our new definition `H⁰`

Now let's prove that a G-module map `φ : M →+[G] N` induces a natural
abelian group hom `φ.H0 : H⁰(G,M) →+ H⁰(G,N)`. I would rather do this in
`φ`'s namespace, which is `distrib_mul_action_hom`, because then
I can write `φ.H0` directly.

-/


namespace distrib_mul_action_hom

variables {G M N : Type}
  [monoid G] [add_comm_group M] [add_comm_group N]
  [distrib_mul_action G M] [distrib_mul_action G N]
  (a : M) (b : N)

-- Let's first define the group homomorphism `H0 G M →+ H0 G N` induced by `φ`.
-- Recall that the constructor of `H0 G N` needs as input a pair consisting
-- of `b : N` and `hb : ∀ g, g • b = b`, and we make the element of `H0 G N`
-- using the `⟨b, hb⟩` notation.

/- The function underlying the group homomorphism `H⁰(G,M) → H⁰(G,N)`
   induced by a `G`-equivariant group homomorphism `φ : M →+[G] N` -/
def H0_underlying_function (φ : M →+[G] N) (m : H0 G M) : H0 G N :=
⟨φ m, begin
  -- use φ.map_smul and a.spec to prove that this map is well-defined.
  -- Remember that `rw` doesn't work under binders, and ∀ is a binder, so start
  -- with `intros`.
  intros,
  rw [←φ.map_smul, m.spec],
end⟩

/-- The group homomorphism  `H⁰(G,M) →+ H⁰(G,N)`
   induced by a `G`-equivariant group homomorphism `φ : M →+[G] N` -/
def H0 (φ : M →+[G] N) : H0 G M →+ H0 G N :=
-- to make a group homomorphism we need apply a constructor
add_monoid_hom.mk'
-- to the function we just made
(H0_underlying_function φ)
-- and then prove that this function preserves addition.
begin
  intros a b,
  simp only [H0_underlying_function],
  ext,
  simp,
end

end distrib_mul_action_hom

-- The API for `φ.H0` starts here

namespace H0

variables {G M N : Type}
  [monoid G] [add_comm_group M] [add_comm_group N]
  [distrib_mul_action G M] [distrib_mul_action G N]
  (a : M) (b : N)

/-

## An API for `φ.H0`

So now if `φ : M →+[G] N` is a G-module homomorphism, we can talk
about `φ.H0 : H0 G M →+ H0 G N`, an abelian group homomorphism 
from H⁰(G,M) to H⁰(G,N).

As ever, this is a definition so we need to make a little API.
We start with the following handy fact:

Given a G-module map `φ : M →+[G] N`, The following diagram commutes:

            φ
  M ----------------> N
  /\                  /\
  | coercion ↑        | coercion ↑
  |                   |
  |                   |
H⁰(G,M) ---------> H⁰(G,N)
-/
@[simp] lemma coe_apply (m : H0 G M) (φ : M →+[G] N) :
  ((φ.H0 m) : N) = φ m :=
begin
  -- Look at the goal the way I have written it.
  -- Unfold the definitions. It's true by definition.
  -- Look at the goal the way Lean is displaying it
  -- right now. It's just coercions everywhere. Ignore them.
  refl,
end

open distrib_mul_action_hom

-- If you're in to that sort of thing, you can prove that `φ.H0`
-- is functorial. That's it and comp.
def id_apply (m : H0 G M) :
  (distrib_mul_action_hom.id G).H0 m = m :=
begin
  -- remember extensionality. 
  ext,
  refl,
end

variables {P : Type} [add_comm_group P] [distrib_mul_action G P]

def comp (φ : M →+[G] N) (ψ : N →+[G] P) :
  (ψ ∘ᵍ φ).H0 = ψ.H0.comp φ.H0 := 
begin
  refl,
end

end H0

/-

## First exactness result

If 0 → M → N → P → 0 is a short exact sequence, then there
is a long exact sequence

0 → H⁰(G,M) → H⁰(G,N) → H⁰(G,P)

and we can't go any further because we haven't defined H¹! This boils
down to two theorems; let's prove them.

-/
open function

open distrib_mul_action_hom

variables {G M N P : Type}
  [monoid G] [add_comm_group M] [add_comm_group N] [add_comm_group P]
  [distrib_mul_action G M] [distrib_mul_action G N] [distrib_mul_action G P]
  (a : M) (b : N)


-- 0 → H⁰(G,M) → H⁰(G,N) is exact, i.e. φ.H0 is injective
theorem H0_hom.left_exact (φ : M →+[G] N) (hφ : injective φ) : 
  injective φ.H0 :=
begin
  intros a b h,
  ext, 
  apply hφ,
  rw H0.ext_iff at h,
  simpa using h,
end


-- H⁰(G,M) → H⁰(G,N) → H⁰(G,P) is exact, i.e. an image equals a kernel.
theorem H0_hom.middle_exact (φ : M →+[G] N) (hφ : injective φ)
  (ψ : N →+[G] P) (he : is_exact φ ψ) : 
  φ.H0.range = ψ.H0.ker :=
begin
  ext x,
  rw add_monoid_hom.mem_ker,
  rw [H0.ext_iff, H0.coe_zero],
  rw H0.coe_apply,
  rw is_exact.def at he,
  rw ← he,
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
    let a : _root_.H0 G M := ⟨m, hm⟩,
    have ha : (a : M) = m := rfl,
    use a,
    ext,
    -- next line not necessary as both proofs are `rfl`
    rw [H0.coe_apply, ha],
    exact hmx },
end
