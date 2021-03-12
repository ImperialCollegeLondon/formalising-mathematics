import week_8.ideas.Part_C_H1
/-

# Boundary maps

If 0 → A → B → C → 0 is exact, we want
a boundary map `H0 G C →+ H1 G A`

We're going to use the axiom of choice in our definition.
Whenever we invoke the axiom of choice we are using something
noncomputable, so it's important that we make a proper API
for the object we construct.

-/

-- missing?
section missing

variables {A B : Type*} [group A] [group B]
  (f : A →* B) (a1 a2 : A)

@[to_additive] lemma monoid_hom.map_div (a1 a2 : A) :
  f (a1 / a2) = f a1 / f a2 :=
by simp [div_eq_mul_inv]

@[simp, to_additive] lemma group.div_self (a : A) : a / a = 1 :=
by simp [div_eq_mul_inv]

@[simp, to_additive] lemma group.div_eq_one_iff (a1 a2 : A) : a1 / a2 = 1 ↔ a1 = a2 :=
⟨by simp [div_eq_mul_inv, mul_eq_one_iff_eq_inv], by {rintro rfl, simp}⟩

@[to_additive] lemma monoid_hom.div_mem_ker (f : A →* B) (a1 a2 : A) :
  a1 / a2 ∈ f.ker ↔ f a1 = f a2 :=
begin
  rw monoid_hom.mem_ker,
  rw f.map_div,
  rw group.div_eq_one_iff,
end

namespace boundary_map

variables {G M N P : Type} [monoid G]
  [add_comm_group M] [distrib_mul_action G M]
  [add_comm_group N] [distrib_mul_action G N]
  [add_comm_group P] [distrib_mul_action G P]
  {φ : M →+[G] N} {ψ : N →+[G] P} (hse : is_short_exact φ ψ)

include hse

noncomputable def raw_boundary_function : H0 G P → (G → M) :=
λ p g, hse.inverse_φ (g • (hse.inverse_ψ p) - hse.inverse_ψ p) 
begin
  rw ← hse.exact_def,
  simp [hse.inverse_ψ_spec, p.spec],
end

lemma raw_boundary_function.is_cocycle
  {p : H0 G P} : is_cocycle (raw_boundary_function hse p) :=
begin
  intros g h,
  unfold raw_boundary_function,
  apply hse.injective,
  -- should `smul_sub` be a `simp` lemma?
  simp [mul_smul, smul_sub],
end

noncomputable def delta : H0 G P →+ H1 G M :=
{ to_fun := λ p, Z1.quotient
  { to_fun := raw_boundary_function hse p,
    is_cocycle := raw_boundary_function.is_cocycle hse },
  map_zero' := begin
    rw ← add_monoid_hom.mem_ker,
    rw H1.ker_quotient,
    simp [raw_boundary_function],
    refine ⟨hse.inverse_φ (hse.inverse_ψ 0) _, _⟩,
    { rw ← hse.exact_def,
      rw hse.inverse_ψ_spec },
    ext g,
    simp,
    apply hse.injective,
    simp [hse.inverse_φ_spec],
  end,
  map_add' := begin
    intros p q,
    rw ← add_monoid_hom.map_add,
    rw ← add_monoid_hom.sub_mem_ker,
    rw H1.ker_quotient,
    have crucial :
      ∃ m : M, φ m = hse.inverse_ψ (↑p + ↑q) - hse.inverse_ψ p - hse.inverse_ψ q,
    { simp [← hse.exact_def] },
    refine ⟨hse.inverse_φ _ crucial, _⟩,
    ext g,
    simp [cochain_map, Z1.coe_add, raw_boundary_function],
    apply hse.injective,
    simp [smul_sub],
    abel,
  end }

/-

todo
In Part D of this week's workshop we will define
a boundary map `H0 G C →+ H1 H A` coming from a short
exact sequence of `G`-modules. In this definition we make
a choice of sign ("do we use `g b - b` or `b - g b`?"). 
The final boss of this course
is verifying the first seven terms of the long exact sequence
of group cohomology associated to a short exact sequence of
G-modules.

TODO

boundary map def

boundary map API

7 term exact sequnce

inf-res

-/

def bound