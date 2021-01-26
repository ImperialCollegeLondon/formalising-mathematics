import week_2.Part_A_groups

/-!

## Subgroups

Lean has subgroups already, so we'll call ours subgroup2.

-/

/-- A subgroup2 of a group G is a subset containing 1
and closed under multiplication and inverse. -/
structure subgroup2 (G : Type) [group2 G] :=
(carrier : set G)
(one_mem' : (1 : G) ∈ carrier)
(mul_mem' {x y} : x ∈ carrier → y ∈ carrier → x * y ∈ carrier)
(inv_mem' {x} : x ∈ carrier → x⁻¹ ∈ carrier)


-- we put dashes in all the names, because we'll define
-- non-dashed versions which don't mention `carrier` at all
-- and just talk about elements of the subgroup2.

namespace subgroup2

variables {G : Type} [group2 G] (H : subgroup2 G)

-- Instead let's define ∈ directly
instance : has_mem G (subgroup2 G) := ⟨λ m H, m ∈ H.carrier⟩

-- subgroups form a lattice -- MOVE TO LATER
instance : has_le (subgroup2 G) := ⟨λ S T, S.carrier ⊆ T.carrier⟩

/-- Two subgroups are equal if the underlying subsets are equal. -/
theorem ext' {H K : subgroup2 G} (h : H.carrier = K.carrier) : H = K :=
by cases H; cases K; congr'

/-- Two subgroup2s are equal if they have the same elements. -/
theorem ext {H K : subgroup2 G}
  (h : ∀ x, x ∈ H ↔ x ∈ K) : H = K := ext' $ set.ext h

lemma mem_coe {g : G} : g ∈ H.carrier ↔ g ∈ H := iff.rfl

/-- Two subgroup2s are equal if and only if the underlying subsets are equal. -/
protected theorem ext'_iff {H K : subgroup2 G} :
  H.carrier = K.carrier ↔ H = K :=
⟨ext', λ h, h ▸ rfl⟩

attribute [ext] subgroup2.ext

/-- A subgroup2 contains the group's 1. -/
theorem one_mem : (1 : G) ∈ H := H.one_mem'

/-- A subgroup2 is closed under multiplication. -/
theorem mul_mem {x y : G} : x ∈ H → y ∈ H → x * y ∈ H := subgroup2.mul_mem' _

/-- A subgroup2 is closed under inverse -/
theorem inv_mem {x : G} : x ∈ H → x⁻¹ ∈ H := subgroup2.inv_mem' _ 

/-- A subgroup2 is closed under integer powers -/
theorem pow_mem {x : G} {n : ℤ} : x ∈ H → x ^ n ∈ H :=
begin
  sorry -- do I do this?
end

@[simp] theorem inv_mem_iff {x :G} : x⁻¹ ∈ H ↔ x ∈ H := 
  ⟨ λ hx, inv_inv x ▸ H.inv_mem hx, H.inv_mem ⟩ 

-- Coersion to group
-- Coercion from subgroup2 to underlying type

instance : has_coe (subgroup2 G) (set G) := ⟨subgroup2.carrier⟩

lemma mem_coe' {g : G} : g ∈ (H : set G) ↔ g ∈ H := iff.rfl

instance of_subgroup2 (K : subgroup2 G) : group ↥K :=
{ mul := λ a b, ⟨a.1 * b.1, K.mul_mem' a.2 b.2⟩,
  one := ⟨1, K.one_mem'⟩,
  inv := λ a, ⟨a⁻¹, K.inv_mem' a.2⟩,
  mul_assoc := λ a b c, by { cases a, cases b, cases c, refine subtype.ext _, 
    apply group.mul_assoc },
  one_mul := λ a, by { cases a, apply subtype.ext, apply group.one_mul },
  mul_left_inv := λ a, by { cases a, apply subtype.ext, 
    apply group.mul_left_inv } } 

/-- Returns index of a subgroup2 in a group -/ 
noncomputable def index (H : subgroup2 G) : ℕ := fincard G / fincard H

/-- `index' H J` returns the index of J in H -/ 
noncomputable def index'(H : subgroup2 G) (J : subgroup2 G): ℕ := fincard H / fincard J

-- Defining cosets thats used in some lemmas
def lcoset (g : G) (K : subgroup2 G) := {s : G | ∃ k ∈ K, s = g * k}
def rcoset (g : G) (K : subgroup2 G) := {s : G | ∃ k ∈ K, s = k * g}
notation g ` ⋆ ` :70 H :70 := lcoset g H
notation H ` ⋆ ` :70 g :70 := rcoset g H

attribute [reducible] lcoset rcoset

@[simp] lemma coe_mul (a b : G) (ha : a ∈ H) (hb : b ∈ H) :
  ((⟨a, ha⟩ * ⟨b, hb⟩ : H) : G) = a * b := rfl

end subgroup2

namespace normal

variables {G : Type} [group G]

instance : has_coe (normal G) (subgroup2 G) := 
  ⟨λ K, K.to_subgroup2⟩

-- This saves me from writting m ∈ (K : subgroup2 G) every time
instance : has_mem G (normal G) := ⟨λ m K, m ∈ K.carrier⟩

instance to_set : has_coe (normal G) (set G) := ⟨λ K, K.carrier⟩

@[simp] lemma mem_to_subgroup2 {K : normal G} (x : G) : 
  x ∈ K.to_subgroup2 ↔ x ∈ K := iff.rfl

@[simp] lemma mem_carrier {K : normal G} (x : G) : 
  x ∈ K.carrier ↔ x ∈ K := iff.rfl

lemma conj_mem  (N : normal G) (n : G) (hn : n ∈ N) (g : G) :
  g * n * g⁻¹ ∈ N := N.conj_mem' n hn g

@[ext] lemma ext (A B : normal G) (h : ∀ g, g ∈ A ↔ g ∈ B) : A = B :=
begin
  cases A with A, cases B with B, cases A with A, cases B with B,
  suffices : A = B,
    simp * at *,
  ext x, exact h x
end

theorem ext' {H K : normal G} (h : H.to_subgroup2 = K.to_subgroup2) : H = K :=
by cases H; cases K; congr'

instance of_normal (N : normal G) : group ↥N := 
  subgroup2.of_subgroup2 (N : subgroup2 G)

def of_subgroup2 (H : subgroup2 G) 
  (hH : ∀ n, n ∈ H → ∀ g : G, g * n * g⁻¹ ∈ H) : normal G := 
{ conj_mem' := hH, .. H }

def of_comm_subgroup2 {G : Type} [comm_group G] (H : subgroup2 G) : 
  normal G := 
{ conj_mem' := λ _ _ _, by simpa [group.mul_comm, group.mul_assoc], .. H}

end normal

/-
An API for subgroup2s

Mathematician-friendly

Let G be a group. The type of subgroup2s of G is `subgroup2 G`. 
In other words, if `H : subgroup2 G` then H is a subgroup2 of G. 
The three basic facts you need to know about H are:

H.one_mem : (1 : G) ∈ H
H.mul_mem {x y : G} : x ∈ H → y ∈ H → x * y ∈ H
H.inv_mem {x : G} : x ∈ H → x⁻¹ ∈ H

-/

variables {G : Type} [group G]

namespace lagrange

variables {H : subgroup2 G}

lemma self_mem_coset (a : G) (H : subgroup2 G): a ∈ a ⋆ H := 
  ⟨1, H.one_mem, (group.mul_one a).symm⟩

/-- Two cosets `a ⋆ H`, `b ⋆ H` are equal if and only if `b⁻¹ * a ∈ H` -/
theorem lcoset_eq {a b : G} :
  a ⋆ H = b ⋆ H ↔ b⁻¹ * a ∈ H := 
begin
  split; intro h,
    { replace h : a ∈ b ⋆ H, rw ←h, exact self_mem_coset a H,
      rcases h with ⟨g, hg₀, hg₁⟩,
      rw hg₁, simp [←group.mul_assoc, hg₀] },
    { ext, split; intro hx,
        { rcases hx with ⟨g, hg₀, hg₁⟩, rw hg₁,
          exact ⟨b⁻¹ * a * g, H.mul_mem h hg₀, by simp [←group.mul_assoc]⟩ },
        { rcases hx with ⟨g, hg₀, hg₁⟩, rw hg₁,
          refine ⟨a⁻¹ * b * g, H.mul_mem _ hg₀, by simp [←group.mul_assoc]⟩,
          convert H.inv_mem h, simp } }
end

-- A corollary of this is a ⋆ H = H iff a ∈ H 

/-- The coset of `H`, `1 ⋆ H` equals `H` -/
theorem lcoset_of_one : 1 ⋆ H = H :=
begin
  ext, split; intro hx,
    { rcases hx with ⟨h, hh₀, hh₁⟩,
      rwa [hh₁, group.one_mul] },
    { exact ⟨x, hx, (group.one_mul x).symm⟩ }
end

/-- A left coset `a ⋆ H` equals `H` if and only if `a ∈ H` -/
theorem lcoset_of_mem {a : G} :
  a ⋆ H = H ↔ a ∈ H := by rw [←lcoset_of_one, lcoset_eq]; simp 

/-- Two left cosets `a ⋆ H` and `b ⋆ H` are equal if they are not disjoint -/
theorem lcoset_digj {a b c : G} (ha : c ∈ a ⋆ H) (hb : c ∈ b ⋆ H) : 
  a ⋆ H = b ⋆ H :=
begin
  rcases ha with ⟨g₀, hg₀, hca⟩,
  rcases hb with ⟨g₁, hg₁, hcb⟩,
  rw lcoset_eq, rw (show a = c * g₀⁻¹, by simp [hca, group.mul_assoc]),
  rw (show b⁻¹ = g₁ * c⁻¹, 
    by rw (show b = c * g₁⁻¹, by simp [hcb, group.mul_assoc]); simp),
  suffices : g₁ * g₀⁻¹ ∈ H, 
    { rw [group.mul_assoc, ←@group.mul_assoc _ _ c⁻¹],
      simp [this] },
  exact H.mul_mem hg₁ (H.inv_mem hg₀)
end

-- Now we would like to prove that all lcosets have the same order

open function

private def aux_map (a : G) (H : subgroup2 G) : H → a ⋆ H := 
  λ h, ⟨a * h, h, h.2, rfl⟩

private lemma aux_map_biject {a : G} : bijective $ aux_map a H := 
begin
  split,
    { intros x y hxy,
      suffices : (x : G) = y, 
        { ext, assumption },
        { simp [aux_map] at hxy, assumption } },
    { rintro ⟨y, y_prop⟩, 
      rcases y_prop with ⟨h, hh₀, hh₁⟩,
      refine ⟨⟨h, hh₀⟩, by simp [aux_map, hh₁]⟩ }
end

/-- There is a bijection between `H` and its left cosets -/
noncomputable theorem lcoset_equiv {a : G} : H ≃ a ⋆ H := 
equiv.of_bijective (aux_map a H) aux_map_biject

-- We are going to use fincard which maps a fintype to its fintype.card 
-- and maps to 0 otherwise

/-- The cardinality of `H` equals its left cosets-/
lemma eq_card_of_lcoset {a : G} : fincard H = fincard (a ⋆ H) := 
  fincard.of_equiv lcoset_equiv

/-- The cardinality of all left cosets are equal -/
theorem card_of_lcoset_eq {a b : G} : 
  fincard (a ⋆ H) = fincard (b ⋆ H) := by iterate 2 { rw ←eq_card_of_lcoset }

-- The rest of the proof will requires quotient

end lagrange

namespace normal

lemma mem_normal {x} {N : normal G} : 
  x ∈ N ↔ ∃ (g : G) (n ∈ N), x = g * n * g⁻¹ :=
begin
  split; intro h, 
    { exact ⟨1, x, h, by simp⟩ },
    { rcases h with ⟨g, n, hn, rfl⟩,
      exact conj_mem _ _ hn _ }
end

lemma mem_normal' {x} {N : normal G} : 
  x ∈ N ↔ ∃ (g : G) (n ∈ N), x = g⁻¹ * n * g :=
begin
  rw mem_normal,
  split; rintro ⟨g, n, hn, rfl⟩;
    { exact ⟨g⁻¹, n, hn, by simp⟩ }
end

-- Any two elements commute regarding the normal subgroup2 membership relation
lemma comm_mem_of_normal {K : normal G} 
  {g k : G} (h : g * k ∈ K) : k * g ∈ K :=
begin
  suffices : k * (g * k) * k⁻¹ ∈ K,
    { simp [group.mul_assoc] at this, assumption },
  refine normal.conj_mem _ _ h _
end

def normal_of_mem_comm {K : subgroup2 G} 
  (h : ∀ g k : G, g * k ∈ K → k * g ∈ K) : normal G :=
{ conj_mem' := 
  begin
    intros n hn g,
    suffices : g * (n * g⁻¹) ∈ K,
      { rwa ←group.mul_assoc at this },
    refine h _ _ _, simpa [group.mul_assoc]
  end, .. K } -- The .. tells Lean that we use K for the unfilled fields

-- If K is a normal subgroup2 of the group G, then the sets of left and right 
-- cosets of K in the G coincide
lemma nomal_coset_eq {K : normal G} : 
  ∀ g : G, g ⋆ (K : subgroup2 G) = (K : subgroup2 G) ⋆ g :=
begin
  -- dsimp, 
  -- Without the dsimp it displays weridly,
  -- dsimp not required if we write out right_coset g K however?
  intros g,
  ext, split; intro hx,
    { rcases hx with ⟨k, hk, rfl⟩,
      refine ⟨_, K.2 k hk g, _⟩,
      simp [group.mul_assoc] },
    { rcases hx with ⟨k, hk, rfl⟩,
      refine ⟨_, K.2 k hk g⁻¹, _⟩,
      simp [←group.mul_assoc] }
end

def normal_of_coset_eq {K : subgroup2 G} 
  (h : ∀ g : G, g ⋆ K = K ⋆ g) : normal G :=
{ conj_mem' := 
  begin
    intros n hn g,
    have : ∃ s ∈ K ⋆ g, s = g * n,
      { refine ⟨g * n, _, rfl⟩,
        rw ←h, exact ⟨n, hn, rfl⟩ },
    rcases this with ⟨s, ⟨l, hl₁, hl₂⟩, hs₂⟩,
    rw [←hs₂, hl₂],
    simpa [group.mul_assoc]
  end, .. K}

-- If K is normal then if x ∈ g K and y ∈ h K then x * y ∈ (g * h) K
lemma prod_in_coset_of_normal {K : normal G} {x y g h : G} 
  (hx : x ∈ g ⋆ K) (hy : y ∈ h ⋆ K) : x * y ∈ (g * h) ⋆ K :=
begin
  rcases hx with ⟨k₀, hx₁, rfl⟩,
  rcases hy with ⟨k₁, hy₁, rfl⟩,
  refine ⟨h⁻¹ * k₀ * h * k₁, _, _⟩,
    { refine K.1.3 _ hy₁, 
      convert K.2 _ hx₁ _, exact (group.inv_inv _).symm },
    { iterate 2 { rw group.mul_assoc },
      rw group.mul_left_cancel_iff g _ _,
      simp [←group.mul_assoc] }
end

def normal_of_prod_in_coset {K : subgroup2 G} 
  (h : ∀ x y g h : G, x ∈ g ⋆ K → y ∈ h ⋆ K → x * y ∈ (g * h) ⋆ K) : normal G :=
{ conj_mem' := 
  begin
    intros n hn g,
    rcases h (g * n) (g⁻¹ * n) g g⁻¹ 
      ⟨n, hn, rfl⟩ ⟨n, hn, rfl⟩ with ⟨m, hm₀, hm₁⟩,
    rw [←group.mul_right_cancel_iff n⁻¹,
        group.mul_assoc, group.mul_assoc, group.mul_assoc] at hm₁,
    suffices : g * n * g⁻¹ = m * n⁻¹, 
      rw this, exact K.mul_mem hm₀ (K.inv_mem hn),
    simp [←group.mul_assoc] at hm₁; assumption
  end, .. K }

end normal

end mygroup

/-
Let G be a group. The type of subgroup2s of G is `subgroup2 G`. 
In other words, if `H : subgroup2 G` then H is a subgroup2 of G. 
The three basic facts you need to know about H are:

H.one_mem : (1 : G) ∈ H
H.mul_mem {x y : G} : x ∈ H → y ∈ H → x * y ∈ H
H.inv_mem {x : G} : x ∈ H → x⁻¹ ∈ H

Subgroup2s of a group form what is known as a *lattice*. 
This is a partially ordered set with a sensible notion of
max and min (and even sup and inf). 

We will prove this here.
-/

open_locale classical

namespace mygroup

open group set

variables {G : Type} [group G]
variables {H K : subgroup2 G}

namespace subgroup2

-- The intersect of two subgroup2s is also a subgroup2
def inf (H K : subgroup2 G) : subgroup2 G :=
{ carrier := H.carrier ∩ K.carrier,
  one_mem' := ⟨H.one_mem, K.one_mem⟩,
  mul_mem' := λ _ _ ⟨hhx, hkx⟩ ⟨hhy, hky⟩, 
  ⟨H.mul_mem hhx hhy, K.mul_mem hkx hky⟩,
  inv_mem' := λ x ⟨hhx, hhy⟩,
  ⟨H.inv_mem hhx, K.inv_mem hhy⟩}

lemma inf_def (H K : subgroup2 G) : (inf H K : set G) = (H : set G) ∩ K := rfl 

/- 
We will consider the closure of a set as the intersect of all subgroup2s
containing the set
-/
instance : has_Inf (subgroup2 G) :=
⟨λ s, {
  carrier := ⋂ t ∈ s, (t : set G),
  one_mem' := mem_bInter $ λ i h, i.one_mem,
  mul_mem' := λ x y hx hy, mem_bInter $ λ i h,
    i.mul_mem (by apply mem_bInter_iff.1 hx i h) 
    (by apply mem_bInter_iff.1 hy i h),
  inv_mem' := λ x hx, mem_bInter $ λ i h,
    i.inv_mem (by apply mem_bInter_iff.1 hx i h) }⟩

variable {ι : Type*}

-- The intersect of a set of subgroup2s is a subgroup2
def infi (H : ι → subgroup2 G) : subgroup2 G := 
{ carrier := ⋂ i, H i,
  one_mem' := mem_Inter.mpr $ λ i, (H i).one_mem,
  mul_mem' := λ _ _ hx hy, mem_Inter.mpr $ λ i, 
  by {rw mem_Inter at *, from mul_mem (H i) (hx i) (hy i)},
  inv_mem' := λ x hx, mem_Inter.mpr $ λ i, (H i).inv_mem $ by apply mem_Inter.mp hx }

def closure (S : set G) : subgroup2 G := Inf {H | S ⊆ H}

lemma mem_closure_iff {S : set G} {x : G} : 
  x ∈ closure S ↔ ∀ H : subgroup2 G, S ⊆ H → x ∈ H := mem_bInter_iff

/- We will now prove some lemmas that are helpful in proving subgroup2s 
form a galois_insertion with the coercion to set-/

lemma le_closure (S : set G) : S ≤ closure S :=
λ s hs H ⟨y, hy⟩, by rw ←hy; simp; exact λ hS, hS hs

lemma closure_le (S : set G) (H : subgroup2 G) : closure S ≤ H ↔ S ≤ H :=
begin
  split,
    { intro h, refine subset.trans (le_closure _) h },
    { intros h y,
      unfold closure, unfold Inf, 
      rw mem_bInter_iff, intro hy,
      exact hy H h }
end

lemma closure_le' (S : set G) (H : subgroup2 G) : 
  (closure S : set G) ⊆ H ↔ S ⊆ H := closure_le S H

lemma closure_le'' (S : set G) (H : subgroup2 G) : 
  (∀ x, x ∈ closure S → x ∈ H) ↔ (∀ x, x ∈ S → x ∈ H) := closure_le S H

lemma closure_self {H : subgroup2 G} : closure (H : set G) = H :=
begin
  rw ←subgroup2.ext'_iff, ext,
  split; intro hx,
    { apply subset.trans _ ((closure_le (H : set G) H).2 (subset.refl H)), 
      exact hx, exact subset.refl _ },
    { apply subset.trans (le_closure (H : set G)), 
      intros g hg, assumption, assumption }
end

lemma closure_induction {p : G → Prop} {x} {k : set G} (h : x ∈ closure k)
  (Hk : ∀ x ∈ k, p x) (H1 : p 1)
  (Hmul : ∀ x y, p x → p y → p (x * y))
  (Hinv : ∀ x, p x → p x⁻¹) : p x :=
(@closure_le _ _ _ ⟨p, H1, Hmul, Hinv⟩).2 Hk h

/-
Now, by considering the coercion between subgroup2 G → set G, we cheat a bit
by transfering the partial order on set to the partial order on subgroup2s.

We do this because galois_insertion requires preorders and partial orders
extends preoders.
-/
instance : partial_order (subgroup2 G) := 
{.. partial_order.lift (coe : subgroup2 G → set G) (λ x y, subgroup2.ext')}

/-
Finially we prove that subgroup2s form a galois_insertion with the coercion 
to set.
-/
def gi : @galois_insertion (set G) (subgroup2 G) _ _ closure (λ H, H.carrier) :=
{ choice := λ S _, closure S,
  gc := λ H K,
    begin
      split; intro h,
        { exact subset.trans (le_closure H) h },
        { exact (closure_le _ _).2 h },
    end,
  le_l_u := λ H, le_closure (H : set G),
  choice_eq := λ _ _, rfl }

/-
With that it follows that subgroup2s form a complete lattice!
-/
instance : complete_lattice (subgroup2 G) :=
{.. galois_insertion.lift_complete_lattice gi}

def trivial : subgroup2 G := 
  ⟨{(1 : G)}, set.mem_singleton 1, 
    λ _ _ hx hy, by rw set.mem_singleton_iff at *; simp [hx, hy],
    λ _ hx, by rw set.mem_singleton_iff at *; rw hx; exact group.one_inv⟩

lemma mem_trivial_iff (g : G) : g ∈ (trivial : subgroup2 G) ↔ g = 1 := iff.rfl

lemma mem_trivial_carrier_iff (g : G) : g ∈ (trivial : subgroup2 G).carrier ↔ g = 1 := iff.rfl

lemma bot_eq_trivial : (⊥ : subgroup2 G) = trivial :=
begin
  apply le_antisymm,
    { change closure (∅ : set G) ≤ _,
      rw closure_le, finish },
    { intros x hx,
      change x ∈ {(1 : G)} at hx, 
      rw set.mem_singleton_iff at hx,
      subst hx, unfold_coes, rw mem_coe,
      exact one_mem ⊥ }
end 

lemma bot_eq_singleton_one : ((⊥ : subgroup2 G) : set G) = {1} :=
by rw bot_eq_trivial; refl

lemma mem_bot_iff {x : G} : x ∈ (⊥ : subgroup2 G) ↔ x = 1 :=
begin 
  split; intro h,
    rw [← mem_singleton_iff, ← bot_eq_singleton_one], exact h,
    rw [bot_eq_trivial], exact h
end

lemma fincard_bot : fincard (⊥ : subgroup2 G) = 1 :=
by rw [← @fincard.card_singleton_eq_one _ (1 : G), ← bot_eq_singleton_one]; refl

lemma eq_top_iff' (H : subgroup2 G) : H = ⊤ ↔ ∀ g, g ∈ H :=
begin
  split,
  { rintro rfl,
    intro g,
    show g ∈ ((⊤ : subgroup2 G) : set G),
    rw ←singleton_subset_iff,
    show ({g} : set G) ≤ _,
    rw ←closure_le, simp },
  { intro h,
    rw eq_top_iff,
    intros g hg,
    apply h  }
end

-- scary example!
-- SL₂(ℝ) acts on the upper half plane {z : ℂ | Im(z) > 0}
-- (a b; c d) sends z to (az+b)/(cz+d)
-- check this is an action
-- so SL₂(ℤ) acts on the upper half plane
-- and H, the stabilizer of i ,is cyclic order 4
-- generated by (0 -1; 1 0)
-- and K, the stabilizer of e^{2 pi i/6}, is cyclic order 6
-- generated by something like (1 1; -1 0) maybe
-- Turns out that the smallest subgroup2 of SL₂(ℤ)
-- containing H and K is all of SL₂(ℤ)!
-- In particular if H and K are finite, but neither of
-- them are normal, then H ⊔ K can be huge

example (H K : subgroup2 G) : subgroup2 G := H ⊔ K

-- theorem: if K is normal in G then H ⊔ K is just 
-- literally {hk : h ∈ H, k ∈ K}

variables {H K}

open normal

/-- The supremum of two subgroup2s induced by the Galois insertion is the closure 
  of the union of their carriers -/
lemma sup_def : H ⊔ K = closure (H.carrier ⊔ K.carrier) := rfl

/-- The supremum of two subgroup2s is larger then their union -/
lemma mem_sup_of_mem {x} (hx : x ∈ H ∨ x ∈ K) : x ∈ H ⊔ K :=
begin
  rw sup_def,
  change x ∈ ⋂ (t : subgroup2 G) (H : H.carrier ∪ K.carrier ⊆ t), ↑t,
  refine mem_bInter (λ S hS, hS hx)
end

lemma mem_sup_of_mem_left {x} (hx : x ∈ H) : x ∈ H ⊔ K :=
by { apply mem_sup_of_mem, left, assumption }

lemma mem_sup_of_mem_right {x} (hx : x ∈ K) : x ∈ H ⊔ K :=
by { apply mem_sup_of_mem, right, assumption }

lemma mem_inf {H K : subgroup2 G} {g : G} : 
  g ∈ H ⊓ K ↔ g ∈ H ∧ g ∈ K := 
begin
  change g ∈ closure ((H : set G) ∩ K) ↔ _,
  rw [←inf_def H K, closure_self], refl
end

namespace product

/-- The product of a subgroup2 and a normal subgroup2 forms a subgroup2 -/
def prod (H : subgroup2 G) (K : normal G) : subgroup2 G := 
{ carrier := { g | ∃ h ∈ H, ∃ k ∈ K, g = h * k },
  one_mem' := ⟨1, one_mem H, 1, one_mem K, (group.one_mul _).symm⟩,
  mul_mem' := λ x y ⟨h₀, hh₀, k₀, hk₀, hx⟩ ⟨h₁, hh₁, k₁, hk₁, hy⟩,
    begin
      rw [hx, hy],
      refine ⟨h₀ * h₁, mul_mem H hh₀ hh₁, h₁⁻¹ * k₀ * h₁ * k₁, _, _⟩,
        { refine mul_mem K (mem_normal'.2 ⟨h₁, k₀, hk₀, rfl⟩) hk₁ },
        { simp [group.mul_assoc] }
    end,
  inv_mem' := λ x ⟨h, hh, k, hk, hx⟩,
    begin
      rw [hx, group.inv_mul],
      rw (show k⁻¹ * h⁻¹ = h⁻¹ * (h * k⁻¹ * h⁻¹), by simp [group.mul_assoc]),
      refine ⟨h⁻¹, inv_mem H hh, h * k⁻¹ * h⁻¹, 
        mem_normal.2 ⟨h, k⁻¹, inv_mem K hk, rfl⟩, by simp [group.mul_assoc]⟩      
    end } 

infix ` ⨯ `:70 := prod

lemma mem_product {H : subgroup2 G} {K : normal G} {x} : 
  x ∈ H ⨯ K ↔ ∃ (h ∈ H) (k ∈ K), x = h * k := iff.rfl

theorem product_eq_sup (H : subgroup2 G) (K : normal G) : H ⨯ K = H ⊔ K :=
begin
  ext, split,
    { intro hx, rcases mem_product.1 hx with ⟨h, hh, k, hk, rfl⟩,
      exact mul_mem _ (mem_sup_of_mem_left hh) (mem_sup_of_mem_right hk) },
    { revert x, 
      simp_rw [sup_def, closure_le'', mem_product],
      intros x hx, cases hx, 
        exact ⟨x, hx, 1, one_mem K, (group.mul_one x).symm⟩,
        exact ⟨1, one_mem H, x, hx, (group.one_mul x).symm⟩ }
end 

end product

-- We make a inductive type `subgroup2_ge G H` which is the the type whose terms 
-- are subgroup2s of `G` greater than `H : subgroup2 G` (this makes sense since we 
-- created a lattice structure on subgroup2s). 

/-- `subgroup2_ge G H` is the inductive type of subgroup2s of `G` thats greater 
  than `H`-/
inductive subgroup2_ge (G : Type) [group G] (K : subgroup2 G) 
| mk (H : subgroup2 G) : (K ≤ H) → subgroup2_ge

namespace ge

open subgroup2_ge

-- We will show that the set of subgroup2s greater than some subgroup2 form a 
-- complete lattice. To do this we will use the fact that the subgroup2s forms 
-- a complete lattice and we will create a Galois insertion from subgroup2s 
-- inducing a complete lattice

@[simp] lemma subgroup2_ge_eq (A B : subgroup2 G) {hA : H ≤ A} {hB : H ≤ B} : 
  subgroup2_ge.mk A hA = subgroup2_ge.mk B hB ↔ A = B := ⟨subgroup2_ge.mk.inj, by cc⟩

instance : has_coe (subgroup2_ge G H) (set G) := ⟨λ ⟨K, _⟩, (K : set G)⟩

@[simp] lemma ext' {A B : subgroup2_ge G H} : 
  A = B ↔ (A : set G) = B :=
begin
  cases A, cases B,
  rw subgroup2_ge_eq,
  exact ⟨by cc, λ h, ext' h⟩,
end

instance : has_mem G (subgroup2_ge G H) := ⟨λ g K, g ∈ (K : set G)⟩

@[ext] theorem ext {A B : subgroup2_ge G H}
  (h : ∀ x, x ∈ A ↔ x ∈ B) : A = B := ext'.2 $ set.ext h

instance has_coe_to_subgroup2 : has_coe (subgroup2_ge G H) (subgroup2 G) := 
  ⟨λ ⟨K, _⟩, K⟩

@[simp] lemma subgroup2_ge_eq' (A B : subgroup2_ge G H) : 
  A = B ↔ (A : subgroup2 G) = B := by { cases A, cases B, exact subgroup2_ge_eq _ _ }

-- We borrow the partital order structure from subgroup2s
instance : partial_order (subgroup2_ge G H) := 
{ .. partial_order.lift (coe : subgroup2_ge G H → subgroup2 G) $ λ x y hxy, by simp [hxy] }

instance : has_bot (subgroup2_ge G H) := ⟨⟨H, le_refl _⟩⟩

instance : has_Inf (subgroup2_ge G H) := 
⟨ λ s, subgroup2_ge.mk (Inf { A | ∃ t ∈ s, (t : subgroup2 G) = A }) $ λ h hh,
  begin
    suffices : ∀ (i : subgroup2 G) (x : subgroup2_ge G H), x ∈ s → ↑x = i → h ∈ ↑i,
      simpa [Inf],
    rintros _ ⟨t, ht⟩ _ rfl,
    exact ht hh
  end ⟩

lemma le_Inf (s : set (subgroup2_ge G H)) : ∀ t ∈ s, Inf s ≤ t :=
begin
  rintros ⟨t, ht⟩ hst a ha,
  change a ∈ ⋂ t _, ↑t at ha,
  rw mem_bInter_iff at ha,
  exact ha t ⟨⟨t, ht⟩, hst, rfl⟩,
end  

def closure (A : subgroup2 G) : subgroup2_ge G H := Inf { B | A ≤ B }

lemma closure_le (A : subgroup2 G) (B : subgroup2_ge G H) : 
  closure A ≤ B ↔ A ≤ B :=
begin
  split,
    { intro h, cases B with B hB,
      exact le_trans 
        (show A ≤ _, by exact (λ _ ha, mem_bInter (λ _ ⟨⟨_, _⟩, ht', rfl⟩, ht' ha))) h },
    { intro h, exact le_Inf _ _ h }
end

lemma le_closure (A : subgroup2_ge G H) : A = closure A :=
begin
  cases A with A hA,
  ext, split,
  { intro hx,
    refine mem_bInter (λ B hB, _),
    rcases hB with ⟨t, ht, rfl⟩,
    exact ht hx },
  { suffices : closure A ≤ ⟨A, hA⟩,
      intro hx, exact this hx,
    apply le_Inf,
    rw mem_set_of_eq,
    exact le_of_eq rfl }  
end

def gi : @galois_insertion (subgroup2 G) (subgroup2_ge G H) _ _ closure (coe) := 
{ choice := λ x _, closure x,
  gc := λ A B, closure_le _ _,
  le_l_u := λ x, le_of_eq $ le_closure x,
  choice_eq := λ _ _, rfl }

instance : complete_lattice (subgroup2_ge G H) := 
{.. @galois_insertion.lift_complete_lattice (subgroup2 G) (subgroup2_ge G H) _ _ _ _ gi }

-- We can see easily that subgroup2 G is the same as subgroup2_ge G ⊥

def subgroup2_ge_bot_equiv : subgroup2 G ≃ subgroup2_ge G ⊥ := 
{ to_fun := λ H, ⟨H, bot_le⟩,
  inv_fun := λ ⟨H, _⟩, H,
  left_inv := λ _, rfl,
  right_inv := λ ⟨_, _⟩, rfl }

def subgroup2_ge_bot_order_iso : 
  let A := subgroup2 G in let B := subgroup2_ge G ⊥ in 
  ((≤) : A → A → Prop) ≃o ((≤) : B → B → Prop) :=
{ ord' := λ _ _, iff.rfl, 
  .. subgroup2_ge_bot_equiv }

end ge

end subgroup2

namespace lattice

/-- Given an equivalence `e` on preorders `A` and `B`, and a Galois connection 
  using `e`, there is an induced `order_iso` between `A` and `B`  -/
def order_iso_of_equiv_gi {A B : Type} [preorder A] [preorder B]
   (e : A ≃ B) (g : galois_connection e.to_fun e.inv_fun) : 
  ((≤) : A → A → Prop) ≃o ((≤) : B → B → Prop) := 
{ ord' := λ a b, let h := g a (e.to_fun b) in
    by { rw e.left_inv at h, rw ←h, refl}, .. e }

open order_iso

/-- Given a `lattice`, `A`, there is an induced `lattice` on the `partial_order`, 
  `B` given that they are order isomorphic -/
def lattice_of_order_iso {A B : Type} [lattice A] [partial_order B] 
  (e : ((≤) : A → A → Prop) ≃o ((≤) : B → B → Prop)) : lattice B := 
{ .. galois_insertion.lift_lattice e.to_galois_insertion }

/-- Given a `lattice`, `B` and an `order_iso` to the `distrib_lattice`, `A`, 
  there is an induced `distrib_lattice` on `B` -/
def distrib_lattice_of_order_iso {A B : Type} [hA : distrib_lattice A] [lattice B]
  (e : ((≤) : B → B → Prop) ≃o ((≤) : A → A → Prop)) : distrib_lattice B := 
{ le_sup_inf := 
    begin
      intros x y z, rw e.ord',
      change e ((x ⊔ y) ⊓ (x ⊔ z)) ≤ e (x ⊔ y ⊓ z),
      rw [map_inf, map_sup, map_sup, map_sup, map_inf],
      apply hA.le_sup_inf
    end
  .. show lattice B, by apply_instance }

def distrib_lattice_of_order_iso' {A B : Type} [distrib_lattice A] [lattice B]
  (e : ((≤) : A → A → Prop) ≃o ((≤) : B → B → Prop)) : distrib_lattice B := 
distrib_lattice_of_order_iso $ order_iso.symm e

/-- Given a `distrib_lattice`, `A`, there is an induced `distrib_lattice` on the 
  `partial_order`, `B` given that they are order isomorphic -/
def distrib_lattice_of_order_iso'' {A B : Type} [distrib_lattice A] [partial_order B]
  (e : ((≤) : A → A → Prop) ≃o ((≤) : B → B → Prop)) : distrib_lattice B :=
@distrib_lattice_of_order_iso' _ _ _ 
  (@lattice_of_order_iso _ _ (distrib_lattice.to_lattice A) _ e) e

end lattice 

namespace normal 

instance : partial_order (normal G) := 
{.. partial_order.lift (normal.to_subgroup2) (λ x y, normal.ext')}

instance : has_Inf (normal G) :=
⟨λ s, {
  carrier := ⋂ t ∈ s, (t : set G),
  one_mem' := mem_bInter $ λ i h, i.one_mem',
  mul_mem' := λ x y hx hy, mem_bInter $ λ i h,
    i.mul_mem' (by apply mem_bInter_iff.1 hx i h) 
    (by apply mem_bInter_iff.1 hy i h),
  inv_mem' := λ x hx, mem_bInter $ λ i h,
    i.inv_mem' (by apply mem_bInter_iff.1 hx i h),
  conj_mem' := 
    begin
      simp_rw mem_bInter_iff,
      intros n hn g N hNs,
      exact N.conj_mem _ (hn N hNs) _, 
    end }⟩

@[simp] lemma mem_Inf (x : G) (s : set (normal G)) : 
  x ∈ Inf s ↔ x ∈ ⋂ t ∈ s, (t : set G) := iff.rfl

def closure (S : set G) : normal G := Inf {H | S ⊆ H}

lemma mem_closure_iff {S : set G} {x : G} : 
  x ∈ closure S ↔ ∀ H : normal G, S ⊆ H → x ∈ H := mem_bInter_iff

lemma le_closure (S : set G) : S ≤ closure S :=
λ s hs H ⟨y, hy⟩, by rw ←hy; simp; exact λ hS, hS hs

lemma closure_le (S : set G) (H : normal G) : closure S ≤ H ↔ S ≤ H :=
begin
  split,
    { intro h, refine subset.trans (le_closure _) h },
    { intros h y hy,
      change y ∈ (_ : normal G) at hy,
      unfold closure at hy,
      rw [mem_Inf, mem_bInter_iff] at hy,
      exact hy H h }
end

lemma closure_le' (S : set G) (H : normal G) : 
  (closure S : set G) ⊆ H ↔ S ⊆ H := closure_le S H

lemma closure_le'' (S : set G) (H : normal G) : 
  (∀ x, x ∈ closure S → x ∈ H) ↔ (∀ x, x ∈ S → x ∈ H) := closure_le S H

lemma closure_self {H : normal G} : closure (H : set G) = H :=
begin
  ext, split; intro hx,
    { apply subset.trans _ ((closure_le (H : set G) H).2 (subset.refl H)), 
      exact hx, exact subset.refl _ },
    { rw ← mem_carrier,
      apply subset.trans (le_closure (H : set G)), 
      intros g hg, assumption, assumption }
end

-- lemma closure_induction {p : G → Prop} {x} {k : set G} (h : x ∈ closure k)
--   (Hk : ∀ x ∈ k, p x) (H1 : p 1)
--   (Hmul : ∀ x y, p x → p y → p (x * y))
--   (Hinv : ∀ x, p x → p x⁻¹) : p x :=
-- (@closure_le _ _ _ ⟨p, H1, Hmul, Hinv⟩).2 Hk h

def gi : @galois_insertion (set G) (normal G) _ _ closure (λ H, H.carrier) :=
{ choice := λ S _, closure S,
  gc := λ H K,
    begin
      split; intro h,
        { exact subset.trans (le_closure H) h },
        { exact (closure_le _ _).2 h },
    end,
  le_l_u := λ H, le_closure (H : set G),
  choice_eq := λ _ _, rfl }

instance : complete_lattice (normal G) :=
{.. galois_insertion.lift_complete_lattice gi}

end normal

end mygroup