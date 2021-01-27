import week_2.Part_A_groups

/-!

## Subgroups

Lean has subgroups already, so we'll call ours subgroup2.


-/

/-- A subgroup of a group G is a subset containing 1
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

open group2

-- let G be a group and let H and K be subgroups
variables {G : Type} [group2 G] (H K : subgroup2 G)

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

--/-- A subgroup2 is closed under integer powers -/
-- theorem pow_mem {x : G} {n : ℤ} : x ∈ H → x ^ n ∈ H :=
-- begin
--   sorry -- do I do this?
-- end

@[simp] theorem inv_mem_iff {x :G} : x⁻¹ ∈ H ↔ x ∈ H := 
  ⟨ λ hx, inv_inv x ▸ H.inv_mem hx, H.inv_mem ⟩ 

-- Coersion to group
-- Coercion from subgroup2 to underlying type

instance : has_coe (subgroup2 G) (set G) := ⟨subgroup2.carrier⟩

lemma mem_coe' {g : G} : g ∈ (H : set G) ↔ g ∈ H := iff.rfl




end subgroup2


/-
An API for subgroups

Mathematician-friendly

Let G be a `group2`. The type of subgroups of G is `subgroup2 G`. 
In other words, if `H : subgroup2 G` then H is a subgroup of G. 
The three basic facts you need to know about H are:

H.one_mem : (1 : G) ∈ H
H.mul_mem {x y : G} : x ∈ H → y ∈ H → x * y ∈ H
H.inv_mem {x : G} : x ∈ H → x⁻¹ ∈ H

-/

variables {G : Type} [group2 G]



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

open group2 set

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

/- We will now prove some lemmas that are helpful in proving subgroups 
form a galois_insertion with the coercion to set
-/

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
by transfering the partial order on set to the partial order on subgroups.

We do this because galois_insertion requires preorders and partial orders
extends preoders.
-/
instance : partial_order (subgroup2 G) := 
{.. partial_order.lift (coe : subgroup2 G → set G) (λ x y, subgroup2.ext')}

/-
Finially we prove that subgroups form a galois_insertion with the coercion 
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
    λ _ hx, by rw set.mem_singleton_iff at *; rw hx; exact group2.one_inv⟩

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

end subgroup2
