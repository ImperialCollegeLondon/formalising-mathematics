import week_2.kb_solutions.Part_A_groups_solutions

/-!

## Subgroups

Lean has subgroups already, so we'll call ours subgroup2.

-/

namespace xena

/-- A subgroup of a group G is a subset containing 1
and closed under multiplication and inverse. -/
structure subgroup (G : Type) [group G] :=
(carrier : set G)
(one_mem' : (1 : G) ∈ carrier)
(mul_mem' {x y} : x ∈ carrier → y ∈ carrier → x * y ∈ carrier)
(inv_mem' {x} : x ∈ carrier → x⁻¹ ∈ carrier)

/-

At this point, here's what we have.

A term `H` of type `subgroup2 G`, written `H : subgroup2 G`, is a
quadruple `H.carrier` (a subset of `G`), `H.one_mem'` (a proof
that `1 ∈ H.carrier`), `H.mul_mem'` (a proof that if `x` and `y` are in
`H.carrier` then so is `x*y`) and `H.inv_mem'` (saying `H` is closed under
inverses). Note here that the _type_ of `x` and `y` is still `G`, 
and `x ∈ carrier` is a Proposition. Note also that `x : carrier` doesn't
make sense (`carrier` is a term, not a type, rather counterintuitively).

This kind of stinks. I don't want to write `H.carrier` everywhere.
I want to write `H`. Let's start by sorting this out.

-/

namespace subgroup

open xena.group

-- let G be a group and let H and K be subgroups
variables {G : Type} [group G] (H K : subgroup G)

-- If `x : G` and `H : subgroup2 G` then let's define `x ∈ H` to mean
-- `x ∈ H.carrier`
instance : has_mem G (subgroup G) := ⟨λ m H, m ∈ H.carrier⟩

-- Now let's define theorems without the `'`s in, which use this
-- more normal notation

/-- A subgroup2 contains the group's 1. -/
theorem one_mem : (1 : G) ∈ H :=
begin
  apply H.one_mem',
end

/-- A subgroup2 is closed under multiplication. -/
theorem mul_mem {x y : G} : x ∈ H → y ∈ H → x * y ∈ H :=
begin
  apply H.mul_mem',
end

/-- A subgroup2 is closed under inverse -/
theorem inv_mem {x : G} : x ∈ H → x⁻¹ ∈ H :=
begin
  apply H.inv_mem',
end

-- let's tell the simplifier that we would rather talk about `g ∈ H`
-- than `g ∈ H.carrier`

@[simp] lemma mem_coe {g : G} : g ∈ H.carrier ↔ g ∈ H := iff.rfl

/-

So here are the three theorems which you need to remember about subgroups.
Say `H : subgroup G`. Then:

`H.one_mem : (1 : G) ∈ H`
`H.mul_mem {x y : G} : x ∈ H → y ∈ H → x * y ∈ H`
`H.inv_mem {x : G} : x ∈ H → x⁻¹ ∈ H`

-/

-- now we can prove basic theorems about subgroups using this sensible notation
-- Remember that `xena.group.inv_inv x` is the statement that `x⁻¹⁻¹ = x`

@[simp] theorem inv_mem_iff {x :G} : x⁻¹ ∈ H ↔ x ∈ H := 
begin
  split,
  { intro h,
    rw ← xena.group.inv_inv x,
    apply H.inv_mem,
    assumption },
  { apply H.inv_mem },
end

/-
Subgroups are extensional objects (like most things in mathematics):
two subgroups are equal if they have the same underlying subset,
and also if they have the same underlying elements.
Let's prove variants of this triviality now.
-/

/-- Two subgroups are equal if the underlying subsets are equal. -/
theorem ext' {H K : subgroup G} (h : H.carrier = K.carrier) : H = K :=
begin
  -- first take H and K apart
  cases H,
  cases K,
  -- and now it must be obvious
  simp * at *,
end

-- here's a variant

/-- Two subgroups are equal if and only if the underlying subsets are equal. -/
protected theorem ext'_iff {H K : subgroup G} :
  H.carrier = K.carrier ↔ H = K :=
begin
  split,
  { exact ext' },
  { intro h,
    rw h, }
end

-- to do this next one, first apply the `ext'` theorem we just proved,
-- and then use the `ext` tactic (which works on sets)

/-- Two subgroups are equal if they have the same elements. -/
@[ext] theorem ext {H K : subgroup G} (h : ∀ x, x ∈ H ↔ x ∈ K) : H = K :=
begin
  -- first apply ext' to reduce to checking the carriers are equal
  apply ext',
  -- now use the ext tactic to reduce to checking the elements of
  -- the carriers are equal
  ext,
  -- and now this is by definition what h says
  apply h,
end

/-
We tagged that theorem with `ext`, so now the `ext` tactic works on subgroups
too: if you ever have a goal of proving that two subgroups are equal, you can
use the `ext` tactic to reduce to showing that they have the same elements.
-/

-- Coersion to group
-- Coercion from subgroup2 to underlying type

instance : has_coe (subgroup G) (set G) := ⟨subgroup.carrier⟩

--lemma mem_coe' {g : G} : g ∈ (H : set G) ↔ g ∈ H := iff.rfl



/-
Subgroups of a group form what is known as a *lattice*. 
This is a partially ordered set with a sensible notion of
max and min. Subgroups even have a good notion of an infinite
sup and inf.

We will prove this here.

We start by defining a relation ≤ on the type of subgroups of a group.
We say H ≤ K iff H.carrier ⊆ K.carrier .
-/
instance : has_le (subgroup G) := ⟨λ S T, S.carrier ⊆ T.carrier⟩


open set

-- The intersect of two subgroup2s is also a subgroup2
def inf (H K : subgroup G) : subgroup G :=
{ carrier := H.carrier ∩ K.carrier,
  one_mem' := ⟨H.one_mem, K.one_mem⟩,
  mul_mem' := λ _ _ ⟨hhx, hkx⟩ ⟨hhy, hky⟩, 
  ⟨H.mul_mem hhx hhy, K.mul_mem hkx hky⟩,
  inv_mem' := λ x ⟨hhx, hhy⟩,
  ⟨H.inv_mem hhx, K.inv_mem hhy⟩}

lemma inf_def (H K : subgroup G) : (inf H K : set G) = (H : set G) ∩ K := rfl 

/- 
We will consider the closure of a set as the intersect of all subgroup2s
containing the set
-/
instance : has_Inf (subgroup G) :=
⟨λ s, {
  carrier := ⋂ t ∈ s, (t : set G),
  one_mem' := mem_bInter $ λ i h, i.one_mem,
  mul_mem' := λ x y hx hy, mem_bInter $ λ i h,
    i.mul_mem (by apply mem_bInter_iff.1 hx i h) 
    (by apply mem_bInter_iff.1 hy i h),
  inv_mem' := λ x hx, mem_bInter $ λ i h,
    i.inv_mem (by apply mem_bInter_iff.1 hx i h) }⟩

def closure (S : set G) : subgroup G := Inf {H | S ⊆ H}

lemma mem_closure_iff {S : set G} {x : G} : 
  x ∈ closure S ↔ ∀ H : subgroup G, S ⊆ H → x ∈ H := mem_bInter_iff

/- We will now prove some lemmas that are helpful in proving subgroups 
form a galois_insertion with the coercion to set
-/

lemma le_closure (S : set G) : S ≤ closure S :=
λ s hs H ⟨y, hy⟩, by rw ←hy; simp; exact λ hS, hS hs

lemma closure_le (S : set G) (H : subgroup G) : closure S ≤ H ↔ S ⊆ H :=
begin
  split,
    { intro h, refine subset.trans (le_closure _) h },
    { intros h y,
      unfold closure, unfold Inf, 
      rw mem_bInter_iff, intro hy,
      exact hy H h }
end

lemma closure_le' (S : set G) (H : subgroup G) : 
  (closure S : set G) ⊆ H ↔ S ⊆ H := closure_le S H

lemma closure_le'' (S : set G) (H : subgroup G) : 
  (∀ x, x ∈ closure S → x ∈ H) ↔ (∀ x, x ∈ S → x ∈ H) := closure_le S H

lemma closure_self {H : subgroup G} : closure (H : set G) = H :=
begin
  rw ←subgroup.ext'_iff, ext,
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
instance : partial_order (subgroup G) := 
{.. partial_order.lift (coe : subgroup G → set G) (λ x y, subgroup.ext')}

/-
Finially we prove that subgroups form a galois_insertion with the coercion 
to set.
-/
def gi : galois_insertion (closure : set G → subgroup G) (coe : subgroup G → set G) :=
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
instance : complete_lattice (subgroup G) :=
{.. galois_insertion.lift_complete_lattice gi}

end subgroup

end xena


/-

Could do bot and top, but would have to practice stuff like mem_singleton

-/
