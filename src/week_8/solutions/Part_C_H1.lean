import week_8.solutions.Part_B_H0
import group_theory.quotient_group

/-

# A crash course in H¹(G,M)

We stick to the conventions that `G` is a group (or even
a monoid, we never use inversion) and that `M` is a `G`-module,
that is, an additive abelian group with a `G`-action.

A key concept here is that of a cocycle, or a twisted homomorphism.
These things were later renamed 1-cocycles when people realised that higher
cocycles existed; today whenever I say "cocycle" I mean 1-cocycle).
A cocycle is a function `f : G → M` satisfying the axiom
`∀ (g h : G), f (g * h) = f g + g • f h`. These things
naturally form an abelian group under pointwise addition
and negation, by which I mean "operate on the target":
`(f₁ + f₂) g = f₁ g + f₂ g`.

Let `Z1 G M` denote the abelian group of cocycles. 
There is a subgroup `B1 G M` of coboundaries, consisting
of the functions `f` for which there exists `m : M`
such that `f g = g • m - m` (note that it is at this point where we
crucially use the fact that `M` is an abelian group and not just an abelian
monoid). One easily checks that all coboundaries are cocycles, and that
coboundaries are a subgroup (you will be doing this below). The
quotient group `H1 G M`, written `H¹(G,M)` by mathematicians, is the main
definition in this file. The first two theorems we shall prove about it here
are that it is functorial (i.e. a map `φ : M →+[G] N` gives
rise to a map `φ.H1_hom : H1 G M →+ H1 G N`), and exact in the
middle (i.e. if `0 → A → B → C → 0` is a short exact sequence
of `G`-modules then the sequence `H1 G A →+ H1 G B →+ H1 G C`
is exact).

Further work would be to verify "inf-res", otherwise known
as the beginning of the long exact
sequence of terms of low degree in the Hochschild-Serre
spectral sequence for group cohomology (i.e.
`0 → H¹(G/N, Aᴺ) → H¹(G, A) → H¹(N, A)` ) and of course one
could go on to define n-cocycles and n-coboundaries (please
get in touch if you're interested in doing this -- I have
ideas about how to set it all up) and to
construct the Hochschild-Serre spectral sequence itself.
I have no doubt that these kinds of results could be turned
into a research paper.

Let's start with a definition of `H1 G M`. First we need
to define cocycles and coboundaries. 
-/

section is_cocycle'

variables {G M : Type}
  [monoid G] [add_comm_group M] [distrib_mul_action G M]

--notation `is_cocycle` f := ∀ (g h : domain f), f (g * h) = f g + g • f h
def is_cocycle (f : G → M) : Prop :=
∀ (g h : G), f (g * h) = f g + g • f h


end is_cocycle'

-- 1-cocycles as an additive subgroup of the group `Hom(G,M)`
-- a.k.a. `G → M` of functions from `G` to `M`, with group
-- law induced from `M`.
def Z1_subgroup (G M : Type)
  [monoid G] [add_comm_group M] [distrib_mul_action G M] : add_subgroup (G → M) :=
{ carrier := { f : G → M | ∀ (g h : G), f (g * h) = f g + g • f h },
  zero_mem' := begin
    -- the zero map is a cocycle
    simp,
  end,
  add_mem' := begin
    -- sum of two cocycles is a cocycle.
    -- Note that the `abel` tactic is to additive abelian groups
    -- what the `ring` tactic is to commutative semirings.
    rintros c b hc hb g h,
    simp [hc g h, hb g h],
    abel,
  end,
  neg_mem' := begin
    rintros c hc g h,
    simp [hc g h],
    abel,
  end }

-- Just like `H0 G M`, we promote this term to a type
structure Z1 (G M : Type)
  [monoid G] [add_comm_group M] [distrib_mul_action G M] : Type :=
(to_fun : G → M)
(is_cocycle : ∀ (g h : G), to_fun (g * h) = to_fun g + g • to_fun h)

-- This is a definition so we need to make an API
namespace Z1

-- let G be a group (or a monoid) and let M be a G-module.
variables {G M : Type}
  [monoid G] [add_comm_group M] [distrib_mul_action G M]

-- add a coercion from a cocycle to the function G → M
instance : has_coe_to_fun (Z1 G M) :=
{ F := λ _, G → M,
  coe := to_fun }

@[simp] lemma coe_apply (to_fun : G → M)
  (is_cocycle : ∀ (g h : G), to_fun (g * h) = to_fun g + g • to_fun h) (g : G) :
({ to_fun := to_fun, is_cocycle := is_cocycle } : Z1 G M) g = to_fun g := rfl


-- add a specification for the coercion

lemma spec (a : Z1 G M) : ∀ (g h : G), a (g * h) = a g + g • a h :=
-- this is the last time we'll see `a.is_cocycle`: we'll 
-- use `a.spec` from now on because it applies to `⇑a` and not `a.to_fun`.
a.is_cocycle

-- add an extensionality lemma
@[ext] lemma ext (a b : Z1 G M) (h : ∀ g, a g = b g) : a = b :=
begin
  cases a, cases b, simp, ext g, exact h g,
end

lemma ext_iff (a b : Z1 G M) : a = b ↔ ∀ g, a g = b g :=
⟨by { rintro rfl, exact λ _, rfl }, ext _ _⟩ 

def add (a b : Z1 G M) : Z1 G M :=
{ to_fun := λ g, a g + b g,
  is_cocycle
 := begin
    rintros g h,
    simp [a.spec, b.spec],
    abel,    
  end }

instance : has_add (Z1 G M) := ⟨add⟩

@[simp] lemma coe_add (a b : Z1 G M) (g : G) : (a + b) g = a g + b g := rfl

def zero : Z1 G M := 
{ to_fun := λ g, 0,
  is_cocycle
 := begin
    simp,
  end
}

instance : has_zero (Z1 G M) := ⟨zero⟩

@[simp] lemma coe_zero (g : G) : (0 : Z1 G M) g = 0 := rfl

def neg (a : Z1 G M) : Z1 G M :=
{ to_fun := λ g, -(a g),
  is_cocycle
 := begin
    intros,
    simp [a.spec],
    abel,
  end
}

instance : has_neg (Z1 G M) := ⟨neg⟩

@[simp] lemma coe_neg (a : Z1 G M) (g : G) : (-a) g = -(a g) := rfl

def sub (a b : Z1 G M) : Z1 G M := a + -b

instance : has_sub (Z1 G M) := ⟨sub⟩

@[simp] lemma coe_sub (a b : Z1 G M) (g : G) : (a - b) g = a g - b g :=
(sub_eq_add_neg _ _).symm

-- make the cocycles into a group
instance : add_comm_group (Z1 G M) :=
begin
  refine_struct { 
    add := (+),
    zero := (0 : Z1 G M),
    neg := has_neg.neg,
    sub := has_sub.sub,
    -- ignore this, we have to fill in this proof for technical reasons
    sub_eq_add_neg := λ _ _, rfl };
  -- we now have five goals. Let's use the semicolon trick to work on 
  -- all of them at once. I'll show you what happens to the proof
  -- of associativity, the others are the same mutatis mutandis
  -- (but harder to see)
  -- *TODO* could documentstring commutativity and remark that 
  -- they can see associativity using the cursor.
  -- ⊢ ∀ (a b c : Z1 G M), a + b + c = a + (b + c)
  intros;
  -- ⊢ a + b + c = a + (b + c)
  ext;
  -- ⊢ ⇑(a + b + c) g = ⇑(a + (b + c)) g
  simp;
  -- ⊢ ⇑a g + ⇑b g + ⇑c g = ⇑a g + (⇑b g + ⇑c g)
  abel
  -- general additive abelian group tactic which solves
  -- goals which are (absolute) identities in every abelian group.
  -- Hypotheses are not looked at though. See Chris Hughes' forthcoming
  -- Imperial MSc thesis for a new group theory tactic which is to `abel`
  -- what `nlinarith` is to `ring`.
end

end Z1

namespace distrib_mul_action_hom

-- The Z1 construction is functorial in the module `M`. Let's construct
-- the relevant function, showing that if `φ : M →+[G] N` then
-- composition induces an additive group homomorphism `Z1 G M → Z1 G N`.
-- Just like `H0` we first define the auxiliary bare function, 
-- and then beef it up to an abelian group homomorphism.

variables {G M N : Type} [monoid G] 
  [add_comm_group M] [distrib_mul_action G M]
  [add_comm_group N] [distrib_mul_action G N]

def Z1_hom_underlying_function (φ : M →+[G] N) (f : Z1 G M) : Z1 G N :=
⟨λ g, φ (f g), begin
  -- need to prove that this function obtained by composing the cocycle
  -- f with the G-module homomorphism φ is also a cocycle.
  simp [←φ.map_smul, -map_smul, f.spec]
end⟩

@[norm_cast] 
lemma Z1_hom_underlying_function_coe_comp (φ : M →+[G] N) (f : Z1 G M) (g : G) :
  (Z1_hom_underlying_function φ f g : N) = φ (f g) := rfl

def Z1 (φ : M →+[G] N) : Z1 G M →+ Z1 G N :=
-- to make a term of type `X →+ Y` (a group homomorphism) from a function
-- `f : X → Y` and
-- a proof that it preserves addition we use the following constructor:
add_monoid_hom.mk' 
-- We now throw in the bare function
(Z1_hom_underlying_function φ)
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
  simp [φ.Z1_hom_underlying_function_coe_comp],
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

section cochain_map

variables (G M : Type) [monoid G] [add_comm_group M]
  [distrib_mul_action G M] 

def cochain_map : M →+ Z1 G M :=
{ to_fun := λ m, { to_fun := λ g, g • m - m, is_cocycle := begin
  simp [mul_smul, smul_sub],
end},
  map_zero' := begin
    ext g,
    simp,
  end,
  map_add' := begin
    intros,
    ext g,
    simp,
    abel,
  end }

@[simp] lemma cochain_map_apply (m : M) (g : G) :
  cochain_map G M m g = g • m - m := rfl

end cochain_map

-- question : do we have cokernels? If A B are abelian groups and
-- `f : A → B` is a group hom, how do I make the type coker f`

-- Lean has inbuilt quotients of additive abelian groups by subgroups
@[derive add_comm_group]
def H1 (G M : Type) [monoid G] [add_comm_group M]
  [distrib_mul_action G M] : Type :=
quotient_add_group.quotient ((cochain_map G M).range)

section quotient_stuff

variables {G M : Type} [monoid G] [add_comm_group M]
  [distrib_mul_action G M]

def Z1.quotient : Z1 G M →+ H1 G M :=
quotient_add_group.mk' _

lemma H1.ker_quotient : (Z1.quotient).ker = (cochain_map G M).range :=
quotient_add_group.ker_mk _

end quotient_stuff

namespace H1

variables {G M : Type} [monoid G] [add_comm_group M]
  [distrib_mul_action G M] 

@[elab_as_eliminator]
def induction_on {p : H1 G M → Prop} 
  (IH : ∀ z : Z1 G M, p (z.quotient)) (h : H1 G M) : p h :=
quot.induction_on h IH

end H1

/-
We have just defined `H1 G M` as a quotient group, and told Lean
to figure out (or "derive") the obvious abelian group structure
on it, which it did.

What we need to do now is to show that if `φ : M →+[G] N` is a `G`-module
hom then `φ` induces a map `H1 G M → H1 G N`. To prove this we will
need to figure out how to define maps from and to quotient group structures.
Just like last week, this is simply a matter of learning the API for the
definition `quotient_add_group.quotient`.

TODO -- make the definition
-/

namespace distrib_mul_action_hom

local notation `Z1'` := _root_.Z1

open add_subgroup

variables {G M N : Type}
  [monoid G] [add_comm_group M] [add_comm_group N]
  [distrib_mul_action G M] [distrib_mul_action G N]

def H1 (φ : M →+[G] N) : H1 G M →+ H1 G N :=
-- We use `quotient_add_group.map` to define this map
-- by saying that it is a descent of the map `φ.Z1_hom`
quotient_add_group.map ((cochain_map G M).range) ((cochain_map G N).range)
  φ.Z1
-- We now have to supply the proof that the map on cocycles induces
-- a map on cohomology, i.e. that it sends coboundaries to coboundaries
begin
  rintro ⟨c, hc⟩ ⟨m, hm⟩,
  use φ m,
  ext g,
  simp [← hm],
end

def H1_spec (φ : M →+[G] N) (f : Z1' G M) : 
  φ.H1 (f.quotient) = (φ.Z1 f).quotient := rfl

-- why isn't this there??
-- ask in Zulip
instance : add_comm_group (M →+[G] N) :=
{ add := λ a b, ({ to_fun := λ m, a m + b m,
    map_smul' := by simp,
    map_zero' := by simp,
    map_add' := by { intros, simp [map_add], abel} }),
  add_assoc := sorry,--by {intros, ext m, simp only [add_comm_group.add], dsimp, },--abel}, -- missing coe_add simp lemma?
  zero := { to_fun := λ m, 0,
    map_smul' := by simp,
    map_zero' := by simp,
    map_add' := by simp },
  zero_add := sorry,
  add_zero := sorry,
  neg := λ a, { to_fun := λ m, -(a m),
    map_smul' := by simp,
    map_zero' := by simp,
    map_add' := by { intros, simp [map_neg], abel} },
  add_left_neg := sorry,
  add_comm := sorry }

-- API for instance
@[simp] lemma zero_val (m : M) : (0 : M →+[G] N) m = 0 := rfl
#check @zero_val
#print zero_val

end distrib_mul_action_hom

section exactness

variables {G M N P : Type}
  [monoid G]
  [add_comm_group M] [distrib_mul_action G M] 
  [add_comm_group N] [distrib_mul_action G N]
  [add_comm_group P] [distrib_mul_action G P]
(φ : M →+[G] N) (z : Z1 G M)

example (α β : Type) [setoid α] [setoid β]
  (f : α → β) (h : (has_equiv.equiv ⇒ has_equiv.equiv) f f) (a : α) : 
  quotient.map f h (⟦a⟧) = ⟦f a⟧ := quotient.map_mk f h a

lemma Z1.H1_map_mk (φ : M →+[G] N) : φ.H1 (z.quotient) = 
  (φ.Z1 z).quotient :=
rfl

open function

open add_monoid_hom

-- right now will work around with sets

theorem H1_hom_middle_exact (φ : M →+[G] N)
  (ψ : N →+[G] P) (hse : is_short_exact φ ψ) : 
  φ.H1.range = ψ.H1.ker :=
begin
  -- need to prove a range is a kernel,
  ext k,
  -- let k be a cohomology class, an element of H^1(G,N).
  -- we're supposed to be proving that we're in a range
  -- if and only if we're in a kernel
  -- I can't see how to do it directly with rewrites
  -- so I'm going to split
  split,
  { rintro ⟨x, rfl⟩,
    refine x.induction_on _, clear x,
    intros z,
    -- should have some map commutes lemma
    rw Z1.H1_map_mk,
    rw mem_ker,
    rw Z1.H1_map_mk,
    convert Z1.quotient.map_zero,
    rw φ.map_comp,
    have hψφ : ψ.comp φ = (0 : M →+[G] P),
    { ext m,
      rw hse.is_exact_def' at he, -- no he any more, use hse
      rw set.ext_iff at he,
      simp * at * },
    rw ← mem_ker,
    rw hψφ,
    
    rw is_exact_def' at he,
    rw mem_ker,
    refl },
  { -- this is the trickier way. What is the maths proof?
/-

I use set theory language
Say k ∈ H¹(N) and H¹(ψ)(k) = 0. Need to find c in H¹(M) such that
H¹(φ)(c) = k. Lift k to a cocycle x in Z¹(N). Need to pull back
x along φ. Can modify x by a coboundary to get λ g, x g + g n - n
So let's see if we can turn "H¹(ψ)(k)=0" into the existence
of a magic `n0` such that ∀ g, ψ (x g + g n0 - n0) = 0 




-/  
    rw mem_ker,
    -- why isn't this better
    refine H1.induction_on _ k, clear k,
    intros z hz,
    rw Z1.H1_map_mk at hz,
    rw ← mem_ker at hz,
    -- rw Z1.ker_quotient at hz,
    -- cases hz with y hy,
    -- rw Z1.ext_iff at hy,
    -- simp_rw cochain_map_apply at hy,
    -- simp_rw ψ.Z1_spec at hy, 
    -- rw is_exact_def at he,
    -- cases hψ y with x hx,
    -- let w : G → N := λ g, z g - (g • x - x),
    -- have crucial : ∀ (g : G), ψ (z g - (g • x - x)) = 0,
    -- { simp [hy, hx] },

    -- note "crucial" above
    rw H1.ker_quotient at hz,
    cases hz with p hp,
    rw Z1.ext_iff at hp,
    simp at hp, -- yes
    rw mem_range,
    /-
    ∃ (x : H1 G M), ⇑(φ.H1) x = ⇑Z1.quotient z -/
    --refine ⟨_, _⟩, swap,
    -- ⊢ ⇑(φ.H1) ?m_1 = ⇑Z1.quotient z
    -- Idea : I want to apply the universal property
    -- for H¹(φ) but this is of the form 

    refine ⟨Z1.quotient (_ : Z1 G M), _⟩, swap, --working backwards
    { rw Z1.H1_map_mk,
      sorry },
    -- this next goal might randomly disappear, it's not a prop
    -- it's `⊢ H1 G M`
    sorry }
end

end exactness

#where

#check H1.induction_on
/-
H1.induction_on : ∀ {G M : Type} [_inst_1 : monoid G]
[_inst_2 : add_comm_group M] [_inst_3 : distrib_mul_action G M]
{p : H1 G M → Prop}, 
(∀ (z : Z1 G M), p (⇑Z1.quotient z)) → ∀ (h : H1 G M), p h
-/
