import week_8.ideas.Part_B_H0
import group_theory.quotient_group

/-

# 1-cocycles

We develop the theory of 1-cocycles. We'll call them cocycles
for short.

# Notation 

Throughout we stick to the conventions that `G` is a group (or even
a monoid, we never use inversion) and that `M` is a `G`-module,
that is, an additive abelian group with a `G`-action.

## The mathematical definition

Let $$G$$, $$M$$, $$g$$ and $$h$$ be variables of the obvious types.

If $$M$$ is a $$G$$-module then a cocycle from $$G$$ to $$M$$
is a function $$f:G → M$$ such that $$f(gh)=f(g)+gf(h)$$.

failed Zulip post:
It is to make the language easier for mathematicians to read. 
To be quite frank mathematicians would like the primary notation to 
be as close to c:G\to Mc:G→M as you can possibly get in your 
horrible unicode (computer scientists and mathematicians do not 
use : in the same way, our : is your :⇑. We would quite happily have 
some `double_down_arrow_notation_c : distrib_mul_action_hom G M`
to be "where all the theorems about cocycles are stored". We love
dot notation for this. we can manipulate `c` as a function and use`c.is_injective`
to extract the fact that it's injective. Was there an idea that in Lean 4
it was better go back to an unbundled approach? I don't have a problem
with the bundled approach, I just want it to look sexy.

TODO: mention to sebastian that function coercion was a classic example
of pretty printer not round tripping.

`Z1 G M` is the type of 1-cocycles `c : G → M`, or, more precisely,
`⇑c : G → M`. In other
words, a 1-cocycle is a pair consisting of a function `⇑c : Z1 G M`
and a proof `c.spec` that it satisfies the cocycle identity:

`∀ (g h : G), c (g * h) = c g + g • c h`

`Z1 G M` has an `add_comm_group` structure on it, defined by
addition of underlying functions (i.e. by pulling back the `add_comm_group`
structure on `M`)

-- need to document G_Z1.hom , φ.Z1_hom if it exists etc
-/

section cocycle_thoughts

-- three ways of doing 1-cocycles.

-- Way 1: do not define 1-cocycles: it's much easier working
-- with the abstract function Π {G} {M} f g h, f (g * h) = f g + g • f h,
-- why name it at all?

-- Way 2: bundled

variables 
-- let `G` be a group, with group law `⋆`
(G : Type) [monoid G] -- it all works with monoids
-- let `M` be an abelian G-module, that is, an group with group law `+`
(M : Type) [add_comm_group M] 
-- equipped with a `G`-action denoted by `•`
[distrib_mul_action G M]

/-- A cocycle is a function $$f:G→ M$$ satisfying the _cocycle identity_ 
`f.spec : ∀ g h, f (g * h) = f g + g • f h` -/
structure cocycle :=
-- (⇑f : G → M)
(to_fun : G → M)
-- stupid notation issue
(spec' : ∀ g h, to_fun (g * h) = to_fun g + g • to_fun h)
-- less ugly would be spec : ∀ (g h : G), c (g * h) = c g + g • c h)

-- Can't I tell the `structure` command to deal with this?
instance : has_coe_to_fun (cocycle G M) := ⟨_,cocycle.to_fun⟩

variables {G M} (c : cocycle G M)
namespace cocycle
def spec : ∀ (g h : G), c (g * h) = c g + g • c h := c.spec'
end cocycle
-- rm -rf cocycle.*'

-- Way 3 : unbundled

--notation `is_cocycle` f := ∀ (g h : domain f), f (g * h) = f g + g • f h
-- or abbreviation?
def is_cocycle (c : G → M) : Prop :=
∀ (g h : G), c (g * h) = c g + g • c h

end cocycle_thoughts

/-

## The term `Z1_subgroup G M : add_subgroup (G → M)` 
## and the type `Z1 G M : Type`

### Z1_subgroup, the term

`Z1_subgroup G M` is the `add_subgroup (G → M)` structure on the
set cut out by the predicate `is_cocycle (c : G → M)`,

-/
def Z1_subgroup (G M : Type)
  [monoid G] [add_comm_group M] [distrib_mul_action G M] : add_subgroup (G → M) :=
{ carrier := { f : G → M | ∀ (g h), f (g * h) = f g + g • f h },
  -- stupid ' s
  zero_mem' := begin
    -- the zero map is a cocycle
    simp,
  end,
  -- :-(
  add_mem' := λ c1 c2 hc1 hc2 g h, begin
    -- sum of two cocycles is a cocycle.
    -- Note that the `abel` tactic is to additive abelian groups
    -- what the `ring` tactic is to commutative semirings.
    simp [hc1 g h, hc2 g h],
    abel,
  end,
  -- proofs are always "use the hypotheses on the goal and then it's obvious"
  neg_mem' := λ c hc g h, begin
    simp [hc g h],
    abel,
  end }

def carrier.is_add_subgroup (G M : Type)
  [monoid G] [add_comm_group M] [distrib_mul_action G M] :
  is_add_subgroup {f : G → M | is_cocycle f } :=
(Z1_subgroup G M).is_add_subgroup
/-
### Z1, the type
-/

/-- The type `Z1 G M` of 1-cocycles from `G` to `M`. Here `G` is a group
and `M` is `G`-module. Comes equipped with a coercion to function.
The cocycle condition on `⇑c` is `c.spec`. -/
structure Z1 (G M : Type)
  [monoid G] [add_comm_monoid M] [distrib_mul_action G M] : Type :=
(to_fun : G → M)
(is_cocycle' : ∀ (g h : G), to_fun (g * h) = to_fun g + g • to_fun h)

-- This is a definition so we need to make an API
namespace Z1

-- let G be a group (or a monoid) and let M be a G-module.
variables {G M : Type}
  [monoid G] [add_comm_monoid M] [distrib_mul_action G M]

-- add a coercion from a cocycle to the function G → M
instance : has_coe_to_fun (Z1 G M) :=
{ F := λ _, G → M,
  coe := to_fun }

@[simp] lemma coe_apply (to_fun : G → M)
  (is_cocycle : ∀ (g h : G), to_fun (g * h) = to_fun g + g • to_fun h) (g : G) :
({ to_fun := to_fun, is_cocycle' := is_cocycle } : Z1 G M) g = to_fun g := rfl


-- add a specification for the coercion

lemma spec (a : Z1 G M) : ∀ (g h : G), a (g * h) = a g + g • a h :=
-- this is the last time we'll see `a.is_cocycle`: we'll 
-- use `a.spec` from now on because it applies to `⇑a` and not `a.to_fun`.
a.is_cocycle'

-- add an extensionality lemma
@[ext] lemma ext (a b : Z1 G M) (h : ∀ g, a g = b g) : a = b :=
begin
  cases a, cases b, simp, ext g, exact h g,
end

lemma ext_iff (a b : Z1 G M) : a = b ↔ ∀ g, a g = b g :=
⟨by { rintro rfl, exact λ _, rfl }, ext _ _⟩ 

def add (a b : Z1 G M) : Z1 G M :=
{ to_fun := λ g, a g + b g,
  is_cocycle'
 := begin
    rintros g h,
    simp [a.spec, b.spec],
    abel,    
  end }

instance : has_add (Z1 G M) := ⟨add⟩

@[simp] lemma coe_add (a b : Z1 G M) (g : G) : (a + b) g = a g + b g := rfl

def zero : Z1 G M := 
{ to_fun := λ g, 0,
  is_cocycle'
 := begin
    simp,
  end
}

instance : has_zero (Z1 G M) := ⟨zero⟩

@[simp] lemma coe_zero (g : G) : (0 : Z1 G M) g = 0 := rfl

-- group versions
variables {A : Type} [add_comm_group A] [distrib_mul_action G A]
def neg (a : Z1 G A) : Z1 G A :=
{ to_fun := λ g, -(a g),
  is_cocycle'
 := begin
    intros,
    simp [a.spec],
    abel,
  end
}

instance : has_neg (Z1 G A) := ⟨neg⟩

@[simp] lemma coe_neg (a : Z1 G A) (g : G) : (-a) g = -(a g) := rfl

def sub (a b : Z1 G A) : Z1 G A := a + -b

instance : has_sub (Z1 G A) := ⟨sub⟩

@[simp] lemma coe_sub (a b : Z1 G A) (g : G) : (a - b) g = a g - b g :=
(sub_eq_add_neg _ _).symm

-- make the cocycles into a group
instance : add_comm_group (Z1 G A) :=
begin
  refine_struct { 
    add := (+),
    zero := (0 : Z1 G A),
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

-- do the same for the monoids, why not
instance : add_comm_monoid (Z1 G M) :=
begin
  refine_struct { add := (+), zero := (0 : Z1 G M) };
  { intros, ext, simp; abel }
end

end Z1
