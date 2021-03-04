import tactic

/-

# Further analysis of the universal property of quotients.

Let `X` be a type with an equivalence relation on it.
We say that a pair `Q` and `p : X → Q` is _universal_
if `p` is constant on equivalence classes, and furthermore
that `p` is "initial" for this property, which means that
for all types `T` and for all functions `f : X → T` which
are constant on equivalence classes, there's a unique `g : Q → T`
such that `f = g ∘ p`. Let's formalise this universal property in Lean.

-/
def is_universal {X : Type} [setoid X] (Q : Type) (p : X → Q) :=
(∀ x y, x ≈ y → p x = p y) ∧
∀ (T : Type) (f : X → T) (h : ∀ x y : X, x ≈ y → f x = f y),
  ∃ (g : Q → T), f = g ∘ p ∧ ∀ k : Q → T, f = k ∘ p → k = g

variables {X : Type} [setoid X] {Q : Type} {p : X → Q}

/-

`is_universal` is a definition, so we need to make a little API for it.
Let's start by giving us a way to get to that function `g` whose
existence is claimed by `is_universal`.

If `hu` is a proof that `(Q, p)` is universal, then given
`f : X → T` and a proof `h` that `f` is constant on equivalence classes,
let's define `g_univ hu h` to be the function `g : Q → T` which makes
the diagram commute. To define this we have to go from an "exists `g`"
statement in `is_universal` to an actual function `g`. We do this with
the `classical.some : (∃ (a : X), p a) → X` function. Note that this function
is noncomputable, but this doesn't matter because we are proving theorems.
-/

noncomputable def g_univ (hu : is_universal Q p)
  {T : Type} {f : X → T} (h : ∀ x y : X, x ≈ y → f x = f y) : Q → T :=
classical.some (hu.2 T f h)

/-

Now `g_univ` is also a definition, so we need to make an API for this too!

The proof that `g := g_univ hu h : Q → T` satisfies `f = g ∘ p` needs
a convenient name -- let's call it called `g_univ_spec hu h`

-/
lemma g_univ_spec (hu : is_universal Q p)
  {T : Type} {f : X → T} (h : ∀ x y : X, x ≈ y → f x = f y) :
    f = (g_univ hu h) ∘ p :=
(classical.some_spec (hu.2 T f h)).1

/-

And here's a variant which says that the functions take the same
values everywhere. This is sometimes more convenient. I prove it
by applying `congr_fun` to the previous proof.

-/

lemma g_univ_spec' (hu : is_universal Q p)
  {T : Type} {f : X → T} (h : ∀ x y : X, x ≈ y → f x = f y) (x : X) :
    f x = (g_univ hu h) (p x) :=
congr_fun (g_univ_spec hu h) x

/-

The proof of uniqueness of `g`, or more precisely that if `k : Q → T`
satisfies `f = k ∘ p` then `k = g`, also needs a convenient name --
let's call it `g_univ_unique hu h`.

-/

lemma g_univ_unique (hu : is_universal Q p)
  {T : Type} {f : X → T} (h : ∀ x y : X, x ≈ y → f x = f y) :
  ∀ (k : Q → T), f = k ∘ p → k = g_univ hu h :=
(classical.some_spec (hu.2 T f h)).2

/-

Let's make a variant where the conclusion is that `k q = g q` for all `q`,
other than just saying `k = g`. Again we just apply `congr_fun` to the
previous proof.

-/

lemma g_univ_unique' (hu : is_universal Q p)
  {T : Type} {f : X → T} (h : ∀ x y : X, x ≈ y → f x = f y) (k : Q → T)
  (hk : f = k ∘ p) (q : Q) : k q = g_univ hu h q :=
congr_fun (g_univ_unique hu h k hk) q

/-

Note that if `h : is_universal Q p` then `h` has type `P ∧ Q`
so `h.1` is a proof of `∀ x y, x ≈ y → p x = p y`. 

Example: if `(Q, p)` is universal, then `p` is constant on equivalence classes.

-/

example (X : Type) [s : setoid X] (Q : Type) (p : X → Q) (h : is_universal Q p)
  (x y : X) (hxy : x ≈ y) : p x = p y :=
h.1 x y hxy

/-

Now let's go through the standard proof that universal objects
are unique up to isomorphism. 


-/

-- Here's how to use `g_univ` to define functions between universal objects.
noncomputable example {X : Type} [s : setoid X] {Q1 Q2 : Type}
  {p1 : X → Q1} {p2 : X → Q2}
  (h1 : is_universal Q1 p1) (h2 : is_universal Q2 p2) :
  Q1 → Q2 :=
  g_univ h1 h2.1

-- Applying the universal property to `p : X → Q` gives us the
-- identity function `id : Q → Q`
lemma useful {X : Type} [s : setoid X] {Q : Type}
  {p : X → Q} (h1 : is_universal Q p) :
  g_univ h1 h1.1 = id :=
begin
  symmetry,
  apply g_univ_unique,
  refl,
end

-- A variant of the previous lemma where we say `g q = q` rather than `g = id`
lemma useful2 {X : Type} [s : setoid X] {Q : Type}
  {p : X → Q} (h1 : is_universal Q p) (q : Q) :
  g_univ h1 h1.1 q = q :=
begin
  rw useful,
  refl
end

-- This is tricky. Ask if you need help.
noncomputable def univ_equiv {X : Type} [s : setoid X] {Q1 Q2 : Type}
  {p1 : X → Q1} {p2 : X → Q2}
  (h1 : is_universal Q1 p1) (h2 : is_universal Q2 p2) :
  Q1 ≃ Q2 :=
{ to_fun := g_univ h1 h2.1,
  inv_fun := g_univ h2 h1.1,
  left_inv := begin
    intro q1,
    conv_rhs {rw ← useful2 h1 q1},
    apply g_univ_unique' h1 h1.1 _ _ q1,
    ext x,
    dsimp only [function.comp],
    rw ← g_univ_spec' h1,
    rw ← g_univ_spec' h2,
  end,
  right_inv := begin
    intro q2,
    conv_rhs {rw ← useful2 h2 q2},
    apply g_univ_unique' h2 h2.1 _ _ q2,
    ext x,
    dsimp only [function.comp],
    rw ← g_univ_spec' h2,
    rw ← g_univ_spec' h1,    
  end }

-- Lean's builtin quotients are universal
theorem quotient_is_universal {X : Type} [s : setoid X] :
  is_universal (quotient s) quotient.mk :=
begin
  use [λ _ _, quotient.sound],
  intros T f h,
  use quotient.lift f h,
  split,
  { refl },
  { rintros g rfl,
    ext x,
    apply quotient.induction_on x,
    intro a,
    refl },
end

-- so any universal object is isomorphic to the quotient object.
noncomputable def universal_equiv_quotient (X : Type) [s : setoid X]
  (Q : Type) (p : X → Q) (hu : is_universal Q p) :
Q ≃ (quotient s) :=
univ_equiv hu quotient_is_universal

