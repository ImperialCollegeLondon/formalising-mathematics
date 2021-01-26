import tactic

/-!

# Groups

Definition and basic properties of a group

-/

namespace xena

/-

## Definition of a group

`has_mul G` means that `G` has a multiplication `* : G → G → G`
`has_one G` means that `G` has a `1 : G`
`has_inv G` means that `G` has an `⁻¹ : G → G`

All of `*`, `1` and `⁻¹` are notation, and no axioms are assumed
for any of them.

A group has all of this notation, and the group axioms too. 
Let's now define the group class.
-/

class group (G : Type) extends has_mul G, has_one G, has_inv G :=
(mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c))
(one_mul : ∀ (a : G), 1 * a = a)
(mul_left_inv : ∀ (a : G), a⁻¹ * a = 1)

/-

Formally, a term of type `group G` is now a multiplication, 1, and inverse
function, together with the notation, and satisfying the axioms.

The way to say "let G be a group" is now `(G : Type) [group G]`

The square bracket notation is the notation used for classes.
Formally, it means "put a term of type `group G` into the type class
inference system"

-/

/-

We have been extremely mean with our axioms. Some authors also add
the axioms `mul_one : ∀ (a : G), a * 1 = a`
and `mul_right_inv : ∀ (a : G), a * a⁻¹ = 1`.

But these follow from the three axioms we used. Our first job is
to prove them. As you might imagine, mathematically this is pretty
much the trickiest part, because we have to be careful not to
accidentally assume these axioms when we're proving them.

Here are the four lemmas we will prove.

`mul_left_cancel : ∀ (a b c : G), a * b = a * c → b = c`
`mul_eq_of_eq_inv_mul {a x y : G} : x = a⁻¹ * y → a * x = y`
`mul_one (a : G) : a * 1 = a`
`mul_right_inv (a : G) : a * a⁻¹ = 1`
-/
namespace group

variables {G : Type} [group G]  

/-
We start by proving `mul_left_cancel : ∀ a b c, a * b = a * c → b = c`.
We assume `Habac : a * b = a * c` and deduce `b = c`. I've written
down the maths proof. Your job is to supply the rewrites that are
necessary to justify each step. Each rewrite is either one of
the axioms of a group, or an assumption. A reminder of the axioms:

`mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c)`
`one_mul : ∀ (a : G), 1 * a = a`
`mul_left_inv : ∀ (a : G), a⁻¹ * a = 1`

This proof could be done using rewrites, but I will take this opportunity
to introduce the `calc` tactic.
-/
lemma mul_left_cancel (a b c : G) (Habac : a * b = a * c) : b = c := 
begin
 calc b = 1 * b         : by rw one_mul
    ... = (a⁻¹ * a) * b : by sorry -- replace `sorry` with `rw X` as appropriate
    ... = a⁻¹ * (a * b) : by sorry
    ... = a⁻¹ * (a * c) : by sorry
    ... = (a⁻¹ * a) * c : by sorry
    ... = 1 * c         : by sorry
    ... = c             : by sorry
end

/-
Next we prove that if `x = a⁻¹ * y` then `a * x = y`. Remember we are still
missing `mul_one` and `mul_right_inv`. A proof that avoids them is
the following: we want `a * x = y`. Now `apply`ing the previous lemma, it
suffices to prove that `a⁻¹ * (a * x) = a⁻¹ * y.`
Now use associativity and left cancellation on on the left, to reduce
to `h`. 

Note that `mul_left_cancel` is a function, and its first input is 
called `a`, but you had better give it `a⁻¹` insted.  
-/
lemma mul_eq_of_eq_inv_mul {a x y : G} (h : x = a⁻¹ * y) : a * x = y :=
begin
  apply mul_left_cancel a⁻¹, 
  sorry
end

-- It's a bore to keep introducing variable names.

-- Let `a,b,c,x,y` be elements of `G`.
variables (a b c x y : G)

/-
We can use `mul_eq_of_eq_inv_mul` to prove the two "missing" axioms `mul_one`
and `mul_right_inv`, and then our lives will be much easier. Try `apply`ing it
in the theorems below.
-/

@[simp] theorem mul_one : a * 1 = a :=
begin
  sorry
end

@[simp] theorem mul_right_inv : a * a⁻¹ = 1 :=
begin
  sorry
end

-- Now let's talk about what that `@[simp]` means.

/-

## Lean's simplifier

A human sees `a * a⁻¹` in group theory, and instantly replaces it with `1`.
We are going to train a simple AI called `simp` to do the same thing.

Lean's simplifier `simp` is a "term rewriting system". This means
that if you teach it a bunch of theorems of the form `A = B` or
`P ↔ Q` (by tagging them with the `@[simp]` attribute) and then give
it a complicated equality, like

`example : (a * b) * 1⁻¹⁻¹ * b⁻¹ * (a⁻¹ * a⁻¹⁻¹⁻¹) * a = 1`

then it will try to use the `rw` tactic as much as it can, using the lemmas
it has been taught, in an attempt to simplify the goal. If it manages
to solve it completely, then great! If it does not, but you feel like
it should have done, you might want to tag more lemmas with `@[simp]`.
`simp` should only be used to completely close goals. We are now
going to train the simplifier to solve the example above (indeed, we are
going to train it to reduce an arbitrary element of a free group into
a unique normal form, so it will solve any equalities which are true
for all groups, like the example above).

## Important note

Lean's simplifier does a series of rewrites, each one replacing something
with something else. But the simplifier will always rewrite from left to right!
If you tell it that `A = B` is a `simp` lemma then it will replace `A`s with
`B`s, but it will never replace `B`s with `A`s. If you tag a proof
of `A = B` with `@[simp]` and you also tag a proof of `B = A` with
`@[simp]`, then the simplifier will get stuck in an infinite loop when
it runs into an `A`!

Because the simplifier works from left to right, an important
rule of thumb is that if `A = B` is a `simp` lemma, then `B` should
probably be simpler than `A`! In particular, equality should not be
thought of as symmetric here. It is not a coincidence that in
the theorems below

`@[simp] theorem mul_one (a : G) : a * 1 = a`
`@[simp] theorem mul_right_inv (a : G) : a * a⁻¹ = 1`

the right hand side is simpler than the left hand side.

Let's train Lean's simplifier! Let's teach it the axioms of a group next:

-/

attribute [simp] one_mul mul_left_inv mul_assoc

/-
Now let's teach the simplifier the following five lemmas:

`inv_mul_cancel_left : a⁻¹ * (a * b) = b`
`mul_inv_cancel_left : a * (a⁻¹ * b) = b`
`inv_mul : (a * b)⁻¹ = b⁻¹ * a⁻¹`
`one_inv : (1 : G)⁻¹ = 1`
`inv_inv : (a⁻¹)⁻¹ = a`

Note that in each case, the right hand side is simpler
than the left hand side.

Try using the simplifier in your proofs! I will do the
first one for you.

-/

@[simp] lemma inv_mul_cancel_left : a⁻¹ * (a * b) = b :=
begin
  sorry
end

@[simp] lemma mul_inv_cancel_left : a * (a⁻¹ * b) = b :=
begin
  sorry
end

@[simp] lemma inv_mul : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
begin
  sorry
end

@[simp] lemma one_inv : (1 : G)⁻¹ = 1 :=
begin
  sorry
end

@[simp] lemma inv_inv : a ⁻¹ ⁻¹ = a :=
begin
  sorry
end

/-

The reason I choose these five lemmas in particular, is that
term rewriting systems are very well understood by computer
scientists, and in particular there is something called the
Knuth-Bendix algorithm, which, given as input the three axioms
for a group which we used, produces a "confluent and noetherian
term rewrite system" that transforms every term into a unique
normal form. The system it produces is precisely the `simp`
lemmas which we haven proven above! See

https://en.wikipedia.org/wiki/Word_problem_(mathematics)#Example:_A_term_rewriting_system_to_decide_the_word_problem_in_the_free_group

for more information. I won't talk any more about the Knuth-Bendix
algorithm because it's really computer science, and I don't really
understand it, but apparently if you apply it to polynomial rings
then you get the Buchberger's algorithm for computing Gröbner bases.

-/

-- Now let's try our example...
example : (a * b) * 1⁻¹⁻¹ * b⁻¹ * (a⁻¹ * a⁻¹⁻¹⁻¹) * a = 1 := by simp -- short for begin simp end

-- The simplifier solves it!

-- try your own identities. `simp` will solve them all!

/-
This is everything I wanted to show you about groups and the simplifier today.
You can now either go on to subgroups in Part B, or practice your group
theory skills by proving the lemmas below.
-/

/-
We already proved `mul_eq_of_eq_inv_mul` but there are several other
similar-looking, but slightly different, versions of this. Here
is one.
-/

lemma eq_mul_inv_of_mul_eq {a b c : G} (h : a * c = b) : a = b * c⁻¹ :=
begin
  sorry
end

lemma eq_inv_mul_of_mul_eq {a b c : G} (h : b * a = c) : a = b⁻¹ * c :=
begin
  sorry
end

lemma mul_left_eq_self {a b : G} : a * b = b ↔ a = 1 :=
begin
  sorry
end

lemma mul_right_eq_self {a b : G} : a * b = a ↔ b = 1 :=
begin
  sorry
end

lemma eq_inv_of_mul_eq_one {a b : G} (h : a * b = 1) : a = b⁻¹ :=
begin
  sorry
end

lemma inv_eq_of_mul_eq_one {a b : G} (h : a * b = 1) : a⁻¹ = b :=
begin
  sorry,
end

lemma unique_left_id {e : G} (h : ∀ x : G, e * x = x) : e = 1 :=
begin
  sorry
end

lemma unique_right_inv {a b : G} (h : a * b = 1) : b = a⁻¹ :=
begin
  sorry
end

lemma mul_left_cancel_iff (a x y : G) : a * x = a * y ↔ x = y :=
begin
  split,
  { apply mul_left_cancel },
  { intro hxy,
    rwa hxy }
end

-- You don't even need to go into tactic mode (begin/end) to use `calc`:
lemma mul_right_cancel (a x y : G) (Habac : x * a = y * a) : x = y := 
calc x = x * 1 : by rw mul_one
  -- missing arguments here
  ... = y : by sorry

-- `↔` lemmas are good simp lemmas too.
@[simp] theorem inv_inj_iff {a b : G}: a⁻¹ = b⁻¹ ↔ a = b :=
begin
  sorry
end   

theorem inv_eq {a b : G}: a⁻¹ = b ↔ b⁻¹ = a :=
begin
  sorry
end  

end group

end xena
