-- need the real numbers
import data.real.basic
-- need the tactics
import tactic

/-

# Limits

We develop a theory of limits of sequences a₀, a₁, a₂, … of reals,
following the way is it traditionally done in a first year undergraduate
mathematics course.

## Overview of the file

This file contains the basic definition of the limit of a sequence, and
proves basic properties about it.

The `data.real.basic` import imports the definition and basic
properties of the real numbers, including, for example, 
the absolute value function `abs : ℝ → ℝ`, and the proof
that `ℝ` is a complete totally ordered archimedean field.
To get `ℝ` in Lean, type `\R`.

We define the predicate `is_limit (a : ℕ → ℝ) (l : ℝ)` to mean that `aₙ → l`
in the usual way:

`∀ ε > 0, ∃ N, ∀ n ≥ N, | a n - l | < ε`

We then develop the basic theory of limits.

## Main theorems

variables (a b c : ℕ → ℝ) (c l m : ℝ)
* `is_limit_const : is_limit (λ n, c) c`
* `is_limit_subsingleton (hl : is_limit a l) (hm : is_limit a m) : l = m`
* `is_limit_add (h1 : is_limit a l) (h2 : is_limit b m) : is_limit (a + b) (l + m)`
* `is_limit_mul (h1 : is_limit a l) (h2 : is_limit b m) : is_limit (a * b) (l * m)`
* `is_limit_le_of_le (hl : is_limit a l) (hm : is_limit b m) (hle : ∀ n, a n ≤ b n) : l ≤ m`
* `sandwich (ha : is_limit a l) (hc : is_limit c l) 
    (hab : ∀ n, a n ≤ b n) (hbc : ∀ n, b n ≤ c n) : is_limit b l`

-/


namespace xena

-- the maths starts here.

-- We introduce the usual mathematical notation for absolute value
local notation `|` x `|` := abs x

-- We model a sequence a₀, a₁, a₂,... of real numbers as a function
-- from ℕ := {0,1,2,...} to ℝ, sending n to aₙ . So in the below
-- definition of the limit of a sequence, a : ℕ → ℝ is the sequence.

/-- `l` is the limit of the sequence `a` of reals -/
definition is_limit (a : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, | a n - l | < ε

/-
Note that `is_limit` is not a *function* (ℕ → ℝ) → ℝ! It is
a _binary relation_ on (ℕ → ℝ) and ℝ, i.e. it's a function which
takes as input a sequence and a candidate limit, and returns the
true-false statement saying that the sequence converges to the limit.

The reason we can't use a "limit" function, which takes in a sequence
and returns its limit, is twofold:
(1) some sequences (like 0, 1, 0, 1, 0, 1,…) don't have
a limit at all, and
(2) at this point in the development, some sequences might in theory have more
than one limit (and if we were working with a non-Hausdorff topological space
rather than `ℝ` this could of course actually happen, although we will see
below that it can't happen here).
-/

/-
Let's start with a warmup : the constant sequence with value c tends to c.
Before we start though, I need to talk about this weird `λ` notation
which functional programmers use.

### λ notation for functions

This is a lot less scary than it looks. The notation `λ n, f n`
in Lean just means what we mathematicians would call `f` or `f(x)`.
Literally, it means "the function sending `n` to `f n`, with this
added twist that we don't need to write the brackets (although `λ n, f(n)`
would also work fine). Another way of rewriting it in a more familiar
manner: `λ n, f n` is the function `n ↦ f n`. So, for example, `λ n, 2 * n`
is just the function `f(x)=2*x`. It's sometimes called "anonymous function notation"
because we do not need to introduce a name for the function if we use
lambda notation.

So you need to know a trick here. What happens if we have such a
function defined by lambda notation, and then we actually try to
evaluate it! You have to know how to change `(λ n, f n) (37)`
into `f(37)` (or, as Lean would call it, `f 37`). Computer scientists
call this transformation "beta reduction". In Lean, beta reduction is true
definitionally, so if you are using `apply` or `intro` or other
tactics which work up to definitional equality then you might not
even have to change it at all. But if your goal contains an "evaluated λ"
like `⊢ (λ n, f n) 37` and you have a hypothesis `h1 : f 37 = 100` then
`rw h1` will fail, because `rw` is pickier and only worked up to syntactic
equality. So you need to know the trick to change this goal to `f 37`,
which is the tactic `dsimp only`. It works on hypotheses too -- `dsimp only at h`
will remove an evaluated `λ` from hypothesis `h`. 

We will now prove that the limit of a constant sequence `aₙ = c` is `c`.
The definition of the constant sequence is `λ n, c`, the function sending
every `n` to `c`. I have given you the proof. Step through it by moving your
cursor through it line by line and watch the tactic state changing.

-/

/-- The limit of a constant sequence is the constant. -/
lemma is_limit_const (c : ℝ) : is_limit (λ n, c) c :=
begin
  -- is_limit a l is *by definition* "∀ ε, ε > 0 → ..." so we
  -- can just start with `intros`.
  intros ε εpos,
  -- we need to come up with some N such that n ≥ N implies |c - c| < ε.
  -- We have some flexibility here :-)
  use 37,
  -- Now assume n is a natural which is at least 37, but we may as
  -- well just forget the fact that n ≥ 37 because we're not going to use it.
  rintro n -,
  -- Now we have an "unreduced lambda term" in the goal, so let's
  -- beta reduce it.
  dsimp only,
  -- the simplifier is bound to know that `c - c = 0`
  simp,
  -- finally, `a > b` is *definitionally* `b < a`, and the `exact`
  -- tactic works up to definitional equality.
  exact εpos,
end

/-

I am going to walk you through the next proof as well. It's a proof
that if `aₙ → l` and `aₙ → m` then `l = m`. Here is how it is stated
in Lean:

```
theorem is_limit_subsingleton {a : ℕ → ℝ} {l m : ℝ} (hl : is_limit a l)
(hm : is_limit a m) : l = m := ...
```

Before we go through this proof, I think it's time I explained these
squiggly brackets properly. How come I've written `{a : ℕ → ℝ}`
and not `(a : ℕ → ℝ)`?

### Squiggly brackets {} in function inputs, and dependent functions.

`is_limit_subsingleton` is a proof that a sequence can have at most one limit.
It is also a function. Learning to think about proofs as functions is
an important skill for proving the theorems in this workshop. So let's
talk a bit about how a proof can be a function.

In Lean's dependent type theory, there are types and terms, and every term has
a unique type. Types and terms are used to unify two ideas which mathematicians
usually regard as completely different: that of sets and elements,
and that of theorems and proofs. Let's take a close look at what exactly this
function `is_limit_subsingleton` does.

Let's take a closer look at `is_limit_subsingleton` (the theorem is stated
20 lines above here). It is a function with five inputs. The first input
is a sequence `a : ℕ → ℝ`. The second and third are real numbers `l` and `m`.
The fourth input is a proof that `a(n)` tends to `l`, and the fifth is a proof that
`a(n)` tends to `m`. The output of the function (after the colon) is a proof
that `l = m`. This is how Lean thinks about proofs internally, and it's
important that you internalise this point of view because you will be treating
proofs as functions and evaluating them on inputs to get other proofs
quite a bit today. If you still think it's a bit weird having proofs as inputs
and outputs to functions, just think of a true-false statement (e.g. a theorem
statement) as being a set, and the elements of that set are the proofs of
the theorem. For example `2 + 2 = 5` is a set with no elements, because
there are no proofs of this theorem (assuming that mathematics is consistent).

Now if you think about these inputs carefully, and you think about your mental
model of a function, you may realised that there is something else a bit fishy
going on here. Usually you would think of a function with five inputs
as a function from `A × B × C × D × E` to `X`, where `A`, `B`, `C`, `D` and `E`
are all sets. The first three inputs `a` (of type `ℕ → ℝ`) and `l` and `m`
(of type `ℝ`) are uncontroversial: we can just set `A = ℕ → ℝ` and `B = C = ℝ`.
But the fourth input to `is_limit_singleton` is an element
of the set of proofs of `is_limit a l`, the statement that `a(n)` tends to `l`,
and in particular this set itself *depends on the first two inputs*. 
The set `D` itself is a function of `a` and `l` -- the actual inputs themselves,
rather than the sets `A` and `B` that they belong to. The same is true
for the set `E`, which is a function of `a` and `m`. This slightly bizarre
set-up has the even more bizarre consequence that actually, if Lean knows the
fourth and fifth inputs (in this case, proofs of `is_limit a l` and `is_limit a m`)
then it *does not actually even need to know what the first three inputs are*,
because Lean can work them out from the *type* of the fourth and fifth inputs.

In summary then, the five inputs to this functions are:
`a` of type `ℕ → ℝ`,
`l` and `m` of type `ℝ`,
`h1` of type `is_limit a l`
`h2` of type `is_limit a m`.

In particular, if we know the fourth and fifth inputs `h1` and `h2`,
then by looking at the types of these terms, we can actually work out
what the first three inputs *have to be* in order to make everything make sense.

This is why we put the first three inputs in `{}` brackets. This means
"these inputs are part of the function, but Lean's *unification system*
(the part of the system which checks that everything has the right type)
will work them out automatically, so we will not trouble the user by
asking for them". In short, if we ever run this function of five inputs,
we can just give `h1` and `h2` and let Lean figure out the first three
inputs itself. In general if a function input has `{}` brackets then
the user does not have to supply those inputs, the user can trust the
system to fill them in automatically.

That's quite enough about the statement! Let's get back to mathematics
and I will talk you through the proof. Step through the proof line
by line and watch the tactic state change.
-/

theorem is_limit_subsingleton {a : ℕ → ℝ} {l m : ℝ} (hl : is_limit a l)
(hm : is_limit a m) : l = m :=
begin
  -- There are several ways to prove this, but let's prove it
  -- by contradiction. Let's assume `h : l ≠ m` and prove `false`.
  by_contra h,
  -- The idea is that if `ε = |l - m|` then the sequence `a` will
  -- eventually be within `ε/2` of `l` and `ε/2` of `m`, which
  -- will be a contradiction. To make life easier let's break
  -- the symmetry and assume WLOG that `l < m`, because then
  -- we can just let `ε` be `m - l`. 
  wlog hlm : l < m,
  -- Lean checks that everything is symmetric in `l` and `m` so
  -- this tactic succeeds, but asks us to prove that either
  -- `l < m` or `m < l`. We now have two goals so let's
  -- put a `{` `}` pair to get back to one goal.
  { -- now we just have the one easy goal `l < m ∨ m < l`. 
    -- First we note that the reals are totally ordered so
    -- we can add `l < m ∨ l = m ∨ m < l` to the list of
    -- hypotheses with the `have` tactic:
    have : l < m ∨ l = m ∨ m < l := lt_trichotomy l m,
    -- Now the result follows from pure logic.
    tauto },
  -- Now let's define ε to be m - l.
  set ε := m - l with hε,
  -- Mathematically, the plan is to now find big natural numbers `L` and `M`
  -- such that `n ≥ L → |a n - l| < ε/2`, and `n ≥ M → |a n - m| < ε/2`,
  -- and then set `n = max L M` to get a contradiction. How do we do this
  -- in Lean?

  -- Well, let's think about `hl` as a function. Its type is
  -- `is_limit a l` which is definitionally `∀ ε, ε > 0 → ...`.
  -- So `hl` is a function which wants as an input a real number
  -- and a proof that it is positive. Let's first give `hl` the
  -- real number `ε/2` once and for all (it's the only time we'll 
  -- be using `hl` in the proof so we can change its definition)
  specialize hl (ε/2),
  -- Now `hl` is a function which wants a proof by `ε/2>0` as its input.
  -- Mathematically, this is obvious: `ε/2=(m-l)/2` and `l < m`. 
  -- Lean's `linarith` (linear arithmetic) tactic can solve this sort of goal:
  have hε2 : ε/2 > 0 := by linarith,
  -- Now we can specialize `hl` further:
  specialize hl hε2,
  -- Now `hl` isn't a function any more. In the lingo, it's an inductive
  -- type rather than a pi type. 
  -- `hl : ∃ (N : ℕ), ∀ (n : ℕ), n ≥ N → |a n - l| < ε / 2`
  -- `hl` is now a made from a pair of pieces of information: first a natural
  -- number `N`, and second a proof of some fact about `N`. We can take
  -- `hl` apart into these two pieces with the `cases` tactic:
  cases hl with L hL,
  -- Now `L` is the natural and `hL` is a proof of a theorem about it:
  -- `hL : ∀ (n : ℕ), n ≥ L → |a n - l| < ε / 2`

  -- We now need to do the same thing with `hm`. Let's just do it all in one
  -- go. Check that you understand why this one line does the same sort of thing
  -- as the four lines above.
  cases hm (ε/2) (by linarith) with M hM,

  -- Now let's get back to the maths proof. Let N be the max of L and M.
  set N := max L M with hN,
  -- Let's record here the fact that `L ≤ N` and `M ≤ N`. I found
  -- these proofs by using `library_search` and then clicking on "Try this!".
  -- For example
  -- `have hLN : L ≤ N := by library_search`,
  have hLN : L ≤ N := le_max_left L M,
  have hMN : M ≤ N := le_max_right L M,
  -- We're going to set `n = N` in `hL` and `hM`. Again I'm thinking
  -- of these things as functions.
  specialize hL N hLN,
  specialize hM N hMN,
  -- It looks like we should be done now: everything should follow
  -- now from chasing inequalities. We need to give Lean one more hint
  -- though, because `linarith` doesn't know anything about the `abs` function;
  -- we need to know that |x|<ε/2 is the same as `-ε/2 < x ∧ x < ε/2`.
  -- This theorem is called `abs_lt` ("absolute value is less than").
  rw abs_lt at hL hM,
  -- As a challenge, can you now look at the tactic state and finish the proof
  -- on paper? Lean's `linarith` tactic can see its way through the inequality
  -- maze. Let's finish this proof and talk about `linarith` and another
  -- high-powered tactic, `ring`. 
  linarith,
end

/-

Two quick comments on some other new things in the above proof: 

1) We will be using `max` a lot in this workshop. `max A B` is
the max of `A` and `B`. `max` is a definition, not a theorem, so 
that means that there will be an API associated with it, i.e. 
a list of little theorems which make `max` possible to use.
We just saw the two important theorems which we'll be using:
`le_max_left A B : A ≤ max A B` and
`le_max-right A B : B ≤ max A B`.

There are other cool functions in the `max` API, for example
`max_le : A ≤ C → B ≤ C → max A B ≤ C`. The easiest way to 
find your way around the `max` API is to *guess* what the names
of the theorems are! For example what do you think 
`max A B < C ↔ A < C ∧ B < C` is called?
If you can't work it out, then cheat by running

```
example (A B C : ℝ) : max A B < C ↔ A < C ∧ B < C :=
begin
  library_search
end
```

2) `specialize` is a tactic which changes a function by fixing once and
for all the first inputs. For example, say `f : A → B → C → D` is a function.
Because `→` is right associative in Lean, `f` is a function which wants
an input from `A`, and then spits out a function which wants an input
from `B`, and spits out a function which wants an input from `C` and
spits out an element of `D`. So really it's just a function which takes
three inputs, one from `A`, one from `B` and one from `C`, and spits
out something in `D`. This is what computer scientists call "currying".

Now say I have `a : A` and I want this to be my first input to `f`, and I never
want to run `f` again with any other inputs from `A`. Then 

`specialize f a`

will feed `a` into `f` and then rename `f` to be the resulting new
function `B → C → D`.
-/
X → Y → Z
-- Before we go on, I need to explain two more high-powered tactics.

/-
## `linarith` and `ring`

`linarith` and `ring` are two high-powered tactics. It's important
to know their "scope".

### `ring`

Let's start with `ring`. The `ring` tactic
will prove any goal which can be deduced from the axioms of
a commutative ring (or even a commutative semiring like `ℕ`). For
example if `(x y : ℝ)` and the goal is `(x+y)^3=x^3+3*x^2*y+3*x*y^2+y^3`
then `ring` will close this goal. In the proof of `is_limit_add`
below in my solutions file, I use `ring` to prove
`a n + b n - (l + m) = (a n - l) + (b n - m)` and to prove `ε/2 + ε/2 = ε`.
Note that `ring` will get confused if it sees `λ` terms and so on, it
works up to syntactic equality. `ring` wants to see a clean statement
about elements of a ring involving only `+`, `-` and `*`. Note also that
`ring` does not look at hypotheses -- it works on the goal only.
So for example `ring` will not solve this goal directly:

```
a b c : ℝ 
ha : a = b + c
⊢ 2 * a = b + b + c + c
```

To solve this goal you need to do `rw ha` and then `ring`.

### `linarith`

`linarith` solves linear inequalities. For example it will solve this goal:

```
a b c : ℝ 
hab : a ≤ b
hbc : b < c
⊢ a ≤ c + 1
```

Note that it will not do your logic for you though. For example it will
not solve this goal:

```
a b c : ℝ 
hab : a ≤ b
hbc : a ≤ b → b < c
⊢ a ≤ c + 1
```

even though `b < c` is "obviously true because of `hab`", `linarith` can't see it.
The *one* thing it can see through is `∧` in hypotheses: it will solve this goal.

```
a b c : ℝ 
h : a ≤ b ∧ b < c
⊢ a ≤ c + 1
```

However it will not see through `∧` in goals; it will not solve this.

```
a b c : ℝ 
h : a ≤ b ∧ b < c
⊢ a ≤ c + 1 ∧ a ≤ c + 1
```

To solve this goal, use `split; linarith`. The semicolon means "apply the
next tactic to all goals created by the previous tactic".

If you're unsure whether `linarith` can see an inequality, just isolate
it as a hypothesis or goal all by itself. Then `linarith` can definitely see it.


-/

/-

## convert

While we're here, here is an explanation of one more high-powered tactic.

If your goal is `⊢ P` and you have a hypothesis `h : P'` where `P` and `P'`
only differ slightly, then `convert h'` will replace the goal with new goals asking
for justification that all the places where `P` and `P'` differ are equal.
Here's an example:


-/

example (a b : ℝ) (h : a * 2 = b + 1) : a + a = b - (-1) :=
begin
  -- rw `h` won't work because we don't have a complete match on either
  -- side of the equality.
  convert h,
  -- now two goals: `a + a = a * 2` and `b - -1 = b + 1`
  { ring },
  { ring }
end

/-

An example where things can go a bit wrong is below. Uncomment the `convert h`
line to see a failure, and then you'll understand the fix.
-/
example (a b : ℝ) (h : a * 2 = b + 1) : a + a = 1 + b :=
begin
  -- uncomment this to see something unfortunate happen:
  -- convert h,
  
  convert h using 1, -- change to 2 or more to see the unfortunate thing again
  { ring },
  { ring }
end

/-

OK it's time to actually do some mathematics! Why don't we start by
looking at what happens when we change a sequence or limit by adding a constant.
-/

lemma is_limit_add_const {a : ℕ → ℝ} {l : ℝ} (c : ℝ) (ha : is_limit a l) :
  is_limit (λ i, a i + c) (l + c) :=
begin
  sorry
end

lemma is_limit_add_const_iff {a : ℕ → ℝ} {l : ℝ} (c : ℝ) :
  is_limit a l ↔ is_limit (λ i, a i + c) (l + c) :=
begin
  sorry,
end

lemma is_limit_iff_is_limit_sub_eq_zero (a : ℕ → ℝ) (l : ℝ) :
  is_limit a l ↔ is_limit (λ i, a i - l) 0 :=
begin
  sorry,
end

/-

We now prove that if aₙ → l and bₙ → m then aₙ + bₙ → l + m.

Here is the proof that I recommend you formalise:
choose L large enough so that n ≥ L implies |aₙ - l|<ε/2
choose M large enough so that n ≥ M implies |bₙ - m|<ε/2
Now N := max M₁ M₂ works.
Some extra things you may need to know:
`pi.add_apply a b : (a + b) n = a n + b n`
`abs_add x y : |x + y| ≤ |x| + |y|`
Good luck!

-/

theorem is_limit_add {a b : ℕ → ℝ} {l m : ℝ}
  (h1 : is_limit a l) (h2 : is_limit b m) :
  is_limit (a + b) (l + m) :=
begin
  sorry,
end
#check lt_div_iff 
-- We have proved `is_limit` behaves well under `+`. If we also
-- prove that it behaves well under scalar multiplication, we can
-- deduce that it's linear. So let's do this next.

-- Helpful things:
-- `abs_pos : 0 < |a| ↔ a ≠ 0`
-- `div_pos : 0 < a → 0 < b → 0 < a / b`
-- `abs_mul x y : |x * y| = |x| * |y|`
-- `lt_div_iff' : 0 < c → (a < b / c ↔ c * a < b)`
-- I typically find these things myself with a combination of
-- the "guess the name of the lemma" game (and ctrl-space), and `library_search`

-- A hint for starting:
-- It might be worth dealing with `c = 0` as a special case. You
-- can start with 
-- `by_cases hc : c = 0`

lemma is_limit_mul_const_left {a : ℕ → ℝ} {l c : ℝ} (h : is_limit a l) :
  is_limit (λ n, c * (a n)) (c * l) :=
begin
  sorry,
end

-- This should just be a couple of lines now.
lemma is_limit_linear (a : ℕ → ℝ) (b : ℕ → ℝ) (α β c d : ℝ) 
    (ha : is_limit a α) (hb : is_limit b β) : 
    is_limit ( λ n, c * (a n) + d * (b n) ) (c * α + d * β) :=
begin
  sorry,
end


-- We need the below result to prove that product of limits is limit
-- of products.
-- Rather than using `√ε`, just choose `N` large enough such that `|a n| ≤ ε`
-- and `|b n| ≤ 1` if `n ≥ N`; this will work.

lemma is_limit_mul_eq_zero_of_is_limit_eq_zero {a : ℕ → ℝ} {b : ℕ → ℝ}
  (ha : is_limit a 0) (hb : is_limit b 0) : is_limit (a * b) 0 :=
begin
  sorry,
end

-- The limit of the product is the product of the limits.
-- If aₙ → l and bₙ → m then aₙ * bₙ → l * m.
-- Here's the proof I recommend. Start with 
-- `suffices : is_limit (λ i, (a i - l) * (b i - m) + (l * (b i - m)) + m * (a i - l)) 0,`
-- (note: this multiplies out to `a i * b i - l * m`)
-- and then prove that all three terms in the sum tend to zero.
theorem is_limit_mul (a : ℕ → ℝ) (b : ℕ → ℝ) (l m : ℝ)
  (h1 : is_limit a l) (h2 : is_limit b m) :
  is_limit (a * b) (l * m) :=
begin
  sorry,
end


-- If aₙ → l and bₙ → m, and aₙ ≤ bₙ for all n, then l ≤ m
theorem is_limit_le_of_le (a : ℕ → ℝ) (b : ℕ → ℝ)
  (l : ℝ) (m : ℝ) (hl : is_limit a l) (hm : is_limit b m) 
  (hle : ∀ n, a n ≤ b n) : l ≤ m :=
begin
  sorry,
end

-- sandwich
theorem sandwich (a b c : ℕ → ℝ)
  (l : ℝ) (ha : is_limit a l) (hc : is_limit c l) 
  (hab : ∀ n, a n ≤ b n) (hbc : ∀ n, b n ≤ c n) : is_limit b l :=
begin
  sorry,
end



-- Let's make a new definition.
definition is_bounded (a : ℕ → ℝ) := ∃ B, ∀ n, |a n| ≤ B

-- Now try this:
lemma tendsto_bounded_mul_zero {a : ℕ → ℝ} {b : ℕ → ℝ}
  (hA : is_bounded a) (hB : is_limit b 0) 
  : is_limit (a*b) 0 :=
begin
  sorry,
end

-- we can make more definitions
def is_cauchy (a : ℕ → ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, |a m - a n| < ε 

-- and of course one can go on and on and on

end xena

-- Take a look at `Part_A_limits_appendix.lean` to see some rather
-- shorter proofs! We will talk about these proofs next week. Perhaps
-- you can try and investigate what is going on, by hovering on things
-- like `tendsto`. Hint: filters. 