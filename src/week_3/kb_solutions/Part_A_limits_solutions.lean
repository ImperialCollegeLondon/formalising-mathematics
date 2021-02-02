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
in the usual way. We then develop the basic theory of limits.

## Main theorems

* `lemma is_limit_const (a : ℝ) : is_limit (λ n, a) a`
* `theorem is_limit_subsingleton {a : ℕ → ℝ} {l m : ℝ}
     (hl : is_limit a l) (hm : is_limit a m) : l = m`

## What to teach?

squiggly brackets

`convert`
`ring`
`linarith`
`norm_num`

/-
API for `max`: le_max_left, le_max_right

API for `abs`: abs_add and abs_lt
-/


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
It is also a function. Remember that in Lean's dependent type theory, 
we have types and terms, and every term has a unique type. Types and terms
are used to unify two completely different things: sets and elements,
and theorems and proofs. Let's take a close look at what exactly this
function `is_limit_subsingleton` does.

`is_limit_subsingleton` is a function with five inputs. The first input
is a sequence `a : ℕ → ℝ`. The second and third are real numbers `l` and `m`.
The fourth is a proof that `a(n)` tends to `l`, and the fifth is a proof that
`a(n)` tends to `m`. The output of the function is a proof that `l = m`. This
is how Lean thinks about proofs internally, and it's important that you
internalise this point of view because you will be evaluating functions
quite a bit today. If you still think it's a bit weird having proofs as inputs
and outputs to functions, just think of a true-false statement (e.g. a theorem
statement) as being a set, and the elements of that set are the proofs of
the theorem. For example `2 + 2 = 5` is a set with no elements, because
there are no proofs of this theorem (assuming that mathematics is consistent).

Now if you think about these inputs carefully, you may realised that something
a bit fishy is going on here. Usually you would think of a function with five inputs
as a function from `A × B × C × D × E` to `X`, where `A`, `B`, `C`, `D` and `E`
are all sets. But the fourth input to `is_limit_singleton` is an element
of the set of proofs of `is_limit a l`, the statement that `a(n)` tends to `l`,
and in particular this set itself *depends on the first three inputs*. 
The set `D` itself is a function of `A`, `B` and `C`! The same is true
for the set `E`. This slightly bizarre set-up has the even more bizarre
consequence that actually, 


-/
theorem is_limit_subsingleton {a : ℕ → ℝ} {l m : ℝ} (hl : is_limit a l)
(hm : is_limit a m) : l = m :=
begin
  by_contra h,
  -- TODO : next three lines need to be taught
  wlog : l < m,
  have := lt_trichotomy l m,
    tauto,
  set ε := m - l with hε,
  cases hl (ε/2) (by linarith) with L hL,
  cases hm (ε/2) (by linarith) with M hM,
  set N := max L M with hN,
  have hLN : L ≤ N := le_max_left L M,
  have hMN : M ≤ N := le_max_right L M,
  specialize hL N hLN,
  specialize hM N hMN,
  rw abs_lt at hL hM,
  linarith,
end

-- THIS IS FOR THE FINAL VERSION
-- comment on what a + b means

-- We now prove that if aₙ → l and bₙ → m then aₙ + bₙ → l + m.
-- Maths proof: choose M₁ large enough so that n ≥ M₁ implies |aₙ - l|<ε/2
-- Maths proof: choose M₂ large enough so that n ≥ M₂ implies |bₙ - m|<ε/2
-- Now N := max M₁ M₂ works
theorem is_limit_add {a b : ℕ → ℝ} {l m : ℝ}
  (h1 : is_limit a l) (h2 : is_limit b m) :
  is_limit (a + b) (l + m) :=
begin
  -- let epsilon be a positive real
  intros ε Hε,
  -- Choose large L such that n ≥ L implies |a n - l| < ε
  cases (h1 (ε/2) (by linarith)) with L HL,
  -- similarly choose M for the b sequence. 
  cases (h2 (ε/2) (by linarith)) with M HM,
  -- let N be the max of M1 and M2
  set N := max L M with hN,
  -- and let's use that 
  use N,
  -- Of course N ≥ L and N ≥ M
  have HLN : N ≥ L := le_max_left _ _,
  have HMN : N ≥ M := le_max_right _ _,
  -- Now say n ≥ N.
  intros n Hn,
  -- Then obviously n ≥ L...
  have HnL : n ≥ L := by linarith,
  -- ...so |aₙ - l| < ε/2
  have H3 : |a n - l| < ε/2 := HL n HnL,
  -- and similarly n ≥ M, so |bₙ - l| < ε/2
  have H4 : |b n - m| < ε/2 := HM n (by linarith),
  -- And now we can show (|aₙ + bₙ - (l + m)| < ε), finishing the proof. 
                               -- First do some obvious algebra
  calc |(a + b) n - (l + m)| = |a n + b n - (l + m)| : rfl
  ...                        = |(a n - l) + (b n - m)| : by ring
                               -- now use the triangle inequality
  ...                        ≤ |(a n - l)| + |(b n - m)| : abs_add _ _
                               -- and our assumptions
  ...                        < ε/2 + ε/2 : by linarith 
                               -- and a bit more algebra
  ...                        = ε : by ring
end

-- this needs to be in because it's my proof for is_limit_mul
lemma is_limit_mul_const_left {a : ℕ → ℝ} {l c : ℝ} (h : is_limit a l) :
  is_limit (λ n, c * (a n)) (c * l) :=
begin
  by_cases hc : c = 0,
  { subst hc,
    convert is_limit_const 0,
    { ext, simp },
    { simp } },
  { have hc' : 0 < |c| := by simp [hc],
    intros ε hε,
    have hεc : 0 < ε / |c| := div_pos hε hc',
    specialize h (ε/|c|) hεc,
    cases h with N hN,
    use N,
    intros n hn,
    specialize hN n hn,
    dsimp only,
    rw [← mul_sub, abs_mul],
    rw ← lt_div_iff' hc',
    exact hN }
end

lemma is_limit_add_const (a : ℕ → ℝ) (l c : ℝ) (ha : is_limit a l) :
  is_limit (λ i, a i + c) (l + c) :=
begin
  intros ε hε,
  -- goal now contains an evaluated lambda
  dsimp,
  cases ha ε hε with N hN,
  use N,
  intros n hn,
  convert hN n hn using 2,
  ring,
end

lemma is_limit_add_const_iff (a : ℕ → ℝ) (l c : ℝ) :
  is_limit a l ↔ is_limit (λ i, a i + c) (l + c) :=
begin
  split,
  { apply is_limit_add_const },
  { intro h,
    convert is_limit_add_const (λ n, a n + c) (l + c) (-c) h,
    { ext, ring },
    { ring }
  }
end

lemma is_limit_iff_is_limit_sub_eq_zero (a : ℕ → ℝ) (l : ℝ) :
  is_limit a l ↔ is_limit (λ i, a i - l) 0 :=
begin
  convert is_limit_add_const_iff a l (-l),
  { ext, ring },
  { ring }
end

lemma is_limit_mul_eq_zero_of_is_limit_eq_zero {a : ℕ → ℝ} {b : ℕ → ℝ}
  (ha : is_limit a 0) (hb : is_limit b 0) : is_limit (a * b) 0 :=
begin
  intros ε hε,
  -- could use √ε for each but much easier to use ε and 1
  cases ha ε hε with A hA,
  cases hb 1 (by linarith) with B hB,
  set N := max A B with hN,
  use N,
  intros n hn,
  have hAN : A ≤ N := le_max_left A B,
  have hBN : B ≤ N := le_max_right A B,
  specialize hA n (by linarith),
  specialize hB n (by linarith),
  rw [sub_zero] at ⊢ hA hB,
  rw pi.mul_apply,
  rw abs_mul,
  convert mul_lt_mul'' hA hB _ _, simp,
  all_goals {apply abs_nonneg},
end

-- The limit of the product is the product of the limits.
-- If aₙ → l and bₙ → m then aₙ * bₙ → l * m.
theorem it_limit_mul (a : ℕ → ℝ) (b : ℕ → ℝ) (l m : ℝ)
  (h1 : is_limit a l) (h2 : is_limit b m) :
  is_limit (a * b) (l * m) :=
begin
  suffices : is_limit (λ i, (a i - l) * (b i - m) + (l * (b i - m)) + m * (a i - l)) 0,
  { rw is_limit_iff_is_limit_sub_eq_zero,
    convert this,
    ext,
    rw pi.mul_apply,
    ring },
  have h1 : is_limit (λ i, a i - l) 0,
  { rwa is_limit_iff_is_limit_sub_eq_zero at h1 },
  have h2 : is_limit (λ i, b i - m) 0,
  { rwa is_limit_iff_is_limit_sub_eq_zero at h2 },
  have h3 : is_limit (λ i, (a i - l) * (b i - m)) 0,
  { apply is_limit_mul_eq_zero_of_is_limit_eq_zero h1 h2 },
  have h4 : is_limit (λ i, l * (b i - m)) 0,
  { convert is_limit_mul_const_left h2,
    ring },
  have h5 : is_limit (λ i, m * (a i - l)) 0,
  { convert is_limit_mul_const_left h1,
    ring },
  convert is_limit_add (_ : is_limit _ 0) h5, norm_num,
  convert is_limit_add h3 h4,
  norm_num,
end


lemma is_limit_linear (a : ℕ → ℝ) (b : ℕ → ℝ) (α β c d : ℝ) 
    (ha : is_limit a α) (hb : is_limit b β) : 
    is_limit ( λ n, c * (a n) + d * (b n) ) (c * α + d * β) :=
begin
  apply is_limit_add,
  { apply is_limit_mul_const_left ha },
  { apply is_limit_mul_const_left hb },
end




-- not hard
-- If aₙ → l and bₙ → m, and aₙ ≤ bₙ for all n, then l ≤ m
theorem tendsto_le_of_le (a : ℕ → ℝ) (b : ℕ → ℝ)
  (l : ℝ) (m : ℝ) (hl : is_limit a l) (hm : is_limit b m) 
  (hle : ∀ n, a n ≤ b n) : l ≤ m :=
begin
  -- Assume for a contradiction that m < l
  apply le_of_not_lt,
  intro hlt,
  -- Let ε be (l - m) / 2...
  set ε := (l - m) /2 with hεlm,
  have hε : 0 < ε := by linarith,
  cases hl ε hε with Na HNa,
  -- Choose Nb s.t.  |bₙ - m| < ε for n ≥ Nb
  cases hm ε hε with Nb HNb,
  -- let N be the max of Na and Nb...
  let N := max Na Nb,
  -- ...and note N ≥ Na and N ≥ Nb,
  have HNa' : Na ≤ N := le_max_left _ _,
  have HNb' : Nb ≤ N := le_max_right _ _,
  -- ... so |a_N - l| < ε and |b_N - m| < ε
  have Hl' : |a N - l| < ε := HNa N HNa',
  have Hm' : |b N - m| < ε := HNb N HNb',
  -- ... and also a_N ≤ b_N.
  have HN : a N ≤ b N := hle N,
  rw abs_lt at Hl' Hm',
  linarith,
end

-- exercise
lemma tendsto_of_mul_eps (a : ℕ → ℝ) (l : ℝ) (A : ℝ)
  (h : ∀ ε > 0, ∃ N, ∀ n ≥ N, | a n - l | < A*ε) : is_limit a l :=
begin
  -- Let ε be any positive number
  intros ε εpos,
  -- A is either non positive or positive
  cases le_or_gt A 0 with Anonpos Apos,
  { -- If A is non positive then our assumed bound quickly
    -- gives a contradiction. 
    exfalso,
    -- Indeed we can apply our assumption to ε = 1 to get N such that
    -- ∀ (n : ℕ), n ≥ N → |a n - l| < A * 1 
    rcases h 1 (by linarith) with ⟨N, H⟩,
    -- in particular this holds when n = N
    specialize H N (by linarith),
    -- but |a N - l| ≥ 0 so we get a contradiction
    have : |a N - l| ≥ 0, from abs_nonneg _,
    linarith },
  { -- Now assume A is positive. Our assumption h gives N such that
    -- ∀ n ≥ N, |a n - l| < A * (ε / A)
    rcases h (ε/A) (div_pos εpos Apos) with ⟨N, H⟩,
    -- we can simplify that A * (ε / A) and we are done.
    rw mul_div_cancel' _ (ne_of_gt Apos) at H,
    tauto }
end

definition is_bounded (a : ℕ → ℝ) := ∃ B, ∀ n, |a n| ≤ B

-- nice exercise
lemma tendsto_bounded_mul_zero {a : ℕ → ℝ} {b : ℕ → ℝ}
  (hA : is_bounded a) (hB : is_limit b 0) 
  : is_limit (a*b) 0 :=
begin
  cases hA with A hA,
  have hAnonneg : 0 ≤ A,
  { refine le_trans _ (hA 0),
    apply abs_nonneg,
  },
  -- A = 0 is a special case
  by_cases hA0 : A = 0,
  { -- if A = 0 then the sequence is 0
    subst hA0,
    have hA2 : ∀ n, a n = 0,
    { intro n,
      specialize hA n,
      have h := abs_nonneg (a n),
      rw ← abs_eq_zero,
      linarith },
    convert is_limit_const 0,
    ext n,
    rw pi.mul_apply,
    rw hA2,
    simp },  
  have hApos : 0 < A,
  exact (ne.symm hA0).le_iff_lt.mp hAnonneg, -- thanks `library_search`
  intros ε εpos,
  -- by assumption hB, we get some N such that 
  -- ∀ (n : ℕ), n ≥ N → |b n| < ε
  cases hB (ε/A) (div_pos εpos hApos) with N hN,
  simp_rw [sub_zero] at hN,
  -- Let's use that N
  use N,
  -- And compute for any n ≥ N
  intros n hn,
  calc 
  |(a * b) n - 0| = |a n * b n|    : by simp
              ... = |a n| * |b n|  : abs_mul _ _
              ... ≤ A*|b n|        : mul_le_mul_of_nonneg_right (hA n) (abs_nonneg _)
              ... < A*(ε/A)        : mul_lt_mul_of_pos_left (hN n hn) hApos
              ... = ε              : mul_div_cancel' ε hA0
end




-- sandwich
theorem sandwich (a b c : ℕ → ℝ)
  (l : ℝ) (ha : is_limit a l) (hc : is_limit c l) 
  (hab : ∀ n, a n ≤ b n) (hbc : ∀ n, b n ≤ c n) : is_limit b l :=
begin
  intros ε hε,
  cases ha ε hε with A hA,
  cases hc ε hε with C hC,
  set N := max A C with hN,
  use N,
  intros n hn,
  rw hN at hn,
  replace hn := max_le_iff.1 hn,
  specialize hA n (by linarith),
  specialize hC n (by linarith),
  specialize hab n,
  specialize hbc n,
  rw abs_lt at *,
  split;
  linarith,
end


-- idea
def is_cauchy (a : ℕ → ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, |a m - a n| < ε 

-- and off you go

end xena
