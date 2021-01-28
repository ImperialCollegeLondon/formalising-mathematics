/-

# Limits

Let's develop a theory of limits of sequences a₀, a₁, a₂, … of reals.
In this file we will develop it the way it is done at university.

-/

/- limits.lean

Limits of sequences.

Part of the M1P1 Lean project.

This file contains the basic definition of the limit of a sequence, and
proves basic properties about it.

It is full of comments in an attempt to make it more comprehensible to
mathematicians with little Lean experience, although by far the best
way to understand what is going on is to open the file within Lean 3.4.2
so you can check out the goal at each line -- this really helps understanding.
-/

-- The import below gives us a working copy of the real numbers ℝ,
-- and functions such as abs : ℝ → ℝ 
import data.real.basic

-- This import has addition of functions, which we need for sums of limits.
-- import algebra.pi_instances

-- This next import gives us several tactics of use to mathematicians:
-- (1) norm_num [to prove basic facts about reals like 2+2 = 4]
-- (2) ring [to prove basic algebra identities like (a+b)^2 = a^2+2ab+b^2]
-- (3) linarith [to prove basic inequalities like x > 0 -> x/2 > 0]
import tactic.linarith

--import topology.basic
-- Ken Lee wanted to import this
--import analysis.exponential

-- These lines switch Lean into "maths proof mode" -- don't worry about them.
-- Basically they tell Lean to use the axiom of choice and the
-- law of the excluded middle, two standard maths facts which we
-- assume all the time in maths, usually without comment. 

-- This imports Patrick's extension obv_ineq of linarith which solves
-- "obvious inequalities", and maybe other things too.
import tactic.linarith data.real.basic

local notation `|` x `|` := abs x

lemma zero_of_abs_lt_all (x : ℝ) (h : ∀ ε > 0, |x| < ε) : x = 0 :=
begin
  rw ← abs_eq_zero,
  apply eq_of_le_of_forall_le_of_dense (abs_nonneg x),
  intros ε ε_pos,
  exact le_of_lt (h ε ε_pos),
end

-- The next few things should be hidden
@[user_attribute]
meta def ineq_rules : user_attribute :=
{ name := `ineq_rules,
  descr := "lemmas usable to prove inequalities" }

attribute [ineq_rules] add_lt_add le_max_left le_max_right

meta def obvious_ineq := `[linarith <|> apply_rules ineq_rules]
run_cmd add_interactive [`obvious_ineq]
-- end of scary things


noncomputable theory
local attribute [instance, priority 0] classical.prop_decidable

-- Let's also put things into an M1P1 namespace so we can define
-- stuff which is already defined in mathlib without breaking anything.
namespace M1P1

-- the maths starts here.

-- We introduce the usual mathematical notation for absolute value
notation `|` x `|` := abs x

-- We model a sequence a₀, a₁, a₂,... of real numbers as a function
-- from ℕ := {0,1,2,...} to ℝ, sending n to aₙ . So in the below
-- definition of the limit of a sequence, a : ℕ → ℝ is the sequence.

-- We first formalise the definition of "aₙ → l as n → ∞"
definition is_limit (a : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, | a n - l | < ε

-- A sequence converges if and only if it has a limit. The difference
-- with this definition is that we don't specify the limit, we just
-- claim that it exists.
definition has_limit (a : ℕ → ℝ) : Prop := ∃ l : ℝ, is_limit a l

lemma tendsto_const (a : ℝ) : is_limit (λ n, a) a :=
begin
  intros ε εpos,
  use 0,
  intros n _,
  simpa using εpos
end

local attribute [simp] sub_zero

-- We will need an easy reformulation of the limit definition
lemma tendsto_iff_sub_tendsto_zero {a : ℕ → ℝ} {l : ℝ} :
  is_limit (λ n, a n - l) 0 ↔ is_limit a l :=
begin
  split ; 
  { intros h ε εpos,
    rcases h ε εpos with ⟨N, H⟩,
    use N,
    intros n hn,
    simpa using H n hn }
end

-- In the definition of a limit, the final ε can be replaced 
-- by a constant multiple of ε. We could assume this constant is positive
-- but we don't want to deal with this when applying the lemma.
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

-- We now start on the proof of the theorem that if a sequence has
-- two limits, they are equal. 

-- We're ready to prove the theorem.
theorem limits_are_unique (a : ℕ → ℝ) (l m : ℝ) (hl : is_limit a l)
(hm : is_limit a m) : l = m :=
begin
  -- Let prove |l - m| is smaller than any positive number, since that will easily imply l = m
  suffices : ∀ ε : ℝ, ε > 0 → |l - m| < ε,
    from eq_of_sub_eq_zero (zero_of_abs_lt_all _ this),
  -- Let ε be any positive number, and let's prove |l - m| < ε
  intros ε ε_pos,
  -- Because aₙ → l, there exists Nₗ such that n ≥ Nₗ → |aₙ - l| < ε/2
  cases hl (ε/2) (by obvious_ineq) with Nₗ Hₗ,
  -- Because aₙ → m, there exists Nₘ such that n ≥ Nₘ → |aₙ - m| < ε/2
  cases hm (ε/2) (by obvious_ineq) with Nₘ Hₘ,
  -- The trick is to let N be the max of Nₗ and Nₘ
  let N := max Nₗ Nₘ,
  -- Now clearly N ≥ Nₗ...
  have H₁ : Nₗ ≤ N := by obvious_ineq,
  -- ... so |a_N - l| < ε/2
  have H : | a N - l| < ε/2 := Hₗ N H₁,
  -- similarly N ≥ Nₘ...
  have H₂ : Nₘ ≤ N := by obvious_ineq,
  -- ... so |a_N - m| < ε/2 too
  have H' : | a N - m| < ε/2 := Hₘ N H₂,
  -- We now combine
  calc 
    |l - m| = |(l - a N) + (a N - m)| : by ring
        ... ≤ |l - a N| + |a N - m|   : abs_add _ _
        ... = |a N - l | + |a N - m|  : by rw abs_sub
        ... < ε/2 + ε/2               : by obvious_ineq
        ... = ε                       : by ring,
end

-- We now prove that if aₙ → l and bₙ → m then aₙ + bₙ → l + m.
theorem tendsto_add (a : ℕ → ℝ) (b : ℕ → ℝ) (l m : ℝ)
  (h1 : is_limit a l) (h2 : is_limit b m) :
  is_limit (a + b) (l + m) :=
begin
  apply tendsto_of_mul_eps,
  -- let epsilon be a positive real
  intros ε Hε,
  -- Choose large M₁ such that n ≥ M₁ implies |a n - l| < ε
  cases (h1 ε Hε) with M₁ HM₁,
  -- similarly choose M₂ for the b sequence. 
  cases (h2 ε Hε) with M₂ HM₂,
  -- let N be the max of M1 and M2
  let N := max M₁ M₂,
  -- and let's use that 
  use N,
  -- Of course N ≥ M₁ and N ≥ M₂
  have H₁ : N ≥ M₁ := by obvious_ineq,
  have H₂ : N ≥ M₂ := by obvious_ineq,
  -- Now say n ≥ N.
  intros n Hn,
  -- Then obviously n ≥ M₁...
  have Hn₁ : n ≥ M₁ := by linarith,
  -- ...so |aₙ - l| < ε
  have H3 : |a n - l| < ε := HM₁ n Hn₁,
  -- and similarly n ≥ M₂, so |bₙ - l| < ε
  have H4 : |b n - m| < ε := HM₂ n (by linarith),
  -- And now we can estimate (|aₙ + bₙ - (l + m)| < 2ε) 
                               -- First do some obvious algebra
  calc |(a + b) n - (l + m)| = |a n + b n - (l + m)| : rfl
  ...                        = |(a n - l) + (b n - m)| : by congr' 1; ring
                               -- now use the triangle inequality
  ...                        ≤ |(a n - l)| + |(b n - m)| : abs_add _ _
                               -- and our assumptions
  ...                        < ε + ε : by linarith 
                               -- and a bit more algebra
  ...                        = 2*ε : by ring
end

-- A sequence (aₙ) is *bounded* if there exists some real number B such that |aₙ| ≤ B for all n≥0.

definition has_bound (a : ℕ → ℝ) (B : ℝ) := ∀ n, |a n| ≤ B
definition is_bounded (a : ℕ → ℝ) := ∃ B, has_bound a B

-- We really have a problem with that |.| notation
-- The following lemma is obvious
lemma has_bound_const (m : ℝ): has_bound (λ n, m) $ |m|  :=
assume n, by simp

-- A convergent sequence is bounded.
open finset
theorem bounded_of_convergent (a : ℕ → ℝ) (Ha : has_limit a) : is_bounded a :=
begin
  -- let l be the limit of the sequence.
  cases Ha with l Hl,
  -- By definition, there exist some N such that n ≥ N → |aₙ - l| < 1
  cases Hl 1 (zero_lt_one) with N HN,
  -- Let X be {|a₀|, |a₁|, ... , |a_N|}...
  let X := image (abs ∘ a) (range (N + 1)),
  -- ...let's remark that |a₀| ∈ X so X ≠ ∅ while we're here...
  have H2 : |a 0| ∈ X := mem_image_of_mem _ (mem_range.2 (nat.zero_lt_succ _)),
  have H3 : X.nonempty := ⟨_, H2⟩,
  -- ...and let B₀ be the max of X.
  let B₀ := max' X H3,
  -- If n ≤ N then |aₙ| ≤ B₀.
  have HB₀ : ∀ n ≤ N, |a n| ≤ B₀ := λ n Hn, le_max' X _
    (mem_image_of_mem _ (mem_range.2 (nat.lt_succ_of_le Hn))),
  -- So now let B = max {B₀, |l| + 1}
  let B := max B₀ ( |l| + 1),
  -- and we claim this bound works, i.e. |aₙ| ≤ B for all n ∈ ℕ.
  use B,
  -- Because if n ∈ ℕ,
  intro n,
  -- then either n ≤ N or n > N.
  cases le_or_gt n N with Hle Hgt,
  { -- if n ≤ N, then |aₙ| ≤ B₀
    have h : |a n| ≤ B₀ := HB₀ n Hle,
    -- and B₀ ≤ B 
    have h2 : B₀ ≤ B := le_max_left _ _,
    -- so we're done
    linarith },
  { -- and if n > N, then |aₙ - l| < 1...
    have h : |a n - l| < 1 := HN n (le_of_lt Hgt),
    -- ...so |aₙ| < 1 + |l|...
    have h2 : |a n| < |l| + 1,
      -- todo (kmb) -- remove linarith bug workaround
      revert h,unfold abs,unfold max,split_ifs;intros;linarith {restrict_type := ℝ},
    -- ...which is ≤ B
    have h3 : |l| + 1 ≤ B := le_max_right _ _,
    -- ...so we're done in this case too
    linarith   
  }
end

-- more convenient theorem: a sequence with a limit
-- is bounded in absolute value by a positive real.
theorem bounded_pos_of_convergent (a : ℕ → ℝ) (Ha : has_limit a) :
∃ B : ℝ, B > 0 ∧ has_bound a B :=
begin
  -- We know the sequence is bounded. Say it's bounded by B₀.
  cases bounded_of_convergent a Ha with B₀ HB₀,
  -- let B = |B₀| + 1; this bound works.
  let B := |B₀| + 1,
  use B,
  -- B is obviously positive 
  split,
  { -- (because 1 > 0...
    apply lt_of_lt_of_le zero_lt_one,
    show 1 ≤ |B₀| + 1,
    apply le_add_of_nonneg_left,
    -- ... and |B₀| ≥ 0)
    exact abs_nonneg _,
    use [0, 1], simp,
  },
  -- so it suffices to prove B is a bound.
  -- If n is a natural
  intro n,
  -- then |aₙ| ≤ B₀
  apply le_trans (HB₀ n),
  -- so it suffices to show B₀ ≤ |B₀| + 1
  show B₀ ≤ |B₀| + 1,
  -- which is obvious.
  apply le_trans (le_abs_self B₀),
  simp [zero_le_one],
end

lemma tendsto_bounded_mul_zero {a : ℕ → ℝ} {b : ℕ → ℝ} {A : ℝ} (Apos : A > 0)
  (hA : has_bound a A) (hB : is_limit b 0) 
  : is_limit (a*b) 0 :=
begin
  -- Let's apply our variant of the definition of limits where the final 
  -- ε gets multiplied by some constant to be determined
  apply tendsto_of_mul_eps,
  -- Let ε be any positive number
  intros ε εpos,
  -- by assumption hB, we get some N such that 
  -- ∀ (n : ℕ), n ≥ N → |b n| < ε
  cases hB ε εpos with N H,
  simp at H,
  -- Let's use that N
  use N,
  -- And compute for any n ≥ N
  intros n nN,
  calc 
  |(a * b) n - 0| = |a n * b n|    : by simp
              ... = |a n| * |b n|  : abs_mul _ _
              ... ≤ A*|b n|        : mul_le_mul_of_nonneg_right (hA n) (abs_nonneg _)
              ... < A*ε            : mul_lt_mul_of_pos_left (H n nN) Apos
end



-- The limit of the product is the product of the limits.
-- If aₙ → l and bₙ → m then aₙ * bₙ → l * m.
theorem tendsto_mul (a : ℕ → ℝ) (b : ℕ → ℝ) (l m : ℝ)
  (h1 : is_limit a l) (h2 : is_limit b m) :
  is_limit (a * b) (l * m) :=
begin
  -- We apply the difference criterion so we need to prove a*b - l*m goes to zero
  rw ←tendsto_iff_sub_tendsto_zero,

  -- The key idea is to introduce (a_n - l) and (b_n - m) in this difference
  have key : (λ n, (a*b) n - l*m) = (λ n, (a n)*(b n - m) + m*(a n - l)),
    simp, ext, ring,
  rw key,
  
  -- By addition of limit, it then suffices to prove a_n * (b_n - m) and m*(a_n - l)
  -- both go to zero
  suffices : is_limit (λ n, a n * (b n - m)) 0 ∧ is_limit (λ n, m * (a n - l)) 0,
  { rw [show (0 : ℝ) = 0 + 0, by simp],
    exact tendsto_add _ _ _ _ this.left this.right},
  -- Let's tacke one after the other
  split,
  { -- Since a is convergent, it's bounded by some positive A
    rcases bounded_pos_of_convergent a ⟨l, h1⟩ with ⟨A, A_pos, hA⟩,
    -- We can reformulate the b convergence assumption as b_n - m goes to zero.
    have limb : is_limit (λ n, b n - m) 0,
     from tendsto_iff_sub_tendsto_zero.2 h2,
    -- So we can conclude using our lemma about product of a bounded sequence and a
    -- sequence converging to zero
    exact tendsto_bounded_mul_zero A_pos hA limb },
  { -- It remains to prove m * (a_n - l) goes to zero
    -- If m = 0 this is obvious.
    by_cases Hm : m = 0,
    { simp [Hm, tendsto_const] },
    -- Otherwise we follow the same strategy as above.
    { -- We reformulate our convergence assumption on a as a_n - l goes to zero
      have lima : is_limit (λ n, a n - l) 0, 
        from tendsto_iff_sub_tendsto_zero.2 h1,
      -- and conclude using the same lemma
      exact tendsto_bounded_mul_zero (abs_pos.2 Hm) (has_bound_const m) lima } }
end

-- If aₙ → l and bₙ → m, and aₙ ≤ bₙ for all n, then l ≤ m
theorem tendsto_le_of_le (a : ℕ → ℝ) (b : ℕ → ℝ)
  (l : ℝ) (m : ℝ) (hl : is_limit a l) (hm : is_limit b m) 
  (hle : ∀ n, a n ≤ b n) : l ≤ m :=
begin
  -- Assume for a contradiction that m < l
  apply le_of_not_lt,
  intro hlt,
  -- Let ε be (l - m) / 2...
  let ε := (l - m) /2,
  -- ...and note that it's positive
  have Hε : ε > 0 := show (l - m) / 2 > 0 , by linarith,
  -- Choose Na s.t.  |aₙ - l| < ε for n ≥ Na
  cases hl ε Hε with Na HNa,
  have Hε : ε > 0 := show (l - m) / 2 > 0 , by linarith,
  -- Choose Nb s.t.  |bₙ - m| < ε for n ≥ Nb
  cases hm ε Hε with Nb HNb,
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
  -- This is probably a contradiction.
  have Hε : ε = (l - m) / 2 := rfl,
  revert Hl' Hm',
  unfold abs,unfold max,split_ifs;intros;linarith
end

lemma lim_times_const (a : ℕ → ℝ) (l c : ℝ) (h : is_limit a l) :
  is_limit (λ n, c * (a n)) (c * l) :=
begin
  by_cases hc : c = 0,
  { subst hc,
    convert tendsto_const 0,
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

/- Lemma
If $\lim_{n \to \infty} a_n = \alpha$ and $\lim_{n \to \infty} b_n = \beta$
and $c$ is a constant, then 
$\lim_{n \to \infty} ( c * a_n + c * b_n) = c \alpha + c \beta$
-/
lemma lim_linear (a : ℕ → ℝ) (b : ℕ → ℝ) (α β c d : ℝ) 
    (ha : is_limit a α) (hb : is_limit b β) : 
    is_limit ( λ n, c * (a n) + d * (b n) ) (c * α + d * β) :=
begin
    apply tendsto_add,
    exact lim_times_const a α c ha,
    exact lim_times_const b β d hb,
    done
end

end M1P1
