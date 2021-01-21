-- We import all of Lean's standard tactics
import tactic

/-!
# Logic

We will develop the basic theory of following five basic logical symbols

* `→` ("implies" -- type with `\l`)
* `¬` ("not" -- type with `\not` or `\n`)
* `∧` ("and" -- type with `\and` or `\an`)
* `↔` ("iff" -- type with `\iff` or `\lr`)
* `∨` ("or" -- type with `\or` or `\v`

# Tactics you will need to know

* `intro`
* `exact`
* `apply`
* `rw`
* `cases`
* `split`
* `left`
* `right`

See `README.md` in `src/week_1` for an explanation of what these
tactics do.

Note that there are plenty of other tactics, and indeed once you've
"got the hang of it" you might want to try tactics such as `cc`, 
`tauto` and its variant `tauto!`, `finish`, and `library_search`.

# What to do

The `example`s are to demonstrate things to you. They sometimes
use tactics you don't know. You can look at them but you don't
need to touch them. 

The `theorem`s and `lemma`s are things which have no proof. You need to change
the `sorry`s into proofs which Lean will accept.

This paragraph is a comment, by the way. One-line comments
are preceded with `--`.
-/

-- We work in a "namespace". All this means is that whenever it
-- looks like we've defined a new theorem called `id`, its full
-- name is `xena.id`. Which is good because `id` is already
-- defined in Lean.
namespace xena

-- Throughout this namespace, P Q and R will be arbitrary (variable)
-- true-false statements.
variables (P Q R : Prop)

/-!
## implies (→)

To prove the theorems in this section, you will need to know about
the tactics `intro`, `apply` and `exact`. You might also like
the `assumption` tactic.
-/

/-- Every proposition implies itself. -/
theorem id : P → P :=
begin
  -- let hP be a proof of P
  intro hP,
  -- then hP is a proof of P!
  exact hP
end

/-
Note that → isn't associative!
Try working out `false → (false → false) and (false → false) → false
-/

example : (false → (false → false)) ↔ true := by simp
example : ((false → false) → false) ↔ false := by simp

-- in Lean, `P → Q → R` is _defined_ to mean `P → (Q → R)`
-- Here's a proof of what I just said.
example : (P → Q → R) ↔ (P → (Q → R)) :=
begin
  -- look at the goal!
  refl -- true because ↔ is reflexive
end

theorem imp_intro : P → Q → P :=
begin
  -- remember that by definition the goal is P → (Q → P),
  -- so it's P implies something, so let's assume 
  -- that P is true and call this hypothesis hP.
  intro hP,
  -- Now we have to prove that Q implies P, so let's
  -- assume that Q is true, and let's call this hypothesis hQ
  intro hQ,
  -- We now have to prove that P is true.
  -- But this is exactly our hypothesis hP.
  exact hP,
end

/-- If we know `P`, and we also know `P → Q`, we can deduce `Q`. -/
lemma modus_ponens : P → (P → Q) → Q :=
begin
  -- remember this means "P implies that ((P implies Q) implies Q)"
  -- so let's assume P is true
  intro hP,
  -- and let's assume hypothesis hPQ, that P implies Q
  intro hPQ,
  -- now `hPQ` says `P → Q` and we're trying to prove `Q`!
  -- So by applying the hypothesis `hPQ`, we can reduce
  -- this puzzle to proving `P`.
  apply hPQ,
  -- Now we have to prove `P`. But this is just an assumption
  exact hP, -- or `assumption`
end

/-- implication is transitive -/
lemma imp_trans : (P → Q) → (Q → R) → (P → R) :=
begin
  -- intros will let you intro many things at once
  intros hPQ hQR hP,
  -- The goal is now `⊢ R`, and `hQR : Q → R` so `apply hQR` reduces the goal to `Q`
  apply hQR,
  -- similarly `apply hPQ` reduces the goal to `P`.
  apply hPQ,
  -- We are kind of proving this result backwards! We already have
  -- a proof of P. 
  exact hP
end

-- This one is a "relative modus ponens" -- in the
-- presence of P, if Q -> R and Q then R.
lemma forall_imp : (P → Q → R) → (P → Q) → (P → R) :=
begin
  -- Let `hPQR` be the hypothesis that `P → Q → R`. 
  intro hPQR,
  -- We now need to prove that `(P → Q)` implies something.
  -- So let `hPQ` be hypothesis that `P → Q`
  intro hPQ,
  -- We now need to prove that `P` implies something, so 
  -- let `hP` be the hypothesis that `P` is true.
  intro hP,
  -- We now have to prove `R`.
  -- We know the hypothesis `hPQR : P → (Q → R)`.
  -- If you think about this, it's the same as `(P ∧ Q) → R`
  -- So perhaps it's not surprising that after
  apply hPQR,
    -- we now have two goals!
    -- The first goal is just to prove P, and this is an assumption
    exact hP,
  -- The number of goals is just one again.
  -- the remaining goal is to prove `Q`. 
  -- But recall that `hPQ` is the hypothesis that `P` implies `Q`
  -- so by applying it,
  apply hPQ,
  -- we change our goal to proving `P`. And this is a hypothesis
  exact hP,
end

/-

### not

`not P`, with notation `¬ P`, is *defined* to mean `P → false` in Lean,
i.e., the proposition that P implies false. You can easily check with
a truth table that P → false and ¬ P are equivalent.

We develop a basic interface for `¬`.
-/


-- I'll prove this one for you
theorem not_def : ¬ P ↔ (P → false) :=
begin
  -- true by definition
  refl
end

theorem not_not_intro : P → ¬ (¬ P) :=
begin
  intro hP,
  -- You can use `rw not_def` to change `¬ X` into `X → false`. 
  rw not_def, rw not_def, -- but it's not necessary really,
  intro hnP,
  apply hnP,
  exact hP,
end

-- Here is a funny alternative proof! Can you work out how it works?
example : P → ¬ (¬ P) :=
begin
  apply modus_ponens,
end

-- Here is a proof which does not use tactics at all, but uses lambda calculus.
-- It is called a "term mode" proof. We will not be discussing term mode
-- much in this course. It is a cool way to do basic logic proofs, but
-- it does not scale well in practice.
example : P → ¬ (¬ P) :=
λ hP hnP, hnP hP

-- This is "modus tollens". Some mathematicians think of it as
-- "proof by contradiction".
theorem modus_tollens : (P → Q) → (¬ Q → ¬ P) :=
begin
  -- this is (P → Q) → (Q → false) → (P → false) so we can just...
  apply imp_trans,
end

-- This one cannot be proved using constructive mathematics!
-- You _have_ to use a tactic like `by_contra` (or, if you're happy
-- to cheat, the full "truth table" tactic `tauto!`.
-- Try it without using these, and you'll get stuck!
theorem double_negation_elimination : ¬ (¬ P) → P :=
begin
  intro hnnP,
  by_contra h,
  -- hnnP is ¬ P → false, and the goal is ⊢ false, so we can do this
  apply hnnP,
  exact h,
end

/-!

### and

The hypothesis `hPaQ : P ∧ Q` in Lean, is equivalent to
hypotheses `hP : P` and `hQ : Q`. 

If you have `hPaQ` as a hypothesis, and you want to get to
`hP` and `hQ`, you can use the `cases` tactic.

If you have `⊢ P ∧ Q` as a goal, and want to turn the goal
into two goals `⊢ P` and `⊢ Q`, then use the `split` tactic.

Note that after `split` it's good etiquette to use braces
e.g.

example (hP : P) (hQ : Q) : P ∧ Q :=
begin
  split,
  { exact hP },
  { exact hQ }
end

but for this sort of stuff I think principled indentation
is OK

```
example (hP : P) (hQ : Q) : P ∧ Q :=
begin
  split,
    exact hP,
  exact hQ
end
```

-/

theorem and.elim_left : P ∧ Q → P :=
begin
  intro hPaQ,
  cases hPaQ with hP hQ,
  exact hP,
end

theorem and.elim_right : P ∧ Q → Q :=
begin
  intro hPaQ,
  -- here's a shortcut
  exact hPaQ.2, -- if `h : P ∧ Q` then `h.1 : P` and `h.2 : Q`
end

-- fancy term mode proof
example : P ∧ Q → Q := λ hPaQ, hPaQ.2

theorem and.intro : P → Q → P ∧ Q :=
begin
  intros hP hQ,
  split,
  { assumption },
  { assumption }
end

/-- the eliminator for `∧` -/ 
theorem and.elim : P ∧ Q → (P → Q → R) → R :=
begin
  -- `rintro` does `intro` and `cases` in one go
  rintro ⟨hP, hQ⟩ hPQR,
  -- hPQR is a function, so we can give it some inputs
  exact hPQR hP hQ,
end

/-- The recursor for `∧` -/
theorem and.rec : (P → Q → R) → P ∧ Q → R :=
begin
  rintro hPQR ⟨hP, hQ⟩,
  exact hPQR hP hQ,
end

/-- `∧` is symmetric -/
theorem and.symm : P ∧ Q → Q ∧ P :=
begin
  -- see how quickly we can do this using ⟨_, _⟩
  rintro ⟨hP, hQ⟩,
  exact ⟨hQ, hP⟩
end

-- term mode proof
example : P ∧ Q → Q ∧ P :=
λ ⟨hP, hQ⟩, ⟨hQ, hP⟩

/-- `∧` is transitive -/
theorem and.trans : (P ∧ Q) → (Q ∧ R) → (P ∧ R) :=
begin
  rintro ⟨hP, hQ⟩ ⟨hQ', hR⟩,
  exact ⟨hP, hR⟩,
end

/-
Recall that the convention for the implies sign →
is that it is _right associative_, by which
I mean that `P → Q → R` means `P → (Q → R)` by definition.
Now note that if `P` implies `Q → R`
then this means that `P` and `Q` together, imply `R`,
so `P → Q → R` is logically equivalent to `(P ∧ Q) → R`.

We proved that `P → Q → R` implied `(P ∧ Q) → R`; this was `and.rec`.
Let's go the other way.
-/

lemma imp_imp_of_and_imp : ((P ∧ Q) → R) → (P → Q → R) :=
begin
  intros h hP hQ,
  exact h ⟨hP, hQ⟩
end


/-!

### iff

The basic theory of `iff`.

In Lean, to prove `P ∧ Q` you have to prove `P` and `Q`.
Similarly, to prove `P ↔ Q` in Lean, you have to prove `P → Q`
and `Q → P`. Just like `∧`, you can uses `cases h` if you have
a hypothesis `h : P ↔ Q`, and `split` if you have a goal `⊢ P ↔ Q`.
-/

/-- `P ↔ P` is true for all propositions `P`, i.e. `↔` is reflexive. -/
theorem iff.refl : P ↔ P :=
begin
  split,
  -- recall that we already proved `id : P → P`
  { apply id },
  { apply id }
end

-- If you get stuck, there is always the "truth table" tactic `tauto!`
example : P ↔ P :=
begin
  tauto!, -- the "truth table" tactic.
end

-- refl tactic also works
example : P ↔ P :=
begin
  refl -- `refl` knows that `=` and `↔` are reflexive.
end

/-- `↔` is symmetric -/
theorem iff.symm : (P ↔ Q) → (Q ↔ P) :=
begin
  intro h,
  /-
  h: P ↔ Q
  ⊢ Q ↔ P
  -/
  rw h,
  -- This changes the goal to `Q ↔ Q`, which is automatically closed by `refl`
  -- because `rw` tries a cheeky `refl` after every invocation, just to see
  -- if it closes the goal
end

-- show-off term mode proof
example : (P ↔ Q) → (Q ↔ P) :=
λ ⟨hPQ, hQP⟩, ⟨hQP, hPQ⟩

/-- `↔` is commutative -/
theorem iff.comm : (P ↔ Q) ↔ (Q ↔ P) :=
begin
  split,
  { apply iff.symm },
  { apply iff.symm }
end

-- without rw or cc this is painful!
/-- `↔` is transitive -/
theorem iff.trans :  (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
  intros hPQ hQR,
  -- ⊢ P ↔ R
  rw hPQ,
  -- ⊢ Q ↔ R
  exact hQR,
end

-- This can be done constructively, but it's hard. You'll need to know
-- about the `have` tactic to do it. Alternatively the truth table
-- tactic `tauto!` will do it.
theorem iff.boss : ¬ (P ↔ ¬ P) :=
begin
  rintro ⟨h1, h2⟩,
  have hnP : ¬ P,
  { intro hP,
    exact h1 hP hP,
  },
  have hP : P := h2 hnP,
  exact hnP hP,
end

-- Now we have iff we can go back to and.

/-!
### ↔ and ∧
-/

/-- `∧` is commutative -/
theorem and.comm : P ∧ Q ↔ Q ∧ P :=
begin
  split; -- semicolon means "apply next tactic to all goals generated by this one"
  apply and.symm,
end

-- fancy term-mode proof
example : P ∧ Q ↔ Q ∧ P :=
⟨and.symm _ _, and.symm _ _⟩

-- Note that ∧ is "right associative" in Lean, which means
-- that `P ∧ Q ∧ R` is _defined to mean_ `P ∧ (Q ∧ R)`.
-- Associativity can hence be written like this:
/-- `∧` is associative -/
theorem and_assoc : ((P ∧ Q) ∧ R) ↔ (P ∧ Q ∧ R) :=
begin
  split,
  { rintro ⟨⟨hP, hQ⟩, hR⟩,
    exact ⟨hP, hQ, hR⟩ },
  { rintro ⟨hP, hQ, hR⟩,
    exact ⟨⟨hP, hQ⟩, hR⟩ },
end



/-!

## Or

`P ∨ Q` is true when at least one of `P` and `Q` are true.
Here is how to work with `∨` in Lean.

If you have a hypothesis `hPoQ : P ∨ Q` then you 
can break into the two cases `hP : P` and `hQ : Q` using
`cases hPoQ with hP hQ`

If you have a _goal_ of the form `⊢ P ∨ Q` then you
need to decide whether you're going to prove `P` or `Q`.
If you want to prove `P` then use the `left` tactic,
and if you want to prove `Q` then use the `right` tactic.

-/

-- recall that P, Q, R are Propositions. We'll need S for this one.
variable (S : Prop)

-- You will need to use the `left `tactic for this one.
theorem or.intro_left : P → P ∨ Q :=
begin
  intro P, 
  left,
  -- `assumption` means `exact <choose the correct hypothesis>`
  assumption,
end

theorem or.intro_right : Q → P ∨ Q :=
begin
  intro Q,
  right,
  assumption,
end

/-- the eliminator for `∨`. -/
theorem or.elim : P ∨ Q → (P → R) → (Q → R) → R :=
begin
  intros hPoQ hPR hQR,
  cases hPoQ with hP hQ,
  { exact hPR hP },
  { exact hQR hQ }
end

/-- `∨` is symmetric -/
theorem or.symm : P ∨ Q → Q ∨ P :=
begin
  intro hPoQ,
  cases hPoQ with hP hQ,
  { right, assumption },
  { left, assumption }
end

/-- `∨` is commutative -/
theorem or.comm : P ∨ Q ↔ Q ∨ P :=
begin
  split; -- note semicolon
  apply or.symm,
end

/-- `∨` is associative -/
theorem or.assoc : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R :=
begin
  split,
  { -- rintro can do intro+cases in one go
    rintro ((hP | hQ) | hR),
    { left, assumption },
    { right, left, assumption },
    { right, right, assumption } },
  { rintro (hP | hQ | hR),
    { left, left, assumption },
    { left, right, assumption },
    { right, assumption } }
end

/-!
### More about → and ∨
-/

theorem or.imp : (P → R) → (Q → S) → P ∨ Q → R ∨ S :=
begin
  rintro hPR hQS (hP | hQ),
  { left, exact hPR hP },
  { right, exact hQS hQ }
end

theorem or.imp_left : (P → Q) → P ∨ R → Q ∨ R :=
begin
  rintro hPQ (hP | hR),
  { left, exact hPQ hP },
  { right, assumption },
end

theorem or.imp_right : (P → Q) → R ∨ P → R ∨ Q :=
begin
  -- reduce to previous lemma
  rw or.comm R,
  rw or.comm R,
  apply or.imp_left,
end

theorem or.left_comm : P ∨ Q ∨ R ↔ Q ∨ P ∨ R :=
begin
  rw [or.comm P, or.assoc, or.comm R],
end

/-- the recursor for `∨` -/
theorem or.rec : (P → R) → (Q → R) → P ∨ Q → R :=
begin
  intros hPR hQR hPoQ,
  exact or.elim _ _ _ hPoQ hPR hQR,
end

theorem or_congr : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) :=
begin
  rintro hPR hQS,
  rw [hPR, hQS],
end

/-!

### true and false

`true` is a true-false statement, which can be proved with the `trivial` tactic.

`false` is a true-false statment which can only be proved if you manage
to find a contradiction within your assumptions.

If you manage to end up with a hypothesis `h : false` then there's quite
a funny way to proceed, which we now explain.

If you have `h : P ∧ Q` then you can uses `cases h with hP hQ` to split
into two cases. 

If you have `h : false` then what do you think happens if we do `cases h`?
Hint: how many cases are there?
-/


/-- eliminator for `false` -/
theorem false.elim : false → P :=
begin
  intro h,
  cases h,
end

theorem and_true_iff : P ∧ true ↔ P :=
begin
  split,
  { rintro ⟨hP, -⟩,
    exact hP },
  { intro hP,
    split,
    { exact hP },
    { trivial } }
end

theorem or_false_iff : P ∨ false ↔ P :=
begin
  split,
  { rintro (hP | h),
    { assumption },
    { cases h} },
  { intro hP,
    left,
    exact hP }
end

-- false.elim is handy for this one
theorem or.resolve_left : P ∨ Q → ¬P → Q :=
begin
  rintro (hP | hQ) hnP,
  { apply false.elim,
    exact hnP hP },
  { exact hQ },
end

-- this one you can't do constructively
theorem or_iff_not_imp_left : P ∨ Q ↔ ¬P → Q :=
begin
  split,
  { apply or.resolve_left },
  { intro hnPQ,
    -- TODO : document this tactic
    by_cases h : P,
    { left, assumption },
    { right, exact hnPQ h} }
end

end xena

