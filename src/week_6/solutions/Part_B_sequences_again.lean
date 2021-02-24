import data.real.basic
import order.filter.at_top_bot
import topology.instances.real
/-

## Sequences, revisited

Recall that in week 3 we made these definitions:

-/

local notation `|` x `|` := abs x

/-- `l` is the limit of the sequence `a` of reals -/
definition is_limit (a : ℕ → ℝ) (l : ℝ) : Prop :=
∀ ε > 0, ∃ N, ∀ n ≥ N, | a n - l | < ε

/-

We then spent some time proving things like
if aₙ → l and bₙ → m then aₙ * bₙ → l * m.

Let's see another proof of these things using filters.

-/

open filter

open_locale topological_space

open metric

theorem is_limit_iff_tendsto (a : ℕ → ℝ) (l : ℝ) :
is_limit a l ↔ tendsto a at_top (𝓝 l) :=
begin
  rw metric.tendsto_at_top,
  refl,
end

example (a b : ℕ → ℝ) (l m : ℝ) (ha : is_limit a l) (hb : is_limit b m) :
  is_limit (a * b) (l * m) :=
begin
  rw is_limit_iff_tendsto at *,
  exact tendsto.mul ha hb,
end

/-

This was much less painful than what we went through in week 3! So where
did the work go?

## Definitions in Lean

Each *definition* you make in Lean comes with a cost. For example
check out Lean's definition of `finset`, the type of finite sets.
Right click on `finset` below and click on "go to definition".
You see one definition, and then over 2000 lines of theorems
about this definition. 
-/

#check finset

/-
The theorems are necessary because it's no good just defining some
concept of a finite set, you need to make it intuitive to use for the
end user, so you need to prove that a subset of a finite set is finite,
the union of two finite sets is finite, the image of a finite set under
a map is finite, the product of two finite sets is finite, a finite product
of finite sets indexed by a finite set is finite, etc etc. Every one of those
lemmas in that file is completely obvious to a mathematician, but needs
to be proved in Lean so that mathematicians can use finite sets the
way they intuitively want to. See if you can understand some of the
statements proved about finite sets in that file. Be very careful
not to edit it though! If you do accidentally change it, just close the
file without saving, or use ctrl-Z to undo your changes. 

When we developed the theory of limits of sequences in week 3, we 
made the definition `is_limit`. This definition comes with a cost;
to make it useful to the end user, we need to prove a ton of theorems
about `is_limit`. This is what happens in an undergraduate analysis
class -- you see the definition, and then you make what computer
scientists call the "API" or the "interface" -- a bunch of lemmas
and theorems about `is_limit`, for example `is_limit_add`, which says
that `aₙ → l` and `bₙ → m` implies `a_n + b_n → l + m`.

But it turns out that `is_limit` is just a very special case of `tendsto`,
and because `tendsto` is already in mathlib, there is already a very big
API for `tendsto` which has developed organically over the last few
years. It was started by the original writer of `tendsto` and then
it grew as other people used `tendsto` more, and added to the list of useful
lemmas as they used `tendsto` to do other things and then abstracted out
properties which they discovered were useful. For example, this week
(I write this in Feb 2021) Heather Macbeth was working on modular forms in Lean
and she discovered that she needed a lemma about `tendsto`, which, after some
discussion on the Zulip Lean chat, Heather and I discovered was a statement
about how `tendsto` commutes with a certain kind of coproduct. Heather is
right now in the process of adding this lemma (`tendsto.prod_map_coprod`)
to `mathlib`, Lean's maths library.

https://github.com/leanprover-community/mathlib/pull/6372

I will remark that I would never have worked on that problem with Heather
if it hadn't been for the fact that I'd been teaching you about filters
and hence I had to learn about them properly!

Let's take a look at our proof again. The proof follows from two
2-line lemmas. I will talk you through the first one, and you can
experiment with the second one. Let's take a look at the first one.

-/

example (a : ℕ → ℝ) (l : ℝ) :
is_limit a l ↔ tendsto a at_top (𝓝 l) :=
begin
  rw metric.tendsto_at_top,
  refl,
end

/-

The guts of the first one is `metric.tendsto_at_top`, which is actually
a statement about metric spaces. It says that in any metric space,
the standard metric space epsilon-N definition of a limit of a sequence
is a special case of this filter `tendsto` predicate. Here is a proof
with more details spelt out (`simp_rw` is just a slightly more powerful
version of `rw` which we need for technical reasons here, because `rw` will
not see under a `∀` statement -- it will not "work under binders"):
-/

example (a : ℕ → ℝ) (l : ℝ) :
is_limit a l ↔ tendsto a at_top (𝓝 l) :=
begin
  simp_rw [metric.tendsto_nhds, eventually_iff, mem_at_top_sets],
  refl,
end

/-

This more explicit proof uses the following fancy notation
called "filter.eventually" :

`(∀ᶠ (x : α) in F, P x) ↔ {x : α | P x} ∈ F` (true by definition, or
you can `rw eventually_iff`)

and then it just boils down to the following two mathematical facts
(here `ball l ε` is the open ball radius `ε` centre `l` )

1) If `a` is in a metric space, then `S ∈ 𝓝 l ↔ ∃ ε > 0, ball l ε ⊆ S`
2) If `at_top` is the filter on on `ℕ` that we saw last time then
`T ∈ at_top ↔ ∃ N : ℕ, {n : ℕ | N ≤ n} ⊆ T`

After that it's easy, because `tendsto a at_top (𝓝 l)` then means,
by definition of `tendsto`, 

`∀ S : set ℝ, S ∈ 𝓝 l → a ⁻¹' S ∈ at_top`

which translates into

`∀ S : set ℝ, (∃ ε > 0, ball l ε ⊆ S) → (∃ N, n ≥ N → a n ∈ S)`

and if you unfold the logical packaging you will see that this is just
the usual definition of `is_limit`.

## tendsto.mul

Now let's look at the second example.

-/

example (a b : ℕ → ℝ) (l m : ℝ) (ha : is_limit a l) (hb : is_limit b m) :
  is_limit (a * b) (l * m) :=
begin
  rw is_limit_iff_tendsto at *,
  exact tendsto.mul ha hb,
end

/-

If you hover over `tendsto.mul` in that proof, you will perhaps be able to make
out that it says the following: if we have a topological space `M` with a
continuous multiplication on it, and if `F` is a filter on `α` and `f` and `g`
are maps `α → M`, then `tendsto f F (𝓝 l)` and `tendsto g F (𝓝 m)` implies
`tendsto (f * g) F 𝓝 (l * m)`. We apply this with `F` the cofinite filter
and we're done! Oh, there is one thing: how did Lean know that multiplication
on ℝ was a continuous function?

-/

-- Ask the type class inference system whether multiplication on ℝ is continuous
example : has_continuous_mul ℝ := infer_instance
-- It is!

/-

The people who defined `ℝ` in Lean made a definition, and the price they
had to then pay for making it usable was that they had to make a big API for
`ℝ`, proving stuff like a non-empty bounded set of reals has a least
upper bound, and that the reals were a topological ring (and hence
multiplication was continuous). But this price was paid way back in 2018
so we mathematicians can use these facts for free.

All that remains then, is to prove `tendsto.mul`, and this is a statement
about filters on topologial spaces, so let's do it.
-/

