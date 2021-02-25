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

Let's see another, much shorter, proof of these things using filters,
and of course also using facts from `mathlib` about filters.

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

theorem is_limit_mul (a b : ℕ → ℝ) (l m : ℝ)
  (ha : is_limit a l) (hb : is_limit b m) :
  is_limit (a * b) (l * m) :=
begin
  rw is_limit_iff_tendsto at *,
  exact tendsto.mul ha hb,
end

/-

This was much less painful than what we went through in week 3! So where
did the work go?

The next 130 lines of this file discuss the first proof, namely
`is_limit_iff_tendsto`. Clearly the key ingredients is
`metric.tendsto_at_top`. There are no exercises here, I will just
explain what's going on, and talk about definitions (e.g. `is_limit`)
and their cost.

The second proof uses `is_limit_iff_tendsto` to reduce `is_limit_mul`
to a theorem about filters, and them proves it with `tendsto.mul`. We will
prove our own version of `tendsto.mul` in this file. So if you want to
get on with the proving you can skip straight down to
the `## tendsto.mul` section on line 184 or so.

The first proof 

## Definitions in Lean

Each *definition* you make in Lean comes with a cost. For example
check out Lean's definition of `finset`, the type of finite sets.
Right click on `finset` below and click on "go to definition".
You see one definition, and then over 2000 lines of theorems
about this definition. Don't forget to close the file afterwards!
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
that `aₙ → l` and `bₙ → m` implies `a_n + b_n → l + m`, and also `is_limit_neg`,
`is_limit_sub`, `is_limit_mul` and so on.

But it turns out that `is_limit` is just a very special case of `tendsto`,
and because `tendsto` is already in mathlib, there is already a very big
API for `tendsto` which has developed organically over the last few
years. It was started by the original writer of `tendsto` and then
it grew as other people used `tendsto` more, and added to the list of useful
lemmas as they used `tendsto` to do other things and then abstracted out
properties which they discovered were useful. For example, this week
(I write this in Feb 2021) Heather Macbeth was working on modular forms in Lean
and she discovered that she needed a lemma about `tendsto`, which, after some
discussion on the Zulip Lean chat, Heather and I realised was a statement
about how `tendsto` commutes with a certain kind of coproduct. We proved this
lemma, Heather is right now in the process of adding it (`tendsto.prod_map_coprod`)
to `mathlib`, Lean's maths library.

https://github.com/leanprover-community/mathlib/pull/6372

I will remark that I would never have worked on that problem with Heather
if it hadn't been for the fact that I'd been teaching you about filters
and hence I had to learn about them properly!

Let's take a look at our new proof of `tendsto_mul` again. The proof follows
from two 2-line lemmas. I will talk you through the first one, and you can
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
(here `ball l ε` is the open ball radius `ε` centre `l` ),
the first being `metric.tendsto_nhds` and the second `mem_at_top_sets`:

1) If `a` is in a metric space, then `S ∈ 𝓝 l ↔ ∃ ε > 0, ball l ε ⊆ S`
2) If `at_top` is the filter on on `ℕ` that we saw last time then
`T ∈ at_top ↔ ∃ N : ℕ, {n : ℕ | N ≤ n} ⊆ T`

After that it's easy, because `tendsto a at_top (𝓝 l)` then means,
by definition of `tendsto`, 

`∀ S : set ℝ, S ∈ 𝓝 l → a ⁻¹' S ∈ at_top`

which translates into

`∀ S : set ℝ, (∃ ε > 0, ball l ε ⊆ S) → (∃ N, n ≥ N → a n ∈ S)`

and if you unfold the logical packaging you will see that this is just
the usual definition of `is_limit` (note that `a n ∈ ball l ε` is
definitionally equal to `dist (a n) l < ε` which, for the reals, is
definitionally equal to `|a n - l| < ε`).

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
and we're done, at least modulo the assertion that multiplication
on ℝ is a continuous function. How did Lean know this? Well, 
`[has_continuous_mul M]` was in square brackets so that means that
the type class inference system is supposed to deal with it. Let's
see how it gets on with the assertion that multiplication is continuous
on the reals.

-/

-- multiplication is continuous on the reals.
example : has_continuous_mul ℝ :=
begin
  -- Ask the type class inference system whether it knows this
  apply_instance
end
-- It does!

/-

The people who defined `ℝ` in Lean made a definition, and the price they
had to then pay for making it usable was that they had to make a big API for
`ℝ`, proving stuff like a non-empty bounded set of reals has a least
upper bound, and that the reals were a topological ring (and hence
multiplication was continuous). But this price was paid way back in 2018
so we mathematicians can now use these facts for free.

All that remains then, if we want to see the details, is to
*prove* `tendsto.mul`, and this is a statement about filters on topological
spaces, so let's do it. First -- what does `continuous` mean?

## Continuity

Let `X` and `Y` be topological spaces, and say `f : X → Y` is a function.

-/
variables (X Y : Type) [topological_space X] [topological_space Y] (f : X → Y)

/-

If `x : X`, then what does it mean for `f` to be continuous at `x`?
Intuitively, it means that if you move `x` by a small amount, then `f x`
moves by a small amount. In other words, `f` sends a small neighbourhood
of `x` into a small neighbourhood of `f x`. 

If our mental model of the neighbourhood filter `𝓝 x` is some kind of
generalised set corresponding to an infinitesimally small
neighbourhood of `x`, you will see why Lean makes the following
definition of `continuous_at`:

-/

lemma continuous_at_def (x : X) :
  continuous_at f x ↔ tendsto f (𝓝 x) (𝓝 (f x)) :=
begin
  -- true by definition
  refl
end

/-

Out of interest, you were probably told the definition of what it means
for a function `f : X → Y` between *metric* spaces to be continuous at `x`.
Were you ever told what it means for a function between *topological* spaces
to be continuous at `x`, rather than just continuous on all of `X`? This
is what it means.

Now let's start on the proof of `tendsto.mul`, by building an API
for the `continuous_at` definition. Don't forget things like

`tendsto_id : tendsto id x x`
`tendsto.comp : tendsto g G H → tendsto f F G → tendsto (g ∘ f) F H`

from Part A.
-/

-- this first lemma called `continuous_at_id`. Prove it yourself using
-- facts from Part A.
example (x : X) : continuous_at id x :=
begin
  sorry
end

-- recall we have `f : X → Y`. Now let's add in a `Z`.
variables (Z : Type) [topological_space Z] (g : Y → Z)

-- this is called `continuous_at.comp`. Prove it yourself using
-- facts from Part A.
example (x : X) (hf : continuous_at f x) (hg : continuous_at g (f x)) :
continuous_at (g ∘ f) x :=
begin
  sorry
end

/-

Now we prove a key result, called `tendsto.prod_mk_nhds`. Notation for product
of types: if `Y` and `Z` are types then `Y × Z` is the product type, and 
the notation for a general term is `(y, z) : Y × Z` with `y : Y` and `z : Z`.

A special case of the theorem below is that if `f : X → Y` and `g : X → Z` are
continuous at `x` then the product map `f × g : X → Y × Z` is also continuous
at `x`. We will actually prove something more general -- if `α` is any type
and `F : filter α` is any filter and if `y : Y` and `z : Z` and if
`f : α → Y` and `g : α → Z` satisfy `tendsto f F (𝓝 y)` and `tendsto g F (𝓝 z)`,
then `tendsto (f × g) F (𝓝 (y,z))`, where `f × g` is the map `λ x, (f x, g x)`.
The key fact you will need from the product topology API is 
`mem_nhds_prod_iff : S ∈ 𝓝 ((a, b) : X × Y) ↔`
  `∃ (U : set X) (H : U ∈ 𝓝 a) (V : set Y) (H : V ∈ 𝓝 b), U.prod V ⊆ S`
This is all you should need about the product topology (we won't go into how
the product topology is defined, but the key fact mathematically says that a
neighbourhood of `(a,b) : X × Y` contains a product of neighbourhoods of `X` and of `Y`).

You will also need to know

`mk_mem_prod : a ∈ U → b ∈ V → (a, b) ∈ U.prod V`

where for `U : set X` and `V : set Y`, `U.prod V = prod U V` is the 
obvious subset of `X × Y`. 

Recall also from Part A:
`mem_map : S ∈ map φ F ↔ {x : α | φ x ∈ S} ∈ F`
`tendsto_def : tendsto f F G ↔ ∀ (S : set Y), S ∈ G → f ⁻¹' S ∈ F`
(although there is a gotcha here : the actual definition of 
`tendsto f F G` is `∀ {S : set Y}, S ∈ G ...` )
-/

-- this is called `tendsto.prod_mk_nhds` in Lean but try proving it yourself.
example {α : Type} (f : α → Y) (g : α → Z) (x : X) (F : filter α) (y : Y) (z : Z)
  (hf : tendsto f F (𝓝 y)) (hg : tendsto g F (𝓝 z)) :
  tendsto (λ x, (f x, g x)) F (𝓝 (y, z)) :=
begin
  sorry,
end

/- Armed with `tendsto.prod_mk_nhds`, let's prove the version of `tendsto.mul`
 which we need. I would recommend starting with
```
set f1 : M × M → M := λ mn, mn.1 * mn.2 with hf1,
set f2 : α → M × M := λ x, (f x, g x) with hf2,
have h1 : f1 ∘ f2 = f * g,
...
```
because it's `f1` and `f2` that we've been proving theorems about,
and then you can use `tendsto.comp`. 
-/

lemma key_lemma {α M : Type} [topological_space M] [has_mul M] 
  {f g : α → M} {F : filter α} {a b : M} (hf : tendsto f F (𝓝 a))
  (hg : tendsto g F (𝓝 b))
  (hcontinuous : continuous_at (λ (mn : M × M), mn.1 * mn.2) (a,b)) :
  tendsto (f * g) F (𝓝 (a * b)) :=
begin
  sorry
end

-- The final ingredient is that multiplication is continuous on ℝ, which we
-- just take from the real API:
lemma real.continuous_mul_at (a b : ℝ) :
  continuous_at (λ xy : ℝ × ℝ, xy.1 * xy.2) (a, b) :=
begin
  -- it's in the library
  exact continuous.continuous_at real.continuous_mul,
end

-- and now we have all the ingredients we need for our own proof of `is_limit_mul`!
example  (a b : ℕ → ℝ) (l m : ℝ)
  (ha : is_limit a l) (hb : is_limit b m) :
  is_limit (a * b) (l * m) :=
begin
  rw is_limit_iff_tendsto at *,
  apply key_lemma ha hb,
  apply real.continuous_mul_at,
end

/-

You might think that this new proof "feels longer". But what you have to
understand is that it's shorter in practice, because the user doesn't
have to write `tendsto.mul` themselves, it's already there in the library.
Writing APIs is an extensive process. But using them is easy. 
-/