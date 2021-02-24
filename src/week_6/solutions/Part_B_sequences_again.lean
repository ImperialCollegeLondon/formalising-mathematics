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
if aₙ → l and bₙ → m then aₙ + bₙ → l + m.

Let's see another proof of these things using filters.

-/

open filter

open_locale topological_space

open metric

example (l : ℝ) (S : set ℝ) (hlS : l ∈ S) (hS : is_open S) :
∃ ε > 0, ball l ε ⊆ S := is_open_iff.mp hS l hlS

theorem is_limit_iff_tendsto (a : ℕ → ℝ) (l : ℝ) :
is_limit a l ↔ tendsto a at_top (𝓝 l) :=
begin
  rw metric.tendsto_nhds,
  unfold is_limit,
  apply forall_congr,
  intro ε,
  apply forall_congr,
  intro hεpos,
  rw eventually_iff,
  rw mem_at_top_sets,
  refl,
end

theorem is_limit_iff_tendsto (a : ℕ → ℝ) (l : ℝ) :
is_limit a l ↔ tendsto a at_top (𝓝 l) :=
begin
  rw metric.tendsto_at_top,
  refl,
end