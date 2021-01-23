import tactic

-- now let's see forall and exists
variables (Ω : Type) (X Y : set Ω)

example : ¬ (∃ a, a ∈ X) ↔ ∀ b, ¬ (b ∈ X) :=
begin
  elide 0,
  split,
  { intro h,
    intros b hb,
    apply h,
    use b,
    assumption },
  { intro h,
    intro h2,
    cases h2 with a ha,
    apply h a,
    assumption },
end
example : ¬ (∀ a, a ∈ X) ↔ ∃ b, ¬ (b ∈ X) :=
begin
  split,
  { -- classical
    intro h,
    classical,
    by_contra hnX,
    apply h,
    intro a,
    by_contra hXa,
    apply hnX,
    use a }, 
  { intro h,
    cases h with b hb,
    intro h,
    apply hb,
    apply h }
end

