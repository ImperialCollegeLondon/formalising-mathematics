import week_7.solutions.Part_A_quotients
import week_7.solutions.Part_B_universal_property

-- pℤ is the usual function ℕ² → ℤ
def pℤ (ab : N2) : ℤ := (ab.1 : ℤ) - ab.2

@[simp] lemma pℤ_def (a b : ℕ) : pℤ (a, b) = (a : ℤ) - b := rfl

theorem pℤsurj : function.surjective pℤ :=
begin
  intro z,
  apply int.induction_on z,
  { use (0, 0),
    simp,
  },
  { rintro i ⟨⟨a, b⟩, h⟩,
    use ⟨a + 1, b⟩,
    rw [←h],
    simp,
    ring },
  { rintro i ⟨⟨a, b⟩, h⟩,
    use ⟨a, b + 1⟩,
    rw [←h],
    simp,
    ring }
end

theorem pℤequiv (ab cd : N2) : ab ≈ cd ↔ pℤ ab = pℤ cd :=
begin
  cases ab with a b,
  cases cd with c d,
  split;
  { simp,
    intros,
    linarith },
end


noncomputable def invp : ℤ → N2 :=
λ z, classical.some (pℤsurj z)

@[simp] theorem invp_inv (z : ℤ) : pℤ (invp z) = z := classical.some_spec (pℤsurj z)

theorem int_is_universal : is_universal ℤ pℤ :=
begin
  split,
  { rintros ⟨a, b⟩ ⟨c, d⟩,
    rw [N2.equiv_def, pℤ],
    simp,
    intros,
    linarith },
  { intros T p h,
    use (λ z, p (invp z)),
    split,
    { ext ab,
      simp,
      apply h,
      rw pℤequiv,
      simp },
    { intros k hk,
      ext z,
      simp [hk, function.comp],
      simp,
    }
  },
end

noncomputable example : ℤ ≃ Z :=
universal_equiv_quotient _ _ _ int_is_universal 
