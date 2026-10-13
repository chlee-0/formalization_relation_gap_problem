import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic.NormNum

/-! General endgames only. These do not establish their topological or module hypotheses. -/
namespace D2RelationGap

/-- Exact Bezout elimination used AFTER both annihilation identities are proved. -/
theorem coprime_annihilators {M : Type*} [AddCommGroup M] (u : M)
    (h15 : (15 : ℤ) • u = 0) (h26 : (26 : ℤ) • u = 0) : u = 0 := by
  have hbez : (-19 : ℤ) * 15 + 11 * 26 = 1 := by norm_num
  calc
    u = (1 : ℤ) • u := (one_zsmul u).symm
    _ = ((-19 : ℤ) * 15 + 11 * 26) • u := by rw [hbez]
    _ = (-19 : ℤ) • ((15 : ℤ) • u) + (11 : ℤ) • ((26 : ℤ) • u) := by
      rw [add_zsmul, mul_zsmul, mul_zsmul]
    _ = 0 := by simp only [h15, h26, smul_zero, add_zero]

/-- The finite counting contradiction, not a proof of the existence of a cyclic tower. -/
theorem no_bounded_strict_growth (f : ℕ → ℕ) (bound : ℕ)
    (hstep : ∀ n, f n < f (n+1)) (hbound : ∀ n, f n ≤ bound) : False := by
  have hgrowth : ∀ n, n ≤ f n := by
    intro n
    induction n with
    | zero => exact Nat.zero_le _
    | succ n ih =>
      have hs := hstep n
      omega
  have h1 := hgrowth (bound+1)
  have h2 := hbound (bound+1)
  omega

end D2RelationGap
