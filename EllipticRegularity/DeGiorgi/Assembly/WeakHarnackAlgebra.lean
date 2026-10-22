module

public import EllipticRegularity.DeGiorgi.Assembly.Statements

/-!
# Extended-real and real algebra for the weak Harnack assembly
-/

@[expose] public section

open scoped ENNReal

namespace PDE.DGNMAssembly

/-- The chain `E1`, `E2`, `E3` of the weak Harnack proof, as pure algebra in `ℝ≥0∞`. -/
theorem weakHarnack_chain_algebra {X F c J K V A C0 C1 M : ℝ≥0∞}
    (hX : X ≤ F * (c * J))
    (hE1 : A * (c * K)⁻¹ ≤ C0 * M)
    (hE3 : (V⁻¹ * J) * (V⁻¹ * K) ≤ C1)
    (hV1 : V ≤ 1) (hA0 : A ≠ 0) (hAtop : A ≠ ⊤) (hc0 : c ≠ 0) (hctop : c ≠ ⊤)
    (hC0 : C0 ≠ 0) (hC0top : C0 ≠ ⊤) (hC1 : C1 ≠ 0) (hC1top : C1 ≠ ⊤) (hF : F ≠ 0) :
    X ≤ F * c * A⁻¹ * C0 * c * C1 * M := by
  have hcoef0 : F * c * A⁻¹ * C0 * c * C1 ≠ 0 := by
    simp [hF, hc0, hC0, hC1, hAtop]
  by_cases hM : M = ⊤
  · rw [hM, ENNReal.mul_top hcoef0]; exact le_top
  by_cases hJ : J = 0
  · simp [hJ] at hX
    rw [hX]; exact zero_le
  have hJK : J * K ≤ C1 := by
    refine le_trans ?_ hE3
    have : (1 : ℝ≥0∞) ≤ V⁻¹ := by
      rw [ENNReal.one_le_inv]; exact hV1
    calc J * K = (1 * J) * (1 * K) := by simp
      _ ≤ (V⁻¹ * J) * (V⁻¹ * K) := by gcongr
  have hKtop : K ≠ ⊤ := by
    intro hK
    rw [hK, ENNReal.mul_top hJ] at hJK
    exact hC1top (top_le_iff.mp hJK)
  have hK0 : K ≠ 0 := by
    intro hK
    rw [hK, mul_zero, ENNReal.inv_zero, ENNReal.mul_top hA0] at hE1
    have : C0 * M ≠ ⊤ := ENNReal.mul_ne_top hC0top hM
    exact this (top_le_iff.mp hE1)
  have hcK0 : c * K ≠ 0 := mul_ne_zero hc0 hK0
  have hcKtop : c * K ≠ ⊤ := ENNReal.mul_ne_top hctop hKtop
  have hA : A ≤ C0 * M * (c * K) := by
    calc A = A * (c * K)⁻¹ * (c * K) := by
          rw [mul_assoc, ENNReal.inv_mul_cancel hcK0 hcKtop, mul_one]
      _ ≤ C0 * M * (c * K) := by gcongr
  have hJA : J * A ≤ C0 * M * c * C1 := by
    calc J * A ≤ J * (C0 * M * (c * K)) := by gcongr
      _ = C0 * M * c * (J * K) := by ring
      _ ≤ C0 * M * c * C1 := by gcongr
  have hJ' : J ≤ A⁻¹ * (C0 * M * c * C1) := by
    calc J = J * A * A⁻¹ := by
          rw [mul_assoc, ENNReal.mul_inv_cancel hA0 hAtop, mul_one]
      _ ≤ (C0 * M * c * C1) * A⁻¹ := by gcongr
      _ = A⁻¹ * (C0 * M * c * C1) := mul_comm _ _
  calc X ≤ F * (c * J) := hX
    _ ≤ F * (c * (A⁻¹ * (C0 * M * c * C1))) := by gcongr
    _ = F * c * A⁻¹ * C0 * c * C1 * M := by ring

end PDE.DGNMAssembly
