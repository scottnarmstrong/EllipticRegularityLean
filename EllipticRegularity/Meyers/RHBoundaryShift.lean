module

public import EllipticRegularity.Meyers.RHBoundaryAssembly
public import EllipticRegularity.Meyers.RHBoundaryCutoffH10
public import EllipticRegularity.Meyers.RHBoundaryData
public import EllipticRegularity.Meyers.ZeroSet
public import PDEFoundation.Sobolev.H1.ZeroBoundaryCutoff
public import PDEFoundation.Sobolev.H1.Mean
public import PDEFoundation.Sobolev.Mean

/-!
# The constant shift in the boundary reverse Hölder inequality

Step 3 of the reverse Hölder lemma: for a cube `Q = centeredAxisCube z r` there is a
constant `c` such that `η (u - c) ∈ H¹₀(B₁)` for every admissible cutoff `η`, and
`|ū - c| ≤ 2^{d-1} ‖u - ū‖_{L^{q'}(4Q)}` (normalized): `c = ū` if `2Q ⊆ B₁`, and `c = 0`
otherwise, using the zero-set geometry.
-/

@[expose] public section

open MeasureTheory

namespace PDE

namespace MeyersRH

variable {d : ℕ}

theorem closedCenteredAxisCube_subset (z : Vec d) {r : ℝ} (hr : 0 < r) :
    closedCenteredAxisCube z (3 * r / 2) ⊆ centeredAxisCube z (2 * r) := by
  intro x hx i _
  have := hx i (Set.mem_univ i)
  simp only [Set.mem_Icc] at this
  constructor <;> dsimp <;> linarith [this.1, this.2]

theorem two_pow_rpow_qDual (hd : 2 ≤ d) : ((2 : ℝ) ^ (d - 1)) ^ qDual d = 4 ^ d := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have h1 : ((d - 1 : ℕ) : ℝ) = (d : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), h1]
  have h2 : ((d : ℝ) - 1) * qDual d = 2 * d := by
    unfold qDual
    have : (d : ℝ) - 1 ≠ 0 := by linarith
    field_simp
  rw [h2, show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_natCast,
    ← Real.rpow_mul (by norm_num)]

/-- The admissible shift `c`. -/
theorem exists_shift (hd : 2 ≤ d) (u : H10Function (euclideanBall (0 : Vec d) 1))
    (z : Vec d) {r : ℝ} (hr : 0 < r)
    (hv : MemLp (fun x => uExt u x - integralAverage (centeredAxisCube z (4 * r)) (uExt u))
      (ENNReal.ofReal (qDual d)) (volume.restrict (centeredAxisCube z (4 * r)))) :
    ∃ c : ℝ,
      (∀ η : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
        tsupport η ⊆ closedCenteredAxisCube z (3 * r / 2) →
        ∃ v : H10Function (euclideanBall (0 : Vec d) 1),
          v.toFun = fun x => η x * (u.toFun x - c)) ∧
      |integralAverage (centeredAxisCube z (4 * r)) (uExt u) - c| ≤
        (2 : ℝ) ^ (d - 1) * lpAvg (centeredAxisCube z (4 * r)) (qDual d)
          (fun x => |uExt u x - integralAverage (centeredAxisCube z (4 * r)) (uExt u)|) := by
  set P := centeredAxisCube z (4 * r) with hP
  set ub := integralAverage P (uExt u) with hub
  have hBc := isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) (R := 1) one_pos
  have hq'0 : 0 < qDual d := (qExp_holderConjugate hd).symm.pos
  have hN0 : 0 ≤ lpAvg P (qDual d) (fun x => |uExt u x - ub|) :=
    lpAvg_nonneg P _ fun x => abs_nonneg _
  by_cases h2 : centeredAxisCube z (2 * r) ⊆ euclideanBall (0 : Vec d) 1
  · refine ⟨ub, fun η hη hηc hηs => ?_, ?_⟩
    · have hηB : tsupport η ⊆ euclideanBall (0 : Vec d) 1 := hηs.trans ((closedCenteredAxisCube_subset z hr).trans h2)
      refine ⟨(u.toH1Function.subConst hBc ub).mulContDiffHasCompactSupportToH10 hBc hη hηc hηB,
        ?_⟩
      have := H1Function.mulContDiffHasCompactSupportToH10_toFun
        (u.toH1Function.subConst hBc ub) hBc hη hηc hηB
      funext x
      simp
    · rw [sub_self, abs_zero]
      exact mul_nonneg (by positivity) hN0
  · refine ⟨0, fun η hη hηc _ => ?_, ?_⟩
    · obtain ⟨v, hv⟩ := exists_h10_mul_contDiff u hη hηc
      exact ⟨v, by simpa using hv⟩
    · have hZ : ((4 : ℝ)⁻¹) ^ d * (volume P).toReal ≤
          (volume (P \ euclideanBall (0 : Vec d) 1)).toReal := volume_cube_diff_ball_ge hr h2
      have hPm : MeasurableSet P := (isOpen_centeredAxisCube z _).measurableSet
      have hint : IntegrableOn (fun x => |uExt u x - ub| ^ qDual d) P := by
        have := hv.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hq'0).ne' ENNReal.ofReal_ne_top
        have h' : Integrable (fun x => |uExt u x - ub| ^ qDual d) (volume.restrict P) := by
          simpa [ENNReal.toReal_ofReal hq'0.le] using this
        exact h'
      have hκ : (0 : ℝ) < (2 : ℝ) ^ (d - 1) := by positivity
      have hvol : (((2 : ℝ) ^ (d - 1)) ^ qDual d)⁻¹ * (volume P).toReal ≤
          (volume (P \ euclideanBall (0 : Vec d) 1)).toReal := by
        rw [two_pow_rpow_qDual hd, ← inv_pow]
        exact hZ
      have := abs_le_mul_lpAvg_of_zero hq'0 (P := P) (Z := P \ euclideanBall (0 : Vec d) 1) Set.sdiff_subset
        (hPm.diff (measurableSet_euclideanBall _ _))
        (volume_centeredAxisCube_toReal_pos z (by positivity)) hκ hint
        (fun x hx => by simp [uExt, Set.indicator_of_notMem hx.2]) hvol
      simpa using this

end MeyersRH

end PDE
