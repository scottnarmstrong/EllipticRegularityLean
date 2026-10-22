module

public import EllipticRegularity.Meyers.RHInteriorSP
public import EllipticRegularity.Meyers.RHInteriorNorm
public import EllipticRegularity.Meyers.RHBoundary
public import PDEFoundation.Sobolev.H1.ZeroExtension
public import SobolevStatements.ConvexSobolevPoincare

/-!
# Sobolev--Poincaré for the zero extension of an `H¹₀(B₁)` function

The zero extension of `u ∈ H¹₀(B₁)` lies in `H¹` of the whole space, hence in `W^{1,q}` of every
cube; the cube Sobolev--Poincaré inequality then gives the `hSP` hypothesis of
`boundary_reverse_holder` (in the `lpAvg` normalization).
-/

@[expose] public section

open scoped ENNReal

namespace PDE.MeyersRH

open MeasureTheory

variable {d : ℕ}

theorem lpAvg_eq_toReal_eLpNorm {P : Set (Vec d)} (hP0 : volume P ≠ 0) {p : ℝ} (hp : 0 < p)
    {g : Vec d → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (hg : MemLp g (ENNReal.ofReal p) (volumeOn P)) :
    lpAvg P p g = (eLpNorm g (ENNReal.ofReal p) (normalizedVolumeOn P)).toReal := by
  have hc : (volume P)⁻¹ ≠ ∞ := ENNReal.inv_ne_top.2 hP0
  have hg' : MemLp g (ENNReal.ofReal p) (normalizedVolumeOn P) := hg.smul_measure hc
  rw [toReal_eLpNorm_eq_integral_rpow hp hg']
  unfold lpAvg normalizedVolumeOn
  rw [integral_smul_measure, ENNReal.toReal_inv]
  simp only [Real.norm_of_nonneg (hg0 _), smul_eq_mul]

theorem memLp_of_memLp_normalizedVolumeOn {P : Set (Vec d)} (hP0 : volume P ≠ 0)
    (hPt : volume P ≠ ∞) {p : ℝ≥0∞} {g : Vec d → ℝ}
    (hg : MemLp g p (normalizedVolumeOn P)) : MemLp g p (volumeOn P) := by
  have hc : volume P ≠ ∞ := hPt
  have := hg.smul_measure hc
  unfold normalizedVolumeOn at this
  rwa [smul_smul, ENNReal.mul_inv_cancel hP0 hPt, one_smul] at this

/-- Sobolev--Poincaré for the zero extension of `u ∈ H¹₀(B₁)` on every cube. -/
theorem sp_zeroExtension (hd : 2 ≤ d) :
    ∃ S : ℝ, 0 < S ∧ ∀ u : H10Function (euclideanBall (0 : Vec d) 1),
      ∀ (z : Vec d) (ρ : ℝ), 0 < ρ →
      MemLp (fun x => uExt u x - integralAverage (centeredAxisCube z ρ) (uExt u))
        (ENNReal.ofReal (qDual d)) (volumeOn (centeredAxisCube z ρ)) ∧
      lpAvg (centeredAxisCube z ρ) (qDual d)
          (fun x => |uExt u x - integralAverage (centeredAxisCube z ρ) (uExt u)|) ≤
        S * (2 * ρ) * lpAvg (centeredAxisCube z ρ) (qExp d)
          (fun x => vecEuclideanNorm (gradExt u x)) := by
  obtain ⟨S, hS, hSP⟩ := cube_sobolevPoincare d hd (exists_convexSobolevPoincare_constant d hd)
  refine ⟨S, hS, fun u z ρ hρ => ?_⟩
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hq : ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) + 1)) ≤ 2 := by
    have : 2 * (d : ℝ) / ((d : ℝ) + 1) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    calc ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) + 1)) ≤ ENNReal.ofReal 2 :=
          ENNReal.ofReal_le_ofReal this
      _ = 2 := by simp
  have hball : IsOpen (euclideanBall (0 : Vec d) 1) :=
    (isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) one_pos).isOpen
  let Z : H1Function (Set.univ : Set (Vec d)) :=
    u.zeroExtendToH1 isOpen_univ hball (Set.subset_univ _)
  let v := restrictCubeW1p Z z (Set.subset_univ (centeredAxisCube z ρ))
    (ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) + 1))) hq
  have hv := hSP z ρ hρ v
  have hvfun : v.toFun = uExt u := rfl
  have hvgrad : v.grad = gradExt u := rfl
  rw [hvfun, hvgrad] at hv
  have hgrad : MemLp (fun x => vecEuclideanNorm (gradExt u x)) (ENNReal.ofReal (qExp d))
      (volumeOn (centeredAxisCube z ρ)) :=
    memLp_vecEuclideanNorm_of_coord (fun i => v.gradMemLp i)
  have hmeas : AEStronglyMeasurable
      (fun x => uExt u x - integralAverage (centeredAxisCube z ρ) (uExt u))
      (volumeOn (centeredAxisCube z ρ)) :=
    (v.memLp.aestronglyMeasurable : AEStronglyMeasurable (uExt u)
      (volumeOn (centeredAxisCube z ρ))).sub aestronglyMeasurable_const
  clear_value v
  set P := centeredAxisCube z ρ with hPdef
  have hvol := volume_centeredAxisCube_toReal_pos z hρ
  have hP0 : volume P ≠ 0 := (ENNReal.toReal_pos_iff.1 hvol).1.ne'
  have hPt : volume P ≠ ∞ := (ENNReal.toReal_pos_iff.1 hvol).2.ne
  have hq0 : 0 < qExp d := by unfold qExp; positivity
  have hqd0 : 0 < qDual d := by
    unfold qDual; apply div_pos (by positivity); linarith
  have hgradN : MemLp (fun x => vecEuclideanNorm (gradExt u x)) (ENNReal.ofReal (qExp d))
      (normalizedVolumeOn P) := hgrad.smul_measure (ENNReal.inv_ne_top.2 hP0)
  have hGtop : eLpNorm (fun x => vecEuclideanNorm (gradExt u x)) (ENNReal.ofReal (qExp d))
      (normalizedVolumeOn P) ≠ ∞ := hgradN.eLpNorm_lt_top.ne
  have hrhs : ENNReal.ofReal (S * (2 * ρ)) *
      euclideanFieldELpMeanNormOn P (ENNReal.ofReal (2 * (d : ℝ) / ((d : ℝ) + 1)))
        (gradExt u) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGtop
  have hF1top : eLpMeanNormOn P (ENNReal.ofReal (qDual d))
      (fun x => uExt u x - integralAverage P (uExt u)) ≠ ∞ :=
    ne_top_of_le_ne_top hrhs hv
  have hmeasN : AEStronglyMeasurable (fun x => uExt u x - integralAverage P (uExt u))
      (normalizedVolumeOn P) := by
    unfold normalizedVolumeOn
    exact hmeas.smul_measure _
  have hmemN : MemLp (fun x => uExt u x - integralAverage P (uExt u))
      (ENNReal.ofReal (qDual d)) (normalizedVolumeOn P) :=
    hF1top.lt_top
  have hmem := memLp_of_memLp_normalizedVolumeOn hP0 hPt hmemN
  refine ⟨hmem, ?_⟩
  have habs : MemLp (fun x => |uExt u x - integralAverage P (uExt u)|)
      (ENNReal.ofReal (qDual d)) (volumeOn P) := by
    simpa only [Real.norm_eq_abs] using hmem.norm
  rw [lpAvg_eq_toReal_eLpNorm hP0 hqd0 (fun x => abs_nonneg _) habs,
    lpAvg_eq_toReal_eLpNorm hP0 hq0 (fun x => vecEuclideanNorm_nonneg _) hgrad]
  have h1 : eLpNorm (fun x => |uExt u x - integralAverage P (uExt u)|)
      (ENNReal.ofReal (qDual d)) (normalizedVolumeOn P) =
      eLpMeanNormOn P (ENNReal.ofReal (qDual d))
        (fun x => uExt u x - integralAverage P (uExt u)) := by
    unfold eLpMeanNormOn
    have : (fun x => |uExt u x - integralAverage P (uExt u)|) =
        fun x => ‖uExt u x - integralAverage P (uExt u)‖ := by
      funext x; rw [Real.norm_eq_abs]
    rw [this]
    exact eLpNorm_norm _ hmeasN
  rw [h1]
  have h2 := ENNReal.toReal_mono hrhs hv
  refine h2.trans (le_of_eq ?_)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)]
  rfl

end PDE.MeyersRH
