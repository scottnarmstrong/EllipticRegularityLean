module

public import PDEFoundation.Analysis.HilbertLaplacian
public import PDEFoundation.Sobolev.ClassicalLaplacian
public import PDEFoundation.Measure.BallVolume

/-! # Exact internal coordinate and Hilbert dictionary -/

@[expose] public section

namespace PDE.Internal

open MeasureTheory Metric InnerProductSpace
open scoped InnerProductSpace Laplacian

noncomputable section

variable {d : ℕ}

local notation "𝔼" => HilbertVec d

/-- Exact continuous linear conversion of the native carrier. -/
def toHilbert : Vec d ≃L[ℝ] HilbertVec d :=
  (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm

@[simp] theorem toHilbert_apply (x : Vec d) :
    toHilbert x = x.toHilbertVec := rfl

@[simp] theorem toHilbert_symm_apply (x : HilbertVec d) :
    toHilbert.symm x = x.toVec := rfl

@[simp] theorem toHilbert_symm_basis (i : Fin d) :
    toHilbert.symm (hilbertBasis d i) = basisVec i := by
  ext j
  simp only [toHilbert, hilbertBasis, OrthonormalBasis.coe_ofRepr]
  change ((LinearIsometryEquiv.refl ℝ (HilbertVec d)).symm
    (WithLp.toLp 2 (Pi.single i (1 : ℝ) : Fin d → ℝ))).toVec j = basisVec i j
  change (Pi.single i (1 : ℝ) : Fin d → ℝ) j = basisVec i j
  simp [basisVec, Pi.single_apply]

/-- Round balls correspond exactly under the internal conversion. -/
theorem preimage_ball_toHilbert (x : Vec d) {r : ℝ} (hr : 0 < r) :
    toHilbert ⁻¹' Metric.ball (toHilbert x) r = euclideanBall x r := by
  ext y
  rw [Set.mem_preimage, Metric.mem_ball, dist_eq_norm,
    ← map_sub, toHilbert_apply, ← Vec.vecEuclideanNorm_eq_norm_toHilbertVec]
  exact (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).symm

/-- Closed round balls correspond exactly under the internal conversion. -/
theorem preimage_closedBall_toHilbert (x : Vec d) {r : ℝ} (hr : 0 ≤ r) :
    toHilbert ⁻¹' Metric.closedBall (toHilbert x) r = euclideanClosedBall x r := by
  ext y
  rw [Set.mem_preimage, Metric.mem_closedBall, dist_eq_norm,
    ← map_sub, toHilbert_apply, ← Vec.vecEuclideanNorm_eq_norm_toHilbertVec]
  exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hr).symm

/-- The exact conversion preserves Lebesgue volume. -/
theorem measurePreserving_toHilbert :
    MeasurePreserving (toHilbert : Vec d → HilbertVec d) volume volume :=
  PiLp.volume_preserving_toLp (Fin d)

/-- The inverse conversion preserves Lebesgue volume. -/
theorem measurePreserving_toHilbert_symm :
    MeasurePreserving (toHilbert.symm : HilbertVec d → Vec d) volume volume :=
  PiLp.volume_preserving_ofLp (Fin d)

theorem fderiv_comp_toHilbert_symm (v : Vec d → ℝ) (z : 𝔼) :
    fderiv ℝ (v ∘ toHilbert.symm) z
      = (fderiv ℝ v (toHilbert.symm z)).comp ((toHilbert.symm : 𝔼 ≃L[ℝ] Vec d) : 𝔼 →L[ℝ] Vec d) :=
  ContinuousLinearEquiv.comp_right_fderiv _

/-- The derivative of the pullback in a standard basis direction is the
CoarseGraining coordinate derivative. -/
theorem fderiv_comp_toHilbert_symm_basis (v : Vec d → ℝ) (z : 𝔼) (i : Fin d) :
    fderiv ℝ (v ∘ toHilbert.symm) z (hilbertBasis d i)
      = euclideanCoordDeriv i v (toHilbert.symm z) := by
  rw [fderiv_comp_toHilbert_symm]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, toHilbert_symm_basis]
  rfl

/-- As a function identity: the standard-direction derivative of the pullback is
the pullback of the CoarseGraining coordinate derivative. -/
theorem fderiv_comp_toHilbert_symm_basis_eq (v : Vec d → ℝ) (i : Fin d) :
    (fun z : 𝔼 => fderiv ℝ (v ∘ toHilbert.symm) z (hilbertBasis d i))
      = (euclideanCoordDeriv i v) ∘ toHilbert.symm := by
  funext z
  exact fderiv_comp_toHilbert_symm_basis v z i

/-! ### Second derivatives -/

/-- The second directional derivative of the pullback, in a standard basis
direction, is the CoarseGraining coordinate second derivative.  Unconditional. -/
theorem dirDeriv2_single_comp_toHilbert_symm (v : Vec d → ℝ) (x : Vec d) (i : Fin d) :
    dirDeriv2 (hilbertBasis d i) (v ∘ toHilbert.symm) (toHilbert x)
      = euclideanCoordSecondDeriv i i v x := by
  rw [dirDeriv2, fderiv_comp_toHilbert_symm_basis_eq v i,
    fderiv_comp_toHilbert_symm (euclideanCoordDeriv i v) (toHilbert x)]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, toHilbert_symm_basis,
    ContinuousLinearEquiv.symm_apply_apply]
  rfl

/-! ### The Laplacian dictionary -/

/-- **The Laplacian dictionary.**  For a `C²` function `v` on the CoarseGraining
coordinate carrier, mathlib's coordinate-free Laplacian of the pullback `v ∘
toHilbert.symm` at `toHilbert x` is the CoarseGraining coordinate Laplacian of `v` at
`x`.

Proof: read `Δ` in the orthonormal basis `hilbertBasis`, convert
each diagonal iterated derivative into a second directional derivative
(`iteratedFDeriv_two_eq_dirDeriv2`), and transfer each along `toHilbert`
(`dirDeriv2_single_comp_toHilbert_symm`). -/
theorem laplacian_comp_toHilbert_symm_apply {v : Vec d → ℝ} (hv : ContDiff ℝ 2 v) (x : Vec d) :
    Δ (v ∘ toHilbert.symm) (toHilbert x) = euclideanCoordLaplacian v x := by
  classical
  have hcd : ContDiff ℝ 2 (v ∘ toHilbert.symm) :=
    hv.comp (toHilbert.symm : 𝔼 ≃L[ℝ] Vec d).contDiff
  have hbasis :=
    congrFun
      (laplacian_eq_iteratedFDeriv_orthonormalBasis (v ∘ toHilbert.symm)
        (hilbertBasis d))
      (toHilbert x)
  rw [hbasis]
  simp only [euclideanCoordLaplacian]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [iteratedFDeriv_two_eq_dirDeriv2 hcd, dirDeriv2_single_comp_toHilbert_symm]

/-- Pointwise form: the coordinate Laplacian of `v` at `toHilbert.symm z`. -/
theorem euclideanCoordLaplacian_eq_laplacian_comp_toHilbert_symm {v : Vec d → ℝ}
    (hv : ContDiff ℝ 2 v) (z : 𝔼) :
    euclideanCoordLaplacian v (toHilbert.symm z) = Δ (v ∘ toHilbert.symm) z := by
  have h := laplacian_comp_toHilbert_symm_apply hv (toHilbert.symm z)
  rwa [ContinuousLinearEquiv.apply_symm_apply, eq_comm] at h


end

end PDE.Internal
