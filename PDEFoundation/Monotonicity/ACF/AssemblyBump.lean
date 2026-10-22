module

public import PDEFoundation.Monotonicity.Defs
public import PDEFoundation.Geometry.EuclideanBall.Topology
public import PDEFoundation.Sobolev.Cutoff.Ball
public import PDEFoundation.Monotonicity.Core.RellichSphere

/-!
# ACF-A: a nonempty relatively open subset of the sphere has finite eigenvalue

If `U` is open and `y ∈ U ∩ ∂B₁` then `λ(U ∩ ∂B₁) ≠ ⊤`: test the Rayleigh quotient with a smooth
bump supported in a small ball around `y`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE

namespace ACFAssembly

noncomputable section

variable {d : ℕ}

theorem continuous_hilbert_toVec : Continuous (fun z : HilbertVec d => z.toVec) := by
  unfold HilbertVec.toVec
  fun_prop

theorem continuous_slice_sq {g : Vec d → ℝ} (hg : Continuous g) :
    Continuous (fun ω : Metric.sphere (0 : HilbertVec d) 1 =>
      g ((1 : ℝ) • (ω : HilbertVec d).toVec) ^ 2) := by
  have h1 : Continuous (fun ω : Metric.sphere (0 : HilbertVec d) 1 => (ω : HilbertVec d).toVec) :=
    continuous_hilbert_toVec.comp continuous_subtype_val
  have h2 : Continuous (fun ω : Metric.sphere (0 : HilbertVec d) 1 =>
      (1 : ℝ) • (ω : HilbertVec d).toVec) := by
    simp only [one_smul]; exact h1
  exact (hg.comp h2).pow 2

/-- The first Dirichlet eigenvalue of a nonempty relatively open subset of the sphere is finite. -/
theorem sphereDirichletEigenvalue_ne_top {U : Set (Vec d)} (hU : IsOpen U) {y : Vec d}
    (hy : y ∈ U) (hyS : y ∈ euclideanSphere (0 : Vec d) 1) :
    sphereDirichletEigenvalue d (U ∩ euclideanSphere (0 : Vec d) 1) ≠ ⊤ := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU y hy
  set g : Vec d → ℝ := canonicalBallCutoff y (ε / 4) (ε / 2) with hg
  have hr0 : (0 : ℝ) ≤ ε / 4 := by positivity
  have hrR : ε / 4 < ε / 2 := by linarith
  have hsm : ContDiff ℝ (⊤ : ℕ∞) g := canonicalBallCutoff_smooth y hr0 hrR
  have hcont : Continuous g := hsm.continuous
  have hts : tsupport g ⊆ euclideanBall y (ε / 2) := canonicalBallCutoff_tsupport_subset_outer hr0 hrR
  have hsub : closure {x | x ∈ euclideanSphere (0 : Vec d) 1 ∧ g x ≠ 0} ⊆
      U ∩ euclideanSphere (0 : Vec d) 1 := by
    intro x hx
    refine ⟨?_, closure_minimal (fun z hz => hz.1) (isClosed_euclideanSphere _ _) hx⟩
    have h1 : x ∈ tsupport g :=
      closure_mono (fun z hz => (Function.mem_support.2 hz.2)) hx
    exact hball (euclideanBall_subset_supBall hε
      (euclideanBall_mono (by positivity) (by linarith) (hts h1)))
  have hy1 : g y = 1 :=
    canonicalBallCutoff_eq_one_on_inner hr0 hrR (center_mem_euclideanBall y (by positivity))
  have hn : vecEuclideanNorm y = 1 := by
    have := mem_euclideanSphere_zero_iff.1 hyS
    unfold vecEuclideanNorm
    rw [this]; simp
  set ω0 : Metric.sphere (0 : HilbertVec d) 1 :=
    ⟨y.toHilbertVec, by
      rw [mem_sphere_zero_iff_norm, ← Vec.vecEuclideanNorm_eq_norm_toHilbertVec]; exact hn⟩
  have hpos : 0 < sphereIntegral (0 : Vec d) 1 (fun x => g x ^ 2) := by
    rw [sphereIntegral_zero_apply, one_pow, one_mul]
    have hc := continuous_slice_sq (d := d) hcont
    refine hc.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := ω0)
      (HasCompactSupport.of_compactSpace _) (fun ω => by positivity) ?_
    simp only [ω0, one_smul, HilbertVec.toVec_toHilbertVec, hy1]
    norm_num
  have hle : sphereDirichletEigenvalue d (U ∩ euclideanSphere (0 : Vec d) 1) ≤
      ENNReal.ofReal
        (sphereIntegral (0 : Vec d) 1 (tangentialGradientNormSq g) /
          sphereIntegral (0 : Vec d) 1 (fun x => g x ^ 2)) := by
    unfold sphereDirichletEigenvalue
    exact iInf_le_of_le g (iInf_le_of_le ⟨hsm.of_le (by exact_mod_cast le_top), hsub, hpos⟩ le_rfl)
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle

end

end ACFAssembly

end PDE
