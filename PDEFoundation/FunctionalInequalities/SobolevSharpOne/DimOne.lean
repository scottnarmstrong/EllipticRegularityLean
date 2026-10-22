module

public import PDEFoundation.FunctionalInequalities.SobolevSharpOne.Density
public import PDEFoundation.Measure.BallVolume
public import PDEFoundation.Geometry.EuclideanBall
public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The one-dimensional case of the sharp `p = 1` Sobolev inequality

For `ψ ∈ C_c^1(ℝ)`, `|ψ(t)| ≤ ½ ∫ |ψ'|` by the fundamental theorem of calculus from both ends.
This is transported to `Vec 1` and combined with the density reduction.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE.SobolevSharp

open Filter MeasureTheory Set

/-- Fundamental theorem of calculus from both ends. -/
theorem two_mul_abs_le_integral_abs_deriv {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hc : HasCompactSupport g) (t : ℝ) :
    2 * |g t| ≤ ∫ s, |deriv g s| := by
  have hint : Integrable (deriv g) :=
    (hg.continuous_deriv le_rfl).integrable_of_hasCompactSupport hc.deriv
  have hint' : Integrable (fun s => |deriv g s|) := hint.abs
  have h1 : |g t| ≤ ∫ s in Iic t, |deriv g s| := by
    rw [← hc.integral_Iic_deriv_eq hg t]
    exact (abs_integral_le_integral_abs).trans_eq' rfl |>.trans_eq rfl
  have h2 : |g t| ≤ ∫ s in Ioi t, |deriv g s| := by
    have := hc.integral_Ioi_deriv_eq hg t
    calc |g t| = |∫ s in Ioi t, deriv g s| := by rw [this, abs_neg]
      _ ≤ _ := abs_integral_le_integral_abs
  have hsum := intervalIntegral.integral_Iic_add_Ioi hint'.integrableOn hint'.integrableOn (b := t)
  linarith


/-- The Euclidean norm on `Vec 1` is the absolute value of the coordinate. -/
theorem vecEuclideanNorm_fin_one (x : Vec 1) : vecEuclideanNorm x = |x 0| := by
  simp [vecEuclideanNorm, vecNormSq_eq_sum_sq, Real.sqrt_sq_eq_abs]

/-- The embedding of the line into `Vec 1`. -/
def lineEmbed (t : ℝ) : Vec 1 := fun _ => t

theorem lineEmbed_hasDerivAt (t : ℝ) : HasDerivAt lineEmbed (basisVec (0 : Fin 1)) t := by
  have h : lineEmbed = fun t : ℝ => t • basisVec (0 : Fin 1) := by
    funext t i
    have : i = 0 := Subsingleton.elim _ _
    subst this
    simp [lineEmbed, basisVec]
  rw [h]
  simpa using (hasDerivAt_id t).smul_const (basisVec (0 : Fin 1))

theorem lineEmbed_apply_zero (x : Vec 1) : lineEmbed (x 0) = x := by
  funext i
  have : i = 0 := Subsingleton.elim _ _
  subst this
  rfl

theorem isClosedEmbedding_lineEmbed : Topology.IsClosedEmbedding lineEmbed :=
  (Homeomorph.funUnique (Fin 1) ℝ).symm.isClosedEmbedding

/-- One-dimensional sup bound for compactly supported `C¹` functions on `Vec 1`. -/
theorem eLpNorm_top_le_half_of_compactSmooth (ψ : Vec 1 → ℝ) (hψ : ContDiff ℝ 1 ψ)
    (hc : HasCompactSupport ψ) :
    eLpNorm ψ ∞ volume ≤
      (1 / 2 : ℝ≥0∞) *
        eLpNorm (fun x => vecEuclideanNorm (classicalGradient ψ x)) 1 volume := by
  set g : ℝ → ℝ := fun t => ψ (lineEmbed t) with hg
  have hgdiff : ContDiff ℝ 1 g := hψ.comp (contDiff_pi.mpr fun _ => contDiff_id)
  have hgc : HasCompactSupport g := hc.comp_isClosedEmbedding isClosedEmbedding_lineEmbed
  have hderiv : ∀ t, deriv g t = fderiv ℝ ψ (lineEmbed t) (basisVec 0) := fun t =>
    (((hψ.differentiable one_ne_zero (lineEmbed t)).hasFDerivAt).comp_hasDerivAt t
      (lineEmbed_hasDerivAt t)).deriv
  have hgrad : ∀ x : Vec 1, vecEuclideanNorm (classicalGradient ψ x) = |deriv g (x 0)| := by
    intro x
    rw [vecEuclideanNorm_fin_one, hderiv, lineEmbed_apply_zero]
    rfl
  have hint : Integrable (fun s => |deriv g s|) :=
    ((hgdiff.continuous_deriv le_rfl).integrable_of_hasCompactSupport hgc.deriv).abs
  set I : ℝ := ∫ s, |deriv g s| with hI
  have hI0 : 0 ≤ I := integral_nonneg fun _ => abs_nonneg _
  have hmp := volume_preserving_funUnique (Fin 1) ℝ
  have hnorm : eLpNorm (fun x => vecEuclideanNorm (classicalGradient ψ x)) 1 volume =
      ENNReal.ofReal I := by
    have hmeas : AEStronglyMeasurable
        (fun x => vecEuclideanNorm (classicalGradient ψ x)) volume := by
      have : (fun x : Vec 1 => vecEuclideanNorm (classicalGradient ψ x)) =
          fun x => |deriv g (x 0)| := funext hgrad
      rw [this]
      exact ((hgdiff.continuous_deriv le_rfl).comp (continuous_apply 0)).abs.aestronglyMeasurable
    rw [eLpNorm_one_eq_lintegral_enorm hmeas]
    have : ∀ x : Vec 1, ‖vecEuclideanNorm (classicalGradient ψ x)‖ₑ =
        (fun t : ℝ => ENNReal.ofReal |deriv g t|) (MeasurableEquiv.funUnique (Fin 1) ℝ x) := by
      intro x
      rw [hgrad, Real.enorm_eq_ofReal_abs, abs_abs]
      rfl
    rw [lintegral_congr this]
    have h2 := hmp.lintegral_comp_emb (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding
      (fun t : ℝ => ENNReal.ofReal |deriv g t|)
    refine h2.trans ?_
    rw [hI, ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall fun _ => abs_nonneg _)]
  rw [hnorm]
  have hbound : ∀ x : Vec 1, ‖ψ x‖ ≤ I / 2 := by
    intro x
    have h := two_mul_abs_le_integral_abs_deriv hgdiff hgc (x 0)
    have hx : ψ x = g (x 0) := by simp only [hg, lineEmbed_apply_zero]
    rw [hx, Real.norm_eq_abs]
    linarith
  calc eLpNorm ψ ∞ volume ≤ ENNReal.ofReal (I / 2) := by
        refine (eLpNorm_exponent_top (f := ψ) (μ := volume) hψ.continuous.aestronglyMeasurable).le.trans ?_
        exact eLpNormEssSup_le_of_ae_bound (Eventually.of_forall hbound)
    _ = (1 / 2 : ℝ≥0∞) * ENNReal.ofReal I := by
        rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat, div_eq_mul_inv, mul_comm,
          one_div]


/-- In `Vec 1` the Euclidean unit ball is the preimage of `(-1, 1)`. -/
theorem volume_euclideanBall_fin_one :
    volume (euclideanBall (0 : Vec 1) 1) = 2 := by
  have hset : euclideanBall (0 : Vec 1) 1 =
      (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' Ioo (-1 : ℝ) 1 := by
    ext x
    simp only [euclideanBall, euclideanSqDist, mem_ofPred_eq, mem_preimage, mem_Ioo,
      MeasurableEquiv.funUnique_apply, sub_zero, vecNormSq_eq_sum_sq]
    simp only [Finset.univ_unique, Fin.default_eq_zero, Finset.sum_singleton]
    rw [one_pow, ← abs_lt]
    exact sq_lt_one_iff_abs_lt_one _
  rw [hset]
  have h := (volume_preserving_funUnique (Fin 1) ℝ).measure_preimage_equiv (Ioo (-1 : ℝ) 1)
  refine h.trans ?_
  rw [Real.volume_Ioo]
  norm_num


/-- The `d = 1` case of the sharp Sobolev inequality (Proposition 1.4), in exactly its form. -/
theorem sobolev_sharp_one_of_dim_one (d : ℕ) (hd : d = 1)
    (u : W1pFunction (Set.univ : Set (Vec d)) 1) :
    eLpNorm u.toFun ((d : ℝ≥0∞) / ((d : ℝ≥0∞) - 1)) volume ≤
      ENNReal.ofReal (((d : ℝ) * (volume (euclideanBall (0 : Vec d) 1)).toReal ^ ((1 : ℝ) / d))⁻¹) *
        eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 1 volume := by
  subst hd
  have hexp : (((1 : ℕ) : ℝ≥0∞) / (((1 : ℕ) : ℝ≥0∞) - 1)) = ∞ := by simp
  have hconst : ENNReal.ofReal ((((1 : ℕ) : ℝ) *
      (volume (euclideanBall (0 : Vec 1) 1)).toReal ^ ((1 : ℝ) / ((1 : ℕ) : ℝ)))⁻¹) =
      (1 / 2 : ℝ≥0∞) := by
    rw [volume_euclideanBall_fin_one]
    norm_num
    rw [ENNReal.ofReal_div_of_pos (by norm_num)]
    simp
  rw [hexp, hconst]
  exact eLpNorm_le_of_forall_compactSmooth (K := (1 / 2 : ℝ≥0∞)) (by simp)
    (fun ψ hψ hc => eLpNorm_top_le_half_of_compactSmooth ψ
      (hψ.of_le (by simp)) hc) u

end PDE.SobolevSharp
