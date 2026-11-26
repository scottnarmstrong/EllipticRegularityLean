module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import BSlocalmax.CubeBasics
public import PDEFoundation.Ambient.Basis
public import PDEFoundation.Ambient.EuclideanNorm
public import PDEFoundation.Geometry.AxisCube
public import PDEFoundation.Measure.NormalizedLp
public import PDEFoundation.Sobolev.ClassicalGradient
public import PDEFoundation.Sobolev.ClassicalOnOpenWeakGradient
public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.Sobolev.Inequalities.ConvexSobolevPoincareAffine
public import PDEFoundation.Sobolev.Mean
public import SobolevStatements.ConvexSobolevPoincare

/-!
# Sobolev inequalities on cube faces and on cubes

This file collects the following pieces, in dependency order: FaceSobolev, FaceSobolev2, FaceGradient, BoundarySobolev, Trunc, SobolevH1, SobolevCube.
-/

-- ==== from FaceSobolev.lean ====
-- Part 1 of `face_sobolev`:
-- Sobolev inequality (not mean-free) for C¹ functions on bounded convex domains,
-- in the normalized ENNReal form of the repository:
--   ‖g‖_{L^{2*}(V)}^{mean} ≤ C D ‖∇g‖_{L²}^{mean} + ‖g‖_{L²}^{mean}.


@[expose] public section

open scoped ENNReal
open MeasureTheory Set PDE

namespace PDE.BSlocalmax

/-- Continuous functions on bounded sets lie in every `L^p`. -/
lemma memLpOn_of_continuous {d : ℕ} {V : Set (Vec d)} (hVo : IsOpen V)
    (hVb : Bornology.IsBounded V) {f : Vec d → ℝ} (hf : Continuous f) (p : ℝ≥0∞) :
    MemLpOn V p f := by
  obtain ⟨B, hB⟩ := hVb.isCompact_closure.exists_bound_of_continuousOn hf.continuousOn
  have : IsFiniteMeasure (volumeOn V) :=
    ⟨by rw [volumeOn, Measure.restrict_apply_univ]; exact hVb.measure_lt_top⟩
  refine MemLp.of_bound hf.aestronglyMeasurable B ?_
  rw [volumeOn, ae_restrict_iff' hVo.measurableSet]
  exact Filter.Eventually.of_forall (fun x hx => hB x (subset_closure hx))

/-- A `C¹` function on `ℝ^d` is `W^{1,p}` on a bounded open set. -/
noncomputable def w1pOfContDiff {d : ℕ} {V : Set (Vec d)} (hVo : IsOpen V)
    (hVb : Bornology.IsBounded V) {g : Vec d → ℝ} (hg : ContDiff ℝ 1 g) (p : ℝ≥0∞) :
    W1pFunction V p where
  toFun := g
  grad := classicalGradient g
  memLp := memLpOn_of_continuous hVo hVb hg.continuous p
  gradMemLp := by
    intro i
    have : Continuous (fun x => classicalGradient g x i) := by
      simpa [classicalGradient_apply] using
        (hg.continuous_fderiv (by simp)).clm_apply continuous_const
    exact memLpOn_of_continuous hVo hVb this p
  hasWeakGradient := HasWeakGradientOn.of_contDiffOn hVo hg.contDiffOn

/-- **Normalized Sobolev inequality for `C¹` functions** (not mean-free),
`p = 2`, `d ≥ 3`. -/
theorem meanNorm_sobolev_le (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Set (Vec d)) (D : ℝ), IsOpenBoundedConvexDomain V → V.Nonempty →
      HasEuclideanDiameterLE V D → ∀ g : Vec d → ℝ, ContDiff ℝ 1 g →
        eLpMeanNormOn V (ENNReal.ofReal (sobolevConjugate d 2)) g ≤
          ENNReal.ofReal (C * D) *
              euclideanFieldELpMeanNormOn V (ENNReal.ofReal 2) (classicalGradient g) +
            eLpMeanNormOn V (ENNReal.ofReal 2) g := by
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨C₀, hC₀, hC⟩ := exists_convexSobolevPoincare_constant d (by omega)
  refine ⟨C₀ * (2 * ((d : ℝ) - 1) / ((d : ℝ) - 2)),
    mul_pos hC₀ (div_pos (by linarith) (by linarith)), ?_⟩
  intro V D hV hne hD g hg
  obtain ⟨hVpos, hVtop⟩ := volume_pos_lt_top_of_isOpenBoundedConvexDomain hV hne
  have hprob : IsProbabilityMeasure (normalizedVolumeOn V) :=
    isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top hVpos hVtop
  let u : W1pFunction V (ENNReal.ofReal 2) :=
    w1pOfContDiff hV.isOpen hV.isBoundedDomain.isBounded hg _
  have h := hC 2 (by norm_num) (by exact_mod_cast (by omega : 2 < d)) V D hV hne hD u
  -- Mean value
  have hq1 : 1 ≤ ENNReal.ofReal (sobolevConjugate d 2) := by
    rw [ENNReal.one_le_ofReal, sobolevConjugate, le_div_iff₀ (by linarith)]
    linarith
  have hgm : AEStronglyMeasurable g (normalizedVolumeOn V) := hg.continuous.aestronglyMeasurable
  have havg : integralAverage V g = ∫ x, g x ∂(normalizedVolumeOn V) := by
    rw [normalizedVolumeOn, integral_smul_measure, ENNReal.toReal_inv, integralAverage]
    try rfl
  have hdecomp : g = (fun x => g x - integralAverage V g) + fun _ => integralAverage V g := by
    funext x; simp
  have hmink : eLpMeanNormOn V (ENNReal.ofReal (sobolevConjugate d 2)) g ≤
      eLpMeanNormOn V (ENNReal.ofReal (sobolevConjugate d 2))
        (fun x => g x - integralAverage V g) +
      eLpNorm (fun _ => integralAverage V g) (ENNReal.ofReal (sobolevConjugate d 2))
        (normalizedVolumeOn V) := by
    unfold eLpMeanNormOn
    conv_lhs => rw [hdecomp]
    exact eLpNorm_add_le hq1
  have hconst : eLpNorm (fun _ => integralAverage V g) (ENNReal.ofReal (sobolevConjugate d 2))
      (normalizedVolumeOn V) = ‖integralAverage V g‖ₑ := by
    have hqpos : 0 < sobolevConjugate d 2 := by
      unfold sobolevConjugate; exact div_pos (by linarith) (by linarith)
    rw [eLpNorm_const' _ (ENNReal.ofReal_pos.2 hqpos).ne' ENNReal.ofReal_ne_top, measure_univ,
      ENNReal.one_rpow, mul_one]
  have havg_le : ‖integralAverage V g‖ₑ ≤ eLpMeanNormOn V (ENNReal.ofReal 2) g := by
    rw [havg]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    rw [← eLpNorm_one_eq_lintegral_enorm hgm]
    unfold eLpMeanNormOn
    exact eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.one_le_ofReal.2 (by norm_num))
  have hu : (fun x => u.toFun x - integralAverage V u.toFun) =
      fun x => g x - integralAverage V g := rfl
  have hug : u.grad = classicalGradient g := rfl
  rw [hu, hug] at h
  rw [hconst] at hmink
  calc eLpMeanNormOn V (ENNReal.ofReal (sobolevConjugate d 2)) g
      ≤ _ := hmink
    _ ≤ _ := add_le_add h havg_le

end PDE.BSlocalmax
end

-- ==== from FaceSobolev2.lean ====
-- Part 2 of `face_sobolev`:
-- real form of the Sobolev inequality on the cube [-r,r]^n, constant uniform in r ∈ [1/2,1].


@[expose] public section

open scoped ENNReal
open MeasureTheory Set PDE

namespace PDE.BSlocalmax

/-- Continuity of the norm of the classical gradient. -/
lemma continuous_gradNorm {d : ℕ} {g : Vec d → ℝ} (hg : ContDiff ℝ 1 g) :
    Continuous (fun x => vecEuclideanNorm (classicalGradient g x)) := by
  have hc : ∀ i, Continuous (fun x => classicalGradient g x i) := by
    intro i
    simpa [classicalGradient_apply] using
      (hg.continuous_fderiv (by simp)).clm_apply continuous_const
  unfold vecEuclideanNorm vecNormSq vecDot
  exact (continuous_finsetSum _ (fun i _ => (hc i).mul (hc i))).sqrt

/-- Real value of the unnormalized `L^p` norm of a continuous function. -/
lemma toReal_eLpNormOn {d : ℕ} {U : Set (Vec d)} {f : Vec d → ℝ} (hf : Continuous f)
    {p : ℝ} (hp : 0 < p) :
    (eLpNormOn U (ENNReal.ofReal p) f).toReal = (∫ x in U, |f x| ^ p) ^ (1 / p) := by
  unfold eLpNormOn
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hp).ne'
    ENNReal.ofReal_ne_top hf.aestronglyMeasurable, ENNReal.toReal_ofReal hp.le,
    ← ENNReal.toReal_rpow]
  congr 1
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => by positivity)
    ((hf.abs.rpow_const (fun x => Or.inr hp.le)).aestronglyMeasurable)]
  congr 1
  refine lintegral_congr (fun x => ?_)
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le]

/-- Real value of the normalized `L^p` norm of a continuous function. -/
lemma toReal_eLpMeanNormOn {d : ℕ} {U : Set (Vec d)} (hUtop : volume U < ∞)
    {f : Vec d → ℝ} (hf : Continuous f) {p : ℝ} (hp : 0 < p) :
    (eLpMeanNormOn U (ENNReal.ofReal p) f).toReal =
      ((volume U).toReal)⁻¹ ^ (1 / p) * (∫ x in U, |f x| ^ p) ^ (1 / p) := by
  rw [eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn hUtop, ENNReal.toReal_mul,
    toReal_eLpNormOn hf hp]
  congr 1
  have h1p : (1 / ENNReal.ofReal p).toReal = 1 / p := by
    rw [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofReal hp.le, one_div]
  rw [h1p, ← ENNReal.toReal_rpow, ENNReal.toReal_inv]

/-- Normalized norms of continuous functions on bounded open sets are finite. -/
lemma eLpMeanNormOn_ne_top {d : ℕ} {V : Set (Vec d)} (hVo : IsOpen V)
    (hVb : Bornology.IsBounded V) (hVpos : 0 < volume V) {f : Vec d → ℝ}
    (hf : Continuous f) (p : ℝ≥0∞) : eLpMeanNormOn V p f ≠ ∞ :=
  (memLp_normalizedVolumeOn_of_memLpOn (memLpOn_of_continuous hVo hVb hf p) hVpos).eLpNorm_lt_top.ne

/-- Real Sobolev inequality on arbitrary bounded open convex domains (`p = 2`). -/
theorem sobolev_real_domain (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Set (Vec d)) (D : ℝ), IsOpenBoundedConvexDomain V → V.Nonempty →
      HasEuclideanDiameterLE V D → ∀ g : Vec d → ℝ, ContDiff ℝ 1 g →
      (∫ x in V, |g x| ^ sobolevConjugate d 2) ^ (1 / sobolevConjugate d 2) ≤
        ((volume V).toReal) ^ (1 / sobolevConjugate d 2 - 1 / 2) *
          (C * D * (∫ x in V, vecNormSq (classicalGradient g x)) ^ (1 / 2 : ℝ) +
            (∫ x in V, g x ^ 2) ^ (1 / 2 : ℝ)) := by
  obtain ⟨C, hC, hmain⟩ := meanNorm_sobolev_le d hd
  refine ⟨C, hC, ?_⟩
  intro V D hV hne hD g hg
  obtain ⟨hvpos, hvtop⟩ := volume_pos_lt_top_of_isOpenBoundedConvexDomain hV hne
  have hD0 : 0 ≤ D := hD.nonneg hne
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hqpos : 0 < sobolevConjugate d 2 := by
    unfold sobolevConjugate; exact div_pos (by linarith) (by linarith)
  have hvr : 0 < (volume V).toReal := ENNReal.toReal_pos hvpos.ne' hvtop.ne
  have hgrad := continuous_gradNorm hg
  have hfin1 : eLpMeanNormOn V (ENNReal.ofReal 2) g ≠ ∞ :=
    eLpMeanNormOn_ne_top hV.isOpen hV.isBoundedDomain.isBounded hvpos hg.continuous _
  have hfin2 : euclideanFieldELpMeanNormOn V (ENNReal.ofReal 2) (classicalGradient g) ≠ ∞ :=
    eLpMeanNormOn_ne_top hV.isOpen hV.isBoundedDomain.isBounded hvpos hgrad _
  have hfin3 : ENNReal.ofReal (C * D) *
      euclideanFieldELpMeanNormOn V (ENNReal.ofReal 2) (classicalGradient g) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin2
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin3, hfin1⟩)
    (hmain V D hV hne hD g hg)
  have hint1 : ∫ x in V, |vecEuclideanNorm (classicalGradient g x)| ^ (2 : ℝ) =
      ∫ x in V, vecNormSq (classicalGradient g x) :=
    setIntegral_congr_fun hV.isOpen.measurableSet (fun x _ => by
      rw [Real.rpow_two, sq_abs, vecEuclideanNorm_sq])
  have hint2 : ∫ x in V, |g x| ^ (2 : ℝ) = ∫ x in V, g x ^ 2 :=
    setIntegral_congr_fun hV.isOpen.measurableSet (fun x _ => by
      rw [Real.rpow_two, sq_abs])
  have hB : (euclideanFieldELpMeanNormOn V (ENNReal.ofReal 2) (classicalGradient g)).toReal =
      ((volume V).toReal)⁻¹ ^ (1 / 2 : ℝ) *
        (∫ x in V, vecNormSq (classicalGradient g x)) ^ (1 / 2 : ℝ) := by
    unfold euclideanFieldELpMeanNormOn
    rw [toReal_eLpMeanNormOn hvtop hgrad (by norm_num : (0 : ℝ) < 2), hint1]
  have hE : (eLpMeanNormOn V (ENNReal.ofReal 2) g).toReal =
      ((volume V).toReal)⁻¹ ^ (1 / 2 : ℝ) * (∫ x in V, g x ^ 2) ^ (1 / 2 : ℝ) := by
    rw [toReal_eLpMeanNormOn hvtop hg.continuous (by norm_num : (0 : ℝ) < 2), hint2]
  rw [ENNReal.toReal_add hfin3 hfin1, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (mul_nonneg hC.le hD0),
    toReal_eLpMeanNormOn hvtop hg.continuous hqpos, hB, hE] at h
  have ha : 0 < (volume V).toReal ^ (1 / sobolevConjugate d 2) := Real.rpow_pos_of_pos hvr _
  have hmul : (volume V).toReal ^ (1 / sobolevConjugate d 2) *
      ((volume V).toReal)⁻¹ ^ (1 / sobolevConjugate d 2) = 1 := by
    rw [Real.inv_rpow hvr.le, mul_inv_cancel₀ ha.ne']
  have hsub : (volume V).toReal ^ (1 / sobolevConjugate d 2 - 1 / 2) =
      (volume V).toReal ^ (1 / sobolevConjugate d 2) * ((volume V).toReal)⁻¹ ^ (1 / 2 : ℝ) := by
    rw [Real.rpow_sub hvr, Real.inv_rpow hvr.le, div_eq_mul_inv]
  calc (∫ x in V, |g x| ^ sobolevConjugate d 2) ^ (1 / sobolevConjugate d 2)
      = (volume V).toReal ^ (1 / sobolevConjugate d 2) *
          (((volume V).toReal)⁻¹ ^ (1 / sobolevConjugate d 2) *
            (∫ x in V, |g x| ^ sobolevConjugate d 2) ^ (1 / sobolevConjugate d 2)) := by
        rw [← mul_assoc, hmul, one_mul]
    _ ≤ (volume V).toReal ^ (1 / sobolevConjugate d 2) *
          (C * D * (((volume V).toReal)⁻¹ ^ (1 / 2 : ℝ) *
              (∫ x in V, vecNormSq (classicalGradient g x)) ^ (1 / 2 : ℝ)) +
            ((volume V).toReal)⁻¹ ^ (1 / 2 : ℝ) * (∫ x in V, g x ^ 2) ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left h ha.le
    _ = _ := by rw [hsub]; ring

lemma axisCube_eq_pi_Ioo {n : ℕ} (r : ℝ) :
    axisCube (fun _ : Fin n => -r) (2 * r) = Set.pi Set.univ (fun _ : Fin n => Ioo (-r) r) := by
  have e : -r + 2 * r = r := by ring
  simp only [axisCube, e]

/-- Scale-invariant Sobolev inequality on the open cube `(-r,r)^n`. -/
theorem face_sobolev_cube {n : ℕ} (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → ∀ g : Vec n → ℝ, ContDiff ℝ 1 g →
      (∫ y in axisCube (fun _ : Fin n => -r) (2 * r), |g y| ^ ((2 * n : ℝ) / (n - 2))) ^
          (((n : ℝ) - 2) / (2 * n)) ≤
        C * (∫ y in axisCube (fun _ : Fin n => -r) (2 * r),
            vecNormSq (classicalGradient g y)) ^ (1 / 2 : ℝ) +
          (2 * r)⁻¹ * (∫ y in axisCube (fun _ : Fin n => -r) (2 * r), g y ^ 2) ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hmain⟩ := sobolev_real_domain n hn
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < n).ne'
  refine ⟨C * Real.sqrt n, mul_pos hC (Real.sqrt_pos.2 (by linarith)), ?_⟩
  intro r hr g hg
  have ht : (0 : ℝ) < 2 * r := by linarith
  have hV := isOpenBoundedConvexDomain_axisCube (fun _ : Fin n => -r) (2 * r)
  have hne := axisCube_nonempty (fun _ : Fin n => -r) ht
  have hD := hasEuclideanDiameterLE_axisCube (fun _ : Fin n => -r) ht.le
  have h := hmain _ _ hV hne hD g hg
  have hvol : (volume (axisCube (fun _ : Fin n => -r) (2 * r))).toReal = (2 * r) ^ n := by
    have e := Real.volume_pi_Ioo_toReal (a := fun _ : Fin n => -r) (b := fun _ : Fin n => -r + 2 * r)
      (fun i => by show -r ≤ -r + 2 * r; linarith)
    have e2 : (volume (axisCube (fun _ : Fin n => -r) (2 * r))).toReal =
        ∏ _i : Fin n, ((-r + 2 * r) - (-r)) := e
    rw [e2]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    ring
  have hs : (n : ℝ) * (1 / sobolevConjugate n 2 - 1 / 2) = -1 := by
    unfold sobolevConjugate
    rw [one_div_div]
    field_simp
    ring
  have hv : ((2 * r) ^ n) ^ (1 / sobolevConjugate n 2 - 1 / 2) = (2 * r)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le, hs, Real.rpow_neg_one]
  have hq : sobolevConjugate n 2 = (2 * n : ℝ) / (n - 2) := by
    unfold sobolevConjugate; ring
  rw [hvol, hv, hq, one_div_div] at h
  have key : ∀ X : ℝ, (2 * r)⁻¹ * (C * (Real.sqrt n * (2 * r)) * X) = C * Real.sqrt n * X := by
    intro X
    calc (2 * r)⁻¹ * (C * (Real.sqrt n * (2 * r)) * X)
        = (C * Real.sqrt n * X) * ((2 * r)⁻¹ * (2 * r)) := by ring
      _ = C * Real.sqrt n * X := by rw [inv_mul_cancel₀ ht.ne', mul_one]
  refine h.trans (le_of_eq ?_)
  rw [mul_add, key]

/-- **Sobolev on a single face** (dimension `n ≥ 3`, `2* = 2n/(n-2)`).
Constant uniform for `r ∈ [1/2, 1]`. -/
theorem face_sobolev {n : ℕ} (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ r ∈ Icc (1 / 2 : ℝ) 1, ∀ g : Vec n → ℝ, ContDiff ℝ 1 g →
      (∫ y in Set.pi Set.univ (fun _ : Fin n => Set.Icc (-r) r),
          |g y| ^ ((2 * n : ℝ) / (n - 2))) ^ (((n : ℝ) - 2) / (2 * n)) ≤
        C * (∫ y in Set.pi Set.univ (fun _ : Fin n => Set.Icc (-r) r),
          (g y ^ 2 + vecNormSq (classicalGradient g y))) ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hcube⟩ := face_sobolev_cube hn
  refine ⟨C + 1, by linarith, ?_⟩
  intro r hr g hg
  have hr0 : 0 < r := by linarith [hr.1]
  have h := hcube r hr0 g hg
  have hae : axisCube (fun _ : Fin n => -r) (2 * r) =ᵐ[volume]
      Set.pi Set.univ (fun _ : Fin n => Icc (-r) r) := by
    rw [axisCube_eq_pi_Ioo]
    exact Measure.pi_Ioo_ae_eq_pi_Icc
  rw [setIntegral_congr_set hae, setIntegral_congr_set hae, setIntegral_congr_set hae] at h
  have hKc : IsCompact (Set.pi Set.univ (fun _ : Fin n => Icc (-r) r)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hKm : MeasurableSet (Set.pi Set.univ (fun _ : Fin n => Icc (-r) r)) :=
    MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have hc2 : Continuous (fun y => vecNormSq (classicalGradient g y)) := by
    refine ((continuous_gradNorm hg).pow 2).congr (fun y => ?_)
    show vecEuclideanNorm (classicalGradient g y) ^ 2 = _
    exact vecEuclideanNorm_sq _
  have hI1 : IntegrableOn (fun y => g y ^ 2) (Set.pi Set.univ (fun _ : Fin n => Icc (-r) r)) :=
    (hg.continuous.pow 2).continuousOn.integrableOn_compact hKc
  have hI2 : IntegrableOn (fun y => vecNormSq (classicalGradient g y))
      (Set.pi Set.univ (fun _ : Fin n => Icc (-r) r)) :=
    hc2.continuousOn.integrableOn_compact hKc
  have hsum := integral_add hI1 hI2
  have hE0 : 0 ≤ ∫ y in Set.pi Set.univ (fun _ : Fin n => Icc (-r) r), g y ^ 2 :=
    setIntegral_nonneg hKm (fun y _ => sq_nonneg _)
  have hB0 : 0 ≤ ∫ y in Set.pi Set.univ (fun _ : Fin n => Icc (-r) r),
      vecNormSq (classicalGradient g y) :=
    setIntegral_nonneg hKm (fun y _ => by rw [← vecEuclideanNorm_sq]; exact sq_nonneg _)
  have hB' : (∫ y in Set.pi Set.univ (fun _ : Fin n => Icc (-r) r),
      vecNormSq (classicalGradient g y)) ^ (1 / 2 : ℝ) ≤
      (∫ y in Set.pi Set.univ (fun _ : Fin n => Icc (-r) r),
        (g y ^ 2 + vecNormSq (classicalGradient g y))) ^ (1 / 2 : ℝ) := by
    rw [hsum]
    exact Real.rpow_le_rpow hB0 (by linarith) (by norm_num)
  have hE' : (∫ y in Set.pi Set.univ (fun _ : Fin n => Icc (-r) r), g y ^ 2) ^ (1 / 2 : ℝ) ≤
      (∫ y in Set.pi Set.univ (fun _ : Fin n => Icc (-r) r),
        (g y ^ 2 + vecNormSq (classicalGradient g y))) ^ (1 / 2 : ℝ) := by
    rw [hsum]
    exact Real.rpow_le_rpow hE0 (by linarith) (by norm_num)
  have hle : (2 * r)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [hr.1])
  calc _ ≤ _ := h
    _ ≤ C * (∫ y in Set.pi Set.univ (fun _ : Fin n => Icc (-r) r),
          (g y ^ 2 + vecNormSq (classicalGradient g y))) ^ (1 / 2 : ℝ) +
        1 * (∫ y in Set.pi Set.univ (fun _ : Fin n => Icc (-r) r),
          (g y ^ 2 + vecNormSq (classicalGradient g y))) ^ (1 / 2 : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left hB' hC.le)
        (mul_le_mul hle hE' (Real.rpow_nonneg hE0 _) zero_le_one)
    _ = _ := by ring

end PDE.BSlocalmax
end

-- ==== from FaceGradient.lean ====
-- Gradient of a restriction to a face:
--   ψ(y) = u(insertNth i c y)  ⇒  |∇ψ(y)|² ≤ |∇u(insertNth i c y)|².


@[expose] public section

open PDE

namespace PDE.BSlocalmax

variable {n : ℕ}

lemma insertNth_eq_sum (i : Fin (n + 1)) (c : ℝ) (y : Fin n → ℝ) :
    (Fin.insertNth i c y : Vec (n + 1)) =
      c • basisVec i + ∑ j, y j • basisVec (i.succAbove j) := by
  have hne : ∀ j : Fin n, i ≠ i.succAbove j := fun j => (Fin.succAbove_ne i j).symm
  funext k
  refine Fin.succAboveCases i ?_ ?_ k
  · simp [basisVec, Pi.single_apply, hne]
  · intro m
    simp [basisVec, Pi.single_apply, Fin.succAbove_right_inj]

/-- Derivative of the affine embedding `y ↦ insertNth i c y`. -/
noncomputable def faceDeriv (i : Fin (n + 1)) : (Fin n → ℝ) →L[ℝ] Vec (n + 1) :=
  ∑ j, (ContinuousLinearMap.proj j : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (basisVec (i.succAbove j))

lemma faceDeriv_apply (i : Fin (n + 1)) (y : Fin n → ℝ) :
    faceDeriv i y = ∑ j, y j • basisVec (i.succAbove j) := by
  simp [faceDeriv]

lemma faceMap_eq (i : Fin (n + 1)) (c : ℝ) :
    (fun y : Fin n → ℝ => (Fin.insertNth i c y : Vec (n + 1))) =
      fun y => c • basisVec i + faceDeriv i y := by
  funext y
  rw [insertNth_eq_sum, faceDeriv_apply]

lemma hasFDerivAt_faceMap (i : Fin (n + 1)) (c : ℝ) (y : Fin n → ℝ) :
    HasFDerivAt (fun y : Fin n → ℝ => (Fin.insertNth i c y : Vec (n + 1))) (faceDeriv i) y := by
  rw [faceMap_eq]
  exact (faceDeriv i).hasFDerivAt.const_add _

lemma contDiff_faceMap (i : Fin (n + 1)) (c : ℝ) :
    ContDiff ℝ 1 (fun y : Fin n → ℝ => (Fin.insertNth i c y : Vec (n + 1))) := by
  rw [faceMap_eq]
  exact contDiff_const.add (faceDeriv i).contDiff

lemma contDiff_comp_face {u : Vec (n + 1) → ℝ} (hu : ContDiff ℝ 1 u) (i : Fin (n + 1)) (c : ℝ) :
    ContDiff ℝ 1 (fun y : Fin n → ℝ => u (Fin.insertNth i c y)) :=
  hu.comp (contDiff_faceMap i c)

lemma classicalGradient_face {u : Vec (n + 1) → ℝ} (hu : ContDiff ℝ 1 u) (i : Fin (n + 1))
    (c : ℝ) (y : Fin n → ℝ) (j : Fin n) :
    classicalGradient (fun y : Fin n → ℝ => u (Fin.insertNth i c y)) y j =
      classicalGradient u (Fin.insertNth i c y) (i.succAbove j) := by
  have hu' : DifferentiableAt ℝ u (Fin.insertNth i c y : Vec (n + 1)) :=
    (hu.differentiable (by simp)) _
  have h := hu'.hasFDerivAt.comp y (hasFDerivAt_faceMap i c y)
  have h2 : fderiv ℝ (fun y : Fin n → ℝ => u (Fin.insertNth i c y)) y =
      (fderiv ℝ u (Fin.insertNth i c y : Vec (n + 1))).comp (faceDeriv i) := h.fderiv
  rw [classicalGradient_apply, h2, ContinuousLinearMap.comp_apply, classicalGradient_apply,
    faceDeriv_apply, Finset.sum_eq_single j]
  · simp [basisVec]
  · intro k _ hk
    simp [basisVec, Pi.single_apply, hk]
  · simp

lemma vecNormSq_face_le {u : Vec (n + 1) → ℝ} (hu : ContDiff ℝ 1 u) (i : Fin (n + 1)) (c : ℝ)
    (y : Fin n → ℝ) :
    vecNormSq (classicalGradient (fun y : Fin n → ℝ => u (Fin.insertNth i c y)) y) ≤
      vecNormSq (classicalGradient u (Fin.insertNth i c y)) := by
  unfold vecNormSq vecDot
  simp only [classicalGradient_face hu i c y]
  rw [Fin.sum_univ_succAbove _ i]
  have : 0 ≤ classicalGradient u (Fin.insertNth i c y) i *
      classicalGradient u (Fin.insertNth i c y) i := mul_self_nonneg _
  linarith

end PDE.BSlocalmax
end

-- ==== from BoundarySobolev.lean ====
-- Sobolev on the cube boundaries, integrated over the shell:
--   ∫_ρ^σ (∫_{∂Q_r} |u|^{2*})^{2/2*} dr ≤ C ∫_{Q_σ∖Q_ρ} (u² + |∇u|²).


@[expose] public section

open MeasureTheory Set PDE

namespace PDE.BSlocalmax

/-- Subadditivity of `t ↦ t^δ` (`0 < δ ≤ 1`) over finite sums of nonnegative terms. -/
lemma rpow_sum_le {ι : Type*} (s : Finset ι) (F : ι → ℝ) (hF : ∀ i ∈ s, 0 ≤ F i) {δ : ℝ}
    (h0 : 0 < δ) (h1 : δ ≤ 1) : (∑ i ∈ s, F i) ^ δ ≤ ∑ i ∈ s, F i ^ δ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Real.zero_rpow h0.ne']
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have hFa : 0 ≤ F a := hF a (Finset.mem_insert_self a s)
    have hs : 0 ≤ ∑ i ∈ s, F i :=
      Finset.sum_nonneg (fun i hi => hF i (Finset.mem_insert_of_mem hi))
    calc (F a + ∑ i ∈ s, F i) ^ δ ≤ F a ^ δ + (∑ i ∈ s, F i) ^ δ :=
          Real.rpow_add_le_add_rpow hFa hs h0.le h1
      _ ≤ _ := add_le_add le_rfl (ih (fun i hi => hF i (Finset.mem_insert_of_mem hi)))

lemma vecNormSq_nonneg' {d : ℕ} (x : Vec d) : 0 ≤ vecNormSq x := by
  rw [← vecEuclideanNorm_sq]; exact sq_nonneg _

lemma continuous_vecNormSq_grad {d : ℕ} {g : Vec d → ℝ} (hg : ContDiff ℝ 1 g) :
    Continuous (fun y => vecNormSq (classicalGradient g y)) := by
  refine ((continuous_gradNorm hg).pow 2).congr (fun y => ?_)
  show vecEuclideanNorm (classicalGradient g y) ^ 2 = _
  exact vecEuclideanNorm_sq _

/-- Sobolev on a single face, with `δ = (n-2)/n`. -/
lemma face_bound {n : ℕ} (hn : 3 ≤ n) {Cf : ℝ}
    (hfs : ∀ r ∈ Icc (1 / 2 : ℝ) 1, ∀ g : Vec n → ℝ, ContDiff ℝ 1 g →
      (∫ y in Set.pi Set.univ (fun _ : Fin n => Set.Icc (-r) r),
          |g y| ^ ((2 * n : ℝ) / (n - 2))) ^ (((n : ℝ) - 2) / (2 * n)) ≤
        Cf * (∫ y in Set.pi Set.univ (fun _ : Fin n => Set.Icc (-r) r),
          (g y ^ 2 + vecNormSq (classicalGradient g y))) ^ (1 / 2 : ℝ))
    {u : Vec (n + 1) → ℝ} (hu : ContDiff ℝ 1 u) (i : Fin (n + 1)) (s : ℝ) {r : ℝ}
    (hr : r ∈ Icc (1 / 2 : ℝ) 1) :
    (faceIntegral i s r (fun x => |u x| ^ ((2 * n : ℝ) / (n - 2)))) ^ (((n : ℝ) - 2) / n) ≤
      Cf ^ 2 * faceIntegral i s r (fun x => u x ^ 2 + vecNormSq (classicalGradient u x)) := by
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := (by linarith : (0 : ℝ) < n).ne'
  have hr0 : 0 ≤ r := by linarith [hr.1]
  have hKm : MeasurableSet (Set.pi Set.univ (fun _ : Fin n => Icc (-r) r)) :=
    MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have hKc : IsCompact (Set.pi Set.univ (fun _ : Fin n => Icc (-r) r)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hgu := contDiff_comp_face hu i (s * r)
  have h1 := hfs r hr (fun y => u (Fin.insertNth i (s * r) y)) hgu
  have hF0 : 0 ≤ ∫ y in Set.pi Set.univ (fun _ : Fin n => Icc (-r) r),
      |u (Fin.insertNth i (s * r) y)| ^ ((2 * n : ℝ) / (n - 2)) :=
    setIntegral_nonneg hKm (fun y _ => Real.rpow_nonneg (abs_nonneg _) _)
  have hH0 : 0 ≤ ∫ y in Set.pi Set.univ (fun _ : Fin n => Icc (-r) r),
      (u (Fin.insertNth i (s * r) y) ^ 2 +
        vecNormSq (classicalGradient (fun y => u (Fin.insertNth i (s * r) y)) y)) :=
    setIntegral_nonneg hKm (fun y _ => add_nonneg (sq_nonneg _) (vecNormSq_nonneg' _))
  have hmono : (∫ y in Set.pi Set.univ (fun _ : Fin n => Icc (-r) r),
      (u (Fin.insertNth i (s * r) y) ^ 2 +
        vecNormSq (classicalGradient (fun y => u (Fin.insertNth i (s * r) y)) y))) ≤
      faceIntegral i s r (fun x => u x ^ 2 + vecNormSq (classicalGradient u x)) := by
    unfold faceIntegral
    have hc1 : Continuous (fun y : Fin n → ℝ =>
        u (Fin.insertNth i (s * r) y) ^ 2 +
          vecNormSq (classicalGradient (fun y => u (Fin.insertNth i (s * r) y)) y)) :=
      (hgu.continuous.pow 2).add (continuous_vecNormSq_grad hgu)
    have hc2 : Continuous (fun y : Fin n → ℝ =>
        u (Fin.insertNth i (s * r) y) ^ 2 +
          vecNormSq (classicalGradient u (Fin.insertNth i (s * r) y))) :=
      ((hu.continuous.comp (contDiff_faceMap i (s * r)).continuous).pow 2).add
        ((continuous_vecNormSq_grad hu).comp (contDiff_faceMap i (s * r)).continuous)
    refine setIntegral_mono_on (hc1.continuousOn.integrableOn_compact hKc)
      (hc2.continuousOn.integrableOn_compact hKc) hKm (fun y _ => ?_)
    exact add_le_add le_rfl (vecNormSq_face_le hu i (s * r) y)
  have hδ : ((n : ℝ) - 2) / n = ((n : ℝ) - 2) / (2 * n) * 2 := by
    field_simp
  have hsq : ((∫ y in Set.pi Set.univ (fun _ : Fin n => Icc (-r) r),
      (u (Fin.insertNth i (s * r) y) ^ 2 +
        vecNormSq (classicalGradient (fun y => u (Fin.insertNth i (s * r) y)) y))) ^ (1 / 2 : ℝ)) ^ 2 =
      ∫ y in Set.pi Set.univ (fun _ : Fin n => Icc (-r) r),
      (u (Fin.insertNth i (s * r) y) ^ 2 +
        vecNormSq (classicalGradient (fun y => u (Fin.insertNth i (s * r) y)) y)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hH0]
    norm_num
  show (∫ y in Set.pi Set.univ (fun _ : Fin n => Icc (-r) r),
      |u (Fin.insertNth i (s * r) y)| ^ ((2 * n : ℝ) / (n - 2))) ^ (((n : ℝ) - 2) / n) ≤ _
  calc (∫ y in Set.pi Set.univ (fun _ : Fin n => Icc (-r) r),
        |u (Fin.insertNth i (s * r) y)| ^ ((2 * n : ℝ) / (n - 2))) ^ (((n : ℝ) - 2) / n)
      = ((∫ y in Set.pi Set.univ (fun _ : Fin n => Icc (-r) r),
        |u (Fin.insertNth i (s * r) y)| ^ ((2 * n : ℝ) / (n - 2))) ^
          (((n : ℝ) - 2) / (2 * n))) ^ 2 := by
        rw [hδ, Real.rpow_mul hF0, Real.rpow_two]
    _ ≤ (Cf * (∫ y in Set.pi Set.univ (fun _ : Fin n => Icc (-r) r),
          (u (Fin.insertNth i (s * r) y) ^ 2 +
            vecNormSq (classicalGradient (fun y => u (Fin.insertNth i (s * r) y)) y))) ^
              (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (Real.rpow_nonneg hF0 _) h1 2
    _ = Cf ^ 2 * ∫ y in Set.pi Set.univ (fun _ : Fin n => Icc (-r) r),
          (u (Fin.insertNth i (s * r) y) ^ 2 +
            vecNormSq (classicalGradient (fun y => u (Fin.insertNth i (s * r) y)) y)) := by
        rw [mul_pow, hsq]
    _ ≤ _ := mul_le_mul_of_nonneg_left hmono (sq_nonneg _)

/-- **Sobolev on the cube boundaries, integrated over the shell.** -/
theorem boundary_sobolev {n : ℕ} (hn : 3 ≤ n) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ρ σ : ℝ}, 1 / 2 ≤ ρ → ρ < σ → σ ≤ 1 →
      ∀ u : Vec (n + 1) → ℝ, ContDiff ℝ 1 u →
      ∫ r in Ioo ρ σ, (cubeBoundaryIntegral r (fun x => |u x| ^ ((2 * n : ℝ) / (n - 2)))) ^
          (((n : ℝ) - 2) / n) ≤
        C * ∫ x in {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ},
          (u x ^ 2 + vecNormSq (classicalGradient u x)) := by
  obtain ⟨Cf, hCf, hfs⟩ := face_sobolev hn
  haveI : NeZero n := ⟨by omega⟩
  refine ⟨Cf ^ 2, by positivity, ?_⟩
  intro ρ σ hρ hρσ hσ u hu
  have hn3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hρ0 : 0 < ρ := by linarith
  have hq : 0 < (2 * n : ℝ) / (n - 2) := div_pos (by linarith) (by linarith)
  have hδ : 0 < ((n : ℝ) - 2) / n := div_pos (by linarith) (by linarith)
  have hδ1 : ((n : ℝ) - 2) / n ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have hgc : Continuous (fun x : Vec (n + 1) => |u x| ^ ((2 * n : ℝ) / (n - 2))) :=
    hu.continuous.abs.rpow_const (fun _ => Or.inr hq.le)
  have hWc : Continuous (fun x : Vec (n + 1) => u x ^ 2 + vecNormSq (classicalGradient u x)) :=
    (hu.continuous.pow 2).add (continuous_vecNormSq_grad hu)
  have hGc : ContinuousOn
      (fun r => cubeBoundaryIntegral r (fun x => |u x| ^ ((2 * n : ℝ) / (n - 2)))) (Icc ρ σ) :=
    (continuousOn_cubeBoundaryIntegral hgc).mono (fun r hr => lt_of_lt_of_le hρ0 hr.1)
  have hBc : ContinuousOn
      (fun r => cubeBoundaryIntegral r
        (fun x => u x ^ 2 + vecNormSq (classicalGradient u x))) (Icc ρ σ) :=
    (continuousOn_cubeBoundaryIntegral hWc).mono (fun r hr => lt_of_lt_of_le hρ0 hr.1)
  have hI1 : IntegrableOn (fun r => (cubeBoundaryIntegral r
      (fun x => |u x| ^ ((2 * n : ℝ) / (n - 2)))) ^ (((n : ℝ) - 2) / n)) (Ioo ρ σ) :=
    (ContinuousOn.integrableOn_Icc
      (hGc.rpow_const (fun r _ => Or.inr hδ.le))).mono_set Ioo_subset_Icc_self
  have hI2 : IntegrableOn (fun r => Cf ^ 2 * cubeBoundaryIntegral r
      (fun x => u x ^ 2 + vecNormSq (classicalGradient u x))) (Ioo ρ σ) :=
    (ContinuousOn.integrableOn_Icc (continuousOn_const.mul hBc)).mono_set Ioo_subset_Icc_self
  have hWint : IntegrableOn (fun x : Vec (n + 1) => u x ^ 2 + vecNormSq (classicalGradient u x))
      {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ} := by
    refine (hWc.continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : Vec (n + 1)) 1)).mono_set ?_
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (hx.2.le).trans hσ
  have hpt : ∀ r ∈ Ioo ρ σ, (cubeBoundaryIntegral r
      (fun x => |u x| ^ ((2 * n : ℝ) / (n - 2)))) ^ (((n : ℝ) - 2) / n) ≤
      Cf ^ 2 * cubeBoundaryIntegral r (fun x => u x ^ 2 + vecNormSq (classicalGradient u x)) := by
    intro r hr
    have hr' : r ∈ Icc (1 / 2 : ℝ) 1 := ⟨by linarith [hr.1], by linarith [hr.2]⟩
    have hr0 : 0 ≤ r := by linarith [hr'.1]
    have hKm : MeasurableSet (Set.pi Set.univ (fun _ : Fin n => Icc (-r) r)) :=
      MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
    have hF0 : ∀ (i : Fin (n + 1)) (s : ℝ),
        0 ≤ faceIntegral i s r (fun x => |u x| ^ ((2 * n : ℝ) / (n - 2))) := by
      intro i s
      unfold faceIntegral
      exact setIntegral_nonneg hKm (fun y _ => Real.rpow_nonneg (abs_nonneg _) _)
    unfold cubeBoundaryIntegral
    calc (∑ i : Fin (n + 1), ∑ s ∈ ({-1, 1} : Finset ℝ),
          faceIntegral i s r (fun x => |u x| ^ ((2 * n : ℝ) / (n - 2)))) ^ (((n : ℝ) - 2) / n)
        ≤ ∑ i : Fin (n + 1), (∑ s ∈ ({-1, 1} : Finset ℝ),
            faceIntegral i s r (fun x => |u x| ^ ((2 * n : ℝ) / (n - 2)))) ^ (((n : ℝ) - 2) / n) :=
          rpow_sum_le _ _ (fun i _ => Finset.sum_nonneg (fun s _ => hF0 i s)) hδ hδ1
      _ ≤ ∑ i : Fin (n + 1), ∑ s ∈ ({-1, 1} : Finset ℝ),
            (faceIntegral i s r (fun x => |u x| ^ ((2 * n : ℝ) / (n - 2)))) ^
              (((n : ℝ) - 2) / n) :=
          Finset.sum_le_sum (fun i _ => rpow_sum_le _ _ (fun s _ => hF0 i s) hδ hδ1)
      _ ≤ ∑ i : Fin (n + 1), ∑ s ∈ ({-1, 1} : Finset ℝ), Cf ^ 2 *
            faceIntegral i s r (fun x => u x ^ 2 + vecNormSq (classicalGradient u x)) :=
          Finset.sum_le_sum (fun i _ => Finset.sum_le_sum
            (fun s _ => face_bound hn (fun r hr g hg => hfs r hr g hg) hu i s hr'))
      _ = Cf ^ 2 * ∑ i : Fin (n + 1), ∑ s ∈ ({-1, 1} : Finset ℝ),
            faceIntegral i s r (fun x => u x ^ 2 + vecNormSq (classicalGradient u x)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [Finset.mul_sum]
  calc ∫ r in Ioo ρ σ, (cubeBoundaryIntegral r
        (fun x => |u x| ^ ((2 * n : ℝ) / (n - 2)))) ^ (((n : ℝ) - 2) / n)
      ≤ ∫ r in Ioo ρ σ, Cf ^ 2 * cubeBoundaryIntegral r
          (fun x => u x ^ 2 + vecNormSq (classicalGradient u x)) :=
        setIntegral_mono_on hI1 hI2 measurableSet_Ioo hpt
    _ = Cf ^ 2 * ∫ r in Ioo ρ σ, cubeBoundaryIntegral r
          (fun x => u x ^ 2 + vecNormSq (classicalGradient u x)) := by
        rw [integral_const_mul]
    _ = _ := by rw [integral_shell_eq_boundaryIntegral hρ0 hWint]

end PDE.BSlocalmax
end

-- ==== from Trunc.lean ====
-- Smooth majorant `psiEps ε t = (√(t²+ε²) + t)/2 ≥ max t 0` of the positive part,
-- with `0 ≤ ψ' ≤ 1` and `ψ(t) ≤ |t| + ε/2`.


@[expose] public section

open PDE

namespace PDE.BSlocalmax

/-- Smooth majorant of the positive part. -/
noncomputable def psiEps (ε t : ℝ) : ℝ := (Real.sqrt (t ^ 2 + ε ^ 2) + t) / 2

lemma psiEps_ge (ε t : ℝ) (hε : 0 < ε) : max t 0 ≤ psiEps ε t := by
  have h1 : |t| ≤ Real.sqrt (t ^ 2 + ε ^ 2) := Real.abs_le_sqrt (by nlinarith [sq_nonneg ε])
  have h2 : 0 ≤ Real.sqrt (t ^ 2 + ε ^ 2) := Real.sqrt_nonneg _
  unfold psiEps
  rcases le_total t 0 with ht | ht
  · rw [max_eq_right ht]
    linarith [abs_of_nonpos ht, neg_abs_le t]
  · rw [max_eq_left ht]
    linarith [abs_of_nonneg ht, le_abs_self t]

lemma psiEps_nonneg (ε t : ℝ) (hε : 0 < ε) : 0 ≤ psiEps ε t :=
  (le_max_right t 0).trans (psiEps_ge ε t hε)

lemma psiEps_le (ε t : ℝ) (hε : 0 < ε) : psiEps ε t ≤ |t| + ε := by
  have h1 : Real.sqrt (t ^ 2 + ε ^ 2) ≤ |t| + ε := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [sq_abs t, abs_nonneg t]
  unfold psiEps
  linarith [le_abs_self t]

lemma contDiff_psiEps {ε : ℝ} (hε : 0 < ε) : ContDiff ℝ 1 (psiEps ε) := by
  unfold psiEps
  have h : ContDiff ℝ 1 fun t : ℝ => Real.sqrt (t ^ 2 + ε ^ 2) :=
    ((contDiff_id.pow 2).add contDiff_const).sqrt (fun t => by positivity)
  exact (h.add contDiff_id).div_const 2

lemma psiEps_deriv {ε : ℝ} (hε : 0 < ε) (t : ℝ) :
    ∃ d : ℝ, 0 ≤ d ∧ d ≤ 1 ∧ HasDerivAt (psiEps ε) d t := by
  have hpos : 0 < t ^ 2 + ε ^ 2 := by positivity
  have hs : 0 < Real.sqrt (t ^ 2 + ε ^ 2) := Real.sqrt_pos.2 hpos
  have h1 : HasDerivAt (fun t : ℝ => t ^ 2 + ε ^ 2) (2 * t) t := by
    have := HasDerivAt.add_const (ε ^ 2) (hasDerivAt_pow 2 t)
    convert this using 1 <;> norm_num
  have h2 := HasDerivAt.sqrt h1 hpos.ne'
  have h3 := HasDerivAt.div_const (HasDerivAt.add h2 (hasDerivAt_id t)) 2
  refine ⟨(2 * t / (2 * Real.sqrt (t ^ 2 + ε ^ 2)) + 1) / 2, ?_, ?_, ?_⟩
  · have habs : |t| ≤ Real.sqrt (t ^ 2 + ε ^ 2) := Real.abs_le_sqrt (by nlinarith [sq_nonneg ε])
    have : -1 ≤ 2 * t / (2 * Real.sqrt (t ^ 2 + ε ^ 2)) := by
      rw [le_div_iff₀ (by positivity)]
      linarith [neg_abs_le t]
    linarith
  · have habs : |t| ≤ Real.sqrt (t ^ 2 + ε ^ 2) := Real.abs_le_sqrt (by nlinarith [sq_nonneg ε])
    have : 2 * t / (2 * Real.sqrt (t ^ 2 + ε ^ 2)) ≤ 1 := by
      rw [div_le_iff₀ (by positivity)]
      linarith [le_abs_self t]
    linarith
  · exact h3

/-- Chain rule: `∇(ψ_ε ∘ w) = d • ∇w` with `0 ≤ d ≤ 1`. -/
lemma classicalGradient_psiEps {d : ℕ} {ε : ℝ} (hε : 0 < ε) {w : Vec d → ℝ}
    (hw : ContDiff ℝ 1 w) (x : Vec d) :
    ∃ c : ℝ, 0 ≤ c ∧ c ≤ 1 ∧
      classicalGradient (fun y => psiEps ε (w y)) x = c • classicalGradient w x := by
  obtain ⟨c, hc0, hc1, hder⟩ := psiEps_deriv hε (w x)
  have hw' : HasFDerivAt w (fderiv ℝ w x) x :=
    ((hw.differentiable (by simp)) x).hasFDerivAt
  have h := hder.comp_hasFDerivAt x hw'
  refine ⟨c, hc0, hc1, ?_⟩
  funext i
  have h2 : fderiv ℝ (fun y => psiEps ε (w y)) x = c • fderiv ℝ w x := h.fderiv
  simp [classicalGradient, h2]

lemma vecNormSq_grad_psiEps_le {d : ℕ} {ε : ℝ} (hε : 0 < ε) {w : Vec d → ℝ}
    (hw : ContDiff ℝ 1 w) (x : Vec d) :
    vecNormSq (classicalGradient (fun y => psiEps ε (w y)) x) ≤
      vecNormSq (classicalGradient w x) := by
  obtain ⟨c, hc0, hc1, h⟩ := classicalGradient_psiEps hε hw x
  rw [h, vecNormSq_smul]
  have h0 : 0 ≤ vecNormSq (classicalGradient w x) := by
    rw [← vecEuclideanNorm_sq]; exact sq_nonneg _
  nlinarith [mul_nonneg hc0 (sub_nonneg.2 hc1)]

end PDE.BSlocalmax
end

-- ==== from SobolevH1.lean ====
-- Sobolev inequality (not mean-free, p = 2, d ≥ 3) for `H¹` functions on
-- bounded open convex domains, in real form.


@[expose] public section

open scoped ENNReal
open MeasureTheory Set PDE

namespace PDE.BSlocalmax

lemma toReal_eLpNormOn' {d : ℕ} {U : Set (Vec d)} {f : Vec d → ℝ}
    (hf : AEStronglyMeasurable f (volumeOn U)) {p : ℝ} (hp : 0 < p) :
    (eLpNormOn U (ENNReal.ofReal p) f).toReal = (∫ x in U, |f x| ^ p) ^ (1 / p) := by
  unfold eLpNormOn
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hp).ne'
    ENNReal.ofReal_ne_top hf, ENNReal.toReal_ofReal hp.le,
    ← ENNReal.toReal_rpow]
  congr 1
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun x => by positivity)
    (((continuous_abs.comp_aestronglyMeasurable hf).aemeasurable.pow_const p).aestronglyMeasurable)]
  congr 1
  refine lintegral_congr (fun x => ?_)
  rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) hp.le]

lemma toReal_eLpMeanNormOn' {d : ℕ} {U : Set (Vec d)} (hUtop : volume U < ∞)
    {f : Vec d → ℝ} (hf : AEStronglyMeasurable f (volumeOn U)) {p : ℝ} (hp : 0 < p) :
    (eLpMeanNormOn U (ENNReal.ofReal p) f).toReal =
      ((volume U).toReal)⁻¹ ^ (1 / p) * (∫ x in U, |f x| ^ p) ^ (1 / p) := by
  rw [eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn hUtop, ENNReal.toReal_mul,
    toReal_eLpNormOn' hf hp]
  congr 1
  have h1p : (1 / ENNReal.ofReal p).toReal = 1 / p := by
    rw [one_div, ENNReal.toReal_inv, ENNReal.toReal_ofReal hp.le, one_div]
  rw [h1p, ← ENNReal.toReal_rpow, ENNReal.toReal_inv]

/-- Normalized Sobolev inequality for `H¹` functions on convex domains. -/
theorem meanNorm_sobolev_h1 (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Set (Vec d)) (D : ℝ), IsOpenBoundedConvexDomain V → V.Nonempty →
      HasEuclideanDiameterLE V D → ∀ u : H1Function V,
        eLpMeanNormOn V (ENNReal.ofReal (sobolevConjugate d 2)) u.toFun ≤
          ENNReal.ofReal (C * D) *
              euclideanFieldELpMeanNormOn V (ENNReal.ofReal 2) u.grad +
            eLpMeanNormOn V (ENNReal.ofReal 2) u.toFun := by
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨C₀, hC₀, hC⟩ := exists_convexSobolevPoincare_constant d (by omega)
  refine ⟨C₀ * (2 * ((d : ℝ) - 1) / ((d : ℝ) - 2)),
    mul_pos hC₀ (div_pos (by linarith) (by linarith)), ?_⟩
  intro V D hV hne hD u
  obtain ⟨hVpos, hVtop⟩ := volume_pos_lt_top_of_isOpenBoundedConvexDomain hV hne
  have hprob : IsProbabilityMeasure (normalizedVolumeOn V) :=
    isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top hVpos hVtop
  let u' : W1pFunction V (ENNReal.ofReal 2) :=
    { toFun := u.toFun
      grad := u.grad
      memLp := by simpa only [ENNReal.ofReal_ofNat] using u.memL2
      gradMemLp := by intro i; simpa only [ENNReal.ofReal_ofNat] using u.gradMemL2 i
      hasWeakGradient := u.hasWeakGradient }
  have h := hC 2 (by norm_num) (by exact_mod_cast (by omega : 2 < d)) V D hV hne hD u'
  have hq1 : 1 ≤ ENNReal.ofReal (sobolevConjugate d 2) := by
    rw [ENNReal.one_le_ofReal, sobolevConjugate, le_div_iff₀ (by linarith)]
    linarith
  have hm2 : MemLpOn V (ENNReal.ofReal 2) u.toFun := by
    simpa only [ENNReal.ofReal_ofNat] using u.memL2
  have hgm : AEStronglyMeasurable u.toFun (normalizedVolumeOn V) :=
    (memLp_normalizedVolumeOn_of_memLpOn hm2 hVpos).aestronglyMeasurable
  have havg : integralAverage V u.toFun = ∫ x, u.toFun x ∂(normalizedVolumeOn V) := by
    rw [normalizedVolumeOn, integral_smul_measure, ENNReal.toReal_inv, integralAverage]
    try rfl
  have hdecomp : u.toFun = (fun x => u.toFun x - integralAverage V u.toFun) +
      fun _ => integralAverage V u.toFun := by
    funext x; simp
  have hmink : eLpMeanNormOn V (ENNReal.ofReal (sobolevConjugate d 2)) u.toFun ≤
      eLpMeanNormOn V (ENNReal.ofReal (sobolevConjugate d 2))
        (fun x => u.toFun x - integralAverage V u.toFun) +
      eLpNorm (fun _ => integralAverage V u.toFun) (ENNReal.ofReal (sobolevConjugate d 2))
        (normalizedVolumeOn V) := by
    unfold eLpMeanNormOn
    conv_lhs => rw [hdecomp]
    exact eLpNorm_add_le hq1
  have hconst : eLpNorm (fun _ => integralAverage V u.toFun)
      (ENNReal.ofReal (sobolevConjugate d 2)) (normalizedVolumeOn V) =
      ‖integralAverage V u.toFun‖ₑ := by
    have hqpos : 0 < sobolevConjugate d 2 := by
      unfold sobolevConjugate; exact div_pos (by linarith) (by linarith)
    rw [eLpNorm_const' _ (ENNReal.ofReal_pos.2 hqpos).ne' ENNReal.ofReal_ne_top, measure_univ,
      ENNReal.one_rpow, mul_one]
  have havg_le : ‖integralAverage V u.toFun‖ₑ ≤ eLpMeanNormOn V (ENNReal.ofReal 2) u.toFun := by
    rw [havg]
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    rw [← eLpNorm_one_eq_lintegral_enorm hgm]
    unfold eLpMeanNormOn
    exact eLpNorm_le_eLpNorm_of_exponent_le (ENNReal.one_le_ofReal.2 (by norm_num))
  have hu : (fun x => u'.toFun x - integralAverage V u'.toFun) =
      fun x => u.toFun x - integralAverage V u.toFun := rfl
  have hug : u'.grad = u.grad := rfl
  rw [hu, hug] at h
  rw [hconst] at hmink
  calc eLpMeanNormOn V (ENNReal.ofReal (sobolevConjugate d 2)) u.toFun
      ≤ _ := hmink
    _ ≤ _ := add_le_add h havg_le


/-- Real Sobolev inequality for `H¹` functions on bounded open convex domains. -/
theorem sobolev_real_h1 (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (V : Set (Vec d)) (D : ℝ), IsOpenBoundedConvexDomain V → V.Nonempty →
      HasEuclideanDiameterLE V D → ∀ u : H1Function V,
      IntegrableOn (fun x => |u.toFun x| ^ sobolevConjugate d 2) V ∧
      (∫ x in V, |u.toFun x| ^ sobolevConjugate d 2) ^ (1 / sobolevConjugate d 2) ≤
        ((volume V).toReal) ^ (1 / sobolevConjugate d 2 - 1 / 2) *
          (C * D * (∫ x in V, vecNormSq (u.grad x)) ^ (1 / 2 : ℝ) +
            (∫ x in V, u.toFun x ^ 2) ^ (1 / 2 : ℝ)) := by
  obtain ⟨C, hC, hmain⟩ := meanNorm_sobolev_h1 d hd
  refine ⟨C, hC, ?_⟩
  intro V D hV hne hD u
  obtain ⟨hvpos, hvtop⟩ := volume_pos_lt_top_of_isOpenBoundedConvexDomain hV hne
  have hD0 : 0 ≤ D := hD.nonneg hne
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hqpos : 0 < sobolevConjugate d 2 := by
    unfold sobolevConjugate; exact div_pos (by linarith) (by linarith)
  have hvr : 0 < (volume V).toReal := ENNReal.toReal_pos hvpos.ne' hvtop.ne
  have hm2 : MemLpOn V (ENNReal.ofReal 2) u.toFun := by
    simpa only [ENNReal.ofReal_ofNat] using u.memL2
  have hgm2 : MemLpOn V (ENNReal.ofReal 2) (fun x => vecEuclideanNorm (u.grad x)) := by
    simpa only [ENNReal.ofReal_ofNat] using u.gradMemL2.memLp_vecEuclideanNorm
  have hum : AEStronglyMeasurable u.toFun (volumeOn V) := hm2.aestronglyMeasurable
  have hgm : AEStronglyMeasurable (fun x => vecEuclideanNorm (u.grad x)) (volumeOn V) :=
    hgm2.aestronglyMeasurable
  have hfin1 : eLpMeanNormOn V (ENNReal.ofReal 2) u.toFun ≠ ∞ :=
    (memLp_normalizedVolumeOn_of_memLpOn hm2 hvpos).eLpNorm_lt_top.ne
  have hfin2 : euclideanFieldELpMeanNormOn V (ENNReal.ofReal 2) u.grad ≠ ∞ :=
    (memLp_normalizedVolumeOn_of_memLpOn hgm2 hvpos).eLpNorm_lt_top.ne
  have hfin3 : ENNReal.ofReal (C * D) *
      euclideanFieldELpMeanNormOn V (ENNReal.ofReal 2) u.grad ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin2
  have hle := hmain V D hV hne hD u
  have hfinq : eLpMeanNormOn V (ENNReal.ofReal (sobolevConjugate d 2)) u.toFun ≠ ∞ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hfin3, hfin1⟩) hle
  -- Integrability
  have hint : IntegrableOn (fun x => |u.toFun x| ^ sobolevConjugate d 2) V := by
    have h1 : eLpNormOn V (ENNReal.ofReal (sobolevConjugate d 2)) u.toFun ≠ ∞ := by
      have e := eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn hvtop
        (p := ENNReal.ofReal (sobolevConjugate d 2)) (f := u.toFun)
      intro hinf
      rw [e, hinf, ENNReal.mul_top] at hfinq
      · exact hfinq rfl
      · refine (ENNReal.rpow_pos (ENNReal.inv_pos.2 hvtop.ne) ?_).ne'
        exact (ENNReal.inv_ne_top.2 hvpos.ne') |> fun _ => (ENNReal.inv_ne_top.2 hvpos.ne')
    have hmem : MemLp u.toFun (ENNReal.ofReal (sobolevConjugate d 2)) (volumeOn V) :=
      lt_top_iff_ne_top.2 h1
    have := hmem.integrable_norm_rpow (ENNReal.ofReal_pos.2 hqpos).ne' ENNReal.ofReal_ne_top
    rw [ENNReal.toReal_ofReal hqpos.le] at this
    simp only [Real.norm_eq_abs] at this
    exact this
  refine ⟨hint, ?_⟩
  have h := ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨hfin3, hfin1⟩) hle
  have hint1 : ∫ x in V, |vecEuclideanNorm (u.grad x)| ^ (2 : ℝ) =
      ∫ x in V, vecNormSq (u.grad x) :=
    setIntegral_congr_fun hV.isOpen.measurableSet (fun x _ => by
      rw [Real.rpow_two, sq_abs, vecEuclideanNorm_sq])
  have hint2 : ∫ x in V, |u.toFun x| ^ (2 : ℝ) = ∫ x in V, u.toFun x ^ 2 :=
    setIntegral_congr_fun hV.isOpen.measurableSet (fun x _ => by
      rw [Real.rpow_two, sq_abs])
  have hB : (euclideanFieldELpMeanNormOn V (ENNReal.ofReal 2) u.grad).toReal =
      ((volume V).toReal)⁻¹ ^ (1 / 2 : ℝ) *
        (∫ x in V, vecNormSq (u.grad x)) ^ (1 / 2 : ℝ) := by
    unfold euclideanFieldELpMeanNormOn
    rw [toReal_eLpMeanNormOn' hvtop hgm (by norm_num : (0 : ℝ) < 2), hint1]
  have hE : (eLpMeanNormOn V (ENNReal.ofReal 2) u.toFun).toReal =
      ((volume V).toReal)⁻¹ ^ (1 / 2 : ℝ) * (∫ x in V, u.toFun x ^ 2) ^ (1 / 2 : ℝ) := by
    rw [toReal_eLpMeanNormOn' hvtop hum (by norm_num : (0 : ℝ) < 2), hint2]
  rw [ENNReal.toReal_add hfin3 hfin1, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (mul_nonneg hC.le hD0),
    toReal_eLpMeanNormOn' hvtop hum hqpos, hB, hE] at h
  have ha : 0 < (volume V).toReal ^ (1 / sobolevConjugate d 2) := Real.rpow_pos_of_pos hvr _
  have hmul : (volume V).toReal ^ (1 / sobolevConjugate d 2) *
      ((volume V).toReal)⁻¹ ^ (1 / sobolevConjugate d 2) = 1 := by
    rw [Real.inv_rpow hvr.le, mul_inv_cancel₀ ha.ne']
  have hsub : (volume V).toReal ^ (1 / sobolevConjugate d 2 - 1 / 2) =
      (volume V).toReal ^ (1 / sobolevConjugate d 2) * ((volume V).toReal)⁻¹ ^ (1 / 2 : ℝ) := by
    rw [Real.rpow_sub hvr, Real.inv_rpow hvr.le, div_eq_mul_inv]
  calc (∫ x in V, |u.toFun x| ^ sobolevConjugate d 2) ^ (1 / sobolevConjugate d 2)
      = (volume V).toReal ^ (1 / sobolevConjugate d 2) *
          (((volume V).toReal)⁻¹ ^ (1 / sobolevConjugate d 2) *
            (∫ x in V, |u.toFun x| ^ sobolevConjugate d 2) ^ (1 / sobolevConjugate d 2)) := by
        rw [← mul_assoc, hmul, one_mul]
    _ ≤ (volume V).toReal ^ (1 / sobolevConjugate d 2) *
          (C * D * (((volume V).toReal)⁻¹ ^ (1 / 2 : ℝ) *
              (∫ x in V, vecNormSq (u.grad x)) ^ (1 / 2 : ℝ)) +
            ((volume V).toReal)⁻¹ ^ (1 / 2 : ℝ) * (∫ x in V, u.toFun x ^ 2) ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left h ha.le
    _ = _ := by rw [hsub]; ring

end PDE.BSlocalmax
end

-- ==== from SobolevCube.lean ====
-- Scale-invariant Sobolev inequality for `H¹` functions on the cube
-- `Metric.ball 0 r` (sup norm), dimension `d ≥ 3`.


@[expose] public section

open scoped ENNReal
open MeasureTheory Set PDE

namespace PDE.BSlocalmax

lemma ball_zero_eq_pi_Ioo {d : ℕ} {r : ℝ} (hr : 0 < r) :
    Metric.ball (0 : Vec d) r = Set.pi Set.univ (fun _ : Fin d => Ioo (-r) r) := by
  rw [ball_pi _ hr]
  congr 1
  funext i
  rw [Real.ball_eq_Ioo]
  simp

theorem sobolev_cube_h1 {d : ℕ} (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → ∀ V : Set (Vec d), V = Metric.ball (0 : Vec d) r →
      ∀ u : H1Function V,
      IntegrableOn (fun x => |u.toFun x| ^ sobolevConjugate d 2) V ∧
      (∫ x in V, |u.toFun x| ^ sobolevConjugate d 2) ^ (1 / sobolevConjugate d 2) ≤
        C * (∫ x in V, vecNormSq (u.grad x)) ^ (1 / 2 : ℝ) +
          (2 * r)⁻¹ * (∫ x in V, u.toFun x ^ 2) ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hmain⟩ := sobolev_real_h1 d hd
  have hd3 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  refine ⟨C * Real.sqrt d, mul_pos hC (Real.sqrt_pos.2 (by linarith)), ?_⟩
  intro r hr V hV u
  have ht : (0 : ℝ) < 2 * r := by linarith
  have hV' : V = axisCube (fun _ : Fin d => -r) (2 * r) :=
    hV.trans ((ball_zero_eq_pi_Ioo hr).trans (axisCube_eq_pi_Ioo r).symm)
  subst hV'
  have hVc := isOpenBoundedConvexDomain_axisCube (fun _ : Fin d => -r) (2 * r)
  have hne := axisCube_nonempty (fun _ : Fin d => -r) ht
  have hD := hasEuclideanDiameterLE_axisCube (fun _ : Fin d => -r) ht.le
  obtain ⟨hint, h⟩ := hmain _ _ hVc hne hD u
  refine ⟨hint, ?_⟩
  have hvol : (volume (axisCube (fun _ : Fin d => -r) (2 * r))).toReal = (2 * r) ^ d := by
    have e := Real.volume_pi_Ioo_toReal (a := fun _ : Fin d => -r)
      (b := fun _ : Fin d => -r + 2 * r) (fun i => by show -r ≤ -r + 2 * r; linarith)
    have e2 : (volume (axisCube (fun _ : Fin d => -r) (2 * r))).toReal =
        ∏ _i : Fin d, ((-r + 2 * r) - (-r)) := e
    rw [e2]
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    congr 1
    ring
  have hs : (d : ℝ) * (1 / sobolevConjugate d 2 - 1 / 2) = -1 := by
    unfold sobolevConjugate
    rw [one_div_div]
    field_simp
    ring
  have hv : ((2 * r) ^ d) ^ (1 / sobolevConjugate d 2 - 1 / 2) = (2 * r)⁻¹ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le, hs, Real.rpow_neg_one]
  rw [hvol, hv] at h
  have key : ∀ X : ℝ, (2 * r)⁻¹ * (C * (Real.sqrt d * (2 * r)) * X) = C * Real.sqrt d * X := by
    intro X
    calc (2 * r)⁻¹ * (C * (Real.sqrt d * (2 * r)) * X)
        = (C * Real.sqrt d * X) * ((2 * r)⁻¹ * (2 * r)) := by ring
      _ = C * Real.sqrt d * X := by rw [inv_mul_cancel₀ ht.ne', mul_one]
  refine h.trans (le_of_eq ?_)
  rw [mul_add, key]

end PDE.BSlocalmax
end
