module

public import PDEFoundation.PDE.HarmonicGradientOscillationSmooth
public import PDEFoundation.Sobolev.Cutoff.Ball
public import PDEFoundation.Measure.OneDimensionalCoordinate
public import PDEFoundation.Sobolev.OneDimensional.SmoothTransport
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Local mean value formula in one dimension -/

@[expose] public section

namespace PDE

open MeasureTheory Set
open Filter
open scoped Laplacian Topology

noncomputable section

variable {d : ℕ}

private theorem contDiff_cutoff_mul_of_contDiffOn
    {x : Vec d} {r R : ℝ} {v : Vec d → ℝ}
    (hr : 0 ≤ r) (hrR : r < R)
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v (euclideanBall x R)) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun y => canonicalBallCutoff x r R y * v y) := by
  let φ := canonicalBallCutoff x r R
  let f : Vec d → ℝ := fun y => φ y * v y
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := by
    exact canonicalBallCutoff_smooth x hr hrR
  have hB : IsOpen (euclideanBall x R) := isOpen_euclideanBall x R
  have hT : IsOpen ((tsupport φ)ᶜ) := (isClosed_tsupport φ).isOpen_compl
  have hinside : ContDiffOn ℝ (⊤ : ℕ∞) f (euclideanBall x R) := by
    exact hφ.contDiffOn.mul hv
  have houtside : ContDiffOn ℝ (⊤ : ℕ∞) f ((tsupport φ)ᶜ) := by
    have hzero : EqOn f (fun _ : Vec d => (0 : ℝ)) ((tsupport φ)ᶜ) := by
      intro y hy
      have hyφ : φ y = 0 := image_eq_zero_of_notMem_tsupport hy
      simp [f, hyφ]
    exact (contDiffOn_congr hzero).2 contDiffOn_const
  have hcover : euclideanBall x R ∪ (tsupport φ)ᶜ = Set.univ := by
    ext y
    simp only [mem_union, mem_compl_iff, mem_univ, iff_true]
    by_cases hy : y ∈ tsupport φ
    · left
      exact canonicalBallCutoff_tsupport_subset_outer hr hrR hy
    · exact Or.inr hy
  dsimp [f, φ] at hinside houtside ⊢
  exact contDiff_of_contDiffOn_union_of_isOpen hinside houtside hcover hB hT

private theorem euclideanCoordLaplacian_eq_of_eqOn_open
    {f g : Vec d → ℝ} {U : Set (Vec d)} (hU : IsOpen U)
    (hfg : EqOn f g U) {x : Vec d} (hx : x ∈ U) :
    euclideanCoordLaplacian f x = euclideanCoordLaplacian g x := by
  unfold euclideanCoordLaplacian
  apply Finset.sum_congr rfl
  intro i _
  unfold euclideanCoordSecondDeriv
  have hderiv : EqOn (euclideanCoordDeriv i f) (euclideanCoordDeriv i g) U := by
    intro y hy
    unfold euclideanCoordDeriv
    have hev : f =ᶠ[𝓝 y] g := by
      filter_upwards [hU.mem_nhds hy] with z hz
      exact hfg hz
    rw [hev.fderiv_eq]
  have hev : euclideanCoordDeriv i f =ᶠ[𝓝 x] euclideanCoordDeriv i g := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hderiv hy
  exact congrArg (fun L : Vec d →L[ℝ] ℝ => L (basisVec i)) hev.fderiv_eq

private theorem cutoff_mul_eqOn_inner
    {x : Vec d} {r R : ℝ} {v : Vec d → ℝ}
    (hr : 0 ≤ r) (hrR : r < R) :
  EqOn (fun y => canonicalBallCutoff x r R y * v y) v
      (euclideanBall x r) := by
  intro y hy
  change canonicalBallCutoff x r R y * v y = v y
  rw [canonicalBallCutoff_eq_one_on_inner hr hrR hy, one_mul]

private theorem cutoff_mul_harmonic_on_inner
    {x : Vec d} {r R : ℝ} {v : Vec d → ℝ}
    (hr : 0 ≤ r) (hrR : r < R)
    (hharm : ∀ y ∈ euclideanBall x R,
      euclideanCoordLaplacian v y = 0) :
    ∀ y ∈ euclideanBall x r,
      euclideanCoordLaplacian
        (fun z => canonicalBallCutoff x r R z * v z) y = 0 := by
  intro y hy
  have hEq := cutoff_mul_eqOn_inner (x := x) (v := v) hr hrR
  rw [euclideanCoordLaplacian_eq_of_eqOn_open
    (isOpen_euclideanBall x r) hEq hy]
  exact hharm y ((euclideanBall_mono hr hrR.le) hy)

private theorem integral_euclideanBall_coord_sub_center_eq_zero
    {d : ℕ} {x : Vec d} {r : ℝ} (i : Fin d) :
    ∫ y in euclideanBall x r, (y i - x i) = 0 := by
  let T : Vec d → Vec d := fun y => 2 • x - y
  let B := euclideanBall x r
  have hvec (y : Vec d) : T y - x = -(y - x) := by
    ext j
    simp [T, Pi.sub_apply, two_smul]
    ring
  have hdist (y : Vec d) : euclideanSqDist (T y) x = euclideanSqDist y x := by
    rw [euclideanSqDist, hvec, vecNormSq_neg]
    rfl
  have hpre : T ⁻¹' B = B := by
    ext y
    change euclideanSqDist (T y) x < r ^ 2 ↔ euclideanSqDist y x < r ^ 2
    rw [hdist]
  have hmp : MeasurePreserving T (volume : Measure (Vec d)) volume := by
    exact Measure.measurePreserving_sub_left volume (2 • x)
  have hchange := hmp.setIntegral_preimage_emb
    (Homeomorph.subLeft (2 • x)).measurableEmbedding
    (fun y : Vec d => y i - x i) B
  rw [hpre] at hchange
  have hodd : EqOn (fun y : Vec d => (T y) i - x i)
      (fun y => -(y i - x i)) B := by
    intro y hy
    simp [T, Pi.sub_apply, two_smul]
    ring
  have hneg : (∫ y in B, (T y) i - x i) =
      ∫ y in B, -(y i - x i) := by
    exact setIntegral_congr_fun (μ := volume)
      (isOpen_euclideanBall x r).measurableSet hodd
  rw [integral_neg] at hneg
  rw [hneg] at hchange
  linarith

private theorem integralAverage_add_of_integrable_local
    {d : ℕ} {U : Set (Vec d)} {f g : Vec d → ℝ}
    (hf : IntegrableOn f U) (hg : IntegrableOn g U) :
    integralAverage U (fun y => f y + g y) =
      integralAverage U f + integralAverage U g := by
  unfold integralAverage
  rw [integral_add hf hg]
  ring

private theorem integralAverage_const_mul_local
    {d : ℕ} {U : Set (Vec d)} {f : Vec d → ℝ} (c : ℝ) :
    integralAverage U (fun y => c * f y) = c * integralAverage U f := by
  unfold integralAverage
  rw [integral_const_mul]
  ring

private theorem integralAverage_const_local
    {d : ℕ} {U : Set (Vec d)} (hpos : 0 < volume U)
    (htop : volume U ≠ ⊤) (c : ℝ) :
    integralAverage U (fun _ => c) = c := by
  unfold integralAverage
  rw [setIntegral_const]
  have hreal : (volume U).toReal ≠ 0 :=
    (ENNReal.toReal_pos hpos.ne' htop).ne'
  change (volume U).toReal⁻¹ * ((volume U).toReal * c) = c
  field_simp

private theorem integralAverage_affine_eq_center
    {x : Vec 1} {r c a : ℝ}
    (hr : 0 < r) :
    integralAverage (euclideanBall x r)
      (fun y => a + c * (y 0 - x 0)) = a := by
  let B := euclideanBall x r
  have hpos : 0 < volume B := volume_euclideanBall_pos x hr
  have htop : volume B ≠ ⊤ := volume_euclideanBall_ne_top x hr.le
  have hcoord : IntegrableOn (fun y : Vec 1 => y 0 - x 0) B := by
    have hcont : Continuous (fun y : Vec 1 => y 0 - x 0) :=
      (continuous_apply (0 : Fin 1)).sub continuous_const
    exact (hcont.continuousOn.integrableOn_compact
      (isCompact_euclideanClosedBall x hr.le)).mono_set
        (euclideanBall_subset_euclideanClosedBall x r)
  have hconst : IntegrableOn (fun _ : Vec 1 => a) B := integrableOn_const htop
  have hmeanCoord : integralAverage B (fun y : Vec 1 => y 0 - x 0) = 0 := by
    unfold integralAverage
    rw [integral_euclideanBall_coord_sub_center_eq_zero 0, mul_zero]
  calc
    integralAverage B (fun y => a + c * (y 0 - x 0)) =
        integralAverage B (fun _ => a) +
          integralAverage B (fun y => c * (y 0 - x 0)) :=
      integralAverage_add_of_integrable_local hconst (hcoord.const_mul c)
    _ = a := by
      rw [integralAverage_const_local hpos htop,
        integralAverage_const_mul_local c, hmeanCoord]
      ring

/-- Round-ball membership on `Vec 1` is the usual open interval condition. -/
private theorem mem_euclideanBall_vecOne_iff
    {x y : Vec 1} {r : ℝ} (hr : 0 < r) :
    y ∈ euclideanBall x r ↔ x 0 - r < y 0 ∧ y 0 < x 0 + r := by
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hr]
  have hnorm : vecEuclideanNorm (y - x) = |y 0 - x 0| := by
    unfold vecEuclideanNorm
    rw [show vecNormSq (y - x) = (y 0 - x 0) ^ 2 by
      simp [vecNormSq, vecDot, Pi.sub_apply]
      ring]
    rw [Real.sqrt_sq_eq_abs]
  rw [hnorm, abs_lt]
  constructor <;> intro h <;> constructor <;> linarith

/-- Local ball mean value formula in dimensions at least two. -/
theorem integralAverage_euclideanBall_eq_center_of_harmonicOn_one
    {v : Vec 1 → ℝ} {x : Vec 1} {R s : ℝ}
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v (euclideanBall x R))
    (hharm : ∀ y ∈ euclideanBall x R,
      euclideanCoordLaplacian v y = 0)
    (hs : 0 < s) (hsR : s < R) :
    integralAverage (euclideanBall x s) v = v x := by
  let t : ℝ := (s + R) / 2
  have hst : s < t := by dsimp [t]; linarith
  have htR : t < R := by dsimp [t]; linarith
  have ht0 : 0 ≤ t := le_of_lt (lt_trans hs hst)
  have htpos : 0 < t := lt_trans hs hst
  let φ := canonicalBallCutoff x t R
  let w : Vec 1 → ℝ := fun y => φ y * v y
  have hw : ContDiff ℝ (⊤ : ℕ∞) w := by
    exact contDiff_cutoff_mul_of_contDiffOn ht0 htR hv
  have hwharm : ∀ y ∈ euclideanBall x t,
      euclideanCoordLaplacian w y = 0 := by
    intro y hy
    change euclideanCoordLaplacian
      (fun z => canonicalBallCutoff x t R z * v z) y = 0
    exact cutoff_mul_harmonic_on_inner ht0 htR hharm y hy
  let F : ℝ → ℝ := scalarPullbackOne w
  have hwOne : ContDiff ℝ 1 w := hw.of_le (by norm_num)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F := by
    exact ContDiff.scalarPullbackOne hw
  have hFDeriv : deriv F = scalarPullbackOne (euclideanCoordDeriv 0 w) := by
    funext a
    exact deriv_scalarPullbackOne_eq_native_directional hwOne a
  have hFDerivTwo : ContDiff ℝ 1 (euclideanCoordDeriv 0 w) :=
    (contDiff_euclideanCoordDeriv hw 0).of_le (by norm_num)
  let S : Set ℝ := Ioo (x 0 - t) (x 0 + t)
  have hcenter : x 0 ∈ S := by
    dsimp [S]
    constructor <;> linarith
  have hSecond : ∀ a ∈ S, deriv (deriv F) a = 0 := by
    intro a ha
    have hball : scalarToVecOne a ∈ euclideanBall x t := by
      apply (mem_euclideanBall_vecOne_iff htpos).2
      exact ha
    have hlap := hwharm (scalarToVecOne a) hball
    have htransport :=
      deriv_scalarPullbackOne_eq_native_directional hFDerivTwo a
    rw [hFDeriv]
    rw [htransport]
    simpa [euclideanCoordLaplacian, euclideanCoordSecondDeriv] using hlap
  have hF2 : ContDiff ℝ 2 F := hF.of_le (by norm_num)
  have hderivDifferentiable : DifferentiableOn ℝ (deriv F) S :=
    (hF2.differentiable_deriv_two).differentiableOn
  let c : ℝ := deriv F (x 0)
  have hderivConst : ∀ a ∈ S, deriv F a = c := by
    intro a ha
    dsimp [c]
    exact (isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      hderivDifferentiable hSecond hcenter ha).symm
  let q : ℝ → ℝ := fun a => F a - c * a
  have hqSmooth : ContDiff ℝ (⊤ : ℕ∞) q := by
    simpa [q] using hF.sub (contDiff_const.mul contDiff_id)
  have hqzero : ∀ a ∈ S, deriv q a = 0 := by
    intro a ha
    have hlin : HasDerivAt (fun z : ℝ => c * z) c a := by
      simpa only [mul_one, id_eq] using (hasDerivAt_id a).const_mul c
    have hqDeriv : deriv (fun z : ℝ => F z - c * z) a = deriv F a - c :=
      ((hF.differentiable (by norm_num) a).hasDerivAt.sub hlin).deriv
    change deriv (fun z : ℝ => F z - c * z) a = 0
    rw [hqDeriv, hderivConst a ha]
    ring
  have hFaffine : ∀ a ∈ S, F a = F (x 0) + c * (a - x 0) := by
    intro a ha
    have hq := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (show DifferentiableOn ℝ q S from by
        exact (hqSmooth.differentiable (by norm_num)).differentiableOn)
      hqzero hcenter ha
    dsimp [q] at hq
    calc
      F a = (F a - c * a) + c * a := by ring
      _ = (F (x 0) - c * x 0) + c * a := by rw [hq]
      _ = F (x 0) + c * (a - x 0) := by ring
  have hAffine : ∀ y ∈ euclideanBall x s,
      w y = w x + c * (y 0 - x 0) := by
    intro y hy
    have hyT : y ∈ euclideanBall x t :=
      (euclideanBall_mono hs.le hst.le) hy
    have hyS : y 0 ∈ S :=
      (mem_euclideanBall_vecOne_iff htpos).mp hyT
    have hFval : F (y 0) = w y := by
      change w (scalarToVecOne (vecOneCoordinate y)) = w y
      exact congrArg w (scalarToVecOne_vecOneCoordinate y)
    have hFvalx : F (x 0) = w x := by
      change w (scalarToVecOne (vecOneCoordinate x)) = w x
      exact congrArg w (scalarToVecOne_vecOneCoordinate x)
    calc
      w y = F (y 0) := hFval.symm
      _ = F (x 0) + c * (y 0 - x 0) := hFaffine (y 0) hyS
      _ = w x + c * (y 0 - x 0) := by rw [hFvalx]
  have hmeanW : integralAverage (euclideanBall x s) w = w x := by
    have hAE : w =ᵐ[volumeOn (euclideanBall x s)]
        (fun y => w x + c * (y 0 - x 0)) := by
      filter_upwards [ae_restrict_mem
        (isOpen_euclideanBall x s).measurableSet] with y hy
      exact hAffine y hy
    rw [integralAverage_congr_ae hAE]
    exact integralAverage_affine_eq_center hs
  have hpatch : w =ᵐ[volumeOn (euclideanBall x s)] v := by
    filter_upwards [ae_restrict_mem
      (isOpen_euclideanBall x s).measurableSet] with y hy
    exact (cutoff_mul_eqOn_inner (x := x) (v := v) (r := t) (R := R)
      ht0 htR) ((euclideanBall_mono hs.le hst.le) hy)
  rw [← integralAverage_congr_ae hpatch]
  calc
    integralAverage (euclideanBall x s) w = w x := hmeanW
    _ = v x :=
      cutoff_mul_eqOn_inner (x := x) (v := v) (r := t) (R := R)
        ht0 htR (center_mem_euclideanBall x (lt_trans hs hst))

end

end PDE
