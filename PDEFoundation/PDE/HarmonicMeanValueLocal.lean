module

public import PDEFoundation.PDE.HarmonicGradientOscillationSmooth
public import PDEFoundation.PDE.HarmonicMeanValueLocalOneDim
public import PDEFoundation.Sobolev.Cutoff.Ball
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace/-! # Local mean values and derivative harmonicity for smooth harmonic functions -/

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

private theorem integralAverage_euclideanBall_eq_center_of_harmonicOn_two_le
    (hd : 2 ≤ d) {v : Vec d → ℝ} {x : Vec d} {R s : ℝ}
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v (euclideanBall x R))
    (hharm : ∀ y ∈ euclideanBall x R,
      euclideanCoordLaplacian v y = 0)
    (hs : 0 < s) (hsR : s < R) :
    integralAverage (euclideanBall x s) v = v x := by
  let t : ℝ := (s + R) / 2
  have hst : s < t := by dsimp [t]; linarith
  have htR : t < R := by dsimp [t]; linarith
  have ht0 : 0 ≤ t := le_of_lt (lt_trans hs hst)
  let φ := canonicalBallCutoff x t R
  let w : Vec d → ℝ := fun y => φ y * v y
  have hw : ContDiff ℝ (⊤ : ℕ∞) w := by
    exact contDiff_cutoff_mul_of_contDiffOn ht0 htR hv
  have hwharm : ∀ y ∈ euclideanBall x t,
      euclideanCoordLaplacian w y = 0 := by
    intro y hy
    change euclideanCoordLaplacian
      (fun z => canonicalBallCutoff x t R z * v z) y = 0
    exact cutoff_mul_harmonic_on_inner ht0 htR hharm y hy
  have hdNe : NeZero d := ⟨Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) hd)⟩
  have hglobal := integralAverage_euclideanBall_eq_center_of_harmonic
    hd (hw.of_le (WithTop.coe_le_coe.mpr le_top)) (lt_trans hs hst)
      hwharm hs hst
  have hpatch : w =ᵐ[volumeOn (euclideanBall x s)] v := by
    filter_upwards [ae_restrict_mem (isOpen_euclideanBall x s).measurableSet]
      with y hy
    have hsT : s ≤ t := le_of_lt hst
    exact (cutoff_mul_eqOn_inner (x := x) (v := v) (r := t) (R := R)
      ht0 htR) ((euclideanBall_mono hs.le hsT) hy)
  rw [← integralAverage_congr_ae hpatch]
  calc
    integralAverage (euclideanBall x s) w = w x := hglobal
    _ = v x := by
      exact (cutoff_mul_eqOn_inner (x := x) (v := v) (r := t) (R := R)
        ht0 htR) (center_mem_euclideanBall x (lt_trans hs hst))

/-- Local mean value formula in every positive dimension. -/
theorem integralAverage_euclideanBall_eq_center_of_harmonicOn
    (hd : 0 < d) {v : Vec d → ℝ} {x : Vec d} {R s : ℝ}
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v (euclideanBall x R))
    (hharm : ∀ y ∈ euclideanBall x R,
      euclideanCoordLaplacian v y = 0)
    (hs : 0 < s) (hsR : s < R) :
    integralAverage (euclideanBall x s) v = v x := by
  by_cases hd2 : 2 ≤ d
  · exact integralAverage_euclideanBall_eq_center_of_harmonicOn_two_le
      hd2 hv hharm hs hsR
  · have hd1 : d = 1 := by omega
    subst d
    exact integralAverage_euclideanBall_eq_center_of_harmonicOn_one
      hv hharm hs hsR

/-- On an open set, every coordinate derivative of a smooth harmonic function
is smooth and harmonic. -/
theorem contDiffOn_euclideanCoordDeriv_and_harmonic
    {U : Set (Vec d)} (hU : IsOpen U) {v : Vec d → ℝ}
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v U)
    (hharm : ∀ y ∈ U, euclideanCoordLaplacian v y = 0)
    (i : Fin d) :
    ContDiffOn ℝ (⊤ : ℕ∞) (euclideanCoordDeriv i v) U ∧
      ∀ y ∈ U, euclideanCoordLaplacian (euclideanCoordDeriv i v) y = 0 := by
  have hderiv : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ v) U :=
    (contDiffOn_infty_iff_fderiv_of_isOpen hU).mp hv |>.2
  have hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (euclideanCoordDeriv i v) U := by
    unfold euclideanCoordDeriv
    exact hderiv.clm_apply contDiffOn_const
  refine ⟨hsmooth, ?_⟩
  intro x hx
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x hx
  let ρ : ℝ := ε / 2
  have hρ : 0 < ρ := by dsimp [ρ]; linarith
  have hρeps : ρ < ε := by dsimp [ρ]; linarith
  have hball : euclideanBall x ρ ⊆ U := by
    intro y hy
    exact hεU ((Metric.ball_subset_ball hρeps.le)
      ((euclideanBall_subset_supBall hρ) hy))
  let φ := canonicalBallCutoff x (ρ / 2) ρ
  let w : Vec d → ℝ := fun y => φ y * v y
  have hvball : ContDiffOn ℝ (⊤ : ℕ∞) v (euclideanBall x ρ) :=
    hv.mono hball
  have hw : ContDiff ℝ (⊤ : ℕ∞) w := by
    simpa [w, φ] using
      contDiff_cutoff_mul_of_contDiffOn (x := x) (r := ρ / 2) (R := ρ)
        (v := v) (by positivity) (by linarith) hvball
  have hEq : EqOn w v (euclideanBall x (ρ / 2)) := by
    simpa [w, φ] using
      (cutoff_mul_eqOn_inner (x := x) (v := v)
        (r := ρ / 2) (R := ρ) (by positivity) (by linarith))
  have hWharm : ∀ y ∈ euclideanBall x (ρ / 2),
      euclideanCoordLaplacian w y = 0 := by
    intro y hy
    have hlocal := euclideanCoordLaplacian_eq_of_eqOn_open
      (isOpen_euclideanBall x (ρ / 2)) hEq hy
    rw [hlocal]
    exact hharm y (hball ((euclideanBall_mono (by positivity) (by linarith)) hy))
  have hglobal := euclideanCoordLaplacian_euclideanCoordDeriv_eq_zero
    hw (isOpen_euclideanBall x (ρ / 2)) hWharm
      (center_mem_euclideanBall x (by linarith : 0 < ρ / 2)) i
  have hEqDeriv : EqOn (euclideanCoordDeriv i w)
      (euclideanCoordDeriv i v) (euclideanBall x (ρ / 2)) := by
    intro y hy
    unfold euclideanCoordDeriv
    have hev : w =ᶠ[𝓝 y] v := by
      filter_upwards [isOpen_euclideanBall x (ρ / 2) |>.mem_nhds hy]
        with z hz
      exact hEq hz
    rw [hev.fderiv_eq]
  rw [← euclideanCoordLaplacian_eq_of_eqOn_open
    (isOpen_euclideanBall x (ρ / 2)) hEqDeriv
    (center_mem_euclideanBall x (by linarith : 0 < ρ / 2))]
  exact hglobal

end

end PDE
