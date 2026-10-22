module

public import PDEFoundation.Ambient.RadialLogFieldBounds
public import PDEFoundation.Measure.BallVolume

/-!
# Essential unboundedness of radial logarithmic modes
-/

@[expose] public section

namespace PDE

open MeasureTheory Set
open scoped ENNReal

noncomputable section

private theorem measurable_log_vecEuclideanNorm {d : ℕ} :
    Measurable (fun x : Vec d => Real.log (vecEuclideanNorm x)) := by
  apply measurable_of_continuousOn_compl_singleton 0
  apply continuous_vecEuclideanNorm.continuousOn.log
  intro x hx
  exact (vecEuclideanNorm_pos_iff.mpr hx).ne'

/-- The logarithm of the Euclidean radius is not essentially bounded on any
positive-radius native round ball in positive dimension. -/
theorem not_memLp_top_log_vecEuclideanNorm_euclideanBall
    {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 < R) :
    ¬MemLp (fun x : Vec d => Real.log (vecEuclideanNorm x)) ⊤
      (volume.restrict (euclideanBall 0 R)) := by
  let : NeZero d := ⟨Nat.ne_of_gt hd⟩
  intro hlog
  have htop : eLpNormEssSup
      (fun x : Vec d => Real.log (vecEuclideanNorm x))
      (volume.restrict (euclideanBall 0 R)) < ⊤ := by
    rw [← eLpNorm_exponent_top hlog.aestronglyMeasurable]
    exact hlog.eLpNorm_lt_top
  obtain ⟨C, hC⟩ :=
    eLpNormEssSup_lt_top_iff_isBoundedUnder.mp htop
  let ε : ℝ := min (R / 2) (Real.exp (-((C : ℝ) + 1)))
  have hε : 0 < ε := by
    dsimp only [ε]
    exact lt_min (half_pos hR) (Real.exp_pos _)
  have hεR : ε < R := by
    exact (min_le_left _ _).trans_lt (half_lt_self hR)
  have hsubset : euclideanBall (0 : Vec d) ε ⊆ euclideanBall 0 R := by
    intro x hx
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hε] at hx
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hR]
    simpa only [sub_zero] using hx.trans hεR
  have hμ : volume.restrict (euclideanBall (0 : Vec d) ε) ≤
      volume.restrict (euclideanBall 0 R) :=
    Measure.restrict_mono hsubset le_rfl
  have hCε : ∀ᵐ x ∂volume.restrict (euclideanBall (0 : Vec d) ε),
      ‖Real.log (vecEuclideanNorm x)‖₊ ≤ C :=
    ae_mono hμ hC
  have hne : ∀ᵐ x ∂volume.restrict (euclideanBall (0 : Vec d) ε),
      x ≠ 0 := by
    rw [ae_iff]
    have hz : volume {(0 : Vec d)} = 0 := measure_singleton 0
    simpa only [not_ne_iff] using! le_zero_iff.mp (calc
      (volume.restrict (euclideanBall (0 : Vec d) ε)) {0} ≤ volume {0} :=
        Measure.restrict_le_self {0}
      _ = 0 := hz)
  obtain ⟨x, hxBall, hxBound, hxne⟩ :=
    Measure.exists_mem_of_measure_ne_zero_of_ae
      (volume_euclideanBall_pos (0 : Vec d) hε).ne'
      (hCε.and hne)
  have hr : 0 < vecEuclideanNorm x := vecEuclideanNorm_pos_iff.mpr hxne
  have hrε : vecEuclideanNorm x < ε := by
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hε] at hxBall
    simpa only [sub_zero] using hxBall
  have hrexp : vecEuclideanNorm x < Real.exp (-((C : ℝ) + 1)) :=
    hrε.trans_le (min_le_right _ _)
  have hloglt : Real.log (vecEuclideanNorm x) < -((C : ℝ) + 1) := by
    rw [← Real.log_exp (-((C : ℝ) + 1))]
    exact Real.strictMonoOn_log hr (Real.exp_pos _) hrexp
  have habs : (C : ℝ) < |Real.log (vecEuclideanNorm x)| := by
    rw [abs_of_neg (lt_trans hloglt (by
      have hC0 : 0 ≤ (C : ℝ) := C.coe_nonneg
      linarith : -((C : ℝ) + 1) < 0))]
    linarith
  have hboundReal : |Real.log (vecEuclideanNorm x)| ≤ (C : ℝ) := by
    exact_mod_cast hxBound
  exact (not_lt_of_ge hboundReal) habs

/-- The Euclidean magnitude of the logarithmic gradient field is not
essentially bounded on any positive-radius native round ball. -/
theorem not_memLp_top_vecEuclideanNorm_radialLogGradientField_euclideanBall
    {d : ℕ} (hd : 0 < d) (k : Fin d) {R : ℝ} (hR : 0 < R) :
    ¬MemLp (fun x : Vec d => vecEuclideanNorm (radialLogGradientField k x)) ⊤
      (volume.restrict (euclideanBall 0 R)) := by
  intro hG
  let μ := volume.restrict (euclideanBall (0 : Vec d) R)
  have hsum : MemLp
      (fun x : Vec d => vecEuclideanNorm (radialLogGradientField k x) + 1)
      ⊤ μ := by
    simpa only [Pi.add_apply] using! hG.add (memLp_top_const (1 : ℝ))
  have hmeas : AEStronglyMeasurable
      (fun x : Vec d => Real.log (vecEuclideanNorm x)) μ :=
    measurable_log_vecEuclideanNorm.aestronglyMeasurable
  have hlog : MemLp (fun x : Vec d => Real.log (vecEuclideanNorm x)) ⊤ μ :=
    hsum.mono hmeas (ae_of_all _ fun x => by
      rw [Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (add_nonneg (vecEuclideanNorm_nonneg _) zero_le_one)]
      linarith only [(vecEuclideanNorm_radialLogGradientField_bounds k x).1])
  exact not_memLp_top_log_vecEuclideanNorm_euclideanBall hd hR hlog

end

end PDE
