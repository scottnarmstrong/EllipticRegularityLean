module

public import PDEFoundation.Measure.AffineExtendedLpBound
public import PDEFoundation.Measure.BallVolume
public import PDEFoundation.Measure.FixedNormalizationBound
public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.Sobolev.W1p.EuclideanGradient

/-! # Finite local norms from an interior essential bound -/

@[expose] public section

namespace PDE

open MeasureTheory Set
open scoped _root_.ENNReal

noncomputable section

/-- An actual essential bound on the three-quarter ball gives finite local
`Lᵖ` membership and a uniform fixed-unit-volume normalization on every source
iteration radius. -/
theorem exists_uniform_interior_eLpNorm_of_ae_bound
    {d : ℕ} (u : H1Function (euclideanBall (0 : Vec d) 1))
    {p M : ℝ} (hp : 1 ≤ p) (hM : 0 ≤ M)
    (hbound : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) (3 / 4)),
      vecEuclideanNorm (u.grad x) ≤ M) :
    ∀ r, 1 / 2 ≤ r → r < 3 / 4 →
      MemLp (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
          (volumeOn (euclideanBall (0 : Vec d) r)) ∧
        eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
            ((volume (euclideanBall (0 : Vec d) 1))⁻¹ •
              volumeOn (euclideanBall (0 : Vec d) r)) ≤
          ENNReal.ofReal M := by
  intro r hr _hr34
  have hr0 : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hsub : euclideanBall (0 : Vec d) r ⊆
      euclideanBall (0 : Vec d) (3 / 4) := by
    intro x hx
    exact (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).2
      ((mem_euclideanBall_iff_vecEuclideanNorm_lt hr0).1 hx |>.trans _hr34)
  have hboundr : ∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) r),
      vecEuclideanNorm (u.grad x) ≤ M :=
    ae_mono (Measure.restrict_mono hsub le_rfl) hbound
  have hunitSub : euclideanBall (0 : Vec d) r ⊆
      euclideanBall (0 : Vec d) 1 := by
    intro x hx
    exact (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).2
      ((mem_euclideanBall_iff_vecEuclideanNorm_lt hr0).1 hx |>.trans
        (lt_trans _hr34 (by norm_num)))
  have hmeas : AEStronglyMeasurable (fun x => vecEuclideanNorm (u.grad x))
      (volumeOn (euclideanBall (0 : Vec d) r)) :=
    (u.gradMemL2.memLp_vecEuclideanNorm.mono_measure
      (Measure.restrict_mono hunitSub le_rfl)).aestronglyMeasurable
  let : IsFiniteMeasure (volumeOn (euclideanBall (0 : Vec d) r)) :=
    isFiniteMeasure_volumeOn_euclideanBall (0 : Vec d) hr0.le
  have hmem : MemLp (fun x => vecEuclideanNorm (u.grad x))
      (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) r)) := by
    apply MemLp.of_bound hmeas M
    filter_upwards [hboundr] with x hx
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (vecEuclideanNorm_nonneg _)] using hx
  refine ⟨hmem, ?_⟩
  let V := volume (euclideanBall (0 : Vec d) 1)
  have hVTop : V ≠ ∞ := volume_euclideanBall_ne_top (0 : Vec d) (by norm_num)
  have hmass : volumeOn (euclideanBall (0 : Vec d) r) Set.univ ≤ V := by
    rw [Measure.restrict_apply_univ]
    exact measure_mono hunitSub
  have hraw := eLpNorm_le_of_ae_ofReal_abs_le_add_mul
    (volumeOn (euclideanBall (0 : Vec d) r))
    (fun x => vecEuclideanNorm (u.grad x)) (fun _ => 0) measurable_const
    hmeas hp hM (by norm_num : (0 : ℝ) ≤ 0) (by
      filter_upwards [hboundr] with x hx
      simp only [ENNReal.ofReal_zero, zero_mul, add_zero]
      apply ENNReal.ofReal_le_ofReal
      simpa only [abs_of_nonneg (vecEuclideanNorm_nonneg _)] using hx)
  have hfixed := eLpNorm_fixedNormalization_le_of_raw_bound
    (volumeOn (euclideanBall (0 : Vec d) r))
    (volumeOn (euclideanBall (0 : Vec d) r))
    (fun x => vecEuclideanNorm (u.grad x)) (fun _ => 0)
    hVTop hmass (zero_lt_one.trans_le hp) (ENNReal.ofReal M) 0
      (by simpa using hraw)
  simpa only [V, zero_mul, add_zero] using hfixed

end

end PDE
