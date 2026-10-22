module

public import PDEFoundation.Analysis.Newtonian.WeakType.AssemblyMain
public import PDEFoundation.Analysis.Newtonian.NewtonKernelHolderProof

/-!
# The local weak-type (1,1) estimate for `∇ u_F`

Final assembly: for `F` smooth with `tsupport F ⊆ B₁` and `λ > 0`,
`|{x ∈ B₂ : |∇ u_F x| > λ}| ≤ C(d) ‖F‖₁ / λ`.  The root box is `I = (-4, 4]^d ⊇ B₃`.  If
`λ ≤ ⨍_I |F|` the bound is trivial (`|B₂| ≤ C ‖F‖₁ / λ`); otherwise the Calderón–Zygmund stopping
cubes exist and `volume_gradient_gt_le_of_stopping` applies.
-/

@[expose] public section

open BoxIntegral MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PDE.NewtonWeakType

noncomputable section

variable {d : ℕ}

/-- The root box `(-4, 4]^d`. -/
def rootBox (d : ℕ) : Box (Fin d) :=
  ⟨fun _ => -4, fun _ => 4, fun _ => by norm_num⟩

theorem rootBox_width (d : ℕ) : ∀ i, (rootBox d).upper i - (rootBox d).lower i = 8 := by
  intro i; simp [rootBox]; norm_num

theorem euclideanBall_one_subset_rootBox (d : ℕ) :
    euclideanBall (0 : Vec d) 1 ⊆ ((rootBox d : Box (Fin d)) : Set (Vec d)) := by
  intro y hy
  have h := (mem_euclideanBall_iff_vecEuclideanNorm_lt one_pos).mp hy
  rw [sub_zero] at h
  rw [Box.mem_coe, Box.mem_def]
  intro i
  have := abs_apply_le_vecEuclideanNorm y i
  rw [abs_le] at this
  simp only [rootBox, mem_Ioc]
  constructor <;> linarith [this.1, this.2]

theorem exists_weakType (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ F : Vec d → Vec d, ContDiff ℝ (⊤ : ℕ∞) F →
        tsupport F ⊆ euclideanBall (0 : Vec d) 1 →
        ∀ lam : ℝ, 0 < lam →
          volume {x | x ∈ euclideanBall (0 : Vec d) 2 ∧
              lam < vecEuclideanNorm (classicalGradient (newtonPotential F) x)} ≤
            ENNReal.ofReal (C / lam * ∫ x, vecEuclideanNorm (F x)) := by
  obtain ⟨A, hA0, hA⟩ := NewtonKernelHolderProof.result d hd
  have hK : KernelHolder d newtonKernelJacobian A := fun z z' hz hzz v => hA z z' hz hzz v
  set V : ℝ := (volume (euclideanBall (0 : Vec d) 1)).toReal with hV
  have hV0 : 0 < V := volume_euclideanBall_toReal_pos (0 : Vec d) one_pos
  set Cd : ℝ := (czDilateConst d).toReal with hCd
  have hCd0 : 0 ≤ Cd := ENNReal.toReal_nonneg
  set H : ℝ := hormanderConst d * A * d with hH
  have hH0 : 0 ≤ H := mul_nonneg (mul_nonneg (hormanderConst_nonneg d) hA0.le) (Nat.cast_nonneg d)
  set C2 : ℝ := 4 * 2 ^ d + 2 ^ d * Cd + 4 * H with hC2
  have hC20 : 0 ≤ C2 := by positivity
  set C1 : ℝ := 2 ^ d * V / 8 ^ d with hC1
  have hC10 : 0 < C1 := by positivity
  refine ⟨C1 + C2, by positivity, ?_⟩
  intro F hF hsupp lam hlam
  set I : Box (Fin d) := rootBox d with hI
  have hFc : HasCompactSupport F := by
    refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : Vec d) 1) (isClosed_tsupport F)
      fun y hy => ?_
    have h := (mem_euclideanBall_iff_vecEuclideanNorm_lt one_pos).mp (hsupp hy)
    rw [sub_zero] at h
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_vecEuclideanNorm y).trans h.le
  have hFsupp : ∀ x, x ∉ (I : Set (Vec d)) → F x = 0 := by
    intro x hx
    by_contra hne
    exact hx (euclideanBall_one_subset_rootBox d (hsupp (subset_tsupport F hne)))
  have hFi : ∀ i, Continuous fun x => F x i := fun i => (contDiff_pi.mp hF i).continuous
  have hFI : ∀ i, IntegrableOn (fun x => F x i) (I : Set (Vec d)) := fun i =>
    ((hFi i).integrable_of_hasCompactSupport (hasCompactSupport_apply hFc i)).integrableOn
  set m : ℝ := ∫ x, vecEuclideanNorm (F x) with hm
  have hm0 : 0 ≤ m := integral_nonneg fun _ => vecEuclideanNorm_nonneg _
  have hvolI : (volume (I : Set (Vec d))).toReal = 8 ^ d :=
    volume_box_toReal_eq_pow_of_commonWidth I 8 (rootBox_width d)
  have hIm : ∫ x in (I : Set (Vec d)), vecEuclideanNorm (F x) = m := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    simp [hFsupp x hx, vecEuclideanNorm, vecNormSq, vecDot]
  have havg : integralAverage (I : Set (Vec d)) (fun x => vecEuclideanNorm (F x)) = (8 ^ d)⁻¹ * m := by
    unfold integralAverage
    rw [hvolI, hIm]
  have hpow : (0 : ℝ) < 8 ^ d := by positivity
  by_cases hcase : integralAverage (I : Set (Vec d)) (fun x => vecEuclideanNorm (F x)) < lam
  · obtain ⟨S⟩ := exists_czStopping hd I 8 (rootBox_width d) hFI hcase
    refine (measure_mono fun x hx => hx.2).trans
      ((volume_gradient_gt_le_of_stopping hd hA0.le hK hF hFc hFsupp S).trans ?_)
    refine ENNReal.ofReal_le_ofReal ?_
    have : 0 ≤ C1 * m / lam := by positivity
    calc C2 * m / lam ≤ C2 * m / lam + C1 * m / lam := le_add_of_nonneg_right this
      _ = (C1 + C2) / lam * m := by ring
  · push Not at hcase
    rw [havg] at hcase
    have hball : volume (euclideanBall (0 : Vec d) 2) = ENNReal.ofReal (2 ^ d * V) := by
      rw [volume_euclideanBall_eq_unit_mul_of_pos _ (by norm_num : (0 : ℝ) < 2),
        ENNReal.ofReal_mul (by positivity), hV, ENNReal.ofReal_toReal
          (volume_euclideanBall_ne_top _ zero_le_one)]
    refine (measure_mono fun x hx => hx.1).trans ?_
    rw [hball]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 : 8 ^ d * lam ≤ m := by
      have := mul_le_mul_of_nonneg_left hcase hpow.le
      rwa [← mul_assoc, mul_inv_cancel₀ hpow.ne', one_mul] at this
    have h2 : 2 ^ d * V ≤ C1 * m / lam := by
      rw [hC1, div_mul_eq_mul_div, div_div, le_div_iff₀ (by positivity)]
      have : 2 ^ d * V * (8 ^ d * lam) ≤ 2 ^ d * V * m :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      linarith
    have h3 : 0 ≤ C2 * m / lam := by positivity
    calc 2 ^ d * V ≤ C1 * m / lam := h2
      _ ≤ C1 * m / lam + C2 * m / lam := le_add_of_nonneg_right h3
      _ = (C1 + C2) / lam * m := by ring

end

end PDE.NewtonWeakType
