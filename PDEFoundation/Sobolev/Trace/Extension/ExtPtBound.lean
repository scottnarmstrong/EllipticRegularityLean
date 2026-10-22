module

public import PDEFoundation.Sobolev.Trace.Extension.ExtC1
public import PDEFoundation.Sobolev.Trace.Extension.ExtInvDeriv

/-!
# Pointwise bounds for the summands of the extension

For `x ∈ Ω`, the `j`-th summand `ηⱼ · (F ∘ φⱼ⁻¹)` of `D.ext g` and its gradient are bounded by
`K (|F| + |∇F|) ∘ φⱼ⁻¹` if `x` lies in the chart cylinder, and vanish otherwise.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

/-- The majorant `x ↦ K (|F| + |∇F|)(Ψⱼ⁻¹ x)` of the `j`-th summand, supported on the chart
cylinder. -/
noncomputable def ExtData.majorant (D : ExtData Ω) (j : Fin D.A.N) (K : ℝ) (F : Vec n × ℝ → ℝ)
    (x : Vec (n + 1)) : ℝ :=
  (Ω ∩ (D.A.chart j).dom).indicator
    (fun y => K * (|F ((D.A.chart j).inv y)| + modelGradNorm F ((D.A.chart j).inv y))) x

theorem ExtData.majorant_nonneg (D : ExtData Ω) (j : Fin D.A.N) {K : ℝ} (hK : 0 ≤ K)
    (F : Vec n × ℝ → ℝ) (x : Vec (n + 1)) : 0 ≤ D.majorant j K F x := by
  unfold ExtData.majorant
  refine indicator_nonneg (fun y _ => ?_) x
  have : 0 ≤ modelGradNorm F ((D.A.chart j).inv y) := Real.sqrt_nonneg _
  positivity

/-- The pointwise bound of the `j`-th summand and its gradient on `Ω`. -/
theorem ExtData.term_bound (D : ExtData Ω) (j : Fin D.A.N) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ F : Vec n × ℝ → ℝ, ContDiffOn ℝ 1 F (upperHalf n) → ∀ x ∈ Ω,
      |D.η j x * F ((D.A.chart j).inv x)| ≤ D.majorant j K F x ∧
      vecEuclideanNorm (classicalGradient (fun y => D.η j y * F ((D.A.chart j).inv y)) x) ≤
        D.majorant j K F x := by
  obtain ⟨B, hB0, hB⟩ := exists_cutoff_bounds (D.contDiff_η j) (D.η_compact j)
  set φ := D.A.chart j with hφ
  have hL := φ.L_nonneg
  set M : ℝ := ((n : ℝ) + 1) * (1 + φ.L) with hM
  have hM1 : 1 ≤ M := by
    have : 0 ≤ (n : ℝ) * φ.L := by positivity
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  refine ⟨B * (1 + M), by positivity, fun F hF x hx => ?_⟩
  by_cases hxd : x ∈ φ.dom
  · have hxW : x ∈ Ω ∩ φ.dom := ⟨hx, hxd⟩
    have hind : D.majorant j (B * (1 + M)) F x =
        B * (1 + M) * (|F (φ.inv x)| + modelGradNorm F (φ.inv x)) := by
      unfold ExtData.majorant
      rw [indicator_of_mem hxW]
    rw [hind]
    have hz : φ.inv x ∈ upperHalf n := ext_inv_mem_upperHalf φ hx hxd
    have hFd : DifferentiableAt ℝ F (φ.inv x) :=
      (hF.differentiableOn one_ne_zero).differentiableAt ((isOpen_upperHalf n).mem_nhds hz)
    have hinv : DifferentiableAt ℝ φ.inv x := (φ.contDiff_inv.differentiable (by simp)) x
    have hFi : DifferentiableAt ℝ (fun y => F (φ.inv y)) x := hFd.comp x hinv
    have hηd : DifferentiableAt ℝ (D.η j) x := ((D.contDiff_η j).differentiable (by simp)) x
    have hm0 : 0 ≤ modelGradNorm F (φ.inv x) := Real.sqrt_nonneg _
    have hF0 := abs_nonneg (F (φ.inv x))
    have hη := (hB x).1
    have hηg := (hB x).2
    have hg1 := vecEuclideanNorm_classicalGradient_comp_inv_le φ hFd
    constructor
    · rw [abs_mul]
      calc |D.η j x| * |F (φ.inv x)| ≤ B * |F (φ.inv x)| := by gcongr
        _ ≤ _ := by nlinarith [mul_nonneg hB0 hF0, mul_nonneg hB0 hm0, mul_nonneg hB0 (by linarith : (0:ℝ) ≤ M), mul_nonneg (mul_nonneg hB0 (by linarith : (0:ℝ) ≤ M)) hF0]
    · refine (vecEuclideanNorm_classicalGradient_mul_le hηd hFi).trans ?_
      have h2 : |D.η j x| * vecEuclideanNorm (classicalGradient (F ∘ φ.inv) x) ≤
          B * (M * modelGradNorm F (φ.inv x)) := by
        have : vecEuclideanNorm (classicalGradient (F ∘ φ.inv) x) ≤
            M * modelGradNorm F (φ.inv x) := by
          refine hg1.trans (le_of_eq ?_)
          rw [hM]; ring
        exact mul_le_mul hη this (vecEuclideanNorm_nonneg _) hB0
      have h3 : |F (φ.inv x)| * vecEuclideanNorm (classicalGradient (D.η j) x) ≤
          |F (φ.inv x)| * B := mul_le_mul_of_nonneg_left hηg hF0
      have h4 : (fun y => F (φ.inv y)) = F ∘ φ.inv := rfl
      rw [h4] at *
      nlinarith [mul_nonneg hB0 hF0, mul_nonneg hB0 hm0, mul_nonneg (mul_nonneg hB0 (by linarith : (0:ℝ) ≤ M)) hF0, mul_nonneg (mul_nonneg hB0 (by linarith : (0:ℝ) ≤ M)) hm0]
  · have hxs : x ∉ tsupport (D.η j) := fun h => hxd (D.η_tsupport j h)
    have hind : D.majorant j (B * (1 + M)) F x = 0 := by
      unfold ExtData.majorant
      exact indicator_of_notMem (fun h => hxd h.2) _
    rw [hind]
    have hη0 : D.η j x = 0 := image_eq_zero_of_notMem_tsupport hxs
    have hev : (fun y => D.η j y * F (φ.inv y)) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [(isClosed_tsupport (D.η j)).isOpen_compl.mem_nhds hxs] with y hy
      simp [image_eq_zero_of_notMem_tsupport hy]
    refine ⟨by simp [hη0], ?_⟩
    have hg : classicalGradient (fun y => D.η j y * F (φ.inv y)) x = 0 := by
      funext i
      simp [classicalGradient, hev.fderiv_eq]
    rw [hg]
    exact (vecEuclideanNorm_eq_zero_iff.2 rfl).le

end PDE.TraceLane
