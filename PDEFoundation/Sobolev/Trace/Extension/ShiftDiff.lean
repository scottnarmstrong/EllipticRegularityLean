module

public import PDEFoundation.Sobolev.Trace.Extension.ShiftChain
public import PDEFoundation.Sobolev.Trace.Smooth.PullbackBound

/-!
# Pointwise bounds for the difference of two vertical shifts

For a chart `φ`, a cutoff `η` with `tsupport η ⊆ dom` and `F` which is `C¹` on the open
half-space, the difference `U = η·(F ∘ (φ⁻¹ + (0, τ))) - η·(F ∘ φ⁻¹)` and its gradient are bounded
at points `x ∈ Ω` by `B (3 + L) · R(φ⁻¹ x)`, where `R` is the sum of the absolute differences of
`F`, `∂ₜF` and the Euclidean norm of the difference of `∇'F` between `(x', t + τ)` and `(x', t)`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

/-- Sum of the differences of `F`, `∂ₜF` and `∇'F` under the vertical shift by `τ`. -/
noncomputable def shiftR (F : Vec n × ℝ → ℝ) (τ : ℝ) (z : Vec n × ℝ) : ℝ :=
  |F (z.1, z.2 + τ) - F z| + |normDeriv F (z.1, z.2 + τ) - normDeriv F z| +
    vecEuclideanNorm (tanGrad F (z.1, z.2 + τ) - tanGrad F z)

theorem shiftR_nonneg (F : Vec n × ℝ → ℝ) (τ : ℝ) (z : Vec n × ℝ) : 0 ≤ shiftR F τ z := by
  unfold shiftR
  have := vecEuclideanNorm_nonneg (tanGrad F (z.1, z.2 + τ) - tanGrad F z)
  positivity

theorem shift_add_vert (z : Vec n × ℝ) (τ : ℝ) : z + ((0 : Vec n), τ) = (z.1, z.2 + τ) :=
  Prod.ext (by simp) rfl

/-- The model gradient length of the shift difference. -/
theorem modelGradNorm_shiftDiff_le {F : Vec n × ℝ → ℝ} {z : Vec n × ℝ} {τ : ℝ}
    (h0 : DifferentiableAt ℝ F z) (h1 : DifferentiableAt ℝ F (z.1, z.2 + τ)) :
    modelGradNorm (fun y => F (y + ((0 : Vec n), τ)) - F y) z ≤
      vecEuclideanNorm (tanGrad F (z.1, z.2 + τ) - tanGrad F z) +
        |normDeriv F (z.1, z.2 + τ) - normDeriv F z| := by
  have h1' : DifferentiableAt ℝ F (z + ((0 : Vec n), τ)) := by rwa [shift_add_vert]
  have hd : DifferentiableAt ℝ (fun y => F (y + ((0 : Vec n), τ))) z :=
    (differentiableAt_comp_add_right _).2 h1'
  have hf : fderiv ℝ (fun y => F (y + ((0 : Vec n), τ)) - F y) z =
      fderiv ℝ F (z + ((0 : Vec n), τ)) - fderiv ℝ F z := by
    rw [fderiv_fun_sub hd h0, fderiv_comp_add_right]
  have ht : tanGrad (fun y => F (y + ((0 : Vec n), τ)) - F y) z =
      tanGrad F (z.1, z.2 + τ) - tanGrad F z := by
    funext i
    simp only [tanGrad, Pi.sub_apply]
    rw [hf, shift_add_vert]
    rfl
  have hn : normDeriv (fun y => F (y + ((0 : Vec n), τ)) - F y) z =
      normDeriv F (z.1, z.2 + τ) - normDeriv F z := by
    simp only [normDeriv]
    rw [hf, shift_add_vert]
    rfl
  unfold modelGradNorm
  rw [ht, hn]
  exact real_sqrt_add_sq_le _ _ (vecNormSq_nonneg _)

variable (φ : GraphChart Ω) {η : Vec (n + 1) → ℝ} {F : Vec n × ℝ → ℝ}

/-- Pointwise bound for the difference of two shifts. -/
theorem shift_term_diff_bound (hη : ContDiff ℝ 1 η) (hts : tsupport η ⊆ φ.dom)
    (hF : ContDiffOn ℝ 1 F (upperHalf n)) {τ : ℝ} (hτ : 0 < τ) {B : ℝ}
    (hB : ∀ y, |η y| ≤ B ∧ vecEuclideanNorm (classicalGradient η y) ≤ B) {x : Vec (n + 1)}
    (hx : x ∈ Ω) :
    |η x * F (φ.inv x + ((0 : Vec n), τ)) - η x * F (φ.inv x + ((0 : Vec n), 0))| ≤
        B * (3 + φ.L) * (upperHalf n).indicator (shiftR F τ) (φ.inv x) ∧
      vecEuclideanNorm (classicalGradient (fun y => η y * F (φ.inv y + ((0 : Vec n), τ)) -
        η y * F (φ.inv y + ((0 : Vec n), 0))) x) ≤
        B * (3 + φ.L) * (upperHalf n).indicator (shiftR F τ) (φ.inv x) := by
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0).1
  have hL := φ.L_nonneg
  have hC : 1 ≤ 3 + φ.L := by linarith
  by_cases hxs : x ∈ tsupport η
  · have hz : φ.inv x ∈ upperHalf n := mem_upperHalf.2 (φ.inv_snd_pos_of_mem hx (hts hxs))
    rw [indicator_of_mem hz]
    have hR0 := shiftR_nonneg F τ (φ.inv x)
    have hd0 : DifferentiableAt ℝ F (φ.inv x) :=
      ((hF.contDiffAt ((isOpen_upperHalf n).mem_nhds hz)).differentiableAt one_ne_zero)
    have hz1 : ((φ.inv x).1, (φ.inv x).2 + τ) ∈ upperHalf n := by
      rw [mem_upperHalf]; simp only; linarith [mem_upperHalf.1 hz]
    have hd1 : DifferentiableAt ℝ F ((φ.inv x).1, (φ.inv x).2 + τ) :=
      ((hF.contDiffAt ((isOpen_upperHalf n).mem_nhds hz1)).differentiableAt one_ne_zero)
    set G : Vec n × ℝ → ℝ := fun y => F (y + ((0 : Vec n), τ)) - F y with hG
    have hGd : DifferentiableAt ℝ G (φ.inv x) := by
      refine DifferentiableAt.sub ((differentiableAt_comp_add_right _).2 ?_) hd0
      rwa [shift_add_vert]
    have hU : (fun y => η y * F (φ.inv y + ((0 : Vec n), τ)) -
        η y * F (φ.inv y + ((0 : Vec n), 0))) = fun y => η y * (G ∘ φ.inv) y := by
      funext y
      simp only [hG, Function.comp, Prod.mk_zero_zero, add_zero, mul_sub]
    have hGinv : DifferentiableAt ℝ (G ∘ φ.inv) x :=
      hGd.comp x (φ.hasFDerivAt_inv x).differentiableAt
    have hηd : DifferentiableAt ℝ η x := (hη.differentiable (by simp)) x
    have hGabs : |G (φ.inv x)| ≤ shiftR F τ (φ.inv x) := by
      have : G (φ.inv x) = F ((φ.inv x).1, (φ.inv x).2 + τ) - F (φ.inv x) := by
        simp only [hG, shift_add_vert]
      rw [this]; unfold shiftR
      have := vecEuclideanNorm_nonneg (tanGrad F ((φ.inv x).1, (φ.inv x).2 + τ) -
        tanGrad F (φ.inv x))
      linarith [abs_nonneg (normDeriv F ((φ.inv x).1, (φ.inv x).2 + τ) - normDeriv F (φ.inv x))]
    have hM := modelGradNorm_shiftDiff_le hd0 hd1
    have hGrad := φ.gradNorm_comp_inv_le hGd
    have hU0 : η x * F (φ.inv x + ((0 : Vec n), τ)) - η x * F (φ.inv x + ((0 : Vec n), 0)) =
        η x * G (φ.inv x) := by
      simp only [hG, mul_sub, Prod.mk_zero_zero, add_zero]
    constructor
    · rw [hU0, abs_mul]
      calc |η x| * |G (φ.inv x)| ≤ B * shiftR F τ (φ.inv x) :=
            mul_le_mul (hB x).1 hGabs (abs_nonneg _) hB0
        _ ≤ _ := by nlinarith [mul_nonneg hB0 hR0]
    · rw [hU]
      refine (vecEuclideanNorm_classicalGradient_mul_le hηd hGinv).trans ?_
      have e1 : |η x| * vecEuclideanNorm (classicalGradient (G ∘ φ.inv) x) ≤
          B * ((2 + φ.L) * (vecEuclideanNorm (tanGrad F ((φ.inv x).1, (φ.inv x).2 + τ) -
            tanGrad F (φ.inv x)) +
            |normDeriv F ((φ.inv x).1, (φ.inv x).2 + τ) - normDeriv F (φ.inv x)|)) := by
        refine mul_le_mul (hB x).1 (hGrad.trans ?_) (vecEuclideanNorm_nonneg _) hB0
        exact mul_le_mul_of_nonneg_left hM (by linarith)
      have e2 : |(G ∘ φ.inv) x| * vecEuclideanNorm (classicalGradient η x) ≤
          shiftR F τ (φ.inv x) * B :=
        mul_le_mul hGabs (hB x).2 (vecEuclideanNorm_nonneg _) hR0
      unfold shiftR at e2 hR0 ⊢
      have := vecEuclideanNorm_nonneg (tanGrad F ((φ.inv x).1, (φ.inv x).2 + τ) -
        tanGrad F (φ.inv x))
      have h5 := abs_nonneg (normDeriv F ((φ.inv x).1, (φ.inv x).2 + τ) - normDeriv F (φ.inv x))
      have h6 := abs_nonneg (F ((φ.inv x).1, (φ.inv x).2 + τ) - F (φ.inv x))
      nlinarith [mul_nonneg hB0 this, mul_nonneg hB0 h5, mul_nonneg hB0 h6,
        mul_nonneg (mul_nonneg hB0 (by linarith : (0 : ℝ) ≤ 1 + φ.L)) this,
        mul_nonneg (mul_nonneg hB0 (by linarith : (0 : ℝ) ≤ 1 + φ.L)) h5]
  · have hev : (fun y => η y * F (φ.inv y + ((0 : Vec n), τ)) -
        η y * F (φ.inv y + ((0 : Vec n), 0))) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [(isClosed_tsupport η).isOpen_compl.mem_nhds hxs] with y hy
      simp [image_eq_zero_of_notMem_tsupport hy]
    have hR : 0 ≤ B * (3 + φ.L) * (upperHalf n).indicator (shiftR F τ) (φ.inv x) := by
      refine mul_nonneg (by positivity) ?_
      by_cases hz : φ.inv x ∈ upperHalf n
      · rw [indicator_of_mem hz]; exact shiftR_nonneg _ _ _
      · rw [indicator_of_notMem hz]
    have hf : fderiv ℝ (fun y => η y * F (φ.inv y + ((0 : Vec n), τ)) -
        η y * F (φ.inv y + ((0 : Vec n), 0))) x = 0 := by
      rw [hev.fderiv_eq]; simp
    refine ⟨?_, ?_⟩
    · have := hev.self_of_nhds
      simp only [this] at *
      simpa using hR
    · have : classicalGradient (fun y => η y * F (φ.inv y + ((0 : Vec n), τ)) -
        η y * F (φ.inv y + ((0 : Vec n), 0))) x = 0 := by
        funext i; simp [classicalGradient, hf]
      rw [this]
      have h0 : vecEuclideanNorm (0 : Vec (n + 1)) = 0 := vecEuclideanNorm_eq_zero_iff.2 rfl
      rw [h0]; exact hR

end PDE.TraceLane
