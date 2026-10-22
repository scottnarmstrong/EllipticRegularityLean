module

public import PDEFoundation.PDE.HolderEllipticScale
public import PDEFoundation.Regularity.GradientEstimateFromMeans
public import PDEFoundation.Sobolev.H1.InteriorBallEnergy
public import PDEFoundation.Regularity.FieldHolderSeminorm

/-! # The higher-dimensional interior Schauder estimate -/

@[expose] public section

namespace PDE

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

/-- The quantitative interior Schauder estimate in dimensions at least two. -/
theorem exists_schauderC1alpha_constant_higherDimensional
    {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} :
    ∃ C : ℝ, 0 < C ∧ ∀ {α : ℝ}, 0 < α → α < 1 →
      ∀ {r₀ : ℝ}, 0 < r₀ → r₀ ≤ 1 / 4 →
      ∀ (a : CoeffField d) (F : Vec d → Vec d),
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ ha : ∃ K : ℝ, 0 ≤ K ∧
        EuclideanMatrixHolderSeminormLE (euclideanBall (0 : Vec d) 1) a α K,
      ∀ hF : ∃ K : ℝ, 0 ≤ K ∧
        EuclideanFieldHolderSeminormLE (euclideanBall (0 : Vec d) 1) F α K,
      r₀ ^ α * euclideanMatrixHolderSeminormOn (euclideanBall (0 : Vec d) 1) a α ha ≤
        C⁻¹ * α * (1 - α) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u 0 F →
      ∃ G : Vec d → Vec d,
      ∃ hG : ∃ K : ℝ, 0 ≤ K ∧
        EuclideanFieldHolderSeminormLE (euclideanBall (0 : Vec d) (1 / 2)) G α K,
      ∃ hgrad : MemLp (fun x => vecEuclideanNorm (u.grad x)) ∞
        (volumeOn (euclideanBall (0 : Vec d) (1 / 2))),
      G =ᵐ[volumeOn (euclideanBall (0 : Vec d) (1 / 2))] u.grad ∧
      euclideanFieldLpNormOn (euclideanBall (0 : Vec d) (1 / 2)) ∞ u.grad hgrad +
        r₀ ^ α * euclideanFieldHolderSeminormOn
          (euclideanBall (0 : Vec d) (1 / 2)) G α hG ≤
        (C / α ^ 2) * (r₀ ^ (-(d : ℝ) / 2) *
          Real.sqrt (integralAverage (euclideanBall (0 : Vec d) 1)
            (fun x => vecNormSq (u.grad x))) +
          r₀ ^ α / (1 - α) *
            euclideanFieldHolderSeminormOn (euclideanBall (0 : Vec d) 1) F α hF) := by
  let : NeZero d := ⟨Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_two hd)⟩
  obtain ⟨Clocal, hClocal, hlocal⟩ := exists_holder_elliptic_scale_constant hd Λ
  obtain ⟨Cg, hCg, hgradient⟩ :=
    exists_gradientEstimateFromMeans_constant (lt_of_lt_of_le Nat.zero_lt_two hd)
  let D : ℝ := (2 : ℝ) ^ ((d : ℝ) / 2)
  let H : ℝ := 1 + 2 * D
  let T : ℝ := 32 * H * (1 + D)
  let C : ℝ := Cg * Clocal + T + 1
  have hD : 0 ≤ D := Real.rpow_nonneg (by norm_num) _
  have hH : 0 < H := by dsimp [H]; positivity
  have hT : 0 < T := by dsimp [T]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro α hα hα1 r₀ hr₀ hr₀le a F hell ha hF hsmall u hsol
  let Ka := euclideanMatrixHolderSeminormOn (euclideanBall (0 : Vec d) 1) a α ha
  let KF := euclideanFieldHolderSeminormOn (euclideanBall (0 : Vec d) 1) F α hF
  have hKa : 0 ≤ Ka := euclideanMatrixHolderSeminormOn_nonneg ha
  have hKF : 0 ≤ KF := euclideanFieldHolderSeminormOn_nonneg hF
  have haKa := euclideanMatrixHolderSeminormOn_bound ha
  have hFKF := euclideanFieldHolderSeminormOn_bound hF
  have hgap : 0 < 1 - α := sub_pos.mpr hα1
  have hq : 0 ≤ r₀ ^ α * Ka :=
    mul_nonneg (Real.rpow_nonneg hr₀.le _) hKa
  have hTC : T ≤ C := by
    dsimp [C]
    have : 0 ≤ Cg * Clocal := mul_nonneg hCg.le hClocal.le
    linarith
  have hCq : C * (r₀ ^ α * Ka) ≤ α * (1 - α) := by
    calc
      _ ≤ C * (C⁻¹ * α * (1 - α)) :=
        mul_le_mul_of_nonneg_left hsmall hC.le
      _ = α * (1 - α) := by field_simp [hC.ne']
  have hsmallLocal : H * r₀ ^ α * Ka ≤
      α * (1 - α) / (32 * (1 + D)) := by
    have hden : 0 < 32 * (1 + D) := by positivity
    apply (le_div_iff₀ hden).2
    calc
      H * r₀ ^ α * Ka * (32 * (1 + D)) = T * (r₀ ^ α * Ka) := by
        dsimp [T]
        ring
      _ ≤ C * (r₀ ^ α * Ka) := mul_le_mul_of_nonneg_right hTC hq
      _ ≤ α * (1 - α) := hCq
  let M := Real.sqrt (integralAverage (euclideanBall (0 : Vec d) 1)
    (fun x => vecNormSq (u.grad x)))
  let X := r₀ ^ (-(d : ℝ) / 2) * M
  let Y := r₀ ^ α * KF / (1 - α)
  let S := X + Y
  let A := Clocal * S
  have hM : 0 ≤ M := Real.sqrt_nonneg _
  have hX : 0 ≤ X := mul_nonneg (Real.rpow_nonneg hr₀.le _) hM
  have hY : 0 ≤ Y := div_nonneg
    (mul_nonneg (Real.rpow_nonneg hr₀.le _) hKF) hgap.le
  have hS : 0 ≤ S := add_nonneg hX hY
  have hA : 0 ≤ A := mul_nonneg hClocal.le hS
  have hmeans : ∀ z ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ,
      0 < r → r ≤ r₀ →
      Real.sqrt (integralAverage (euclideanBall z r)
        (fun x => vecNormSq (u.grad x))) ≤ A / α ∧
      (r₀ / r) ^ α * centeredVectorMeanL2 (euclideanBall z r) u.grad ≤ A / α := by
    intro z hz r hr hrr₀
    have hr₀half : r₀ ≤ 1 / 2 := hr₀le.trans (by norm_num)
    have hsub : euclideanBall z r₀ ⊆ euclideanBall (0 : Vec d) 1 :=
      (euclideanBall_mono hr₀.le hr₀half).trans
        (euclideanBall_half_subset_unit_of_center_mem_half hz)
    let uz : H1Function (euclideanBall z r₀) :=
      u.restrict (isOpen_euclideanBall z r₀) hsub
    have hsolz : IsWeakDivergenceFormSolutionOn a (euclideanBall z r₀) uz 0 F :=
      hsol.restrict (isOpen_euclideanBall (0 : Vec d) 1)
        (isOpen_euclideanBall z r₀) hsub
    have hzlocal := hlocal hr₀ hα hα1 hKa hKF
      (fun x hx => hell x (hsub hx))
      (fun x hx y hy v => haKa x (hsub hx) y (hsub hy) v)
      (hFKF.mono_set hsub) uz hsolz hsmallLocal r hr hrr₀
    have hinitial := sqrt_integralAverage_vecNormSq_interiorBall_le
      hz hr₀ hr₀half u.gradMemL2
    have hbracket : Real.sqrt (integralAverage (euclideanBall z r₀)
          (fun x => vecNormSq (u.grad x))) + r₀ ^ α * KF / (1 - α) ≤ S := by
      dsimp [S, X, Y, M]
      exact add_le_add hinitial le_rfl
    have hbound : (Clocal / α) *
        (Real.sqrt (integralAverage (euclideanBall z r₀)
          (fun x => vecNormSq (u.grad x))) + r₀ ^ α * KF / (1 - α)) ≤ A / α := by
      calc
        _ = (Clocal * (Real.sqrt (integralAverage (euclideanBall z r₀)
            (fun x => vecNormSq (u.grad x))) + r₀ ^ α * KF / (1 - α))) / α := by
          ring
        _ ≤ (Clocal * S) / α := div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hbracket hClocal.le) hα.le
        _ = A / α := by rfl
    simpa only [uz, H1Function.restrict_grad] using
      ⟨hzlocal.1.trans hbound, hzlocal.2.trans hbound⟩
  obtain ⟨G, hG, hgrad, hGae, hestimate⟩ :=
    hgradient hα hα1 hr₀ hr₀le hA u.gradMemL2 hmeans
  refine ⟨G, hG, hgrad, hGae, hestimate.trans ?_⟩
  have hcoef : Cg * Clocal ≤ C := by
    dsimp [C]
    linarith [hT.le]
  calc
    (Cg / α ^ 2) * A = ((Cg * Clocal) / α ^ 2) * S := by
      dsimp [A]
      ring
    _ ≤ (C / α ^ 2) * S := by
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hcoef (sq_nonneg α)) hS
    _ = _ := by dsimp [S, X, Y, M, KF]; ring

end

end PDE
