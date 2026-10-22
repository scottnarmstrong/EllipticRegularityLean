module

public import PDEFoundation.Sobolev.Ch4.Local
public import PDEFoundation.Sobolev.ClassicalGradient
public import PDEFoundation.Ambient.Basis
public import Mathlib.Analysis.Calculus.Rademacher

/-!
# Euclidean-Lipschitz functions

`EucLip L η` says that `η` is `L`-Lipschitz for the *Euclidean* distance `vecEuclideanNorm (x - y)`
(not the sup-norm distance of the inherited metric).  By Rademacher's theorem such a function is
differentiable almost everywhere, and at a point of differentiability the Euclidean norm of its
gradient is at most `L`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace PDE.Ch4Infra

variable {d : ℕ}

/-- `η` is `L`-Lipschitz for the Euclidean distance on `Vec d`. -/
def EucLip (L : ℝ) (η : Vec d → ℝ) : Prop :=
  ∀ x y, |η x - η y| ≤ L * vecEuclideanNorm (x - y)

namespace EucLip

variable {L : ℝ} {η : Vec d → ℝ}

/-- A function that is `L`-Lipschitz for the inherited (sup) norm is `L`-Lipschitz for the
Euclidean distance (the Euclidean norm dominates the sup norm). -/
theorem of_norm {K : ℝ} (hK : 0 ≤ K) (h : ∀ x y, |η x - η y| ≤ K * ‖x - y‖) : EucLip K η :=
  fun x y => (h x y).trans (mul_le_mul_of_nonneg_left (norm_le_vecEuclideanNorm _) hK)

theorem nonneg (h : EucLip L η) (hd : 0 < d) : 0 ≤ L := by
  by_contra hL
  replace hL := lt_of_not_ge hL
  let x : Vec d := 0
  let y : Vec d := basisVec ⟨0, hd⟩
  have := h x y
  have hy : vecEuclideanNorm (x - y) = 1 := by
    show vecEuclideanNorm (0 - basisVec _) = 1
    rw [zero_sub, vecEuclideanNorm_neg, vecEuclideanNorm_basisVec]
  rw [hy] at this
  linarith [abs_nonneg (η x - η y)]

theorem lipschitzWith (h : EucLip L η) (hL : 0 ≤ L) :
    LipschitzWith (⟨L * Real.sqrt d, by positivity⟩ : NNReal) η := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, dist_eq_norm]
  refine (h x y).trans ?_
  show _ ≤ L * Real.sqrt d * _
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (vecEuclideanNorm_le_sqrt_natCast_mul_norm _) hL

theorem continuous (h : EucLip L η) (hL : 0 ≤ L) : Continuous η :=
  (h.lipschitzWith hL).continuous

theorem ae_differentiableAt (h : EucLip L η) (hL : 0 ≤ L) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), DifferentiableAt ℝ η x :=
  (h.lipschitzWith hL).ae_differentiableAt

/-- At a point of differentiability, the derivative in any direction `v` is at most
`L * |v|` (Euclidean length). -/
theorem abs_fderiv_le (h : EucLip L η) (hL : 0 ≤ L) {x : Vec d} (hx : DifferentiableAt ℝ η x)
    (v : Vec d) : |fderiv ℝ η x v| ≤ L * vecEuclideanNorm v := by
  have hγ : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have h1 : HasDerivAt (fun t : ℝ => η (x + t • v)) (fderiv ℝ η x v) 0 := by
    have hx' : HasFDerivAt η (fderiv ℝ η x) (x + (0 : ℝ) • v) := by simpa using hx.hasFDerivAt
    have := hx'.comp_hasDerivAt (0 : ℝ) hγ
    exact this
  have := h1.le_of_lip' (C := L * vecEuclideanNorm v) (mul_nonneg hL (vecEuclideanNorm_nonneg v))
    (Eventually.of_forall fun t => by
      simp only [zero_smul, add_zero, Real.norm_eq_abs, sub_zero]
      refine (h _ _).trans ?_
      rw [show x + t • v - x = t • v by abel, vecEuclideanNorm_smul]
      linarith)
  simpa using this

/-- The Euclidean length of the gradient of an `L`-Lipschitz function is at most `L` at every
point of differentiability. -/
theorem vecEuclideanNorm_classicalGradient_le (h : EucLip L η) (hL : 0 ≤ L) {x : Vec d}
    (hx : DifferentiableAt ℝ η x) : vecEuclideanNorm (classicalGradient η x) ≤ L := by
  set g := classicalGradient η x with hg
  have h1 : fderiv ℝ η x g = vecNormSq g := by
    conv_lhs => rw [← sum_smul_basisVec g]
    rw [map_sum]
    simp only [map_smul, smul_eq_mul, vecNormSq, vecDot]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hg]
  have h2 := abs_fderiv_le h hL hx g
  rw [h1, abs_of_nonneg (vecNormSq_nonneg g)] at h2
  have h3 : vecEuclideanNorm g * vecEuclideanNorm g ≤ L * vecEuclideanNorm g := by
    nlinarith [vecEuclideanNorm_sq g]
  rcases (vecEuclideanNorm_nonneg g).eq_or_lt with h0 | h0
  · rw [← h0]; exact hL
  · exact le_of_mul_le_mul_right h3 h0

theorem abs_partialDeriv_le (h : EucLip L η) (hL : 0 ≤ L) {x : Vec d}
    (hx : DifferentiableAt ℝ η x) (i : Fin d) : |fderiv ℝ η x (basisVec i)| ≤ L := by
  have := h.abs_fderiv_le hL hx (basisVec i)
  rwa [vecEuclideanNorm_basisVec, mul_one] at this

theorem mono (h : EucLip L η) {L' : ℝ} (hLL : L ≤ L') : EucLip L' η := fun x y =>
  (h x y).trans (mul_le_mul_of_nonneg_right hLL (vecEuclideanNorm_nonneg _))

theorem const (c : ℝ) : EucLip 0 (fun _ : Vec d => c) := fun x y => by simp

theorem add {L' : ℝ} {ζ : Vec d → ℝ} (h : EucLip L η) (h' : EucLip L' ζ) :
    EucLip (L + L') (fun x => η x + ζ x) := fun x y => by
  calc |η x + ζ x - (η y + ζ y)| = |(η x - η y) + (ζ x - ζ y)| := by ring_nf
    _ ≤ |η x - η y| + |ζ x - ζ y| := abs_add_le _ _
    _ ≤ L * vecEuclideanNorm (x - y) + L' * vecEuclideanNorm (x - y) := add_le_add (h x y) (h' x y)
    _ = (L + L') * vecEuclideanNorm (x - y) := by ring

theorem neg (h : EucLip L η) : EucLip L (fun x => -η x) := fun x y => by
  rw [show -η x - -η y = -(η x - η y) by ring, abs_neg]; exact h x y

theorem sub {L' : ℝ} {ζ : Vec d → ℝ} (h : EucLip L η) (h' : EucLip L' ζ) :
    EucLip (L + L') (fun x => η x - ζ x) := by
  simpa [sub_eq_add_neg] using h.add h'.neg

theorem smul (c : ℝ) (h : EucLip L η) : EucLip (|c| * L) (fun x => c * η x) := fun x y => by
  rw [← mul_sub, abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h x y) (abs_nonneg c)

theorem max {L' : ℝ} {ζ : Vec d → ℝ} (h : EucLip L η) (h' : EucLip L' ζ) :
    EucLip (Max.max L L') (fun x => Max.max (η x) (ζ x)) := fun x y => by
  have hn := vecEuclideanNorm_nonneg (x - y)
  have h1 : |η x - η y| ≤ Max.max L L' * vecEuclideanNorm (x - y) :=
    (h x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hn)
  have h2 : |ζ x - ζ y| ≤ Max.max L L' * vecEuclideanNorm (x - y) :=
    (h' x y).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hn)
  simp only [abs_le] at h1 h2 ⊢
  constructor <;> rcases le_total (η x) (ζ x) with a | a <;> rcases le_total (η y) (ζ y) with b | b <;>
    simp only [max_eq_left, max_eq_right, a, b] <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem min {L' : ℝ} {ζ : Vec d → ℝ} (h : EucLip L η) (h' : EucLip L' ζ) :
    EucLip (Max.max L L') (fun x => Min.min (η x) (ζ x)) := fun x y => by
  have hn := vecEuclideanNorm_nonneg (x - y)
  have h1 : |η x - η y| ≤ Max.max L L' * vecEuclideanNorm (x - y) :=
    (h x y).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hn)
  have h2 : |ζ x - ζ y| ≤ Max.max L L' * vecEuclideanNorm (x - y) :=
    (h' x y).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hn)
  simp only [abs_le] at h1 h2 ⊢
  constructor <;> rcases le_total (η x) (ζ x) with a | a <;> rcases le_total (η y) (ζ y) with b | b <;>
    simp only [min_eq_left, min_eq_right, a, b] <;> linarith [h1.1, h1.2, h2.1, h2.2]

theorem mul {L' M N : ℝ} {ζ : Vec d → ℝ} (h : EucLip L η) (h' : EucLip L' ζ)
    (hM : ∀ x, |η x| ≤ M) (hN : ∀ x, |ζ x| ≤ N) :
    EucLip (M * L' + N * L) (fun x => η x * ζ x) := fun x y => by
  have hn := vecEuclideanNorm_nonneg (x - y)
  calc |η x * ζ x - η y * ζ y| = |η x * (ζ x - ζ y) + ζ y * (η x - η y)| := by ring_nf
    _ ≤ |η x * (ζ x - ζ y)| + |ζ y * (η x - η y)| := abs_add_le _ _
    _ = |η x| * |ζ x - ζ y| + |ζ y| * |η x - η y| := by rw [abs_mul, abs_mul]
    _ ≤ M * (L' * vecEuclideanNorm (x - y)) + N * (L * vecEuclideanNorm (x - y)) :=
        add_le_add (mul_le_mul (hM x) (h' x y) (abs_nonneg _) ((abs_nonneg _).trans (hM x)))
          (mul_le_mul (hN y) (h x y) (abs_nonneg _) ((abs_nonneg _).trans (hN y)))
    _ = (M * L' + N * L) * vecEuclideanNorm (x - y) := by ring

/-- A `C¹` compactly supported function is Euclidean-Lipschitz. -/
theorem of_contDiff_hasCompactSupport {φ : Vec d → ℝ} (hφ : ContDiff ℝ 1 φ)
    (hφc : HasCompactSupport φ) : ∃ K : ℝ, 0 ≤ K ∧ EucLip K φ := by
  obtain ⟨K, hK⟩ := hφ.lipschitzWith_of_hasCompactSupport hφc (by simp)
  refine ⟨K, K.2, of_norm K.2 fun x y => ?_⟩
  have := hK.dist_le_mul x y
  rwa [Real.dist_eq, dist_eq_norm] at this

/-- The distance to a fixed point is `1`-Lipschitz for the Euclidean distance. -/
theorem dist_center (x₀ : Vec d) : EucLip 1 (fun x => vecEuclideanNorm (x - x₀)) := fun x y => by
  have h1 := vecEuclideanNorm_add_le (x - y) (y - x₀)
  have h2 := vecEuclideanNorm_add_le (y - x) (x - x₀)
  rw [show x - y + (y - x₀) = x - x₀ by abel] at h1
  rw [show y - x + (x - x₀) = y - x₀ by abel, vecEuclideanNorm_sub_comm y x] at h2
  rw [one_mul, abs_le]
  constructor <;> linarith

end EucLip

end PDE.Ch4Infra
