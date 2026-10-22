module

public import PDEFoundation.Geometry.EuclideanBall
public import PDEFoundation.Measure.AxisBoxVolume
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# The zero set of a boundary cube

If the doubled cube `2Q` is not contained in the unit ball, then the part of
`4Q` outside the unit ball has volume at least `4⁻ᵈ |4Q|`. The proof is the
corner-subcube argument of the Meyers reverse Hölder lemma: pick `y ∈ 2Q`
outside the ball and let `s_i` be the sign of `y_i`. The subcube of side `ℓ(Q)`
in the corner of `4Q` with sign pattern `s` lies in `{x | y ⬝ x ≥ |y|²}`, which
lies outside the ball.
-/

@[expose] public section

open MeasureTheory

namespace PDE

namespace MeyersRH

variable {d : ℕ}

/-- The corner subcube of `4Q` (half-open) with the sign pattern of `y`. -/
def cornerSubcube (z y : Vec d) (r : ℝ) : Set (Vec d) :=
  Set.pi Set.univ fun i =>
    if 0 ≤ y i then Set.Ico (z i + 2 * r) (z i + 4 * r)
    else Set.Ioc (z i - 4 * r) (z i - 2 * r)

theorem volume_cornerSubcube (z y : Vec d) {r : ℝ} (hr : 0 < r) :
    (volume (cornerSubcube z y r)).toReal = (2 * r) ^ d := by
  rw [cornerSubcube, volume_pi_pi]
  have h : ∀ i : Fin d, volume (if 0 ≤ y i then Set.Ico (z i + 2 * r) (z i + 4 * r)
      else Set.Ioc (z i - 4 * r) (z i - 2 * r)) = ENNReal.ofReal (2 * r) := by
    intro i
    split_ifs
    · rw [Real.volume_Ico]; congr 1; ring
    · rw [Real.volume_Ioc]; congr 1; ring
  simp_rw [h]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow
    (by positivity), ENNReal.toReal_ofReal (by positivity)]

theorem cornerSubcube_subset_cube (z y : Vec d) {r : ℝ} :
    cornerSubcube z y r ⊆ centeredAxisCube z (4 * r) := by
  intro x hx i _
  have hxi := hx i (Set.mem_univ i)
  simp only at hxi
  split_ifs at hxi with h
  · obtain ⟨h1, h2⟩ := hxi
    constructor <;> dsimp <;> linarith
  · obtain ⟨h1, h2⟩ := hxi
    constructor <;> dsimp <;> linarith

theorem cornerSubcube_outside_ball (z y : Vec d) {r : ℝ}
    (hy : y ∈ centeredAxisCube z (2 * r)) (hy1 : y ∉ euclideanBall (0 : Vec d) 1) :
    cornerSubcube z y r ⊆ (euclideanBall (0 : Vec d) 1)ᶜ := by
  intro x hx
  have hN : 1 ≤ vecNormSq y := by
    by_contra hlt
    apply hy1
    simp only [euclideanBall, Set.mem_ofPred_eq, euclideanSqDist, sub_zero]
    linarith
  -- coordinatewise comparison `y i * x i ≥ y i * y i`
  have key : ∀ i, y i * y i ≤ y i * x i := by
    intro i
    have hxi := hx i (Set.mem_univ i)
    have hyi := hy i (Set.mem_univ i)
    simp only at hxi
    obtain ⟨hy1', hy2'⟩ := hyi
    dsimp at hy1' hy2'
    split_ifs at hxi with h
    · obtain ⟨h1, h2⟩ := hxi
      -- y i ≥ 0, x i ≥ z i + 2r ≥ y i
      have : y i ≤ x i := by linarith
      exact mul_le_mul_of_nonneg_left this h
    · obtain ⟨h1, h2⟩ := hxi
      have hneg : y i < 0 := not_le.mp h
      have : x i ≤ y i := by linarith
      nlinarith
  have hdot : vecNormSq y ≤ vecDot y x := by
    unfold vecNormSq vecDot
    exact Finset.sum_le_sum fun i _ => key i
  have hcs := sq_vecDot_le_vecNormSq_mul_vecNormSq y x
  have hpos : 0 < vecNormSq y := by linarith
  have hx2 : 1 ≤ vecNormSq x := by
    by_contra hlt
    replace hlt := not_le.mp hlt
    have h1 : vecNormSq y ^ 2 ≤ vecDot y x ^ 2 :=
      pow_le_pow_left₀ hpos.le hdot 2
    nlinarith [vecNormSq_nonneg x]
  intro hb
  simp only [euclideanBall, Set.mem_ofPred_eq, euclideanSqDist, sub_zero] at hb
  linarith

/-- Zero-set geometry: if `2Q ⊄ B₁` then the part of `4Q` outside `B₁` has at least a
`4⁻ᵈ` fraction of the volume of `4Q`. -/
theorem volume_cube_diff_ball_ge {z : Vec d} {r : ℝ} (hr : 0 < r)
    (h : ¬ centeredAxisCube z (2 * r) ⊆ euclideanBall (0 : Vec d) 1) :
    ((4 : ℝ)⁻¹) ^ d * (volume (centeredAxisCube z (4 * r))).toReal ≤
      (volume (centeredAxisCube z (4 * r) \ euclideanBall (0 : Vec d) 1)).toReal := by
  obtain ⟨y, hy, hy1⟩ := Set.not_subset.mp h
  have hsub : cornerSubcube z y r ⊆
      centeredAxisCube z (4 * r) \ euclideanBall (0 : Vec d) 1 :=
    fun x hx => ⟨cornerSubcube_subset_cube z y hx,
      cornerSubcube_outside_ball z y hy hy1 hx⟩
  have hfin : volume (centeredAxisCube z (4 * r) \ euclideanBall (0 : Vec d) 1) ≠ ⊤ :=
    ne_top_of_le_ne_top (volume_centeredAxisCube_ne_top z (4 * r))
      (measure_mono Set.sdiff_subset)
  have := ENNReal.toReal_mono hfin (measure_mono hsub)
  rw [volume_cornerSubcube z y hr] at this
  rw [volume_centeredAxisCube_toReal z (by positivity)]
  calc ((4 : ℝ)⁻¹) ^ d * (2 * (4 * r)) ^ d = (2 * r) ^ d := by
        rw [← mul_pow]; congr 1; ring
    _ ≤ _ := this

end MeyersRH

end PDE
