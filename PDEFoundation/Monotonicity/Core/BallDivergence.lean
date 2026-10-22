module

public import PDEFoundation.Monotonicity.Core.BallDivergenceLimit
public import PDEFoundation.Sobolev.Cutoff.Ball

/-!
# The divergence theorem on Euclidean balls

For `F : Vec d → Vec d` of class `C¹` on `euclideanBall 0 R`, `d ≥ 1` and `0 < r < R`,

`∫_{B_r} div F = r⁻¹ ∫_{∂B_r} F · x`

with the surface integral `PDE.sphereIntegral` and `PDE.classicalDivergence`.  (Since
`x = r ν` on `∂B_r` this is `∫_{∂B_r} F · ν`.)  The proof localizes with `canonicalBallCutoff` to a
globally `C¹` field and uses `BallDivergenceLimit`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace PDE

noncomputable section

variable {d : ℕ}

theorem mem_euclideanBall_zero_iff {x : Vec d} {r : ℝ} :
    x ∈ euclideanBall (0 : Vec d) r ↔ vecNormSq x < r ^ 2 := by
  unfold euclideanBall
  simp only [mem_ofPred_eq, BallDivergence.euclideanSqDist_zero_right]

theorem classicalDivergence_congr_of_eventuallyEq {F G : Vec d → Vec d} {x : Vec d}
    (h : F =ᶠ[𝓝 x] G) : classicalDivergence F x = classicalDivergence G x := by
  unfold classicalDivergence
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold euclideanCoordDeriv
  rw [Filter.EventuallyEq.fderiv_eq (𝕜 := ℝ) (f := fun y => G y k)
    (h.mono fun y hy => by simp [hy])]

/-- **Divergence theorem on balls** for a field of class `C¹` on the open ball `B_R`:
`∫_{B_r} div F = r⁻¹ ∫_{∂B_r} F · x` for `0 < r < R`, in every dimension `d ≥ 1`. -/
theorem integral_euclideanBall_classicalDivergence [NeZero d] {F : Vec d → Vec d} {R r : ℝ}
    (hF : ContDiffOn ℝ 1 F (euclideanBall (0 : Vec d) R)) (hr : 0 < r) (hrR : r < R) :
    ∫ x in euclideanBall (0 : Vec d) r, classicalDivergence F x =
      r⁻¹ * sphereIntegral (0 : Vec d) r (fun x => vecDot (F x) x) := by
  set r' : ℝ := (r + R) / 2 with hr'
  have hrr' : r < r' := by rw [hr']; linarith only [hrR]
  have hr'R : r' < R := by rw [hr']; linarith only [hrR]
  have hr'0 : 0 ≤ r' := by rw [hr']; linarith only [hr, hrR]
  set χ : Vec d → ℝ := canonicalBallCutoff (0 : Vec d) r' R with hχ
  have hχs : ContDiff ℝ (⊤ : ℕ∞) χ := canonicalBallCutoff_smooth 0 hr'0 hr'R
  have hχ1 : ∀ x ∈ euclideanBall (0 : Vec d) r', χ x = 1 := fun x hx =>
    canonicalBallCutoff_eq_one_on_inner hr'0 hr'R hx
  have hχsupp := canonicalBallCutoff_tsupport_subset_outer (x₀ := (0 : Vec d)) hr'0 hr'R
  set G : Vec d → Vec d := fun x => χ x • F x with hG
  have hGc : ContDiff ℝ 1 G := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : x ∈ euclideanBall (0 : Vec d) R
    · exact ((hχs.of_le (by exact_mod_cast le_top)).contDiffAt).smul
        (hF.contDiffAt ((isOpen_euclideanBall 0 R).mem_nhds hx))
    · have hxt : x ∉ tsupport χ := fun h => hx (hχsupp h)
      have hev : G =ᶠ[𝓝 x] fun _ => (0 : Vec d) := by
        filter_upwards [(notMem_tsupport_iff_eventuallyEq.1 hxt)] with y hy
        simp [hG, hy]
      exact contDiffAt_const.congr_of_eventuallyEq hev
  have hGF : ∀ x ∈ euclideanBall (0 : Vec d) r', G x = F x := by
    intro x hx; simp [hG, hχ1 x hx]
  have hev : ∀ x ∈ euclideanBall (0 : Vec d) r', G =ᶠ[𝓝 x] F := by
    intro x hx
    filter_upwards [(isOpen_euclideanBall 0 r').mem_nhds hx] with y hy using hGF y hy
  have hsub : euclideanBall (0 : Vec d) r ⊆ euclideanBall (0 : Vec d) r' := by
    intro x hx
    rw [mem_euclideanBall_zero_iff] at hx ⊢
    nlinarith only [hx, hr, hrr']
  have key := BallDivergence.integral_euclideanBall_classicalDivergence_of_contDiff hGc hr
  have hsph : sphereIntegral (0 : Vec d) r (fun x => vecDot (G x) x) =
      sphereIntegral (0 : Vec d) r (fun x => vecDot (F x) x) := by
    unfold sphereIntegral
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun ω => ?_)
    have hn : ‖(ω : HilbertVec d)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.2
    have hmem : (0 : Vec d) + r • (ω : HilbertVec d).toVec ∈ euclideanBall (0 : Vec d) r' := by
      rw [mem_euclideanBall_zero_iff, zero_add, vecNormSq_smul,
        BallDivergence.vecNormSq_toVec, hn]
      nlinarith only [hr, hrr']
    simp only [hGF _ hmem]
  rw [← hsph, ← key]
  exact setIntegral_congr_fun (measurableSet_euclideanBall 0 r) fun x hx =>
    (classicalDivergence_congr_of_eventuallyEq (hev x (hsub hx))).symm

/-- The divergence theorem on balls, for `d ≥ 1` given as a hypothesis. -/
theorem integral_euclideanBall_classicalDivergence_of_one_le (hd : 1 ≤ d) {F : Vec d → Vec d}
    {R r : ℝ} (hF : ContDiffOn ℝ 1 F (euclideanBall (0 : Vec d) R)) (hr : 0 < r)
    (hrR : r < R) :
    ∫ x in euclideanBall (0 : Vec d) r, classicalDivergence F x =
      r⁻¹ * sphereIntegral (0 : Vec d) r (fun x => vecDot (F x) x) :=
  haveI : NeZero d := ⟨by omega⟩
  integral_euclideanBall_classicalDivergence hF hr hrR

end

end PDE
