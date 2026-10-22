module

public import PDEFoundation.Monotonicity.ACF.WeightedLimit

/-!
# Rewriting the limit bound through the radial flux

With `Q₀(s) = s^{-κ}` and `K₀(s) = 2 Q₀(s) Z'(s)` (smooth, since `Z' = 0` near `s ≤ 0`) one has

`T₀ = d K₀ + 2 s K₀' - 2 (d-2) Q₀ Z'` on `s ≥ 0`,

so that, by the radial integration by parts,

`½ ∫ u² T₀(|x|²) = -∫ u K₀(|x|²) (x · ∇u) - ((d-2)/2) ∫ u² K₀(|x|²)`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace PDE

noncomputable section

variable {r k : ℝ}

/-- `K₀(s) = 2 s^{-κ} Z'(s)`. -/
def acfK0 (d : ℕ) (r k s : ℝ) : ℝ := 2 * acfQ (acfKappa d) 0 s * deriv (acfCut r k) s

theorem contDiff_acfK0 {d : ℕ} (hr : 0 < r) (hk : 0 < k) : ContDiff ℝ (⊤ : ℕ∞) (acfK0 d r k) := by
  rw [contDiff_iff_contDiffAt]
  intro s
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (deriv (acfCut r k)) :=
    (contDiff_infty_iff_deriv.mp (contDiff_acfCut hr hk)).2
  by_cases hs : s < r ^ 2
  · have : acfK0 d r k =ᶠ[nhds s] fun _ => 0 := by
      filter_upwards [gt_mem_nhds hs] with t ht
      unfold acfK0
      rw [deriv_acfCut_eq_zero_of_lt hr hk ht]; ring
    exact contDiffAt_const.congr_of_eventuallyEq this
  · have hs0 : 0 < s := lt_of_lt_of_le (by positivity) (not_lt.mp hs)
    have hQ : ContDiffAt ℝ (⊤ : ℕ∞) (acfQ (acfKappa d) 0) s := by
      unfold acfQ
      exact (contDiffAt_id.add contDiffAt_const).rpow_const_of_ne (by simp only [id]; positivity)
    unfold acfK0
    exact (contDiffAt_const.mul hQ).mul h1.contDiffAt

theorem acfK0_eq_zero {d : ℕ} (hk : 0 < k) {s : ℝ} (hs : (r + k) ^ 2 < s) : acfK0 d r k s = 0 := by
  unfold acfK0
  rw [deriv_acfCut_eq_zero_of_gt hk hs]; ring

/-- The algebraic identity relating `T₀` and `K₀`. -/
theorem acfT_zero_eq {d : ℕ} (hr : 0 < r) (hk : 0 < k) {s : ℝ} :
    acfT d r k 0 s = d * acfK0 d r k s + 2 * s * deriv (acfK0 d r k) s -
      2 * ((d : ℝ) - 2) * (acfQ (acfKappa d) 0 s * deriv (acfCut r k) s) := by
  by_cases hs1 : s < r ^ 2
  · have hK : acfK0 d r k =ᶠ[nhds s] fun _ => 0 := by
      filter_upwards [gt_mem_nhds hs1] with t ht
      unfold acfK0
      rw [deriv_acfCut_eq_zero_of_lt hr hk ht]; ring
    rw [acfT_eq_zero hr hk (Or.inl hs1), hK.deriv_eq, hK.self_of_nhds,
      deriv_acfCut_eq_zero_of_lt hr hk hs1]
    simp
  · have hs0 : 0 < s := lt_of_lt_of_le (by positivity) (not_lt.mp hs1)
    have hpos : 0 < s + (0 : ℝ) ^ 2 := by simpa using hs0
    have hK0 : HasDerivAt (acfK0 d r k)
        (2 * acfQ1 (acfKappa d) 0 s * deriv (acfCut r k) s +
          2 * acfQ (acfKappa d) 0 s * deriv (deriv (acfCut r k)) s) s :=
      ((hasDerivAt_acfQ (κ := acfKappa d) hpos).const_mul 2).mul
        (hasDerivAt_acfCut_deriv_deriv hr hk s)
    have hmul := acfQ1_mul_self_eq (κ := acfKappa d) (ε := 0) hpos
    simp only [zero_pow two_ne_zero, add_zero] at hmul
    rw [hK0.deriv]
    unfold acfT acfK0
    have hd := acfKappa_eq d
    linear_combination (4 * deriv (acfCut r k) s) * hmul +
      (2 * acfQ (acfKappa d) 0 s * deriv (acfCut r k) s) * hd

theorem deriv_acfK0_eq_zero {d : ℕ} (hk : 0 < k) {s : ℝ} (hs : (r + k) ^ 2 < s) :
    deriv (acfK0 d r k) s = 0 :=
  deriv_eq_zero_of_gt (fun _ ht => acfK0_eq_zero hk ht) hs

/-- **The identity.** -/
theorem acf_half_T_eq {d : ℕ} {R : ℝ} (hr : 0 < r) (hk : 0 < k) (hrk : r + k < R)
    (u : H1Function (euclideanBall (0 : Vec d) R))
    (hcont : ContinuousOn u.toFun (euclideanBall (0 : Vec d) R)) :
    (1 / 2) * ∫ x in euclideanBall (0 : Vec d) R,
        u.toFun x ^ 2 * acfT d r k 0 (vecNormSq x) =
      -(∫ x in euclideanBall (0 : Vec d) R,
          u.toFun x * (acfK0 d r k (vecNormSq x) * vecDot x (u.grad x))) -
        (((d : ℝ) - 2) / 2) * ∫ x in euclideanBall (0 : Vec d) R,
          u.toFun x ^ 2 * acfK0 d r k (vecNormSq x) := by
  set ρ₁ : ℝ := (r + k + R) / 2 with hρ₁
  have hρ₁pos : 0 < ρ₁ := by rw [hρ₁]; linarith
  have hρ₁R : ρ₁ < R := by rw [hρ₁]; linarith
  have hK : ContDiff ℝ (⊤ : ℕ∞) (acfK0 d r k) := contDiff_acfK0 hr hk
  have hK0 : ∀ s, ρ₁ ^ 2 ≤ s → acfK0 d r k s = 0 := by
    intro s hs
    refine acfK0_eq_zero hk (lt_of_lt_of_le ?_ hs)
    rw [hρ₁]; nlinarith
  have hibp := integral_radial_ibp u hcont hK hρ₁pos hρ₁R hK0
  have hc0 : Continuous (acfK0 d r k) := hK.continuous
  have hc1 : Continuous (deriv (acfK0 d r k)) := (contDiff_infty_iff_deriv.mp hK).2.continuous
  have hA := integrableOn_sq_mul_radial u
    (G := fun s => d * acfK0 d r k s + 2 * s * deriv (acfK0 d r k) s)
    ((continuous_const.mul hc0).add ((continuous_const.mul continuous_id).mul hc1)).continuousOn
    (by positivity : 0 ≤ r + k) (fun s hs => by
      simp [acfK0_eq_zero hk hs, deriv_acfK0_eq_zero hk hs])
  have hB := integrableOn_sq_mul_radial u (G := acfK0 d r k) hc0.continuousOn
    (by positivity : 0 ≤ r + k) (fun s hs => acfK0_eq_zero hk hs)
  have hpt : ∫ x in euclideanBall (0 : Vec d) R, u.toFun x ^ 2 * acfT d r k 0 (vecNormSq x) =
      (∫ x in euclideanBall (0 : Vec d) R, u.toFun x ^ 2 *
          (d * acfK0 d r k (vecNormSq x) + 2 * vecNormSq x * deriv (acfK0 d r k) (vecNormSq x))) -
        ((d : ℝ) - 2) * ∫ x in euclideanBall (0 : Vec d) R,
          u.toFun x ^ 2 * acfK0 d r k (vecNormSq x) := by
    rw [← integral_const_mul, ← integral_sub hA (hB.const_mul _)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [acfT_zero_eq hr hk (s := vecNormSq x), acfK0]
    ring
  rw [hpt, hibp]
  ring

end

end PDE
