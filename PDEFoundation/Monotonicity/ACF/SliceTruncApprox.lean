module

public import PDEFoundation.Monotonicity.ACF.SliceApprox
public import PDEFoundation.Sobolev.W1p.ConvexApprox.Density
public import PDEFoundation.Sobolev.H1.Truncation
public import PDEFoundation.Sobolev.H1.LevelSets
public import PDEFoundation.Sobolev.H1.Smooth

/-!
# ACF-S2: support of the convex-approximation smoothings of a truncation

For continuous `u` and `δ > 0`, the smoothings `wₙ` of `(u - δ)₊` obtained by convex
approximation are supported, for large `n` and uniformly in the point, where `u > δ / 2`.
-/

@[expose] public section

open MeasureTheory Set Filter

namespace PDE

noncomputable section

variable {d : ℕ}

theorem exists_closedBall_subset_euclideanBall {R : ℝ} (hR : 0 < R) :
    ∃ r0 : ℝ, 0 < r0 ∧ r0 ≤ R ∧
      Metric.closedBall (0 : Vec d) r0 ⊆ euclideanBall (0 : Vec d) R := by
  refine ⟨R / (d + 1), by positivity, ?_, fun x hx => ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    nlinarith [(Nat.cast_nonneg d : (0 : ℝ) ≤ d)]
  · rw [mem_euclideanBall_zero_iff]
    have hxi : ∀ i, x i ^ 2 ≤ (R / (d + 1)) ^ 2 := fun i => by
      have : |x i| ≤ R / (d + 1) := by
        have := (pi_norm_le_iff_of_nonneg (by positivity : (0 : ℝ) ≤ R / (d + 1))).1
          (by simpa using hx) i
        simpa using this
      exact sq_le_sq' (by linarith [abs_le.1 this]) (abs_le.1 this).2
    rw [vecNormSq_eq_sum_sq]
    calc ∑ i, x i ^ 2 ≤ ∑ _i : Fin d, (R / (d + 1)) ^ 2 := Finset.sum_le_sum fun i _ => hxi i
      _ = d * (R / (d + 1)) ^ 2 := by simp
      _ < R ^ 2 := by
        rw [div_pow, ← mul_div_assoc, div_lt_iff₀ (by positivity)]
        have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        have h : (0 : ℝ) < ((d : ℝ) + 1) ^ 2 - d := by nlinarith
        nlinarith [mul_pos (pow_pos hR 2) h]

theorem exists_sample_of_representative_ne_zero {U : Set (Vec d)}
    (hU : IsOpenBoundedConvexDomain U) {v : Vec d → ℝ} {x0 : Vec d} {r0 ε : ℝ}
    (hball : Metric.closedBall x0 r0 ⊆ U) (hr0 : 0 < r0) (hε0 : 0 < ε) (hε1 : ε < 1)
    {x : Vec d} (hx : x ∈ U)
    (h : convexApproxSmoothRepresentative U (unitConvexApproxKernel (d := d)) v x0 r0 ε x ≠ 0) :
    ∃ z : Vec d, (∀ i, |z i| ≤ 1) ∧ v (convexApproxSample x0 z r0 ε x) ≠ 0 := by
  rw [convexApproxSmoothRepresentative_eq_convexApproxSmoothing_of_mem hU
    isConvexApproxKernel_unitConvexApproxKernel hx hball hr0 hε0 hε1] at h
  by_contra hcon
  push Not at hcon
  apply h
  rw [convexApproxSmoothing_apply]
  refine setIntegral_eq_zero_of_forall_eq_zero fun z hz => ?_
  have hz1 : z ∈ Metric.closedBall (0 : Vec d) 1 :=
    isConvexApproxKernel_unitConvexApproxKernel.support_subset_closedBall hz
  have hzi : ∀ i, |z i| ≤ 1 := fun i => by
    have := (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).1 (by simpa using hz1) i
    simpa using this
  simp only [convexApproxIntegrand_apply, hcon z hzi, mul_zero]

theorem eventually_half_lt_of_representative_ne_zero {R : ℝ} (hR : 0 < R) {u : Vec d → ℝ}
    (hu : Continuous u) {δ : ℝ} (hδ : 0 < δ) {r0 : ℝ} (hr0 : 0 < r0) (hr0R : r0 ≤ R)
    (hball : Metric.closedBall (0 : Vec d) r0 ⊆ euclideanBall (0 : Vec d) R) :
    ∀ᶠ n : ℕ in atTop, ∀ x ∈ euclideanBall (0 : Vec d) R,
      convexApproxSmoothRepresentative (euclideanBall (0 : Vec d) R)
        (unitConvexApproxKernel (d := d)) (fun y => max (u y - δ) 0) 0 r0
        (unitConvexApproxScale n) x ≠ 0 → δ / 2 < u x := by
  have hU := isOpenBoundedConvexDomain_euclideanBall (0 : Vec d) hR
  have hK : IsCompact (Metric.closedBall (0 : Vec d) (3 * R)) := isCompact_closedBall _ _
  obtain ⟨η, hη, hηu⟩ := Metric.uniformContinuousOn_iff.1
    (hK.uniformContinuousOn_of_continuous hu.continuousOn) (δ / 2) (by positivity)
  have hev : ∀ᶠ n : ℕ in atTop, unitConvexApproxScale n < min 1 (η / (2 * R)) :=
    (tendsto_order.1 tendsto_unitConvexApproxScale_zero).2 _ (lt_min one_pos (by positivity))
  filter_upwards [hev] with n hn x hx hne
  have hε0 := unitConvexApproxScale_pos n
  have hε1 : unitConvexApproxScale n < 1 := lt_of_lt_of_le hn (min_le_left _ _)
  have hε2 : unitConvexApproxScale n < η / (2 * R) := lt_of_lt_of_le hn (min_le_right _ _)
  obtain ⟨z, hz, hs⟩ := exists_sample_of_representative_ne_zero hU hball hr0 hε0 hε1 hx hne
  set ε := unitConvexApproxScale n
  set s := convexApproxSample (0 : Vec d) z r0 ε x with hsdef
  have hxi : ∀ i, |x i| ≤ R := fun i => by
    have h1 : x i ^ 2 ≤ vecNormSq x := sq_apply_le_vecNormSq x i
    rw [mem_euclideanBall_zero_iff] at hx
    exact abs_le_of_sq_le_sq' (by nlinarith) hR.le |>.2 |> fun h => abs_le.2 ⟨by
      have := abs_le_of_sq_le_sq' (by nlinarith : x i ^ 2 ≤ R ^ 2) hR.le; linarith [this.1], h⟩
  have hdiff : ∀ i, |s i - x i| ≤ ε * (2 * R) := fun i => by
    have : s i - x i = ε * (-(x i) - r0 * z i) := by
      simp only [hsdef, convexApproxSample_apply, Pi.add_apply, Pi.smul_apply, Pi.sub_apply,
        smul_eq_mul, Pi.zero_apply]
      ring
    rw [this, abs_mul, abs_of_pos hε0]
    gcongr
    calc |-(x i) - r0 * z i| ≤ |x i| + r0 * |z i| := by
          calc _ ≤ |-(x i)| + |r0 * z i| := abs_sub _ _
            _ = _ := by rw [abs_neg, abs_mul, abs_of_pos hr0]
      _ ≤ R + R * 1 := by
          gcongr
          · exact hxi i
          · exact hz i
      _ = 2 * R := by ring
  have hxK : x ∈ Metric.closedBall (0 : Vec d) (3 * R) := by
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    simpa using (hxi i).trans (by linarith)
  have hsK : s ∈ Metric.closedBall (0 : Vec d) (3 * R) := by
    rw [mem_closedBall_zero_iff]
    refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
    have h1 : ε * (2 * R) ≤ 2 * R := by nlinarith
    have : |s i| ≤ |x i| + |s i - x i| := by
      calc |s i| = |x i + (s i - x i)| := by ring_nf
        _ ≤ _ := abs_add_le _ _
    simpa using this.trans (by linarith [hxi i, hdiff i])
  have hdist : dist s x < η := by
    rw [dist_pi_lt_iff hη]
    intro i
    rw [Real.dist_eq]
    refine lt_of_le_of_lt (hdiff i) ?_
    calc ε * (2 * R) < η / (2 * R) * (2 * R) := by gcongr
      _ = η := by field_simp
  have hclose := hηu s hsK x hxK hdist
  rw [Real.dist_eq] at hclose
  have hgt : δ < u s := by
    by_contra hle
    push Not at hle
    apply hs
    simp only [max_eq_right (by linarith : u s - δ ≤ 0)]
  linarith [(abs_lt.1 hclose).2]

end

end PDE
