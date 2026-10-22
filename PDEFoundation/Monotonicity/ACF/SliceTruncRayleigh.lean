module

public import PDEFoundation.Monotonicity.ACF.SliceTrunc

/-!
# ACF-S2: Rayleigh bound for a.e. slice of a truncation `(u - δ)₊`

For `u ∈ H¹(B_R)` continuous and `δ > 0`, for a.e. `r ∈ (0, R)` the Rayleigh inequality holds for
`((u - δ)₊, 1_{u > δ} ∇u)` with `Ω(r) = {y | 0 < u (r y)}`.
-/

@[expose] public section

open MeasureTheory Set Filter

namespace PDE

noncomputable section

variable {d : ℕ}

theorem ae_rayleigh_truncation [NeZero d] {R : ℝ} (hR : 0 < R)
    (u : H1Function (euclideanBall (0 : Vec d) R)) (hu : Continuous u.toFun) {δ : ℝ}
    (hδ : 0 < δ) :
    ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R)),
      SliceIntegrable (fun x => vecNormSq (({y | δ < u.toFun y}.indicator u.grad) x)) r ∧
      SliceIntegrable (fun x => max (u.toFun x - δ) 0 ^ 2) r ∧
      SliceIntegrable (fun x => vecDot (({y | δ < u.toFun y}.indicator u.grad) x)
        (unitDir x) ^ 2) r ∧
      sliceIntegral (fun x => vecDot (({y | δ < u.toFun y}.indicator u.grad) x)
          (unitDir x) ^ 2) r +
        (sphereDirichletEigenvalue d {y | 0 < u.toFun (r • y)}).toReal * r⁻¹ ^ 2 *
          sliceIntegral (fun x => max (u.toFun x - δ) 0 ^ 2) r ≤
      sliceIntegral (fun x => vecNormSq (({y | δ < u.toFun y}.indicator u.grad) x)) r := by
  obtain ⟨r0, w, hr0, hr0R, hball, hw, hdata⟩ := exists_truncation_approxData hR u δ
  refine hdata.rayleigh_ae (Ω := fun r => {y | 0 < u.toFun (r • y)}) ?_
  filter_upwards [eventually_half_lt_of_representative_ne_zero hR hu hδ hr0 hr0R hball]
    with n hn r hr
  have hsub : {y : Vec d | y ∈ euclideanSphere (0 : Vec d) 1 ∧ w n (r • y) ≠ 0} ⊆
      {y : Vec d | δ / 2 ≤ u.toFun (r • y)} := by
    rintro y ⟨hy, hwy⟩
    have hyb : r • y ∈ euclideanBall (0 : Vec d) R := by
      rw [mem_euclideanSphere_zero_iff] at hy
      rw [mem_euclideanBall_zero_iff, vecNormSq_smul, hy]
      nlinarith [hr.1, hr.2]
    rw [hw n] at hwy
    exact (hn _ hyb hwy).le
  have hcl : IsClosed {y : Vec d | δ / 2 ≤ u.toFun (r • y)} :=
    isClosed_le continuous_const (hu.comp (continuous_const_smul r))
  refine (closure_minimal hsub hcl).trans ?_
  intro y hy
  exact lt_of_lt_of_le (by positivity : (0 : ℝ) < δ / 2) hy

end

end PDE
