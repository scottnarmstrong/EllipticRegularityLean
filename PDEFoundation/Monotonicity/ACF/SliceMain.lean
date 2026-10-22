module

public import PDEFoundation.Monotonicity.ACF.SliceFinal
public import PDEFoundation.Monotonicity.ACF.Interface

/-!
# ACF-S: the slice Rayleigh bound (facade)

Public statements for the slice Rayleigh bound, in the radial-slice normalization
`sphereIntegral 0 1 (fun y => G (r • y))` of the surface integral on the unit sphere.

* `PDE.sphereIntegral_gradient_slice_ge` (S1): smooth slices, all `r ≠ 0`.
* `PDE.acf_slice_rayleigh` (S2): continuous nonnegative `H¹(B_R)` function, a.e. `r ∈ (0, R)`.
* `PDE.acf_slice_rayleigh_interface`: the same in the `ACF/Interface.lean` normalization
  (`a, b, c` through `sphereIntegral 0 r`, `radialDeriv`, `SphereIntegrable`).
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

noncomputable section

variable {d : ℕ}

theorem sliceIntegral_radial_eq (g : Vec d → Vec d) {r : ℝ} (hr : 0 < r) :
    sliceIntegral (fun x => vecDot (g x) (unitDir x) ^ 2) r =
      sphereIntegral (0 : Vec d) 1 (fun y => vecDot (g (r • y)) y ^ 2) := by
  unfold sliceIntegral
  refine sphereIntegral_zero_congr fun y hy => ?_
  rw [mem_euclideanSphere_zero_iff] at hy
  simp only [unitDir_smul hr (by simpa using hy)]

/-- **ACF-S2.** Let `u ∈ H¹(B_R)` be continuous and nonnegative.  For almost every `r ∈ (0, R)`
the slices of `|∇u|²` and `(∂ᵣu)²` are integrable on the unit sphere and, with
`Ω(r) = {y | 0 < u (r y)}`,
`∫_{S} (∇u(ry)·y)² + λ(Ω(r)) r⁻² ∫_{S} u(ry)² ≤ ∫_{S} |∇u(ry)|²`
(`λ = sphereDirichletEigenvalue d Ω(r)`, finite whenever the slice of `u` is not identically
zero; if `u(r·) ≡ 0` then `Ω(r) = ∅`, the eigenvalue is `⊤` and `toReal = 0`). -/
theorem acf_slice_rayleigh [NeZero d] {R : ℝ} (hR : 0 < R)
    (u : H1Function (euclideanBall (0 : Vec d) R)) (hu : Continuous u.toFun)
    (hnn : ∀ x, 0 ≤ u.toFun x) :
    ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R)),
      SliceIntegrable (fun x => vecNormSq (u.grad x)) r ∧
      SliceIntegrable (fun x => vecDot (u.grad x) (unitDir x) ^ 2) r ∧
      sphereIntegral (0 : Vec d) 1 (fun y => vecDot (u.grad (r • y)) y ^ 2) +
          (sphereDirichletEigenvalue d {y | 0 < u.toFun (r • y)}).toReal * r⁻¹ ^ 2 *
            sphereIntegral (0 : Vec d) 1 (fun y => u.toFun (r • y) ^ 2) ≤
        sphereIntegral (0 : Vec d) 1 (fun y => vecNormSq (u.grad (r • y))) := by
  filter_upwards [acf_slice_rayleigh_ae hR u hu hnn, ae_restrict_mem (measurableSet_Ioo (a := (0 : ℝ)) (b := R))]
    with r ⟨h1, h2, h3⟩ hr
  refine ⟨h1, h2, ?_⟩
  rw [sliceIntegral_radial_eq _ hr.1] at h3
  exact h3

theorem radialDeriv_sq_eq (G : Vec d → Vec d) (x : Vec d) :
    radialDeriv G x ^ 2 = vecDot (G x) (unitDir x) ^ 2 := by
  have h : radialDeriv G x = vecDot (G x) (unitDir x) := by
    unfold radialDeriv unitDir vecDot
    rw [div_eq_inv_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [h]

theorem sphereIntegral_zero_eq_mul_sliceIntegral (f : Vec d → ℝ) (r : ℝ) :
    sphereIntegral (0 : Vec d) r f = r ^ (d - 1) * sliceIntegral f r := by
  rw [sphereIntegral_zero_apply, sliceIntegral_eq]

theorem sphereIntegrable_iff_sliceIntegrable (f : Vec d → ℝ) (r : ℝ) :
    SphereIntegrable r f ↔ SliceIntegrable f r := by
  unfold SphereIntegrable SliceIntegrable
  simp only [zero_add]

/-- **ACF-S2 in the `ACF.Interface` normalization.**  With
`a(r) = ∫_{∂B_r} u²`, `b(r) = ∫_{∂B_r} (∂ᵣu)²`, `c(r) = ∫_{∂B_r} |∇u|²` (all
`sphereIntegral 0 r`), for a.e. `r ∈ (0, R)`: the slice of `|∇u|²` is integrable and
`b(r) + λ(Ω(r)) r⁻² a(r) ≤ c(r)`. -/
theorem acf_slice_rayleigh_interface [NeZero d] {R : ℝ} (hR : 0 < R)
    (u : H1Function (euclideanBall (0 : Vec d) R)) (hu : Continuous u.toFun)
    (hnn : ∀ x, 0 ≤ u.toFun x) :
    ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R)),
      SphereIntegrable r (fun x => vecNormSq (u.grad x)) ∧
      sphereIntegral (0 : Vec d) r (fun x => radialDeriv u.grad x ^ 2) +
          (sphereDirichletEigenvalue d {y | 0 < u.toFun (r • y)}).toReal * (r ^ 2)⁻¹ *
            sphereIntegral (0 : Vec d) r (fun x => u.toFun x ^ 2) ≤
        sphereIntegral (0 : Vec d) r (fun x => vecNormSq (u.grad x)) := by
  filter_upwards [acf_slice_rayleigh_ae hR u hu hnn,
    ae_restrict_mem (measurableSet_Ioo (a := (0 : ℝ)) (b := R))] with r ⟨h1, h2, h3⟩ hr
  refine ⟨(sphereIntegrable_iff_sliceIntegrable _ r).2 h1, ?_⟩
  simp only [sphereIntegral_zero_eq_mul_sliceIntegral, radialDeriv_sq_eq]
  have hpos : 0 < r ^ (d - 1) := pow_pos hr.1 _
  have := mul_le_mul_of_nonneg_left h3 hpos.le
  rw [inv_pow] at this
  nlinarith only [this]

end

end PDE
