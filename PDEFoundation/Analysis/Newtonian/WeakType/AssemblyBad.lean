module

public import PDEFoundation.Analysis.Newtonian.WeakType.AssemblyOffSupport
public import PDEFoundation.Analysis.Newtonian.WeakType.HormanderIntegral

/-!
# Hörmander bound for the gradient of the potential of a smooth mean-zero piece

If `b` is smooth, compactly supported in the closed ball `|y - c| ≤ 2 r` and has mean zero, then
`∫_{|x - c| ≥ 4 r} |∇ u_b| ≤ hormanderConst d · A · ‖b‖₁`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.NewtonWeakType

noncomputable section

variable {d : ℕ}

theorem lintegral_gradient_newtonPotential_exterior_le (hd : 0 < d) {A : ℝ} (hA : 0 ≤ A)
    (hK : KernelHolder d newtonKernelJacobian A) {b : Vec d → Vec d}
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hbc : HasCompactSupport b) {c : Vec d} {r : ℝ} (hr : 0 < r)
    (hsupp : ∀ y, 2 * r < vecEuclideanNorm (y - c) → b y = 0)
    (hmean : ∀ i, ∫ y, b y i = 0) :
    ∫⁻ x in (euclideanBall c (2 * (2 * r)))ᶜ,
        ENNReal.ofReal (vecEuclideanNorm (classicalGradient (newtonPotential b) x)) ≤
      ENNReal.ofReal (hormanderConst d * A * ∫ y, vecEuclideanNorm (b y)) := by
  have : NeZero d := ⟨hd.ne'⟩
  have hbi : ∀ i, Integrable (fun y => b y i) volume := fun i =>
    ((contDiff_pi.mp hb i).continuous).integrable_of_hasCompactSupport (hasCompactSupport_apply hbc i)
  have hr2 : 0 < 2 * r := by linarith
  refine le_trans (le_of_eq ?_) (lintegral_exterior_hormander_le hA hK hr2 hbi hsupp)
  refine setLIntegral_congr_fun (measurableSet_euclideanBall c _).compl fun x hx => ?_
  have hx' : 2 * (2 * r) ≤ vecEuclideanNorm (x - c) := by
    by_contra hlt
    exact hx ((mem_euclideanBall_iff_vecEuclideanNorm_lt (by linarith)).mpr (not_le.mp hlt))
  have hfar : ∀ y, b y ≠ 0 → 2 * r ≤ vecEuclideanNorm (x - y) := by
    intro y hy
    have h1 : vecEuclideanNorm (y - c) ≤ 2 * r := by
      by_contra hlt
      exact hy (hsupp y (not_le.mp hlt))
    have h2 : vecEuclideanNorm (x - c) ≤ vecEuclideanNorm (x - y) + vecEuclideanNorm (y - c) := by
      have := vecEuclideanNorm_add_le (x - y) (y - c)
      simpa using this
    linarith
  have hg := fun k => classicalGradient_newtonPotential_eq_of_far hd hb hbc hr2 hfar k
  congr 2
  funext i
  rw [(hg i).2, integral_kernel_sub_eq_of_integral_eq_zero hbi hmean (fun k => (hg k).1) i]

end

end PDE.NewtonWeakType
