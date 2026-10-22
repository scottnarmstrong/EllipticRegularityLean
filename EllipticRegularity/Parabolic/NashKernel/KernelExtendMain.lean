module

public import EllipticRegularity.Parabolic.NashKernel.KernelLimitAE
public import EllipticRegularity.Parabolic.NashKernel.KernelExtend

/-!
# Abstract kernel construction and representation (measurable kernel and extension step)

`PDE.NashKernelExtend.exists_kernel_representation` combines `exists_kernel_of_aemeasurable` and
`kernel_represents`: from dyadic data `T` (a.e. measurable, `0 ≤ T Q ≤ M vol Q` a.e., additive on
children a.e.) and an operator `Tf` on `L¹(Vec d)` (a.e. additive and homogeneous, bounded
`L¹ → L^∞` by `M`, agreeing with `T Q` on `1_Q`) there is a jointly measurable kernel
`0 ≤ P ≤ M` with `∫_Q P(x, ·) = T Q x` a.e. for every dyadic cube and
`Tf f = ∫ P(·, y) f(y) dy` a.e. for every integrable `f`.
-/

@[expose] public section

namespace PDE.NashKernelExtend

open MeasureTheory PDE.NashKernelDyadic PDE.NashKernelLimit

variable {d : ℕ}

theorem exists_kernel_representation {M : ℝ} (hM : 0 ≤ M)
    {T : ℕ → (Fin d → ℤ) → PDE.Vec d → ℝ} (hT : ∀ n k, AEMeasurable (T n k) volume)
    (hbd : ∀ n k, ∀ᵐ x, 0 ≤ T n k x ∧ T n k x ≤ M * (volume (cube n k)).toReal)
    (hadd : ∀ n k, ∀ᵐ x, T n k x = ∑ ε : Fin d → Bool, T (n + 1) (child k ε) x)
    {Tf : (PDE.Vec d → ℝ) → PDE.Vec d → ℝ} (hL : LinearBounded M Tf)
    (hcube : ∀ n k, Tf ((cube n k).indicator fun _ => (1 : ℝ)) =ᵐ[volume] T n k) :
    ∃ P : PDE.Vec d → PDE.Vec d → ℝ, Measurable (Function.uncurry P) ∧
      (∀ x y, 0 ≤ P x y ∧ P x y ≤ M) ∧
      (∀ n k, ∀ᵐ x, ∫ y in cube n k, P x y = T n k x) ∧
      ∀ f : PDE.Vec d → ℝ, Integrable f → Tf f =ᵐ[volume] fun x => ∫ y, P x y * f y := by
  obtain ⟨P, hPm, hPb, hP⟩ := exists_kernel_of_aemeasurable hM hT hbd hadd
  exact ⟨P, hPm, hPb, hP, fun f hf => kernel_represents hPm hPb hL hP hcube hf⟩

end PDE.NashKernelExtend
