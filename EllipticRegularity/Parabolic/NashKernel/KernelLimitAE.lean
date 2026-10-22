module

public import EllipticRegularity.Parabolic.NashKernel.KernelLimit

/-!
# Abstract dyadic kernel for a.e.-measurable data

Version of `PDE.NashKernelLimit.exists_kernel` where each `T n k` is only assumed a.e.-measurable
(replace it by a measurable modification; all hypotheses and the conclusion are a.e. statements).
-/

@[expose] public section

namespace PDE.NashKernelLimit

open MeasureTheory Set PDE.NashKernelDyadic

variable {d : ℕ}

theorem exists_kernel_of_aemeasurable {M : ℝ} (hM : 0 ≤ M)
    {T : ℕ → (Fin d → ℤ) → PDE.Vec d → ℝ} (hT : ∀ n k, AEMeasurable (T n k) volume)
    (hbd : ∀ n k, ∀ᵐ x, 0 ≤ T n k x ∧ T n k x ≤ M * (volume (cube n k)).toReal)
    (hadd : ∀ n k, ∀ᵐ x, T n k x = ∑ ε : Fin d → Bool, T (n + 1) (child k ε) x) :
    ∃ P : PDE.Vec d → PDE.Vec d → ℝ, Measurable (Function.uncurry P) ∧
      (∀ x y, 0 ≤ P x y ∧ P x y ≤ M) ∧
      ∀ n k, ∀ᵐ x, ∫ y in cube n k, P x y = T n k x := by
  set T' : ℕ → (Fin d → ℤ) → PDE.Vec d → ℝ := fun n k => (hT n k).mk (T n k)
  have hae : ∀ n k, T n k =ᵐ[volume] T' n k := fun n k => (hT n k).ae_eq_mk
  have hmeas : ∀ n k, Measurable (T' n k) := fun n k => (hT n k).measurable_mk
  have hall : ∀ᵐ x, ∀ n k, T n k x = T' n k x :=
    ae_all_iff.mpr fun n => ae_all_iff.mpr fun k => hae n k
  obtain ⟨P, hPm, hPb, hP⟩ := exists_kernel hM (T := T') hmeas
    (fun n k => by
      filter_upwards [hbd n k, hall] with x hx h
      rwa [← h n k])
    (fun n k => by
      filter_upwards [hadd n k, hall] with x hx h
      rw [← h n k, hx]
      exact Finset.sum_congr rfl fun ε _ => h _ _)
  refine ⟨P, hPm, hPb, fun n k => ?_⟩
  filter_upwards [hP n k, hall] with x hx h
  rw [hx, h n k]

end PDE.NashKernelLimit
