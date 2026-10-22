module

public import PDEFoundation.Sobolev.Mean
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# First absolute moment against the second moment on a finite-measure set
-/

@[expose] public section

namespace PDE.DGNMLog

open MeasureTheory

/-- Cauchy-Schwarz for averages: if `∫_V g² ≤ M² |V|` then the average of `|g|` is at most `M`. -/
theorem integralAverage_abs_le_of_sq_le {d : ℕ} {V : Set (Vec d)}
    (hpos : 0 < volume V) (hfin : volume V < ⊤) {g : Vec d → ℝ}
    (hg : MemLp g 2 (volume.restrict V)) {M : ℝ} (hM : 0 ≤ M)
    (h : ∫ x in V, g x ^ 2 ≤ M ^ 2 * (volume V).toReal) :
    integralAverage V (fun x => |g x|) ≤ M := by
  have : IsFiniteMeasure (volume.restrict V) := ⟨by simpa using hfin⟩
  set Vr : ℝ := (volume V).toReal with hVr
  have hVpos : 0 < Vr := ENNReal.toReal_pos hpos.ne' hfin.ne
  have hint1 : Integrable (fun x => |g x|) (volume.restrict V) :=
    (hg.integrable (by norm_num)).abs
  have hint2 : Integrable (fun x => g x ^ 2) (volume.restrict V) := hg.integrable_sq
  set m : ℝ := ∫ x in V, |g x| with hm
  set c : ℝ := m / Vr with hc
  have hsq : 0 ≤ ∫ x in V, (|g x| - c) ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  have hexp : ∫ x in V, (|g x| - c) ^ 2 = (∫ x in V, g x ^ 2) - 2 * c * m + c ^ 2 * Vr := by
    have : ∀ x, (|g x| - c) ^ 2 = (g x ^ 2 - 2 * c * |g x|) + c ^ 2 := by
      intro x; rw [sub_sq, sq_abs]; ring
    simp_rw [this]
    rw [integral_add (f := fun x => g x ^ 2 - 2 * c * |g x|) (g := fun _ => c ^ 2)
        (hint2.sub (hint1.const_mul _)) (integrable_const _),
      integral_sub (f := fun x => g x ^ 2) (g := fun x => 2 * c * |g x|) hint2
        (hint1.const_mul _), integral_const_mul, integral_const]
    simp [hVr, Measure.real, hm]
    ring
  have hm0 : 0 ≤ m := integral_nonneg fun x => abs_nonneg _
  have key : m ^ 2 ≤ Vr * ∫ x in V, g x ^ 2 := by
    have h1 : c * m = m ^ 2 / Vr := by rw [hc]; ring
    have h2 : c ^ 2 * Vr = m ^ 2 / Vr := by rw [hc]; field_simp
    rw [hexp] at hsq
    have h3 : 0 ≤ (∫ x in V, g x ^ 2) - m ^ 2 / Vr := by nlinarith [h1, h2]
    rw [sub_nonneg, div_le_iff₀ hVpos] at h3
    linarith
  have hmM : m ≤ Vr * M := by
    have : m ^ 2 ≤ (Vr * M) ^ 2 := by nlinarith
    exact le_of_sq_le_sq this (by positivity) |> fun h => by simpa using h
  unfold integralAverage
  rw [show (∫ x in V, |g x|) = m from rfl]
  rw [← hVr, inv_mul_le_iff₀ hVpos]
  linarith

end PDE.DGNMLog
