module

public import PDEFoundation.Analysis.Inequalities.JohnNirenberg.Cube

/-!
# The John–Nirenberg inequality on closed cubes

The manuscript states Lemma 1.16 for closed cubes and their closed dyadic subcubes. A
closed box `Box.Icc I` differs from the half-open carrier of `I` by a null set, so averages,
integrability and distribution functions agree; this file records the closed form.
-/

@[expose] public section

namespace PDE.JohnNirenberg

open BoxIntegral MeasureTheory Set

/-- Averages over the closed box and over its half-open carrier agree. -/
theorem integralAverage_Icc_eq {d : ℕ} (J : Box (Fin d)) (f : Vec d → ℝ) :
    integralAverage (Box.Icc J) f = integralAverage (J : Set (Vec d)) f := by
  unfold integralAverage
  rw [measure_congr J.coe_ae_eq_Icc.symm, setIntegral_congr_set J.coe_ae_eq_Icc.symm]

/-- **John–Nirenberg inequality on closed cubes** (Lemma 1.16, closed form). If
`v ∈ L¹(Q)` for the closed box `Q = Box.Icc I` and `⨍_P |v - (v)_P| ≤ N` for every closed dyadic
subcube `P = Box.Icc (dyadicDescendant I p)` (including `Q`), then
`|{x ∈ Q : |v(x) - (v)_Q| > t}| ≤ e² |Q| exp(-t / (2 ^ d e N))`. -/
theorem volume_lt_abs_sub_integralAverage_Icc_le {d : ℕ} (hd : 0 < d) (I : Box (Fin d))
    {v : Vec d → ℝ} (hv : IntegrableOn v (Box.Icc I)) {N : ℝ} (hN : 0 < N)
    (hosc : ∀ p : List (Set (Fin d)),
      integralAverage (Box.Icc (dyadicDescendant I p))
        (fun x => |v x - integralAverage (Box.Icc (dyadicDescendant I p)) v|) ≤ N)
    (t : ℝ) :
    (volume {x ∈ Box.Icc I | t < |v x - integralAverage (Box.Icc I) v|}).toReal ≤
      Real.exp 2 * Real.exp (-(t / ((2 : ℝ) ^ d * Real.exp 1 * N))) *
        (volume (Box.Icc I)).toReal := by
  have hv' : IntegrableOn v (I : Set (Vec d)) := hv.mono_set Box.coe_subset_Icc
  have hosc' : ∀ p : List (Set (Fin d)),
      integralAverage (dyadicDescendant I p : Set (Vec d))
        (fun x => |v x - integralAverage (dyadicDescendant I p : Set (Vec d)) v|) ≤ N := by
    intro p
    have h := hosc p
    rwa [integralAverage_Icc_eq, integralAverage_Icc_eq] at h
  have hmain := volume_lt_abs_sub_integralAverage_le hd I hv' hN hosc' t
  rw [integralAverage_Icc_eq, ← measure_congr I.coe_ae_eq_Icc]
  have hle : volume {x ∈ Box.Icc I | t < |v x - integralAverage (I : Set (Vec d)) v|} ≤
      volume {x ∈ (I : Set (Vec d)) | t < |v x - integralAverage (I : Set (Vec d)) v|} := by
    apply measure_mono_ae
    filter_upwards [I.coe_ae_eq_Icc.symm.le] with x hx hxs
    exact ⟨hx hxs.1, hxs.2⟩
  have htop : volume {x ∈ (I : Set (Vec d)) | t < |v x - integralAverage (I : Set (Vec d)) v|} ≠
      ⊤ := (measure_mono fun x hx => hx.1).trans_lt (I.measure_coe_lt_top volume) |>.ne
  exact (ENNReal.toReal_mono htop hle).trans hmain

end PDE.JohnNirenberg
