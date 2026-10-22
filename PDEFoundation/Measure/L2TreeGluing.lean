module

public import PDEFoundation.Measure.L2CoverGluing

/-!
# Root-center gluing for a four-piece cover

The tree is `T - L - B` together with `T - R`.  This is the adjacency tree
used by the square-shell cover.  The statement is measure-generic; the
geometric construction only has to provide the literal volume bounds.
-/

@[expose] public section

namespace PDE

open MeasureTheory

variable {X : Type*} [MeasurableSpace X]
variable {μ : Measure X}

/-- A root-center `L²` gluing estimate for the four-piece tree
`T - L - B` and `T - R`.

If each piece has volume at most `M`, every tree overlap has volume at least
`m > 0`, and the four local variances are bounded by `Vᵀ,Vᴸ,Vᴮ,Vᴿ`, then the
variance over the covered set about the top center is bounded by
`(2 + 20 * M / m) * (Vᵀ + Vᴸ + Vᴮ + Vᴿ)`.

All volume bounds are expressed through `μ.real`; finiteness is assumed
exactly for the pieces and overlaps where the proof requires it. -/
theorem setIntegral_sq_sub_le_root_center_four_tree
    {u : X → ℝ} {S sT sL sB sR : Set X}
    {cT cL cB cR VT VL VB VR M m : ℝ}
    (hcover : S ⊆ (sT ∪ sL) ∪ (sB ∪ sR))
    (hIntT : IntegrableOn (fun x => (u x - cT) ^ 2) sT μ)
    (hIntL : IntegrableOn (fun x => (u x - cL) ^ 2) sL μ)
    (hIntB : IntegrableOn (fun x => (u x - cB) ^ 2) sB μ)
    (hIntR : IntegrableOn (fun x => (u x - cR) ^ 2) sR μ)
    (hIntLRoot : IntegrableOn (fun x => (u x - cT) ^ 2) sL μ)
    (hIntBRoot : IntegrableOn (fun x => (u x - cT) ^ 2) sB μ)
    (hIntRRoot : IntegrableOn (fun x => (u x - cT) ^ 2) sR μ)
    (hfiniteL : μ sL ≠ ⊤) (hfiniteB : μ sB ≠ ⊤)
    (hfiniteR : μ sR ≠ ⊤)
    (hTLmeas : MeasurableSet (sT ∩ sL))
    (hLBmeas : MeasurableSet (sL ∩ sB))
    (hTRmeas : MeasurableSet (sT ∩ sR))
    (hTLfinite : μ (sT ∩ sL) ≠ ⊤)
    (hLBfinite : μ (sL ∩ sB) ≠ ⊤)
    (hTRfinite : μ (sT ∩ sR) ≠ ⊤)
    (hm : 0 < m)
    (hTLvol : m ≤ μ.real (sT ∩ sL))
    (hLBvol : m ≤ μ.real (sL ∩ sB))
    (hTRvol : m ≤ μ.real (sT ∩ sR))
    (hTvol : μ.real sT ≤ M) (hLvol : μ.real sL ≤ M)
    (hBvol : μ.real sB ≤ M) (hRvol : μ.real sR ≤ M)
    (hVT : (∫ x in sT, (u x - cT) ^ 2 ∂μ) ≤ VT)
    (hVL : (∫ x in sL, (u x - cL) ^ 2 ∂μ) ≤ VL)
    (hVB : (∫ x in sB, (u x - cB) ^ 2 ∂μ) ≤ VB)
    (hVR : (∫ x in sR, (u x - cR) ^ 2 ∂μ) ≤ VR) :
    ∫ x in S, (u x - cT) ^ 2 ∂μ ≤
      (2 + 20 * M / m) * (VT + VL + VB + VR) := by
  have hITnonneg : 0 ≤ ∫ x in sT, (u x - cT) ^ 2 ∂μ :=
    integral_nonneg_of_ae <|
      Filter.Eventually.of_forall fun x => sq_nonneg (u x - cT)
  have hILnonneg : 0 ≤ ∫ x in sL, (u x - cL) ^ 2 ∂μ :=
    integral_nonneg_of_ae <|
      Filter.Eventually.of_forall fun x => sq_nonneg (u x - cL)
  have hIBnonneg : 0 ≤ ∫ x in sB, (u x - cB) ^ 2 ∂μ :=
    integral_nonneg_of_ae <|
      Filter.Eventually.of_forall fun x => sq_nonneg (u x - cB)
  have hIRnonneg : 0 ≤ ∫ x in sR, (u x - cR) ^ 2 ∂μ :=
    integral_nonneg_of_ae <|
      Filter.Eventually.of_forall fun x => sq_nonneg (u x - cR)
  have hVTnonneg : 0 ≤ VT := hITnonneg.trans hVT
  have hVLnonneg : 0 ≤ VL := hILnonneg.trans hVL
  have hVBnonneg : 0 ≤ VB := hIBnonneg.trans hVB
  have hVRnonneg : 0 ≤ VR := hIRnonneg.trans hVR
  have hMnonneg : 0 ≤ M := by
    exact measureReal_nonneg.trans hTvol
  have haNonneg : 0 ≤ M / m := div_nonneg hMnonneg hm.le
  have hTLbound : m * (cT - cL) ^ 2 ≤ 2 * (VT + VL) :=
    overlap_center_distance_sq_le_of_local_bounds
      (u := u) (s := sT) (t := sL) (c := cT) (d := cL)
      (V := VT) (W := VL) (m := m)
      hIntT hIntL hTLmeas hTLfinite hTLvol hVT hVL
  have hTLcenter' : (cT - cL) ^ 2 ≤ 2 * (VT + VL) / m :=
    overlap_center_distance_sq_le_of_integral_bound hTLbound hm
  have hTLcenter : (cL - cT) ^ 2 ≤ 2 * (VT + VL) / m := by
    simpa only [sub_sq_comm] using hTLcenter'
  have hLBbound : m * (cL - cB) ^ 2 ≤ 2 * (VL + VB) :=
    overlap_center_distance_sq_le_of_local_bounds
      (u := u) (s := sL) (t := sB) (c := cL) (d := cB)
      (V := VL) (W := VB) (m := m)
      hIntL hIntB hLBmeas hLBfinite hLBvol hVL hVB
  have hLBcenter' : (cL - cB) ^ 2 ≤ 2 * (VL + VB) / m :=
    overlap_center_distance_sq_le_of_integral_bound hLBbound hm
  have hLBcenter : (cB - cL) ^ 2 ≤ 2 * (VL + VB) / m := by
    simpa only [sub_sq_comm] using hLBcenter'
  have hTRbound : m * (cT - cR) ^ 2 ≤ 2 * (VT + VR) :=
    overlap_center_distance_sq_le_of_local_bounds
      (u := u) (s := sT) (t := sR) (c := cT) (d := cR)
      (V := VT) (W := VR) (m := m)
      hIntT hIntR hTRmeas hTRfinite hTRvol hVT hVR
  have hTRcenter' : (cT - cR) ^ 2 ≤ 2 * (VT + VR) / m :=
    overlap_center_distance_sq_le_of_integral_bound hTRbound hm
  have hTRcenter : (cR - cT) ^ 2 ≤ 2 * (VT + VR) / m := by
    simpa only [sub_sq_comm] using hTRcenter'
  have hBTcenter : (cB - cT) ^ 2 ≤ 4 * (VT + 2 * VL + VB) / m := by
    calc
      (cB - cT) ^ 2 ≤ 2 * (cB - cL) ^ 2 + 2 * (cL - cT) ^ 2 :=
        sq_sub_le_two_sq_sub_add_two_sq cB cL cT
      _ ≤ 2 * (2 * (VL + VB) / m) + 2 * (2 * (VT + VL) / m) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_left hLBcenter (by norm_num))
          (mul_le_mul_of_nonneg_left hTLcenter (by norm_num))
      _ = 4 * (VT + 2 * VL + VB) / m := by ring
  have hLroot :
      ∫ x in sL, (u x - cT) ^ 2 ∂μ ≤
        2 * VL + 4 * (M / m) * (VT + VL) := by
    have hLprod : μ.real sL * (cL - cT) ^ 2 ≤
        M * (2 * (VT + VL) / m) :=
      mul_le_mul hLvol hTLcenter (sq_nonneg _) hMnonneg
    calc
      ∫ x in sL, (u x - cT) ^ 2 ∂μ ≤
          2 * (∫ x in sL, (u x - cL) ^ 2 ∂μ) +
            2 * μ.real sL * (cL - cT) ^ 2 :=
        setIntegral_sq_sub_le_change_center hIntL hIntLRoot hfiniteL
      _ ≤ 2 * VL + 2 * M * (2 * (VT + VL) / m) := by
        nlinarith only [hVL, hLprod]
      _ = 2 * VL + 4 * (M / m) * (VT + VL) := by ring
  have hBroot :
      ∫ x in sB, (u x - cT) ^ 2 ∂μ ≤
        2 * VB + 8 * (M / m) * (VT + 2 * VL + VB) := by
    have hBprod : μ.real sB * (cB - cT) ^ 2 ≤
        M * (4 * (VT + 2 * VL + VB) / m) :=
      mul_le_mul hBvol hBTcenter (sq_nonneg _) hMnonneg
    calc
      ∫ x in sB, (u x - cT) ^ 2 ∂μ ≤
          2 * (∫ x in sB, (u x - cB) ^ 2 ∂μ) +
            2 * μ.real sB * (cB - cT) ^ 2 :=
        setIntegral_sq_sub_le_change_center hIntB hIntBRoot hfiniteB
      _ ≤ 2 * VB + 2 * M * (4 * (VT + 2 * VL + VB) / m) := by
        nlinarith only [hVB, hBprod]
      _ = 2 * VB + 8 * (M / m) * (VT + 2 * VL + VB) := by ring
  have hRroot :
      ∫ x in sR, (u x - cT) ^ 2 ∂μ ≤
        2 * VR + 4 * (M / m) * (VT + VR) := by
    have hRprod : μ.real sR * (cR - cT) ^ 2 ≤
        M * (2 * (VT + VR) / m) :=
      mul_le_mul hRvol hTRcenter (sq_nonneg _) hMnonneg
    calc
      ∫ x in sR, (u x - cT) ^ 2 ∂μ ≤
          2 * (∫ x in sR, (u x - cR) ^ 2 ∂μ) +
            2 * μ.real sR * (cR - cT) ^ 2 :=
        setIntegral_sq_sub_le_change_center hIntR hIntRRoot hfiniteR
      _ ≤ 2 * VR + 2 * M * (2 * (VT + VR) / m) := by
        nlinarith only [hVR, hRprod]
      _ = 2 * VR + 4 * (M / m) * (VT + VR) := by ring
  have hcoverBound := setIntegral_le_sum_four_of_subset_union
    hcover hIntT hIntLRoot hIntBRoot hIntRRoot
    (fun x => sq_nonneg (u x - cT))
  have hbase : VT + 2 * VL + 2 * VB + 2 * VR ≤
      2 * (VT + VL + VB + VR) := by
    linarith only [hVTnonneg]
  have hcoeff : 16 * VT + 20 * VL + 8 * VB + 4 * VR ≤
      20 * (VT + VL + VB + VR) := by
    linarith only [hVTnonneg, hVBnonneg, hVRnonneg]
  calc
    ∫ x in S, (u x - cT) ^ 2 ∂μ ≤
        (∫ x in sT, (u x - cT) ^ 2 ∂μ) +
          (∫ x in sL, (u x - cT) ^ 2 ∂μ) +
          (∫ x in sB, (u x - cT) ^ 2 ∂μ) +
          ∫ x in sR, (u x - cT) ^ 2 ∂μ := hcoverBound
    _ ≤ VT +
          (2 * VL + 4 * (M / m) * (VT + VL)) +
          (2 * VB + 8 * (M / m) * (VT + 2 * VL + VB)) +
          (2 * VR + 4 * (M / m) * (VT + VR)) := by
      exact add_le_add (add_le_add (add_le_add hVT hLroot) hBroot) hRroot
    _ = (VT + 2 * VL + 2 * VB + 2 * VR) +
          (M / m) * (16 * VT + 20 * VL + 8 * VB + 4 * VR) := by ring
    _ ≤ 2 * (VT + VL + VB + VR) +
          (M / m) * (20 * (VT + VL + VB + VR)) := by
      exact add_le_add hbase (mul_le_mul_of_nonneg_left hcoeff haNonneg)
    _ = (2 + 20 * M / m) * (VT + VL + VB + VR) := by ring

end PDE
