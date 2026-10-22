module

public import EllipticRegularity.Parabolic.Energy.Mollifier
public import PDEFoundation.Sobolev.Ch4.Compact
public import PDEFoundation.Sobolev.Inequalities.SobolevWholeSpaceCutoff

/-!
# The weak-derivative identity for `C¹` compactly supported test functions

If `f` has weak partial derivative `Df` in `U` (tested against smooth functions), both locally
integrable, then `∫ f ∂ᵢζ = - ∫ Df ζ` for every `C¹` compactly supported `ζ` with support in `U`.
-/

@[expose] public section

open scoped ENNReal Convolution Topology

namespace PDE.Parabolic.Slice

open MeasureTheory Set Filter Metric PDE PDE.Parabolic.Energy

variable {d : ℕ}

theorem weak_partial_C1 {U : Set (Vec d)} (hU : IsOpen U) {i : Fin d} {f Df : Vec d → ℝ}
    (hw : HasWeakPartialDerivOn U i f Df) {ζ : Vec d → ℝ} (hζ : ContDiff ℝ 1 ζ)
    (hζc : HasCompactSupport ζ) (_hζU : tsupport ζ ⊆ U) {K' : Set (Vec d)} (hK'c : IsCompact K')
    (hK'U : K' ⊆ U) {δ : ℝ} (hδ : 0 < δ) (hδK : cthickening δ (tsupport ζ) ⊆ K')
    (hf : Integrable f (volume.restrict K')) (hDf : Integrable Df (volume.restrict K')) :
    ∫ x in U, f x * fderiv ℝ ζ x (basisVec i) = -∫ x in U, Df x * ζ x := by
  have hρ := isConvexApproxKernel_unitConvexApproxKernel (d := d)
  set Dζ : Vec d → ℝ := fun x => fderiv ℝ ζ x (basisVec i) with hDζ
  have hDζc : Continuous Dζ := (hζ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hDζ0 : ∀ x, x ∉ tsupport ζ → Dζ x = 0 := fun x hx => by
    simp [hDζ, fderiv_of_notMem_tsupport ℝ hx]
  have hDζcs : HasCompactSupport Dζ := by
    refine HasCompactSupport.of_support_subset_isCompact hζc.isCompact fun x hx => ?_
    by_contra h; exact hx (hDζ0 x h)
  have hζcont : Continuous ζ := hζ.continuous
  set E : ℝ := (∫ x in U, f x * Dζ x) + ∫ x in U, Df x * ζ x with hE
  -- reduce `∫_U` to `∫_{K'}` for functions supported in `K'`
  have hcut : ∀ g : Vec d → ℝ, (∀ x, x ∉ K' → g x = 0) → ∫ x in U, g x = ∫ x in K', g x := by
    intro g hg
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hK'U fun x hx => ?_
    exact hg x hx.2
  have hsuppK : tsupport ζ ⊆ K' := (self_subset_cthickening _).trans hδK
  have hmain : ∀ ε : ℝ, 0 < ε → |E| ≤ ε * ((∫ x in K', |f x|) + ∫ x in K', |Df x|) := by
    intro ε hε
    obtain ⟨a1, ha1, h1⟩ := exists_forall_dist_wholeSpaceMollify_le hDζc hDζcs hε
    obtain ⟨a2, ha2, h2⟩ := exists_forall_dist_wholeSpaceMollify_le hζcont hζc hε
    set a : ℝ := min (min a1 a2) (min δ 1) with hadef
    have ha0 : 0 < a := lt_min (lt_min ha1 ha2) (lt_min hδ one_pos)
    have haa1 : a ≤ a1 := (min_le_left _ _).trans (min_le_left _ _)
    have haa2 : a ≤ a2 := (min_le_left _ _).trans (min_le_right _ _)
    have haδ : a ≤ δ := (min_le_right _ _).trans (min_le_left _ _)
    set ζn : Vec d → ℝ := wholeSpaceMollify a ζ with hζn
    have hζs : ContDiff ℝ (⊤ : ℕ∞) ζn := moll_contDiff ha0 (hζcont.locallyIntegrable)
    have hsupp : Function.support ζn ⊆ cthickening a (tsupport ζ) :=
      PDE.Ch4Infra.support_wholeSpaceMollify_subset_cthickening ha0
    have hζnc : HasCompactSupport ζn :=
      HasCompactSupport.of_support_subset_isCompact (hζc.isCompact.cthickening (r := a)) hsupp
    have hts : tsupport ζn ⊆ K' :=
      closure_minimal (hsupp.trans ((cthickening_mono haδ _).trans hδK)) hK'c.isClosed
    have hderiv : ∀ x, fderiv ℝ ζn x (basisVec i) = wholeSpaceMollify a Dζ x := fun x =>
      congrFun (euclideanCoordDeriv_convolution_eq_of_hasWeakPartialDerivOn
        (hasCompactSupport_scaledConvexApproxKernel hρ.compactSupport ha0)
        (contDiff_scaledConvexApproxKernel hρ _) (hζcont.locallyIntegrable)
        (HasWeakPartialDerivOn.of_contDiff (U := Set.univ) (i := i) hζ)) x
    have hid := hw ζn hζs hζnc (hts.trans hK'U)
    simp only [hderiv] at hid
    -- support of the mollified derivative
    have hmDsupp : Function.support (wholeSpaceMollify a Dζ) ⊆ K' := by
      intro x hx
      have := PDE.Ch4Infra.support_wholeSpaceMollify_subset_cthickening ha0 hx
      have htD : tsupport Dζ ⊆ tsupport ζ :=
        closure_minimal (fun x hx => by
          by_contra h; exact hx (hDζ0 x h)) (isClosed_tsupport ζ)
      exact ((cthickening_mono haδ _).trans hδK) (cthickening_subset_of_subset a htD this)
    have hmc : Continuous (wholeSpaceMollify a Dζ) :=
      (moll_contDiff ha0 (hDζc.locallyIntegrable)).continuous
    have hζnC : Continuous ζn := hζs.continuous
    -- pass to integrals over `K'`
    have hvan1 : ∀ x, x ∉ K' → f x * Dζ x = 0 := fun x hx => by
      rw [hDζ0 x (fun h => hx (hsuppK h)), mul_zero]
    have hvan2 : ∀ x, x ∉ K' → Df x * ζ x = 0 := fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hsuppK h)), mul_zero]
    have hvan3 : ∀ x, x ∉ K' → f x * wholeSpaceMollify a Dζ x = 0 := fun x hx => by
      rw [show wholeSpaceMollify a Dζ x = 0 from by
        by_contra h; exact hx (hmDsupp h), mul_zero]
    have hvan4 : ∀ x, x ∉ K' → Df x * ζn x = 0 := fun x hx => by
      rw [show ζn x = 0 from by by_contra h; exact hx (hts (subset_tsupport _ h)), mul_zero]
    rw [hcut _ hvan3, hcut _ hvan4] at hid
    have hEK : E = (∫ x in K', f x * Dζ x) + ∫ x in K', Df x * ζ x := by
      rw [hE, hcut _ hvan1, hcut _ hvan2]
    -- integrability on `K'`
    have hbd : ∀ {g h : Vec d → ℝ}, Integrable g (volume.restrict K') → Continuous h →
        HasCompactSupport h → Integrable (fun x => g x * h x) (volume.restrict K') := by
      intro g h hg hh hhc
      obtain ⟨C, hC⟩ := hh.bounded_above_of_compact_support hhc
      exact hg.mul_bdd hh.aestronglyMeasurable (c := C) (Filter.Eventually.of_forall hC)
    have hmDcs : HasCompactSupport (wholeSpaceMollify a Dζ) :=
      HasCompactSupport.of_support_subset_isCompact hK'c hmDsupp
    have iA := hbd hf hDζc hDζcs
    have iB := hbd hf hmc hmDcs
    have iC := hbd hDf hζcont hζc
    have iD := hbd hDf hζnC hζnc
    have hEdiff : E = (∫ x in K', f x * (Dζ x - wholeSpaceMollify a Dζ x)) +
        ∫ x in K', Df x * (ζ x - ζn x) := by
      have e1 : ∫ x in K', f x * (Dζ x - wholeSpaceMollify a Dζ x) =
          (∫ x in K', f x * Dζ x) - ∫ x in K', f x * wholeSpaceMollify a Dζ x := by
        rw [← integral_sub iA iB]; congr 1; funext x; ring
      have e2 : ∫ x in K', Df x * (ζ x - ζn x) =
          (∫ x in K', Df x * ζ x) - ∫ x in K', Df x * ζn x := by
        rw [← integral_sub iC iD]; congr 1; funext x; ring
      rw [e1, e2, hEK]
      linarith [hid]
    have hb1 : ∀ x, |Dζ x - wholeSpaceMollify a Dζ x| ≤ ε := fun x => by
      have := h1 a ha0 haa1 x
      rw [Real.dist_eq, abs_sub_comm] at this; exact this
    have hb2 : ∀ x, |ζ x - ζn x| ≤ ε := fun x => by
      have := h2 a ha0 haa2 x
      rw [Real.dist_eq, abs_sub_comm] at this; exact this
    have hI1 : |∫ x in K', f x * (Dζ x - wholeSpaceMollify a Dζ x)| ≤ ε * ∫ x in K', |f x| := by
      calc |∫ x in K', f x * (Dζ x - wholeSpaceMollify a Dζ x)|
          ≤ ∫ x in K', |f x * (Dζ x - wholeSpaceMollify a Dζ x)| := abs_integral_le_integral_abs
        _ ≤ ∫ x in K', ε * |f x| := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _)
            (hf.abs.const_mul ε) (Filter.Eventually.of_forall fun x => ?_)
          show |f x * (Dζ x - wholeSpaceMollify a Dζ x)| ≤ ε * |f x|
          rw [abs_mul]
          nlinarith [hb1 x, abs_nonneg (f x)]
        _ = ε * ∫ x in K', |f x| := integral_const_mul _ _
    have hI2 : |∫ x in K', Df x * (ζ x - ζn x)| ≤ ε * ∫ x in K', |Df x| := by
      calc |∫ x in K', Df x * (ζ x - ζn x)|
          ≤ ∫ x in K', |Df x * (ζ x - ζn x)| := abs_integral_le_integral_abs
        _ ≤ ∫ x in K', ε * |Df x| := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _)
            (hDf.abs.const_mul ε) (Filter.Eventually.of_forall fun x => ?_)
          show |Df x * (ζ x - ζn x)| ≤ ε * |Df x|
          rw [abs_mul]
          nlinarith [hb2 x, abs_nonneg (Df x)]
        _ = ε * ∫ x in K', |Df x| := integral_const_mul _ _
    rw [hEdiff]
    calc |(∫ x in K', f x * (Dζ x - wholeSpaceMollify a Dζ x)) +
          ∫ x in K', Df x * (ζ x - ζn x)|
        ≤ |∫ x in K', f x * (Dζ x - wholeSpaceMollify a Dζ x)| +
          |∫ x in K', Df x * (ζ x - ζn x)| := abs_add_le _ _
      _ ≤ ε * ((∫ x in K', |f x|) + ∫ x in K', |Df x|) := by linarith
  -- conclude `E = 0`
  have hE0 : E = 0 := by
    by_contra hne
    set C : ℝ := (∫ x in K', |f x|) + ∫ x in K', |Df x| with hC
    have hC0 : 0 ≤ C := by
      rw [hC]; exact add_nonneg (integral_nonneg fun x => abs_nonneg _)
        (integral_nonneg fun x => abs_nonneg _)
    have hEpos : 0 < |E| := abs_pos.2 hne
    have hε : 0 < |E| / (2 * (C + 1)) := by positivity
    have := hmain _ hε
    have h3 : |E| / (2 * (C + 1)) * C < |E| := by
      rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith
    linarith
  linarith [hE0, hE]

end PDE.Parabolic.Slice
