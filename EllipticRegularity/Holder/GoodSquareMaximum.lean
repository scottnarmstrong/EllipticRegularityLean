module

public import EllipticRegularity.MaximumPrinciple.Weak
public import PDEFoundation.Regularity.EssentialOscillationHolder
public import PDEFoundation.Sobolev.H1.SquareBoundaryBounds
public import PDEFoundation.Sobolev.H1.SquareLowerZeroBoundary
public import PDEFoundation.Sobolev.H1.SquareZeroBoundary

/-!
# Good-square maximum principle

This module is the first composition of the planar good-boundary selection
with the weak maximum principle.  A harmonic function on an outer square has
an intermediate square whose continuous certified trace determines an
explicit almost-everywhere upper bound in its interior.  The radius selection,
restriction of the coefficient field and weak equation, and the
trace-to-`H¹₀` argument are retained rather than hidden in an assumption.
-/

@[expose] public section

namespace PDE

open Filter MeasureTheory Set

noncomputable section

/-- Transport the public axis-box maximum principle to a centered planar
square, while retaining the restriction from the ambient domain explicitly.
The input is the raw positive-truncation `H¹₀` membership so that no
representative-level coercion is hidden in the transport. -/
private theorem ae_le_on_centeredAxisCube_of_positivePart_memH10
    {lam Lam k : ℝ} {U : Set (Vec 2)} {a : CoeffField 2}
    {u : H1Function U} {x₀ : Vec 2} {ρ : ℝ}
    (hU : IsOpenBoundedConvexDomain U)
    (hρ : 0 < ρ)
    (hQU : centeredAxisCube x₀ ρ ⊆ U)
    (hEll : IsEllipticFieldOn lam Lam U a) (hlam : 0 < lam)
    (hsol : IsWeakDivergenceFormHarmonicOn a U u)
    (hzero : MemH10 (centeredAxisCube x₀ ρ)
      (fun x => max (u.toFun x - k) 0)) :
    ∀ᵐ x ∂volumeOn (centeredAxisCube x₀ ρ), u.toFun x ≤ k := by
  let lower : Vec 2 := ![x₀ 0 - ρ, x₀ 1 - ρ]
  let upper : Vec 2 := ![x₀ 0 + ρ, x₀ 1 + ρ]
  let box : Set (Vec 2) := axisBox lower upper
  have hbox : centeredAxisCube x₀ ρ = box := by
    dsimp only [box, lower, upper]
    exact (planar_axisBox_eq_centeredAxisCube x₀ ρ).symm
  have hboxU : box ⊆ U := hbox ▸ hQU
  let uBox : H1Function box :=
    u.restrict (isOpen_axisBox lower upper) hboxU
  have hEllBox : IsEllipticFieldOn lam Lam box a :=
    hEll.mono (isOpen_axisBox lower upper).measurableSet hboxU
  have hsolBox : IsWeakDivergenceFormHarmonicOn a box uBox := by
    simpa only [uBox] using hsol.restrict hU.isOpen
      (isOpen_axisBox lower upper) hboxU
  have hzeroBoxRaw : MemH10 box (fun x => max (u.toFun x - k) 0) :=
    hbox ▸ hzero
  have hzeroBox : MemH10 box
      (uBox.positivePartSubConst
        (isOpenBoundedConvexDomain_axisBox lower upper) k).toFun := by
    simpa only [uBox, H1Function.positivePartSubConst_toFun,
      H1Function.restrict_toFun] using hzeroBoxRaw
  have hmaxBox : ∀ᵐ x ∂volumeOn box, uBox.toFun x ≤ k :=
    weakMaximumOn_axisBox_of_positivePartSubConst_memH10
      (a := lower) (b := upper) (coeff := a) (u := uBox)
      (lam := lam) (Lam := Lam) (k := k)
      (by
        intro i
        fin_cases i
        · change x₀ 0 - ρ < x₀ 0 + ρ
          linarith
        · change x₀ 1 - ρ < x₀ 1 + ρ
          linarith)
      ⟨0, by omega⟩ hEllBox hlam
      (hsolBox.toH10SubharmonicOn hEllBox) hzeroBox
  have hmaxRawBox : ∀ᵐ x ∂volumeOn box, u.toFun x ≤ k := by
    simpa only [uBox, H1Function.restrict_toFun] using hmaxBox
  exact hbox.symm ▸ hmaxRawBox

/-- The symmetric centered-square transport for the public axis-box minimum
principle.  As above, the restriction of the equation and coefficient field
is visible and the input is the raw negative truncation. -/
private theorem ae_const_le_on_centeredAxisCube_of_negativePart_memH10
    {lam Lam k : ℝ} {U : Set (Vec 2)} {a : CoeffField 2}
    {u : H1Function U} {x₀ : Vec 2} {ρ : ℝ}
    (hU : IsOpenBoundedConvexDomain U)
    (hρ : 0 < ρ)
    (hQU : centeredAxisCube x₀ ρ ⊆ U)
    (hEll : IsEllipticFieldOn lam Lam U a) (hlam : 0 < lam)
    (hsol : IsWeakDivergenceFormHarmonicOn a U u)
    (hzero : MemH10 (centeredAxisCube x₀ ρ)
      (fun x => max (k - u.toFun x) 0)) :
    ∀ᵐ x ∂volumeOn (centeredAxisCube x₀ ρ), k ≤ u.toFun x := by
  let lower : Vec 2 := ![x₀ 0 - ρ, x₀ 1 - ρ]
  let upper : Vec 2 := ![x₀ 0 + ρ, x₀ 1 + ρ]
  let box : Set (Vec 2) := axisBox lower upper
  have hbox : centeredAxisCube x₀ ρ = box := by
    dsimp only [box, lower, upper]
    exact (planar_axisBox_eq_centeredAxisCube x₀ ρ).symm
  have hboxU : box ⊆ U := hbox ▸ hQU
  let uBox : H1Function box :=
    u.restrict (isOpen_axisBox lower upper) hboxU
  have hEllBox : IsEllipticFieldOn lam Lam box a :=
    hEll.mono (isOpen_axisBox lower upper).measurableSet hboxU
  have hsolBox : IsWeakDivergenceFormHarmonicOn a box uBox := by
    simpa only [uBox] using hsol.restrict hU.isOpen
      (isOpen_axisBox lower upper) hboxU
  have hzeroBoxRaw : MemH10 box (fun x => max (k - u.toFun x) 0) :=
    hbox ▸ hzero
  have hzeroBox : MemH10 box (fun x => max (k - uBox.toFun x) 0) := by
    simpa only [uBox, H1Function.restrict_toFun] using hzeroBoxRaw
  have hminBox : ∀ᵐ x ∂volumeOn box, k ≤ uBox.toFun x :=
    weakMinimumOn_axisBox_of_constSub_positivePart_memH10
      (a := lower) (b := upper) (coeff := a) (u := uBox)
      (lam := lam) (Lam := Lam) (k := k)
      (by
        intro i
        fin_cases i
        · change x₀ 0 - ρ < x₀ 0 + ρ
          linarith
        · change x₀ 1 - ρ < x₀ 1 + ρ
          linarith)
      ⟨0, by omega⟩ hEllBox hlam
      (hsolBox.toH10SuperharmonicOn hEllBox) hzeroBox
  have hminRawBox : ∀ᵐ x ∂volumeOn box, k ≤ u.toFun x := by
    simpa only [uBox, H1Function.restrict_toFun] using hminBox
  exact hbox.symm ▸ hminRawBox

/-- A planar harmonic function has an intermediate square on which its value
is bounded above almost everywhere by the right-side trace at the center of
that side, plus the literal square root of `64` times the surrounding shell
energy.  The selected common trace certificate is retained so that the
symmetric lower bound can be composed with the same square and same trace.

The result is deliberately stated before any estimate replacing the shell
energy by coefficient energy: the `64` comes solely from the good-boundary
selection and is therefore not mixed with ellipticity constants. -/
theorem exists_squareNormalTraceCertificate_with_ae_upper_bound_of_harmonic
    {lam Lam : ℝ} {U : Set (Vec 2)} {a : CoeffField 2}
    {u : H1Function U} (hU : IsOpenBoundedConvexDomain U)
    {x₀ : Vec 2} {r : ℝ} (hr : 0 < r)
    (houter : centeredAxisCube x₀ (2 * r) ⊆ U)
    (hEll : IsEllipticFieldOn lam Lam U a) (hlam : 0 < lam)
    (hsol : IsWeakDivergenceFormHarmonicOn a U u) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ ρ,
      ∃ C : SquareNormalTraceCertificate
        (fun n =>
          (W1pFunction.convexApproxSmoothW1p hU (by norm_num)
            u.toW1pFunction x₀ hr (k n)).toFun)
        u.toFun u.grad x₀ ρ,
      ρ ∈ Ioo r (2 * r) ∧
        C.traceProvenance.trace.HasBoundarySqOscillationLE
          (64 * squareShellVectorEnergy u.grad x₀ r) ∧
        ∀ᵐ x ∂volumeOn (centeredAxisCube x₀ ρ),
          u.toFun x ≤ C.traceProvenance.trace.right (x₀ 1) +
            Real.sqrt (64 * squareShellVectorEnergy u.grad x₀ r) := by
  obtain ⟨k, hk, ρ, C, hρ, hboundary, _hactual, _henlarged⟩ :=
    u.exists_squareNormalTraceCertificate_with_boundarySqOscillationLE
      hU hr houter
  let Q : Set (Vec 2) := centeredAxisCube x₀ ρ
  let uQ : H1Function Q :=
    u.restrict (isOpen_centeredAxisCube x₀ ρ)
      ((centeredAxisCube_mono x₀ hρ.2.le).trans houter)
  have hQU : Q ⊆ U := by
    dsimp only [Q]
    exact (centeredAxisCube_mono x₀ hρ.2.le).trans houter
  let B : ℝ := 64 * squareShellVectorEnergy u.grad x₀ r
  let K : ℝ := C.traceProvenance.trace.right (x₀ 1) + Real.sqrt B
  have hρnonneg : 0 ≤ ρ := (hr.trans hρ.1).le
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg (by norm_num)
      (integral_nonneg fun x => vecNormSq_nonneg (u.grad x))
  have htrace_left : ∀ t ∈ Icc (x₀ 1 - ρ) (x₀ 1 + ρ),
      C.traceProvenance.trace.left t ≤ K := by
    intro t ht
    simpa only [SquareSideTrace.sideValue, B, K] using
      hboundary.sideValue_le_right_center_add_sqrt hρnonneg hB .left t ht
  have htrace_right : ∀ t ∈ Icc (x₀ 1 - ρ) (x₀ 1 + ρ),
      C.traceProvenance.trace.right t ≤ K := by
    intro t ht
    simpa only [SquareSideTrace.sideValue, B, K] using
      hboundary.sideValue_le_right_center_add_sqrt hρnonneg hB .right t ht
  have htrace_bottom : ∀ s ∈ Icc (x₀ 0 - ρ) (x₀ 0 + ρ),
      C.traceProvenance.trace.bottom s ≤ K := by
    intro s hs
    simpa only [SquareSideTrace.sideValue, B, K] using
      hboundary.sideValue_le_right_center_add_sqrt hρnonneg hB .bottom s hs
  have htrace_top : ∀ s ∈ Icc (x₀ 0 - ρ) (x₀ 0 + ρ),
      C.traceProvenance.trace.top s ≤ K := by
    intro s hs
    simpa only [SquareSideTrace.sideValue, B, K] using
      hboundary.sideValue_le_right_center_add_sqrt hρnonneg hB .top s hs
  have hzero : MemH10 Q
      (uQ.positivePartSubConst
        (isOpenBoundedConvexDomain_centeredAxisCube x₀ ρ) K).toFun :=
    by
      simpa only [uQ, H1Function.restrict_toFun, H1Function.restrict_grad] using
        C.memH10_positivePartSubConst_of_trace_upper_bounds
          htrace_left htrace_right htrace_bottom htrace_top
  have hzeroRawQ : MemH10 Q (fun x => max (u.toFun x - K) 0) := by
    simpa only [uQ, H1Function.positivePartSubConst_toFun,
      H1Function.restrict_toFun] using hzero
  have hmax : ∀ᵐ x ∂volumeOn Q, u.toFun x ≤ K :=
    ae_le_on_centeredAxisCube_of_positivePart_memH10
      hU (hr.trans hρ.1) hQU hEll hlam hsol hzeroRawQ
  refine ⟨k, hk, ρ, C, hρ, hboundary, ?_⟩
  simpa only [Q, B, K] using hmax

/-- A single selected good square controls both sides of a planar harmonic
function.  Its lower and upper levels are the same right-side reference trace
value shifted by the literal square root of `64` times the surrounding shell
energy.  In particular, the two bounds use one common approximation sequence,
one radius, and one trace certificate. -/
theorem exists_squareNormalTraceCertificate_with_ae_bounds_of_harmonic
    {lam Lam : ℝ} {U : Set (Vec 2)} {a : CoeffField 2}
    {u : H1Function U} (hU : IsOpenBoundedConvexDomain U)
    {x₀ : Vec 2} {r : ℝ} (hr : 0 < r)
    (houter : centeredAxisCube x₀ (2 * r) ⊆ U)
    (hEll : IsEllipticFieldOn lam Lam U a) (hlam : 0 < lam)
    (hsol : IsWeakDivergenceFormHarmonicOn a U u) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ ρ,
      ∃ C : SquareNormalTraceCertificate
        (fun n =>
          (W1pFunction.convexApproxSmoothW1p hU (by norm_num)
            u.toW1pFunction x₀ hr (k n)).toFun)
        u.toFun u.grad x₀ ρ,
      ρ ∈ Ioo r (2 * r) ∧
        C.traceProvenance.trace.HasBoundarySqOscillationLE
          (64 * squareShellVectorEnergy u.grad x₀ r) ∧
        ∀ᵐ x ∂volumeOn (centeredAxisCube x₀ ρ),
          C.traceProvenance.trace.right (x₀ 1) -
              Real.sqrt (64 * squareShellVectorEnergy u.grad x₀ r) ≤
            u.toFun x ∧
            u.toFun x ≤ C.traceProvenance.trace.right (x₀ 1) +
              Real.sqrt (64 * squareShellVectorEnergy u.grad x₀ r) := by
  obtain ⟨k, hk, ρ, C, hρ, hboundary, hupper⟩ :=
    exists_squareNormalTraceCertificate_with_ae_upper_bound_of_harmonic
      hU hr houter hEll hlam hsol
  let Q : Set (Vec 2) := centeredAxisCube x₀ ρ
  let uQ : H1Function Q :=
    u.restrict (isOpen_centeredAxisCube x₀ ρ)
      ((centeredAxisCube_mono x₀ hρ.2.le).trans houter)
  have hQU : Q ⊆ U := by
    dsimp only [Q]
    exact (centeredAxisCube_mono x₀ hρ.2.le).trans houter
  let B : ℝ := 64 * squareShellVectorEnergy u.grad x₀ r
  let K : ℝ := C.traceProvenance.trace.right (x₀ 1) - Real.sqrt B
  have hρnonneg : 0 ≤ ρ := (hr.trans hρ.1).le
  have hB : 0 ≤ B := by
    dsimp only [B]
    exact mul_nonneg (by norm_num)
      (integral_nonneg fun x => vecNormSq_nonneg (u.grad x))
  have htrace_left : ∀ t ∈ Icc (x₀ 1 - ρ) (x₀ 1 + ρ),
      K ≤ C.traceProvenance.trace.left t := by
    intro t ht
    simpa only [SquareSideTrace.sideValue, B, K] using
      hboundary.right_center_sub_sqrt_le_sideValue hρnonneg hB .left t ht
  have htrace_right : ∀ t ∈ Icc (x₀ 1 - ρ) (x₀ 1 + ρ),
      K ≤ C.traceProvenance.trace.right t := by
    intro t ht
    simpa only [SquareSideTrace.sideValue, B, K] using
      hboundary.right_center_sub_sqrt_le_sideValue hρnonneg hB .right t ht
  have htrace_bottom : ∀ s ∈ Icc (x₀ 0 - ρ) (x₀ 0 + ρ),
      K ≤ C.traceProvenance.trace.bottom s := by
    intro s hs
    simpa only [SquareSideTrace.sideValue, B, K] using
      hboundary.right_center_sub_sqrt_le_sideValue hρnonneg hB .bottom s hs
  have htrace_top : ∀ s ∈ Icc (x₀ 0 - ρ) (x₀ 0 + ρ),
      K ≤ C.traceProvenance.trace.top s := by
    intro s hs
    simpa only [SquareSideTrace.sideValue, B, K] using
      hboundary.right_center_sub_sqrt_le_sideValue hρnonneg hB .top s hs
  have hzero : MemH10 Q
      (uQ.negativePartConstSub
        (isOpenBoundedConvexDomain_centeredAxisCube x₀ ρ) K).toFun := by
    simpa only [uQ, H1Function.restrict_toFun, H1Function.restrict_grad] using
      C.memH10_negativePartConstSub_of_trace_lower_bounds
        htrace_left htrace_right htrace_bottom htrace_top
  have hzeroRawQ : MemH10 Q (fun x => max (K - u.toFun x) 0) := by
    simpa only [uQ, H1Function.negativePartConstSub_toFun,
      H1Function.restrict_toFun] using hzero
  have hlower : ∀ᵐ x ∂volumeOn Q, K ≤ u.toFun x :=
    ae_const_le_on_centeredAxisCube_of_negativePart_memH10
      hU (hr.trans hρ.1) hQU hEll hlam hsol hzeroRawQ
  refine ⟨k, hk, ρ, C, hρ, hboundary, ?_⟩
  filter_upwards [hlower, hupper] with x hxlower hxupper
  constructor
  · simpa only [Q, B, K] using hxlower
  · simpa only [B] using hxupper

/-- The common selected good square has essential oscillation at most `16`
times the square root of the surrounding shell energy.  This is exactly twice
the trace-to-interior half-width; the factor `16` is the simplification of
`2 * sqrt 64`, while the preceding trace certificate retains the literal
boundary constant `64`. -/
theorem exists_squareNormalTraceCertificate_with_essentialOscillationLE_of_harmonic
    {lam Lam : ℝ} {U : Set (Vec 2)} {a : CoeffField 2}
    {u : H1Function U} (hU : IsOpenBoundedConvexDomain U)
    {x₀ : Vec 2} {r : ℝ} (hr : 0 < r)
    (houter : centeredAxisCube x₀ (2 * r) ⊆ U)
    (hEll : IsEllipticFieldOn lam Lam U a) (hlam : 0 < lam)
    (hsol : IsWeakDivergenceFormHarmonicOn a U u) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ ρ,
      ∃ C : SquareNormalTraceCertificate
        (fun n =>
          (W1pFunction.convexApproxSmoothW1p hU (by norm_num)
            u.toW1pFunction x₀ hr (k n)).toFun)
        u.toFun u.grad x₀ ρ,
      ρ ∈ Ioo r (2 * r) ∧
        C.traceProvenance.trace.HasBoundarySqOscillationLE
          (64 * squareShellVectorEnergy u.grad x₀ r) ∧
        HasEssentialOscillationLEOn u.toFun (centeredAxisCube x₀ ρ)
          (16 * Real.sqrt (squareShellVectorEnergy u.grad x₀ r)) := by
  obtain ⟨k, hk, ρ, C, hρ, hboundary, hbounds⟩ :=
    exists_squareNormalTraceCertificate_with_ae_bounds_of_harmonic
      hU hr houter hEll hlam hsol
  let E : ℝ := squareShellVectorEnergy u.grad x₀ r
  have hsqrt64 : Real.sqrt (64 : ℝ) = 8 := by
    rw [Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)]
    norm_num
  have hsqrt : Real.sqrt (64 * E) = 8 * Real.sqrt E := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 64), hsqrt64]
  refine ⟨k, hk, ρ, C, hρ, hboundary, ?_⟩
  refine ⟨C.traceProvenance.trace.right (x₀ 1) - Real.sqrt (64 * E),
    C.traceProvenance.trace.right (x₀ 1) + Real.sqrt (64 * E), ?_, ?_⟩
  · filter_upwards [hbounds] with x hx
    simpa only [E] using! hx
  · calc
      (C.traceProvenance.trace.right (x₀ 1) + Real.sqrt (64 * E)) -
          (C.traceProvenance.trace.right (x₀ 1) - Real.sqrt (64 * E)) =
        2 * Real.sqrt (64 * E) := by ring
      _ = 16 * Real.sqrt E := by rw [hsqrt]; ring
      _ ≤ 16 * Real.sqrt (squareShellVectorEnergy u.grad x₀ r) := by
        rfl

/-- Clean downstream form of the good-square estimate: some intermediate
centered square has essential oscillation at most `16` times the square root
of the surrounding shell energy.  The certificate-producing theorem above
retains the approximation and trace data when those are needed. -/
theorem exists_radius_essentialOscillationLEOn_centeredAxisCube_of_harmonic
    {lam Lam : ℝ} {U : Set (Vec 2)} {a : CoeffField 2}
    {u : H1Function U} (hU : IsOpenBoundedConvexDomain U)
    {x₀ : Vec 2} {r : ℝ} (hr : 0 < r)
    (houter : centeredAxisCube x₀ (2 * r) ⊆ U)
    (hEll : IsEllipticFieldOn lam Lam U a) (hlam : 0 < lam)
    (hsol : IsWeakDivergenceFormHarmonicOn a U u) :
    ∃ ρ ∈ Ioo r (2 * r),
      HasEssentialOscillationLEOn u.toFun (centeredAxisCube x₀ ρ)
        (16 * Real.sqrt (squareShellVectorEnergy u.grad x₀ r)) := by
  obtain ⟨_k, _hk, ρ, _C, hρ, _hboundary, hosc⟩ :=
    exists_squareNormalTraceCertificate_with_essentialOscillationLE_of_harmonic
      hU hr houter hEll hlam hsol
  exact ⟨ρ, hρ, hosc⟩

end

end PDE
