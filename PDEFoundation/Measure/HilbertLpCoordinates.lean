module

public import PDEFoundation.Ambient.HilbertVec
public import PDEFoundation.Ambient.Basis
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-! # Exact coordinate decomposition of internal Hilbert-valued `Lᵖ` -/

@[expose] public section

namespace PDE.Internal
open MeasureTheory
open scoped ENNReal
noncomputable section
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {d : ℕ}

private theorem coeFn_finset_sumLp {ι E : Type*} [NormedAddCommGroup E]
    (p : ENNReal) (s : Finset ι) (f : ι → Lp E p μ) :
    ⇑(∑ i ∈ s, f i) =ᵐ[μ] fun x => ∑ i ∈ s, (f i : α → E) x := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using! Lp.coeFn_zero E p μ
  | @insert a s ha ih =>
    filter_upwards [Lp.coeFn_add (f a) (∑ i ∈ s, f i), ih] with x hadd hsum
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, Pi.add_apply, hsum]

/-- Insert a scalar into the native coordinate basis, inside the Hilbert wrapper. -/
def hilbertVecCoordinateInjection (i : Fin d) : ℝ →L[ℝ] HilbertVec d :=
  (ContinuousLinearMap.id ℝ ℝ).smulRight (basisVec i).toHilbertVec

/-- Apply the coordinate insertion pointwise to an actual scalar `Lᵖ` class. -/
def hilbertLpCoordinateInjection (p : ENNReal) [Fact (1 ≤ p)] (i : Fin d) :
    Lp ℝ p μ →L[ℝ] Lp (HilbertVec d) p μ :=
  (hilbertVecCoordinateInjection i).compLpL p μ

/-- Extract an actual coordinate `Lᵖ` class from a Hilbert-valued class. -/
def hilbertLpCoordinateProjection (p : ENNReal) [Fact (1 ≤ p)] (i : Fin d) :
    Lp (HilbertVec d) p μ →L[ℝ] Lp ℝ p μ :=
  (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i).compLpL p μ

/-- Every Hilbert-valued `Lᵖ` element is exactly the finite sum of its
coordinate insertions, with no representative equality assumed. -/
theorem hilbertLp_eq_sum_coordinate_injections
    {p : ENNReal} [Fact (1 ≤ p)] (f : Lp (HilbertVec d) p μ) :
    f = ∑ i : Fin d, hilbertLpCoordinateInjection p i
      (hilbertLpCoordinateProjection p i f) := by
  apply Lp.ext
  have hsum := coeFn_finset_sumLp p (Finset.univ : Finset (Fin d))
    (fun i => hilbertLpCoordinateInjection p i (hilbertLpCoordinateProjection p i f))
  have hcoords : ∀ᵐ x ∂μ, ∀ i : Fin d,
      (hilbertLpCoordinateInjection p i (hilbertLpCoordinateProjection p i f)) x =
        f x i • (basisVec i).toHilbertVec := by
    apply ae_all_iff.mpr
    intro i
    filter_upwards [(hilbertVecCoordinateInjection i).coeFn_compLpL
      (hilbertLpCoordinateProjection p i f),
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i).coeFn_compLpL f] with x hi hp
    simp only [hilbertLpCoordinateInjection, hilbertVecCoordinateInjection,
      ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply] at hi ⊢
    rw [hi]
    change (hilbertLpCoordinateProjection p i f) x • _ = _
    rw [show (hilbertLpCoordinateProjection p i f) x = f x i from hp]
  filter_upwards [hsum, hcoords] with x hx hcx
  rw [hx]
  ext j
  simp [hcx, basisVec_apply]

end

end PDE.Internal
