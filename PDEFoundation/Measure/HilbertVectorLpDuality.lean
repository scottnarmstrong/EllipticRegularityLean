module

public import PDEFoundation.Measure.ScalarLpDuality
public import PDEFoundation.Measure.HilbertLpCoordinates
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp
public import PDEFoundation.Analysis.HilbertLpPairingNorm

/-! # Genuine duality for the internal finite Hilbert-vector `Lᵖ` carrier -/

@[expose] public section

namespace PDE.Internal
open MeasureTheory
open scoped ENNReal RealInnerProductSpace
noncomputable section
variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {d : ℕ}

private theorem exists_hilbertVectorLp_representing_density
    [IsFiniteMeasure μ] {r : ℝ} (hr : 1 < r)
    [Fact (1 ≤ ENNReal.ofReal r)]
    [Fact (1 ≤ ENNReal.ofReal (r / (r - 1)))]
    (L : Lp (HilbertVec d) (ENNReal.ofReal (r / (r - 1))) μ →L[ℝ] ℝ) :
    ∃ g : Lp (HilbertVec d) (ENNReal.ofReal r) μ,
      ∀ f : Lp (HilbertVec d) (ENNReal.ofReal (r / (r - 1))) μ,
        L f = ∫ x, inner ℝ (g x) (f x) ∂μ := by
  classical
  let p : ENNReal := ENNReal.ofReal r
  let q : ENNReal := ENNReal.ofReal (r / (r - 1))
  have : ENNReal.HolderConjugate p q :=
    (Real.HolderConjugate.conjExponent hr).ennrealOfReal
  have hScalar : ∀ i : Fin d, ∃ g : Lp ℝ p μ,
      (∀ f : Lp ℝ q μ,
        L (hilbertLpCoordinateInjection q i f) = ∫ x, g x * f x ∂μ) ∧
      ‖g‖ = ‖L.comp (hilbertLpCoordinateInjection q i)‖ := by
    intro i
    exact exists_scalarLp_dual_density hr (L.comp (hilbertLpCoordinateInjection q i))
  choose gi hgi using hScalar
  let G : α → HilbertVec d := fun x => WithLp.toLp 2 (fun i => gi i x)
  have hG : MemLp G p μ := MemLp.of_eval_piLp (fun i => Lp.memLp (gi i))
  refine ⟨hG.toLp G, ?_⟩
  intro f
  let fi : Fin d → Lp ℝ q μ := fun i => hilbertLpCoordinateProjection q i f
  have hInt (i : Fin d) : Integrable (fun x => gi i x * fi i x) μ :=
    memLp_one_iff_integrable.mp (by
      exact (Lp.memLp (gi i)).fun_mul (r := 1) (Lp.memLp (fi i)))
  have hSum : L f = ∑ i : Fin d, ∫ x, gi i x * fi i x ∂μ := by
    calc
      L f = L (∑ i : Fin d, hilbertLpCoordinateInjection q i (fi i)) := by
        rw [← hilbertLp_eq_sum_coordinate_injections f]
      _ = ∑ i : Fin d, L (hilbertLpCoordinateInjection q i (fi i)) := map_sum L _ _
      _ = _ := Finset.sum_congr rfl (fun i _ => (hgi i).1 (fi i))
  rw [hSum, ← integral_finsetSum Finset.univ (fun i _ => hInt i)]
  apply integral_congr_ae
  have hCoord : ∀ᵐ x ∂μ, ∀ i : Fin d, fi i x = f x i := by
    apply ae_all_iff.mpr
    intro i
    exact (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i).coeFn_compLpL f
  filter_upwards [hG.coeFn_toLp, hCoord] with x hGx hcx
  rw [hGx]
  simp [G, PiLp.inner_apply, hcx, mul_comm]

/-- A continuous functional on finite-measure, finite-dimensional Hilbert
`Lᑫ` has an actual `Lʳ` representing density with exactly the same norm.
Scalar RN representation, vector membership, all-input representation and the
sharp norm equality are derived internally. Native fields are obtained through
the exact Hilbert conversion API. -/
theorem exists_hilbertVectorLp_dual_density
    [IsFiniteMeasure μ] {r : ℝ} (hr : 1 < r)
    [Fact (1 ≤ ENNReal.ofReal r)]
    [Fact (1 ≤ ENNReal.ofReal (r / (r - 1)))]
    (L : Lp (HilbertVec d) (ENNReal.ofReal (r / (r - 1))) μ →L[ℝ] ℝ) :
    ∃ g : Lp (HilbertVec d) (ENNReal.ofReal r) μ,
      (∀ f : Lp (HilbertVec d) (ENNReal.ofReal (r / (r - 1))) μ,
        L f = ∫ x, inner ℝ (g x) (f x) ∂μ) ∧ ‖g‖ = ‖L‖ := by
  have : ENNReal.HolderConjugate (ENNReal.ofReal r)
      (ENNReal.ofReal (r / (r - 1))) :=
    (Real.HolderConjugate.conjExponent hr).ennrealOfReal
  rcases exists_hilbertVectorLp_representing_density hr L with ⟨g, hRep⟩
  refine ⟨g, hRep, ?_⟩
  have hEq : L = (innerSL ℝ).lpPairing μ (ENNReal.ofReal r)
      (ENNReal.ofReal (r / (r - 1))) g := by
    ext f
    rw [hRep f, ContinuousLinearMap.lpPairing_eq_integral]
    rfl
  rw [hEq]
  exact (norm_hilbertLpPairing_eq hr g).symm

end

end PDE.Internal
