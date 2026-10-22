module

public import PDEFoundation.Sobolev.H1.ZeroBoundary
public import PDEFoundation.Geometry.EuclideanBall
public import PDEFoundation.Ambient.CoefficientField
public import PDEFoundation.Ambient.HilbertVec
public import PDEFoundation.Measure.RestrictedVolume
public import PDEFoundation.Measure.EuclideanFieldMeasurability
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-!
# Zero-extended data of the boundary reverse Hölder inequality

For `u ∈ H¹₀(B₁)` solving `-∇⋅a∇u = ∇⋅f`, this file defines the energy density
`w = √(∇u ⬝ a∇u)` and the extensions by zero outside `B₁` of `u`, `∇u`, `w`, `|f|`,
`w²` and `|f|²`, and proves their `L^q` membership on bounded sets.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE

namespace MeyersRH

variable {d : ℕ}

/-- The Sobolev exponent `q = 2d/(d+1)` of the reverse Hölder lemma. -/
noncomputable def qExp (d : ℕ) : ℝ := 2 * (d : ℝ) / ((d : ℝ) + 1)

/-- The dual Sobolev exponent `q' = 2d/(d-1)`. -/
noncomputable def qDual (d : ℕ) : ℝ := 2 * (d : ℝ) / ((d : ℝ) - 1)

theorem qExp_holderConjugate (hd : 2 ≤ d) : (qExp d).HolderConjugate (qDual d) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  rw [Real.holderConjugate_iff]
  refine ⟨?_, ?_⟩
  · unfold qExp
    rw [lt_div_iff₀ (by linarith)]; linarith
  · unfold qExp qDual
    have h1 : (d : ℝ) + 1 ≠ 0 := by linarith
    have h2 : (d : ℝ) - 1 ≠ 0 := by linarith
    have h3 : (d : ℝ) ≠ 0 := by linarith
    field_simp
    ring

/-- The energy density `w = √(∇u ⬝ a∇u)`. -/
noncomputable def wField (a : CoeffField d) (u : H10Function (euclideanBall (0 : Vec d) 1))
    (x : Vec d) : ℝ :=
  Real.sqrt (vecDot (u.grad x) (matVecMul (a x) (u.grad x)))

/-- `w²` extended by zero outside `B₁`. -/
noncomputable def gExt (a : CoeffField d) (u : H10Function (euclideanBall (0 : Vec d) 1)) :
    Vec d → ℝ :=
  (euclideanBall (0 : Vec d) 1).indicator (fun x => wField a u x ^ 2)

/-- `|f|²` extended by zero outside `B₁`. -/
noncomputable def hExt (f : Vec d → Vec d) : Vec d → ℝ :=
  (euclideanBall (0 : Vec d) 1).indicator (fun x => vecEuclideanNorm (f x) ^ 2)

/-- `w` extended by zero outside `B₁`. -/
noncomputable def wExt (a : CoeffField d) (u : H10Function (euclideanBall (0 : Vec d) 1)) :
    Vec d → ℝ :=
  (euclideanBall (0 : Vec d) 1).indicator (wField a u)

/-- `|f|` extended by zero outside `B₁`. -/
noncomputable def sExt (f : Vec d → Vec d) : Vec d → ℝ :=
  (euclideanBall (0 : Vec d) 1).indicator (fun x => vecEuclideanNorm (f x))

/-- `u` extended by zero outside `B₁`. -/
noncomputable def uExt (u : H10Function (euclideanBall (0 : Vec d) 1)) : Vec d → ℝ :=
  (euclideanBall (0 : Vec d) 1).indicator u.toFun

/-- `∇u` extended by zero outside `B₁`. -/
noncomputable def gradExt (u : H10Function (euclideanBall (0 : Vec d) 1)) : Vec d → Vec d :=
  (euclideanBall (0 : Vec d) 1).indicator u.grad

theorem vecEuclideanNorm_gradExt (u : H10Function (euclideanBall (0 : Vec d) 1)) (x : Vec d) :
    vecEuclideanNorm (gradExt u x) =
      (euclideanBall (0 : Vec d) 1).indicator (fun x => vecEuclideanNorm (u.grad x)) x := by
  by_cases hx : x ∈ euclideanBall (0 : Vec d) 1
  · simp [gradExt, hx]
  · simp only [gradExt, Set.indicator_of_notMem hx]
    have : vecEuclideanNorm (0 : Vec d) = 0 := by
      simp [vecEuclideanNorm_eq_zero_iff]
    simpa using this

theorem gExt_rpow (a : CoeffField d) (u : H10Function (euclideanBall (0 : Vec d) 1))
    {θ : ℝ} (hθ : 0 < θ) (x : Vec d) :
    gExt a u x ^ θ = wExt a u x ^ (2 * θ) := by
  by_cases hx : x ∈ euclideanBall (0 : Vec d) 1
  · simp only [gExt, wExt, Set.indicator_of_mem hx]
    have hw : 0 ≤ wField a u x := Real.sqrt_nonneg _
    rw [Real.rpow_mul hw, Real.rpow_two]
  · simp only [gExt, wExt, Set.indicator_of_notMem hx]
    rw [Real.zero_rpow hθ.ne', Real.zero_rpow (by positivity)]

theorem wExt_nonneg (a : CoeffField d) (u : H10Function (euclideanBall (0 : Vec d) 1))
    (x : Vec d) : 0 ≤ wExt a u x :=
  Set.indicator_nonneg (fun _ _ => Real.sqrt_nonneg _) x

theorem sExt_nonneg (f : Vec d → Vec d) (x : Vec d) : 0 ≤ sExt f x :=
  Set.indicator_nonneg (fun _ _ => vecEuclideanNorm_nonneg _) x

theorem gExt_nonneg (a : CoeffField d) (u : H10Function (euclideanBall (0 : Vec d) 1))
    (x : Vec d) : 0 ≤ gExt a u x :=
  Set.indicator_nonneg (fun _ _ => sq_nonneg _) x

theorem sExt_sq (f : Vec d → Vec d) (x : Vec d) : sExt f x ^ (2 : ℕ) = hExt f x := by
  by_cases hx : x ∈ euclideanBall (0 : Vec d) 1
  · simp [sExt, hExt, hx]
  · simp [sExt, hExt, hx]

theorem wExt_sq (a : CoeffField d) (u : H10Function (euclideanBall (0 : Vec d) 1))
    (x : Vec d) : wExt a u x ^ (2 : ℕ) = gExt a u x := by
  by_cases hx : x ∈ euclideanBall (0 : Vec d) 1
  · simp [wExt, gExt, hx]
  · simp [wExt, gExt, hx]

/-- Coordinatewise `L^q` membership gives `L^q` membership of the Euclidean magnitude. -/
theorem memLp_vecEuclideanNorm_of_coord
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {q : ℝ≥0∞} {g : α → Vec d}
    (hg : ∀ i, MemLp (fun x => g x i) q μ) :
    MemLp (fun x => vecEuclideanNorm (g x)) q μ := by
  have hHilbert : MemLp (fun x => (g x).toHilbertVec) q μ := by
    rw [memLp_piLp_iff]
    exact hg
  exact hHilbert.norm.ae_eq (Filter.Eventually.of_forall fun x =>
    Vec.vecEuclideanNorm_eq_norm_toHilbertVec (g x) |>.symm)

theorem memLp_grad_norm (u : H10Function (euclideanBall (0 : Vec d) 1)) :
    MemLp (fun x => vecEuclideanNorm (u.grad x)) 2
      (volumeOn (euclideanBall (0 : Vec d) 1)) :=
  memLp_vecEuclideanNorm_of_coord u.toH1Function.gradMemL2

/-- The energy density is a.e. strongly measurable if the coefficient entries are
a.e. measurable. -/
theorem aestronglyMeasurable_wField (a : CoeffField d)
    (hA : ∀ i j : Fin d, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec d) 1)))
    (u : H10Function (euclideanBall (0 : Vec d) 1)) :
    AEStronglyMeasurable (wField a u) (volumeOn (euclideanBall (0 : Vec d) 1)) := by
  have hg : ∀ i, AEMeasurable (fun x => u.grad x i) (volumeOn (euclideanBall (0 : Vec d) 1)) :=
    fun i => (u.toH1Function.gradMemL2 i).aestronglyMeasurable.aemeasurable
  have hinner : ∀ i, AEMeasurable (fun x => matVecMul (a x) (u.grad x) i)
      (volumeOn (euclideanBall (0 : Vec d) 1)) := fun i => by
    unfold matVecMul
    exact Finset.aemeasurable_fun_sum _ fun j _ => (hA i j).mul (hg j)
  have hsum : AEMeasurable (fun x => vecDot (u.grad x) (matVecMul (a x) (u.grad x)))
      (volumeOn (euclideanBall (0 : Vec d) 1)) := by
    unfold vecDot
    exact Finset.aemeasurable_fun_sum _ fun i _ => (hg i).mul (hinner i)
  exact (Real.continuous_sqrt.measurable.comp_aemeasurable hsum).aestronglyMeasurable

/-- Extension by zero from `B` preserves `L²` membership on any finite-volume set,
and lowers the exponent. -/
theorem memLp_indicator_restrict {B P : Set (Vec d)} (hB : MeasurableSet B)
    (hPfin : volume P ≠ ⊤) {F : Vec d → ℝ} {q : ℝ≥0∞} (hq : q ≤ 2)
    (hF : MemLp F 2 (volume.restrict B)) :
    MemLp (B.indicator F) q (volume.restrict P) := by
  rw [memLp_indicator_iff_restrict hB, Measure.restrict_restrict hB]
  have : IsFiniteMeasure (volume.restrict (B ∩ P)) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact lt_of_le_of_lt (measure_mono Set.inter_subset_right) hPfin.lt_top⟩
  exact (hF.mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl)).mono_exponent hq

theorem aestronglyMeasurable_indicator_restrict {B P : Set (Vec d)} (hB : MeasurableSet B)
    {F : Vec d → ℝ} (hF : AEStronglyMeasurable F (volume.restrict B)) :
    AEStronglyMeasurable (B.indicator F) (volume.restrict P) := by
  rw [aestronglyMeasurable_indicator_iff hB, Measure.restrict_restrict hB]
  exact hF.mono_measure (Measure.restrict_mono Set.inter_subset_left le_rfl)

end MeyersRH

end PDE
