module

public import PDEFoundation.Measure.EuclideanFieldLpTriangle
public import PDEFoundation.Measure.EuclideanFieldMeasurability
public import PDEFoundation.PDE.PerturbationL2

/-! # Euclidean `Lᵖ` bound for perturbative forcing -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped _root_.ENNReal

/-- Coordinates of the perturbation flux are measurable using only
coefficient and field coordinate measurability. -/
theorem aestronglyMeasurable_perturbationFlux_coord
    {d : ℕ} {μ : Measure (Vec d)} {a : CoeffField d} {g : Vec d → Vec d}
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) μ)
    (hg : ∀ j, AEStronglyMeasurable (fun x => g x j) μ) (i : Fin d) :
    AEStronglyMeasurable (fun x => matVecMul (a x - 1) (g x) i) μ := by
  classical
  have hs := Finset.aestronglyMeasurable_sum Finset.univ (fun j _ =>
    ((ha i j).sub (aemeasurable_const : AEMeasurable
      (fun _ : Vec d => (1 : Mat d) i j) μ)).aestronglyMeasurable.mul (hg j))
  convert hs using 1
  funext x
  dsimp only [matVecMul]
  rw [Finset.sum_apply]
  rfl

/-- The literal forcing `F + (a-I)g` has the exact dimension-free `Lᵖ`
bound, with no target membership or finiteness premise.  Coordinate
measurability of `F` makes the forcing itself measurable. -/
theorem eLpNorm_perturbativeForcing_le
    {d : ℕ} {μ : Measure (Vec d)} {a : CoeffField d}
    {F g : Vec d → Vec d} {delta : ℝ} {p : ENNReal}
    (hdelta : 0 ≤ delta) (hp : 1 ≤ p)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) μ)
    (hclose : ∀ᵐ x ∂μ, IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (hF : ∀ i, AEStronglyMeasurable (fun x => F x i) μ)
    (hg : ∀ j, AEStronglyMeasurable (fun x => g x j) μ) :
    eLpNorm (fun x => vecEuclideanNorm
        (F x + matVecMul (a x - 1) (g x))) p μ ≤
      eLpNorm (fun x => vecEuclideanNorm (F x)) p μ +
        ENNReal.ofReal delta * eLpNorm (fun x => vecEuclideanNorm (g x)) p μ := by
  let P : Vec d → Vec d := fun x => matVecMul (a x - 1) (g x)
  have hPcoord : ∀ i, AEStronglyMeasurable (fun x => P x i) μ :=
    fun i => aestronglyMeasurable_perturbationFlux_coord ha hg i
  have hPmag := aestronglyMeasurable_vecEuclideanNorm_of_coord hPcoord
  have htriangle := eLpNorm_vecEuclideanNorm_add_le hp F P
    (aestronglyMeasurable_vecEuclideanNorm_of_coord hF) hPmag
    (aestronglyMeasurable_vecEuclideanNorm_of_coord fun i => (hF i).add (hPcoord i))
  let c : NNReal := ⟨delta, hdelta⟩
  have hc : (c : ENNReal) = ENNReal.ofReal delta := by
    rw [ENNReal.coe_nnreal_eq]
    rfl
  have hpert : eLpNorm (fun x => vecEuclideanNorm (P x)) p μ ≤
      ENNReal.ofReal delta * eLpNorm (fun x => vecEuclideanNorm (g x)) p μ := by
    have hscale := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'
      (μ := μ) (f := fun x => vecEuclideanNorm (P x))
      (g := fun x => vecEuclideanNorm (g x)) (c := c) (p := p) hPmag (by
        filter_upwards [hclose] with x hx
        simpa only [Real.enorm_eq_ofReal (vecEuclideanNorm_nonneg _), hc,
          ENNReal.ofReal_mul hdelta] using
          ENNReal.ofReal_le_ofReal (hx (g x)))
    simpa only [ENNReal.smul_def, smul_eq_mul, hc] using! hscale
  exact htriangle.trans (add_le_add_right hpert _)

end PDE
