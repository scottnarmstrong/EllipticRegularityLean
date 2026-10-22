module

public import PDEFoundation.Euler.TimeSums
public import PDEFoundation.Euler.MollifiedSlices

/-!
# The bilinear time forms of the cross-term identity

For two a.e. bounded space-time fields `u`, `v` (periodic in `x`) and a mollification scale `a`:
* `crossF a u v τ σ = ∑ᵢ ∫_cube uᵢ(x,τ) vᵢᵃ(x,σ) dx`,
* `crossH a u v τ σ = ∑ᵢⱼ ∫_cube (uᵢuⱼ)(x,τ) ∂ⱼvᵢᵃ(x,σ) dx`,
* `crossK a u v τ σ = ∑ᵢⱼ ∫_cube (vᵢvⱼ)(x,σ) ∂ⱼuᵢᵃ(x,τ) dx`,
and their diagonal limits under the time mollifier `η_n`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace PDE

/-- Standing facts about a bounded space-time field. -/
structure EulerBdd (T B : ℝ) (w : Vec 2 × ℝ → Vec 2) : Prop where
  meas : AEStronglyMeasurable w (eulerMeasure T)
  per : ∀ t, IsTorusPeriodic (fun x => w (x, t))
  bdd : ∀ᵐ z ∂(eulerMeasure T), vecNormSq (w z) ≤ B
  nonneg : 0 ≤ B

noncomputable def crossF (a : ℝ) (u v : Vec 2 × ℝ → Vec 2) (τ σ : ℝ) : ℝ :=
  ∑ i, ∫ x in torusCube, u (x, τ) i * mollifyVecST a v (x, σ) i

noncomputable def crossH (a : ℝ) (u v : Vec 2 × ℝ → Vec 2) (τ σ : ℝ) : ℝ :=
  ∑ i, ∑ j, ∫ x in torusCube, (u (x, τ) i * u (x, τ) j) * gradMollST a v (x, σ) i j

noncomputable def crossK (a : ℝ) (u v : Vec 2 × ℝ → Vec 2) (τ σ : ℝ) : ℝ :=
  ∑ i, ∑ j, ∫ x in torusCube, (v (x, σ) i * v (x, σ) j) * gradMollST a u (x, τ) i j

noncomputable def crossD (a : ℝ) (v₀ : Vec 2 → Vec 2) (w : Vec 2 × ℝ → Vec 2) (σ : ℝ) : ℝ :=
  ∑ i, ∫ x in torusCube, v₀ x i * mollifyVecST a w (x, σ) i

namespace EulerBdd

variable {T B : ℝ} {w : Vec 2 × ℝ → Vec 2}

theorem coord_aesm (h : EulerBdd T B w) (i : Fin 2) :
    AEStronglyMeasurable (fun z => w z i) (eulerMeasure T) :=
  (continuous_apply i).comp_aestronglyMeasurable h.meas

theorem abs_coord_le (h : EulerBdd T B w) (i : Fin 2) :
    ∀ᵐ z ∂(eulerMeasure T), |w z i| ≤ Real.sqrt B :=
  h.bdd.mono fun _ hz => abs_coord_le_sqrt hz i

theorem prod_aesm (h : EulerBdd T B w) (i j : Fin 2) :
    AEStronglyMeasurable (fun z => w z i * w z j) (eulerMeasure T) :=
  (h.coord_aesm i).mul (h.coord_aesm j)

theorem abs_prod_le (h : EulerBdd T B w) (i j : Fin 2) :
    ∀ᵐ z ∂(eulerMeasure T), |w z i * w z j| ≤ B := by
  filter_upwards [h.abs_coord_le i, h.abs_coord_le j] with z h1 h2
  rw [abs_mul]
  calc |w z i| * |w z j| ≤ Real.sqrt B * Real.sqrt B :=
        mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
    _ = B := Real.mul_self_sqrt h.nonneg

theorem mol_aesm (h : EulerBdd T B w) (a : ℝ) (i : Fin 2) :
    AEStronglyMeasurable (fun z => mollifyVecST a w z i) (eulerMeasure T) :=
  aestronglyMeasurable_mollifyVecST h.meas h.per a i

theorem abs_mol_le (h : EulerBdd T B w) {a : ℝ} (ha : 0 < a) (i : Fin 2) :
    ∀ᵐ z ∂(eulerMeasure T), |mollifyVecST a w z i| ≤ Real.sqrt B :=
  ae_abs_mollifyVecST_le h.meas h.per h.bdd ha i

theorem grad_aesm (h : EulerBdd T B w) {a : ℝ} (ha : 0 < a) (i j : Fin 2) :
    AEStronglyMeasurable (fun z => gradMollST a w z i j) (eulerMeasure T) :=
  aestronglyMeasurable_gradMollST h.meas h.per h.bdd ha i j

theorem abs_grad_le (h : EulerBdd T B w) {a : ℝ} (ha : 0 < a) (i j : Fin 2) :
    ∀ᵐ z ∂(eulerMeasure T), |gradMollST a w z i j| ≤ pdMolKNorm a j * Real.sqrt B :=
  ae_abs_gradMollST_le h.meas h.per h.bdd ha i j

end EulerBdd

theorem pdMolKNorm_nonneg (a : ℝ) (j : Fin 2) : 0 ≤ pdMolKNorm a j :=
  integral_nonneg fun _ => abs_nonneg _

section Limits

variable {T B1 B2 : ℝ} {u v : Vec 2 × ℝ → Vec 2}

theorem tendsto_crossF (hu : EulerBdd T B1 u) (hv : EulerBdd T B2 v) {a : ℝ} (ha : 0 < a)
    {g : ℝ → ℝ} (hg : Continuous g) :
    Tendsto (fun n : ℕ => ∫ τ, g τ * ∫ σ, etaK n (σ - τ) * crossF a u v τ σ
        ∂(volume.restrict (Icc (0 : ℝ) T)) ∂(volume.restrict (Icc (0 : ℝ) T))) atTop
      (𝓝 (∫ τ, g τ * crossF a u v τ τ ∂(volume.restrict (Icc (0 : ℝ) T)))) := by
  have h := tendsto_time_mollify_sum (μ := volume.restrict torusCube) (T := T) (Finset.univ : Finset (Fin 2))
    (a := fun i p => u p i) (b := fun i p => mollifyVecST a v p i)
    (A := fun _ => Real.sqrt B1) (B := fun _ => Real.sqrt B2)
    (fun _ _ => Real.sqrt_nonneg _)
    (fun i _ => by rw [← eulerMeasure_eq_prod]; exact hu.coord_aesm i)
    (fun i _ => by rw [← eulerMeasure_eq_prod]; exact hv.mol_aesm a i)
    (fun i _ => by rw [← eulerMeasure_eq_prod]; exact hu.abs_coord_le i)
    (fun i _ => by rw [← eulerMeasure_eq_prod]; exact hv.abs_mol_le ha i)
    (fun _ _ => Real.sqrt_nonneg _) hg
  exact h

theorem crossH_eq_sum (a : ℝ) (u v : Vec 2 × ℝ → Vec 2) (τ σ : ℝ) :
    crossH a u v τ σ = ∑ p : Fin 2 × Fin 2, ∫ x in torusCube,
      (u (x, τ) p.1 * u (x, τ) p.2) * gradMollST a v (x, σ) p.1 p.2 := by
  simp only [crossH, Fintype.sum_prod_type]

theorem crossK_eq_sum (a : ℝ) (u v : Vec 2 × ℝ → Vec 2) (τ σ : ℝ) :
    crossK a u v τ σ = ∑ p : Fin 2 × Fin 2, ∫ x in torusCube,
      (v (x, σ) p.1 * v (x, σ) p.2) * gradMollST a u (x, τ) p.1 p.2 := by
  simp only [crossK, Fintype.sum_prod_type]

theorem tendsto_crossH (hu : EulerBdd T B1 u) (hv : EulerBdd T B2 v) {a : ℝ} (ha : 0 < a)
    {g : ℝ → ℝ} (hg : Continuous g) :
    Tendsto (fun n : ℕ => ∫ τ, g τ * ∫ σ, etaK n (σ - τ) * crossH a u v τ σ
        ∂(volume.restrict (Icc (0 : ℝ) T)) ∂(volume.restrict (Icc (0 : ℝ) T))) atTop
      (𝓝 (∫ τ, g τ * crossH a u v τ τ ∂(volume.restrict (Icc (0 : ℝ) T)))) := by
  have h := tendsto_time_mollify_sum (μ := volume.restrict torusCube) (T := T)
    (Finset.univ : Finset (Fin 2 × Fin 2))
    (a := fun p z => u z p.1 * u z p.2) (b := fun p z => gradMollST a v z p.1 p.2)
    (A := fun _ => B1) (B := fun p => pdMolKNorm a p.2 * Real.sqrt B2)
    (fun _ _ => hu.nonneg)
    (fun p _ => by rw [← eulerMeasure_eq_prod]; exact hu.prod_aesm p.1 p.2)
    (fun p _ => by rw [← eulerMeasure_eq_prod]; exact hv.grad_aesm ha p.1 p.2)
    (fun p _ => by rw [← eulerMeasure_eq_prod]; exact hu.abs_prod_le p.1 p.2)
    (fun p _ => by rw [← eulerMeasure_eq_prod]; exact hv.abs_grad_le ha p.1 p.2)
    (fun p _ => mul_nonneg (pdMolKNorm_nonneg a p.2) (Real.sqrt_nonneg _)) hg
  simp only [crossH_eq_sum]
  exact h

theorem tendsto_crossK (hu : EulerBdd T B1 u) (hv : EulerBdd T B2 v) {a : ℝ} (ha : 0 < a)
    {g : ℝ → ℝ} (hg : Continuous g) :
    Tendsto (fun n : ℕ => ∫ τ, g τ * ∫ σ, etaK n (σ - τ) * crossK a u v τ σ
        ∂(volume.restrict (Icc (0 : ℝ) T)) ∂(volume.restrict (Icc (0 : ℝ) T))) atTop
      (𝓝 (∫ τ, g τ * crossK a u v τ τ ∂(volume.restrict (Icc (0 : ℝ) T)))) := by
  have h := tendsto_time_mollify_sum (μ := volume.restrict torusCube) (T := T)
    (Finset.univ : Finset (Fin 2 × Fin 2))
    (a := fun p z => gradMollST a u z p.1 p.2) (b := fun p z => v z p.1 * v z p.2)
    (A := fun p => pdMolKNorm a p.2 * Real.sqrt B1) (B := fun _ => B2)
    (fun p _ => mul_nonneg (pdMolKNorm_nonneg a p.2) (Real.sqrt_nonneg _))
    (fun p _ => by rw [← eulerMeasure_eq_prod]; exact hu.grad_aesm ha p.1 p.2)
    (fun p _ => by rw [← eulerMeasure_eq_prod]; exact hv.prod_aesm p.1 p.2)
    (fun p _ => by rw [← eulerMeasure_eq_prod]; exact hu.abs_grad_le ha p.1 p.2)
    (fun p _ => by rw [← eulerMeasure_eq_prod]; exact hv.abs_prod_le p.1 p.2)
    (fun _ _ => hv.nonneg) hg
  simp only [crossK_eq_sum]
  have e : ∀ τ σ : ℝ, ∀ p : Fin 2 × Fin 2, ∫ x in torusCube, (v (x, σ) p.1 * v (x, σ) p.2) *
      gradMollST a u (x, τ) p.1 p.2 = ∫ x in torusCube, gradMollST a u (x, τ) p.1 p.2 *
      (v (x, σ) p.1 * v (x, σ) p.2) := fun τ σ p => by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring
  simp only [e]
  exact h

end Limits

end PDE
