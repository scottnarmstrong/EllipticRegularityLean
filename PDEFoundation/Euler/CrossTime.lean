module

public import PDEFoundation.Euler.CrossLimit
public import PDEFoundation.Euler.TimeRepresentation

/-!
# The cross-term identity in time-slice form

`sliceDot u v τ = ∑ᵢ ∫_cube uᵢ(x,τ) vᵢ(x,τ) dx` and
`sliceR u v G τ = ∑ᵢⱼ ∫_cube (uⱼ - vⱼ) uᵢ Gᵢⱼ (x,τ) dx`.  From `cross_identity` and
`ae_eq_of_weak_derivative`: for a.e. `t`, `sliceDot u v t = ‖v₀‖² + ∫₀ᵗ sliceR u v G`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace PDE

noncomputable def sliceDot (u v : Vec 2 × ℝ → Vec 2) (τ : ℝ) : ℝ :=
  ∑ i, ∫ x in torusCube, u (x, τ) i * v (x, τ) i

noncomputable def sliceR (u v : Vec 2 × ℝ → Vec 2) (G : Vec 2 × ℝ → Fin 2 → Fin 2 → ℝ) (τ : ℝ) : ℝ :=
  ∑ i, ∑ j, ∫ x in torusCube, ((u (x, τ) j - v (x, τ) j) * u (x, τ) i) * G (x, τ) i j

section

variable {T B1 B2 : ℝ} {v₀ : Vec 2 → Vec 2} {u v : Vec 2 × ℝ → Vec 2}
  {G : Vec 2 × ℝ → Fin 2 → Fin 2 → ℝ}

theorem integrable_sliceDot (hbu : EulerBdd T B1 u) (hbv : EulerBdd T B2 v) :
    IntegrableOn (sliceDot u v) (Icc (0 : ℝ) T) := by
  have hint : ∀ i, Integrable (fun z => u z i * v z i) (eulerMeasure T) := fun i =>
    integrable_of_bdd_E ((hbu.coord_aesm i).mul (hbv.coord_aesm i)) (C := Real.sqrt B1 * Real.sqrt B2)
      ((hbu.abs_coord_le i).and (hbv.abs_coord_le i) |>.mono fun z ⟨h1, h2⟩ => by
        rw [abs_mul]; exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1))
  unfold sliceDot
  refine integrable_finsetSum _ fun i _ => ?_
  have := integrable_time_slice (hint i) (g := fun _ => (1 : ℝ)) continuous_const
  simpa using this

theorem integrable_sliceR (hbu : EulerBdd T B1 u) (hbv : EulerBdd T B2 v) (hG : SpaceTimeGrad T B2 v G) :
    IntegrableOn (sliceR u v G) (Icc (0 : ℝ) T) := by
  have hint : ∀ i j, Integrable (fun z => ((u z j - v z j) * u z i) * G z i j) (eulerMeasure T) := by
    intro i j
    have hG1 : Integrable (fun z => G z i j) (eulerMeasure T) := (hG.memLp i j).integrable (by norm_num)
    refine hG1.bdd_mul (((hbu.coord_aesm j).sub (hbv.coord_aesm j)).mul (hbu.coord_aesm i))
      (c := (Real.sqrt B1 + Real.sqrt B2) * Real.sqrt B1) ?_
    filter_upwards [hbu.abs_coord_le i, hbu.abs_coord_le j, hbv.abs_coord_le j] with z h1 h2 h3
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul ?_ h1 (abs_nonneg _) (by positivity)
    exact (abs_sub _ _).trans (add_le_add h2 h3)
  unfold sliceR
  refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
  have := integrable_time_slice (hint i j) (g := fun _ => (1 : ℝ)) continuous_const
  simpa using this

theorem cross_identity_time (hT : 0 < T) (hu : IsEulerWeakSolutionWithDatum T v₀ u)
    (hv : IsEulerWeakSolutionWithDatum T v₀ v) (hbu : EulerBdd T B1 u) (hbv : EulerBdd T B2 v)
    (hG : SpaceTimeGrad T B2 v G) :
    ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)),
      sliceDot u v t = (∑ i, ∫ x in torusCube, v₀ x i * v₀ x i) + ∫ s in Icc 0 t, sliceR u v G s := by
  refine ae_eq_of_weak_derivative (integrable_sliceDot hbu hbv) (integrable_sliceR hbu hbv hG) ?_
  intro χ hχ b hbT hχb
  have hχc : Continuous χ := hχ.continuous
  have hχ'c : Continuous (deriv χ) := continuous_deriv_of_contDiff_top hχ
  have h := cross_identity hT hu hv hbu hbv hG hχ hbT hχb
  have hint1 : ∀ i, Integrable (fun z => u z i * v z i) (eulerMeasure T) := fun i =>
    integrable_of_bdd_E ((hbu.coord_aesm i).mul (hbv.coord_aesm i)) (C := Real.sqrt B1 * Real.sqrt B2)
      ((hbu.abs_coord_le i).and (hbv.abs_coord_le i) |>.mono fun z ⟨h1, h2⟩ => by
        rw [abs_mul]; exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1))
  have hint2 : ∀ i j, Integrable (fun z => ((u z j - v z j) * u z i) * G z i j) (eulerMeasure T) := by
    intro i j
    have hG1 : Integrable (fun z => G z i j) (eulerMeasure T) := (hG.memLp i j).integrable (by norm_num)
    refine hG1.bdd_mul (((hbu.coord_aesm j).sub (hbv.coord_aesm j)).mul (hbu.coord_aesm i))
      (c := (Real.sqrt B1 + Real.sqrt B2) * Real.sqrt B1) ?_
    filter_upwards [hbu.abs_coord_le i, hbu.abs_coord_le j, hbv.abs_coord_le j] with z h1 h2 h3
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul ?_ h1 (abs_nonneg _) (by positivity)
    exact (abs_sub _ _).trans (add_le_add h2 h3)
  have e1 : ∫ τ in Icc (0 : ℝ) T, deriv χ τ * sliceDot u v τ =
      ∑ i, ∫ z, deriv χ z.2 * (u z i * v z i) ∂(eulerMeasure T) :=
    time_slice_sum (Finset.univ : Finset (Fin 2)) (h := fun i z => u z i * v z i) (fun i _ => hint1 i) hχ'c
  have e2 : ∫ τ in Icc (0 : ℝ) T, χ τ * sliceR u v G τ =
      ∑ i, ∑ j, ∫ z, χ z.2 * (((u z j - v z j) * u z i) * G z i j) ∂(eulerMeasure T) := by
    have := time_slice_sum (Finset.univ : Finset (Fin 2 × Fin 2))
      (h := fun p z => ((u z p.2 - v z p.2) * u z p.1) * G z p.1 p.2) (fun p _ => hint2 p.1 p.2) hχc
    simp only [Fintype.sum_prod_type] at this
    unfold sliceR
    exact this
  rw [e1, e2]
  exact h

end

end PDE
