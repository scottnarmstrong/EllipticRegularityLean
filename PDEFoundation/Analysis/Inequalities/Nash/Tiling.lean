module

public import PDEFoundation.Geometry.AxisCube
public import PDEFoundation.Measure.CubeVolume
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Tiling of `ℝ^d` by open axis cubes

The open cubes `ℓ (k + (0,1)^d)`, `k ∈ ℤ^d`, are pairwise disjoint and cover `ℝ^d` up to a
null set (the coordinate hyperplanes at multiples of `ℓ`).  Hence integrals of integrable
functions over `ℝ^d` are the sums of their integrals over the cubes.
-/

@[expose] public section

namespace PDE.Nash

open MeasureTheory

variable {d : ℕ}

/-- The open cube of side `ℓ` indexed by `k ∈ ℤ^d`. -/
def tileCube (ℓ : ℝ) (k : Fin d → ℤ) : Set (Vec d) :=
  axisCube (fun i => ℓ * (k i : ℝ)) ℓ

theorem tileCube_disjoint {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Pairwise (Function.onFun Disjoint (tileCube (d := d) ℓ)) := by
  intro k k' hkk'
  rw [Function.onFun, Set.disjoint_left]
  intro x hx hx'
  apply hkk'
  funext i
  have h1 := hx i (Set.mem_univ i)
  have h2 := hx' i (Set.mem_univ i)
  simp only [Set.mem_Ioo] at h1 h2
  have a1 : (k i : ℝ) < k' i + 1 := by
    have : ℓ * (k i : ℝ) < ℓ * (k' i + 1) := by nlinarith [h1.1, h2.2]
    exact lt_of_mul_lt_mul_left this hℓ.le
  have a2 : (k' i : ℝ) < k i + 1 := by
    have : ℓ * (k' i : ℝ) < ℓ * (k i + 1) := by nlinarith [h2.1, h1.2]
    exact lt_of_mul_lt_mul_left this hℓ.le
  have b1 : k i < k' i + 1 := by exact_mod_cast a1
  have b2 : k' i < k i + 1 := by exact_mod_cast a2
  omega

theorem volume_hyperplane_eq_zero (i : Fin d) (c : ℝ) :
    volume {x : Vec d | x i = c} = 0 := by
  have : {x : Vec d | x i = c} =
      Set.pi Set.univ (Function.update (fun _ : Fin d => (Set.univ : Set ℝ)) i {c}) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
    constructor
    · intro h j
      by_cases hj : j = i
      · subst hj; simp [h]
      · simp [Function.update_of_ne hj]
    · intro h
      simpa using h i
  rw [this, volume_pi_pi]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

theorem tileCube_iUnion_ae {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (⋃ k : Fin d → ℤ, tileCube ℓ k) =ᵐ[volume] (Set.univ : Set (Vec d)) := by
  rw [ae_eq_univ]
  have hsub : (⋃ k : Fin d → ℤ, tileCube ℓ k)ᶜ ⊆
      ⋃ (i : Fin d) (m : ℤ), {x : Vec d | x i = ℓ * m} := by
    intro x hx
    by_contra hcon
    apply hx
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, not_exists] at hcon ⊢
    refine ⟨fun i => ⌊x i / ℓ⌋, fun i _ => ?_⟩
    have h1 := Int.floor_le (x i / ℓ)
    have h2 := Int.lt_floor_add_one (x i / ℓ)
    have hne : x i ≠ ℓ * (⌊x i / ℓ⌋ : ℤ) := hcon i _
    have h1' : ℓ * (⌊x i / ℓ⌋ : ℝ) ≤ x i := by
      have := mul_le_mul_of_nonneg_left h1 hℓ.le
      rwa [mul_div_cancel₀ _ hℓ.ne'] at this
    have h2' : x i < ℓ * ((⌊x i / ℓ⌋ : ℝ) + 1) := by
      have := mul_lt_mul_of_pos_left h2 hℓ
      rwa [mul_div_cancel₀ _ hℓ.ne'] at this
    exact ⟨lt_of_le_of_ne h1' (Ne.symm hne), by simpa [mul_add] using h2'⟩
  refine measure_mono_null hsub (measure_iUnion_null fun i => measure_iUnion_null fun m => ?_)
  exact volume_hyperplane_eq_zero i _

/-- Integrals over `ℝ^d` are the sums of the integrals over the tile cubes. -/
theorem hasSum_setIntegral_tileCube {ℓ : ℝ} (hℓ : 0 < ℓ) {g : Vec d → ℝ}
    (hg : Integrable g volume) :
    HasSum (fun k : Fin d → ℤ => ∫ x in tileCube ℓ k, g x) (∫ x, g x) := by
  have h := hasSum_integral_iUnion (μ := (volume : Measure (Vec d)))
    (s := fun k : Fin d → ℤ => tileCube ℓ k) (f := g)
    (fun k => (isOpen_axisCube _ _).measurableSet) (tileCube_disjoint hℓ) hg.integrableOn
  rwa [Measure.restrict_congr_set (tileCube_iUnion_ae hℓ), Measure.restrict_univ] at h

end PDE.Nash
