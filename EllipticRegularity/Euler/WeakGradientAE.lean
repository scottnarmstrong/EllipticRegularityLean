module

public import EllipticRegularity.Euler.WeakGradientSlice

/-!
# `W^{1,p}` regularity of a.e. time slices of a bounded-vorticity weak Euler solution

`ae_exists_weak_gradient` feeds the bundles `ae_mollify_slice_div` / `ae_mollify_slice_curl` of `PDEFoundation.Euler.MollifyBundle`
into `exists_torus_weak_gradient`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PDE

/-- For a.e. `t`, `v(·,t)` has a weak gradient `G ∈ L²(cube)` with `‖G‖_{L^p(cube)} ≤ K p M`
for every `p ≥ 2` (`K` absolute); moreover `∇(v^{aₙ}(·,t)) → G` in `L²(cube)` for the given mollification
scales `aₙ → 0`. -/
theorem ae_exists_weak_gradient :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (T : ℝ), 0 < T → ∀ (v : Vec 2 × ℝ → Vec 2) (ω : Vec 2 × ℝ → ℝ) (B M : ℝ)
      (a : ℕ → ℝ),
      AEStronglyMeasurable v (eulerMeasure T) →
      (∀ t, IsTorusPeriodic (fun x => v (x, t))) →
      (∀ᵐ z ∂(eulerMeasure T), vecNormSq (v z) ≤ B) →
      (∀ ψ : Vec 2 × ℝ → ℝ, IsPeriodicSmooth ψ → VanishesOutsideInterior T ψ →
        ∫ z, vecDot (v z) (fun j => fderiv ℝ ψ z (basisVec j, 0)) ∂(eulerMeasure T) = 0) →
      AEStronglyMeasurable ω (eulerMeasure T) → (∀ᵐ z ∂(eulerMeasure T), |ω z| ≤ M) →
      (∀ ψ : Vec 2 × ℝ → ℝ, IsPeriodicSmooth ψ → VanishesOutsideInterior T ψ →
        ∫ z, ω z * ψ z ∂(eulerMeasure T) =
          ∫ z, (v z 0 * fderiv ℝ ψ z (basisVec 1, 0) - v z 1 * fderiv ℝ ψ z (basisVec 0, 0))
            ∂(eulerMeasure T)) →
      (∀ n, 0 < a n) → (∀ n, a n ≤ 1) → Tendsto a atTop (𝓝 0) →
      ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)),
        ∃ G : Vec 2 → Fin 2 → Fin 2 → ℝ,
          (∀ i j, MemLp (fun x => G x i j) 2 (volume.restrict torusCube)) ∧
          Tendsto (fun n => eLpNorm
            (fun x => gradMat (mollifyVec (a n) (fun y => v (y, t))) x - G x) 2
            (volume.restrict torusCube)) atTop (𝓝 0) ∧
          IsTorusWeakGradient (fun x => v (x, t)) G ∧
          ∀ p : ℝ, 2 ≤ p →
            MemLp (fun x => matFrobNorm (G x)) (ENNReal.ofReal p) (volume.restrict torusCube) ∧
            eLpNorm (fun x => matFrobNorm (G x)) (ENNReal.ofReal p) (volume.restrict torusCube) ≤
              ENNReal.ofReal (K * p * M) := by
  obtain ⟨K, hK, hslice⟩ := exists_torus_weak_gradient
  refine ⟨K, hK, ?_⟩
  intro T hT v ω B M a hmeas hper hB hdiv hωm hωM hcurl ha ha1 ha0
  have prod_eq : eulerMeasure T =
      (volume.restrict torusCube).prod (volume.restrict (Icc (0 : ℝ) T)) := eulerMeasure_eq_prod T
  have hbt : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), ∀ᵐ x ∂(volume.restrict torusCube),
      vecNormSq (v (x, t)) ≤ B := by
    rw [prod_eq] at hB
    have h1 := (Measure.measurePreserving_swap (μ := volume.restrict (Icc (0 : ℝ) T))
      (ν := volume.restrict torusCube)).quasiMeasurePreserving.ae hB
    exact Measure.ae_ae_of_ae_prod h1
  have hωbt : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), ∀ᵐ x ∂(volume.restrict torusCube),
      |ω (x, t)| ≤ M := by
    rw [prod_eq] at hωM
    have h1 := (Measure.measurePreserving_swap (μ := volume.restrict (Icc (0 : ℝ) T))
      (ν := volume.restrict torusCube)).quasiMeasurePreserving.ae hωM
    exact Measure.ae_ae_of_ae_prod h1
  have hvmt : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)),
      AEStronglyMeasurable (fun x => v (x, t)) (volume.restrict torusCube) := by
    rw [prod_eq] at hmeas
    exact (hmeas.comp_quasiMeasurePreserving (Measure.measurePreserving_swap
      (μ := volume.restrict (Icc (0 : ℝ) T)) (ν := volume.restrict torusCube)).quasiMeasurePreserving).prodMk_left
  have hωmt : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)),
      AEStronglyMeasurable (fun x => ω (x, t)) (volume.restrict torusCube) := by
    rw [prod_eq] at hωm
    exact (hωm.comp_quasiMeasurePreserving (Measure.measurePreserving_swap
      (μ := volume.restrict (Icc (0 : ℝ) T)) (ν := volume.restrict torusCube)).quasiMeasurePreserving).prodMk_left
  filter_upwards [ae_mollify_slice_div hT hmeas hper hB hdiv,
    ae_mollify_slice_curl hT hmeas hper hB hωm hωM hcurl, hbt, hωbt, hvmt, hωmt]
    with t hd hc hb hωb hvm hωm'
  have hvL2 : ∀ i, MemLp (fun x => v (x, t) i) 2 (volume.restrict torusCube) := fun i =>
    MemLp.of_bound ((continuous_apply i).comp_aestronglyMeasurable hvm) (Real.sqrt B)
      (hb.mono fun x hx => by simpa [Real.norm_eq_abs] using abs_coord_le_sqrt hx i)
  have hωL2' : MemLp (fun x => ω (x, t)) 2 (volume.restrict torusCube) :=
    MemLp.of_bound hωm' M (hωb.mono fun x hx => by simpa [Real.norm_eq_abs] using hx)
  have hωL2 : MemLp (periodExt fun y => ω (y, t)) 2 (volume.restrict torusCube) :=
    MemLp.ae_eq ((ae_periodExt_eq (fun y => ω (y, t))).mono fun x hx => hx.symm) hωL2'
  exact hslice (fun x => v (x, t)) (periodExt fun y => ω (y, t)) M a (hper t) hvL2
    (isTorusPeriodic_periodExt _) hωL2 ha ha1 ha0
    (fun n => ⟨(hd (a n) (ha n)).1, (hd (a n) (ha n)).2.1, (hd (a n) (ha n)).2.2.1⟩)
    (fun n => hc (a n) (ha n))

end PDE
