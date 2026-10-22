module

public import PDEFoundation.Analysis.HilbertDictionary
public import PDEFoundation.Sobolev.Trace.Model.Defs
public import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Polar coordinates for radial `lintegral`s on `Vec n`

For `n ≥ 1` there is a finite constant `c` with
`∫⁻ k, f (|k|) dk = c ∫⁻_{(0,∞)} r^{n-1} f(r) dr` for every measurable `f : ℝ → [0, ∞]`, where
`|k|` is the Euclidean length `vecEuclideanNorm`.  This is transported from the Hilbert
realisation `HilbertVec n`.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Metric
open scoped ENNReal

/-- Polar coordinates on the Hilbert realisation, `lintegral` form. -/
theorem lintegral_comp_norm_hilbert {n : ℕ} [NeZero n] (f : ℝ → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ x : HilbertVec n, f ‖x‖ =
      (volume : Measure (HilbertVec n)).toSphere univ *
        ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (n - 1)) * f r := by
  classical
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  have : Nontrivial (HilbertVec n) := inferInstance
  have hdim : Module.finrank ℝ (HilbertVec n) = n := by
    calc Module.finrank ℝ (HilbertVec n) = Module.finrank ℝ (Fin n → ℝ) :=
          (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).finrank_eq
      _ = n := by simp
  have hmp := (volume : Measure (HilbertVec n)).measurePreserving_homeomorphUnitSphereProd
  have h1 : ∫⁻ x : HilbertVec n, f ‖x‖ =
      ∫⁻ x : ({0}ᶜ : Set (HilbertVec n)), f ‖(x : HilbertVec n)‖
        ∂(Measure.comap Subtype.val volume) := by
    rw [lintegral_subtype_comap (measurableSet_singleton (0 : HilbertVec n)).compl
      (fun x => f ‖x‖), restrict_compl_singleton]
  have h2 := hmp.lintegral_comp_emb (Homeomorph.measurableEmbedding _)
    (fun q : sphere (0 : HilbertVec n) 1 × Ioi (0 : ℝ) => f (q.2 : ℝ))
  simp only [homeomorphUnitSphereProd_apply_snd_coe] at h2
  rw [h1, h2, lintegral_prod _ (by fun_prop : Measurable _).aemeasurable]
  simp only [lintegral_const]
  rw [mul_comm, hdim, Measure.volumeIoiPow,
    lintegral_withDensity_eq_lintegral_mul _
      (f := fun r : Ioi (0 : ℝ) => ENNReal.ofReal ((r : ℝ) ^ (n - 1)))
      ((measurable_subtype_coe.pow_const _).ennreal_ofReal)
      (g := fun r : Ioi (0 : ℝ) => f r) (hf.comp measurable_subtype_coe)]
  congr 1
  have := lintegral_subtype_comap (μ := (volume : Measure ℝ)) (measurableSet_Ioi (a := (0 : ℝ)))
    (fun r => ENNReal.ofReal (r ^ (n - 1)) * f r)
  simpa using this

/-- Polar coordinates for radial `lintegral`s on `Vec n` (`n ≥ 1`), with a finite constant. -/
theorem exists_lintegral_comp_vecEuclideanNorm (n : ℕ) [NeZero n] :
    ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ f : ℝ → ℝ≥0∞, Measurable f →
      ∫⁻ k : Vec n, f (vecEuclideanNorm k) =
        c * ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (r ^ (n - 1)) * f r := by
  refine ⟨(volume : Measure (HilbertVec n)).toSphere univ, measure_ne_top _ _, fun f hf => ?_⟩
  rw [← lintegral_comp_norm_hilbert f hf]
  have h := (PDE.Internal.measurePreserving_toHilbert (d := n)).lintegral_comp_emb
    (PDE.Internal.toHilbert (d := n)).toHomeomorph.measurableEmbedding (fun x => f ‖x‖)
  rw [← h]
  refine lintegral_congr (fun k => ?_)
  simp only [PDE.Internal.toHilbert_apply, ← Vec.vecEuclideanNorm_eq_norm_toHilbertVec]

end PDE.TraceLane
