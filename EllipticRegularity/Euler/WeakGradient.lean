module

public import EllipticRegularity.Euler.PeriodicCZ
public import PDEFoundation.Euler.WeakGradLimit

/-!
# `W^{1,p}` regularity of `v₂` from the uniform periodic CZ bound

If smooth periodic divergence-free fields `uₙ` have vorticities bounded by `M`, converging in `L²(cube)`,
and `uₙ → v` in `L²(cube)`, then `v` has a weak gradient `G ∈ L²(cube)` with
`‖G‖_{L^p(cube)} ≤ K p M` for every `p ≥ 2` (`K` the absolute constant of the periodic CZ estimate), and
`∇uₙ → G` strongly in `L²(cube)`.  The `L^p` bound passes to the limit by lower semicontinuity of the norm
along an a.e. convergent subsequence.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PDE

theorem torusGradNorm_eq_matFrobNorm (u : Vec 2 → Vec 2) (x : Vec 2) :
    torusGradNorm u x = matFrobNorm (gradMat u x) := rfl

/-- **Periodic `W^{1,p}` bound for the limit.**  The constant `K` is absolute. -/
theorem exists_weak_gradient_of_smooth_seq :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (u : ℕ → Vec 2 → Vec 2) (v : Vec 2 → Vec 2) (ω : Vec 2 → ℝ) (M : ℝ),
      (∀ n i, ContDiff ℝ (⊤ : ℕ∞) (fun x => u n x i)) → (∀ n, IsTorusPeriodic (u n)) →
      (∀ n x, torusDiv (u n) x = 0) → (∀ n x, |torusCurl (u n) x| ≤ M) →
      Tendsto (fun n => eLpNorm (fun x => torusCurl (u n) x - ω x) 2 (volume.restrict torusCube))
        atTop (𝓝 0) →
      (∀ i, MemLp (fun x => v x i) 2 (volume.restrict torusCube)) →
      (∀ i, Tendsto (fun n => eLpNorm (fun x => u n x i - v x i) 2 (volume.restrict torusCube))
        atTop (𝓝 0)) →
      ∃ G : Vec 2 → Fin 2 → Fin 2 → ℝ,
        (∀ i j, MemLp (fun x => G x i j) 2 (volume.restrict torusCube)) ∧
        Tendsto (fun n => eLpNorm (fun x => gradMat (u n) x - G x) 2 (volume.restrict torusCube))
          atTop (𝓝 0) ∧
        (∀ i j (ψ : Vec 2 → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → IsTorusPeriodic ψ →
          ∫ x in torusCube, v x i * pd j ψ x = -∫ x in torusCube, G x i j * ψ x) ∧
        ∀ p : ℝ, 2 ≤ p →
          MemLp (fun x => matFrobNorm (G x)) (ENNReal.ofReal p) (volume.restrict torusCube) ∧
          eLpNorm (fun x => matFrobNorm (G x)) (ENNReal.ofReal p) (volume.restrict torusCube) ≤
            ENNReal.ofReal (K * p * M) := by
  obtain ⟨K, hK, hcz⟩ := exists_torus_cz_eLpNorm
  refine ⟨K, hK, ?_⟩
  intro u v ω M hu hup hdiv hM hωconv hv hvconv
  obtain ⟨G, hG, hGc⟩ := exists_gradMat_limit hu hup hdiv hωconv
  refine ⟨G, memLp_apply_of_memLp_gradMat hG |> fun h i j => h i j, hGc,
    fun i j ψ hψ hψp => weak_gradient_of_tendsto hu hup hv hvconv hG hGc i j hψ hψp, ?_⟩
  intro p hp
  obtain ⟨ns, -, hae⟩ := (tendstoInMeasure_of_tendsto_eLpNorm (f := fun n => gradMat (u n))
    (by norm_num) hGc).exists_seq_tendsto_ae
  have hmeas : AEStronglyMeasurable (fun x => matFrobNorm (G x)) (volume.restrict torusCube) :=
    continuous_matFrobNorm.comp_aestronglyMeasurable hG.aestronglyMeasurable
  have hlim := Lp.eLpNorm_lim_le_liminf_eLpNorm (p := ENNReal.ofReal p)
    (f := fun k x => matFrobNorm (gradMat (u (ns k)) x))
    (fun k => (continuous_matFrobNorm.comp (continuous_gradMat (hu (ns k)))).aestronglyMeasurable)
    (fun x => matFrobNorm (G x)) hmeas
    (hae.mono fun x hx => (continuous_matFrobNorm.tendsto _).comp hx)
  have hb : ∀ k, eLpNorm (fun x => matFrobNorm (gradMat (u (ns k)) x)) (ENNReal.ofReal p)
      (volume.restrict torusCube) ≤ ENNReal.ofReal (K * p * M) := fun k =>
    (hcz p hp (u (ns k)) M (hu (ns k)) (hup (ns k)) (hdiv (ns k)) (hM (ns k))).2
  have hle : eLpNorm (fun x => matFrobNorm (G x)) (ENNReal.ofReal p) (volume.restrict torusCube) ≤
      ENNReal.ofReal (K * p * M) :=
    hlim.trans (Filter.liminf_le_of_frequently_le' (Filter.Eventually.of_forall hb).frequently)
  have hmem : MemLp (fun x => matFrobNorm (G x)) (ENNReal.ofReal p) (volume.restrict torusCube) :=
    lt_of_le_of_lt hle ENNReal.ofReal_lt_top
  exact ⟨hmem, hle⟩

end PDE
