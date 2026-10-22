module

public import PDEFoundation.Analysis.Newtonian.WeakType.MollifyConverge
public import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Passing to the limit `a → 0⁺` in a weak-type bound

If `Φ a → Φ₀` pointwise as `a → 0⁺` and the superlevel sets `{l < Φ a}` have volume `≤ B` for all
small `a`, then so does `{l < Φ₀}`.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal Topology

namespace PDE.NewtonWeakType

noncomputable section

variable {d : ℕ}

theorem volume_gt_le_of_tendsto {Φ : ℝ → Vec d → ℝ} {Φ₀ : Vec d → ℝ} {l : ℝ} {B : ℝ≥0∞}
    (hconv : ∀ x, Tendsto (fun a => Φ a x) (𝓝[>] (0 : ℝ)) (𝓝 (Φ₀ x)))
    (hbd : ∀ᶠ a in 𝓝[>] (0 : ℝ), volume {x | l < Φ a x} ≤ B) :
    volume {x | l < Φ₀ x} ≤ B := by
  obtain ⟨u, hu', hsub⟩ := (mem_nhdsGT_iff_exists_Ioc_subset).mp hbd
  have hu : 0 < u := hu'
  set a : ℕ → ℝ := fun m => u * (1 / ((m : ℝ) + 1)) with ha
  have hapos : ∀ m, 0 < a m := fun m => by
    show 0 < u * (1 / ((m : ℝ) + 1))
    positivity
  have hale : ∀ m, a m ≤ u := fun m => by
    show u * (1 / ((m : ℝ) + 1)) ≤ u
    have h1 : 1 / ((m : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      linarith
    nlinarith
  have ha0 : Tendsto a atTop (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, Filter.Eventually.of_forall hapos⟩
    simpa [ha, one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul u
  have hbound : ∀ m, volume {x | l < Φ (a m) x} ≤ B := fun m => hsub ⟨hapos m, hale m⟩
  have hsub2 : {x | l < Φ₀ x} ⊆ ⋃ n, ⋂ m ∈ Ici n, {x | l < Φ (a m) x} := by
    intro x hx
    have h1 : Tendsto (fun m => Φ (a m) x) atTop (𝓝 (Φ₀ x)) := (hconv x).comp ha0
    have h2 : ∀ᶠ m in atTop, l < Φ (a m) x := h1.eventually (lt_mem_nhds hx)
    obtain ⟨n, hn⟩ := eventually_atTop.mp h2
    exact mem_iUnion.mpr ⟨n, mem_iInter₂.mpr fun m hm => hn m hm⟩
  have hmono : Monotone fun n : ℕ => ⋂ m ∈ Ici n, {x | l < Φ (a m) x} := by
    intro n n' hnn'
    exact iInter₂_mono' fun m hm => ⟨m, le_trans hnn' hm, subset_rfl⟩
  calc volume {x | l < Φ₀ x} ≤ volume (⋃ n, ⋂ m ∈ Ici n, {x | l < Φ (a m) x}) := measure_mono hsub2
    _ = ⨆ n, volume (⋂ m ∈ Ici n, {x | l < Φ (a m) x}) := hmono.measure_iUnion
    _ ≤ B := iSup_le fun n =>
        (measure_mono (iInter₂_subset n (mem_Ici.mpr le_rfl))).trans (hbound n)

theorem tendsto_vecEuclideanNorm_gradient_mollVec (hd : 0 < d) {F : Vec d → Vec d}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F) (x : Vec d) :
    Tendsto (fun a => vecEuclideanNorm (classicalGradient (newtonPotential (mollVec a F)) x))
      (𝓝[>] (0 : ℝ)) (𝓝 (vecEuclideanNorm (classicalGradient (newtonPotential F) x))) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hε' : 0 < ε / (2 * d) := by positivity
  have hev : ∀ᶠ a in 𝓝[>] (0 : ℝ), ∀ k : Fin d,
      |euclideanCoordDeriv k (newtonPotential (mollVec a F)) x -
        euclideanCoordDeriv k (newtonPotential F) x| ≤ ε / (2 * d) := by
    rw [eventually_all]
    exact fun k => eventually_abs_coordDeriv_mollVec_sub_le hd hF hFc x k hε'
  filter_upwards [hev] with a ha
  rw [Real.dist_eq]
  set v := classicalGradient (newtonPotential (mollVec a F)) x
  set w := classicalGradient (newtonPotential F) x
  have h1 : |vecEuclideanNorm v - vecEuclideanNorm w| ≤ vecEuclideanNorm (v - w) := by
    rw [abs_le]
    constructor
    · have := vecEuclideanNorm_add_le (w - v) v
      rw [vecEuclideanNorm_sub_comm] at this
      simp only [sub_add_cancel] at this
      linarith
    · have := vecEuclideanNorm_add_le (v - w) w
      simp only [sub_add_cancel] at this
      linarith
  have h2 : vecEuclideanNorm (v - w) ≤ ∑ k : Fin d, |(v - w) k| := vecEuclideanNorm_le_sum_abs _
  have h3 : ∑ k : Fin d, |(v - w) k| ≤ ∑ _k : Fin d, ε / (2 * d) :=
    Finset.sum_le_sum fun k _ => ha k
  have h4 : ∑ _k : Fin d, ε / (2 * d) = ε / 2 := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  linarith

end

end PDE.NewtonWeakType
