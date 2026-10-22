module

public import PDEFoundation.Analysis.Inequalities.Bombieri.Ball

/-!
# The Bombieri lemma, full statement (Lemma 1.13)

Reduction of the statement with almost-everywhere hypotheses to the measurable, everywhere positive
case by choosing a measurable positive representative.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE.Bombieri

/-- The Bombieri lemma (Lemma 1.13), with exactly the type of the statement `exists_bombieri_bound`. -/
theorem exists_bombieri_bound_full (d : ℕ) (_hd : 1 ≤ d) (q k A : ℝ) (hq : 0 < q) (hk : 0 < k)
    (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : Vec d → ℝ,
      MemLp v (ENNReal.ofReal q) (volumeOn (euclideanBall (0 : Vec d) 1)) →
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 < v x) →
      eLpNorm (fun x => Real.log (v x)) 1 (volumeOn (euclideanBall (0 : Vec d) 1)) ≤
        ENNReal.ofReal A →
      (∀ r s : ℝ, 1 / 2 ≤ r → r < s → s ≤ 1 → ∀ p : ℝ, 0 < p → p ≤ min 1 (q / 2) →
        eLpNorm v (ENNReal.ofReal q) (volumeOn (euclideanBall (0 : Vec d) r)) ≤
          ENNReal.ofReal ((A / (s - r) ^ k) ^ (1 / p)) *
            eLpMeanNormOn (euclideanBall (0 : Vec d) s) (ENNReal.ofReal p) v) →
      eLpNorm v (ENNReal.ofReal q) (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
        ENNReal.ofReal C := by
  obtain ⟨C, hC, hcore⟩ := exists_bombieri_core d q k A hq hk hA
  refine ⟨C, hC, ?_⟩
  intro v hv hvpos hlogv hyp
  set μ := volumeOn (euclideanBall (0 : Vec d) 1) with hμ
  set g := hv.aestronglyMeasurable.mk v with hg
  have hgm : Measurable g := hv.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  set v' : Vec d → ℝ := fun x => if 0 < g x then g x else 1 with hv'
  have hv'm : Measurable v' := Measurable.ite (measurableSet_lt measurable_const hgm) hgm
    measurable_const
  have hv'pos : ∀ x, 0 < v' x := by
    intro x
    simp only [hv']
    split_ifs with h
    · exact h
    · exact one_pos
  have hae : v =ᵐ[μ] v' := by
    filter_upwards [hv.aestronglyMeasurable.ae_eq_mk, hvpos] with x h1 h2
    have : 0 < g x := by simpa only [hg, ← h1] using h2
    simp only [hv', this, ↓reduceIte]
    exact h1
  have hae' : ∀ σ : ℝ, 0 ≤ σ → σ ≤ 1 →
      v =ᵐ[volumeOn (euclideanBall (0 : Vec d) σ)] v' := fun σ h0 h1 =>
    hae.filter_mono (ae_mono (Measure.restrict_mono (euclideanBall_mono h0 h1) le_rfl))
  have hmean : ∀ s : ℝ, 0 < s → s ≤ 1 → ∀ p : ℝ≥0∞,
      eLpMeanNormOn (euclideanBall (0 : Vec d) s) p v =
        eLpMeanNormOn (euclideanBall (0 : Vec d) s) p v' := by
    intro s hs0 hs1 p
    have htop := lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top (0 : Vec d) hs0.le)
    rw [eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn htop,
      eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn htop]
    simp only [eLpNormOn]
    rw [eLpNorm_congr_ae (hae' s hs0.le hs1)]
  refine (eLpNorm_congr_ae (hae' (1 / 2) (by norm_num) (by norm_num))).trans_le ?_
  refine hcore v' hv'm hv'pos ?_ ?_ ?_
  · rw [← eLpNorm_congr_ae hae]; exact hv.eLpNorm_lt_top
  · have hlogae : (fun x => Real.log (v x)) =ᵐ[μ] (fun x => Real.log (v' x)) := by
      filter_upwards [hae] with x hx
      simp [hx]
    rw [← eLpNorm_congr_ae hlogae]; exact hlogv
  · intro r s hr hrs hs p hp hpq
    have hr0 : 0 ≤ r := by linarith
    rw [← eLpNorm_congr_ae (hae' r hr0 (by linarith)), ← hmean s (by linarith) hs]
    exact hyp r s hr hrs hs p hp hpq

end PDE.Bombieri
