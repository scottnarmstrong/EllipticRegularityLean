module

public import EllipticRegularity.Parabolic.NashLower.Chain

/-!
# Pigeonhole for small balls (Nash-Aronson lower bound)

If `∫_{B(y,ρ)} v ≥ 1/2`, then some small ball `B(z,r)` with `z ∈ B(y,ρ)` carries a large essential
supremum of `v`: `ess sup ≥ 1/(4 |B(y,ρ)|)`.  The argument is by contradiction with a countable
(Lindelöf) subcover of `B(y,ρ)` by the balls `B(z,r)`.
-/

@[expose] public section

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

namespace PDE.Parabolic.NashLower

/-- A countable set of centres in `S` whose `r`-balls cover `S`. -/
theorem exists_countable_centers_cover {d : ℕ} (S : Set (Vec d)) {r : ℝ} (hr : 0 < r) :
    ∃ T ⊆ S, T.Countable ∧ S ⊆ ⋃ z ∈ T, euclideanBall z r := by
  obtain ⟨T, hTS, hTc, hTU⟩ := isOpen_biUnion_countable S (fun z => euclideanBall z r)
    (fun z _ => isOpen_euclideanBall z r)
  refine ⟨T, hTS, hTc, ?_⟩
  rw [hTU]
  intro x hx
  exact mem_biUnion hx (center_mem_euclideanBall x hr)

theorem exists_center_essSup_ge {d : ℕ} (y : Vec d) {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (v : Vec d → ℝ) (hI : (1 / 2 : ℝ) ≤ ∫ x in euclideanBall y ρ, v x) :
    ∃ z ∈ euclideanBall y ρ,
      ENNReal.ofReal (1 / (4 * (volume (euclideanBall y ρ)).toReal)) ≤
        essSup (fun x => ENNReal.ofReal (v x)) (volume.restrict (euclideanBall z r)) := by
  set B := euclideanBall y ρ with hB
  set V := (volume B).toReal with hV
  have hVpos : 0 < V := ENNReal.toReal_pos (volume_euclideanBall_pos y hρ).ne'
    (volume_euclideanBall_ne_top y hρ.le)
  set M : ℝ := 1 / (4 * V) with hM
  have hMpos : 0 < M := by positivity
  by_contra hcon
  push Not at hcon
  have hlt : ∀ z ∈ B, ∀ᵐ x ∂(volume.restrict (euclideanBall z r)), v x < M := by
    intro z hz
    have h := ae_lt_of_essSup_lt (hcon z hz)
    filter_upwards [h] with x hx
    exact ((ENNReal.ofReal_lt_ofReal_iff' ).1 hx).1
  obtain ⟨T, hTB, hTc, hcov⟩ := exists_countable_centers_cover B hr
  have hae : ∀ᵐ x ∂(volume.restrict (⋃ z ∈ T, euclideanBall z r)), v x < M :=
    (ae_restrict_biUnion_iff (fun z => euclideanBall z r) hTc (fun x => v x < M)).2
      fun z hz => hlt z (hTB hz)
  have hae2 : ∀ᵐ x ∂(volume.restrict B), v x < M :=
    ae_restrict_of_ae_restrict_of_subset hcov hae
  have hint : Integrable v (volume.restrict B) := by
    by_contra hni
    rw [integral_undef hni] at hI
    norm_num at hI
  have hfin : IsFiniteMeasure (volume.restrict B) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact (volume_euclideanBall_ne_top y hρ.le).lt_top⟩
  have hle : ∫ x in B, v x ≤ ∫ _ in B, M :=
    integral_mono_ae hint (integrable_const M) (hae2.mono fun x hx => hx.le)
  have hconst : ∫ _ in B, M = V * M := by
    rw [setIntegral_const, smul_eq_mul, Measure.real, hV]
  have hVM : V * M = 1 / 4 := by
    rw [hM]; field_simp
  linarith

/-- Local essential-infimum bounds on small balls around every point of `B(x,R)` give an
a.e. lower bound on `B(x,R)`. -/
theorem ae_ge_of_local_essInf {d : ℕ} (x : Vec d) {R r : ℝ} (hr : 0 < r) (f : Vec d → ℝ)
    {m : ℝ} (hm : 0 < m)
    (h : ∀ x' ∈ euclideanBall x R, ENNReal.ofReal m ≤
      essInf (fun y => ENNReal.ofReal (f y)) (volume.restrict (euclideanBall x' r))) :
    ∀ᵐ y ∂(volume.restrict (euclideanBall x R)), m ≤ f y := by
  obtain ⟨T, hTB, hTc, hcov⟩ := exists_countable_centers_cover (euclideanBall x R) hr
  have hae : ∀ᵐ y ∂(volume.restrict (⋃ z ∈ T, euclideanBall z r)), m ≤ f y := by
    refine (ae_restrict_biUnion_iff (fun z => euclideanBall z r) hTc (fun y => m ≤ f y)).2 ?_
    intro z hz
    have h1 : ∀ᵐ y ∂(volume.restrict (euclideanBall z r)),
        essInf (fun y => ENNReal.ofReal (f y)) (volume.restrict (euclideanBall z r)) ≤
          ENNReal.ofReal (f y) := ae_essInf_le
    filter_upwards [h1] with y hy
    have h2 := (h z (hTB hz)).trans hy
    rcases (ENNReal.ofReal_le_ofReal_iff').1 h2 with h3 | h3
    · exact h3
    · exact absurd h3 (not_le.2 hm)
  exact ae_restrict_of_ae_restrict_of_subset hcov hae

end PDE.Parabolic.NashLower
