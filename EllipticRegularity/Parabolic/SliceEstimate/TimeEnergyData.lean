module

public import EllipticRegularity.Parabolic.Energy.Slab
public import EllipticRegularity.Parabolic.Energy.Limits
public import EllipticRegularity.Parabolic.SliceEstimate.TimeChain

/-!
# Abstract data for the mollified time-energy estimate

`EData` bundles the PDE-free hypotheses: a compact set `K` with collar `δ0`, a time interval
`(p,q]`, a `C¹` cutoff `φ`, `L²` functions `W` (gradient of `u`) and `Z` (gradient of `v = ∂ₜu`),
and every-time mollified objects `Ab`, `Zb` which are absolutely continuous in time with
derivative `Zb` and agree for a.e. time with the slice-wise mollifications of `W`, `Z`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.Slice

open MeasureTheory Set Filter Topology Metric PDE PDE.Parabolic.Energy

variable {d : ℕ}

structure EData (d : ℕ) where
  K : Set (Vec d)
  hK : IsCompact K
  δ0 : ℝ
  hδ0 : 0 < δ0
  hδ1 : δ0 ≤ 1
  p : ℝ
  q : ℝ
  hpq : p < q
  lam : ℝ
  Lam : ℝ
  A : Vec d → Mat d
  hAm : ∀ i j, AEMeasurable (fun x => A x i j) (volume.restrict K)
  hAe : ∀ᵐ x ∂(volume.restrict K), IsEllipticMatrix lam Lam (A x)
  φ : Vec d × ℝ → ℝ
  hφ : ContDiff ℝ 1 φ
  hφp : ∀ x ∈ K, φ (x, p) = 0
  W : Fin d → Vec d × ℝ → ℝ
  Z : Fin d → Vec d × ℝ → ℝ
  hW2 : ∀ i, MemLp (W i) 2 (volume.restrict (cthickening δ0 K ×ˢ Ioc p q))
  hZ2 : ∀ i, MemLp (Z i) 2 (volume.restrict (cthickening δ0 K ×ˢ Ioc p q))
  Ab : Fin d → ℝ → Vec d → ℝ → ℝ
  Zb : Fin d → ℝ → Vec d → ℝ → ℝ
  hAb : ∀ᵐ τ ∂(volume.restrict (Ioc p q)), ∀ a : ℝ, 0 < a → a ≤ δ0 → ∀ y ∈ K, ∀ i,
    Ab i a y τ = mollT a (cthickening δ0 K) (W i) (y, τ)
  hZb : ∀ᵐ τ ∂(volume.restrict (Ioc p q)), ∀ a : ℝ, 0 < a → a ≤ δ0 → ∀ y ∈ K, ∀ i,
    Zb i a y τ = mollT a (cthickening δ0 K) (Z i) (y, τ)
  hAC : ∀ a : ℝ, 0 < a → a ≤ δ0 → ∀ y ∈ K, ∀ i, ∀ τ1 τ2, p ≤ τ1 → τ1 ≤ τ2 → τ2 ≤ q →
    Ab i a y τ2 - Ab i a y τ1 = ∫ σ in τ1..τ2, Zb i a y σ
  hZint : ∀ a : ℝ, 0 < a → a ≤ δ0 → ∀ y ∈ K, ∀ i, IntervalIntegrable (Zb i a y) volume p q

namespace EData

variable (D : EData d)

/-- The collar. -/
abbrev K1 : Set (Vec d) := cthickening D.δ0 D.K

theorem K1_compact : IsCompact D.K1 := D.hK.cthickening
theorem K1_measurable : MeasurableSet D.K1 := D.K1_compact.measurableSet
theorem K_subset_K1 : D.K ⊆ D.K1 := self_subset_cthickening _
theorem K_measurable : MeasurableSet D.K := D.hK.measurableSet

/-- The measure on the slab `K × (p, t]`. -/
noncomputable abbrev μ (t : ℝ) : Measure (Vec d × ℝ) := volume.restrict (D.K ×ˢ Ioc D.p t)

/-- The scale sequence. -/
noncomputable def aSeq (n : ℕ) : ℝ := D.δ0 / ((n : ℝ) + 1)

theorem aSeq_pos (n : ℕ) : 0 < D.aSeq n := by unfold aSeq; have := D.hδ0; positivity

theorem aSeq_le_δ0 (n : ℕ) : D.aSeq n ≤ D.δ0 := by
  unfold aSeq
  rw [div_le_iff₀ (by positivity)]
  nlinarith [D.hδ0, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem aSeq_le_one (n : ℕ) : D.aSeq n ≤ 1 := (D.aSeq_le_δ0 n).trans D.hδ1

theorem aSeq_tendsto : Tendsto D.aSeq atTop (𝓝 0) := by
  unfold aSeq
  have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul D.δ0
  simpa [div_eq_mul_inv] using this

/-- Convergence of slice-wise mollifications of an `L²` function on the slab `K × (p, t]`. -/
theorem conv_mollT {t : ℝ} (ht : t ≤ D.q) {g : Vec d × ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict (D.K1 ×ˢ Ioc D.p D.q))) :
    MemLp g 2 (D.μ t) ∧ (∀ n, MemLp (mollT (D.aSeq n) D.K1 g) 2 (D.μ t)) ∧
      Tendsto (fun n => eLpNorm (mollT (D.aSeq n) D.K1 g - g) 2 (D.μ t)) atTop (𝓝 0) := by
  have hg' : MemLp g 2 (volume.restrict (D.K1 ×ˢ Ioc D.p t)) :=
    hg.mono_measure (Measure.restrict_mono (prod_mono subset_rfl (Ioc_subset_Ioc_right ht)) le_rfl)
  have hg'' : MemLp g 2 (D.μ t) :=
    hg'.mono_measure (Measure.restrict_mono (prod_mono D.K_subset_K1 subset_rfl) le_rfl)
  refine ⟨hg'', fun n => memLp_mollT D.K1_compact hg' (D.aSeq_pos n), ?_⟩
  refine tendsto_eLpNorm_sub_of_lintegral
    (fun n => aestronglyMeasurable_mollT D.K1_measurable D.K hg'.aestronglyMeasurable _)
    hg''.aestronglyMeasurable ?_
  exact tendsto_lintegral_mollT D.K1_compact D.K_subset_K1 D.K_measurable hg' D.aSeq_pos
    D.aSeq_le_one D.aSeq_tendsto

end EData

end PDE.Parabolic.Slice
