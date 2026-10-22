module

public import EllipticRegularity.Parabolic.Energy.Slab
public import EllipticRegularity.Parabolic.Energy.TimeAC

/-!
# The abstract energy-identity data

`Data d` bundles the hypotheses of the abstract (PDE-free) energy identity: a compact set `K`, a
collar width `δ0`, a time slab `[s,t]`, functions `u`, `Du`, `G` (with `Du`, `G` Borel), a `C¹`
cutoff `φ`, the local `L²` conditions, the weak-gradient identity for mollified test functions
and the mollified weak time-slice identity.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.Energy

open MeasureTheory Set Filter Topology Metric

variable {d : ℕ}

structure Data (d : ℕ) where
  K : Set (Vec d)
  hK : IsCompact K
  δ0 : ℝ
  hδ0 : 0 < δ0
  hδ1 : δ0 ≤ 1
  s : ℝ
  t : ℝ
  hst : s < t
  u : Vec d × ℝ → ℝ
  Du : Vec d × ℝ → Vec d
  G : Vec d × ℝ → Vec d
  φ : Vec d × ℝ → ℝ
  hφ : ContDiff ℝ 1 φ
  hφK : ∀ x τ, τ ∈ Icc s t → x ∈ cthickening (2 * δ0) K → x ∉ K → φ (x, τ) = 0
  hDum : ∀ i, Measurable fun z => Du z i
  hGm : ∀ i, Measurable fun z => G z i
  hu2 : MemLp u 2 (volume.restrict (cthickening δ0 K ×ˢ Ioc s t))
  hDu2 : ∀ i, MemLp (fun z => Du z i) 2 (volume.restrict (cthickening δ0 K ×ˢ Ioc s t))
  hG2 : ∀ i, MemLp (fun z => G z i) 2 (volume.restrict (cthickening δ0 K ×ˢ Ioc s t))
  hus : ∀ τ ∈ Icc s t, MemLp (fun y => u (y, τ)) 2 (volume.restrict (cthickening δ0 K))
  hwg : ∀ᵐ τ ∂(volume.restrict (Ioc s t)), ∀ a : ℝ, 0 < a → a ≤ δ0 → ∀ x ∈ K, ∀ i,
    ∫ y in cthickening δ0 K, fderiv ℝ (kern a) (x - y) (basisVec i) * u (y, τ) =
      ∫ y in cthickening δ0 K, kern a (x - y) * Du (y, τ) i
  hslice : ∀ a : ℝ, 0 < a → a ≤ δ0 → ∀ x ∈ K, ∀ τ1 τ2 : ℝ, s ≤ τ1 → τ1 ≤ τ2 → τ2 ≤ t →
    (∫ y in cthickening δ0 K, kern a (x - y) * u (y, τ2)) -
        (∫ y in cthickening δ0 K, kern a (x - y) * u (y, τ1)) =
      ∫ z in cthickening δ0 K ×ˢ Ioc τ1 τ2,
        ∑ i, G z i * fderiv ℝ (kern a) (x - z.1) (basisVec i)

namespace Data

variable (D : Data d)

/-- The collar `K1 = cthickening δ0 K` (compact). -/
abbrev K1 : Set (Vec d) := cthickening D.δ0 D.K

theorem K1_compact : IsCompact D.K1 := D.hK.cthickening

theorem K1_measurable : MeasurableSet D.K1 := D.K1_compact.measurableSet

theorem K_subset_K1 : D.K ⊆ D.K1 := self_subset_cthickening _

theorem K_measurable : MeasurableSet D.K := D.hK.measurableSet

/-- The mollified `u`. -/
noncomputable def v (a : ℝ) : Vec d × ℝ → ℝ := mollT a D.K1 D.u

/-- The mollified time derivative `D̂_a(x,σ) = ∫_{K1} G(y,σ)·∇k_a(x-y) dy`. -/
noncomputable def Dh (a : ℝ) (x : Vec d) (σ : ℝ) : ℝ :=
  ∫ y in D.K1, ∑ i, D.G (y, σ) i * fderiv ℝ (kern a) (x - y) (basisVec i)

theorem measure_slab_lt_top (p q : ℝ) : volume (D.K1 ×ˢ Ioc p q) < ⊤ := by
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  exact ENNReal.mul_lt_top D.K1_compact.measure_lt_top (by simp)

instance (p q : ℝ) : IsFiniteMeasure (volume.restrict (D.K1 ×ˢ Ioc p q)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact D.measure_slab_lt_top p q⟩

theorem integrableOn_G (i : Fin d) :
    IntegrableOn (fun z => D.G z i) (D.K1 ×ˢ Ioc D.s D.t) :=
  (D.hG2 i).integrable (by norm_num)

end Data

end PDE.Parabolic.Energy
