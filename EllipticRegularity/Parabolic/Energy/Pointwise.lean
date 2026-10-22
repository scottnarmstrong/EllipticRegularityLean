module

public import EllipticRegularity.Parabolic.Energy.Data

/-!
# The pointwise-in-`x` identity for the mollified energy

For `x ∈ K` the mollified solution `τ ↦ v_a(x,τ)` is an integral of `Dh_a(x,·)`, so
`½ φ² v²` obeys the absolutely continuous chain rule in time.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.Energy

open MeasureTheory Set Filter Topology Metric PDE

variable {d : ℕ}

namespace Data

variable (D : Data d)

/-- The integrand of the time-slice identity. -/
noncomputable def Phi (a : ℝ) (x : Vec d) (z : Vec d × ℝ) : ℝ :=
  ∑ i, D.G z i * fderiv ℝ (kern a) (x - z.1) (basisVec i)

theorem Phi_integrableOn {a : ℝ} (ha : 0 < a) (x : Vec d) {p q : ℝ} (hp : D.s ≤ p) (hq : q ≤ D.t) :
    IntegrableOn (D.Phi a x) (D.K1 ×ˢ Ioc p q) := by
  have hsub : D.K1 ×ˢ Ioc p q ⊆ D.K1 ×ˢ Ioc D.s D.t :=
    prod_mono subset_rfl (Ioc_subset_Ioc hp hq)
  unfold Phi
  refine integrable_finsetSum _ fun i _ => ?_
  obtain ⟨C, hC⟩ := kern_fderiv_bound (d := d) ha (basisVec i)
  refine Integrable.mul_bdd ((D.integrableOn_G i).mono_set hsub) ?_ (c := C) ?_
  · exact ((kern_fderiv_continuous a (basisVec i)).comp
      (continuous_const.sub continuous_fst)).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun z => by simpa using hC (x - z.1)

theorem integral_Phi_eq {a : ℝ} (ha : 0 < a) (x : Vec d) {p q : ℝ} (hp : D.s ≤ p)
    (hq : q ≤ D.t) :
    ∫ z in D.K1 ×ˢ Ioc p q, D.Phi a x z = ∫ σ in Ioc p q, D.Dh a x σ := by
  have hint := D.Phi_integrableOn ha x hp hq
  unfold IntegrableOn at hint
  rw [volume_restrict_prod] at hint ⊢
  rw [integral_prod_symm _ hint]
  rfl

theorem Dh_integrableOn {a : ℝ} (ha : 0 < a) (x : Vec d) {p q : ℝ} (hp : D.s ≤ p) (hq : q ≤ D.t) :
    IntegrableOn (D.Dh a x) (Ioc p q) := by
  have hint := D.Phi_integrableOn ha x hp hq
  unfold IntegrableOn at hint ⊢
  rw [volume_restrict_prod] at hint
  exact hint.integral_prod_right

theorem v_eq (a : ℝ) (x : Vec d) (τ : ℝ) :
    D.v a (x, τ) = ∫ y in D.K1, kern a (x - y) * D.u (y, τ) := by
  unfold v
  rw [mollT_eq, ← integral_indicator D.K1_measurable]
  congr 1; funext y
  by_cases hy : y ∈ D.K1 <;> simp [hy]

theorem v_rep {a : ℝ} (ha : 0 < a) (haδ : a ≤ D.δ0) {x : Vec d} (hx : x ∈ D.K) {τ : ℝ}
    (hτ : τ ∈ Icc D.s D.t) :
    D.v a (x, τ) = D.v a (x, D.s) + ∫ σ in D.s..τ, D.Dh a x σ := by
  have h : (∫ y in D.K1, kern a (x - y) * D.u (y, τ)) -
      (∫ y in D.K1, kern a (x - y) * D.u (y, D.s)) =
      ∫ z in D.K1 ×ˢ Ioc D.s τ, D.Phi a x z := D.hslice a ha haδ x hx D.s τ le_rfl hτ.1 hτ.2
  rw [intervalIntegral.integral_of_le hτ.1, ← D.integral_Phi_eq ha x le_rfl hτ.2]
  rw [D.v_eq, D.v_eq]
  linarith

theorem Dh_intervalIntegrable {a : ℝ} (ha : 0 < a) (x : Vec d) :
    IntervalIntegrable (D.Dh a x) volume D.s D.t :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le D.hst.le).2 (D.Dh_integrableOn ha x le_rfl le_rfl)

theorem contDiff_timeSlice (x : Vec d) : ContDiff ℝ 1 fun τ => D.φ (x, τ) :=
  D.hφ.comp (contDiff_const.prodMk contDiff_id)

theorem deriv_timeSlice (x : Vec d) (τ : ℝ) :
    deriv (fun τ => D.φ (x, τ)) τ = parTimeDeriv D.φ (x, τ) := by
  have h1 : HasFDerivAt D.φ (fderiv ℝ D.φ (x, τ)) (x, τ) :=
    ((D.hφ.differentiable (by simp)) (x, τ)).hasFDerivAt
  have h2 : HasDerivAt (fun τ : ℝ => ((x, τ) : Vec d × ℝ)) ((0 : Vec d), (1 : ℝ)) τ :=
    (hasDerivAt_const τ x).prodMk (hasDerivAt_id τ)
  exact (h1.comp_hasDerivAt τ h2).deriv

/-- The pointwise (in `x ∈ K`) energy identity for the mollified solution. -/
theorem pointwise_identity {a : ℝ} (ha : 0 < a) (haδ : a ≤ D.δ0) {x : Vec d} (hx : x ∈ D.K) :
    (1 / 2 : ℝ) * D.φ (x, D.t) ^ 2 * D.v a (x, D.t) ^ 2 -
        (1 / 2 : ℝ) * D.φ (x, D.s) ^ 2 * D.v a (x, D.s) ^ 2 =
      ∫ σ in D.s..D.t, (D.φ (x, σ) * parTimeDeriv D.φ (x, σ) * D.v a (x, σ) ^ 2 +
        D.φ (x, σ) ^ 2 * D.v a (x, σ) * D.Dh a x σ) := by
  have := time_energy_identity D.hst.le (v := fun τ => D.v a (x, τ)) (D := D.Dh a x)
    (ψ := fun τ => D.φ (x, τ)) (D.Dh_intervalIntegrable ha x)
    (fun τ hτ => D.v_rep ha haδ hx hτ) (D.contDiff_timeSlice x)
  simp only [D.deriv_timeSlice] at this
  exact this

end Data

end PDE.Parabolic.Energy
