module

public import EllipticRegularity.Parabolic.Cauchy.Duality.MassCompactFlux
public import EllipticRegularity.Parabolic.Cauchy.Duality.MassExponential
public import EllipticRegularity.Parabolic.Cauchy.Duality.MassInitial
public import EllipticRegularity.Parabolic.Cauchy.L1.Contraction
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.MeasureTheory.Integral.ExpDecay

@[expose] public section

namespace PDE.Parabolic.Duality

open MeasureTheory Set

/-- A one-dimensional exponential tail is integrable. -/
private theorem cauchyMass_scalar_exp_neg_abs_integrable {β : ℝ} (hβ : 0 < β) :
    Integrable (fun x : ℝ => Real.exp (-(β * |x|))) volume := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  refine IntegrableOn.union ?_ ?_
  · refine (integrableOn_exp_mul_Iic (a := β) hβ 0).congr_fun
      (fun x hx => ?_) measurableSet_Iic
    simp [abs_of_nonpos (show x ≤ 0 from hx)]
  · refine (integrableOn_exp_mul_Ioi (a := -β) (by linarith) 0).congr_fun
      (fun x hx => ?_) measurableSet_Ioi
    simp [abs_of_pos (show 0 < x from hx)]

/-- The square of the inverse Euclidean exponential weight is integrable in space. -/
private theorem cauchyMass_inverse_exp_sq_integrable {d : ℕ} {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun x : Vec d => Real.exp (-(2 * ε * vecEuclideanNorm x))) volume := by
  let α : ℝ := 2 * ε / ((d : ℝ) + 1)
  have hα : 0 < α := by dsimp [α]; positivity
  have hcoord : ∀ i : Fin d, Integrable
      (fun x : ℝ => Real.exp (-(α * |x|))) (volume : Measure ℝ) := by
    intro i
    exact cauchyMass_scalar_exp_neg_abs_integrable (by simpa [abs_mul] using hα)
  have hp : Integrable (fun x : Vec d => ∏ i : Fin d,
      Real.exp (-(α * |x i|))) (Measure.pi fun _ : Fin d => (volume : Measure ℝ)) :=
    Integrable.fintype_prod hcoord
  have hpv : Integrable (fun x : Vec d => ∏ i : Fin d,
      Real.exp (-(α * |x i|))) (volume : Measure (Vec d)) := by
    rw [volume_pi]
    exact hp
  have hnormcont : Continuous (fun x : Vec d => vecEuclideanNorm x) :=
    continuous_vecEuclideanNorm
  have hmeas : AEStronglyMeasurable
      (fun x : Vec d => Real.exp (-(2 * ε * vecEuclideanNorm x))) volume := by
    have hcArg : Continuous (fun x : Vec d => -(2 * ε * vecEuclideanNorm x)) := by
      have heq : (fun x : Vec d => -(2 * ε * vecEuclideanNorm x)) =
          (fun x => (-2 * ε) * vecEuclideanNorm x) := by
        funext x
        ring
      rw [heq]
      exact continuous_const.mul hnormcont
    have hc : Continuous
        (fun x : Vec d => Real.exp (-(2 * ε * vecEuclideanNorm x))) :=
      Real.continuous_exp.comp hcArg
    exact hc.aestronglyMeasurable
  refine Integrable.mono' hpv hmeas ?_
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _)]
  have hsum : (∑ i : Fin d, |x i|) ≤ (d : ℝ) * vecEuclideanNorm x := by
    calc
      (∑ i : Fin d, |x i|) ≤ ∑ _i : Fin d, vecEuclideanNorm x :=
        Finset.sum_le_sum fun i _ => abs_apply_le_vecEuclideanNorm x i
      _ = (d : ℝ) * vecEuclideanNorm x := by simp
  have hexp : Real.exp (-(2 * ε * vecEuclideanNorm x)) ≤
      Real.exp (-(α * ∑ i : Fin d, |x i|)) := by
    apply Real.exp_le_exp.mpr
    have hmul := mul_le_mul_of_nonneg_left hsum hα.le
    dsimp [α] at hmul ⊢
    have hnorm : 0 ≤ vecEuclideanNorm x := vecEuclideanNorm_nonneg x
    have hratio : (2 * ε / ((d : ℝ) + 1)) * (d : ℝ) ≤ 2 * ε := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ (by positivity : 0 < (d : ℝ) + 1)).2
      nlinarith
    have hmul' := mul_le_mul_of_nonneg_right hratio hnorm
    nlinarith
  have hprod : Real.exp (-(α * ∑ i : Fin d, |x i|)) =
      ∏ i : Fin d, Real.exp (-(α * |x i|)) := by
    have hsum : -(α * ∑ i : Fin d, |x i|) = ∑ i, -(α * |x i|) := by
      rw [Finset.mul_sum]
      rw [Finset.sum_neg_distrib]
    rw [hsum, Real.exp_sum]
  rw [hprod] at hexp
  exact hexp

/-- The inverse exponential weight belongs to `L²` on every bounded time slab. -/
theorem cauchyMass_inverse_exponential_memLp {d : ℕ} {ε s t : ℝ} (hε : 0 < ε)
    (_hst : s < t) :
    MemLp (fun z : Vec d × ℝ => Real.exp (-ε * vecEuclideanNorm z.1)) 2
      (volume.restrict ((univ : Set (Vec d)) ×ˢ Ioc s t)) := by
  let J : Set ℝ := Ioc s t
  let Q : Set (Vec d × ℝ) := (univ : Set (Vec d)) ×ˢ J
  let μ : Measure (Vec d × ℝ) := volume.restrict Q
  have htime : IsFiniteMeasure (volume.restrict J) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_lt_top
  let := htime
  have hprod : Integrable (fun z : Vec d × ℝ =>
      Real.exp (-(2 * ε * vecEuclideanNorm z.1)))
      ((volume : Measure (Vec d)).prod (volume.restrict J)) := by
    exact (cauchyMass_inverse_exp_sq_integrable hε).comp_fst (volume.restrict J)
  have hsq : Integrable (fun z : Vec d × ℝ =>
      (Real.exp (-ε * vecEuclideanNorm z.1)) ^ 2) μ := by
    have hμ : μ = (volume : Measure (Vec d)).prod (volume.restrict J) := by
      dsimp [μ, Q, J]
      simpa using PDE.Parabolic.Energy.volume_restrict_prod
        (univ : Set (Vec d)) (Ioc s t)
    rw [hμ]
    refine hprod.congr ?_
    filter_upwards [] with z
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hmeas : AEStronglyMeasurable
      (fun z : Vec d × ℝ => Real.exp (-ε * vecEuclideanNorm z.1)) μ := by
    have hnormcont : Continuous (fun z : Vec d × ℝ => vecEuclideanNorm z.1) :=
      continuous_vecEuclideanNorm.comp continuous_fst
    have hcArg : Continuous (fun z : Vec d × ℝ => -ε * vecEuclideanNorm z.1) :=
      continuous_const.mul hnormcont
    have hc : Continuous (fun z : Vec d × ℝ => Real.exp (-ε * vecEuclideanNorm z.1)) :=
      Real.continuous_exp.comp hcArg
    exact hc.aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq hmeas]
  simpa [μ, Q, J] using hsq

/-- Compactly supported data satisfy the weighted-flux hypotheses used in the mass cutoff limit,
and hence conserve mass at every time. -/
theorem cauchy_mass_of_ball_supported {d : ℕ} {lam Lam : ℝ} {a : ParCoeffField d}
    {s T S : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (f : Vec d → ℝ)
    (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume)
    (hS : 0 ≤ S) (hfS : ∀ x ∉ euclideanClosedBall (0 : Vec d) S, f x = 0)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) {t : ℝ} (ht : t ∈ Icc s T) :
    Integrable (parSlice u.toFun t) volume ∧ ∫ x, u.toFun (x, t) = ∫ x, f x := by
  by_cases hst : s < t
  · have hut := PDE.Parabolic.Cauchy.L1.cauchyL1Contraction d lam Lam a s T hsT ha f
      hf1 hf2 u hu t ht
    have hfluxT := cauchyMass_exponential_flux_of_ball_supported hsT ha f hf2 u hu hS
      (le_of_lt (by norm_num : (0 : ℝ) < 1)) hfS
    have hflux : MemLp
        (fun z : Vec d × ℝ => Real.exp (1 * vecEuclideanNorm z.1) *
          vecEuclideanNorm (matVecMul (a z) (u.grad z))) 2
        (volume.restrict ((univ : Set (Vec d)) ×ˢ Ioc s t)) := by
      have hsub : (univ : Set (Vec d)) ×ˢ Ioc s t ⊆ univ ×ˢ Ioc s T :=
        prod_mono subset_rfl (Ioc_subset_Ioc le_rfl ht.2)
      exact hfluxT.mono_measure (Measure.restrict_mono hsub le_rfl)
    have hinv := cauchyMass_inverse_exponential_memLp (d := d) (ε := 1) (by norm_num) hst
    have hmass := cauchy_mass_of_exponential_flux (ε := 1) hsT ha f hf1 u hu ht hst hut.1
      hflux hinv
    exact ⟨hut.1, hmass⟩
  · have hts : t = s := le_antisymm (le_of_not_gt hst) ht.1
    subst t
    exact cauchy_mass_initial a s T f hf1 u hu

end PDE.Parabolic.Duality
