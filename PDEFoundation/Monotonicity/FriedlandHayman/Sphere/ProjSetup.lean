module

public import PDEFoundation.Monotonicity.Core.BridgeSphere
public import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
public import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Friedland--Hayman: Gaussian polar setup for the projection formula

The first-`n`-coordinates projection `projFst`, the measure-preserving splitting
`HilbertVec n × HilbertVec N ≃ᵐ HilbertVec (n + N)`, the Gaussian integrability on
`HilbertVec d`, and the polar evaluation of the Gaussian-weighted degree-zero homogeneous
extension `homExt H` of a bounded measurable function.
-/

@[expose] public section

open MeasureTheory

namespace PDE.FHLane

noncomputable section

/-- First `n` coordinates of a point of `Vec (n + N)`. -/
def projFst {n N : ℕ} (x : Vec (n + N)) : Vec n := fun i => x (Fin.castAdd N i)

/-- Concatenation of coordinates, as a measurable equivalence. -/
def appendEquiv (n N : ℕ) : Vec n × Vec N ≃ᵐ Vec (n + N) :=
  (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin n ⊕ Fin N => ℝ)).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin (n + N) => ℝ) finSumFinEquiv)

theorem appendEquiv_apply (n N : ℕ) (p : Vec n × Vec N) : appendEquiv n N p = Fin.append p.1 p.2 := by
  ext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [appendEquiv, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
    rfl
  · simp [appendEquiv, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]
    rfl

theorem mp_appendEquiv (n N : ℕ) : MeasurePreserving (appendEquiv n N) volume volume := by
  unfold appendEquiv
  exact (volume_measurePreserving_sumPiEquivProdPi_symm (fun _ : Fin n ⊕ Fin N => ℝ)).trans
    (volume_measurePreserving_piCongrLeft (fun _ : Fin (n + N) => ℝ) finSumFinEquiv)

/-- The native/Hilbert conversion as a measurable equivalence. -/
def hilbME (d : ℕ) : Vec d ≃ᵐ HilbertVec d := PDE.Internal.toHilbert.toHomeomorph.toMeasurableEquiv

/-- The measure-preserving splitting `HilbertVec n × HilbertVec N ≃ᵐ HilbertVec (n + N)`. -/
def splitEquiv (n N : ℕ) : HilbertVec n × HilbertVec N ≃ᵐ HilbertVec (n + N) :=
  ((hilbME n).symm.prodCongr (hilbME N).symm).trans ((appendEquiv n N).trans (hilbME (n + N)))

theorem mp_splitEquiv (n N : ℕ) : MeasurePreserving (splitEquiv n N) volume volume := by
  unfold splitEquiv
  refine MeasurePreserving.trans ?_ (MeasurePreserving.trans (mp_appendEquiv n N) ?_)
  · exact (PDE.Internal.measurePreserving_toHilbert_symm).prod (PDE.Internal.measurePreserving_toHilbert_symm)
  · exact PDE.Internal.measurePreserving_toHilbert

theorem splitEquiv_toVec (n N : ℕ) (p : HilbertVec n × HilbertVec N) :
    (splitEquiv n N p).toVec = Fin.append p.1.toVec p.2.toVec := by
  simp [splitEquiv, hilbME, appendEquiv_apply]
  rfl

theorem norm_splitEquiv_sq (n N : ℕ) (p : HilbertVec n × HilbertVec N) :
    ‖splitEquiv n N p‖ ^ 2 = ‖p.1‖ ^ 2 + ‖p.2‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2, Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    have := congrFun (splitEquiv_toVec n N p) (Fin.castAdd N i)
    simp only [HilbertVec.toVec_apply, Fin.append_left] at this
    rw [this]
  · refine Finset.sum_congr rfl fun i _ => ?_
    have := congrFun (splitEquiv_toVec n N p) (Fin.natAdd n i)
    simp only [HilbertVec.toVec_apply, Fin.append_right] at this
    rw [this]

theorem projFst_splitEquiv (n N : ℕ) (p : HilbertVec n × HilbertVec N) :
    projFst (splitEquiv n N p).toVec = p.1.toVec := by
  rw [splitEquiv_toVec]; ext i; simp [projFst]

theorem integrable_gauss (d : ℕ) :
    Integrable (fun z : HilbertVec d => Real.exp (-(‖z‖ ^ 2 / 2))) := by
  have := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := HilbertVec d)
    (b := (1/2 : ℂ)) (by norm_num) 0 0)
  have h2 := this.re
  convert h2 using 2 with z
  simp
  have h : (-(2⁻¹ * (‖z‖ : ℂ) ^ 2)) = ((-(‖z‖ ^ 2 / 2) : ℝ) : ℂ) := by push_cast; ring
  rw [h, Complex.exp_ofReal_re]


/-- The radial Gaussian moment `∫_0^∞ r^(d-1) exp(-r²/2) dr`. -/
def radialGauss (d : ℕ) : ℝ := ∫ r in Set.Ioi (0 : ℝ), r ^ (d - 1) * Real.exp (-(r ^ 2 / 2))

theorem integrableOn_radialGauss (d : ℕ) :
    IntegrableOn (fun r : ℝ => r ^ (d - 1) * Real.exp (-(r ^ 2 / 2))) (Set.Ioi 0) := by
  have := integrable_rpow_mul_exp_neg_mul_sq (b := 1/2) (by norm_num) (s := ((d - 1 : ℕ) : ℝ))
    (by have : (0 : ℝ) ≤ ((d - 1 : ℕ) : ℝ) := Nat.cast_nonneg _; linarith)
  refine (this.integrableOn).congr_fun (fun r hr => ?_) measurableSet_Ioi
  simp only [Real.rpow_natCast]
  congr 2; ring

theorem radialGauss_pos (d : ℕ) : 0 < radialGauss d := by
  unfold radialGauss
  refine (setIntegral_pos_iff_support_of_nonneg_ae ?_ (integrableOn_radialGauss d)).2 ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact (mul_pos (pow_pos hr _) (Real.exp_pos _)).le
  · have : Function.support (fun r : ℝ => r ^ (d - 1) * Real.exp (-(r ^ 2 / 2))) ∩ Set.Ioi 0 = Set.Ioi 0 := by
      ext r
      simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_Ioi]
      constructor
      · exact fun h => h.2
      · exact fun hr => ⟨(mul_pos (pow_pos hr _) (Real.exp_pos _)).ne', hr⟩
    rw [this]; simp

/-- Gaussian-weighted degree-zero homogeneous extension. -/
def homExt {d : ℕ} (H : HilbertVec d → ℝ) (z : HilbertVec d) : ℝ :=
  Real.exp (-(‖z‖ ^ 2 / 2)) * H (‖z‖⁻¹ • z)

theorem measurable_homExt {d : ℕ} {H : HilbertVec d → ℝ} (hH : Measurable H) :
    Measurable (homExt H) := by
  unfold homExt; fun_prop

theorem integrable_homExt {d : ℕ} {H : HilbertVec d → ℝ} (hH : Measurable H) {C : ℝ}
    (hb : ∀ z, |H z| ≤ C) : Integrable (homExt H) := by
  refine ((integrable_gauss d).const_mul C).mono' (measurable_homExt hH).aestronglyMeasurable
    (ae_of_all _ fun z => ?_)
  unfold homExt
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), mul_comm]
  exact mul_le_mul_of_nonneg_right (hb _) (Real.exp_pos _).le

theorem integral_homExt {d : ℕ} [NeZero d] {H : HilbertVec d → ℝ} (hH : Measurable H) {C : ℝ}
    (hb : ∀ z, |H z| ≤ C) :
    ∫ z, homExt H z = radialGauss d * ∫ ω, H (ω : HilbertVec d) ∂(Internal.sphereMeasure d) := by
  rw [Internal.integral_eq_integral_Ioi_sphere (integrable_homExt hH hb), radialGauss,
    ← integral_mul_const]
  refine setIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
  have hr' : (0 : ℝ) < r := hr
  have h1 : ∀ ω : Metric.sphere (0 : HilbertVec d) 1,
      homExt H (r • (ω : HilbertVec d)) = Real.exp (-(r ^ 2 / 2)) * H ω := by
    intro ω
    have hω : ‖(ω : HilbertVec d)‖ = 1 := by simp
    unfold homExt
    rw [norm_smul, hω, Real.norm_eq_abs, abs_of_pos hr', mul_one,
      inv_smul_smul₀ hr'.ne']
  simp only [h1, smul_eq_mul]
  rw [integral_const_mul]; ring



end

end PDE.FHLane
