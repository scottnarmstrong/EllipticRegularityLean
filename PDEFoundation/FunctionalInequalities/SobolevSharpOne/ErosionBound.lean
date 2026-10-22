module

public import PDEFoundation.FunctionalInequalities.SobolevSharpOne.ErosionBasic
public import PDEFoundation.Sobolev.ClassicalGradient
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.MeasureTheory.Constructions.Pi
public import PDEFoundation.Measure.BallVolume

/-!
# Erosion of `|ψ|` for a smooth compactly supported `ψ`

With `f = |ψ|` and `g = |∇ψ|` (Euclidean norm of the classical gradient) we prove
`f x - erode f h x ≤ h * (g x + modulus g h)`, vanishing outside the `h`-neighbourhood of the
support, and the integrated bound
`∫ (f - erode f h) ≤ h * (∫ g + modulus g h * |K_h|)`, together with the uniform-continuity
inclusion `{f ≥ s + modulus f h} ⊆ A_s`.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Pointwise

namespace PDE.SobolevSharp

variable {d : ℕ}

/-- The Euclidean norm of the classical gradient. -/
noncomputable def gradNorm (ψ : Vec d → ℝ) (x : Vec d) : ℝ :=
  vecEuclideanNorm (classicalGradient ψ x)

/-- The closed `h`-neighbourhood of the support of `ψ`. -/
def supportNbhd (ψ : Vec d → ℝ) (h : ℝ) : Set (Vec d) :=
  tsupport ψ + euclideanClosedBall (0 : Vec d) h

theorem continuous_abs_comp {ψ : Vec d → ℝ} (hψ : Continuous ψ) :
    Continuous fun x => |ψ x| := hψ.abs

theorem hasCompactSupport_abs_comp {ψ : Vec d → ℝ} (hc : HasCompactSupport ψ) :
    HasCompactSupport fun x => |ψ x| :=
  hc.comp_left (g := fun t : ℝ => |t|) (by simp)

theorem continuous_gradNorm {ψ : Vec d → ℝ} (hψ : ContDiff ℝ 1 ψ) :
    Continuous (gradNorm ψ) :=
  continuous_vecEuclideanNorm.comp (ContDiff.continuous_classicalGradient hψ)

theorem hasCompactSupport_gradNorm {ψ : Vec d → ℝ} (hc : HasCompactSupport ψ) :
    HasCompactSupport (gradNorm ψ) := by
  refine HasCompactSupport.intro hc fun x hx => ?_
  have hev : ψ =ᶠ[𝓝 x] fun _ => (0 : ℝ) := notMem_tsupport_iff_eventuallyEq.mp hx
  have h0 : fderiv ℝ ψ x = 0 := by
    rw [hev.fderiv_eq]; simp
  have : classicalGradient ψ x = 0 := by
    ext i; simp [h0]
  unfold gradNorm
  rw [this]; exact vecEuclideanNorm_eq_zero_iff.mpr rfl

theorem isCompact_supportNbhd {ψ : Vec d → ℝ} (hc : HasCompactSupport ψ) {h : ℝ} (hh : 0 ≤ h) :
    IsCompact (supportNbhd ψ h) :=
  IsCompact.add hc (isCompact_euclideanClosedBall (0 : Vec d) hh)

theorem measure_supportNbhd_lt_top {ψ : Vec d → ℝ} (hc : HasCompactSupport ψ) {h : ℝ}
    (hh : 0 ≤ h) : volume (supportNbhd ψ h) < ⊤ :=
  (isCompact_supportNbhd hc hh).measure_lt_top

/-- Pointwise Lipschitz-type bound for the erosion defect. -/
theorem abs_sub_erode_le {ψ : Vec d → ℝ} (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    {h : ℝ} (hh : 0 ≤ h) (x : Vec d) :
    |ψ x| - erode (fun y => |ψ y|) h x ≤ h * (gradNorm ψ x + modulus (gradNorm ψ) h) := by
  have hf := continuous_abs_comp hψ.continuous
  have hfc := hasCompactSupport_abs_comp hc
  obtain ⟨v, hv, hve⟩ := exists_eq_erode (x := x) hf hfc hh
  have hnv : vecEuclideanNorm v ≤ h := by
    have := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hh).mp hv
    rwa [sub_zero] at this
  have hω := modulus_nonneg (continuous_gradNorm hψ) (hasCompactSupport_gradNorm hc) hh
  rw [← hve]
  have h1 : |ψ x| - |ψ (x + v)| ≤ |ψ (x + v) - ψ x| := by
    exact (le_abs_self _).trans
      ((abs_abs_sub_abs_le_abs_sub (ψ x) (ψ (x + v))).trans_eq (abs_sub_comm _ _))
  -- mean value theorem along the segment
  have hderiv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => ψ (x + t • v))
      (fderiv ℝ ψ (x + t • v) v) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => x + t • v) v t := by
      simpa using ((hasDerivAt_id t).smul_const v).const_add x
    exact (hψ.differentiable (by simp) (x + t • v)).hasFDerivAt.comp_hasDerivAt t h1
  obtain ⟨c, hc01, hcd⟩ := exists_hasDerivAt_eq_slope (fun t : ℝ => ψ (x + t • v))
    (fun t => fderiv ℝ ψ (x + t • v) v) zero_lt_one
    (hψ.continuous.comp (by fun_prop : Continuous fun t : ℝ => x + t • v)).continuousOn
    (fun t _ => hderiv t)
  have hslope : fderiv ℝ ψ (x + c • v) v = ψ (x + v) - ψ x := by
    simpa using hcd
  have hcv : c • v ∈ euclideanClosedBall (0 : Vec d) h :=
    smul_mem_euclideanClosedBall_zero hv hh hc01.1.le hc01.2.le
  have hgc : gradNorm ψ (x + c • v) ≤ gradNorm ψ x + modulus (gradNorm ψ) h := by
    have := abs_sub_le_modulus (continuous_gradNorm hψ) (hasCompactSupport_gradNorm hc) hcv x
    have := (abs_le.mp this).2
    linarith
  calc |ψ x| - |ψ (x + v)| ≤ |ψ (x + v) - ψ x| := h1
    _ = |fderiv ℝ ψ (x + c • v) v| := by rw [hslope]
    _ ≤ gradNorm ψ (x + c • v) * vecEuclideanNorm v :=
        abs_fderiv_apply_le_vecEuclideanNorm_gradient_mul ψ _ v
    _ ≤ (gradNorm ψ x + modulus (gradNorm ψ) h) * h := by
        refine mul_le_mul hgc hnv (vecEuclideanNorm_nonneg v) ?_
        have := (continuous_gradNorm hψ)
        have h0 : 0 ≤ gradNorm ψ x := vecEuclideanNorm_nonneg _
        linarith
    _ = h * (gradNorm ψ x + modulus (gradNorm ψ) h) := mul_comm _ _

/-- The erosion defect vanishes away from the `h`-neighbourhood of the support. -/
theorem abs_sub_erode_eq_zero_of_notMem {ψ : Vec d → ℝ} (hψ : Continuous ψ)
    (hc : HasCompactSupport ψ) {h : ℝ} (hh : 0 ≤ h) {x : Vec d}
    (hx : x ∉ supportNbhd ψ h) : |ψ x| - erode (fun y => |ψ y|) h x = 0 := by
  have hf := continuous_abs_comp hψ
  have hfc := hasCompactSupport_abs_comp hc
  have hz : ∀ v ∈ euclideanClosedBall (0 : Vec d) h, ψ (x + v) = 0 := by
    intro v hv
    by_contra hne
    apply hx
    refine ⟨x + v, subset_tsupport _ hne, -v, neg_mem_euclideanClosedBall_zero hv hh, ?_⟩
    simp
  have h0 : ψ x = 0 := by simpa using hz 0 (zero_mem_euclideanClosedBall_zero hh)
  have : erode (fun y => |ψ y|) h x = 0 := by
    apply le_antisymm
    · simpa [h0] using erode_le_self (x := x) hf hfc hh
    · rw [le_erode_iff hf hfc hh]
      intro v hv; simp [hz v hv]
  rw [this, h0]; simp

/-- Integrated erosion defect bound. -/
theorem integral_abs_sub_erode_le {ψ : Vec d → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hc : HasCompactSupport ψ) {h : ℝ} (hh : 0 ≤ h) :
    ∫ x, (|ψ x| - erode (fun y => |ψ y|) h x) ≤
      h * ((∫ x, gradNorm ψ x) +
        modulus (gradNorm ψ) h * (volume (supportNbhd ψ h)).toReal) := by
  have hf := continuous_abs_comp hψ.continuous
  have hK := isCompact_supportNbhd hc hh
  have hgc := continuous_gradNorm hψ
  have hgcs := hasCompactSupport_gradNorm hc
  have hG : Continuous fun x => |ψ x| - erode (fun y => |ψ y|) h x :=
    hf.sub (continuous_erode hf hh)
  have hgi : Integrable (gradNorm ψ) := hgc.integrable_of_hasCompactSupport hgcs
  set ω := modulus (gradNorm ψ) h with hω
  have hω0 : 0 ≤ ω := modulus_nonneg hgc hgcs hh
  have hfin : volume (supportNbhd ψ h) < ⊤ := hK.measure_lt_top
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := supportNbhd ψ h) (fun x hx => abs_sub_erode_eq_zero_of_notMem hψ.continuous hc hh hx)]
  have hint : IntegrableOn (fun x => h * (gradNorm ψ x + ω)) (supportNbhd ψ h) :=
    (hgi.integrableOn.add (integrableOn_const hfin.ne)).const_mul h
  calc ∫ x in supportNbhd ψ h, (|ψ x| - erode (fun y => |ψ y|) h x)
      ≤ ∫ x in supportNbhd ψ h, h * (gradNorm ψ x + ω) :=
        setIntegral_mono_on (hG.continuousOn.integrableOn_compact hK) hint hK.measurableSet
          (fun x _ => abs_sub_erode_le hψ hc hh x)
    _ = h * ((∫ x in supportNbhd ψ h, gradNorm ψ x) + ω * (volume (supportNbhd ψ h)).toReal) := by
        rw [integral_const_mul, integral_add hgi.integrableOn (integrableOn_const hfin.ne),
          setIntegral_const, smul_eq_mul]
        simp only [Measure.real]
        ring
    _ ≤ h * ((∫ x, gradNorm ψ x) + ω * (volume (supportNbhd ψ h)).toReal) := by
        refine mul_le_mul_of_nonneg_left ?_ hh
        have := setIntegral_le_integral (s := supportNbhd ψ h) hgi
          (Eventually.of_forall fun x => vecEuclideanNorm_nonneg _)
        linarith

end PDE.SobolevSharp
