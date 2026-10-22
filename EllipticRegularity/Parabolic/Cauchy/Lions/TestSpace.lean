module

public import EllipticRegularity.Parabolic.CauchyDef
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.MeasureTheory.SpecificCodomains.WithLp

/-! # Cauchy test functions for the Lions construction

The tests are globally `C¹` and compactly supported in space-time, are permitted to be nonzero at
the initial time, and vanish at the final time. The value/gradient pair uses the existing
`PDE.HilbertVec` bridge for the Euclidean norm on native vectors.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set
open scoped InnerProductSpace

namespace PDE.Parabolic.Lions

/-- Space-time volume restricted to the finite Cauchy horizon. -/
noncomputable abbrev slabMeasure (d : ℕ) (s T : ℝ) : Measure (Vec d × ℝ) :=
  (volume : Measure (Vec d × ℝ)).restrict (univ ×ˢ Icc s T)

/-- Smooth compactly supported test functions that vanish at the terminal time. -/
def CauchyTestSpace (d : ℕ) (_s : ℝ) (T : ℝ) : Submodule ℝ (Vec d × ℝ → ℝ) where
  carrier := {φ | ContDiff ℝ 1 φ ∧ HasCompactSupport φ ∧ ∀ x, φ (x, T) = 0}
  add_mem' hφ hψ := ⟨hφ.1.add hψ.1, hφ.2.1.add hψ.2.1, fun x => by
    rw [Pi.add_apply, hφ.2.2 x, hψ.2.2 x, add_zero]
  ⟩
  zero_mem' := ⟨contDiff_const, HasCompactSupport.zero, fun _ => rfl⟩
  smul_mem' := by
    intro c φ hφ
    exact ⟨contDiff_const.smul hφ.1, hφ.2.1.smul_left, fun x => by
      rw [Pi.smul_apply, smul_eq_mul, hφ.2.2 x, mul_zero]⟩

/-- Continuous compact support follows when a function vanishes off a compact set. -/
theorem hasCompactSupport_of_zero_off {α E : Type*} [TopologicalSpace α] [Zero E]
    [R1Space α] {f : α → E} {K : Set α} (hK : IsCompact K)
    (hf : ∀ x, x ∉ K → f x = 0) :
    HasCompactSupport f := by
  exact HasCompactSupport.of_support_subset_isCompact hK fun x hx => by
    by_contra hxK
    exact hx (by simp [hf x hxK])

/-- The time derivative is continuous for a `C¹` space-time function. -/
theorem continuous_parTimeDeriv {d : ℕ} {φ : Vec d × ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) : Continuous (parTimeDeriv φ) := by
  exact (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const

/-- The spatial gradient is continuous for a `C¹` space-time function. -/
theorem continuous_parSpaceGrad {d : ℕ} {φ : Vec d × ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) : Continuous (parSpaceGrad φ) := by
  exact continuous_pi fun i =>
    (hφ.continuous_fderiv (by norm_num)).clm_apply continuous_const

theorem parTimeDeriv_add {d : ℕ} {φ ψ : Vec d × ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hψ : ContDiff ℝ 1 ψ) :
    parTimeDeriv (φ + ψ) = parTimeDeriv φ + parTimeDeriv ψ := by
  funext z
  simp only [parTimeDeriv, Pi.add_apply]
  rw [fderiv_add (hφ.differentiable (by norm_num) z) (hψ.differentiable (by norm_num) z)]
  rfl

theorem parSpaceGrad_add {d : ℕ} {φ ψ : Vec d × ℝ → ℝ}
    (hφ : ContDiff ℝ 1 φ) (hψ : ContDiff ℝ 1 ψ) :
    parSpaceGrad (φ + ψ) = parSpaceGrad φ + parSpaceGrad ψ := by
  funext z i
  simp only [parSpaceGrad, Pi.add_apply]
  rw [fderiv_add (hφ.differentiable (by norm_num) z) (hψ.differentiable (by norm_num) z)]
  rfl

theorem parTimeDeriv_smul {d : ℕ} (c : ℝ) (φ : Vec d × ℝ → ℝ) :
    parTimeDeriv (c • φ) = c • parTimeDeriv φ := by
  funext z
  simp only [parTimeDeriv, Pi.smul_apply, smul_eq_mul]
  rw [fderiv_const_smul_field]
  rfl

theorem parSpaceGrad_smul {d : ℕ} (c : ℝ) (φ : Vec d × ℝ → ℝ) :
    parSpaceGrad (c • φ) = c • parSpaceGrad φ := by
  funext z i
  simp only [parSpaceGrad, Pi.smul_apply, smul_eq_mul]
  rw [fderiv_const_smul_field]
  rfl

/-- The initial trace of a Cauchy test. -/
noncomputable def initialTrace {d : ℕ} (s : ℝ) (φ : Vec d × ℝ → ℝ) : Vec d → ℝ :=
  fun x => φ (x, s)

/-- The initial trace is continuous and compactly supported in space. -/
theorem initialTrace_continuous_hasCompactSupport {d : ℕ} {s T : ℝ}
    {φ : CauchyTestSpace d s T} :
    Continuous (initialTrace s (φ : Vec d × ℝ → ℝ)) ∧
      HasCompactSupport (initialTrace s (φ : Vec d × ℝ → ℝ)) := by
  have hφc : Continuous (φ : Vec d × ℝ → ℝ) := φ.2.1.continuous
  refine ⟨hφc.comp (continuous_id.prodMk continuous_const), ?_⟩
  let K : Set (Vec d) := Prod.fst '' tsupport (φ : Vec d × ℝ → ℝ)
  have hK : IsCompact K := by
    dsimp [K]
    exact (φ.2.2.1.isCompact.image continuous_fst)
  apply hasCompactSupport_of_zero_off hK
  intro x hxK
  have hxφ : (x, s) ∉ tsupport (φ : Vec d × ℝ → ℝ) := by
    intro hmem
    apply hxK
    exact ⟨(x, s), hmem, rfl⟩
  simpa [initialTrace] using image_eq_zero_of_notMem_tsupport hxφ

/-- A `C¹_c` scalar function on space-time is square integrable on the slab. -/
theorem memLp_slab_of_continuous_compact {d : ℕ} {s T : ℝ} {f : Vec d × ℝ → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) : MemLp f 2 (slabMeasure d s T) := by
  exact hf.memLp_of_hasCompactSupport hfc

/-- A compactly supported continuous spatial function is in `L²(ℝᵈ)`. -/
theorem memLp_space_of_continuous_compact {d : ℕ} {f : Vec d → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) : MemLp f 2 (volume : Measure (Vec d)) :=
  hf.memLp_of_hasCompactSupport hfc

end PDE.Parabolic.Lions
