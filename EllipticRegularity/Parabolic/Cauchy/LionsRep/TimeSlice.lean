module

public import EllipticRegularity.Parabolic.Cauchy.Lions.ClosureData
public import EllipticRegularity.Parabolic.Cauchy.LionsRep.ScalarTracePairing
public import Mathlib.Analysis.Normed.Operator.Extend
public import Mathlib.Analysis.InnerProductSpace.Dual

/-! # Every-time spatial `L²` classes from the scalar trace -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set
open scoped ENNReal ContDiff

namespace PDE.Parabolic.LionsRep

/-- Smooth compactly supported functions as a real linear subspace of the function space. -/
def smoothCompactSubmodule (d : ℕ) : Submodule ℝ (Vec d → ℝ) where
  carrier := {φ | HasCompactSupport φ ∧ ContDiff ℝ 1 φ}
  zero_mem' := by
    constructor
    · exact HasCompactSupport.zero
    · exact contDiff_const
  add_mem' := by
    intro φ ψ hφ hψ
    exact ⟨hφ.1.add hψ.1, hφ.2.add hψ.2⟩
  smul_mem' := by
    intro c φ hφ
    exact ⟨hφ.1.smul_left, hφ.2.const_smul c⟩

theorem smoothCompact_spec {d : ℕ} (φ : smoothCompactSubmodule d) :
    HasCompactSupport (φ : Vec d → ℝ) ∧ ContDiff ℝ 1 (φ : Vec d → ℝ) :=
  φ.property

theorem smoothCompact_memLp {d : ℕ} (φ : smoothCompactSubmodule d) :
    MemLp (φ : Vec d → ℝ) 2 (volume : Measure (Vec d)) :=
  (smoothCompact_spec φ).2.continuous.memLp_of_hasCompactSupport
    (smoothCompact_spec φ).1

/-- The dense linear map that sends a smooth compact test to its `L²` class. -/
noncomputable def smoothCompactEmbedding (d : ℕ) :
    smoothCompactSubmodule d →ₗ[ℝ] Lp ℝ 2 (volume : Measure (Vec d)) where
  toFun φ := (smoothCompact_memLp φ).toLp (φ : Vec d → ℝ)
  map_add' φ ψ := by
    exact MemLp.toLp_add (smoothCompact_memLp φ) (smoothCompact_memLp ψ)
  map_smul' c φ := by
    exact MemLp.toLp_const_smul c (smoothCompact_memLp φ)

theorem smoothCompactEmbedding_denseRange (d : ℕ) :
    DenseRange (smoothCompactEmbedding d) := by
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  have hdense := Lp.dense_hasCompactSupport_contDiff (E := Vec d) (F := ℝ)
    (p := 2) (μ := (volume : Measure (Vec d)))
    (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  apply hdense.mono
  rintro q ⟨g, hqg, hgc, hgd⟩
  let φ : smoothCompactSubmodule d := ⟨g, hgc, hgd.of_le (by norm_num)⟩
  let hg : MemLp g 2 (volume : Measure (Vec d)) :=
    hgd.continuous.memLp_of_hasCompactSupport hgc
  have hq : q = hg.toLp g := Lp.ext (hqg.trans hg.coeFn_toLp.symm)
  have he : smoothCompactEmbedding d φ = hg.toLp g := by
    change (smoothCompact_memLp φ).toLp (φ : Vec d → ℝ) = hg.toLp g
    apply Lp.ext
    filter_upwards [(smoothCompact_memLp φ).coeFn_toLp] with x hφx
    rw [hφx]
  refine ⟨φ, ?_⟩
  exact (hq.trans he.symm).symm

/-- A smooth-test functional equipped with its `L²` norm bound. -/
structure BoundedSmoothTrace (d : ℕ) where
  trace : smoothCompactSubmodule d →ₗ[ℝ] ℝ
  trace_bound : ∃ C, ∀ φ, ‖trace φ‖ ≤ C * ‖smoothCompactEmbedding d φ‖

/-- Extend a bounded smooth-test functional to all of whole-space `L²`. -/
noncomputable def BoundedSmoothTrace.extend {d : ℕ}
    (F : BoundedSmoothTrace d) : Lp ℝ 2 (volume : Measure (Vec d)) →L[ℝ] ℝ :=
  LinearMap.extendOfNorm
    (F.trace : smoothCompactSubmodule d →ₛₗ[RingHom.id ℝ] ℝ)
    (smoothCompactEmbedding d)

/-- On smooth tests the extension agrees with the original functional. -/
theorem BoundedSmoothTrace.extend_apply {d : ℕ}
    (F : BoundedSmoothTrace d) (φ : smoothCompactSubmodule d) :
    F.extend (smoothCompactEmbedding d φ) = F.trace φ :=
  LinearMap.extendOfNorm_eq (smoothCompactEmbedding_denseRange d) F.trace_bound φ

/-- The smooth-test trace as a linear functional on smooth compactly supported representatives. -/
noncomputable def cauchySmoothTraceMap
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (t : Icc s T) : smoothCompactSubmodule d →ₗ[ℝ] ℝ where
  toFun φ := cauchyScalarTrace hsT ha f hf u hrep (φ : Vec d → ℝ)
    (smoothCompact_spec φ).2 (smoothCompact_spec φ).1 t
  map_add' φ ψ := by
    exact cauchyScalarTrace_add hsT ha f hf u hrep
      (φ : Vec d → ℝ) (ψ : Vec d → ℝ)
      (smoothCompact_spec φ).2 (smoothCompact_spec φ).1
      (smoothCompact_spec ψ).2 (smoothCompact_spec ψ).1 t t.property
  map_smul' c φ := by
    exact cauchyScalarTrace_smul hsT ha f hf u hrep c
      (φ : Vec d → ℝ) (smoothCompact_spec φ).2 (smoothCompact_spec φ).1
      t t.property

theorem cauchySmoothTraceMap_apply
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (t : Icc s T) (φ : smoothCompactSubmodule d) :
    cauchySmoothTraceMap hsT ha f hf u hrep t φ =
      cauchyScalarTrace hsT ha f hf u hrep (φ : Vec d → ℝ)
        (smoothCompact_spec φ).2 (smoothCompact_spec φ).1 t := rfl

attribute [irreducible] cauchySmoothTraceMap

theorem cauchySmoothTraceMap_norm_bound
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T) {u₀ : PDE.Parabolic.Lions.CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (t : Icc s T) (φ : smoothCompactSubmodule d) :
    ‖cauchySmoothTraceMap hsT ha f hf u hrep t φ‖ ≤
      Real.sqrt (cauchySliceEnergyBound (a := a) f u) *
        ‖smoothCompactEmbedding d φ‖ := by
  rw [Real.norm_eq_abs]
  have h := cauchyScalarTrace_norm_bound hsT ha f hf u hclose hrep
    (φ : Vec d → ℝ) (smoothCompact_spec φ).2 (smoothCompact_spec φ).1 t t.property
  simpa [cauchySmoothTraceMap, smoothCompactEmbedding, Lp.norm_toLp] using h

/-- The time-`t` Lions trace together with its energy-based norm bound. -/
noncomputable def cauchyBoundedSmoothTrace
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T) {u₀ : PDE.Parabolic.Lions.CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (t : Icc s T) : BoundedSmoothTrace d where
  trace := cauchySmoothTraceMap hsT ha f hf u hrep t
  trace_bound := ⟨Real.sqrt (cauchySliceEnergyBound (a := a) f u), fun φ =>
    cauchySmoothTraceMap_norm_bound hsT ha f hf u hclose hrep t φ⟩

/-- Extend the time-`t` smooth-test trace to a bounded functional on whole-space `L²`. -/
noncomputable def cauchyL2PairingFunctional
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T) {u₀ : PDE.Parabolic.Lions.CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (t : Icc s T) : Lp ℝ 2 (volume : Measure (Vec d)) →L[ℝ] ℝ :=
  (cauchyBoundedSmoothTrace hsT ha f hf u hclose hrep t).extend

/-- The functional extension retains the continuous scalar trace on smooth compact tests. -/
theorem cauchyL2PairingFunctional_smooth
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T) {u₀ : PDE.Parabolic.Lions.CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (t : Icc s T) (φ : smoothCompactSubmodule d) :
    cauchyL2PairingFunctional hsT ha f hf u hclose hrep t
      (smoothCompactEmbedding d φ) =
      cauchyScalarTrace hsT ha f hf u hrep (φ : Vec d → ℝ)
        (smoothCompact_spec φ).2 (smoothCompact_spec φ).1 t := by
  rw [cauchyL2PairingFunctional, BoundedSmoothTrace.extend_apply]
  change cauchySmoothTraceMap hsT ha f hf u hrep t φ = _
  exact cauchySmoothTraceMap_apply hsT ha f hf u hrep t φ

/-- Riesz representation, abstracted so the application only handles its Hilbert-space instance. -/
noncomputable def hilbertDualRepresentative
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (L : E →L[ℝ] ℝ) : E :=
  (InnerProductSpace.toDual ℝ E).symm L

theorem hilbertDualRepresentative_pairing
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (L : E →L[ℝ] ℝ) (x : E) :
    inner ℝ (hilbertDualRepresentative L) x = L x := by
  rw [hilbertDualRepresentative, InnerProductSpace.toDual_symm_apply]

/-- The Riesz slice associated with the continuous scalar pairings at each time. -/
noncomputable def cauchyL2TimeSlice
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T) {u₀ : PDE.Parabolic.Lions.CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (t : Icc s T) : Lp ℝ 2 (volume : Measure (Vec d)) :=
  hilbertDualRepresentative
    (cauchyL2PairingFunctional hsT ha f hf u hclose hrep t)

/-- Pairing the Riesz slice with a smooth compact test recovers its all-time scalar trace. -/
theorem cauchyL2TimeSlice_pairing_smooth
    {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume)
    (u : PDE.Parabolic.Lions.CauchyX d s T) {u₀ : PDE.Parabolic.Lions.CauchyY d}
    (hclose : PDE.Parabolic.Lions.CauchyClosure u u₀)
    (hrep : PDE.Parabolic.Lions.CauchyRepresents ha f hf u)
    (t : Icc s T) (φ : smoothCompactSubmodule d) :
    inner ℝ (cauchyL2TimeSlice hsT ha f hf u hclose hrep t)
        (smoothCompactEmbedding d φ) =
      cauchyScalarTrace hsT ha f hf u hrep (φ : Vec d → ℝ)
        (smoothCompact_spec φ).2 (smoothCompact_spec φ).1 t := by
  change inner ℝ
      (hilbertDualRepresentative
        (cauchyL2PairingFunctional hsT ha f hf u hclose hrep t))
      (smoothCompactEmbedding d φ) = _
  rw [hilbertDualRepresentative_pairing]
  exact cauchyL2PairingFunctional_smooth hsT ha f hf u hclose hrep t φ

end PDE.Parabolic.LionsRep
