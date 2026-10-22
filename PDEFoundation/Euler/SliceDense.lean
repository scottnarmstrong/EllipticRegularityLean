module

public import PDEFoundation.Euler.SliceTest
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Slice identities for all test functions simultaneously

With `A, B₀, B₁ ∈ L¹(eulerMeasure T)` as in `SliceTest`, the weak identity against all admissible space-time
test functions implies: for a.e. `t ∈ [0,T]` and **every** smooth periodic `φ`,
`∫_cube (A φ + B₀ ∂₁φ + B₁ ∂₂φ)(x,t) dx = 0`.  The null set is made independent of `φ` by a countable set
of test functions that is dense in the `C¹(cube)`-topology (separability of `C(cube, ℝ³)`).
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

theorem integrable_mul_cont_cube {a g : Vec 2 → ℝ} (ha : Integrable a (volume.restrict torusCube))
    (hg : Continuous g) : Integrable (fun x => a x * g x) (volume.restrict torusCube) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact torusCube).exists_bound_of_continuousOn hg.continuousOn
  refine ha.mul_bdd (c := C) hg.aestronglyMeasurable ?_
  exact (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall hC)

theorem abs_sliceDiff_le {a₀ a₁ a₂ : Vec 2 → ℝ} (h₀ : Integrable a₀ (volume.restrict torusCube))
    (h₁ : Integrable a₁ (volume.restrict torusCube)) (h₂ : Integrable a₂ (volume.restrict torusCube))
    {φ φ' : Vec 2 → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφ' : ContDiff ℝ (⊤ : ℕ∞) φ') {δ : ℝ}
    (hδ : ∀ x ∈ torusCube, |φ x - φ' x| ≤ δ ∧ |pd 0 φ x - pd 0 φ' x| ≤ δ ∧
      |pd 1 φ x - pd 1 φ' x| ≤ δ) :
    |(∫ x in torusCube, (a₀ x * φ x + a₁ x * pd 0 φ x + a₂ x * pd 1 φ x)) -
        ∫ x in torusCube, (a₀ x * φ' x + a₁ x * pd 0 φ' x + a₂ x * pd 1 φ' x)| ≤
      δ * ∫ x in torusCube, (|a₀ x| + |a₁ x| + |a₂ x|) := by
  have hc0 : ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → Continuous ψ := fun ψ h => h.continuous
  have hc1 : ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → ∀ j, Continuous (pd j ψ) :=
    fun ψ h j => (contDiff_pd_top h j).continuous
  have hI : ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      Integrable (fun x => a₀ x * ψ x + a₁ x * pd 0 ψ x + a₂ x * pd 1 ψ x) (volume.restrict torusCube) :=
    fun ψ h => ((integrable_mul_cont_cube h₀ (hc0 ψ h)).add
      (integrable_mul_cont_cube h₁ (hc1 ψ h 0))).add (integrable_mul_cont_cube h₂ (hc1 ψ h 1))
  have hsub := integral_sub (hI φ hφ) (hI φ' hφ')
  rw [← hsub]
  have hbound : Integrable (fun x => δ * (|a₀ x| + |a₁ x| + |a₂ x|)) (volume.restrict torusCube) :=
    ((h₀.abs.add h₁.abs).add h₂.abs).const_mul δ
  rw [← integral_const_mul]
  have := norm_integral_le_of_norm_le (μ := volume.restrict torusCube) hbound
    (f := fun x => (a₀ x * φ x + a₁ x * pd 0 φ x + a₂ x * pd 1 φ x) -
      (a₀ x * φ' x + a₁ x * pd 0 φ' x + a₂ x * pd 1 φ' x)) ?_
  · simpa [Real.norm_eq_abs] using this
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
    obtain ⟨e0, e1, e2⟩ := hδ x hx
    have : (a₀ x * φ x + a₁ x * pd 0 φ x + a₂ x * pd 1 φ x) -
        (a₀ x * φ' x + a₁ x * pd 0 φ' x + a₂ x * pd 1 φ' x) =
        a₀ x * (φ x - φ' x) + a₁ x * (pd 0 φ x - pd 0 φ' x) + a₂ x * (pd 1 φ x - pd 1 φ' x) := by ring
    rw [this, Real.norm_eq_abs]
    calc |a₀ x * (φ x - φ' x) + a₁ x * (pd 0 φ x - pd 0 φ' x) + a₂ x * (pd 1 φ x - pd 1 φ' x)|
        ≤ |a₀ x * (φ x - φ' x)| + |a₁ x * (pd 0 φ x - pd 0 φ' x)| + |a₂ x * (pd 1 φ x - pd 1 φ' x)| :=
          (abs_add_three _ _ _)
      _ ≤ |a₀ x| * δ + |a₁ x| * δ + |a₂ x| * δ := by
          rw [abs_mul, abs_mul, abs_mul]
          gcongr
      _ = δ * (|a₀ x| + |a₁ x| + |a₂ x|) := by ring

/-- The `C¹(cube)`-jet of a smooth periodic function, as an element of `C(cube, ℝ³)`. -/
noncomputable def jetCube (φ : {φ : Vec 2 → ℝ // ContDiff ℝ (⊤ : ℕ∞) φ ∧ IsTorusPeriodic φ}) :
    C(torusCube, ℝ × ℝ × ℝ) :=
  ⟨fun x => (φ.1 x, pd 0 φ.1 x, pd 1 φ.1 x), by
    have h0 := φ.2.1.continuous
    have h1 : ∀ j, Continuous (pd j φ.1) := fun j => (contDiff_pd_top φ.2.1 j).continuous
    exact (h0.comp continuous_subtype_val).prodMk
      (((h1 0).comp continuous_subtype_val).prodMk ((h1 1).comp continuous_subtype_val))⟩

theorem ae_forall_sliceFunctional_eq_zero {T : ℝ} (hT : 0 < T) {A B₀ B₁ : Vec 2 × ℝ → ℝ}
    (hA : Integrable A (eulerMeasure T)) (hB₀ : Integrable B₀ (eulerMeasure T))
    (hB₁ : Integrable B₁ (eulerMeasure T))
    (hweak : ∀ ψ : Vec 2 × ℝ → ℝ, IsPeriodicSmooth ψ → VanishesOutsideInterior T ψ →
      ∫ z, (A z * ψ z + B₀ z * fderiv ℝ ψ z (basisVec 0, 0) + B₁ z * fderiv ℝ ψ z (basisVec 1, 0))
        ∂(eulerMeasure T) = 0) :
    ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), ∀ φ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ →
      IsTorusPeriodic φ → sliceFunctional A B₀ B₁ φ t = 0 := by
  have : CompactSpace torusCube := isCompact_iff_compactSpace.mp isCompact_Icc
  set S : Set C(torusCube, ℝ × ℝ × ℝ) := Set.range jetCube with hS
  have hsep : TopologicalSpace.IsSeparable S := TopologicalSpace.IsSeparable.of_separableSpace S
  obtain ⟨D, hDS, hDc, hSD⟩ := hsep.exists_countable_dense_subset
  -- good times for the dense family
  have hD : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), ∀ d ∈ D, ∀ φ : {φ : Vec 2 → ℝ //
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ IsTorusPeriodic φ}, jetCube φ = d → sliceFunctional A B₀ B₁ φ.1 t = 0 := by
    rw [ae_ball_iff hDc]
    intro d hd
    obtain ⟨φ₀, rfl⟩ := hDS hd
    filter_upwards [ae_sliceFunctional_eq_zero hT hA hB₀ hB₁ hweak φ₀.2.1 φ₀.2.2] with t ht φ hφ
    have hcongr : ∀ x ∈ torusCube, φ.1 x = φ₀.1 x ∧ pd 0 φ.1 x = pd 0 φ₀.1 x ∧ pd 1 φ.1 x = pd 1 φ₀.1 x := by
      intro x hx
      have := congrArg (fun f : C(torusCube, ℝ × ℝ × ℝ) => f ⟨x, hx⟩) hφ
      simp only [jetCube, ContinuousMap.coe_mk, Prod.mk.injEq] at this
      exact this
    rw [← ht]
    unfold sliceFunctional
    refine setIntegral_congr_fun measurableSet_Icc fun x hx => ?_
    obtain ⟨e0, e1, e2⟩ := hcongr x hx
    simp only [e0, e1, e2]
  have hint : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)),
      Integrable (fun x => A (x, t)) (volume.restrict torusCube) ∧
      Integrable (fun x => B₀ (x, t)) (volume.restrict torusCube) ∧
      Integrable (fun x => B₁ (x, t)) (volume.restrict torusCube) := by
    have prod_eq : eulerMeasure T = (volume.restrict torusCube).prod (volume.restrict (Icc (0 : ℝ) T)) :=
      eulerMeasure_eq_prod T
    rw [prod_eq] at hA hB₀ hB₁
    filter_upwards [hA.prod_left_ae, hB₀.prod_left_ae, hB₁.prod_left_ae] with t h1 h2 h3
    exact ⟨h1, h2, h3⟩
  filter_upwards [hD, hint] with t htD ⟨h1, h2, h3⟩
  intro φ hφ hp
  set N : ℝ := ∫ x in torusCube, (|A (x, t)| + |B₀ (x, t)| + |B₁ (x, t)|) with hN
  have hN0 : 0 ≤ N := setIntegral_nonneg measurableSet_Icc fun x _ => by positivity
  have hmain : ∀ ε : ℝ, 0 < ε → |sliceFunctional A B₀ B₁ φ t| ≤ ε * N := by
    intro ε hε
    have hmem : jetCube ⟨φ, hφ, hp⟩ ∈ closure D := hSD ⟨⟨φ, hφ, hp⟩, rfl⟩
    obtain ⟨d, hdD, hdist⟩ := Metric.mem_closure_iff.mp hmem ε hε
    obtain ⟨φ', hφ'⟩ := hDS hdD
    have h0 := htD d hdD φ' hφ'
    have hsup : ∀ x ∈ torusCube, |φ x - φ'.1 x| ≤ ε ∧ |pd 0 φ x - pd 0 φ'.1 x| ≤ ε ∧
        |pd 1 φ x - pd 1 φ'.1 x| ≤ ε := by
      intro x hx
      have hle := ContinuousMap.norm_coe_le_norm (jetCube ⟨φ, hφ, hp⟩ - jetCube φ') ⟨x, hx⟩
      have hnorm : ‖jetCube ⟨φ, hφ, hp⟩ - jetCube φ'‖ < ε := by
        rw [← dist_eq_norm, hφ']; exact hdist
      have hlt := lt_of_le_of_lt hle hnorm
      simp only [ContinuousMap.sub_apply, jetCube, ContinuousMap.coe_mk] at hlt
      refine ⟨?_, ?_, ?_⟩
      · have := (norm_fst_le _).trans_lt hlt
        rw [Real.norm_eq_abs] at this
        exact this.le
      · have := ((norm_fst_le _).trans (norm_snd_le _)).trans_lt hlt
        rw [Real.norm_eq_abs] at this
        exact this.le
      · have := ((norm_snd_le _).trans (norm_snd_le _)).trans_lt hlt
        rw [Real.norm_eq_abs] at this
        exact this.le
    have := abs_sliceDiff_le h1 h2 h3 hφ φ'.2.1 hsup
    unfold sliceFunctional at h0 ⊢
    rw [h0, sub_zero] at this
    exact this
  by_contra hne
  have hpos : 0 < |sliceFunctional A B₀ B₁ φ t| := abs_pos.mpr hne
  have := hmain (|sliceFunctional A B₀ B₁ φ t| / (N + 1)) (by positivity)
  have hN1 : 0 < N + 1 := by linarith
  have h2 : |sliceFunctional A B₀ B₁ φ t| / (N + 1) * N < |sliceFunctional A B₀ B₁ φ t| := by
    rw [div_mul_eq_mul_div, div_lt_iff₀ hN1]
    nlinarith
  linarith

end PDE
