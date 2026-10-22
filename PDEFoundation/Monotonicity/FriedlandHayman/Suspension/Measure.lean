module

public import PDEFoundation.Monotonicity.FriedlandHayman.Suspension.Defs

/-!
# Friedland--Hayman: the suspension preserves normalized measure

Applying the projection formula to the degree-zero homogeneous extension of `1_Ω`.
-/

@[expose] public section

open MeasureTheory

namespace PDE.FHLane

noncomputable section

namespace Susp

/-- The cone over `Ω`, with the origin removed. -/
def coneSet {n : ℕ} (Ω : Set (Vec n)) : Set (Vec n) :=
  {y | y ≠ 0 ∧ (vecEuclideanNorm y)⁻¹ • y ∈ Ω}

theorem measurableSet_coneSet {n : ℕ} {Ω : Set (Vec n)} (hΩ : MeasurableSet Ω) :
    MeasurableSet (coneSet Ω) := by
  have h1 : Measurable (fun y : Vec n => (vecEuclideanNorm y)⁻¹ • y) := by
    have := measurable_vecEuclideanNorm (d := n)
    fun_prop
  exact (measurableSet_singleton (0 : Vec n)).compl.inter (hΩ.preimage h1)

theorem sphereIntegral_const {d : ℕ} (r : ℝ) :
    sphereIntegral (0 : Vec d) r (fun _ => (1 : ℝ)) = r ^ (d - 1) * sphereArea d := by
  simp [sphereIntegral, sphereArea, Internal.sphereMeasure]

theorem sphereIntegral_cone {n : ℕ} {Ω : Set (Vec n)} {r : ℝ} (hr : 0 < r) :
    sphereIntegral (0 : Vec n) r ((coneSet Ω).indicator fun _ => (1 : ℝ)) =
      r ^ (n - 1) * sphereIntegral (0 : Vec n) 1
        ((Ω ∩ euclideanSphere (0 : Vec n) 1).indicator fun _ => (1 : ℝ)) := by
  unfold sphereIntegral
  simp only [one_pow, one_mul, zero_add, one_smul]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun ω => ?_)
  have hω := vecNormSq_toVec_sphere ω
  have hnorm : vecEuclideanNorm (r • (ω : HilbertVec n).toVec) = r := by
    rw [vecEuclideanNorm_smul, abs_of_pos hr]
    have : vecEuclideanNorm (ω : HilbertVec n).toVec = 1 := by
      unfold vecEuclideanNorm; rw [hω]; exact Real.sqrt_one
    rw [this, mul_one]
  have hmem : r • (ω : HilbertVec n).toVec ∈ coneSet Ω ↔ (ω : HilbertVec n).toVec ∈ Ω := by
    have hne : r • (ω : HilbertVec n).toVec ≠ 0 := by
      intro h0
      have := congrArg vecEuclideanNorm h0
      rw [hnorm] at this
      have h00 : vecEuclideanNorm (0 : Vec n) = 0 := vecEuclideanNorm_eq_zero_iff.2 rfl
      rw [h00] at this
      exact hr.ne' this
    simp only [coneSet, Set.mem_ofPred_eq]
    rw [hnorm, inv_smul_smul₀ hr.ne']
    exact ⟨fun h => h.2, fun h => ⟨hne, h⟩⟩
  have hmem' : (ω : HilbertVec n).toVec ∈ Ω ∩ euclideanSphere (0 : Vec n) 1 ↔
      (ω : HilbertVec n).toVec ∈ Ω :=
    ⟨fun h => h.1, fun h => ⟨h, toVec_mem_sphere ω⟩⟩
  beta_reduce
  by_cases h : (ω : HilbertVec n).toVec ∈ Ω
  · rw [Set.indicator_of_mem (hmem.2 h), Set.indicator_of_mem (hmem'.2 h)]
  · rw [Set.indicator_of_notMem (fun h' => h (hmem.1 h')),
      Set.indicator_of_notMem (fun h' => h (hmem'.1 h'))]

/-- The projection of `1_{Ω_N}` is the cone indicator. -/
theorem sphereIntegral_suspension {n N : ℕ} [NeZero n] [NeZero N] {Ω : Set (Vec n)}
    (hΩ : MeasurableSet Ω) :
    sphereIntegral (0 : Vec (n + N)) 1 ((suspension n N Ω).indicator fun _ => (1 : ℝ)) =
      sphereArea N * sphereIntegral (0 : Vec n) 1
        ((Ω ∩ euclideanSphere (0 : Vec n) 1).indicator fun _ => (1 : ℝ)) *
        ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.sin θ ^ (N - 1) * Real.cos θ ^ (n - 1) := by
  have hcongr : sphereIntegral (0 : Vec (n + N)) 1 ((suspension n N Ω).indicator fun _ => (1 : ℝ)) =
      sphereIntegral (0 : Vec (n + N)) 1
        (fun x => ((coneSet Ω).indicator fun _ => (1 : ℝ)) (projFst x)) := by
    refine sphereIntegral_congr_sphere fun x hx => ?_
    have : x ∈ suspension n N Ω ↔ projFst x ∈ coneSet Ω := by
      simp only [suspension, coneSet, Set.mem_ofPred_eq]
      exact ⟨fun h => ⟨h.2.1, h.2.2⟩, fun h => ⟨hx, h.1, h.2⟩⟩
    by_cases h : x ∈ suspension n N Ω
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (this.1 h)]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (this.2 h'))]
  rw [hcongr, sphereIntegral_comp_projFst _
    ((measurable_const).indicator (measurableSet_coneSet hΩ)) ⟨1, fun y => by
      by_cases h : y ∈ coneSet Ω <;> simp [Set.indicator, h]⟩]
  have hint : ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.sin θ ^ (N - 1) *
      sphereIntegral (0 : Vec n) (Real.cos θ) ((coneSet Ω).indicator fun _ => (1 : ℝ)) =
      sphereIntegral (0 : Vec n) 1
        ((Ω ∩ euclideanSphere (0 : Vec n) 1).indicator fun _ => (1 : ℝ)) *
        ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.sin θ ^ (N - 1) * Real.cos θ ^ (n - 1) := by
    rw [← intervalIntegral.integral_const_mul]
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo,
      intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]
    refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
    have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
    rw [sphereIntegral_cone hc]
    ring
  rw [hint]
  ring

end Susp

/-- Normalized measure is preserved. -/
theorem suspension_measure {n N : ℕ} [NeZero n] [NeZero N] {Ω : Set (Vec n)}
    (hΩ : MeasurableSet Ω) :
    sphereIntegral (0 : Vec (n + N)) 1 ((suspension n N Ω).indicator fun _ => (1 : ℝ)) /
        sphereArea (n + N) =
      sphereIntegral (0 : Vec n) 1 ((Ω ∩ euclideanSphere (0 : Vec n) 1).indicator fun _ => (1 : ℝ)) /
        sphereArea n := by
  have : NeZero (n + N) := ⟨by have := NeZero.ne n; omega⟩
  set W := ∫ θ in (0 : ℝ)..(Real.pi / 2), Real.sin θ ^ (N - 1) * Real.cos θ ^ (n - 1) with hW
  have hD : sphereArea (n + N) = sphereArea N * sphereArea n * W := by
    have h := sphereIntegral_comp_projFst (n := n) (N := N) (fun _ => (1 : ℝ))
      measurable_const ⟨1, fun y => by simp⟩
    simp only [Susp.sphereIntegral_const] at h
    have h2 : ∫ θ in (0 : ℝ)..(Real.pi / 2),
        Real.sin θ ^ (N - 1) * (Real.cos θ ^ (n - 1) * sphereArea n) = W * sphereArea n := by
      rw [hW, ← intervalIntegral.integral_mul_const]
      congr 1; ext θ; ring
    rw [h2, one_pow, one_mul] at h
    rw [h]; ring
  have hpos : 0 < sphereArea N * sphereArea n * W := hD ▸ sphereArea_pos
  have hW0 : W ≠ 0 := fun h0 => by rw [h0, mul_zero] at hpos; exact lt_irrefl _ hpos
  rw [Susp.sphereIntegral_suspension hΩ, hD]
  have h1 := sphereArea_ne_zero (d := N)
  have h2 := sphereArea_ne_zero (d := n)
  rw [hW] at hW0 ⊢
  field_simp

end

end PDE.FHLane
