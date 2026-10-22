module

public import PDEFoundation.Monotonicity.Defs
public import PDEFoundation.Monotonicity.Core.BallDivergence
public import PDEFoundation.Analysis.HilbertSphereAverage

/-!
# The one-dimensional sphere

In dimension one the unit sphere of `HilbertVec 1` consists of the two points `±e`, each of mass
one for `Measure.toSphere`.  Hence `sphereIntegral x r f = f (x + r e) + f (x - r e)` and
`sphereMean x r f = (f (x + r e) + f (x - r e)) / 2`, where `e = basisVec 0`.
-/

@[expose] public section

open MeasureTheory Set
open scoped Pointwise

namespace PDE

noncomputable section

namespace OneDim

/-- The unit vector of `HilbertVec 1`. -/
def unitVec : HilbertVec 1 := (basisVec (0 : Fin 1)).toHilbertVec

theorem unitVec_toVec : unitVec.toVec = basisVec (0 : Fin 1) := rfl

theorem norm_unitVec : ‖unitVec‖ = 1 := by
  rw [HilbertVec.norm_eq_vecEuclideanNorm, unitVec_toVec]
  simp [vecEuclideanNorm, vecNormSq, vecDot, basisVec]

theorem mem_sphere_unitVec : unitVec ∈ Metric.sphere (0 : HilbertVec 1) 1 := by
  simp [norm_unitVec]

theorem mem_sphere_neg_unitVec : -unitVec ∈ Metric.sphere (0 : HilbertVec 1) 1 := by
  simp [norm_unitVec]

theorem eq_unitVec_or_neg (ω : Metric.sphere (0 : HilbertVec 1) 1) :
    (ω : HilbertVec 1) = unitVec ∨ (ω : HilbertVec 1) = -unitVec := by
  have hn : ‖(ω : HilbertVec 1)‖ = 1 := mem_sphere_zero_iff_norm.mp ω.2
  rw [HilbertVec.norm_eq_vecEuclideanNorm] at hn
  have h2 : ((ω : HilbertVec 1) 0) ^ 2 = 1 := by
    have := congrArg (· ^ 2) hn
    simp only [vecEuclideanNorm_sq] at this
    simpa [vecNormSq, vecDot, sq] using this
  have : (ω : HilbertVec 1) 0 = 1 ∨ (ω : HilbertVec 1) 0 = -1 := by
    exact sq_eq_sq_iff_eq_or_eq_neg.1 (h2.trans (one_pow 2).symm)
  rcases this with h | h
  · left; ext i; fin_cases i; simpa [unitVec, Vec.toHilbertVec, basisVec] using h
  · right; ext i; fin_cases i; simpa [unitVec, Vec.toHilbertVec, basisVec] using h

theorem finrank_hilbertVec_one : Module.finrank ℝ (HilbertVec 1) = 1 := by
  calc Module.finrank ℝ (HilbertVec 1) = Module.finrank ℝ (Fin 1 → ℝ) :=
        (WithLp.linearEquiv 2 ℝ (Fin 1 → ℝ)).finrank_eq
    _ = 1 := by simp

theorem volume_cone_unitVec :
    volume (Set.Ioo (0 : ℝ) 1 • ({unitVec} : Set (HilbertVec 1))) = 1 := by
  have hset : Set.Ioo (0 : ℝ) 1 • ({unitVec} : Set (HilbertVec 1)) =
      (WithLp.ofLp (p := 2) (V := Fin 1 → ℝ)) ⁻¹'
        (Set.pi Set.univ fun _ : Fin 1 => Set.Ioo (0 : ℝ) 1) := by
    ext z
    simp only [Set.smul_singleton, Set.mem_image, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
      forall_true_left]
    constructor
    · rintro ⟨t, ht, rfl⟩ i
      fin_cases i
      simpa [unitVec, Vec.toHilbertVec, basisVec] using ht
    · intro h
      refine ⟨z 0, h 0, ?_⟩
      ext i; fin_cases i; simp [unitVec, Vec.toHilbertVec, basisVec]
  rw [hset, (PiLp.volume_preserving_ofLp (Fin 1)).measure_preimage
    (MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Ioo).nullMeasurableSet,
    Real.volume_pi_Ioo]
  simp

theorem volume_cone_neg_unitVec :
    volume (Set.Ioo (0 : ℝ) 1 • ({-unitVec} : Set (HilbertVec 1))) = 1 := by
  have hset : Set.Ioo (0 : ℝ) 1 • ({-unitVec} : Set (HilbertVec 1)) =
      (WithLp.ofLp (p := 2) (V := Fin 1 → ℝ)) ⁻¹'
        (Set.pi Set.univ fun _ : Fin 1 => Set.Ioo (-1 : ℝ) 0) := by
    ext z
    simp only [Set.smul_singleton, Set.mem_image, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
      forall_true_left]
    constructor
    · rintro ⟨t, ht, rfl⟩ i
      fin_cases i
      simp only [unitVec, Vec.toHilbertVec, basisVec]
      simp only [Fin.zero_eta, Fin.isValue, PiLp.smul_apply, PiLp.neg_apply,
        Pi.single_eq_same, smul_eq_mul, mul_neg, mul_one, Set.mem_Ioo, neg_lt_neg_iff,
        neg_lt_zero]
      exact ⟨ht.2, ht.1⟩
    · intro h
      refine ⟨-(z 0), ⟨by linarith only [(h 0).2], by linarith only [(h 0).1]⟩, ?_⟩
      ext i; fin_cases i; simp [unitVec, Vec.toHilbertVec, basisVec]
  rw [hset, (PiLp.volume_preserving_ofLp (Fin 1)).measure_preimage
    (MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Ioo).nullMeasurableSet,
    Real.volume_pi_Ioo]
  simp

theorem sphereMeasure_singleton_unitVec :
    Internal.sphereMeasure 1 {⟨unitVec, mem_sphere_unitVec⟩} = 1 := by
  unfold Internal.sphereMeasure
  rw [Measure.toSphere_apply' _ (measurableSet_singleton _), finrank_hilbertVec_one]
  have : (Subtype.val : Metric.sphere (0 : HilbertVec 1) 1 → HilbertVec 1) ''
      {⟨unitVec, mem_sphere_unitVec⟩} = {unitVec} := Set.image_singleton
  rw [this, volume_cone_unitVec]
  simp

theorem sphereMeasure_singleton_neg_unitVec :
    Internal.sphereMeasure 1 {⟨-unitVec, mem_sphere_neg_unitVec⟩} = 1 := by
  unfold Internal.sphereMeasure
  rw [Measure.toSphere_apply' _ (measurableSet_singleton _), finrank_hilbertVec_one]
  have : (Subtype.val : Metric.sphere (0 : HilbertVec 1) 1 → HilbertVec 1) ''
      {⟨-unitVec, mem_sphere_neg_unitVec⟩} = {-unitVec} := Set.image_singleton
  rw [this, volume_cone_neg_unitVec]
  simp

theorem unitVec_ne_neg : unitVec ≠ -unitVec := by
  intro h
  have := congrArg (fun z : HilbertVec 1 => z 0) h
  simp [unitVec, Vec.toHilbertVec, basisVec] at this
  linarith only [this]

/-- Integration over the unit sphere of `HilbertVec 1`: two points of mass one. -/
theorem integral_sphereMeasure_one (h : Metric.sphere (0 : HilbertVec 1) 1 → ℝ) :
    ∫ ω, h ω ∂(Internal.sphereMeasure 1) =
      h ⟨unitVec, mem_sphere_unitVec⟩ + h ⟨-unitVec, mem_sphere_neg_unitVec⟩ := by
  have hfin : (Metric.sphere (0 : HilbertVec 1) 1).Finite :=
    (Set.toFinite {unitVec, -unitVec}).subset fun ω hω => by
      rcases eq_unitVec_or_neg ⟨ω, hω⟩ with h | h
      · exact Or.inl h
      · exact Or.inr h
  have : Finite (Metric.sphere (0 : HilbertVec 1) 1) := hfin.to_subtype
  have : Fintype (Metric.sphere (0 : HilbertVec 1) 1) := Fintype.ofFinite _
  rw [integral_fintype Integrable.of_finite]
  have huniv : (Finset.univ : Finset (Metric.sphere (0 : HilbertVec 1) 1)) =
      {⟨unitVec, mem_sphere_unitVec⟩, ⟨-unitVec, mem_sphere_neg_unitVec⟩} := by
    ext ω
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    rcases eq_unitVec_or_neg ω with h | h
    · left; exact Subtype.ext h
    · right; exact Subtype.ext h
  have hne : (⟨unitVec, mem_sphere_unitVec⟩ : Metric.sphere (0 : HilbertVec 1) 1) ≠
      ⟨-unitVec, mem_sphere_neg_unitVec⟩ := fun h => unitVec_ne_neg (congrArg Subtype.val h)
  rw [huniv, Finset.sum_pair hne]
  simp [Measure.real, sphereMeasure_singleton_unitVec, sphereMeasure_singleton_neg_unitVec]

end OneDim

open OneDim in
/-- In dimension one the surface integral is the sum over the two endpoints. -/
theorem sphereIntegral_one (x : Vec 1) (r : ℝ) (f : Vec 1 → ℝ) :
    sphereIntegral x r f = f (x + r • basisVec (0 : Fin 1)) + f (x - r • basisVec (0 : Fin 1)) := by
  unfold sphereIntegral
  rw [show (1 : ℕ) - 1 = 0 from rfl, pow_zero, one_mul]
  have := integral_sphereMeasure_one
    (fun ω => f (x + r • (ω : HilbertVec 1).toVec))
  unfold Internal.sphereMeasure at this
  rw [this]
  have h1 : (⟨unitVec, mem_sphere_unitVec⟩ : Metric.sphere (0 : HilbertVec 1) 1).1.toVec =
      basisVec (0 : Fin 1) := rfl
  have h2 : (⟨-unitVec, mem_sphere_neg_unitVec⟩ : Metric.sphere (0 : HilbertVec 1) 1).1.toVec =
      -basisVec (0 : Fin 1) := by
    ext i; fin_cases i; simp [unitVec, Vec.toHilbertVec, basisVec]
  simp only [h1, h2, smul_neg, sub_eq_add_neg]

open OneDim in
/-- In dimension one the surface mean is the average over the two endpoints. -/
theorem sphereMean_one (x : Vec 1) (r : ℝ) (f : Vec 1 → ℝ) :
    sphereMean x r f =
      (f (x + r • basisVec (0 : Fin 1)) + f (x - r • basisVec (0 : Fin 1))) / 2 := by
  have hint := integral_sphereMeasure_one
    (fun ω => f (x + r • (ω : HilbertVec 1).toVec))
  have hone := integral_sphereMeasure_one (fun _ => (1 : ℝ))
  unfold Internal.sphereMeasure at hint hone
  have h1 : (⟨unitVec, mem_sphere_unitVec⟩ : Metric.sphere (0 : HilbertVec 1) 1).1.toVec =
      basisVec (0 : Fin 1) := rfl
  have h2 : (⟨-unitVec, mem_sphere_neg_unitVec⟩ : Metric.sphere (0 : HilbertVec 1) 1).1.toVec =
      -basisVec (0 : Fin 1) := by
    ext i; fin_cases i; simp [unitVec, Vec.toHilbertVec, basisVec]
  unfold sphereMean
  rw [average_eq, smul_eq_mul]
  simp only [integral_const, smul_eq_mul, mul_one] at hone
  rw [hint, hone]
  simp only [h1, h2, smul_neg, sub_eq_add_neg]
  rw [inv_mul_eq_div]
  norm_num

end

end PDE
