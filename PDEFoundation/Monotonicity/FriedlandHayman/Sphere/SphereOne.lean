module

public import PDEFoundation.Monotonicity.Core.BridgeSphere
public import Mathlib.MeasureTheory.Constructions.HaarToSphere

/-!
# Friedland--Hayman: the zero-dimensional sphere

The unit sphere of `HilbertVec 1` is `{±e}` and its surface measure gives each point mass one,
so `sphereIntegral (0 : Vec 1) r G = G(r e) + G(-r e)`.
-/

@[expose] public section

open MeasureTheory
open scoped Pointwise

namespace PDE.FHLane

noncomputable section

/-- The first coordinate of `HilbertVec 1` is volume preserving. -/
theorem mp_coord0 : MeasurePreserving (fun z : HilbertVec 1 => z 0) volume volume := by
  exact (volume_preserving_funUnique (Fin 1) ℝ).comp
    (PDE.Internal.measurePreserving_toHilbert_symm (d := 1))

theorem sphere1_coord (ω : Metric.sphere (0 : HilbertVec 1) 1) :
    (ω : HilbertVec 1) 0 = 1 ∨ (ω : HilbertVec 1) 0 = -1 := by
  have hn : ‖(ω : HilbertVec 1)‖ = 1 := by simp
  rw [PiLp.norm_eq_of_L2] at hn
  simpa using hn

/-- The point `s • e` of the unit sphere of `HilbertVec 1`, for `s = ±1`. -/
def unitPt (s : ℝ) (hs : s = 1 ∨ s = -1) : Metric.sphere (0 : HilbertVec 1) 1 :=
  ⟨WithLp.toLp 2 (fun _ => s), by
    rw [mem_sphere_zero_iff_norm, PiLp.norm_eq_of_L2]
    rcases hs with rfl | rfl <;> simp⟩

theorem unitPt_coord (s : ℝ) (hs : s = 1 ∨ s = -1) : ((unitPt s hs : _) : HilbertVec 1) 0 = s := rfl

theorem sphere1_eq (ω : Metric.sphere (0 : HilbertVec 1) 1) :
    ω = unitPt 1 (Or.inl rfl) ∨ ω = unitPt (-1) (Or.inr rfl) := by
  rcases sphere1_coord ω with h | h
  · left; apply Subtype.ext; ext i; fin_cases i; exact h
  · right; apply Subtype.ext; ext i; fin_cases i; exact h

theorem sphere1_mass (s : ℝ) (hs : s = 1 ∨ s = -1) :
    ((volume : Measure (HilbertVec 1)).toSphere).real {unitPt s hs} = 1 := by
  have hs2 : s * s = 1 := by rcases hs with rfl | rfl <;> norm_num
  rw [Measure.real, Measure.toSphere_apply' _ (measurableSet_singleton _)]
  have hset : Set.Ioo (0 : ℝ) 1 • (Subtype.val '' ({unitPt s hs} : Set (Metric.sphere (0 : HilbertVec 1) 1))) =
      (fun z : HilbertVec 1 => z 0) ⁻¹' {x : ℝ | s * x ∈ Set.Ioo 0 1} := by
    rw [Set.image_singleton, Set.smul_singleton]
    ext z
    simp only [Set.mem_image, Set.mem_preimage, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t, ht, rfl⟩
      have : (t • ((unitPt s hs : _) : HilbertVec 1)) 0 = t * s := rfl
      have h3 : s * (t * s) = t := by
        calc s * (t * s) = t * (s * s) := by ring
          _ = t := by rw [hs2, mul_one]
      rw [this, h3]
      exact ht
    · intro hz
      refine ⟨s * z 0, hz, ?_⟩
      ext i
      fin_cases i
      show s * z 0 * s = z 0
      calc s * z 0 * s = (s * s) * z 0 := by ring
        _ = z 0 := by rw [hs2, one_mul]
  have hmeas : MeasurableSet {x : ℝ | s * x ∈ Set.Ioo 0 1} :=
    measurableSet_Ioo.preimage (measurable_const.mul measurable_id)
  have hvol : volume {x : ℝ | s * x ∈ Set.Ioo 0 1} = 1 := by
    rcases hs with rfl | rfl
    · have : {x : ℝ | (1 : ℝ) * x ∈ Set.Ioo 0 1} = Set.Ioo 0 1 := by ext x; simp
      rw [this]; simp
    · have : {x : ℝ | (-1 : ℝ) * x ∈ Set.Ioo 0 1} = Set.Ioo (-1) 0 := by
        ext x
        simp only [Set.mem_ofPred_eq, Set.mem_Ioo]
        constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
      rw [this]; simp
  rw [hset, mp_coord0.measure_preimage hmeas.nullMeasurableSet, hvol]
  simp

theorem unitPt_ne : unitPt 1 (Or.inl rfl) ≠ unitPt (-1) (Or.inr rfl) := by
  intro h
  have := congrArg (fun ω : Metric.sphere (0 : HilbertVec 1) 1 => (ω : HilbertVec 1) 0) h
  simp only [unitPt_coord] at this
  norm_num at this

/-- The `S⁰` evaluation: two unit masses at `±r e`. -/
theorem sphereIntegral_vec_one (G : Vec 1 → ℝ) (r : ℝ) :
    sphereIntegral (0 : Vec 1) r G = G (fun _ => r) + G (fun _ => -r) := by
  unfold sphereIntegral
  simp only [Nat.sub_self, pow_zero, one_mul]
  have hf : (fun ω : Metric.sphere (0 : HilbertVec 1) 1 =>
      G ((0 : Vec 1) + r • (ω : HilbertVec 1).toVec)) =
      fun ω => G (fun _ => r) *
          ({unitPt 1 (Or.inl rfl)} : Set (Metric.sphere (0 : HilbertVec 1) 1)).indicator
            (1 : Metric.sphere (0 : HilbertVec 1) 1 → ℝ) ω +
        G (fun _ => -r) *
          ({unitPt (-1) (Or.inr rfl)} : Set (Metric.sphere (0 : HilbertVec 1) 1)).indicator
            (1 : Metric.sphere (0 : HilbertVec 1) 1 → ℝ) ω := by
    ext ω
    rcases sphere1_eq ω with rfl | rfl
    · have h1 : ((0 : Vec 1) + r • ((unitPt 1 (Or.inl rfl) : _) : HilbertVec 1).toVec) =
          fun _ => r := by
        ext i; simp [unitPt]
      rw [h1]
      simp [Set.indicator_of_notMem (show unitPt 1 (Or.inl rfl) ∉
        ({unitPt (-1) (Or.inr rfl)} : Set (Metric.sphere (0 : HilbertVec 1) 1)) from
          fun h => unitPt_ne h)]
    · have h1 : ((0 : Vec 1) + r • ((unitPt (-1) (Or.inr rfl) : _) : HilbertVec 1).toVec) =
          fun _ => -r := by
        ext i; simp [unitPt]
      rw [h1]
      simp [Set.indicator_of_notMem (show unitPt (-1) (Or.inr rfl) ∉
        ({unitPt 1 (Or.inl rfl)} : Set (Metric.sphere (0 : HilbertVec 1) 1)) from
          fun h => unitPt_ne h.symm)]
  have hi : ∀ x : Metric.sphere (0 : HilbertVec 1) 1, Integrable
      (({x} : Set (Metric.sphere (0 : HilbertVec 1) 1)).indicator
        (1 : Metric.sphere (0 : HilbertVec 1) 1 → ℝ)) ((volume : Measure (HilbertVec 1)).toSphere) :=
    fun x => (integrable_const (1 : ℝ)).indicator (measurableSet_singleton _)
  rw [hf, integral_add ((hi _).const_mul _) ((hi _).const_mul _), integral_const_mul,
    integral_const_mul, integral_indicator_one (measurableSet_singleton _),
    integral_indicator_one (measurableSet_singleton _), sphere1_mass 1 (Or.inl rfl),
    sphere1_mass (-1) (Or.inr rfl)]
  ring

end

end PDE.FHLane
