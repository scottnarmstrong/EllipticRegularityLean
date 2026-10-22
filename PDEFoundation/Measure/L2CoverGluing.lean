module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Quantitative `L²` gluing over finite covers

These measure-generic lemmas assemble local squared-oscillation estimates
over overlapping sets. No disjointness is required. Set volumes and overlap
volumes remain literal, so a geometric application can expose every
constant.
-/

@[expose] public section

namespace PDE

open MeasureTheory

variable {X : Type*} [MeasurableSpace X]
variable {μ : Measure X}

/-- A nonnegative integrable function has integral over a two-set union no
larger than the sum of its two local integrals. -/
theorem setIntegral_union_le_of_nonneg
    {f : X → ℝ} {s t : Set X}
    (hfs : IntegrableOn f s μ) (hft : IntegrableOn f t μ)
    (hf : ∀ x, 0 ≤ f x) :
    ∫ x in s ∪ t, f x ∂μ ≤
      (∫ x in s, f x ∂μ) + ∫ x in t, f x ∂μ := by
  rw [← integral_add_measure hfs hft]
  apply integral_mono_measure (Measure.restrict_union_le s t)
  · filter_upwards with x
    exact hf x
  · exact Integrable.add_measure hfs hft

/-- Bound the integral over a set contained in a two-set cover by the two
local nonnegative integrals. -/
theorem setIntegral_le_add_setIntegral_of_subset_union
    {f : X → ℝ} {S s t : Set X}
    (hS : S ⊆ s ∪ t)
    (hfs : IntegrableOn f s μ) (hft : IntegrableOn f t μ)
    (hf : ∀ x, 0 ≤ f x) :
    ∫ x in S, f x ∂μ ≤
      (∫ x in s, f x ∂μ) + ∫ x in t, f x ∂μ := by
  calc
    ∫ x in S, f x ∂μ ≤ ∫ x in s ∪ t, f x ∂μ := by
      apply setIntegral_mono_set (hfs.union hft)
      · filter_upwards with x
        exact hf x
      · exact Filter.Eventually.of_forall hS
    _ ≤ (∫ x in s, f x ∂μ) + ∫ x in t, f x ∂μ :=
      setIntegral_union_le_of_nonneg hfs hft hf

/-- A four-set cover costs at most the sum of its four local nonnegative
integrals. -/
theorem setIntegral_le_sum_four_of_subset_union
    {f : X → ℝ} {S s₀ s₁ s₂ s₃ : Set X}
    (hS : S ⊆ (s₀ ∪ s₁) ∪ (s₂ ∪ s₃))
    (h₀ : IntegrableOn f s₀ μ) (h₁ : IntegrableOn f s₁ μ)
    (h₂ : IntegrableOn f s₂ μ) (h₃ : IntegrableOn f s₃ μ)
    (hf : ∀ x, 0 ≤ f x) :
    ∫ x in S, f x ∂μ ≤
      (∫ x in s₀, f x ∂μ) +
        (∫ x in s₁, f x ∂μ) +
        (∫ x in s₂, f x ∂μ) +
        ∫ x in s₃, f x ∂μ := by
  have h01 := setIntegral_union_le_of_nonneg h₀ h₁ hf
  have h23 := setIntegral_union_le_of_nonneg h₂ h₃ hf
  calc
    ∫ x in S, f x ∂μ ≤
        (∫ x in s₀ ∪ s₁, f x ∂μ) +
          ∫ x in s₂ ∪ s₃, f x ∂μ :=
      setIntegral_le_add_setIntegral_of_subset_union
        hS (h₀.union h₁) (h₂.union h₃) hf
    _ ≤ ((∫ x in s₀, f x ∂μ) +
          ∫ x in s₁, f x ∂μ) +
        ((∫ x in s₂, f x ∂μ) +
          ∫ x in s₃, f x ∂μ) := by
      gcongr
    _ = (∫ x in s₀, f x ∂μ) +
          (∫ x in s₁, f x ∂μ) +
          (∫ x in s₂, f x ∂μ) +
          ∫ x in s₃, f x ∂μ := by
      ring

/-- Pointwise algebra behind changing the center of a squared
oscillation. -/
theorem sq_sub_le_two_sq_sub_add_two_sq (a b c : ℝ) :
    (a - c) ^ 2 ≤
      2 * (a - b) ^ 2 + 2 * (b - c) ^ 2 := by
  nlinarith [sq_nonneg ((a - b) - (b - c))]

/-- Changing the center of a local square integral costs the old variance
and the set volume times the squared distance between centers. -/
theorem setIntegral_sq_sub_le_change_center
    {u : X → ℝ} {s : Set X} {b c : ℝ}
    (hIntOld : IntegrableOn (fun x => (u x - b) ^ 2) s μ)
    (hIntNew : IntegrableOn (fun x => (u x - c) ^ 2) s μ)
    (hfinite : μ s ≠ ⊤) :
    ∫ x in s, (u x - c) ^ 2 ∂μ ≤
      2 * (∫ x in s, (u x - b) ^ 2 ∂μ) +
        2 * μ.real s * (b - c) ^ 2 := by
  have hIntConst :
      IntegrableOn (fun _x : X => 2 * (b - c) ^ 2) s μ :=
    integrableOn_const hfinite
  have hIntRhs :
      IntegrableOn
        (fun x => 2 * (u x - b) ^ 2 +
          2 * (b - c) ^ 2) s μ :=
    (hIntOld.const_mul 2).add hIntConst
  calc
    ∫ x in s, (u x - c) ^ 2 ∂μ ≤
        ∫ x in s,
          2 * (u x - b) ^ 2 + 2 * (b - c) ^ 2 ∂μ := by
      exact setIntegral_mono hIntNew hIntRhs fun x =>
        sq_sub_le_two_sq_sub_add_two_sq (u x) b c
    _ = 2 * (∫ x in s, (u x - b) ^ 2 ∂μ) +
        2 * μ.real s * (b - c) ^ 2 := by
      calc
        ∫ x in s,
            2 * (u x - b) ^ 2 + 2 * (b - c) ^ 2 ∂μ =
            (∫ x in s, 2 * (u x - b) ^ 2 ∂μ) +
              ∫ _x in s, 2 * (b - c) ^ 2 ∂μ :=
          integral_add (hIntOld.const_mul 2) hIntConst
        _ = 2 * (∫ x in s, (u x - b) ^ 2 ∂μ) +
              μ.real s * (2 * (b - c) ^ 2) := by
          rw [integral_const_mul, setIntegral_const]
          simp only [smul_eq_mul]
        _ = 2 * (∫ x in s, (u x - b) ^ 2 ∂μ) +
              2 * μ.real s * (b - c) ^ 2 := by
          ring

/-- Divide an overlap-center bound by an explicit positive lower volume. -/
theorem overlap_center_distance_sq_le_of_integral_bound
    {c d V W m : ℝ}
    (hbound : m * (c - d) ^ 2 ≤ 2 * (V + W))
    (hm : 0 < m) :
    (c - d) ^ 2 ≤ (2 * (V + W)) / m :=
  (le_div_iff₀ hm).2 (by simpa only [mul_comm] using hbound)

/-- Two local centers are quantitatively close when their sets have a
positive-volume overlap. The overlap volume remains literal. -/
theorem overlap_center_distance_sq_bound
    {u : X → ℝ} {s t : Set X} {c d : ℝ}
    (hIntS : IntegrableOn (fun x => (u x - c) ^ 2) s μ)
    (hIntT : IntegrableOn (fun x => (u x - d) ^ 2) t μ)
    (hOverlapMeas : MeasurableSet (s ∩ t))
    (hOverlapFinite : μ (s ∩ t) ≠ ⊤) :
    μ.real (s ∩ t) * (c - d) ^ 2 ≤
      2 * ((∫ x in s, (u x - c) ^ 2 ∂μ) +
        ∫ x in t, (u x - d) ^ 2 ∂μ) := by
  let O : Set X := s ∩ t
  have hIntSO :
      IntegrableOn (fun x => (u x - c) ^ 2) O μ :=
    hIntS.mono_set fun _ hx => hx.1
  have hIntTO :
      IntegrableOn (fun x => (u x - d) ^ 2) O μ :=
    hIntT.mono_set fun _ hx => hx.2
  have hIntRhs :
      IntegrableOn
        (fun x => 2 * (u x - c) ^ 2 +
          2 * (u x - d) ^ 2) O μ :=
    (hIntSO.const_mul 2).add (hIntTO.const_mul 2)
  have hpointwise : ∀ x ∈ O,
      (c - d) ^ 2 ≤
        2 * (u x - c) ^ 2 + 2 * (u x - d) ^ 2 := by
    intro x _
    simpa only [sub_sq_comm] using
      sq_sub_le_two_sq_sub_add_two_sq c (u x) d
  have hLower :
      μ.real O * (c - d) ^ 2 ≤
        ∫ x in O,
          2 * (u x - c) ^ 2 + 2 * (u x - d) ^ 2 ∂μ := by
    simpa only [smul_eq_mul] using
      (setIntegral_ge_of_const_le (μ := μ)
        (c := (c - d) ^ 2)
        (by simpa only [O] using hOverlapMeas)
        (by simpa only [O] using hOverlapFinite)
        hpointwise hIntRhs)
  have hSmono :
      (∫ x in O, (u x - c) ^ 2 ∂μ) ≤
        ∫ x in s, (u x - c) ^ 2 ∂μ := by
    apply setIntegral_mono_set hIntS
    · exact Filter.Eventually.of_forall fun x =>
        sq_nonneg (u x - c)
    · exact Filter.Eventually.of_forall fun _ hx => hx.1
  have hTmono :
      (∫ x in O, (u x - d) ^ 2 ∂μ) ≤
        ∫ x in t, (u x - d) ^ 2 ∂μ := by
    apply setIntegral_mono_set hIntT
    · exact Filter.Eventually.of_forall fun x =>
        sq_nonneg (u x - d)
    · exact Filter.Eventually.of_forall fun _ hx => hx.2
  calc
    μ.real (s ∩ t) * (c - d) ^ 2 =
        μ.real O * (c - d) ^ 2 := rfl
    _ ≤ ∫ x in O,
        2 * (u x - c) ^ 2 + 2 * (u x - d) ^ 2 ∂μ :=
      hLower
    _ = 2 * ((∫ x in O, (u x - c) ^ 2 ∂μ) +
          ∫ x in O, (u x - d) ^ 2 ∂μ) := by
      rw [integral_add (hIntSO.const_mul 2)
          (hIntTO.const_mul 2),
        integral_const_mul, integral_const_mul]
      ring
    _ ≤ 2 * ((∫ x in s, (u x - c) ^ 2 ∂μ) +
          ∫ x in t, (u x - d) ^ 2 ∂μ) := by
      gcongr

/-- Insert explicit upper bounds for two local variances into the overlap
center comparison. -/
theorem overlap_center_distance_sq_le_of_local_bounds
    {u : X → ℝ} {s t : Set X} {c d V W m : ℝ}
    (hIntS : IntegrableOn (fun x => (u x - c) ^ 2) s μ)
    (hIntT : IntegrableOn (fun x => (u x - d) ^ 2) t μ)
    (hOverlapMeas : MeasurableSet (s ∩ t))
    (hOverlapFinite : μ (s ∩ t) ≠ ⊤)
    (hm : m ≤ μ.real (s ∩ t))
    (hV : (∫ x in s, (u x - c) ^ 2 ∂μ) ≤ V)
    (hW : (∫ x in t, (u x - d) ^ 2 ∂μ) ≤ W) :
    m * (c - d) ^ 2 ≤ 2 * (V + W) := by
  have hcenter :=
    overlap_center_distance_sq_bound
      hIntS hIntT hOverlapMeas hOverlapFinite
  calc
    m * (c - d) ^ 2 ≤
        μ.real (s ∩ t) * (c - d) ^ 2 := by
      gcongr
    _ ≤ 2 * ((∫ x in s, (u x - c) ^ 2 ∂μ) +
          ∫ x in t, (u x - d) ^ 2 ∂μ) :=
      hcenter
    _ ≤ 2 * (V + W) := by
      gcongr

end PDE
