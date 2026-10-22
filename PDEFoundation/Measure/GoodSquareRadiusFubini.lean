module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Integral.Prod
public import PDEFoundation.Measure.GoodSquareRadius

/-!
# Coordinate Fubini helpers for good square radii

The good-boundary argument needs to turn the four fixed-width strips around a
square into iterated one-dimensional integrals.  This file keeps that change
of variables on the native `Vec 2` carrier.
-/

@[expose] public section

namespace PDE

open MeasureTheory Set

noncomputable section

/-- Membership of a native square point in a two-dimensional axis box is
exactly the pair of one-dimensional interval conditions. -/
theorem squarePoint_mem_axisBox_iff
    (a b c d s t : ℝ) :
    squarePoint s t ∈ axisBox ![a, c] ![b, d] ↔
      s ∈ Ioo a b ∧ t ∈ Ioo c d := by
  constructor
  · intro h
    have h0 := h 0 (Set.mem_univ 0)
    have h1 := h 1 (Set.mem_univ 1)
    change a < s ∧ s < b at h0
    change c < t ∧ t < d at h1
    exact ⟨h0, h1⟩
  · rintro ⟨hs, ht⟩ i _
    fin_cases i
    · change a < s ∧ s < b
      exact hs
    · change c < t ∧ t < d
      exact ht

/-- Fubini on native two-dimensional vectors, with coordinate zero outermost
and coordinate one innermost. -/
theorem integral_vec_two_eq_iterated_squarePoint
    {f : Vec 2 → ℝ}
    (hf : Integrable f (volume : Measure (Vec 2))) :
    (∫ x, f x ∂(volume : Measure (Vec 2))) =
      ∫ s : ℝ, ∫ t : ℝ, f (squarePoint s t) := by
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  have hpres : MeasurePreserving e (volume : Measure (Vec 2)) volume :=
    volume_preserving_piFinTwo _
  have hfprod : Integrable (fun p : ℝ × ℝ => f (e.symm p)) :=
    hpres.symm.integrable_comp_of_integrable hf
  calc
    (∫ x, f x ∂(volume : Measure (Vec 2))) =
        ∫ p : ℝ × ℝ, f (e.symm p) :=
      (hpres.symm.integral_comp' f).symm
    _ = ∫ s : ℝ, ∫ t : ℝ, f (squarePoint s t) := by
      change
        (∫ p : ℝ × ℝ, f (e.symm p)
          ∂((volume : Measure ℝ).prod (volume : Measure ℝ))) = _
      rw [integral_prod _ hfprod]
      simp only [e, MeasurableEquiv.piFinTwo_symm_apply]
      apply integral_congr_ae
      filter_upwards with s
      apply integral_congr_ae
      filter_upwards with t
      congr 1
      funext i
      fin_cases i <;> simp [squarePoint]

/-- Fubini on a two-dimensional open axis box, expressed using `squarePoint`.
This is the fixed-strip identity used by the square-boundary radius argument. -/
theorem integralOn_axisBox_eq_integral_squarePoint
    {f : Vec 2 → ℝ} {a b c d : ℝ}
    (hf : IntegrableOn f (axisBox ![a, c] ![b, d])) :
    (∫ x in axisBox ![a, c] ![b, d], f x) =
      ∫ s in Ioo a b, ∫ t in Ioo c d, f (squarePoint s t) := by
  let Q : Set (Vec 2) := axisBox ![a, c] ![b, d]
  have hQ : MeasurableSet Q := (isOpen_axisBox _ _).measurableSet
  have hindicator : Integrable (Q.indicator f) := hf.integrable_indicator hQ
  rw [show (∫ x in Q, f x) = ∫ x, Q.indicator f x by
    rw [integral_indicator hQ]]
  rw [integral_vec_two_eq_iterated_squarePoint hindicator]
  have hpointwise :
      (fun s : ℝ => ∫ t : ℝ, Q.indicator f (squarePoint s t)) =
        fun s : ℝ => (Ioo a b).indicator
          (fun s => ∫ t : ℝ, (Ioo c d).indicator
            (fun t => f (squarePoint s t)) t) s := by
    funext s
    by_cases hs : s ∈ Ioo a b
    · rw [Set.indicator_of_mem hs]
      apply integral_congr_ae
      filter_upwards with t
      by_cases ht : t ∈ Ioo c d
      · have hq : squarePoint s t ∈ Q := by
          change squarePoint s t ∈ axisBox ![a, c] ![b, d]
          exact (squarePoint_mem_axisBox_iff a b c d s t).mpr ⟨hs, ht⟩
        rw [Set.indicator_of_mem hq, Set.indicator_of_mem ht]
      · have hq : squarePoint s t ∉ Q := by
          intro hq
          apply ht
          change squarePoint s t ∈ axisBox ![a, c] ![b, d] at hq
          exact ((squarePoint_mem_axisBox_iff a b c d s t).mp hq).2
        rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem ht]
    · rw [Set.indicator_of_notMem hs]
      apply integral_eq_zero_of_ae
      filter_upwards with t
      have hq : squarePoint s t ∉ Q := by
        intro hq
        apply hs
        change squarePoint s t ∈ axisBox ![a, c] ![b, d] at hq
        exact ((squarePoint_mem_axisBox_iff a b c d s t).mp hq).1
      simp [Set.indicator_of_notMem hq]
  rw [hpointwise, integral_indicator measurableSet_Ioo]
  simp_rw [integral_indicator measurableSet_Ioo]

/-- The inner one-dimensional integral of an integrable function on an axis
box is integrable in the remaining coordinate.  This is the integrability
half of the fixed-strip Fubini calculation; it is recorded separately because
the radius-selection theorem needs a genuine `IntegrableOn` hypothesis. -/
theorem integrableOn_axisBox_innerIntegral_squarePoint
    {f : Vec 2 → ℝ} {a b c d : ℝ}
    (hf : IntegrableOn f (axisBox ![a, c] ![b, d])) :
    IntegrableOn
      (fun s : ℝ => ∫ t in Ioo c d, f (squarePoint s t)) (Ioo a b) := by
  let Q : Set (Vec 2) := axisBox ![a, c] ![b, d]
  have hQ : MeasurableSet Q := (isOpen_axisBox _ _).measurableSet
  have hindicator : Integrable (Q.indicator f) := hf.integrable_indicator hQ
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  have hfprod : Integrable (fun p : ℝ × ℝ => Q.indicator f (e.symm p)) :=
    (volume_preserving_piFinTwo _).symm.integrable_comp_of_integrable hindicator
  have houter : Integrable
      (fun s : ℝ => ∫ t : ℝ, Q.indicator f (squarePoint s t)) := by
    refine hfprod.integral_prod_left.congr (Filter.Eventually.of_forall fun s => ?_)
    apply integral_congr_ae
    filter_upwards with t
    congr 1
    funext i
    fin_cases i <;> simp [e, MeasurableEquiv.piFinTwo_symm_apply, squarePoint]
  apply (integrableOn_congr_fun (s := Ioo a b) ?_ measurableSet_Ioo).mpr
    houter.integrableOn
  intro s hs
  change (∫ t in Ioo c d, f (squarePoint s t)) =
    ∫ t : ℝ, Q.indicator f (squarePoint s t)
  rw [← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards with t
  by_cases ht : t ∈ Ioo c d
  · have hq : squarePoint s t ∈ Q := by
      change squarePoint s t ∈ axisBox ![a, c] ![b, d]
      exact (squarePoint_mem_axisBox_iff a b c d s t).mpr ⟨hs, ht⟩
    rw [Set.indicator_of_mem hq, Set.indicator_of_mem ht]
  · have hq : squarePoint s t ∉ Q := by
      intro hq
      apply ht
      change squarePoint s t ∈ axisBox ![a, c] ![b, d] at hq
      exact ((squarePoint_mem_axisBox_iff a b c d s t).mp hq).2
    rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem ht]

/-- The analogous coordinate-peeling conclusion with coordinate one outermost.
This is needed for the horizontal sides of a square and avoids introducing a
second, swapped ambient vector representation. -/
theorem integrableOn_axisBox_outerSecond_innerIntegral_squarePoint
    {f : Vec 2 → ℝ} {a b c d : ℝ}
    (hf : IntegrableOn f (axisBox ![a, c] ![b, d])) :
    IntegrableOn
      (fun t : ℝ => ∫ s in Ioo a b, f (squarePoint s t)) (Ioo c d) := by
  let Q : Set (Vec 2) := axisBox ![a, c] ![b, d]
  have hQ : MeasurableSet Q := (isOpen_axisBox _ _).measurableSet
  have hindicator : Integrable (Q.indicator f) := hf.integrable_indicator hQ
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  have hfprod : Integrable (fun p : ℝ × ℝ => Q.indicator f (e.symm p)) :=
    (volume_preserving_piFinTwo _).symm.integrable_comp_of_integrable hindicator
  have hsquare : Integrable
      (fun p : ℝ × ℝ => Q.indicator f (squarePoint p.1 p.2)) := by
    refine hfprod.congr (Filter.Eventually.of_forall fun p => ?_)
    change Q.indicator f (e.symm p) =
      Q.indicator f (squarePoint p.1 p.2)
    congr 2
    funext i
    fin_cases i <;> simp [e, MeasurableEquiv.piFinTwo_symm_apply, squarePoint]
  have houter : Integrable
      (fun t : ℝ => ∫ s : ℝ, Q.indicator f (squarePoint s t)) :=
    hsquare.integral_prod_right
  apply (integrableOn_congr_fun (s := Ioo c d) ?_ measurableSet_Ioo).mpr
    houter.integrableOn
  intro t ht
  change (∫ s in Ioo a b, f (squarePoint s t)) =
    ∫ s : ℝ, Q.indicator f (squarePoint s t)
  rw [← integral_indicator measurableSet_Ioo]
  apply integral_congr_ae
  filter_upwards with s
  by_cases hs : s ∈ Ioo a b
  · have hq : squarePoint s t ∈ Q := by
      change squarePoint s t ∈ axisBox ![a, c] ![b, d]
      exact (squarePoint_mem_axisBox_iff a b c d s t).mpr ⟨hs, ht⟩
    rw [Set.indicator_of_mem hq, Set.indicator_of_mem hs]
  · have hq : squarePoint s t ∉ Q := by
      intro hq
      apply hs
      change squarePoint s t ∈ axisBox ![a, c] ![b, d] at hq
      exact ((squarePoint_mem_axisBox_iff a b c d s t).mp hq).1
    rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hs]

/-- Fubini on a two-dimensional open axis box, with coordinate one outermost. -/
theorem integralOn_axisBox_eq_integral_outerSecond_squarePoint
    {f : Vec 2 → ℝ} {a b c d : ℝ}
    (hf : IntegrableOn f (axisBox ![a, c] ![b, d])) :
    (∫ x in axisBox ![a, c] ![b, d], f x) =
      ∫ t in Ioo c d, ∫ s in Ioo a b, f (squarePoint s t) := by
  let Q : Set (Vec 2) := axisBox ![a, c] ![b, d]
  have hQ : MeasurableSet Q := (isOpen_axisBox _ _).measurableSet
  have hindicator : Integrable (Q.indicator f) := hf.integrable_indicator hQ
  let e := MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ)
  have hfprod : Integrable (fun p : ℝ × ℝ => Q.indicator f (e.symm p)) :=
    (volume_preserving_piFinTwo _).symm.integrable_comp_of_integrable hindicator
  have hsquare : Integrable
      (fun p : ℝ × ℝ => Q.indicator f (squarePoint p.1 p.2)) := by
    refine hfprod.congr (Filter.Eventually.of_forall fun p => ?_)
    change Q.indicator f (e.symm p) =
      Q.indicator f (squarePoint p.1 p.2)
    congr 2
    funext i
    fin_cases i <;> simp [e, MeasurableEquiv.piFinTwo_symm_apply, squarePoint]
  rw [show (∫ x in Q, f x) = ∫ x, Q.indicator f x by
    rw [integral_indicator hQ]]
  calc
    (∫ x : Vec 2, Q.indicator f x) =
        ∫ s : ℝ, ∫ t : ℝ, Q.indicator f (squarePoint s t) :=
      integral_vec_two_eq_iterated_squarePoint hindicator
    _ = ∫ t : ℝ, ∫ s : ℝ, Q.indicator f (squarePoint s t) := by
      exact integral_integral_swap hsquare
    _ = ∫ t in Ioo c d, ∫ s in Ioo a b, f (squarePoint s t) := by
      rw [← integral_indicator measurableSet_Ioo]
      apply integral_congr_ae
      filter_upwards with t
      by_cases ht : t ∈ Ioo c d
      · rw [Set.indicator_of_mem ht]
        rw [← integral_indicator measurableSet_Ioo]
        apply integral_congr_ae
        filter_upwards with s
        by_cases hs : s ∈ Ioo a b
        · have hq : squarePoint s t ∈ Q := by
            change squarePoint s t ∈ axisBox ![a, c] ![b, d]
            exact (squarePoint_mem_axisBox_iff a b c d s t).mpr ⟨hs, ht⟩
          rw [Set.indicator_of_mem hq, Set.indicator_of_mem hs]
        · have hq : squarePoint s t ∉ Q := by
            intro hq
            apply hs
            change squarePoint s t ∈ axisBox ![a, c] ![b, d] at hq
            exact ((squarePoint_mem_axisBox_iff a b c d s t).mp hq).1
          rw [Set.indicator_of_notMem hq, Set.indicator_of_notMem hs]
      · rw [Set.indicator_of_notMem ht]
        apply integral_eq_zero_of_ae
        filter_upwards with s
        have hq : squarePoint s t ∉ Q := by
          intro hq
          apply ht
          change squarePoint s t ∈ axisBox ![a, c] ![b, d] at hq
          exact ((squarePoint_mem_axisBox_iff a b c d s t).mp hq).2
        simp [Set.indicator_of_notMem hq]

/-- Translation of a set integral on an open interval.  This deliberately
uses the ambient Lebesgue-measure preserving map, rather than an interval
integral: the good-radius selection theorem is stated with `IntegrableOn`. -/
private theorem integralOn_Ioo_comp_add_left
    {H : ℝ → ℝ} {a b c : ℝ} :
    (∫ ρ in Ioo a b, H (c + ρ)) =
      ∫ s in Ioo (c + a) (c + b), H s := by
  let I : Set ℝ := Ioo a b
  let J : Set ℝ := Ioo (c + a) (c + b)
  have hI : MeasurableSet I := measurableSet_Ioo
  have hJ : MeasurableSet J := measurableSet_Ioo
  have hpres : MeasurePreserving (fun x : ℝ => c + x) volume volume :=
    measurePreserving_add_left volume c
  calc
    (∫ ρ in I, H (c + ρ)) = ∫ ρ, I.indicator (fun ρ => H (c + ρ)) ρ := by
      rw [integral_indicator hI]
    _ = ∫ ρ, J.indicator H (c + ρ) := by
      apply integral_congr_ae
      filter_upwards with ρ
      by_cases hρ : ρ ∈ I
      · have hcρ : c + ρ ∈ J := by
          change a < ρ ∧ ρ < b at hρ
          change c + a < c + ρ ∧ c + ρ < c + b
          constructor <;> linarith
        simp [Set.indicator_of_mem hρ, Set.indicator_of_mem hcρ]
      · have hcρ : c + ρ ∉ J := by
          intro hcρ
          apply hρ
          change c + a < c + ρ ∧ c + ρ < c + b at hcρ
          change a < ρ ∧ ρ < b
          constructor <;> linarith
        simp [Set.indicator_of_notMem hρ, Set.indicator_of_notMem hcρ]
    _ = ∫ s, J.indicator H s := by
      exact hpres.integral_comp' (f := MeasurableEquiv.addLeft c) _
    _ = ∫ s in J, H s := integral_indicator hJ

/-- Reflection and translation of a set integral on an open interval. -/
private theorem integralOn_Ioo_comp_sub_left
    {H : ℝ → ℝ} {a b c : ℝ} :
    (∫ ρ in Ioo a b, H (c - ρ)) =
      ∫ s in Ioo (c - b) (c - a), H s := by
  let I : Set ℝ := Ioo a b
  let J : Set ℝ := Ioo (c - b) (c - a)
  have hI : MeasurableSet I := measurableSet_Ioo
  have hJ : MeasurableSet J := measurableSet_Ioo
  have hpres : MeasurePreserving (fun x : ℝ => c - x) volume volume := by
    simpa only [Function.comp_apply, sub_eq_add_neg] using!
      (measurePreserving_add_left volume c).comp
        (Measure.measurePreserving_neg (volume : Measure ℝ))
  calc
    (∫ ρ in I, H (c - ρ)) = ∫ ρ, I.indicator (fun ρ => H (c - ρ)) ρ := by
      rw [integral_indicator hI]
    _ = ∫ ρ, J.indicator H (c - ρ) := by
      apply integral_congr_ae
      filter_upwards with ρ
      by_cases hρ : ρ ∈ I
      · have hcρ : c - ρ ∈ J := by
          change a < ρ ∧ ρ < b at hρ
          change c - b < c - ρ ∧ c - ρ < c - a
          constructor <;> linarith
        simp [Set.indicator_of_mem hρ, Set.indicator_of_mem hcρ]
      · have hcρ : c - ρ ∉ J := by
          intro hcρ
          apply hρ
          change c - b < c - ρ ∧ c - ρ < c - a at hcρ
          change a < ρ ∧ ρ < b
          constructor <;> linarith
        simp [Set.indicator_of_notMem hρ, Set.indicator_of_notMem hcρ]
    _ = ∫ s, J.indicator H s := by
      exact hpres.integral_comp' (f := MeasurableEquiv.subLeft c) _
    _ = ∫ s in J, H s := integral_indicator hJ

private theorem integrableOn_Ioo_comp_add_left
    {H : ℝ → ℝ} {a b c : ℝ}
    (hH : IntegrableOn H (Ioo (c + a) (c + b))) :
    IntegrableOn (fun ρ => H (c + ρ)) (Ioo a b) := by
  have hpres : MeasurePreserving (fun x : ℝ => c + x) volume volume :=
    measurePreserving_add_left volume c
  have hpreimage : (fun x : ℝ => c + x) ⁻¹' Ioo (c + a) (c + b) = Ioo a b := by
    ext x
    change (c + a < c + x ∧ c + x < c + b) ↔ a < x ∧ x < b
    constructor <;> intro hx <;> constructor <;> linarith
  have htransport :=
    (hpres.integrableOn_comp_preimage
      (MeasurableEquiv.addLeft c).measurableEmbedding).mpr hH
  rw [hpreimage] at htransport
  simpa only [Function.comp_apply] using! htransport

private theorem integrableOn_Ioo_comp_sub_left
    {H : ℝ → ℝ} {a b c : ℝ}
    (hH : IntegrableOn H (Ioo (c - b) (c - a))) :
    IntegrableOn (fun ρ => H (c - ρ)) (Ioo a b) := by
  have hpres : MeasurePreserving (fun x : ℝ => c - x) volume volume := by
    simpa only [Function.comp_apply, sub_eq_add_neg] using!
      (measurePreserving_add_left volume c).comp
        (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hpreimage : (fun x : ℝ => c - x) ⁻¹' Ioo (c - b) (c - a) = Ioo a b := by
    ext x
    change (c - b < c - x ∧ c - x < c - a) ↔ a < x ∧ x < b
    constructor <;> intro hx <;> constructor <;> linarith
  have htransport :=
    (hpres.integrableOn_comp_preimage
      (MeasurableEquiv.subLeft c).measurableEmbedding).mpr hH
  rw [hpreimage] at htransport
  simpa only [Function.comp_apply] using! htransport

private theorem integrableOn_coordinate_sq_of_memVectorL2On
    {g : Vec 2 → Vec 2} {U S : Set (Vec 2)} {i : Fin 2}
    (hg : MemVectorL2On U g) (hSU : S ⊆ U) :
    IntegrableOn (fun x => (g x i) ^ 2) S := by
  simpa only [pow_two] using
    (integrableOn_mul_of_memL2On (hg i) (hg i)).mono_set hSU

private theorem coordinate_sq_strip_integral_le_squareShellVectorEnergy
    {g : Vec 2 → Vec 2} {x₀ : Vec 2} {r : ℝ}
    {S : Set (Vec 2)} {i : Fin 2}
    (hg : MemVectorL2On (centeredAxisCube x₀ (2 * r)) g)
    (hS : S ⊆ dyadicSquareShell x₀ r) :
    (∫ x in S, (g x i) ^ 2) ≤ squareShellVectorEnergy g x₀ r := by
  have hShell : IntegrableOn (fun x => vecNormSq (g x))
      (dyadicSquareShell x₀ r) :=
    integrableOn_squareShellVectorEnergy_integrand hg
  have hSvec : IntegrableOn (fun x => vecNormSq (g x)) S :=
    hShell.mono_set hS
  calc
    (∫ x in S, (g x i) ^ 2) ≤ ∫ x in S, vecNormSq (g x) := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun x => sq_nonneg _
      · exact hSvec
      · exact Filter.Eventually.of_forall fun x => sq_apply_le_vecNormSq (g x) i
    _ ≤ ∫ x in dyadicSquareShell x₀ r, vecNormSq (g x) := by
      apply setIntegral_mono_set hShell
      · exact Filter.Eventually.of_forall fun x => vecNormSq_nonneg (g x)
      · exact Filter.Eventually.of_forall fun x hx => hS hx

/-- The `L²` hypothesis on the outer square supplies both Fubini hypotheses
for the concrete enlarged-square boundary energy.  The proof treats the four
sides separately, keeping the positive and reflected radius changes explicit.
Consequently the sole loss in the subsequent selection step is its displayed
factor `4 / r`. -/
theorem exists_good_enlargedSquare_radius_of_memVectorL2On
    {g : Vec 2 → Vec 2} {x₀ : Vec 2} {r : ℝ} {N : Set ℝ}
    (hr : 0 < r)
    (hg : MemVectorL2On (centeredAxisCube x₀ (2 * r)) g)
    (hN : volume N = 0) :
    ∃ ρ ∈ Ioo r (2 * r), ρ ∉ N ∧
      enlargedSquareSideTangentialEnergy g x₀ r ρ ≤
        (4 / r) * squareShellVectorEnergy g x₀ r := by
  have hRightOuter : dyadicSquareShellRight x₀ r ⊆ centeredAxisCube x₀ (2 * r) :=
    fun x hx => (dyadicSquareShellRight_subset x₀ r hx).1
  have hLeftOuter : dyadicSquareShellLeft x₀ r ⊆ centeredAxisCube x₀ (2 * r) :=
    fun x hx => (dyadicSquareShellLeft_subset x₀ r hx).1
  have hTopOuter : dyadicSquareShellTop x₀ r ⊆ centeredAxisCube x₀ (2 * r) :=
    fun x hx => (dyadicSquareShellTop_subset x₀ r hx).1
  have hBottomOuter : dyadicSquareShellBottom x₀ r ⊆ centeredAxisCube x₀ (2 * r) :=
    fun x hx => (dyadicSquareShellBottom_subset x₀ r hx).1
  have hRight : IntegrableOn (fun x => (g x 1) ^ 2)
      (dyadicSquareShellRight x₀ r) := by
    apply integrableOn_coordinate_sq_of_memVectorL2On hg
    exact hRightOuter
  have hLeft : IntegrableOn (fun x => (g x 1) ^ 2)
      (dyadicSquareShellLeft x₀ r) := by
    apply integrableOn_coordinate_sq_of_memVectorL2On hg
    exact hLeftOuter
  have hTop : IntegrableOn (fun x => (g x 0) ^ 2)
      (dyadicSquareShellTop x₀ r) := by
    apply integrableOn_coordinate_sq_of_memVectorL2On hg
    exact hTopOuter
  have hBottom : IntegrableOn (fun x => (g x 0) ^ 2)
      (dyadicSquareShellBottom x₀ r) := by
    apply integrableOn_coordinate_sq_of_memVectorL2On hg
    exact hBottomOuter
  have hRightRadius : IntegrableOn
      (fun ρ : ℝ => ∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
        (g (squarePoint (x₀ 0 + ρ) t) 1) ^ 2) (Ioo r (2 * r)) := by
    simpa only [Function.comp_apply] using
      (integrableOn_Ioo_comp_add_left (c := x₀ 0)
        (integrableOn_axisBox_innerIntegral_squarePoint (by
          simpa only [dyadicSquareShellRight] using hRight)))
  have hLeftRadius : IntegrableOn
      (fun ρ : ℝ => ∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
        (g (squarePoint (x₀ 0 - ρ) t) 1) ^ 2) (Ioo r (2 * r)) := by
    simpa only [Function.comp_apply] using
      (integrableOn_Ioo_comp_sub_left (c := x₀ 0)
        (integrableOn_axisBox_innerIntegral_squarePoint (by
          simpa only [dyadicSquareShellLeft] using hLeft)))
  have hTopRadius : IntegrableOn
      (fun ρ : ℝ => ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
        (g (squarePoint t (x₀ 1 + ρ)) 0) ^ 2) (Ioo r (2 * r)) := by
    simpa only [Function.comp_apply] using
      (integrableOn_Ioo_comp_add_left (c := x₀ 1)
        (integrableOn_axisBox_outerSecond_innerIntegral_squarePoint (by
          simpa only [dyadicSquareShellTop] using hTop)))
  have hBottomRadius : IntegrableOn
      (fun ρ : ℝ => ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
        (g (squarePoint t (x₀ 1 - ρ)) 0) ^ 2) (Ioo r (2 * r)) := by
    simpa only [Function.comp_apply] using
      (integrableOn_Ioo_comp_sub_left (c := x₀ 1)
        (integrableOn_axisBox_outerSecond_innerIntegral_squarePoint (by
          simpa only [dyadicSquareShellBottom] using hBottom)))
  have hBoundary : IntegrableOn (enlargedSquareSideTangentialEnergy g x₀ r)
      (Ioo r (2 * r)) := by
    exact ((hRightRadius.add hLeftRadius).add hTopRadius).add hBottomRadius
  have hRightEq :
      (∫ ρ in Ioo r (2 * r), ∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
        (g (squarePoint (x₀ 0 + ρ) t) 1) ^ 2) =
        ∫ x in dyadicSquareShellRight x₀ r, (g x 1) ^ 2 := by
    calc
      (∫ ρ in Ioo r (2 * r), ∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
          (g (squarePoint (x₀ 0 + ρ) t) 1) ^ 2) =
          ∫ s in Ioo (x₀ 0 + r) (x₀ 0 + 2 * r),
            ∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
              (g (squarePoint s t) 1) ^ 2 :=
        integralOn_Ioo_comp_add_left (a := r) (b := 2 * r) (c := x₀ 0)
          (H := fun s => ∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
            (g (squarePoint s t) 1) ^ 2)
      _ = ∫ x in dyadicSquareShellRight x₀ r, (g x 1) ^ 2 := by
        simpa only [dyadicSquareShellRight] using
          (integralOn_axisBox_eq_integral_squarePoint hRight).symm
  have hLeftEq :
      (∫ ρ in Ioo r (2 * r), ∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
        (g (squarePoint (x₀ 0 - ρ) t) 1) ^ 2) =
        ∫ x in dyadicSquareShellLeft x₀ r, (g x 1) ^ 2 := by
    calc
      (∫ ρ in Ioo r (2 * r), ∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
          (g (squarePoint (x₀ 0 - ρ) t) 1) ^ 2) =
          ∫ s in Ioo (x₀ 0 - 2 * r) (x₀ 0 - r),
            ∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
              (g (squarePoint s t) 1) ^ 2 :=
        integralOn_Ioo_comp_sub_left (a := r) (b := 2 * r) (c := x₀ 0)
          (H := fun s => ∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
            (g (squarePoint s t) 1) ^ 2)
      _ = ∫ x in dyadicSquareShellLeft x₀ r, (g x 1) ^ 2 := by
        simpa only [dyadicSquareShellLeft] using
          (integralOn_axisBox_eq_integral_squarePoint hLeft).symm
  have hTopEq :
      (∫ ρ in Ioo r (2 * r), ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
        (g (squarePoint t (x₀ 1 + ρ)) 0) ^ 2) =
        ∫ x in dyadicSquareShellTop x₀ r, (g x 0) ^ 2 := by
    calc
      (∫ ρ in Ioo r (2 * r), ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
          (g (squarePoint t (x₀ 1 + ρ)) 0) ^ 2) =
          ∫ s in Ioo (x₀ 1 + r) (x₀ 1 + 2 * r),
            ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
              (g (squarePoint t s) 0) ^ 2 :=
        integralOn_Ioo_comp_add_left (a := r) (b := 2 * r) (c := x₀ 1)
          (H := fun s => ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
            (g (squarePoint t s) 0) ^ 2)
      _ = ∫ x in dyadicSquareShellTop x₀ r, (g x 0) ^ 2 := by
        simpa only [dyadicSquareShellTop] using
          (integralOn_axisBox_eq_integral_outerSecond_squarePoint hTop).symm
  have hBottomEq :
      (∫ ρ in Ioo r (2 * r), ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
        (g (squarePoint t (x₀ 1 - ρ)) 0) ^ 2) =
        ∫ x in dyadicSquareShellBottom x₀ r, (g x 0) ^ 2 := by
    calc
      (∫ ρ in Ioo r (2 * r), ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
          (g (squarePoint t (x₀ 1 - ρ)) 0) ^ 2) =
          ∫ s in Ioo (x₀ 1 - 2 * r) (x₀ 1 - r),
            ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
              (g (squarePoint t s) 0) ^ 2 :=
        integralOn_Ioo_comp_sub_left (a := r) (b := 2 * r) (c := x₀ 1)
          (H := fun s => ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
            (g (squarePoint t s) 0) ^ 2)
      _ = ∫ x in dyadicSquareShellBottom x₀ r, (g x 0) ^ 2 := by
        simpa only [dyadicSquareShellBottom] using
          (integralOn_axisBox_eq_integral_outerSecond_squarePoint hBottom).symm
  have hRightBound :=
    coordinate_sq_strip_integral_le_squareShellVectorEnergy hg
      (dyadicSquareShellRight_subset x₀ r) (i := 1)
  have hLeftBound :=
    coordinate_sq_strip_integral_le_squareShellVectorEnergy hg
      (dyadicSquareShellLeft_subset x₀ r) (i := 1)
  have hTopBound :=
    coordinate_sq_strip_integral_le_squareShellVectorEnergy hg
      (dyadicSquareShellTop_subset x₀ r) (i := 0)
  have hBottomBound :=
    coordinate_sq_strip_integral_le_squareShellVectorEnergy hg
      (dyadicSquareShellBottom_subset x₀ r) (i := 0)
  let R : ℝ → ℝ := fun ρ => ∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
    (g (squarePoint (x₀ 0 + ρ) t) 1) ^ 2
  let L : ℝ → ℝ := fun ρ => ∫ t in Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r),
    (g (squarePoint (x₀ 0 - ρ) t) 1) ^ 2
  let T : ℝ → ℝ := fun ρ => ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
    (g (squarePoint t (x₀ 1 + ρ)) 0) ^ 2
  let B : ℝ → ℝ := fun ρ => ∫ t in Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r),
    (g (squarePoint t (x₀ 1 - ρ)) 0) ^ 2
  have hR : IntegrableOn R (Ioo r (2 * r)) := by simpa [R] using hRightRadius
  have hL : IntegrableOn L (Ioo r (2 * r)) := by simpa [L] using hLeftRadius
  have hT : IntegrableOn T (Ioo r (2 * r)) := by simpa [T] using hTopRadius
  have hB : IntegrableOn B (Ioo r (2 * r)) := by simpa [B] using hBottomRadius
  have henergy : enlargedSquareSideTangentialEnergy g x₀ r = ((R + L) + T) + B := by
    funext ρ
    rfl
  have hREq : (∫ ρ in Ioo r (2 * r), R ρ) =
      ∫ x in dyadicSquareShellRight x₀ r, (g x 1) ^ 2 := by simpa [R] using hRightEq
  have hLEq : (∫ ρ in Ioo r (2 * r), L ρ) =
      ∫ x in dyadicSquareShellLeft x₀ r, (g x 1) ^ 2 := by simpa [L] using hLeftEq
  have hTEq : (∫ ρ in Ioo r (2 * r), T ρ) =
      ∫ x in dyadicSquareShellTop x₀ r, (g x 0) ^ 2 := by simpa [T] using hTopEq
  have hBEq : (∫ ρ in Ioo r (2 * r), B ρ) =
      ∫ x in dyadicSquareShellBottom x₀ r, (g x 0) ^ 2 := by simpa [B] using hBottomEq
  apply exists_good_enlargedSquare_radius_of_strip_bound hr hBoundary
  calc
    (∫ ρ in Ioo r (2 * r), enlargedSquareSideTangentialEnergy g x₀ r ρ) =
        ∫ ρ in Ioo r (2 * r), (((R + L) + T) + B) ρ := by rw [henergy]
    _ = (((∫ ρ in Ioo r (2 * r), R ρ) + ∫ ρ in Ioo r (2 * r), L ρ) +
        ∫ ρ in Ioo r (2 * r), T ρ) + ∫ ρ in Ioo r (2 * r), B ρ := by
      rw [show (∫ ρ in Ioo r (2 * r), (((R + L) + T) + B) ρ) =
          (∫ ρ in Ioo r (2 * r), ((R + L) + T) ρ) + ∫ ρ in Ioo r (2 * r), B ρ by
        simpa only [Pi.add_apply] using integral_add ((hR.add hL).add hT) hB,
        show (∫ ρ in Ioo r (2 * r), ((R + L) + T) ρ) =
          (∫ ρ in Ioo r (2 * r), (R + L) ρ) + ∫ ρ in Ioo r (2 * r), T ρ by
        simpa only [Pi.add_apply] using integral_add (hR.add hL) hT,
        show (∫ ρ in Ioo r (2 * r), (R + L) ρ) =
          (∫ ρ in Ioo r (2 * r), R ρ) + ∫ ρ in Ioo r (2 * r), L ρ by
        simpa only [Pi.add_apply] using integral_add hR hL]
    _ = (((∫ x in dyadicSquareShellRight x₀ r, (g x 1) ^ 2) +
          ∫ x in dyadicSquareShellLeft x₀ r, (g x 1) ^ 2) +
        ∫ x in dyadicSquareShellTop x₀ r, (g x 0) ^ 2) +
        ∫ x in dyadicSquareShellBottom x₀ r, (g x 0) ^ 2 := by
      rw [hREq, hLEq, hTEq, hBEq]
    _ ≤ 4 * squareShellVectorEnergy g x₀ r := by linarith
  exact hN

end

end PDE
