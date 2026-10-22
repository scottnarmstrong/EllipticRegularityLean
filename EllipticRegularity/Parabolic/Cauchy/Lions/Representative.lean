module

public import EllipticRegularity.Parabolic.Cauchy.Lions.KernelTest
public import Mathlib.MeasureTheory.Integral.IntervalAverage

/-! # Measurable representatives from scalar time traces -/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped Interval

namespace PDE.Parabolic.Lions

/-- Radius of the shrinking time windows used to select a measurable representative. -/
noncomputable def representativeWindowRadius (s T : ℝ) (n : ℕ) : ℝ :=
  (T - s) / ((n : ℝ) + 1)

/-- Left endpoint of the time window centered at `t`, clipped to `[s,T]`. -/
noncomputable def representativeWindowLeft (s T : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  max s (t - representativeWindowRadius s T n)

/-- Right endpoint of the time window centered at `t`, clipped to `[s,T]`. -/
noncomputable def representativeWindowRight (s T : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  min T (t + representativeWindowRadius s T n)

theorem representativeWindowRadius_pos {s T : ℝ} (hsT : s < T) (n : ℕ) :
    0 < representativeWindowRadius s T n := by
  unfold representativeWindowRadius
  exact div_pos (sub_pos.mpr hsT) (by positivity)

theorem representativeWindowRadius_tendsto {s T : ℝ} (_hsT : s < T) :
    Tendsto (representativeWindowRadius s T) atTop (𝓝 0) := by
  have h := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (T - s)
  have heq : representativeWindowRadius s T = fun n : ℕ =>
      (T - s) * ((n : ℝ) + 1)⁻¹ := by
    funext n
    simp [representativeWindowRadius, div_eq_mul_inv]
  rw [heq]
  simpa [one_div] using h

theorem representativeWindow_bounds {s T : ℝ} (hsT : s < T) {t : ℝ}
    (ht : t ∈ Icc s T) (n : ℕ) :
    representativeWindowLeft s T n t ≤ t ∧ t ≤ representativeWindowRight s T n t := by
  constructor
  · unfold representativeWindowLeft
    apply max_le
    · exact ht.1
    · exact sub_le_self _ (representativeWindowRadius_pos hsT n).le
  · unfold representativeWindowRight
    apply le_min
    · exact ht.2
    · linarith [representativeWindowRadius_pos hsT n]

theorem representativeWindow_strict {s T : ℝ} (hsT : s < T) {t : ℝ}
    (ht : t ∈ Icc s T) (n : ℕ) :
    representativeWindowLeft s T n t < representativeWindowRight s T n t := by
  have h := representativeWindowRadius_pos hsT n
  unfold representativeWindowLeft representativeWindowRight
  by_cases hts : t = s
  · subst t
    rw [max_eq_left (by linarith)]
    exact lt_min hsT (by linarith)
  · by_cases htT : t = T
    · subst t
      have hleft : max s (T - representativeWindowRadius s T n) < T := by
        exact max_lt hsT (by linarith [h])
      rw [min_eq_left (by linarith)]
      exact hleft
    · have hst : s < t := lt_of_le_of_ne ht.1 (Ne.symm hts)
      have htt : t < T := lt_of_le_of_ne ht.2 htT
      have hleft : max s (t - representativeWindowRadius s T n) < t :=
        max_lt hst (by linarith [representativeWindowRadius_pos hsT n])
      have hright : t < min T (t + representativeWindowRadius s T n) :=
        lt_min htt (by linarith [representativeWindowRadius_pos hsT n])
      exact hleft.trans hright

/-- Continuous functions are recovered at every time by averages over the clipped shrinking
windows. -/
theorem tendsto_representativeWindowAverage {s T : ℝ} (hsT : s < T) {v : ℝ → ℝ}
    (hv : ContinuousOn v (Icc s T)) {t : ℝ} (ht : t ∈ Icc s T) :
    Tendsto (fun n => ⨍ τ in (representativeWindowLeft s T n t)..
      (representativeWindowRight s T n t), v τ) atTop (𝓝 (v t)) := by
  have hwidth := representativeWindowRadius_tendsto hsT
  choose c hc hcavg using fun n =>
    exists_eq_interval_average (a := representativeWindowRight s T n t)
      (b := representativeWindowLeft s T n t) (f := v)
      (ne_of_gt (representativeWindow_strict hsT ht n))
      (hv.mono (by
        intro τ hτ
        have hbounds := representativeWindow_bounds hsT ht n
        have houterL : s ≤ representativeWindowLeft s T n t ∧
            representativeWindowLeft s T n t ≤ T :=
          ⟨le_max_left _ _, hbounds.1.trans ht.2⟩
        have houterR : s ≤ representativeWindowRight s T n t ∧
            representativeWindowRight s T n t ≤ T :=
          ⟨ht.1.trans hbounds.2, min_le_left _ _⟩
        have hLR := representativeWindow_strict hsT ht n
        have hτ' : τ ∈ Icc (representativeWindowLeft s T n t)
            (representativeWindowRight s T n t) := by
          simpa [uIcc_comm, uIcc_of_le hLR.le] using hτ
        exact ⟨houterL.1.trans hτ'.1, hτ'.2.trans houterR.2⟩))
  have hc_mem : ∀ n, c n ∈ Icc s T := by
    intro n
    have hbounds := representativeWindow_bounds hsT ht n
    have houterL : s ≤ representativeWindowLeft s T n t ∧
        representativeWindowLeft s T n t ≤ T :=
      ⟨le_max_left _ _, hbounds.1.trans ht.2⟩
    have houterR : s ≤ representativeWindowRight s T n t ∧
        representativeWindowRight s T n t ≤ T :=
      ⟨ht.1.trans hbounds.2, min_le_left _ _⟩
    have hwindow : c n ∈ Ioo (representativeWindowLeft s T n t)
        (representativeWindowRight s T n t) := by
      simpa [uIoo_comm, uIoo_of_le (representativeWindow_strict hsT ht n).le] using hc n
    have hL := hwindow.1
    have hR := hwindow.2
    exact ⟨houterL.1.trans hL.le, hR.le.trans houterR.2⟩
  have hdist : ∀ n, dist (c n) t ≤ representativeWindowRadius s T n := by
    intro n
    have hbounds := representativeWindow_bounds hsT ht n
    have houterL : s ≤ representativeWindowLeft s T n t ∧
        representativeWindowLeft s T n t ≤ T :=
      ⟨le_max_left _ _, hbounds.1.trans ht.2⟩
    have houterR : s ≤ representativeWindowRight s T n t ∧
        representativeWindowRight s T n t ≤ T :=
      ⟨ht.1.trans hbounds.2, min_le_left _ _⟩
    have hwindow : c n ∈ Ioo (representativeWindowLeft s T n t)
        (representativeWindowRight s T n t) := by
      simpa [uIoo_comm, uIoo_of_le (representativeWindow_strict hsT ht n).le] using hc n
    have hcL := hwindow.1
    have hcR := hwindow.2
    have hrad := representativeWindowRadius_pos hsT n
    have hleft : t - representativeWindowRadius s T n ≤ c n := by
      unfold representativeWindowLeft at hcL
      exact (le_max_right _ _).trans hcL.le
    have hright : c n ≤ t + representativeWindowRadius s T n := by
      unfold representativeWindowRight at hcR
      exact hcR.le.trans (min_le_right _ _)
    rw [Real.dist_eq, abs_le]
    constructor <;> linarith
  have hct : Tendsto c atTop (𝓝 t) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    rcases Metric.tendsto_atTop.1 hwidth ε hε with ⟨N, hN⟩
    exact ⟨N, fun n hn => (hdist n).trans_lt (by
      simpa [Real.dist_eq, abs_of_nonneg (representativeWindowRadius_pos hsT n).le]
        using hN n hn)⟩
  have hctWithin : Tendsto c atTop (𝓝[Icc s T] t) :=
    tendsto_nhdsWithin_iff.mpr ⟨hct, Filter.Eventually.of_forall (hc_mem)⟩
  have hcont : ContinuousWithinAt v (Icc s T) t := hv t ht
  have hvct : Tendsto (fun n => v (c n)) atTop (𝓝 (v t)) :=
    hcont.tendsto.comp hctWithin
  have hcavg' : ∀ n, v (c n) =
      ⨍ τ in (representativeWindowLeft s T n t)..
        (representativeWindowRight s T n t), v τ := by
    intro n
    calc
      v (c n) = ⨍ τ in (representativeWindowRight s T n t)..
          (representativeWindowLeft s T n t), v τ := hcavg n
      _ = ⨍ τ in (representativeWindowLeft s T n t)..
          (representativeWindowRight s T n t), v τ :=
        interval_average_symm v _ _
  exact hvct.congr' (Filter.Eventually.of_forall fun n => hcavg' n)

/-- Jointly measurable integrand for a clipped time-window average. -/
private noncomputable def representativeWindowIntegrand {d : ℕ} (s T : ℝ) (n : ℕ)
    (g : Vec d × ℝ → ℝ) (p : (Vec d × ℝ) × ℝ) : ℝ :=
  if p.1.2 ∈ Icc s T ∧
      p.2 ∈ Icc (representativeWindowLeft s T n p.1.2)
        (representativeWindowRight s T n p.1.2) then g (p.1.1, p.2) else 0

/-- A measurable time average of `g` on the clipped window; it is set to zero outside `[s,T]`. -/
noncomputable def representativeWindowAverage {d : ℕ} (s T : ℝ) (n : ℕ)
    (g : Vec d × ℝ → ℝ) (z : Vec d × ℝ) : ℝ :=
  if z.2 ∈ Icc s T then
    ⨍ τ in Icc (representativeWindowLeft s T n z.2)
      (representativeWindowRight s T n z.2), g (z.1, τ)
  else 0

private theorem representativeWindowIntegrand_measurable {d : ℕ} {s T : ℝ}
    {g : Vec d × ℝ → ℝ} (hg : Measurable g) (n : ℕ) :
    Measurable (representativeWindowIntegrand s T n g) := by
  let L : (Vec d × ℝ) × ℝ → ℝ := fun p => representativeWindowLeft s T n p.1.2
  let R : (Vec d × ℝ) × ℝ → ℝ := fun p => representativeWindowRight s T n p.1.2
  have htime : Measurable fun p : (Vec d × ℝ) × ℝ => p.1.2 := measurable_fst.snd
  have hτ : Measurable fun p : (Vec d × ℝ) × ℝ => p.2 := measurable_snd
  have hL : Measurable L := by
    dsimp [L, representativeWindowLeft]
    exact measurable_const.max (htime.sub measurable_const)
  have hR : Measurable R := by
    dsimp [R, representativeWindowRight]
    exact measurable_const.min (htime.add measurable_const)
  have hslab : MeasurableSet {p : (Vec d × ℝ) × ℝ | p.1.2 ∈ Icc s T} :=
    measurableSet_Icc.preimage htime
  have hwindow : MeasurableSet {p : (Vec d × ℝ) × ℝ | L p ≤ p.2 ∧ p.2 ≤ R p} :=
    (measurableSet_le hL hτ).inter (measurableSet_le hτ hR)
  have hS : MeasurableSet {p : (Vec d × ℝ) × ℝ |
      p.1.2 ∈ Icc s T ∧ p.2 ∈ Icc (L p) (R p)} := by
    have heq : {p : (Vec d × ℝ) × ℝ |
        p.1.2 ∈ Icc s T ∧ p.2 ∈ Icc (L p) (R p)} =
        {p | p.1.2 ∈ Icc s T} ∩ {p | L p ≤ p.2 ∧ p.2 ≤ R p} := by
      ext p
      simp [Set.mem_Icc]
    rw [heq]
    exact hslab.inter hwindow
  have hcomp : Measurable (fun p : (Vec d × ℝ) × ℝ => g (p.1.1, p.2)) :=
    hg.comp (measurable_fst.fst.prodMk measurable_snd)
  unfold representativeWindowIntegrand
  exact Measurable.ite hS hcomp measurable_const

private theorem representativeWindowIntegral_eq {d : ℕ} {s T : ℝ} {g : Vec d × ℝ → ℝ}
    (n : ℕ) (z : Vec d × ℝ) (hz : z.2 ∈ Icc s T) :
    (∫ τ, representativeWindowIntegrand s T n g (z, τ)) =
      ∫ τ in Icc (representativeWindowLeft s T n z.2)
        (representativeWindowRight s T n z.2), g (z.1, τ) := by
  let K : Set ℝ := Icc (representativeWindowLeft s T n z.2)
    (representativeWindowRight s T n z.2)
  have hEq : (fun τ => representativeWindowIntegrand s T n g (z, τ)) =
      K.indicator (fun τ => g (z.1, τ)) := by
    funext τ
    by_cases hτ : τ ∈ K <;> simp [representativeWindowIntegrand, K, hz, hτ]
  rw [hEq, integral_indicator (measurableSet_Icc)]

private theorem representativeWindowAverage_measurable {d : ℕ} {s T : ℝ}
    {g : Vec d × ℝ → ℝ} (hg : StronglyMeasurable g) (n : ℕ) :
    Measurable (representativeWindowAverage s T n g) := by
  have hH := representativeWindowIntegrand_measurable (s := s) (T := T) hg.measurable n
  have hInt : StronglyMeasurable (fun z : Vec d × ℝ =>
      ∫ τ, representativeWindowIntegrand s T n g (z, τ)) :=
    hH.stronglyMeasurable.integral_prod_right' (ν := (volume : Measure ℝ))
  have htime : Measurable fun z : Vec d × ℝ => z.2 := measurable_snd
  have hL : Measurable fun z : Vec d × ℝ => representativeWindowLeft s T n z.2 := by
    exact measurable_const.max (htime.sub measurable_const)
  have hR : Measurable fun z : Vec d × ℝ => representativeWindowRight s T n z.2 := by
    exact measurable_const.min (htime.add measurable_const)
  have hvol : Measurable fun z : Vec d × ℝ =>
      (volume.real (Icc (representativeWindowLeft s T n z.2)
        (representativeWindowRight s T n z.2))) := by
    have heq : (fun z : Vec d × ℝ =>
        volume.real (Icc (representativeWindowLeft s T n z.2)
          (representativeWindowRight s T n z.2))) =
        fun z => max (representativeWindowRight s T n z.2 -
          representativeWindowLeft s T n z.2) 0 := by
      funext z
      simp
    rw [heq]
    exact (hR.sub hL).max measurable_const
  have hI : MeasurableSet {z : Vec d × ℝ | z.2 ∈ Icc s T} :=
    measurableSet_Icc.preimage htime
  have hform (z : Vec d × ℝ) : representativeWindowAverage s T n g z =
      if z.2 ∈ Icc s T then
        (volume.real (Icc (representativeWindowLeft s T n z.2)
          (representativeWindowRight s T n z.2)))⁻¹ *
          ∫ τ, representativeWindowIntegrand s T n g (z, τ) else 0 := by
    by_cases hz : z.2 ∈ Icc s T
    · simp only [representativeWindowAverage, ite_eq_left hz]
      rw [setAverage_eq, smul_eq_mul, representativeWindowIntegral_eq n z hz]
    · simp [representativeWindowAverage, hz]
  have hraw : Measurable (fun z : Vec d × ℝ =>
      (volume.real (Icc (representativeWindowLeft s T n z.2)
        (representativeWindowRight s T n z.2)))⁻¹ *
        ∫ τ, representativeWindowIntegrand s T n g (z, τ)) :=
    hvol.inv.mul hInt.measurable
  have hite : Measurable (fun z : Vec d × ℝ =>
      if z.2 ∈ Icc s T then
        (volume.real (Icc (representativeWindowLeft s T n z.2)
          (representativeWindowRight s T n z.2)))⁻¹ *
          ∫ τ, representativeWindowIntegrand s T n g (z, τ) else 0) :=
    Measurable.ite hI hraw measurable_const
  have heq : representativeWindowAverage s T n g = fun z =>
      if z.2 ∈ Icc s T then
        (volume.real (Icc (representativeWindowLeft s T n z.2)
          (representativeWindowRight s T n z.2)))⁻¹ *
          ∫ τ, representativeWindowIntegrand s T n g (z, τ) else 0 := by
    funext z
    exact hform z
  rw [heq]
  exact hite

/-- A family of scalar continuous representatives that is only given separately at each spatial
point has a single jointly measurable representative. We obtain it as a pointwise limit of
measurable time-window averages. -/
theorem exists_measurable_continuousOn_timeRepresentative {d : ℕ} {s T : ℝ}
    (hsT : s < T) {g : Vec d × ℝ → ℝ} (hg : StronglyMeasurable g)
    (hrep : ∀ x : Vec d, ∃ v : ℝ → ℝ,
      ContinuousOn v (Icc s T) ∧
      (fun t => g (x, t)) =ᵐ[volume.restrict (Icc s T)] v) :
    ∃ w : Vec d × ℝ → ℝ, Measurable w ∧
      (∀ x, ContinuousOn (fun t => w (x, t)) (Icc s T)) ∧
      (∀ x, (fun t => g (x, t)) =ᵐ[volume.restrict (Icc s T)] (fun t => w (x, t))) := by
  classical
  let v : Vec d → ℝ → ℝ := fun x => Classical.choose (hrep x)
  have hv : ∀ x, ContinuousOn (v x) (Icc s T) ∧
      (fun t => g (x, t)) =ᵐ[volume.restrict (Icc s T)] (v x) := by
    intro x
    exact Classical.choose_spec (hrep x)
  let w : Vec d × ℝ → ℝ := fun z => if z.2 ∈ Icc s T then v z.1 z.2 else 0
  let A : ℕ → Vec d × ℝ → ℝ := fun n z =>
    if z.2 ∈ Icc s T then representativeWindowAverage s T n g z else 0
  have hAmeas : ∀ n, Measurable (A n) := by
    intro n
    have havg := representativeWindowAverage_measurable (s := s) (T := T) hg n
    exact Measurable.ite (measurableSet_Icc.preimage measurable_snd) havg measurable_const
  have hlim : Tendsto A atTop (𝓝 w) := by
    rw [tendsto_pi_nhds]
    intro z
    by_cases ht : z.2 ∈ Icc s T
    · have hV := hv z.1
      have hAvgEq (m : ℕ) : representativeWindowAverage s T m g z =
          ⨍ τ in Icc (representativeWindowLeft s T m z.2)
            (representativeWindowRight s T m z.2), v z.1 τ := by
        dsimp [representativeWindowAverage]
        rw [ite_eq_left ht]
        have hbounds' := representativeWindow_bounds hsT ht m
        have houterL' : s ≤ representativeWindowLeft s T m z.2 ∧
            representativeWindowLeft s T m z.2 ≤ T :=
          ⟨le_max_left _ _, hbounds'.1.trans ht.2⟩
        have houterR' : s ≤ representativeWindowRight s T m z.2 ∧
            representativeWindowRight s T m z.2 ≤ T :=
          ⟨ht.1.trans hbounds'.2, min_le_left _ _⟩
        have hsub' : Icc (representativeWindowLeft s T m z.2)
            (representativeWindowRight s T m z.2) ⊆ Icc s T := by
          intro τ hτ
          exact ⟨houterL'.1.trans hτ.1, hτ.2.trans houterR'.2⟩
        have hAE := ae_restrict_of_ae_restrict_of_subset hsub' hV.2
        have hAE' : ∀ᵐ τ ∂volume, τ ∈
            Icc (representativeWindowLeft s T m z.2)
              (representativeWindowRight s T m z.2) →
              g (z.1, τ) = v z.1 τ := by
          exact (ae_restrict_iff' measurableSet_Icc).1 hAE
        exact setAverage_congr_fun measurableSet_Icc hAE'
      have hbounds0 := representativeWindow_bounds hsT ht 0
      have houterL0 : s ≤ representativeWindowLeft s T 0 z.2 ∧
          representativeWindowLeft s T 0 z.2 ≤ T :=
        ⟨le_max_left _ _, hbounds0.1.trans ht.2⟩
      have houterR0 : s ≤ representativeWindowRight s T 0 z.2 ∧
          representativeWindowRight s T 0 z.2 ≤ T :=
        ⟨ht.1.trans hbounds0.2, min_le_left _ _⟩
      have hwidth := representativeWindowRadius_tendsto hsT
      choose c hc havg using fun m =>
        exists_eq_setAverage (isConnected_Icc
          (representativeWindow_strict hsT ht m).le)
          (hV.1.mono (by
            intro τ hτ
            have hb := representativeWindow_bounds hsT ht m
            have hL : s ≤ representativeWindowLeft s T m z.2 := le_max_left _ _
            have hR : representativeWindowRight s T m z.2 ≤ T := min_le_left _ _
            exact ⟨hL.trans hτ.1, hτ.2.trans hR⟩))
          ((hV.1.mono (by
            intro τ hτ
            have hL : s ≤ representativeWindowLeft s T m z.2 := le_max_left _ _
            have hR : representativeWindowRight s T m z.2 ≤ T := min_le_left _ _
            exact ⟨hL.trans hτ.1, hτ.2.trans hR⟩)).integrableOn_compact
              isCompact_Icc)
          (isCompact_Icc.measure_ne_top)
          (ne_of_gt (by
            rw [Real.volume_Icc]
            exact ENNReal.ofReal_pos.mpr
              (sub_pos.mpr (representativeWindow_strict hsT ht m))))
      have hc_in : ∀ m, c m ∈ Icc s T := by
        intro m
        have hc' := hc m
        have hL : s ≤ representativeWindowLeft s T m z.2 := le_max_left _ _
        have hR : representativeWindowRight s T m z.2 ≤ T := min_le_left _ _
        exact ⟨le_trans hL hc'.1, le_trans hc'.2 hR⟩
      have hdist : ∀ m, dist (c m) z.2 ≤ representativeWindowRadius s T m := by
        intro m
        have hc' := hc m
        have hl : z.2 - representativeWindowRadius s T m ≤ c m :=
          (le_max_right _ _).trans hc'.1
        have hr : c m ≤ z.2 + representativeWindowRadius s T m :=
          hc'.2.trans (min_le_right _ _)
        rw [Real.dist_eq, abs_le]
        constructor <;> linarith
      have hct : Tendsto c atTop (𝓝 z.2) := by
        apply Metric.tendsto_atTop.2
        intro ε hε
        rcases Metric.tendsto_atTop.1 hwidth ε hε with ⟨N, hN⟩
        exact ⟨N, fun m hm => (hdist m).trans_lt (by
          simpa [Real.dist_eq, abs_of_nonneg (representativeWindowRadius_pos hsT m).le]
            using hN m hm)⟩
      have hctWithin : Tendsto c atTop (𝓝[Icc s T] z.2) :=
        tendsto_nhdsWithin_iff.mpr ⟨hct, Filter.Eventually.of_forall hc_in⟩
      have hcont : ContinuousWithinAt (v z.1) (Icc s T) z.2 := hV.1 z.2 ht
      have hvlim : Tendsto (fun m => v z.1 (c m)) atTop (𝓝 (v z.1 z.2)) :=
        hcont.tendsto.comp hctWithin
      have havg' : ∀ m, v z.1 (c m) =
          ⨍ τ in Icc (representativeWindowLeft s T m z.2)
            (representativeWindowRight s T m z.2), v z.1 τ := havg
      have hEq : (fun m => v z.1 (c m)) = fun m => A m z := by
        funext m
        simp only [A]
        simp [ht, hAvgEq m, (havg' m).symm]
      rw [← hEq]
      have hwz : w z = v z.1 z.2 := ite_eq_left ht
      rw [hwz]
      exact hvlim
    · have hwz : w z = 0 := ite_eq_right ht
      have hAz : (fun m => A m z) = fun _ => 0 := by
        funext m
        exact ite_eq_right ht
      rw [hAz, hwz]
      exact tendsto_const_nhds
  have hmeas : Measurable w :=
    measurable_of_tendsto_metrizable' atTop hAmeas hlim
  refine ⟨w, hmeas, ?_, ?_⟩
  · intro x t ht
    have hw (τ : ℝ) (hτ : τ ∈ Icc s T) : w (x, τ) = v x τ := ite_eq_left hτ
    exact (hv x).1 t ht |>.congr (fun τ hτ => hw τ hτ) (hw t ht)
  · intro x
    filter_upwards [ae_restrict_mem measurableSet_Icc, (hv x).2] with t htI htg
    have hw : w (x, t) = v x t := ite_eq_left htI
    rw [hw]
    exact htg


end PDE.Parabolic.Lions
