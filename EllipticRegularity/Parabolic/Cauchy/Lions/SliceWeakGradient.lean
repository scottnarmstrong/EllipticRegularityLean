module

public import EllipticRegularity.Parabolic.Cauchy.Lions.SliceGradient
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace
public import Mathlib.Topology.Metrizable.ContinuousMap
public import Mathlib.Topology.UniformSpace.Uniformizable

/-! # Uniform almost-everywhere slices for joint weak gradients

The fixed-test identity is promoted to all smooth compactly supported spatial tests by choosing a
countable dense family of `C¹` jets on each compact ball and passing to the limit in the slice
integrals.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Filter Topology Set

namespace PDE.Parabolic.Lions

variable {d : ℕ}

/-- The `C¹` jet of a smooth compactly supported spatial test. -/
noncomputable def cauchySmoothJet (ψ : Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    C(Vec d, ℝ × Vec d) :=
  ⟨fun x => (ψ x, fun i => fderiv ℝ ψ x (Pi.single i 1)),
    hψ.continuous.prodMk (continuous_pi fun i =>
      (hψ.continuous_fderiv (by simp)).clm_apply continuous_const)⟩

/-- Smooth test jets with support in a fixed compact ball. -/
def cauchySmoothJets (d : ℕ) (R : ℝ) : Set C(Vec d, ℝ × Vec d) :=
  {j | ∃ ψ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧
    tsupport ψ ⊆ Metric.closedBall 0 R ∧
    ∀ x, j x = (ψ x, fun i => fderiv ℝ ψ x (Pi.single i 1))}

/-- A continuous compactly supported multiplier times a function integrable on its support ball
is integrable, and the whole-space integral agrees with the set integral. -/
private theorem cauchyIntegrable_mul_of_integrableOn {h b : Vec d → ℝ} {B : Set (Vec d)}
    (hB : IsCompact B) (hh : IntegrableOn h B) (hb : Continuous b)
    (hbB : tsupport b ⊆ B) :
    Integrable (fun x => h x * b x) (volume : Measure (Vec d)) ∧
      ∫ x, h x * b x = ∫ x in B, h x * b x := by
  have hon : IntegrableOn (fun x => h x * b x) B :=
    hh.mul_continuousOn hb.continuousOn hB
  have hzero : ∀ x ∉ B, h x * b x = 0 := fun x hx => by
    simp [image_eq_zero_of_notMem_tsupport (fun h' => hx (hbB h'))]
  exact ⟨hon.integrable_of_forall_notMem_eq_zero hzero,
    (setIntegral_eq_integral_of_forall_compl_eq_zero hzero).symm⟩

/-- Slices of an `L²` function on the Cauchy slab are globally `L²` for a.e. time. -/
private theorem cauchyJointValue_ae_sliceL2 {d : ℕ} {s T : ℝ} (u : CauchyX d s T) :
    ∀ᵐ t ∂(volume.restrict (Icc s T)),
      MemLp (fun x : Vec d => cauchyJointValue u (x, t)) 2 (volume : Measure (Vec d)) := by
  have h := PDE.Parabolic.Energy.ae_slice_memLp (d := d) (K1 := (univ : Set (Vec d)))
    (J := Icc s T) (g := cauchyJointValue u) MeasurableSet.univ
    (cauchyJointValue_memLp u)
  filter_upwards [h] with t ht
  simpa using ht

private theorem cauchyJointGradient_ae_sliceL2 {d : ℕ} {s T : ℝ} (u : CauchyX d s T)
    (i : Fin d) :
    ∀ᵐ t ∂(volume.restrict (Icc s T)),
      MemLp (fun x : Vec d => cauchyJointGradient u (x, t) i) 2
        (volume : Measure (Vec d)) := by
  have h := PDE.Parabolic.Energy.ae_slice_memLp (d := d) (K1 := (univ : Set (Vec d)))
    (J := Icc s T) (g := fun z => cauchyJointGradient u z i) MeasurableSet.univ
    (cauchyJointGradient_memLp u i)
  filter_upwards [h] with t ht
  simpa using ht

/-- A joint Lions limit has its stated gradient on almost every time slice. -/
theorem cauchyClosure_ae_sliceWeakGradient {d : ℕ} {s T : ℝ}
    {u : CauchyX d s T} {u₀ : CauchyY d}
    (hu : WithLp.toLp 2 (u, u₀) ∈
      (LinearMap.range (initialTraceMap (cauchyJ (d := d) (s := s) (T := T))
        (cauchyGamma (d := d) (s := s) (T := T)))).topologicalClosure) :
    ∀ᵐ t ∂(volume.restrict (Icc s T)),
      HasWeakGradientOn (univ : Set (Vec d))
        (fun x => cauchyJointValue u (x, t)) (fun x => cauchyJointGradient u (x, t)) := by
  have hsep := fun R : ℕ => TopologicalSpace.exists_countable_dense
    (cauchySmoothJets d (R : ℝ))
  choose D hDc hDd using hsep
  have hDcount : ∀ R : ℕ, Countable (D R) := fun R => (hDc R).to_subtype
  let ψof : ∀ R : ℕ, cauchySmoothJets d (R : ℝ) → Vec d → ℝ :=
    fun R j => Classical.choose j.2
  have hψof : ∀ (R : ℕ) (j : cauchySmoothJets d (R : ℝ)),
      ContDiff ℝ (⊤ : ℕ∞) (ψof R j) ∧
      tsupport (ψof R j) ⊆ Metric.closedBall 0 (R : ℝ) ∧
      ∀ x, (j : C(Vec d, ℝ × Vec d)) x =
        (ψof R j x, fun i => fderiv ℝ (ψof R j) x (Pi.single i 1)) :=
    fun R j => Classical.choose_spec j.2
  have hgood : ∀ᵐ t ∂(volume.restrict (Icc s T)),
      ∀ R : ℕ, ∀ j : D R, ∀ i : Fin d,
        ∫ x, cauchyJointValue u (x, t) *
          fderiv ℝ (ψof R (j : cauchySmoothJets d (R : ℝ))) x (Pi.single i 1) =
        -∫ x, cauchyJointGradient u (x, t) i *
          ψof R (j : cauchySmoothJets d (R : ℝ)) x := by
    rw [ae_all_iff]
    intro R
    rw [ae_all_iff]
    intro j
    rw [ae_all_iff]
    intro i
    have hs := hψof R (j : cauchySmoothJets d (R : ℝ))
    have hc : HasCompactSupport (ψof R (j : cauchySmoothJets d (R : ℝ))) :=
      HasCompactSupport.of_support_subset_isCompact
        (isCompact_closedBall 0 (R : ℝ)) ((subset_tsupport _).trans hs.2.1)
    exact cauchyClosure_fixedSliceTest hu _ hs.1 hc i
  have hval := cauchyJointValue_ae_sliceL2 u
  have hgrad : ∀ i : Fin d, ∀ᵐ t ∂(volume.restrict (Icc s T)),
      MemLp (fun x : Vec d => cauchyJointGradient u (x, t) i) 2 volume :=
    fun i => cauchyJointGradient_ae_sliceL2 u i
  filter_upwards [hgood, hval, (ae_all_iff.mpr hgrad)] with t htests hvalT hgradT
  intro i ψ hψ hψc hψsupport
  obtain ⟨r, hr⟩ := hψc.isCompact.isBounded.subset_closedBall (0 : Vec d)
  obtain ⟨R, hR⟩ := exists_nat_ge r
  let B : Set (Vec d) := Metric.closedBall 0 (R : ℝ)
  have hBc : IsCompact B := isCompact_closedBall 0 (R : ℝ)
  have hψB : tsupport ψ ⊆ B := hr.trans
    (Metric.closedBall_subset_closedBall hR)
  have huLoc : LocallyIntegrable (fun x : Vec d => cauchyJointValue u (x, t)) volume :=
    hvalT.locallyIntegrable (by norm_num)
  have hgLoc : LocallyIntegrable
      (fun x : Vec d => cauchyJointGradient u (x, t) i) volume :=
    (hgradT i).locallyIntegrable (by norm_num)
  have huB : IntegrableOn (fun x : Vec d => cauchyJointValue u (x, t)) B :=
    huLoc.integrableOn_isCompact hBc
  have hgB : IntegrableOn (fun x : Vec d => cauchyJointGradient u (x, t) i) B :=
    hgLoc.integrableOn_isCompact hBc
  let ψ' : Vec d → ℝ := fun x => fderiv ℝ ψ x (Pi.single i 1)
  have hψ'c : Continuous ψ' :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψ'B : tsupport ψ' ⊆ B :=
    (tsupport_comp_subset (g := fun L : Vec d →L[ℝ] ℝ => L (Pi.single i 1))
      (by simp) _).trans ((tsupport_fderiv_subset ℝ).trans hψB)
  obtain ⟨hI1, hE1⟩ := cauchyIntegrable_mul_of_integrableOn hBc huB hψ'c hψ'B
  obtain ⟨hI2, hE2⟩ := cauchyIntegrable_mul_of_integrableOn hBc hgB hψ.continuous hψB
  change (∫ x in (univ : Set (Vec d)), cauchyJointValue u (x, t) *
      (fderiv ℝ ψ x) (basisVec i)) =
    -∫ x in (univ : Set (Vec d)), cauchyJointGradient u (x, t) i * ψ x
  rw [setIntegral_univ, setIntegral_univ]
  change (∫ x, cauchyJointValue u (x, t) * ψ' x) =
    -∫ x, cauchyJointGradient u (x, t) i * ψ x
  rw [hE1, hE2]
  let j₀ : cauchySmoothJets d (R : ℝ) :=
    ⟨cauchySmoothJet ψ hψ, ψ, hψ, hψB, fun x => rfl⟩
  have hcl : j₀ ∈ closure (D R) := (hDd R).closure_eq ▸ Set.mem_univ _
  obtain ⟨js, hjsD, hjs⟩ := mem_closure_iff_seq_limit.1 hcl
  let ψs : ℕ → Vec d → ℝ := fun n => ψof R (js n)
  have hψs : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψs n) ∧ tsupport (ψs n) ⊆ B ∧
      ∀ x, ((js n : cauchySmoothJets d (R : ℝ)) : C(Vec d, ℝ × Vec d)) x =
        (ψs n x, fun k => fderiv ℝ (ψs n) x (Pi.single k 1)) :=
    fun n => hψof R (js n)
  have hjsC : Tendsto (fun n =>
      ((js n : cauchySmoothJets d (R : ℝ)) : C(Vec d, ℝ × Vec d))) atTop
      (𝓝 (cauchySmoothJet ψ hψ)) :=
    (continuous_subtype_val.tendsto j₀).comp hjs
  have hpt : ∀ x, Tendsto (fun n =>
      ((js n : cauchySmoothJets d (R : ℝ)) : C(Vec d, ℝ × Vec d)) x) atTop
      (𝓝 (cauchySmoothJet ψ hψ x)) := fun x =>
    ((continuous_eval_const x).tendsto _).comp hjsC
  have hpt0 : ∀ x, Tendsto (fun n => ψs n x) atTop (𝓝 (ψ x)) := by
    intro x
    have hx := (continuous_fst.tendsto _).comp (hpt x)
    simpa [Function.comp_def, (hψs _).2.2 x, cauchySmoothJet] using hx
  have hpt1 : ∀ x, Tendsto (fun n => fderiv ℝ (ψs n) x (Pi.single i 1)) atTop
      (𝓝 (ψ' x)) := by
    intro x
    have hx := ((continuous_apply i).tendsto _).comp
      ((continuous_snd.tendsto _).comp (hpt x))
    simpa [Function.comp_def, (hψs _).2.2 x, cauchySmoothJet, ψ'] using hx
  obtain ⟨M, hM⟩ := hBc.exists_bound_of_continuousOn
    (cauchySmoothJet ψ hψ).continuous.continuousOn
  have hunif := (ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn.1 hjsC) B hBc
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  have hbd : ∀ᶠ n in atTop, ∀ x ∈ B,
      ‖((js n : cauchySmoothJets d (R : ℝ)) : C(Vec d, ℝ × Vec d)) x‖ ≤ M + 1 := by
    filter_upwards [hunif 1 one_pos] with n hn x hx
    have hn' := hn x hx
    rw [dist_comm, dist_eq_norm] at hn'
    calc
      _ = ‖(((js n : cauchySmoothJets d (R : ℝ)) : C(Vec d, ℝ × Vec d)) x -
          cauchySmoothJet ψ hψ x) + cauchySmoothJet ψ hψ x‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
      _ ≤ 1 + M := add_le_add hn'.le (hM x hx)
      _ = M + 1 := add_comm _ _
  have hbd0 : ∀ᶠ n in atTop, ∀ x ∈ B, |ψs n x| ≤ M + 1 := by
    filter_upwards [hbd] with n hn x hx
    have hx' := (norm_fst_le _).trans (hn x hx)
    simpa [(hψs n).2.2 x] using hx'
  have hbd1 : ∀ᶠ n in atTop, ∀ x ∈ B,
      |fderiv ℝ (ψs n) x (Pi.single i 1)| ≤ M + 1 := by
    filter_upwards [hbd] with n hn x hx
    have hx' := ((norm_le_pi_norm _ i).trans (norm_snd_le _)).trans (hn x hx)
    simpa [(hψs n).2.2 x] using hx'
  have hseq : ∀ n,
      (∫ x in B, cauchyJointValue u (x, t) *
          fderiv ℝ (ψs n) x (Pi.single i 1)) +
        ∫ x in B, cauchyJointGradient u (x, t) i * ψs n x = 0 := by
    intro n
    have hn := htests R (⟨js n, hjsD n⟩ : D R) i
    have hc' : Continuous (fun x => fderiv ℝ (ψs n) x (Pi.single i 1)) :=
      (hψs n).1.continuous_fderiv (by simp) |>.clm_apply continuous_const
    have hs' : tsupport (fun x => fderiv ℝ (ψs n) x (Pi.single i 1)) ⊆ B :=
      (tsupport_comp_subset (g := fun L : Vec d →L[ℝ] ℝ => L (Pi.single i 1))
        (by simp) _).trans ((tsupport_fderiv_subset ℝ).trans (hψs n).2.1)
    rw [← (cauchyIntegrable_mul_of_integrableOn hBc huB hc' hs').2,
      ← (cauchyIntegrable_mul_of_integrableOn hBc hgB (hψs n).1.continuous
        (hψs n).2.1).2]
    change (∫ x, cauchyJointValue u (x, t) *
      fderiv ℝ (ψof R (js n)) x (Pi.single i 1)) +
      ∫ x, cauchyJointGradient u (x, t) i * ψof R (js n) x = 0
    rw [hn]
    ring
  have hlim1 : Tendsto (fun n => ∫ x in B, cauchyJointValue u (x, t) *
      fderiv ℝ (ψs n) x (Pi.single i 1)) atTop
      (𝓝 (∫ x in B, cauchyJointValue u (x, t) * ψ' x)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => (M + 1) * ‖cauchyJointValue u (x, t)‖) ?_ ?_
      (huB.norm.const_mul _) ?_
    · exact Eventually.of_forall fun n => huB.aestronglyMeasurable.mul
        ((hψs n).1.continuous_fderiv (by simp) |>.clm_apply continuous_const).aestronglyMeasurable
    · filter_upwards [hbd1] with n hn
      filter_upwards [ae_restrict_mem hBc.measurableSet] with x hx
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (by simpa using hn x hx) (norm_nonneg _)
    · exact Eventually.of_forall fun x => (hpt1 x).const_mul _
  have hlim2 : Tendsto (fun n => ∫ x in B, cauchyJointGradient u (x, t) i * ψs n x)
      atTop (𝓝 (∫ x in B, cauchyJointGradient u (x, t) i * ψ x)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun x => (M + 1) * ‖cauchyJointGradient u (x, t) i‖) ?_ ?_
      (hgB.norm.const_mul _) ?_
    · exact Eventually.of_forall fun n => hgB.aestronglyMeasurable.mul
        (hψs n).1.continuous.aestronglyMeasurable
    · filter_upwards [hbd0] with n hn
      filter_upwards [ae_restrict_mem hBc.measurableSet] with x hx
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right (by simpa using hn x hx) (norm_nonneg _)
    · exact Eventually.of_forall fun x => (hpt0 x).const_mul _
  have hsum := hlim1.add hlim2
  simp only [hseq] at hsum
  have hzero := tendsto_nhds_unique tendsto_const_nhds hsum
  linarith

end PDE.Parabolic.Lions
