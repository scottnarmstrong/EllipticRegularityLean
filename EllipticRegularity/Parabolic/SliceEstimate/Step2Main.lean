module

public import EllipticRegularity.Parabolic.SliceEstimate.Step2Centers
public import EllipticRegularity.Parabolic.SliceEstimate.Bridge

/-!
# Step 2: the identity `∫ φ² v² + ∫ φ² a∇u·∇v + 2 ∫ φ v a∇u·∇φ = 0`
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.Slice

open MeasureTheory Set Filter Topology Metric PDE PDE.Parabolic PDE.Parabolic.Energy
  PDE.Parabolic.WeakSlice

variable {d : ℕ}

theorem ae_slice_integrable {S : Set (Vec d)} (hSc : IsCompact S)
    (hSB : S ⊆ euclideanBall (0 : Vec d) 1) {p : ℝ} (hp : -1 ≤ p) {f : Vec d × ℝ → ℝ}
    (hf : MemLp f 2 (volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0))) :
    ∀ᵐ τ ∂(volume.restrict (Ioc p 0)),
      Integrable (fun x => f (x, τ)) (volume.restrict S) := by
  have hle : (volume.restrict (S ×ˢ Ioc p 0) : Measure (Vec d × ℝ)) ≤
      volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0) :=
    Measure.restrict_mono (prod_mono hSB (Ioc_subset_Ioc_left hp)) le_rfl
  have hfin : IsFiniteMeasure (volume.restrict (S ×ˢ Ioc p 0) : Measure (Vec d × ℝ)) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ, Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_lt_top hSc.measure_lt_top (by simp)
  have hint : Integrable f (volume.restrict (S ×ˢ Ioc p 0)) :=
    (hf.mono_measure hle).integrable one_le_two
  rw [Energy.volume_restrict_prod] at hint
  exact hint.prod_left_ae


theorem abs_parSpaceGrad_le {U : Set (Vec d)} {I : Set ℝ} (φ : ParCutoff U I) (z : Vec d × ℝ) (C : ℝ)
    (h : ‖fderiv ℝ φ.toFun z‖ ≤ C) (i : Fin d) : |parSpaceGrad φ.toFun z i| ≤ C := by
  have h1 := (fderiv ℝ φ.toFun z).le_opNorm (basisVec i, (0 : ℝ))
  have h2 : ‖(basisVec i, (0 : ℝ))‖ ≤ 1 := by
    rw [Prod.norm_def]
    refine max_le ?_ (by simp)
    refine (pi_norm_le_iff_of_nonneg zero_le_one).2 fun j => ?_
    by_cases hj : j = i <;> simp [hj]
  have hC : 0 ≤ C := (norm_nonneg _).trans h
  have h3 : ‖parSpaceGrad φ.toFun z i‖ ≤ ‖fderiv ℝ φ.toFun z‖ * ‖(basisVec i, (0 : ℝ))‖ := h1
  rw [Real.norm_eq_abs] at h3
  calc |parSpaceGrad φ.toFun z i| ≤ ‖fderiv ℝ φ.toFun z‖ * ‖(basisVec i, (0 : ℝ))‖ := h3
    _ ≤ ‖fderiv ℝ φ.toFun z‖ * 1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ ≤ C := by rw [mul_one]; exact h

theorem step2_key {lam Lam : ℝ} {a₀ : Vec d → Mat d}
    (ha : IsParabolicCoeff lam Lam (fun z : Vec d × ℝ => a₀ z.1)
      (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (u v : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0))
    (hu : IsParabolicWeakSolution (fun z : Vec d × ℝ => a₀ z.1)
      (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) u)
    (hv : ∀ ψ : ParTestFunction (euclideanBall (0 : Vec d) 1) (interior (Ioc (-1 : ℝ) 0)),
      ∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0, v.toFun z * ψ.toFun z =
        -∫ z in euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0,
          u.toFun z * parTimeDeriv ψ.toFun z)
    (φ : ParCutoff (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0)) :
    ∫ z, (v.toFun z * (φ.toFun z ^ 2 * v.toFun z) + ∑ i, matVecMul (a₀ z.1) (u.grad z) i *
        (φ.toFun z ^ 2 * v.grad z i + 2 * φ.toFun z * v.toFun z * parSpaceGrad φ.toFun z i))
      ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)) = 0 := by
  have hU : IsOpen (euclideanBall (0 : Vec d) 1) := isOpen_euclideanBall _ _
  have hI : (Ioc (-1 : ℝ) 0).OrdConnected := ordConnected_Ioc
  obtain ⟨K, δ0, hKc, hKU, hδ0, hδ1, hcU, hφ0⟩ := exists_collar hU φ
  obtain ⟨m, hm1, hm0, hmφ⟩ := PDE.ParabCaccioppoli.exists_vanishing_time φ
  set p : ℝ := (-1 + m) / 2 with hp
  have hpm : p < m := by rw [hp]; linarith
  have hp1 : -1 < p := by rw [hp]; linarith
  have hp0 : p < 0 := by linarith
  have hpJ : p ∈ Ioc (-1 : ℝ) 0 := ⟨hp1, hp0.le⟩
  set 𝒦 : Set (Vec d) := cthickening δ0 K with h𝒦
  set S : Set (Vec d) := cthickening δ0 𝒦 with hS
  have h𝒦c : IsCompact 𝒦 := hKc.cthickening
  have hSc : IsCompact S := h𝒦c.cthickening
  have h𝒦U : 𝒦 ⊆ euclideanBall (0 : Vec d) 1 := (cthickening_mono (by linarith) K).trans hcU
  have hSU : S ⊆ euclideanBall (0 : Vec d) 1 := by
    refine (cthickening_cthickening_subset hδ0.le hδ0.le K).trans ?_
    rw [← two_mul]; exact hcU
  have h𝒦S : 𝒦 ⊆ S := self_subset_cthickening _
  have hSm : MeasurableSet S := hSc.measurableSet
  obtain ⟨D, hDK, hDδ, hDp, hDq, -, -, -, -, -, -⟩ := exists_edata_gen ha u v hv (K := 𝒦)
    h𝒦c hδ0 hδ1 h𝒦U hSU hp1 hp0 φ.toFun φ.contDiff
    (fun x hx => hmφ (x, p) ⟨h𝒦U hx, hp1, hp0.le⟩ hpm)
  have hK1 : D.K1 = S := by
    show cthickening D.δ0 D.K = S
    rw [hDδ, hDK]
  have hslabS : S ×ˢ Ioc p 0 ⊆ euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0 :=
    prod_mono hSU (Ioc_subset_Ioc_left hp1.le)
  have hleS : (volume.restrict (S ×ˢ Ioc p 0) : Measure (Vec d × ℝ)) ≤
      volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0) :=
    Measure.restrict_mono hslabS le_rfl
  have hφc : Continuous φ.toFun := φ.contDiff.continuous
  -- boundedness of `φ` and its space-gradient on the slab
  obtain ⟨Cφ, hCφ0, hCφ⟩ := PDE.ParabCaccioppoli.exists_bound hU φ
  -- `L²` facts
  set ψ0 : Vec d × ℝ → ℝ := fun z => φ.toFun z ^ 2 * v.toFun z with hψ0
  set gψ : Fin d → Vec d × ℝ → ℝ := fun i z => φ.toFun z ^ 2 * v.grad z i +
    2 * φ.toFun z * v.toFun z * parSpaceGrad φ.toFun z i with hgψ
  set Fl : Fin d → Vec d × ℝ → ℝ := fun i z => matVecMul (a₀ z.1) (u.grad z) i with hFl
  have hv2S : MemLp v.toFun 2 (volume.restrict (S ×ˢ Ioc p 0)) := v.memL2.mono_measure hleS
  have hψ2 : MemLp ψ0 2 (volume.restrict (S ×ˢ Ioc p 0)) := by
    refine hv2S.of_le_mul (c := Cφ ^ 2) ((hφc.pow 2).aestronglyMeasurable.mul
      hv2S.aestronglyMeasurable) ?_
    filter_upwards [(ae_restrict_iff' (hSm.prod measurableSet_Ioc)).2
      (Eventually.of_forall fun z hz => hz)] with z hz
    have h1 := (hCφ z (hslabS hz)).1
    simp only [hψ0, Real.norm_eq_abs, abs_mul, abs_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) h1 2) (abs_nonneg _)
  have hgψ2 : ∀ i, MemLp (gψ i) 2 (volume.restrict (S ×ˢ Ioc p 0)) := by
    intro i
    have hgv : MemLp (fun z => v.grad z i) 2 (volume.restrict (S ×ˢ Ioc p 0)) :=
      (v.gradMemL2 i).mono_measure hleS
    have hdφ : Continuous fun z : Vec d × ℝ => parSpaceGrad φ.toFun z i :=
      (φ.contDiff.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hae : ∀ᵐ z ∂(volume.restrict (S ×ˢ Ioc p 0)), z ∈ S ×ˢ Ioc p 0 :=
      (ae_restrict_iff' (hSm.prod measurableSet_Ioc)).2 (Eventually.of_forall fun z hz => hz)
    have t1 : MemLp (fun z => φ.toFun z ^ 2 * v.grad z i) 2 (volume.restrict (S ×ˢ Ioc p 0)) := by
      refine hgv.of_le_mul (c := Cφ ^ 2) ((hφc.pow 2).aestronglyMeasurable.mul
        hgv.aestronglyMeasurable) ?_
      filter_upwards [hae] with z hz
      have h1 := (hCφ z (hslabS hz)).1
      simp only [Real.norm_eq_abs, abs_mul, abs_pow]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) h1 2) (abs_nonneg _)
    have t2 : MemLp (fun z => 2 * φ.toFun z * v.toFun z * parSpaceGrad φ.toFun z i) 2
        (volume.restrict (S ×ˢ Ioc p 0)) := by
      refine hv2S.of_le_mul (c := 2 * Cφ * Cφ)
        ((((continuous_const.mul hφc).aestronglyMeasurable.mul hv2S.aestronglyMeasurable).mul
          hdφ.aestronglyMeasurable)) ?_
      filter_upwards [hae] with z hz
      have h1 := (hCφ z (hslabS hz)).1
      have h2 := abs_parSpaceGrad_le φ z Cφ (hCφ z (hslabS hz)).2 i
      simp only [Real.norm_eq_abs, abs_mul, abs_two]
      nlinarith [abs_nonneg (φ.toFun z), abs_nonneg (v.toFun z), abs_nonneg (parSpaceGrad φ.toFun z i),
        mul_nonneg (abs_nonneg (φ.toFun z)) (abs_nonneg (v.toFun z)),
        mul_le_mul h1 h2 (abs_nonneg _) hCφ0]
    exact t1.add t2
  have hFl2 : ∀ i, MemLp (Fl i) 2 (volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)) :=
    fun i => flux_memLp ha u i
  have hFl2S : ∀ i, MemLp (Fl i) 2 (volume.restrict (S ×ˢ Ioc p 0)) := fun i =>
    (hFl2 i).mono_measure hleS
  -- good times
  have hJp : Ioc p 0 ⊆ Ioc (-1 : ℝ) 0 := Ioc_subset_Ioc_left hp1.le
  have hfinS : IsFiniteMeasure (volume.restrict S : Measure (Vec d)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hSc.measure_lt_top⟩
  have hgood : ∀ᵐ τ ∂(volume.restrict (Ioc p 0)),
      HasWeakGradientOn (euclideanBall (0 : Vec d) 1) (parSlice v.toFun τ) (parSlice v.grad τ) ∧
      (∀ i, Integrable (fun x => Fl i (x, τ)) (volume.restrict S)) ∧
      Integrable (fun x => v.toFun (x, τ)) (volume.restrict S) ∧
      (∀ i, Integrable (fun x => v.grad (x, τ) i) (volume.restrict S)) := by
    have h1 := ae_restrict_of_ae_restrict_of_subset hJp v.sliceWeakGradient
    have h2 : ∀ᵐ τ ∂(volume.restrict (Ioc p 0)),
        ∀ i, Integrable (fun x => Fl i (x, τ)) (volume.restrict S) :=
      ae_all_iff.2 fun i => ae_slice_integrable hSc hSU hp1.le (hFl2 i)
    have h3 : ∀ᵐ τ ∂(volume.restrict (Ioc p 0)),
        Integrable (fun x => v.toFun (x, τ)) (volume.restrict S) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with τ hτ
      exact (v.sliceL2loc τ (hJp hτ) S hSc hSU).integrable one_le_two
    have h4 : ∀ᵐ τ ∂(volume.restrict (Ioc p 0)),
        ∀ i, Integrable (fun x => v.grad (x, τ) i) (volume.restrict S) :=
      ae_all_iff.2 fun i => ae_slice_integrable hSc hSU hp1.le (v.gradMemL2 i)
    filter_upwards [h1, h2, h3, h4] with τ a b c e using ⟨a, b, c, e⟩
  have hball : ∀ n, ∀ y ∈ 𝒦, closedBall y (D.aSeq n) ⊆ S := fun n y hy =>
    (closedBall_subset_cthickening hy (D.aSeq n)).trans
      (cthickening_mono (hDδ ▸ D.aSeq_le_δ0 n) 𝒦)
  have hcent := all_centers_ae ha u v hu hv hSm hSU (a := D.aSeq) (𝒦 := 𝒦) D.aSeq_pos hball
    hpJ hp0
  -- the identity at a fixed good time
  have hslice : ∀ᵐ τ ∂(volume.restrict (Ioc p 0)), ∀ n,
      ∫ x in S, (v.toFun (x, τ) * mollT (D.aSeq n) S ψ0 (x, τ) +
        ∑ i, Fl i (x, τ) * mollT (D.aSeq n) S (gψ i) (x, τ)) = 0 := by
    filter_upwards [hgood, hcent, ae_restrict_mem measurableSet_Ioc] with τ hg hc hτ n
    obtain ⟨hwg, hF, hv1, hv2⟩ := hg
    have hτJ : τ ∈ Ioc (-1 : ℝ) 0 := hJp hτ
    have hc' := hc hF hv1 n
    have hφτ : Continuous fun y : Vec d => φ.toFun (y, τ) := (contDiff_slice φ.toFun φ.contDiff τ).continuous
    have hdφτ : ∀ i, Continuous fun y : Vec d => parSpaceGrad φ.toFun (y, τ) i := fun i =>
      ((φ.contDiff.continuous_fderiv one_ne_zero).clm_apply continuous_const).comp
        (continuous_id.prodMk continuous_const)
    have hφ2τ : Continuous fun y : Vec d => φ.toFun (y, τ) ^ 2 := hφτ.pow 2
    have hcoef : ∀ i, Continuous fun y : Vec d => 2 * φ.toFun (y, τ) * parSpaceGrad φ.toFun (y, τ) i :=
      fun i => (continuous_const.mul hφτ).mul (hdφτ i)
    have hψint : Integrable (fun y => ψ0 (y, τ)) (volume.restrict S) := by
      have := integrable_mul_cont hSc hv1 hφ2τ
      exact this.congr (Eventually.of_forall fun y => by simp only [hψ0]; ring)
    have hgint : ∀ i, Integrable (fun y => gψ i (y, τ)) (volume.restrict S) := fun i => by
      have t1 := integrable_mul_cont hSc (hv2 i) hφ2τ
      have t2 := integrable_mul_cont hSc hv1 (hcoef i)
      exact (t1.add t2).congr (Eventually.of_forall fun y => by simp only [hgψ, Pi.add_apply]; ring)
    have hψ0v : ∀ y ∈ S, y ∉ 𝒦 → ψ0 (y, τ) = 0 := fun y hy hy𝒦 => by
      have := hφ0 y (hSU hy) (fun hyK => hy𝒦 (self_subset_cthickening K hyK)) τ hτJ
      simp [hψ0, this]
    have hweak : ∀ i x, ∫ y in S, kern (D.aSeq n) (x - y) * gψ i (y, τ) =
        ∫ y in S, fderiv ℝ (kern (D.aSeq n)) (x - y) (basisVec i) * ψ0 (y, τ) := fun i x =>
      psi_weak_identity v φ hδ0 hKc hcU hφ0 hSc hSU h𝒦S (D.aSeq_pos n)
        (hDδ ▸ D.aSeq_le_δ0 n) hτJ hwg hv1 hv2 x i
    obtain ⟨Ci, hCi⟩ : ∃ Ci : Fin d → ℝ, ∀ i z, |fderiv ℝ (kern (d := d) (D.aSeq n)) z (basisVec i)| ≤ Ci i := by
      have := fun i => kern_fderiv_bound (d := d) (D.aSeq_pos n) (basisVec i)
      choose C hC using this
      exact ⟨C, hC⟩
    obtain ⟨C0, hC0⟩ := kern_bound (d := d) (D.aSeq_pos n)
    have hP : ∀ y ∈ 𝒦, ∫ x in S, (v.toFun (x, τ) * kern (D.aSeq n) (x - y) +
        ∑ i, Fl i (x, τ) * fderiv ℝ (kern (D.aSeq n)) (x - y) (basisVec i)) = 0 := by
      intro y hy
      have := hc' y hy
      unfold PF at this
      rw [integral_add (integrable_mul_kern hv1 (kern_continuous _) C0 hC0 y)
        (integrable_finsetSum _ fun i _ => integrable_mul_kern (hF i)
          (kern_fderiv_continuous _ (basisVec i)) (Ci i) (hCi i) y),
        integral_finsetSum _ fun i _ => integrable_mul_kern (hF i)
          (kern_fderiv_continuous _ (basisVec i)) (Ci i) (hCi i) y]
      exact this
    have key := slice_test_identity hSc (D.aSeq_pos n) (f := fun x => v.toFun (x, τ))
      (ψ := fun y => ψ0 (y, τ)) (F := fun i x => Fl i (x, τ)) (g := fun i y => gψ i (y, τ))
      (𝒦 := 𝒦) hv1 hF hψint hgint hψ0v hweak hP
    simpa only [mollT_eq_setIntegral hSm] using key
  -- vanishing of the mollifications outside `𝒦`
  have hvanish : ∀ n, ∀ x ∈ S, x ∉ 𝒦 → ∀ τ ∈ Ioc (-1 : ℝ) 0, ∀ g : Vec d × ℝ → ℝ,
      (∀ y ∈ S, y ∉ K → g (y, τ) = 0) → mollT (D.aSeq n) S g (x, τ) = 0 := by
    intro n x hx hx𝒦 τ hτ g hg
    rw [mollT_eq_setIntegral hSm]
    refine setIntegral_eq_zero_of_forall_eq_zero fun y hy => ?_
    by_cases hyK : y ∈ K
    · by_cases hk : kern (D.aSeq n) (x - y) = 0
      · rw [hk, zero_mul]
      · exfalso
        apply hx𝒦
        have hle : ‖x - y‖ ≤ D.aSeq n := not_lt.mp fun hlt =>
          hk (kern_eq_zero_of_lt_norm (D.aSeq_pos n) hlt)
        refine mem_cthickening_of_dist_le x y δ0 K hyK ?_
        rw [dist_eq_norm]
        exact hle.trans (hDδ ▸ D.aSeq_le_δ0 n)
    · rw [hg y hy hyK, mul_zero]
  have hψ0K : ∀ τ, ∀ y ∈ S, y ∉ K → τ ∈ Ioc (-1 : ℝ) 0 → ψ0 (y, τ) = 0 := fun τ y hy hyK hτ => by
    simp [hψ0, hφ0 y (hSU hy) hyK τ hτ]
  have hgψK : ∀ τ, ∀ y ∈ S, y ∉ K → τ ∈ Ioc (-1 : ℝ) 0 → ∀ i, gψ i (y, τ) = 0 :=
    fun τ y hy hyK hτ i => by simp [hgψ, hφ0 y (hSU hy) hyK τ hτ]
  -- the joint identity at each scale
  have hμ : D.μ D.q = volume.restrict (𝒦 ×ˢ Ioc p 0) := by
    show volume.restrict (D.K ×ˢ Ioc D.p D.q) = _
    rw [hDK, hDp, hDq]
  have h𝒦slab : 𝒦 ×ˢ Ioc p 0 ⊆ S ×ˢ Ioc p 0 := prod_mono h𝒦S subset_rfl
  have hle𝒦 : (volume.restrict (𝒦 ×ˢ Ioc p 0) : Measure (Vec d × ℝ)) ≤
      volume.restrict (S ×ˢ Ioc p 0) := Measure.restrict_mono h𝒦slab le_rfl
  have hm𝒦 : MeasurableSet (𝒦 ×ˢ Ioc p 0) := h𝒦c.measurableSet.prod measurableSet_Ioc
  have hJ : ∀ n, ∫ z, (v.toFun z * mollT (D.aSeq n) S ψ0 z +
      ∑ i, Fl i z * mollT (D.aSeq n) S (gψ i) z) ∂(volume.restrict (𝒦 ×ˢ Ioc p 0)) = 0 := by
    intro n
    have hΨ : MemLp (mollT (D.aSeq n) S ψ0) 2 (volume.restrict (𝒦 ×ˢ Ioc p 0)) :=
      memLp_mollT hSc hψ2 (D.aSeq_pos n)
    have hG : ∀ i, MemLp (mollT (D.aSeq n) S (gψ i)) 2 (volume.restrict (𝒦 ×ˢ Ioc p 0)) :=
      fun i => memLp_mollT hSc (hgψ2 i) (D.aSeq_pos n)
    have hv𝒦 : MemLp v.toFun 2 (volume.restrict (𝒦 ×ˢ Ioc p 0)) := hv2S.mono_measure hle𝒦
    have hint : Integrable (fun z => v.toFun z * mollT (D.aSeq n) S ψ0 z +
        ∑ i, Fl i z * mollT (D.aSeq n) S (gψ i) z) (volume.restrict (𝒦 ×ˢ Ioc p 0)) :=
      (hv𝒦.integrable_mul hΨ).add (integrable_finsetSum _ fun i _ =>
        ((hFl2S i).mono_measure hle𝒦).integrable_mul (hG i))
    rw [Energy.volume_restrict_prod] at hint ⊢
    rw [integral_prod_symm _ hint]
    have hzero : ∀ᵐ τ ∂(volume.restrict (Ioc p 0)), ∫ x in 𝒦,
        (v.toFun (x, τ) * mollT (D.aSeq n) S ψ0 (x, τ) +
          ∑ i, Fl i (x, τ) * mollT (D.aSeq n) S (gψ i) (x, τ)) = 0 := by
      filter_upwards [hslice, ae_restrict_mem measurableSet_Ioc] with τ hτ hτJ
      have hτJ' : τ ∈ Ioc (-1 : ℝ) 0 := hJp hτJ
      refine Eq.trans ?_ (hτ n)
      refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hSm h𝒦S fun x hx => ?_).symm
      rw [hvanish n x hx.1 hx.2 τ hτJ' ψ0 (fun y hy hyK => hψ0K τ y hy hyK hτJ'),
        Finset.sum_eq_zero fun i _ => by
          rw [hvanish n x hx.1 hx.2 τ hτJ' (gψ i) (fun y hy hyK => hgψK τ y hy hyK hτJ' i),
            mul_zero]]
      simp
    rw [integral_congr_ae hzero]
    simp
  -- the limit `n → ∞`
  have hψ2' : MemLp ψ0 2 (volume.restrict (D.K1 ×ˢ Ioc D.p D.q)) := by
    rw [hK1, hDp, hDq]; exact hψ2
  have hgψ2' : ∀ i, MemLp (gψ i) 2 (volume.restrict (D.K1 ×ˢ Ioc D.p D.q)) := fun i => by
    rw [hK1, hDp, hDq]; exact hgψ2 i
  obtain ⟨-, hΨn, hΨl⟩ := D.conv_mollT (le_refl D.q) hψ2'
  have hGn := fun i => (D.conv_mollT (le_refl D.q) (hgψ2' i))
  rw [hK1, hμ] at hΨn hΨl
  have hGn' : ∀ i, (∀ n, MemLp (mollT (D.aSeq n) S (gψ i)) 2 (volume.restrict (𝒦 ×ˢ Ioc p 0))) ∧
      Tendsto (fun n => eLpNorm (mollT (D.aSeq n) S (gψ i) - gψ i) 2
        (volume.restrict (𝒦 ×ˢ Ioc p 0))) atTop (𝓝 0) := fun i => by
    obtain ⟨-, h1, h2⟩ := hGn i
    rw [hK1, hμ] at h1 h2
    exact ⟨h1, h2⟩
  have hv𝒦 : MemLp v.toFun 2 (volume.restrict (𝒦 ×ˢ Ioc p 0)) := hv2S.mono_measure hle𝒦
  have hψ𝒦 : MemLp ψ0 2 (volume.restrict (𝒦 ×ˢ Ioc p 0)) := hψ2.mono_measure hle𝒦
  have hzeroF : ∀ {μ' : Measure (Vec d × ℝ)} (f : Vec d × ℝ → ℝ),
      Tendsto (fun _ : ℕ => eLpNorm (f - f) 2 μ') atTop (𝓝 0) := fun f => by
    simp only [sub_self, eLpNorm_zero]; exact tendsto_const_nhds
  have t1 := tendsto_integral_mul_of_L2 (μ := volume.restrict (𝒦 ×ˢ Ioc p 0))
    (F := fun _ => v.toFun) (G := fun n => mollT (D.aSeq n) S ψ0) (F0 := v.toFun) (G0 := ψ0)
    (fun _ => hv𝒦) hΨn hv𝒦 hψ𝒦 (hzeroF _) hΨl
  have t2 : ∀ i, Tendsto (fun n => ∫ z, Fl i z * mollT (D.aSeq n) S (gψ i) z
      ∂(volume.restrict (𝒦 ×ˢ Ioc p 0))) atTop
      (𝓝 (∫ z, Fl i z * gψ i z ∂(volume.restrict (𝒦 ×ˢ Ioc p 0)))) := fun i =>
    tendsto_integral_mul_of_L2 (μ := volume.restrict (𝒦 ×ˢ Ioc p 0))
      (F := fun _ => Fl i) (G := fun n => mollT (D.aSeq n) S (gψ i)) (F0 := Fl i) (G0 := gψ i)
      (fun _ => (hFl2S i).mono_measure hle𝒦) (hGn' i).1 ((hFl2S i).mono_measure hle𝒦)
      ((hgψ2 i).mono_measure hle𝒦) (hzeroF _) (hGn' i).2
  have hsumlim := t1.add (tendsto_finsetSum Finset.univ fun i _ => t2 i)
  have hseq : ∀ n, (∫ z, v.toFun z * mollT (D.aSeq n) S ψ0 z ∂(volume.restrict (𝒦 ×ˢ Ioc p 0))) +
      ∑ i, ∫ z, Fl i z * mollT (D.aSeq n) S (gψ i) z ∂(volume.restrict (𝒦 ×ˢ Ioc p 0)) = 0 := by
    intro n
    have i1 : Integrable (fun z => v.toFun z * mollT (D.aSeq n) S ψ0 z)
        (volume.restrict (𝒦 ×ˢ Ioc p 0)) :=
      hv𝒦.integrable_mul (memLp_mollT hSc hψ2 (D.aSeq_pos n))
    have i2 : ∀ i, Integrable (fun z => Fl i z * mollT (D.aSeq n) S (gψ i) z)
        (volume.restrict (𝒦 ×ˢ Ioc p 0)) := fun i =>
      ((hFl2S i).mono_measure hle𝒦).integrable_mul (memLp_mollT hSc (hgψ2 i) (D.aSeq_pos n))
    rw [← integral_finsetSum _ fun i _ => i2 i, ← integral_add i1 (integrable_finsetSum _ fun i _ => i2 i)]
    exact hJ n
  have hlim0 : (∫ z, v.toFun z * ψ0 z ∂(volume.restrict (𝒦 ×ˢ Ioc p 0))) +
      ∑ i, ∫ z, Fl i z * gψ i z ∂(volume.restrict (𝒦 ×ˢ Ioc p 0)) = 0 :=
    tendsto_nhds_unique hsumlim (tendsto_const_nhds.congr fun n => (hseq n).symm)
  -- back to the cylinder
  have hmBJ : MeasurableSet (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0) :=
    hU.measurableSet.prod measurableSet_Ioc
  have hsub𝒦 : 𝒦 ×ˢ Ioc p 0 ⊆ euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0 :=
    prod_mono h𝒦U (Ioc_subset_Ioc_left hp1.le)
  have hvanH : ∀ z ∈ euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0 \ 𝒦 ×ˢ Ioc p 0,
      (v.toFun z * ψ0 z + ∑ i, Fl i z * gψ i z) = 0 := by
    rintro ⟨x, τ⟩ ⟨⟨hx, hτ⟩, hn⟩
    have hφz : φ.toFun (x, τ) = 0 := by
      by_cases hτp : p < τ
      · have hx𝒦 : x ∉ 𝒦 := fun h => hn ⟨h, hτp, hτ.2⟩
        exact hφ0 x hx (fun hxK => hx𝒦 (self_subset_cthickening K hxK)) τ hτ
      · exact hmφ (x, τ) ⟨hx, hτ⟩ (lt_of_le_of_lt (not_lt.mp hτp) hpm)
    simp [hψ0, hgψ, hφz]
  have hcyl : ∫ z, (v.toFun z * ψ0 z + ∑ i, Fl i z * gψ i z)
      ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)) =
      ∫ z, (v.toFun z * ψ0 z + ∑ i, Fl i z * gψ i z)
      ∂(volume.restrict (𝒦 ×ˢ Ioc p 0)) :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hmBJ hsub𝒦 hvanH
  have i1 : Integrable (fun z => v.toFun z * ψ0 z) (volume.restrict (𝒦 ×ˢ Ioc p 0)) :=
    hv𝒦.integrable_mul hψ𝒦
  have i2 : ∀ i, Integrable (fun z => Fl i z * gψ i z) (volume.restrict (𝒦 ×ˢ Ioc p 0)) :=
    fun i => ((hFl2S i).mono_measure hle𝒦).integrable_mul ((hgψ2 i).mono_measure hle𝒦)
  show ∫ z, (v.toFun z * ψ0 z + ∑ i, Fl i z * gψ i z)
      ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)) = 0
  rw [hcyl, integral_add i1 (integrable_finsetSum _ fun i _ => i2 i),
    integral_finsetSum _ fun i _ => i2 i]
  exact hlim0

end PDE.Parabolic.Slice
