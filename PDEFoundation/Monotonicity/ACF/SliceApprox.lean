module

public import PDEFoundation.Monotonicity.ACF.SliceLimit

/-!
# ACF-S2: the Rayleigh bound for a.e. slice of an `L²`-limit of smooth functions

If smooth `wₙ → v` and `∇wₙ → g` in `L²(B_R)`, and the supports of the slices of `wₙ` lie
(uniformly in `n`, `r`) in sets `Ω r`, then the Rayleigh inequality of `ACF.SliceRayleigh` holds
for `(v, g)` at almost every `r ∈ (0, R)`.
-/

@[expose] public section

open MeasureTheory Set Filter

namespace PDE

noncomputable section

variable {d : ℕ}

/-- The radial unit vector `x / |x|` (zero at the origin). -/
def unitDir (x : Vec d) : Vec d := (vecEuclideanNorm x)⁻¹ • x

theorem unitDir_smul {r : ℝ} (hr : 0 < r) {y : Vec d} (hy : vecNormSq y = 1) :
    unitDir (r • y) = y := by
  have h1 : vecEuclideanNorm y = 1 := by
    rw [vecEuclideanNorm, hy, Real.sqrt_one]
  have : vecEuclideanNorm (r • y) = r := by
    rw [vecEuclideanNorm_smul, h1, abs_of_pos hr, mul_one]
  rw [unitDir, this, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]

theorem vecNormSq_unitDir_le (x : Vec d) : vecNormSq (unitDir x) ≤ 1 := by
  unfold unitDir
  rw [vecNormSq_smul, inv_pow, vecEuclideanNorm_sq]
  by_cases h : vecNormSq x = 0
  · simp [h]
  · rw [inv_mul_cancel₀ h]

theorem sq_vecDot_unitDir_le (a x : Vec d) : vecDot a (unitDir x) ^ 2 ≤ vecNormSq a := by
  calc vecDot a (unitDir x) ^ 2 ≤ vecNormSq a * vecNormSq (unitDir x) :=
        sq_vecDot_le_vecNormSq_mul_vecNormSq _ _
    _ ≤ vecNormSq a * 1 := mul_le_mul_of_nonneg_left (vecNormSq_unitDir_le x) (vecNormSq_nonneg a)
    _ = _ := mul_one _

theorem continuous_vecNormSq' : Continuous (fun x : Vec d => vecNormSq x) := by
  have := continuous_vecDot_of_continuous (continuous_id (X := Vec d))
    (continuous_id (X := Vec d))
  exact this

theorem measurable_unitDir_apply (i : Fin d) : Measurable (fun x : Vec d => unitDir x i) := by
  have h1 : Continuous (fun x : Vec d => vecEuclideanNorm x) :=
    Real.continuous_sqrt.comp continuous_vecNormSq'
  have : (fun x : Vec d => unitDir x i) = fun x => (vecEuclideanNorm x)⁻¹ * x i := by
    funext x; simp [unitDir]
  rw [this]
  exact h1.measurable.inv.mul (measurable_pi_apply i)

theorem aestronglyMeasurable_vecDot_unitDir {μ : Measure (Vec d)} {a : Vec d → Vec d}
    (ha : ∀ i, AEStronglyMeasurable (fun x => a x i) μ) :
    AEStronglyMeasurable (fun x => vecDot (a x) (unitDir x)) μ := by
  unfold vecDot
  exact Finset.aestronglyMeasurable_fun_sum _ fun i _ =>
    (ha i).mul (measurable_unitDir_apply i).aestronglyMeasurable

theorem aestronglyMeasurable_vecEuclideanNorm {μ : Measure (Vec d)} {a : Vec d → Vec d}
    (ha : ∀ i, AEStronglyMeasurable (fun x => a x i) μ) :
    AEStronglyMeasurable (fun x => vecEuclideanNorm (a x)) μ := by
  have h : AEStronglyMeasurable (fun x => vecNormSq (a x)) μ := by
    unfold vecNormSq vecDot
    exact Finset.aestronglyMeasurable_fun_sum _ fun i _ => (ha i).mul (ha i)
  exact Real.continuous_sqrt.comp_aestronglyMeasurable h

theorem vecDot_sub_left (a b c : Vec d) : vecDot (a - b) c = vecDot a c - vecDot b c := by
  unfold vecDot
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by simp [sub_mul]

/-- Integrability and convergence data for an `L²(B_R)` approximation `(wₙ, ∇wₙ) → (v, g)`
by `C¹` functions. -/
structure SliceApproxData (R : ℝ) (w : ℕ → Vec d → ℝ) (v : Vec d → ℝ) (g : Vec d → Vec d) :
    Prop where
  w_smooth : ∀ n, ContDiff ℝ 1 (w n)
  v_meas : AEStronglyMeasurable v (volume.restrict (euclideanBall (0 : Vec d) R))
  g_meas : ∀ i, AEStronglyMeasurable (fun x => g x i)
    (volume.restrict (euclideanBall (0 : Vec d) R))
  v_sq : Integrable (fun x => v x ^ 2) (volume.restrict (euclideanBall (0 : Vec d) R))
  g_sq : Integrable (fun x => vecNormSq (g x)) (volume.restrict (euclideanBall (0 : Vec d) R))
  w_sq : ∀ n, Integrable (fun x => w n x ^ 2) (volume.restrict (euclideanBall (0 : Vec d) R))
  dw_sq : ∀ n, Integrable (fun x => vecNormSq (classicalGradient (w n) x))
    (volume.restrict (euclideanBall (0 : Vec d) R))
  diff_sq : ∀ n, Integrable (fun x => vecNormSq (classicalGradient (w n) x - g x))
    (volume.restrict (euclideanBall (0 : Vec d) R))
  diff_v_sq : ∀ n, Integrable (fun x => (w n x - v x) ^ 2)
    (volume.restrict (euclideanBall (0 : Vec d) R))
  conv_v : Tendsto (fun n => ∫ x in euclideanBall (0 : Vec d) R, (w n x - v x) ^ 2) atTop
    (nhds 0)
  conv_g : Tendsto (fun n => ∫ x in euclideanBall (0 : Vec d) R,
    vecNormSq (classicalGradient (w n) x - g x)) atTop (nhds 0)

theorem SliceApproxData.comp {R : ℝ} {w : ℕ → Vec d → ℝ} {v : Vec d → ℝ} {g : Vec d → Vec d}
    (h : SliceApproxData R w v g) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    SliceApproxData R (fun k => w (φ k)) v g where
  w_smooth k := h.w_smooth (φ k)
  v_meas := h.v_meas
  g_meas := h.g_meas
  v_sq := h.v_sq
  g_sq := h.g_sq
  w_sq k := h.w_sq (φ k)
  dw_sq k := h.dw_sq (φ k)
  diff_sq k := h.diff_sq (φ k)
  diff_v_sq k := h.diff_v_sq (φ k)
  conv_v := h.conv_v.comp hφ.tendsto_atTop
  conv_g := h.conv_g.comp hφ.tendsto_atTop

theorem coord_aesm {R : ℝ} {w : ℕ → Vec d → ℝ} {v : Vec d → ℝ} {g : Vec d → Vec d}
    (h : SliceApproxData R w v g) (n : ℕ) (i : Fin d) :
    AEStronglyMeasurable (fun x => classicalGradient (w n) x i)
      (volume.restrict (euclideanBall (0 : Vec d) R)) :=
  (((continuous_apply i).comp
    (PDE.ContDiff.continuous_classicalGradient (h.w_smooth n))).aestronglyMeasurable)

/-- Radial family: slices of `(∇wₙ · x̂)²`. -/
theorem SliceApproxData.subseq_radial [NeZero d] {R : ℝ} {w : ℕ → Vec d → ℝ} {v : Vec d → ℝ}
    {g : Vec d → Vec d} (h : SliceApproxData R w v g) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R)),
      SliceIntegrable (fun x => vecDot (g x) (unitDir x) ^ 2) r ∧
      (∀ k, SliceIntegrable
        (fun x => vecDot (classicalGradient (w (φ k)) x) (unitDir x) ^ 2) r) ∧
      Tendsto (fun k => sliceIntegral
        (fun x => vecDot (classicalGradient (w (φ k)) x) (unitDir x) ^ 2) r) atTop
        (nhds (sliceIntegral (fun x => vecDot (g x) (unitDir x) ^ 2) r)) := by
  refine exists_subseq_sliceIntegral_sq_of_dom
    (pn := fun n x => vecDot (classicalGradient (w n) x) (unitDir x))
    (p := fun x => vecDot (g x) (unitDir x)) (S := fun x => vecNormSq (g x))
    (Sn := fun n x => vecNormSq (classicalGradient (w n) x))
    (Dn := fun n x => vecNormSq (classicalGradient (w n) x - g x))
    (aestronglyMeasurable_vecDot_unitDir h.g_meas)
    (fun n => aestronglyMeasurable_vecDot_unitDir (coord_aesm h n))
    h.g_sq h.dw_sq h.diff_sq
    (fun x => sq_vecDot_unitDir_le _ _) (fun n x => sq_vecDot_unitDir_le _ _)
    (fun n x => ?_) h.conv_g
  rw [← vecDot_sub_left]
  exact sq_vecDot_unitDir_le _ _

/-- Value family: slices of `wₙ²`. -/
theorem SliceApproxData.subseq_value [NeZero d] {R : ℝ} {w : ℕ → Vec d → ℝ} {v : Vec d → ℝ}
    {g : Vec d → Vec d} (h : SliceApproxData R w v g) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R)),
      SliceIntegrable (fun x => v x ^ 2) r ∧
      (∀ k, SliceIntegrable (fun x => w (φ k) x ^ 2) r) ∧
      Tendsto (fun k => sliceIntegral (fun x => w (φ k) x ^ 2) r) atTop
        (nhds (sliceIntegral (fun x => v x ^ 2) r)) := by
  refine exists_subseq_sliceIntegral_sq_of_dom (pn := w) (p := v) (S := fun x => v x ^ 2)
    (Sn := fun n x => w n x ^ 2) (Dn := fun n x => (w n x - v x) ^ 2)
    h.v_meas (fun n => (h.w_smooth n).continuous.aestronglyMeasurable) h.v_sq h.w_sq
    h.diff_v_sq (fun x => le_rfl) (fun n x => le_rfl) (fun n x => le_rfl) h.conv_v

theorem sq_vecEuclideanNorm_sub_le (a b : Vec d) :
    (vecEuclideanNorm a - vecEuclideanNorm b) ^ 2 ≤ vecNormSq (a - b) := by
  have h1 : vecEuclideanNorm a ≤ vecEuclideanNorm (a - b) + vecEuclideanNorm b := by
    simpa using vecEuclideanNorm_add_le (a - b) b
  have h2 : vecEuclideanNorm b ≤ vecEuclideanNorm (a - b) + vecEuclideanNorm a := by
    have := vecEuclideanNorm_add_le (b - a) a
    rwa [vecEuclideanNorm_sub_comm, sub_add_cancel] at this
  have h3 : |vecEuclideanNorm a - vecEuclideanNorm b| ≤ vecEuclideanNorm (a - b) :=
    abs_le.2 ⟨by linarith, by linarith⟩
  rw [← vecEuclideanNorm_sq, ← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) h3 2

/-- Gradient-norm family: slices of `|∇wₙ|²`. -/
theorem SliceApproxData.subseq_gradient [NeZero d] {R : ℝ} {w : ℕ → Vec d → ℝ}
    {v : Vec d → ℝ} {g : Vec d → Vec d} (h : SliceApproxData R w v g) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R)),
      SliceIntegrable (fun x => vecNormSq (g x)) r ∧
      (∀ k, SliceIntegrable (fun x => vecNormSq (classicalGradient (w (φ k)) x)) r) ∧
      Tendsto (fun k => sliceIntegral
        (fun x => vecNormSq (classicalGradient (w (φ k)) x)) r) atTop
        (nhds (sliceIntegral (fun x => vecNormSq (g x)) r)) := by
  obtain ⟨φ, hφ, hae⟩ := exists_subseq_sliceIntegral_sq_of_dom
    (pn := fun n x => vecEuclideanNorm (classicalGradient (w n) x))
    (p := fun x => vecEuclideanNorm (g x)) (S := fun x => vecNormSq (g x))
    (Sn := fun n x => vecNormSq (classicalGradient (w n) x))
    (Dn := fun n x => vecNormSq (classicalGradient (w n) x - g x))
    (aestronglyMeasurable_vecEuclideanNorm h.g_meas)
    (fun n => aestronglyMeasurable_vecEuclideanNorm (coord_aesm h n))
    h.g_sq h.dw_sq h.diff_sq
    (fun x => (vecEuclideanNorm_sq _).le) (fun n x => (vecEuclideanNorm_sq _).le)
    (fun n x => sq_vecEuclideanNorm_sub_le _ _) h.conv_g
  exact ⟨φ, hφ, by simpa only [vecEuclideanNorm_sq] using hae⟩

/-- Rayleigh bound for the slices of an `L²(B_R)` limit of smooth functions whose slice supports
lie in `Ω r`. -/
theorem SliceApproxData.rayleigh_ae [NeZero d] {R : ℝ} {w : ℕ → Vec d → ℝ} {v : Vec d → ℝ}
    {g : Vec d → Vec d} (h : SliceApproxData R w v g) {Ω : ℝ → Set (Vec d)}
    (hΩ : ∀ᶠ n in atTop, ∀ r ∈ Ioo (0 : ℝ) R,
      closure {x | x ∈ euclideanSphere (0 : Vec d) 1 ∧ w n (r • x) ≠ 0} ⊆ Ω r) :
    ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R)),
      SliceIntegrable (fun x => vecNormSq (g x)) r ∧ SliceIntegrable (fun x => v x ^ 2) r ∧
      SliceIntegrable (fun x => vecDot (g x) (unitDir x) ^ 2) r ∧
      sliceIntegral (fun x => vecDot (g x) (unitDir x) ^ 2) r +
          (sphereDirichletEigenvalue d (Ω r)).toReal * r⁻¹ ^ 2 *
            sliceIntegral (fun x => v x ^ 2) r ≤
        sliceIntegral (fun x => vecNormSq (g x)) r := by
  obtain ⟨φ1, hφ1, hB⟩ := h.subseq_radial
  have h2 := h.comp hφ1
  obtain ⟨φ2, hφ2, hC⟩ := h2.subseq_value
  have h3 := h2.comp hφ2
  obtain ⟨φ3, hφ3, hA⟩ := h3.subseq_gradient
  have hψ : StrictMono fun k => φ1 (φ2 (φ3 k)) := hφ1.comp (hφ2.comp hφ3)
  have hΩ' := hψ.tendsto_atTop.eventually hΩ
  have hmem : ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R)), r ∈ Ioo (0 : ℝ) R :=
    ae_restrict_mem measurableSet_Ioo
  filter_upwards [hB, hC, hA, hmem] with r ⟨hB1, hB2, hB3⟩ ⟨hC1, hC2, hC3⟩ ⟨hA1, hA2, hA3⟩ hr
  refine ⟨hA1, hC1, hB1, ?_⟩
  have hB3' := hB3.comp (hφ2.comp hφ3).tendsto_atTop
  have hC3' := hC3.comp hφ3.tendsto_atTop
  have hlim := (hB3'.add (hC3'.const_mul
    ((sphereDirichletEigenvalue d (Ω r)).toReal * r⁻¹ ^ 2)))
  refine le_of_tendsto_of_tendsto hlim hA3 ?_
  filter_upwards [hΩ'] with k hk
  have hr0 : r ≠ 0 := hr.1.ne'
  have hineq := sphereIntegral_gradient_slice_ge (h.w_smooth (φ1 (φ2 (φ3 k)))) hr0 (hk r hr)
  have hrad : sliceIntegral (fun x => vecDot (classicalGradient (w (φ1 (φ2 (φ3 k)))) x)
        (unitDir x) ^ 2) r =
      sphereIntegral (0 : Vec d) 1 (fun y => vecDot
        (classicalGradient (w (φ1 (φ2 (φ3 k)))) (r • y)) y ^ 2) := by
    unfold sliceIntegral
    refine sphereIntegral_zero_congr fun y hy => ?_
    rw [mem_euclideanSphere_zero_iff] at hy
    simp only [unitDir_smul hr.1 (by simpa using hy)]
  simp only [Function.comp_apply]
  rw [hrad]
  unfold sliceIntegral at *
  simp only [mul_assoc] at hineq ⊢
  exact hineq

end

end PDE
