module

public import EllipticRegularity.Meyers.DualityAux
public import PDEFoundation.Sobolev.W1p.EuclideanGradient
public import PDEFoundation.Measure.NormalizedLp

/-! # The Dirichlet estimate for `p < 2` by duality

Given the Dirichlet estimate for the conjugate exponent `p' ∈ [2, 2 + c/√Λ]` for all
elliptic fields (applied to the transpose), Lax--Milgram and the test field
`F = |∇u|^{p-2} ∇u` give the Dirichlet estimate for `p ∈ [(2 + c/√Λ)', 2]`. -/

@[expose] public section

open scoped ENNReal

namespace PDE.MeyersDuality

open MeasureTheory

noncomputable section

variable {d : ℕ}

private theorem vecDot_matVecMul_transpose' (x y : Vec d) (A : Mat d) :
    vecDot x (matVecMul (matTranspose A) y) = vecDot (matVecMul A x) y := by
  calc
    vecDot x (matVecMul (matTranspose A) y)
        = ∑ i, ∑ j, x i * (A j i * y j) := by
          unfold vecDot matVecMul matTranspose
          congr with i
          rw [Finset.mul_sum]
          simp only [Matrix.transpose_apply]
    _ = ∑ j, ∑ i, (A j i * x i) * y j := by
          rw [Finset.sum_comm]
          congr with j
          congr with i
          ring
    _ = ∑ j, (∑ i, A j i * x i) * y j := by
          congr with j
          exact (Finset.sum_mul Finset.univ (fun i => A j i * x i) (y j)).symm
    _ = vecDot (matVecMul A x) y := rfl

private theorem vecDot_smul_left' (c : ℝ) (x y : Vec d) :
    vecDot (c • x) y = c * vecDot x y := by
  simp only [vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- Pointwise properties of the test field `|g|^{p-2} g`. -/
theorem testField_facts {p : ℝ} (hp : 1 < p) (g : Vec d) :
    vecEuclideanNorm ((vecEuclideanNorm g) ^ (p - 2) • g) = (vecEuclideanNorm g) ^ (p - 1) ∧
    vecDot ((vecEuclideanNorm g) ^ (p - 2) • g) g = (vecEuclideanNorm g) ^ p := by
  by_cases h : vecEuclideanNorm g = 0
  · have hg : vecNormSq g = 0 := by
      have := vecEuclideanNorm_sq g
      rw [h] at this; simpa using this.symm
    have hg0 : g = 0 := vecNormSq_eq_zero hg
    subst hg0
    rw [h, Real.zero_rpow (by linarith : p - 1 ≠ 0), Real.zero_rpow (by linarith : p ≠ 0),
      smul_zero]
    simp [vecEuclideanNorm, vecNormSq, vecDot]
  · have hr : 0 < vecEuclideanNorm g := lt_of_le_of_ne (vecEuclideanNorm_nonneg g) (Ne.symm h)
    set r := vecEuclideanNorm g with hr'
    constructor
    · rw [vecEuclideanNorm_smul, abs_of_nonneg (Real.rpow_nonneg hr.le _)]
      have : r ^ (p - 1) = r ^ (p - 2) * r := by
        rw [show p - 1 = (p - 2) + 1 by ring, Real.rpow_add hr, Real.rpow_one]
      rw [this]
    · rw [vecDot_smul_left']
      have hsq : vecDot g g = r ^ (2 : ℕ) := (vecEuclideanNorm_sq g).symm
      rw [hsq]
      rw [show p = (p - 2) + 2 by ring, Real.rpow_add hr]
      norm_num

/-- **Dirichlet estimate for `p ≤ 2` from the estimate for the conjugate exponent.**
The hypothesis `HI` is the Dirichlet estimate for exponents `p' ∈ [2, 2 + c/√Λ]`, for all
elliptic coefficient fields of contrast `Λ` (it is applied to the transpose of `a`).
The conclusion is the clause of the Meyers estimate for `p ∈ [(2 + c/√Λ)', 2]`,
with the same constant. -/
theorem dirichlet_low_of_high (hd : 0 < d) (c C : ℝ) (hc : 0 < c)
    (HI : ∀ (Λ : ℝ) (b : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => b x i j)
        (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (b x)) →
      ∀ (p' : ℝ), 2 ≤ p' → p' ≤ 2 + c / Real.sqrt Λ →
      ∀ (F : Vec d → Vec d),
      (∀ i : Fin d, AEStronglyMeasurable (fun x => F x i)
        (volumeOn (euclideanBall (0 : Vec d) 1))) →
      MemLp (fun x => vecEuclideanNorm (F x)) 2
        (volumeOn (euclideanBall (0 : Vec d) 1)) →
      MemLp (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p')
        (volumeOn (euclideanBall (0 : Vec d) 1)) →
      ∀ v : H10Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSolutionOn b (euclideanBall (0 : Vec d) 1)
        v.toH1Function (0 : Vec d → ℝ) F →
        eLpNorm (fun x => vecEuclideanNorm (v.grad x)) (ENNReal.ofReal p')
            (volumeOn (euclideanBall (0 : Vec d) 1)) ≤
          ENNReal.ofReal C *
            eLpNorm (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p')
              (volumeOn (euclideanBall (0 : Vec d) 1)))
    (Λ : ℝ) (a : CoeffField d)
    (ha : ∀ i j : Fin d, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec d) 1)))
    (hell : ∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x))
    (p : ℝ) (hp1 : (2 + c / Real.sqrt Λ) / (1 + c / Real.sqrt Λ) ≤ p) (hp2 : p ≤ 2)
    (f : Vec d → Vec d)
    (hfmeas : ∀ i : Fin d, AEStronglyMeasurable (fun x => f x i)
      (volumeOn (euclideanBall (0 : Vec d) 1)))
    (hf2 : MemLp (fun x => vecEuclideanNorm (f x)) 2
      (volumeOn (euclideanBall (0 : Vec d) 1)))
    (hfp : MemLp (fun x => vecEuclideanNorm (f x)) (ENNReal.ofReal p)
      (volumeOn (euclideanBall (0 : Vec d) 1)))
    (u : H10Function (euclideanBall (0 : Vec d) 1))
    (hu : IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1)
      u.toH1Function (0 : Vec d → ℝ) f) :
    eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
        (volumeOn (euclideanBall (0 : Vec d) 1)) ≤
      ENNReal.ofReal C *
        eLpNorm (fun x => vecEuclideanNorm (f x)) (ENNReal.ofReal p)
          (volumeOn (euclideanBall (0 : Vec d) 1)) := by
  have hBmeas : MeasurableSet (euclideanBall (0 : Vec d) 1) := measurableSet_euclideanBall _ _
  have : IsFiniteMeasure (volumeOn (euclideanBall (0 : Vec d) 1)) := isFiniteMeasure_volumeOn_euclideanBall 0 (by norm_num)
  have h0 : (0 : Vec d) ∈ (euclideanBall (0 : Vec d) 1) := by
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt one_pos]
    simp [vecEuclideanNorm, vecNormSq, vecDot]
  have hΛ : 1 ≤ Λ := (hell 0 h0).lam_le_Lam
  have ht : 0 < c / Real.sqrt Λ := div_pos hc (Real.sqrt_pos.2 (by linarith))
  set t := c / Real.sqrt Λ with htdef
  have hp1' : 1 < p := by
    refine lt_of_lt_of_le ?_ hp1
    rw [lt_div_iff₀ (by linarith)]; linarith
  set q : ℝ := p / (p - 1) with hqdef
  have hpm : 0 < p - 1 := by linarith
  have hq2 : 2 ≤ q := by rw [hqdef, le_div_iff₀ hpm]; linarith
  have hqt : q ≤ 2 + t := by
    rw [hqdef, div_le_iff₀ hpm]
    rw [div_le_iff₀ (by linarith)] at hp1
    nlinarith
  have hqp : q * (p - 1) = p := by rw [hqdef]; field_simp
  have hconj : Real.HolderConjugate p q :=
    Real.holderConjugate_iff.mpr ⟨hp1', by rw [hqdef]; field_simp; ring⟩
  -- gradient of `u`
  set g := u.grad with hg
  set N : Vec d → ℝ := fun x => vecEuclideanNorm (g x) with hNdef
  have hN2 : MemLp N 2 (volumeOn (euclideanBall (0 : Vec d) 1)) := GradMemLpOn.memLp_vecEuclideanNorm u.gradMemL2
  have hNmeas : AEStronglyMeasurable N (volumeOn (euclideanBall (0 : Vec d) 1)) := hN2.aestronglyMeasurable
  have hNp : MemLp N (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) 1)) :=
    hN2.mono_exponent (by simpa using ENNReal.ofReal_le_ofReal hp2)
  set X := eLpNorm N (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) 1)) with hX
  have hXtop : X ≠ ⊤ := hNp.eLpNorm_ne_top
  -- the test field
  set F : Vec d → Vec d := fun x => (N x) ^ (p - 2) • g x with hFdef
  have hFnorm : ∀ x, vecEuclideanNorm (F x) = N x ^ (p - 1) :=
    fun x => (testField_facts hp1' (g x)).1
  have hFdot : ∀ x, vecDot (F x) (g x) = N x ^ p :=
    fun x => (testField_facts hp1' (g x)).2
  have hFcoord : ∀ i : Fin d, AEStronglyMeasurable (fun x => F x i) (volumeOn (euclideanBall (0 : Vec d) 1)) := by
    intro i
    have : AEStronglyMeasurable (fun x => N x ^ (p - 2) * g x i) (volumeOn (euclideanBall (0 : Vec d) 1)) :=
      (hNmeas.aemeasurable.pow_const (p - 2)).aestronglyMeasurable.mul
        (u.gradMemL2 i).aestronglyMeasurable
    simpa only [hFdef, Pi.smul_apply, smul_eq_mul] using this
  have hFq : eLpNorm (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal q) (volumeOn (euclideanBall (0 : Vec d) 1)) =
      X ^ (p - 1) := by
    have := eLpNorm_norm_rpow N hNmeas (p := ENNReal.ofReal q) (q := p - 1) hpm
    rw [← ENNReal.ofReal_mul (by linarith), hqp] at this
    simp only [hFnorm]
    rw [← hX] at this
    rw [← this]
    congr 1
    funext x
    rw [Real.norm_of_nonneg (vecEuclideanNorm_nonneg _)]
  have hFmem : MemLp (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal q) (volumeOn (euclideanBall (0 : Vec d) 1)) := by
    have h2 : eLpNorm (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal q) (volumeOn (euclideanBall (0 : Vec d) 1)) < ⊤ := by
      rw [hFq]
      exact ENNReal.rpow_lt_top_of_nonneg hpm.le hXtop
    exact h2
  have hF2 : MemLp (fun x => vecEuclideanNorm (F x)) 2 (volumeOn (euclideanBall (0 : Vec d) 1)) :=
    hFmem.mono_exponent (by simpa using ENNReal.ofReal_le_ofReal hq2)
  have hFL2 : MemVectorL2On (euclideanBall (0 : Vec d) 1) F :=
    memVectorL2On_euclideanBall_of_memLp_vecEuclideanNorm (p := 2) le_rfl (0 : Vec d)
      one_pos (V := (euclideanBall (0 : Vec d) 1)) subset_rfl (by simpa using hF2) hFcoord
  have hfL2 : MemVectorL2On (euclideanBall (0 : Vec d) 1) f :=
    memVectorL2On_euclideanBall_of_memLp_vecEuclideanNorm (p := 2) le_rfl (0 : Vec d)
      one_pos (V := (euclideanBall (0 : Vec d) 1)) subset_rfl (by simpa using hf2) hfmeas
  -- transposed coefficient field and its solution
  have hbT : ∀ i j : Fin d, AEMeasurable (fun x => matTranspose (a x) i j) (volumeOn (euclideanBall (0 : Vec d) 1)) :=
    fun i j => ha j i
  have hbTell : ∀ x ∈ (euclideanBall (0 : Vec d) 1), IsEllipticMatrix 1 Λ (matTranspose (a x)) :=
    fun x hx => isEllipticMatrix_transpose (hell x hx)
  obtain ⟨v, hv⟩ := exists_h10_solution_of_elliptic hd
    (a := fun x => matTranspose (a x)) hbT hbTell hFL2
  have hvHI := HI Λ (fun x => matTranspose (a x)) hbT hbTell q hq2 hqt F hFcoord hF2 hFmem v hv
  rw [hFq] at hvHI
  -- testing both equations
  have hu10 := IsWeakDivergenceFormSolutionOn.toH10 hBmeas ha hell hfL2 hu
  have hv10 := IsWeakDivergenceFormSolutionOn.toH10 hBmeas hbT hbTell hFL2 hv
  have e1 := (hu10 v).2
  have e2 := (hv10 u).2
  simp only [Pi.zero_apply, zero_mul, integral_zero, zero_sub] at e1 e2
  have e2' : ∫ x in (euclideanBall (0 : Vec d) 1), vecDot (matVecMul (a x) (u.toH1Function.grad x))
      (v.toH1Function.grad x) = -∫ x in (euclideanBall (0 : Vec d) 1), vecDot (F x) (u.toH1Function.grad x) := by
    rw [← e2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show vecDot (matVecMul (a x) (u.toH1Function.grad x)) (v.toH1Function.grad x) =
      vecDot (matVecMul (matTranspose (a x)) (v.toH1Function.grad x))
        (u.toH1Function.grad x)
    rw [vecDot_comm (matVecMul (matTranspose (a x)) _) _, vecDot_matVecMul_transpose']
  have hkey : ∫ x in (euclideanBall (0 : Vec d) 1), vecDot (F x) (g x) = ∫ x in (euclideanBall (0 : Vec d) 1), vecDot (f x) (v.toH1Function.grad x) := by
    change ∫ x in (euclideanBall (0 : Vec d) 1), vecDot (F x) (u.toH1Function.grad x) = _
    linarith
  -- Hölder
  have hgv : MemLp (fun x => vecEuclideanNorm (v.grad x)) 2 (volumeOn (euclideanBall (0 : Vec d) 1)) :=
    GradMemLpOn.memLp_vecEuclideanNorm v.gradMemL2
  have hint_h : Integrable (fun x => vecEuclideanNorm (f x) * vecEuclideanNorm (v.grad x)) (volumeOn (euclideanBall (0 : Vec d) 1)) :=
    hf2.integrable_mul hgv
  have hint_dot : Integrable (fun x => vecDot (f x) (v.grad x)) (volumeOn (euclideanBall (0 : Vec d) 1)) :=
    integrableOn_vecDot_of_memVectorL2On hfL2 v.gradMemL2
  have hle : ∫ x in (euclideanBall (0 : Vec d) 1), vecDot (f x) (v.grad x) ≤
      ∫ x, vecEuclideanNorm (f x) * vecEuclideanNorm (v.grad x) ∂(volumeOn (euclideanBall (0 : Vec d) 1)) :=
    integral_mono hint_dot hint_h fun x =>
      (le_abs_self _).trans (abs_vecDot_le_vecEuclideanNorm_mul _ _)
  have hnn : ∀ x, 0 ≤ vecEuclideanNorm (f x) * vecEuclideanNorm (v.grad x) :=
    fun x => mul_nonneg (vecEuclideanNorm_nonneg _) (vecEuclideanNorm_nonneg _)
  have hh : eLpNorm (fun x => vecEuclideanNorm (f x) * vecEuclideanNorm (v.grad x)) 1 (volumeOn (euclideanBall (0 : Vec d) 1)) =
      ENNReal.ofReal (∫ x, vecEuclideanNorm (f x) * vecEuclideanNorm (v.grad x) ∂(volumeOn (euclideanBall (0 : Vec d) 1))) := by
    rw [eLpNorm_one_eq_lintegral_enorm hint_h.aestronglyMeasurable,
      ofReal_integral_eq_lintegral_ofReal hint_h (Filter.Eventually.of_forall hnn)]
    refine lintegral_congr fun x => ?_
    rw [Real.enorm_of_nonneg (hnn x)]
  have hholder : eLpNorm (fun x => vecEuclideanNorm (f x) * vecEuclideanNorm (v.grad x)) 1 (volumeOn (euclideanBall (0 : Vec d) 1)) ≤
      eLpNorm (fun x => vecEuclideanNorm (f x)) (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) 1)) *
        eLpNorm (fun x => vecEuclideanNorm (v.grad x)) (ENNReal.ofReal q) (volumeOn (euclideanBall (0 : Vec d) 1)) := by
    have := hconj.ennrealOfReal
    have key := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (μ := volumeOn (euclideanBall (0 : Vec d) 1))
      (p := ENNReal.ofReal p) (q := ENNReal.ofReal q) (r := 1)
      (fun x y : ℝ => x * y) 1 (by fun_prop)
      hfp.aestronglyMeasurable hgv.aestronglyMeasurable
      (f := fun x => vecEuclideanNorm (f x)) (g := fun x => vecEuclideanNorm (v.grad x))
      (Filter.Eventually.of_forall fun x => by simp [nnnorm_mul])
    simpa using key
  have hA : ENNReal.ofReal (∫ x in (euclideanBall (0 : Vec d) 1), vecDot (F x) (g x)) = X ^ p := by
    have hp0 : ENNReal.ofReal p ≠ 0 := by simp; linarith
    have h1 := hNp.eLpNorm_eq_integral_rpow_norm hp0 ENNReal.ofReal_ne_top
    rw [ENNReal.toReal_ofReal (by linarith)] at h1
    rw [hX, h1, ENNReal.ofReal_rpow_of_nonneg (by positivity) (by linarith),
      Real.rpow_inv_rpow (integral_nonneg fun x => by positivity) (by linarith)]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hFdot]
    rw [Real.norm_of_nonneg (show 0 ≤ N x from vecEuclideanNorm_nonneg _)]
  -- conclusion
  have hchain : X ^ p ≤ ENNReal.ofReal C * eLpNorm (fun x => vecEuclideanNorm (f x))
      (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) 1)) * X ^ (p - 1) := by
    calc X ^ p = ENNReal.ofReal (∫ x in (euclideanBall (0 : Vec d) 1), vecDot (F x) (g x)) := hA.symm
      _ ≤ ENNReal.ofReal (∫ x, vecEuclideanNorm (f x) * vecEuclideanNorm (v.grad x) ∂(volumeOn (euclideanBall (0 : Vec d) 1))) := by
        apply ENNReal.ofReal_le_ofReal
        rw [hkey]; exact hle
      _ = eLpNorm (fun x => vecEuclideanNorm (f x) * vecEuclideanNorm (v.grad x)) 1 (volumeOn (euclideanBall (0 : Vec d) 1)) := hh.symm
      _ ≤ _ := hholder
      _ ≤ eLpNorm (fun x => vecEuclideanNorm (f x)) (ENNReal.ofReal p) (volumeOn (euclideanBall (0 : Vec d) 1)) *
            (ENNReal.ofReal C * X ^ (p - 1)) := by gcongr
      _ = _ := by ring
  by_cases hX0 : X = 0
  · rw [hX0]; exact zero_le
  · have hpow : X ^ p = X * X ^ (p - 1) := by
      conv_lhs => rw [show p = 1 + (p - 1) by ring]
      rw [ENNReal.rpow_add _ _ hX0 hXtop, ENNReal.rpow_one]
    rw [hpow] at hchain
    have hne0 : X ^ (p - 1) ≠ 0 := by
      intro h
      rcases ENNReal.rpow_eq_zero_iff.1 h with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact hX0 h1
      · linarith
    have hnetop : X ^ (p - 1) ≠ ⊤ := (ENNReal.rpow_lt_top_of_nonneg hpm.le hXtop).ne
    exact (ENNReal.mul_le_mul_iff_left hne0 hnetop).1
      (by simpa only [mul_comm] using hchain)

end

end PDE.MeyersDuality
