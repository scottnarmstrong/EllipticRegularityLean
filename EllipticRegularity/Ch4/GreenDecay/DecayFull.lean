module

public import EllipticRegularity.Ch4.GreenDecay.Duality
public import EllipticRegularity.Ch4.GreenDecay.Algebra2

/-!
# `greenDecay_full`

The exact type of the statement `greenDecay` (Lemma 4.35).
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4GreenDecay

open MeasureTheory PDE PDE.MeyersDuality

theorem decayConst_pos {d : ℕ} (hd : 0 < d) {Cp ω : ℝ} (hCp : 0 < Cp) (hω : 0 < ω) :
    0 < decayConst d Cp ω := by
  have h2d : (2 : ℝ) ≤ 2 ^ d := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ d := pow_le_pow_right₀ (by norm_num) hd
  unfold decayConst
  have h1 : 0 < Real.sqrt ((2 : ℝ) ^ d) := Real.sqrt_pos.2 (by positivity)
  have h2 : 0 < Real.sqrt ((2 : ℝ) ^ d - 1) := Real.sqrt_pos.2 (by linarith)
  have h3 : 0 < Real.sqrt ω := Real.sqrt_pos.2 hω
  positivity

/-- Decay lemma (Lemma 4.35): exact type of the statement `greenDecay`. -/
theorem greenDecay_full (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ R : ℝ), 10 ≤ R → ∀ a : CoeffField d,
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) R))) →
      (∀ x ∈ euclideanBall (0 : Vec d) R, IsEllipticMatrix 1 Λ (a x)) →
      ∀ (β Cs : ℝ), 0 < β → β ≤ 1 → 0 ≤ Cs →
      (∀ ρ : ℝ, 4 ≤ ρ → ρ ≤ R → ∀ w : H1Function (euclideanBall (0 : Vec d) ρ),
        IsWeakDivergenceFormSolutionOn (adjointCoeffField a) (euclideanBall (0 : Vec d) ρ) w
          (0 : Vec d → ℝ) (0 : Vec d → Vec d) →
        ∃ m : ℝ, ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 2)),
          m ≤ w.toFun x ∧
          ENNReal.ofReal (w.toFun x - m) ≤
            ENNReal.ofReal (Cs * ρ ^ (-β)) *
              eLpMeanNormOn (euclideanBall (0 : Vec d) ρ) 2
                (fun y => w.toFun y - integralAverage (euclideanBall (0 : Vec d) ρ) w.toFun)) →
      ∀ f : Vec d → Vec d, MemVectorL2On (euclideanBall (0 : Vec d) 1) f →
      ∀ u : H10Function (euclideanBall (0 : Vec d) R),
      IsWeakDivergenceFormH10SolutionOn a (euclideanBall (0 : Vec d) R) u.toH1Function
        (0 : Vec d → ℝ) ((euclideanBall (0 : Vec d) 1).indicator f) →
      ∀ r : ℝ, 10 ≤ r → r ≤ R →
        eLpMeanNormOn (euclideanBall (0 : Vec d) r \ euclideanBall (0 : Vec d) (r / 2)) 2
            (fun x => u.toH1Function.toFun x -
              integralAverage (euclideanBall (0 : Vec d) r \ euclideanBall (0 : Vec d) (r / 2))
                u.toH1Function.toFun) ≤
          ENNReal.ofReal (C * Cs * Real.sqrt Λ * r ^ (2 - β - (d : ℝ))) *
            eLpNorm (fun x => vecEuclideanNorm (f x)) 2 (volumeOn (euclideanBall (0 : Vec d) 1)) := by
  have hd0 : 0 < d := by omega
  have hω : 0 < (volume (euclideanBall (0 : Vec d) 1)).toReal :=
    volume_euclideanBall_toReal_pos 0 one_pos
  have hCp : (0 : ℝ) < 2 ^ d * 2 := by positivity
  refine ⟨decayConst d (2 ^ d * 2) (volume (euclideanBall (0 : Vec d) 1)).toReal,
    decayConst_pos hd0 hCp hω, ?_⟩
  intro Λ R hR a hmeas hell β Cs hβ0 hβ1 hCs hosc f hf u hu r hr10 hrR
  have hR0 : 0 < R := by linarith
  have hr0 : 0 < r := by linarith
  have hρ0 : 0 < r / 2 := by linarith
  have hρ4 : 4 ≤ r / 2 := by linarith
  have hρR : r / 2 ≤ R := by linarith
  have hrR' : r ≤ R := hrR
  have hUm : MeasurableSet (euclideanBall (0 : Vec d) R) := measurableSet_euclideanBall _ _
  obtain ⟨hbmT, hbellT⟩ := adjoint_coeff_hyps hmeas hell
    (Or.inr rfl : adjointCoeffField a = a ∨ adjointCoeffField a = adjointCoeffField a)
  have hΛ : 1 ≤ Λ := (hell 0 (center_mem_euclideanBall 0 hR0)).lam_le_Lam
  have hg := annulusSource_memL2 hr0 hrR u.toH1Function
  have hF0 : MemVectorL2On (euclideanBall (0 : Vec d) R) (0 : Vec d → Vec d) :=
    fun i => MemLp.zero
  obtain ⟨v, hv⟩ := exists_dirichlet_solution hd0 hR0 hbmT hbellT hg hF0
  -- restriction to `B_{r/2}` and local harmonicity
  have hsolρ := solution_restrict_ball hρ0 hρR hbmT hbellT
    (g := annulusSource d r u.toH1Function.toFun)
    (Filter.eventually_of_mem (self_mem_ae_restrict (measurableSet_euclideanBall _ _))
      fun x hx => annulusSource_eq_zero_of_mem_half _ hx) hv
  have hsubρ : euclideanBall (0 : Vec d) (r / 2) ⊆ euclideanBall (0 : Vec d) R :=
    euclideanBall_mono hρ0.le hρR
  obtain ⟨m, hm⟩ := hosc (r / 2) hρ4 hρR
    (v.toH1Function.restrict (isOpen_euclideanBall 0 (r / 2)) hsubρ) hsolρ
  -- the oscillation bound in `B_2`
  have hfinρ : IsFiniteMeasure (volumeOn (euclideanBall (0 : Vec d) (r / 2))) :=
    isFiniteMeasure_volumeOn_euclideanBall 0 hρ0.le
  have hwL2 : MemL2On (euclideanBall (0 : Vec d) (r / 2))
      (fun y => v.toH1Function.toFun y -
        integralAverage (euclideanBall (0 : Vec d) (r / 2)) v.toH1Function.toFun) := by
    have h := ((v.toH1Function.restrict (isOpen_euclideanBall 0 (r / 2)) hsubρ).memL2).sub
      (memLp_const (integralAverage (euclideanBall (0 : Vec d) (r / 2)) v.toH1Function.toFun))
    exact h
  have hEfin : eLpMeanNormOn (euclideanBall (0 : Vec d) (r / 2)) 2
      (fun y => v.toH1Function.toFun y -
        integralAverage (euclideanBall (0 : Vec d) (r / 2)) v.toH1Function.toFun) ≠ ⊤ := by
    have := memLp_normalizedVolumeOn_of_memLpOn hwL2 (volume_euclideanBall_pos 0 hρ0)
    exact this.eLpNorm_ne_top
  have hρβ : 0 ≤ Cs * (r / 2) ^ (-β) := by positivity
  have hQm : ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 2)), m ≤ v.toH1Function.toFun x ∧
      v.toH1Function.toFun x - m ≤ Cs * (r / 2) ^ (-β) *
        (eLpMeanNormOn (euclideanBall (0 : Vec d) (r / 2)) 2
          (fun y => v.toH1Function.toFun y -
            integralAverage (euclideanBall (0 : Vec d) (r / 2)) v.toH1Function.toFun)).toReal := by
    filter_upwards [hm] with x hx
    refine ⟨hx.1, ?_⟩
    have h2 : ENNReal.ofReal (v.toH1Function.toFun x - m) ≤
        ENNReal.ofReal (Cs * (r / 2) ^ (-β)) *
          eLpMeanNormOn (euclideanBall (0 : Vec d) (r / 2)) 2
            (fun y => v.toH1Function.toFun y -
              integralAverage (euclideanBall (0 : Vec d) (r / 2)) v.toH1Function.toFun) := hx.2
    rw [← ENNReal.ofReal_toReal hEfin, ← ENNReal.ofReal_mul hρβ] at h2
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2
  have hbmρ : ∀ i j : Fin d, AEMeasurable (fun x => adjointCoeffField a x i j)
      (volumeOn (euclideanBall (0 : Vec d) (r / 2))) :=
    fun i j => (hbmT i j).mono_measure (Measure.restrict_mono hsubρ le_rfl)
  have hbellρ : ∀ x ∈ euclideanBall (0 : Vec d) (r / 2),
      IsEllipticMatrix 1 Λ (adjointCoeffField a x) := fun x hx => hbellT x (hsubρ hx)
  have hgrad := local_gradient_bound (Λ := Λ) (ρ := r / 2)
    (m := m) (Q := Cs * (r / 2) ^ (-β) *
        (eLpMeanNormOn (euclideanBall (0 : Vec d) (r / 2)) 2
          (fun y => v.toH1Function.toFun y -
            integralAverage (euclideanBall (0 : Vec d) (r / 2)) v.toH1Function.toFun)).toReal)
    (by linarith) hbmρ hbellρ
    (v.toH1Function.restrict (isOpen_euclideanBall 0 (r / 2)) hsubρ) hsolρ hQm
  have hgu := integral_annulusSource_mul hd0 hr0 hrR u.toH1Function
  have hdual := duality_estimate (by linarith : (1 : ℝ) ≤ R) hf hu hv hgu
  have hgmean := integral_annulusSource hd0 hr0 hrR u.toH1Function
  have henergy := dirichlet_energy_local hr0 hrR hbmT hbellT hg hgmean
    (fun x hx => annulusSource_eq_zero_of_notMem _ hx) hv
  have hpoinc := ball_mean_poincare_restrict hρ0 hρR v.toH1Function
  have hEreal := toReal_eLpMeanNormOn_two hwL2 (volume_euclideanBall_ne_top 0 hρ0.le).lt_top
  have hvolρ := volume_euclideanBall_toReal_eq_unit_mul_of_pos (0 : Vec d) hρ0
  have hvol2 := volume_euclideanBall_toReal_eq_unit_mul_of_pos (0 : Vec d) (by norm_num : (0 : ℝ) < 2)
  have hmonoρ : (∫ x in euclideanBall (0 : Vec d) (r / 2), vecNormSq (v.toH1Function.grad x)) ≤
      ∫ x in euclideanBall (0 : Vec d) R, vecNormSq (v.toH1Function.grad x) :=
    setIntegral_mono_set (integrableOn_vecNormSq_of_memVectorL2On v.toH1Function.gradMemL2)
      (Filter.Eventually.of_forall fun x => vecNormSq_nonneg _)
      (Filter.Eventually.of_forall hsubρ)
  have hG2nn : 0 ≤ ∫ x in euclideanBall (0 : Vec d) R,
      annulusSource d r u.toH1Function.toFun x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hIRnn : 0 ≤ ∫ x in euclideanBall (0 : Vec d) R, vecNormSq (v.toH1Function.grad x) :=
    integral_nonneg fun x => vecNormSq_nonneg _
  have hI1nn : 0 ≤ ∫ x in euclideanBall (0 : Vec d) 1, vecNormSq (v.toH1Function.grad x) :=
    integral_nonneg fun x => vecNormSq_nonneg _
  have hInnf : 0 ≤ ∫ x in euclideanBall (0 : Vec d) 1, vecNormSq (f x) :=
    integral_nonneg fun x => vecNormSq_nonneg _
  have hIρnn : 0 ≤ ∫ x in euclideanBall (0 : Vec d) (r / 2),
      (v.toH1Function.toFun x - integralAverage (euclideanBall (0 : Vec d) (r / 2))
        v.toH1Function.toFun) ^ 2 := integral_nonneg fun x => sq_nonneg _
  have key := decay_algebra hd0
    (ω := (volume (euclideanBall (0 : Vec d) 1)).toReal) (Λ := Λ) (Cs := Cs) (β := β) (r := r)
    (Cp := 2 ^ d * 2)
    (nG := Real.sqrt (∫ x in euclideanBall (0 : Vec d) R,
      annulusSource d r u.toH1Function.toFun x ^ 2))
    (nf := Real.sqrt (∫ x in euclideanBall (0 : Vec d) 1, vecNormSq (f x)))
    (n1 := Real.sqrt (∫ x in euclideanBall (0 : Vec d) 1, vecNormSq (v.toH1Function.grad x)))
    (nR := Real.sqrt (∫ x in euclideanBall (0 : Vec d) R, vecNormSq (v.toH1Function.grad x)))
    (Q := Cs * (r / 2) ^ (-β) *
        (eLpMeanNormOn (euclideanBall (0 : Vec d) (r / 2)) 2
          (fun y => v.toH1Function.toFun y -
            integralAverage (euclideanBall (0 : Vec d) (r / 2)) v.toH1Function.toFun)).toReal)
    (Iρ := ∫ x in euclideanBall (0 : Vec d) (r / 2),
      (v.toH1Function.toFun x - integralAverage (euclideanBall (0 : Vec d) (r / 2))
        v.toH1Function.toFun) ^ 2)
    hω hΛ hβ1 hCs hr0 hCp (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    hIρnn ?_ ?_ ?_ ?_ ?_
  · -- conversion of the goal to real numbers
    have hAmem := annulus_sub_average_memL2 hr0 hrR u.toH1Function
    have hVApos : 0 < volume (annulus d r) := volume_annulus_pos hd0 hr0
    have hVAtop : volume (annulus d r) < ∞ := (volume_annulus_ne_top hr0).lt_top
    have hLHSfin : eLpMeanNormOn (annulus d r) 2
        (fun x => u.toH1Function.toFun x - integralAverage (annulus d r) u.toH1Function.toFun) ≠ ⊤ :=
      (memLp_normalizedVolumeOn_of_memLpOn hAmem hVApos).eLpNorm_ne_top
    have hLHSreal := toReal_eLpMeanNormOn_two hAmem hVAtop
    rw [← integral_annulusSource_sq hr0 hrR u.toH1Function.toFun,
      volume_annulus_toReal hr0, Real.sqrt_div hG2nn] at hLHSreal
    have hfn : MemL2On (euclideanBall (0 : Vec d) 1) (fun x => vecEuclideanNorm (f x)) :=
      GradMemLpOn.memLp_vecEuclideanNorm hf
    have hfnreal := toReal_eLpNorm_two_eq_sqrt hfn
    have hfsq : (∫ x in euclideanBall (0 : Vec d) 1, vecEuclideanNorm (f x) ^ 2) =
        ∫ x in euclideanBall (0 : Vec d) 1, vecNormSq (f x) :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => vecEuclideanNorm_sq' _)
    rw [hfsq] at hfnreal
    have hKnn : 0 ≤ decayConst d (2 ^ d * 2) (volume (euclideanBall (0 : Vec d) 1)).toReal * Cs *
        Real.sqrt Λ * r ^ (2 - β - (d : ℝ)) := by
      have := decayConst_pos hd0 hCp hω
      positivity
    have hfin2 : eLpNorm (fun x => vecEuclideanNorm (f x)) 2
        (volumeOn (euclideanBall (0 : Vec d) 1)) ≠ ⊤ := hfn.eLpNorm_ne_top
    rw [← ENNReal.ofReal_toReal hLHSfin, ← ENNReal.ofReal_toReal hfin2, ← ENNReal.ofReal_mul hKnn]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [hLHSreal, hfnreal]
    exact key
  · rw [Real.sq_sqrt hG2nn]; exact hdual
  · rw [Real.sq_sqrt hI1nn]
    calc (∫ x in euclideanBall (0 : Vec d) 1, vecNormSq (v.toH1Function.grad x))
        ≤ 4 * Λ * (volume (euclideanBall (0 : Vec d) 2)).toReal *
          (Cs * (r / 2) ^ (-β) *
            (eLpMeanNormOn (euclideanBall (0 : Vec d) (r / 2)) 2
              (fun y => v.toH1Function.toFun y -
                integralAverage (euclideanBall (0 : Vec d) (r / 2)) v.toH1Function.toFun)).toReal) ^ 2 :=
          hgrad
      _ = _ := by rw [hvol2]; ring
  · rw [hEreal, hvolρ, mul_comm ((r / 2) ^ d)]
  · rw [Real.sq_sqrt hIRnn]
    calc _ ≤ ((2 : ℝ) ^ d * (2 * (r / 2))) ^ 2 *
          ∫ x in euclideanBall (0 : Vec d) (r / 2), vecNormSq (v.toH1Function.grad x) := hpoinc
      _ ≤ ((2 : ℝ) ^ d * (2 * (r / 2))) ^ 2 *
          ∫ x in euclideanBall (0 : Vec d) R, vecNormSq (v.toH1Function.grad x) :=
          mul_le_mul_of_nonneg_left hmonoρ (sq_nonneg _)
      _ = _ := by ring
  · exact henergy.trans_eq (by ring)

end PDE.Ch4GreenDecay
