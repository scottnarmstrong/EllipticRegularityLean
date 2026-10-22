module

public import EllipticRegularity.Euler.PeriodicCZBall
public import PDEFoundation.Euler.PeriodicCZTile
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Per-ball CZ bound for the components of a periodic divergence-free field

For `u` smooth, periodic, divergence free with `|curl u| ≤ M`, every component `uᵢ` and centre `z ∈ [0,1]²`:
`∫_{B_{1/2}} |∇uᵢ(z + x)|^p dx ≤ |B_{1/2}| (C (c₀ M + p M))^p`, `c₀ = 3 / √|B₁|`, `C` the absolute CZ constant.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

theorem classicalGradient_comp_add_left (g : Vec 2 → ℝ) (z x : Vec 2) :
    classicalGradient (fun y => g (z + y)) x = classicalGradient g (z + x) := by
  funext i
  simp only [classicalGradient_apply]
  rw [fderiv_comp_add_left]

theorem volume_torusCube : volume torusCube = 1 := by
  rw [torusCube, Real.volume_Icc_pi]
  simp

/-- Ball CZ estimate for a translate of a global smooth solution of `Δ g = -∂_k h`. -/
theorem exists_ball_cz_translate :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ p : ℝ, 2 ≤ p → ∀ (g h : Vec 2 → ℝ) (k : Fin 2) (M : ℝ) (z : Vec 2),
      ContDiff ℝ (⊤ : ℕ∞) g → ContDiff ℝ (⊤ : ℕ∞) h → 0 ≤ M → (∀ x, |h x| ≤ M) →
      (∀ x, torusLap g x = -pd k h x) →
      ∫ x in euclideanBall (0 : Vec 2) (1 / 2 : ℝ),
          vecEuclideanNorm (classicalGradient g (z + x)) ^ p ≤
        (volume (euclideanBall (0 : Vec 2) (1 / 2 : ℝ))).toReal *
          (C * (Real.sqrt ((volume (euclideanBall (0 : Vec 2) 1)).toReal⁻¹ *
              ∫ x in euclideanBall (0 : Vec 2) 1, vecNormSq (classicalGradient g (z + x))) +
            p * M)) ^ p := by
  obtain ⟨C, hC1, hC⟩ := exists_ball_cz_integral
  refine ⟨C, hC1, ?_⟩
  intro p hp g h k M z hg hh hM hhM hlap
  have hg' := contDiff_translate hg z
  have hh' := contDiff_translate hh z
  have := hC p hp (fun x => g (z + x)) (fun x => h (z + x)) k M hg' hh' hM (fun x => hhM _) (by
    intro x
    rw [torusLap_comp_add_left, hlap, pd_comp_add_left])
  simpa only [classicalGradient_comp_add_left, integralAverage] using this

theorem contDiff_torusCurl {u : Vec 2 → Vec 2} (hu : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => u x i)) :
    ContDiff ℝ (⊤ : ℕ∞) (torusCurl u) :=
  ContDiff.sub (contDiff_pd_top (hu 1) 0) (contDiff_pd_top (hu 0) 1)

theorem vecNormSq_classicalGradient (g : Vec 2 → ℝ) (x : Vec 2) :
    vecNormSq (classicalGradient g x) = ∑ j, pd j g x ^ 2 := by
  simp only [vecNormSq, vecDot, classicalGradient_apply, sq]
  rfl

/-- Energy of one component over a translated unit ball is controlled by `9 M²`. -/
theorem component_energy_bound {u : Vec 2 → Vec 2}
    (hu : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => u x i)) (hup : IsTorusPeriodic u)
    (hdiv : ∀ x, torusDiv u x = 0) {M : ℝ} (hω : ∀ x, |torusCurl u x| ≤ M) (i : Fin 2) {z : Vec 2}
    (hz : z ∈ torusCube) :
    ∫ x in euclideanBall (0 : Vec 2) 1, vecNormSq (classicalGradient (fun y => u y i) (z + x)) ≤
      9 * M ^ 2 := by
  have hcont : ∀ i j, Continuous (pd j (fun y => u y i)) := fun i j =>
    (contDiff_pd_top (hu i) j).continuous
  have hf : ∀ i, Continuous (fun y => vecNormSq (classicalGradient (fun y => u y i) y)) := by
    intro i
    simp only [vecNormSq_classicalGradient]
    exact continuous_finsetSum _ fun j _ => (hcont i j).pow 2
  have hper : ∀ i, IsTorusPeriodic (fun y => vecNormSq (classicalGradient (fun y => u y i) y)) := by
    intro i
    simp only [vecNormSq_classicalGradient]
    intro a x
    refine Finset.sum_congr rfl fun j _ => ?_
    have := (IsTorusPeriodic.pd (hup.comp (fun v => v i)) j) a x
    simp only [this]
  have hnn : ∀ i y, 0 ≤ vecNormSq (classicalGradient (fun y => u y i) y) := fun i y => vecNormSq_nonneg _
  have h1 := setIntegral_ball_comp_add_le (hf i) (hper i) (hnn i) hz
  have hE : ∫ x in torusCube, ∑ i, ∑ j, pd j (fun y => u y i) x ^ 2 =
      ∫ x in torusCube, torusCurl u x ^ 2 :=
    integral_sq_gradient_eq_integral_sq_curl hu hup hdiv
  have hsum : ∀ y, vecNormSq (classicalGradient (fun y => u y i) y) ≤ ∑ i, ∑ j, pd j (fun y => u y i) y ^ 2 := by
    intro y
    rw [vecNormSq_classicalGradient]
    exact Finset.single_le_sum (f := fun i => ∑ j, pd j (fun y => u y i) y ^ 2)
      (fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have hIcc : ∀ {F : Vec 2 → ℝ}, Continuous F → IntegrableOn F torusCube :=
    fun hF => hF.continuousOn.integrableOn_Icc
  have hsumc : Continuous (fun y => ∑ i, ∑ j, pd j (fun y => u y i) y ^ 2) :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => (hcont i j).pow 2
  have h2 : ∫ x in torusCube, vecNormSq (classicalGradient (fun y => u y i) x) ≤
      ∫ x in torusCube, ∑ i, ∑ j, pd j (fun y => u y i) x ^ 2 :=
    setIntegral_mono (hIcc (hf i)) (hIcc hsumc) hsum
  have hωc : Continuous (torusCurl u) := (contDiff_torusCurl hu).continuous
  have h3 : ∫ x in torusCube, torusCurl u x ^ 2 ≤ ∫ x in torusCube, M ^ 2 :=
    setIntegral_mono (hIcc (hωc.pow 2)) (integrableOn_const (by rw [volume_torusCube]; exact ENNReal.one_ne_top))
      (fun x => by
        have := hω x
        have h0 : 0 ≤ M := le_trans (abs_nonneg _) this
        have := sq_le_sq' (abs_le.mp this).1 (abs_le.mp this).2
        exact this)
  have h4 : ∫ x in torusCube, M ^ 2 = M ^ 2 := by
    rw [setIntegral_const]
    simp [Measure.real, volume_torusCube]
  linarith

/-- `|B_{1/2}|` as a real number. -/
noncomputable def ballVolHalf : ℝ := (volume (euclideanBall (0 : Vec 2) (1 / 2 : ℝ))).toReal

/-- `|B_1|` as a real number. -/
noncomputable def ballVolOne : ℝ := (volume (euclideanBall (0 : Vec 2) 1)).toReal

theorem ballVolHalf_nonneg : 0 ≤ ballVolHalf := ENNReal.toReal_nonneg

theorem ballVolOne_nonneg : 0 ≤ ballVolOne := ENNReal.toReal_nonneg

/-- **Component CZ bound on a ball** for smooth periodic divergence-free `u` with `|curl u| ≤ M`. -/
theorem exists_component_cz :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ p : ℝ, 2 ≤ p → ∀ (u : Vec 2 → Vec 2) (M : ℝ),
      (∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => u x i)) → IsTorusPeriodic u → (∀ x, torusDiv u x = 0) →
      (∀ x, |torusCurl u x| ≤ M) → ∀ (i : Fin 2) (z : Vec 2), z ∈ torusCube →
      ∫ x in euclideanBall (0 : Vec 2) (1 / 2 : ℝ),
          vecEuclideanNorm (classicalGradient (fun y => u y i) (z + x)) ^ p ≤
        ballVolHalf * (C * ((3 * Real.sqrt ballVolOne⁻¹) * M + p * M)) ^ p := by
  obtain ⟨C, hC1, hC⟩ := exists_ball_cz_translate
  refine ⟨C, hC1, ?_⟩
  intro p hp u M hu hup hdiv hω i z hz
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hω 0)
  have hp0 : 0 ≤ p := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hν : 0 ≤ ballVolOne⁻¹ := inv_nonneg.mpr ballVolOne_nonneg
  have key : ∀ A : ℝ, A ≤ 9 * M ^ 2 →
      ballVolHalf * (C * (Real.sqrt (ballVolOne⁻¹ * A) + p * M)) ^ p ≤
        ballVolHalf * (C * ((3 * Real.sqrt ballVolOne⁻¹) * M + p * M)) ^ p := by
    intro A hA
    refine mul_le_mul_of_nonneg_left ?_ ballVolHalf_nonneg
    have hs : Real.sqrt (ballVolOne⁻¹ * A) ≤ (3 * Real.sqrt ballVolOne⁻¹) * M := by
      rw [Real.sqrt_le_iff]
      refine ⟨by positivity, ?_⟩
      have : ((3 * Real.sqrt ballVolOne⁻¹) * M) ^ 2 = ballVolOne⁻¹ * (9 * M ^ 2) := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hν]; ring
      rw [this]
      exact mul_le_mul_of_nonneg_left hA hν
    have hbase : 0 ≤ C * (Real.sqrt (ballVolOne⁻¹ * A) + p * M) := by positivity
    exact Real.rpow_le_rpow hbase (mul_le_mul_of_nonneg_left (by linarith) hC0) hp0
  have hen := component_energy_bound hu hup hdiv hω i hz
  have hcurl := contDiff_torusCurl hu
  fin_cases i
  · have := hC p hp (fun y => u y 0) (torusCurl u) 1 M z (hu 0) hcurl hM hω
      (fun x => torusLap_fst hu hdiv x)
    exact this.trans (key _ hen)
  · have hneg : ContDiff ℝ (⊤ : ℕ∞) (fun x => -torusCurl u x) := ContDiff.neg hcurl
    have := hC p hp (fun y => u y 1) (fun x => -torusCurl u x) 0 M z (hu 1) hneg hM
      (fun x => by simpa using hω x)
      (fun x => by rw [torusLap_snd hu hdiv x, pd_neg]; simp)
    exact this.trans (key _ hen)

end PDE
