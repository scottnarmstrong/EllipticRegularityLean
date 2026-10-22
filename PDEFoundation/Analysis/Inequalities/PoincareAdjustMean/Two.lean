module

public import PDEFoundation.Analysis.Inequalities.PoincareAdjustMean.Half
public import PDEFoundation.Analysis.Inequalities.PoincareAdjustMean.LayerCake
public import PDEFoundation.Analysis.Inequalities.Trudinger.Main

/-!
# Mean-difference bound for `d = 2` and `θ < 1/2` via the Trudinger inequality
-/

@[expose] public section

open scoped ENNReal

namespace PDE.PoincareAdjustMean

open MeasureTheory Real

local notation "𝔹" => euclideanBall (0 : Vec 2) 1

/-- The Gaussian tail of the centered function, from the Trudinger inequality. -/
theorem exists_gaussian_tail :
    ∃ CT : ℝ, 0 < CT ∧ ∀ u : H1Function 𝔹,
      (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2 (volume.restrict 𝔹)).toReal ≠ 0 →
      ∀ t : ℝ, 0 < t →
        (volume {z ∈ 𝔹 | t < |u.toFun z - integralAverage 𝔹 u.toFun|}).toReal ≤
          CT * Real.exp (-(1 / (CT * (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2
            (volume.restrict 𝔹)).toReal ^ 2)) * t ^ 2) := by
  obtain ⟨CT, hCT, hT⟩ := PDE.Trudinger.exists_trudinger_constant_full 2 le_rfl
  refine ⟨CT, hCT, fun u hg t ht => ?_⟩
  let u' : W1pFunction 𝔹 (ENNReal.ofReal ((2 : ℕ) : ℝ)) :=
    { toFun := u.toFun
      grad := u.grad
      memLp := by simpa only [Nat.cast_ofNat, ENNReal.ofReal_ofNat] using u.memL2
      gradMemLp := by intro i; simpa only [Nat.cast_ofNat, ENNReal.ofReal_ofNat] using u.gradMemL2 i
      hasWeakGradient := u.hasWeakGradient }
  have h := hT u' t ht
  simp only [Nat.cast_ofNat, ENNReal.ofReal_ofNat, volumeOn] at h
  have h2 : (2 : ℝ) / (2 - 1) = 2 := by norm_num
  have hu'g : u'.grad = u.grad := rfl
  rw [hu'g] at h
  rw [h2, ite_eq_right_iff.2 (fun h0 => absurd h0 hg)] at h
  refine h.trans (le_of_eq ?_)
  congr 2
  have hg' : (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2 (volume.restrict 𝔹)).toReal ≠ 0 := hg
  rw [Real.rpow_two, div_pow]
  field_simp

/-- Mean-difference bound for `d = 2`, `θ < 1/2`. -/
theorem exists_meanDiff_bound_lt_half_two :
    ∃ M : ℝ, 0 < M ∧ ∀ θ : ℝ, 0 < θ → θ < 1 / 2 →
      ∀ u : H1Function 𝔹, ∀ E : Set (Vec 2), MeasurableSet E → E ⊆ 𝔹 →
        ENNReal.ofReal θ * volume 𝔹 ≤ volume E →
        |integralAverage 𝔹 u.toFun - integralAverage E u.toFun| ≤
          M * Real.sqrt |Real.log θ| *
            (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2 (volume.restrict 𝔹)).toReal := by
  obtain ⟨CT, hCT, hTail⟩ := exists_gaussian_tail
  have hBpos : 0 < volume 𝔹 := volume_euclideanBall_pos 0 one_pos
  have hBtop : volume 𝔹 ≠ ⊤ := volume_euclideanBall_ne_top 0 zero_le_one
  set V : ℝ := (volume 𝔹).toReal with hV
  have hVpos : 0 < V := ENNReal.toReal_pos hBpos.ne' hBtop
  have hs0 : 0 < Real.sqrt (Real.log 2) := Real.sqrt_pos.2 (Real.log_pos (by norm_num))
  have hCT' : 0 < Real.sqrt CT := Real.sqrt_pos.2 hCT
  have hπ : 0 < Real.sqrt (π * CT) := Real.sqrt_pos.2 (by positivity)
  refine ⟨Real.sqrt CT + CT * Real.sqrt (π * CT) / (2 * V * Real.sqrt (Real.log 2)),
    by positivity, fun θ hθ0 hθ u E hE hEB hθE => ?_⟩
  have hE0 : volume E ≠ 0 := by
    intro h
    rw [h, nonpos_iff_eq_zero] at hθE
    rcases mul_eq_zero.1 hθE with h1 | h1
    · simp at h1; linarith
    · exact hBpos.ne' h1
  have hEt : volume E ≠ ⊤ := ne_top_of_le_ne_top hBtop (measure_mono hEB)
  have hEV : θ * V ≤ (volume E).toReal := by
    have := ENNReal.toReal_mono hEt hθE
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hθ0.le] at this
  have hEpos : 0 < (volume E).toReal := ENNReal.toReal_pos hE0 hEt
  set g := (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2 (volume.restrict 𝔹)).toReal with hg
  have hg0 : 0 ≤ g := ENNReal.toReal_nonneg
  set w := fun x => u.toFun x - integralAverage 𝔹 u.toFun with hw
  have hwi : IntegrableOn w 𝔹 volume := (memLp_centered u).integrable (by norm_num)
  have hML2 : MemLp w (ENNReal.ofReal 2) (volume.restrict 𝔹) := by
    simpa only [ENNReal.ofReal_ofNat] using memLp_centered u
  have hN : (eLpNorm w 2 (volume.restrict 𝔹)).toReal ≤ (2 : ℝ) ^ 2 * 2 * g :=
    toReal_eLpNorm_centered_le u
  have hlogθ : Real.log θ < 0 := Real.log_neg hθ0 (by linarith)
  have hlog2 : Real.log 2 ≤ -Real.log θ := by
    have h1 : Real.log θ ≤ Real.log (1 / 2) := Real.log_le_log hθ0 hθ.le
    rw [one_div, Real.log_inv] at h1
    linarith
  set s := Real.sqrt |Real.log θ| with hs
  have hsabs : |Real.log θ| = -Real.log θ := abs_of_neg hlogθ
  have hs0s : Real.sqrt (Real.log 2) ≤ s := by
    rw [hs, hsabs]; exact Real.sqrt_le_sqrt hlog2
  have hspos : 0 < s := lt_of_lt_of_le hs0 hs0s
  rcases hg0.eq_or_lt with hgz | hgpos
  · -- g = 0
    have h1 := abs_avg_sub_avg_le u hE hEB hE0 hEt (q := 2) (by norm_num) hML2
    have h2 : (eLpNorm w (ENNReal.ofReal 2) (volume.restrict 𝔹)).toReal ≤ 0 := by
      simp only [ENNReal.ofReal_ofNat]
      rw [← hgz] at hN; simpa using hN
    have h3 : |integralAverage 𝔹 u.toFun - integralAverage E u.toFun| ≤ 0 :=
      h1.trans (by
        have := mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg hEpos.le (-(1 / (2 : ℝ))))
        simpa using this)
    rw [← hgz]
    simpa using h3
  · have hgne : g ≠ 0 := hgpos.ne'
    set b : ℝ := 1 / (CT * g ^ 2) with hb
    have hbpos : 0 < b := by positivity
    set t0 : ℝ := g * (Real.sqrt CT * s) with ht0
    have ht0nn : 0 ≤ t0 := by positivity
    have hdist : ∀ t : ℝ, 0 < t →
        (volume.restrict 𝔹).real {z | t < |w z|} ≤ CT * Real.exp (-b * t ^ 2) := by
      intro t ht
      have h := hTail u hgne t ht
      rw [Measure.real, Measure.restrict_apply' (measurableSet_euclideanBall 0 1)]
      have hset : ({z | t < |w z|} ∩ 𝔹) =
          {z ∈ 𝔹 | t < |u.toFun z - integralAverage 𝔹 u.toFun|} := by
        ext z; simp only [hw, Set.mem_inter_iff, Set.mem_ofPred_eq]; tauto
      rw [hset]; exact h
    have hJ := integral_posPart_le_of_gaussian_tail (volume.restrict 𝔹) w hwi ht0nn hbpos
      hCT.le hdist
    have hs2 : s ^ 2 = -Real.log θ := by
      rw [hs, hsabs]; exact Real.sq_sqrt (by linarith)
    have hsqCT : Real.sqrt CT ^ 2 = CT := Real.sq_sqrt hCT.le
    have hexp : Real.exp (-b * t0 ^ 2) = θ := by
      have : -b * t0 ^ 2 = Real.log θ := by
        rw [hb, ht0, mul_pow, mul_pow, hsqCT, hs2]; field_simp
      rw [this, Real.exp_log hθ0]
    have hsq : Real.sqrt (π / b) = Real.sqrt (π * CT) * g := by
      have : π / b = (π * CT) * g ^ 2 := by rw [hb]; field_simp
      rw [this, Real.sqrt_mul (by positivity), Real.sqrt_sq hg0]
    rw [hexp, hsq] at hJ
    -- the integral over E
    have hfint : Integrable (fun z => max (|w z| - t0) 0) (volume.restrict 𝔹) :=
      (hwi.abs.sub (integrable_const t0)).pos_part
    have hfE : ∫ x in E, max (|w x| - t0) 0 ≤ ∫ z, max (|w z| - t0) 0 ∂(volume.restrict 𝔹) :=
      setIntegral_mono_set hfint (Filter.Eventually.of_forall fun z => le_max_right _ _)
        (Filter.Eventually.of_forall fun x hx => hEB hx)
    have hEint : ∫ x in E, |w x| ≤ t0 * (volume E).toReal +
        ∫ z, max (|w z| - t0) 0 ∂(volume.restrict 𝔹) := by
      have h1 : ∫ x in E, |w x| ≤ ∫ x in E, (t0 + max (|w x| - t0) 0) :=
        integral_mono (hwi.mono_set hEB).abs
          ((integrableOn_const (C := t0) hEt).add (hfint.mono_measure (Measure.restrict_mono hEB le_rfl)))
          (fun x => by have := le_max_left (|w x| - t0) 0; linarith)
      rw [integral_add (integrableOn_const (C := t0) hEt)
        (hfint.mono_measure (Measure.restrict_mono hEB le_rfl)), setIntegral_const] at h1
      simp only [Measure.real, smul_eq_mul] at h1
      linarith
    have hΔ := avg_sub_avg hEB (integrableOn_ball u) hE0 hEt
    have hΔ' : |integralAverage 𝔹 u.toFun - integralAverage E u.toFun| =
        (volume E).toReal⁻¹ * |∫ x in E, w x| := by
      rw [abs_sub_comm, hΔ, abs_mul, abs_of_pos (inv_pos.2 hEpos)]
    have habsE : |∫ x in E, w x| ≤ ∫ x in E, |w x| := by
      simpa using abs_integral_le_integral_abs (μ := volume.restrict E) (f := w)
    set J := ∫ z, max (|w z| - t0) 0 ∂(volume.restrict 𝔹) with hJdef
    have hE'ne : (volume E).toReal ≠ 0 := hEpos.ne'
    have hstep1 : |integralAverage 𝔹 u.toFun - integralAverage E u.toFun| ≤
        t0 + J / (volume E).toReal := by
      rw [hΔ']
      calc (volume E).toReal⁻¹ * |∫ x in E, w x|
          ≤ (volume E).toReal⁻¹ * (t0 * (volume E).toReal + J) :=
            mul_le_mul_of_nonneg_left (habsE.trans hEint) (inv_nonneg.2 hEpos.le)
        _ = t0 + J / (volume E).toReal := by field_simp
    have hJ2 : J / (volume E).toReal ≤ CT * Real.sqrt (π * CT) * g / (2 * V) := by
      have hJnn : J ≤ CT * θ * (Real.sqrt (π * CT) * g / 2) := hJ
      calc J / (volume E).toReal ≤ CT * θ * (Real.sqrt (π * CT) * g / 2) / (volume E).toReal :=
            div_le_div_of_nonneg_right hJnn hEpos.le
        _ ≤ CT * θ * (Real.sqrt (π * CT) * g / 2) / (θ * V) := by
            apply div_le_div_of_nonneg_left (by positivity) (by positivity) hEV
        _ = _ := by field_simp
    have hJ3 : CT * Real.sqrt (π * CT) * g / (2 * V) ≤
        CT * Real.sqrt (π * CT) / (2 * V * Real.sqrt (Real.log 2)) * s * g := by
      have h1 : 0 ≤ CT * Real.sqrt (π * CT) * g / (2 * V) := by positivity
      have h2 : CT * Real.sqrt (π * CT) / (2 * V * Real.sqrt (Real.log 2)) * s * g =
          (CT * Real.sqrt (π * CT) * g / (2 * V)) * (s / Real.sqrt (Real.log 2)) := by
        field_simp
      rw [h2]
      have h3 : 1 ≤ s / Real.sqrt (Real.log 2) := by rw [le_div_iff₀ hs0]; linarith
      exact le_mul_of_one_le_right h1 h3
    calc |integralAverage 𝔹 u.toFun - integralAverage E u.toFun|
        ≤ t0 + J / (volume E).toReal := hstep1
      _ ≤ g * (Real.sqrt CT * s) + CT * Real.sqrt (π * CT) / (2 * V * Real.sqrt (Real.log 2)) * s * g :=
          by linarith
      _ = _ := by ring

end PDE.PoincareAdjustMean
