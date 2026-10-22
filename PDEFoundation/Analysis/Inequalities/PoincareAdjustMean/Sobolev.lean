module

public import PDEFoundation.Analysis.Inequalities.PoincareAdjustMean.Setup
public import SobolevStatements.ConvexSobolevPoincare

/-!
# `L^{2*}` bound for the centered function on the unit ball (`d ≥ 3`)

Consequence of the proved convex Sobolev--Poincaré inequality with `p = 2`
(display (1.13)), converted from normalized to unnormalized norms.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.PoincareAdjustMean

open MeasureTheory

/-- For `d ≥ 3`, `‖u - (u)_B‖_{L^{2d/(d-2)}(B)} ≤ K ‖∇u‖_{L²(B)}`. -/
theorem exists_sobolev_bound (d : ℕ) (hd : 3 ≤ d) :
    ∃ K : ℝ, 0 < K ∧ ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      MemLp (fun x => u.toFun x - integralAverage (euclideanBall (0 : Vec d) 1) u.toFun)
          (ENNReal.ofReal (2 * d / ((d : ℝ) - 2)))
          (volume.restrict (euclideanBall (0 : Vec d) 1)) ∧
      (eLpNorm (fun x => u.toFun x - integralAverage (euclideanBall (0 : Vec d) 1) u.toFun)
          (ENNReal.ofReal (2 * d / ((d : ℝ) - 2)))
          (volume.restrict (euclideanBall (0 : Vec d) 1))).toReal ≤
        K * (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2
          (volume.restrict (euclideanBall (0 : Vec d) 1))).toReal := by
  have hd2 : 2 ≤ d := by omega
  obtain ⟨C, hC, hS⟩ := exists_convexSobolevPoincare_constant d hd2
  set B := euclideanBall (0 : Vec d) 1 with hB
  have hV := ball_isOpenBoundedConvexDomain d
  have hpos : 0 < volume B := volume_euclideanBall_pos 0 one_pos
  have htop : volume B < ⊤ := lt_top_iff_ne_top.2 (volume_euclideanBall_ne_top 0 zero_le_one)
  have hdR : (2 : ℝ) < d := by exact_mod_cast (by omega : 2 < d)
  set q : ℝ := 2 * d / ((d : ℝ) - 2) with hq
  have hqc : sobolevConjugate d 2 = q := by unfold sobolevConjugate; rw [hq]; ring
  set K0 : ℝ := C * (2 * ((d : ℝ) - 1) / ((d : ℝ) - 2)) * 2 with hK0
  have hK0pos : 0 < K0 := by
    have : 0 < (d : ℝ) - 2 := by linarith
    have : 0 < (d : ℝ) - 1 := by linarith
    positivity
  set V : ℝ := (volume B).toReal with hV0
  have hVpos : 0 < V := ENNReal.toReal_pos hpos.ne' htop.ne
  have hq0 : 0 < q := by
    have : 0 < (d : ℝ) - 2 := by linarith
    positivity
  refine ⟨V ^ (1 / q) * K0 * V⁻¹ ^ (1 / (2 : ℝ)), by positivity, fun u => ?_⟩
  let u' : W1pFunction B (ENNReal.ofReal 2) :=
    { toFun := u.toFun
      grad := u.grad
      memLp := by simpa only [ENNReal.ofReal_ofNat] using u.memL2
      gradMemLp := by intro i; simpa only [ENNReal.ofReal_ofNat] using u.gradMemL2 i
      hasWeakGradient := u.hasWeakGradient }
  have h := hS 2 (by norm_num) (by exact_mod_cast (by omega : 2 < d)) B 2 hV (euclideanBall_nonempty 0 one_pos)
    (by simpa using hasEuclideanDiameterLE_euclideanBall (d := d) 0 one_pos) u'
  rw [hqc] at h
  have hu'1 : u'.toFun = u.toFun := rfl
  have e1 := eLpNormOn_eq_volume_rpow_mul_eLpMeanNormOn hpos htop (ENNReal.ofReal q)
    (fun x => u.toFun x - integralAverage B u.toFun)
  have e2 := euclideanFieldELpMeanNormOn_eq_volume_inv_rpow_mul htop (ENNReal.ofReal 2) u.grad
  simp only [eLpNormOn, volumeOn] at e1
  have hfin : eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2 (volume.restrict B) ≠ ⊤ :=
    (memLp_grad u).eLpNorm_ne_top
  have hexp1 : (1 / ENNReal.ofReal q).toReal = 1 / q := by
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal hq0.le]; simp
  have hexp2 : (1 / ENNReal.ofReal 2).toReal = 1 / (2 : ℝ) := by
    rw [ENNReal.toReal_div, ENNReal.toReal_ofReal (by norm_num)]; simp
  rw [hexp1] at e1
  rw [hexp2] at e2
  have hK : ENNReal.ofReal (V ^ (1 / q) * K0 * V⁻¹ ^ (1 / (2 : ℝ))) =
      (volume B) ^ (1 / q) * ENNReal.ofReal K0 * (volume B)⁻¹ ^ (1 / (2 : ℝ)) := by
    have hvB : volume B = ENNReal.ofReal V := (ENNReal.ofReal_toReal htop.ne).symm
    rw [hvB, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_rpow_of_pos hVpos, ← ENNReal.ofReal_inv_of_pos hVpos,
      ENNReal.ofReal_rpow_of_pos (inv_pos.2 hVpos)]
  have hmain : eLpNorm (fun x => u.toFun x - integralAverage B u.toFun) (ENNReal.ofReal q)
      (volume.restrict B) ≤
      ENNReal.ofReal (V ^ (1 / q) * K0 * V⁻¹ ^ (1 / (2 : ℝ))) *
        eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2 (volume.restrict B) := by
    rw [hK, e1]
    have h' : eLpMeanNormOn B (ENNReal.ofReal q) (fun x => u.toFun x - integralAverage B u.toFun) ≤
        ENNReal.ofReal K0 * ((volume B)⁻¹ ^ (1 / (2 : ℝ)) *
          eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2 (volume.restrict B)) := by
      have := h
      simp only [hu'1] at this
      rw [e2] at this
      simpa only [euclideanFieldELpNormOn, eLpNormOn, volumeOn, ENNReal.ofReal_ofNat, hK0] using this
    calc (volume B) ^ (1 / q) * eLpMeanNormOn B (ENNReal.ofReal q)
          (fun x => u.toFun x - integralAverage B u.toFun)
        ≤ (volume B) ^ (1 / q) * (ENNReal.ofReal K0 * ((volume B)⁻¹ ^ (1 / (2 : ℝ)) *
          eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2 (volume.restrict B))) := by gcongr
      _ = _ := by ring
  have hR : ENNReal.ofReal (V ^ (1 / q) * K0 * V⁻¹ ^ (1 / (2 : ℝ))) *
      eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2 (volume.restrict B) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin
  have hML : MemLp (fun x => u.toFun x - integralAverage B u.toFun) (ENNReal.ofReal q)
      (volume.restrict B) := by
    exact (ne_top_of_le_ne_top hR hmain).lt_top
  refine ⟨hML, ?_⟩
  have := ENNReal.toReal_mono hR hmain
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  exact this

end PDE.PoincareAdjustMean
