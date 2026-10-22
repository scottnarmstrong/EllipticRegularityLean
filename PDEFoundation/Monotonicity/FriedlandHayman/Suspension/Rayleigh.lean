module

public import PDEFoundation.Monotonicity.FriedlandHayman.Suspension.Slice
public import PDEFoundation.Monotonicity.FriedlandHayman.Suspension.Support
public import PDEFoundation.Monotonicity.FriedlandHayman.Suspension.Cutoff

/-!
# Friedland--Hayman: Rayleigh quotient of the cut-off lifts

For a `C¹` function `f` on `Vec n`, `a ≥ 0` and `ε > 0` the function
`F_ε(x) = χ_ε(|x'|) |x'|^a f(x'/|x'|)` on `Vec (n + N)` is `C¹`, and its numerator and denominator
integrals are `σ_N` times explicit one-dimensional integrals in the angle `θ`.
-/

@[expose] public section

open MeasureTheory

namespace PDE.FHLane

noncomputable section

namespace Susp

/-- The cut-off lift `F_ε(x) = χ_ε(|x'|) |x'|^a f(x'/|x'|)`. -/
def cutLift {n N : ℕ} (ε a : ℝ) (f : Vec n → ℝ) (x : Vec (n + N)) : ℝ :=
  radialLift (radProf ε a) f (projFst x)

theorem contDiffAt_radProf {ε a t : ℝ} (ht : 0 < t) : ContDiffAt ℝ 1 (radProf ε a) t := by
  unfold radProf cutoff
  have h1 : ContDiff ℝ 1 fun r : ℝ => Real.smoothTransition ((r - ε) / ε) :=
    (Real.smoothTransition.contDiff (n := 1)).comp ((contDiff_id.sub contDiff_const).div_const ε)
  exact h1.contDiffAt.mul (Real.contDiffAt_rpow_const_of_ne ht.ne')

theorem contDiff_radialLift_radProf {n : ℕ} {ε a : ℝ} (hε : 0 < ε) {f : Vec n → ℝ}
    (hf : ContDiff ℝ 1 f) : ContDiff ℝ 1 (radialLift (radProf ε a) f) :=
  contDiff_radialLift hε (fun _ ht => radProf_eq_zero hε ht) (fun _ ht => contDiffAt_radProf ht) hf

theorem contDiff_cutLift {n N : ℕ} {ε a : ℝ} (hε : 0 < ε) {f : Vec n → ℝ} (hf : ContDiff ℝ 1 f) :
    ContDiff ℝ 1 (cutLift (N := N) ε a f) :=
  contDiff_comp_projFst (contDiff_radialLift_radProf hε hf)

theorem continuous_radialGradQ {n : ℕ} {g : ℝ → ℝ} {f : Vec n → ℝ}
    (hΦ : ContDiff ℝ 1 (radialLift g f)) : Continuous (radialGradQ g f) := by
  have hg := PDE.ContDiff.continuous_classicalGradient hΦ
  unfold radialGradQ vecNormSq vecDot
  refine Continuous.sub ?_ (Continuous.pow ?_ 2)
  · exact continuous_finsetSum _ fun i _ => ((continuous_apply i).comp hg).mul
      ((continuous_apply i).comp hg)
  · exact continuous_finsetSum _ fun i _ => ((continuous_apply i).comp hg).mul (continuous_apply i)

theorem tgn_cutLift {n N : ℕ} {ε a : ℝ} (hε : 0 < ε) {f : Vec n → ℝ} (hf : ContDiff ℝ 1 f) :
    tangentialGradientNormSq (cutLift (N := N) ε a f) = fun x => radialGradQ (radProf ε a) f (projFst x) :=
  funext fun x => tgn_comp_projFst (contDiff_radialLift_radProf hε hf) x

/-- The numerator integrand in the angle. -/
def numInt (n N : ℕ) (a I J ε θ : ℝ) : ℝ :=
  Real.sin θ ^ (N - 1) * (Real.cos θ ^ (n - 1) *
    ((1 - Real.cos θ ^ 2) * (radProfD ε a (Real.cos θ) ^ 2 * I) +
      (radProf ε a (Real.cos θ) / Real.cos θ) ^ 2 * J))

/-- The denominator integrand in the angle. -/
def denInt (n N : ℕ) (a I ε θ : ℝ) : ℝ :=
  Real.sin θ ^ (N - 1) * (Real.cos θ ^ (n - 1) * (radProf ε a (Real.cos θ) ^ 2 * I))

theorem numerator_cutLift {n N : ℕ} [NeZero n] [NeZero N] {ε a : ℝ} (hε : 0 < ε)
    {f : Vec n → ℝ} (hf : ContDiff ℝ 1 f) :
    sphereIntegral (0 : Vec (n + N)) 1 (tangentialGradientNormSq (cutLift (N := N) ε a f)) =
      sphereArea N * ∫ θ in (0 : ℝ)..(Real.pi / 2),
        numInt n N a (sphereIntegral (0 : Vec n) 1 (fun x => f x ^ 2))
          (sphereIntegral (0 : Vec n) 1 (tangentialGradientNormSq f)) ε θ := by
  rw [tgn_cutLift hε hf, sphereIntegral_comp_projFst_cont
    (continuous_radialGradQ (contDiff_radialLift_radProf hε hf))]
  congr 1
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  rw [sphereIntegral_radialGradQ hf hc (hasDerivAt_radProf hc)]
  unfold numInt
  ring

theorem denominator_cutLift {n N : ℕ} [NeZero n] [NeZero N] {ε a : ℝ} (hε : 0 < ε)
    {f : Vec n → ℝ} (hf : ContDiff ℝ 1 f) :
    sphereIntegral (0 : Vec (n + N)) 1 (fun x => cutLift (N := N) ε a f x ^ 2) =
      sphereArea N * ∫ θ in (0 : ℝ)..(Real.pi / 2),
        denInt n N a (sphereIntegral (0 : Vec n) 1 (fun x => f x ^ 2)) ε θ := by
  have hΦ := contDiff_radialLift_radProf (a := a) hε hf
  have := sphereIntegral_comp_projFst_cont (N := N)
    (G := fun y => radialLift (radProf ε a) f y ^ 2) (hΦ.continuous.pow 2)
  unfold cutLift
  rw [this]
  congr 1
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo,
    intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  rw [sphereIntegral_radialLift_sq hc]
  unfold denInt
  ring

end Susp

end

end PDE.FHLane
