module

public import PDEFoundation.Monotonicity.Core.RellichDiv
public import PDEFoundation.Monotonicity.Core.RellichSphere

/-!
# The Rellich identity and Cauchy-Schwarz on spheres

For a harmonic `u` on `B_R`, `d ≥ 1` and `0 < r < R`:

`(d - 2) ∫_{B_r} |∇u|² = r ∫_{∂B_r} |∇u|² - 2 r⁻¹ ∫_{∂B_r} (x·∇u)²`.

Also exported (from `RellichDiv`, `RellichSphere`): the pointwise divergence of the Rellich field,
Cauchy-Schwarz for `PDE.sphereIntegral` and its equality case.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

noncomputable section

variable {d : ℕ}

theorem vecDot_rellichField (u : Vec d → ℝ) (x : Vec d) :
    vecDot (rellichField u x) x =
      vecNormSq (classicalGradient u x) * vecNormSq x - 2 * vecDot x (classicalGradient u x) ^ 2 := by
  have h : vecDot (classicalGradient u x) x = vecDot x (classicalGradient u x) := vecDot_comm _ _
  have e1 : ∀ A : ℝ, ∑ k, A * x k * x k = A * vecDot x x := fun A => by
    rw [vecDot, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have e2 : ∀ E : ℝ, ∑ k, E * classicalGradient u x k * x k =
      E * vecDot (classicalGradient u x) x := fun E => by
    rw [vecDot, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hx : vecDot (rellichField u x) x =
      ∑ k, vecNormSq (classicalGradient u x) * x k * x k -
        ∑ k, (2 * vecDot x (classicalGradient u x)) * classicalGradient u x k * x k := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [rellichField, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hx, e1, e2, h]
  unfold vecNormSq
  ring

theorem continuousOn_vecNormSq_gradient {R : ℝ} {u : Vec d → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (euclideanBall (0 : Vec d) R)) :
    ContinuousOn (fun x => vecNormSq (classicalGradient u x)) (euclideanBall (0 : Vec d) R) := by
  have hU : IsOpen (euclideanBall (0 : Vec d) R) := isOpen_euclideanBall 0 R
  have hg : ∀ j, ContinuousOn (euclideanCoordDeriv j u) (euclideanBall (0 : Vec d) R) :=
    fun j => (contDiffOn_top_euclideanCoordDeriv hU hu j).continuousOn
  change ContinuousOn (fun x => ∑ j, euclideanCoordDeriv j u x * euclideanCoordDeriv j u x) _
  exact continuousOn_finsetSum _ fun j _ => (hg j).mul (hg j)

theorem continuousOn_euler_sq {R : ℝ} {u : Vec d → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (euclideanBall (0 : Vec d) R)) :
    ContinuousOn (fun x => vecDot x (classicalGradient u x) ^ 2) (euclideanBall (0 : Vec d) R) :=
  ((contDiffOn_euler (isOpen_euclideanBall 0 R) hu).continuousOn).pow 2

/-- **Rellich identity.** -/
theorem rellich_identity (hd : 0 < d) {R r : ℝ} {u : Vec d → ℝ}
    (hu : ContDiffOn ℝ 2 u (euclideanBall (0 : Vec d) R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0)
    (hr : 0 < r) (hrR : r < R) :
    ((d : ℝ) - 2) * ∫ x in euclideanBall (0 : Vec d) r, vecNormSq (classicalGradient u x) =
      r * sphereIntegral (0 : Vec d) r (fun x => vecNormSq (classicalGradient u x)) -
        2 * r⁻¹ * sphereIntegral (0 : Vec d) r (fun x => vecDot x (classicalGradient u x) ^ 2) := by
  have htop := contDiffOn_top_of_harmonicOn hd hu hharm
  have hsub : euclideanBall (0 : Vec d) r ⊆ euclideanBall (0 : Vec d) R := by
    intro x hx
    rw [mem_euclideanBall_zero_iff] at hx ⊢
    nlinarith only [hx, hr, hrR]
  have hsph : euclideanSphere (0 : Vec d) r ⊆ euclideanBall (0 : Vec d) R := by
    intro x hx
    rw [mem_euclideanSphere_zero_iff] at hx
    rw [mem_euclideanBall_zero_iff, hx]
    nlinarith only [hr, hrR]
  have hdiv := integral_euclideanBall_classicalDivergence_of_one_le (Nat.one_le_iff_ne_zero.2 hd.ne')
    (contDiffOn_one_rellichField_of_harmonicOn hd hu hharm) hr hrR
  have hL : ∫ x in euclideanBall (0 : Vec d) r, classicalDivergence (rellichField u) x =
      ((d : ℝ) - 2) * ∫ x in euclideanBall (0 : Vec d) r, vecNormSq (classicalGradient u x) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun (isOpen_euclideanBall 0 r).measurableSet fun x hx => ?_
    exact classicalDivergence_rellichField_of_harmonicOn hd hu hharm (hsub hx)
  have ha := (continuousOn_vecNormSq_gradient htop).mono hsph
  have hb := (continuousOn_euler_sq htop).mono hsph
  have hS : sphereIntegral (0 : Vec d) r (fun x => vecDot (rellichField u x) x) =
      r ^ 2 * sphereIntegral (0 : Vec d) r (fun x => vecNormSq (classicalGradient u x)) -
        2 * sphereIntegral (0 : Vec d) r (fun x => vecDot x (classicalGradient u x) ^ 2) := by
    rw [← sphereIntegral_zero_sub_const_mul ha hb]
    refine sphereIntegral_zero_congr fun x hx => ?_
    rw [vecDot_rellichField, (mem_euclideanSphere_zero_iff.1 hx)]
    ring
  rw [← hL, hdiv, hS]
  field_simp

end

end PDE
