module

public import PDEFoundation.Euler.GradLimitBasic
public import PDEFoundation.Euler.TorusParts
public import PDEFoundation.Euler.SmoothIdentities

/-!
# Smooth periodic product identity on the torus

For a smooth periodic divergence-free field `z` and a smooth periodic field `θ`,
`∑ᵢⱼ ∫ zᵢ zⱼ ∂ⱼθᵢ = - ∑ᵢⱼ ∫ θᵢ zⱼ ∂ⱼzᵢ` (periodic integration by parts and `div z = 0`).
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

theorem integrableOn_cube_of_continuous {f : Vec 2 → ℝ} (hf : Continuous f) :
    Integrable f (volume.restrict torusCube) := hf.integrableOn_Icc

theorem quad_ibp_component {z θ : Vec 2 → Vec 2} (hz : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => z x i))
    (hzp : IsTorusPeriodic z) (hθ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => θ x i))
    (hθp : IsTorusPeriodic θ) (i j : Fin 2) :
    ∫ x in torusCube, (z x i * z x j) * gradMat θ x i j =
      -(∫ x in torusCube, θ x i * (z x j * gradMat z x i j)) -
        ∫ x in torusCube, θ x i * (z x i * pd j (fun y => z y j) x) := by
  have hzi := hz i
  have hzj := hz j
  have hzd : ∀ k, Differentiable ℝ (fun x => z x k) := fun k =>
    (hz k).differentiable (by simp)
  have hprod : ContDiff ℝ 1 (fun x => z x i * z x j) :=
    ContDiff.mul (hzi.of_le (by simp)) (hzj.of_le (by simp))
  have hib := torus_integral_by_parts (f := fun x => z x i * z x j) (g := fun x => θ x i) hprod
    ((hθ i).of_le (by simp)) ((hzp.comp (fun r => r i)).mul (hzp.comp (fun r => r j)))
    (hθp.comp (fun r => r i)) j
  have hder : ∀ x, fderiv ℝ (fun x => z x i * z x j) x (basisVec j) =
      pd j (fun y => z y i) x * z x j + z x i * pd j (fun y => z y j) x := by
    intro x
    rw [fderiv_fun_mul ((hzd i) x) ((hzd j) x)]
    simp only [add_apply, smul_apply, smul_eq_mul, pd_def]
    ring
  simp only [hder] at hib
  have c1 : Continuous fun x => pd j (fun y => z y i) x := continuous_pd_of_contDiff hzi j
  have c2 : Continuous fun x => pd j (fun y => z y j) x := continuous_pd_of_contDiff hzj j
  have cz : ∀ k, Continuous fun x => z x k := fun k => (hz k).continuous
  have ct : Continuous fun x => θ x i := (hθ i).continuous
  have i1 : IntegrableOn (fun x => θ x i * (z x j * gradMat z x i j)) torusCube :=
    (ct.mul ((cz j).mul c1)).integrableOn_Icc
  have i2 : IntegrableOn (fun x => θ x i * (z x i * pd j (fun y => z y j) x)) torusCube :=
    (ct.mul ((cz i).mul c2)).integrableOn_Icc
  have e1 : ∫ x in torusCube, (pd j (fun y => z y i) x * z x j + z x i * pd j (fun y => z y j) x) *
      θ x i = (∫ x in torusCube, θ x i * (z x j * gradMat z x i j)) +
        ∫ x in torusCube, θ x i * (z x i * pd j (fun y => z y j) x) := by
    rw [← integral_add i1 i2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [gradMat]
    ring
  have hib' : ∫ x in torusCube, (pd j (fun y => z y i) x * z x j + z x i * pd j (fun y => z y j) x) *
      θ x i = -∫ x in torusCube, (z x i * z x j) * gradMat θ x i j := hib
  linarith

theorem quad_ibp_div_zero {z θ : Vec 2 → Vec 2} (hz : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => z x i))
    (hzd : ∀ x, torusDiv z x = 0) (hθ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => θ x i)) (i : Fin 2) :
    (∫ x in torusCube, θ x i * (z x i * pd 0 (fun y => z y 0) x)) +
      ∫ x in torusCube, θ x i * (z x i * pd 1 (fun y => z y 1) x) = 0 := by
  have ct : Continuous fun x => θ x i := (hθ i).continuous
  have cz : Continuous fun x => z x i := (hz i).continuous
  have c0 : Continuous fun x => pd 0 (fun y => z y 0) x := continuous_pd_of_contDiff (hz 0) 0
  have c1 : Continuous fun x => pd 1 (fun y => z y 1) x := continuous_pd_of_contDiff (hz 1) 1
  have j0 : IntegrableOn (fun x => θ x i * (z x i * pd 0 (fun y => z y 0) x)) torusCube :=
    (ct.mul (cz.mul c0)).integrableOn_Icc
  have j1 : IntegrableOn (fun x => θ x i * (z x i * pd 1 (fun y => z y 1) x)) torusCube :=
    (ct.mul (cz.mul c1)).integrableOn_Icc
  rw [← integral_add j0 j1]
  have : ∀ x, θ x i * (z x i * pd 0 (fun y => z y 0) x) + θ x i * (z x i * pd 1 (fun y => z y 1) x) = 0 := by
    intro x
    have := hzd x
    simp only [torusDiv] at this
    rw [← mul_add, ← mul_add, this]
    simp
  simp [this]

/-- **Smooth quadratic identity.** -/
theorem torus_quad_identity {z θ : Vec 2 → Vec 2} (hz : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => z x i))
    (hzp : IsTorusPeriodic z) (hzd : ∀ x, torusDiv z x = 0)
    (hθ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => θ x i)) (hθp : IsTorusPeriodic θ) :
    (∑ i, ∑ j, ∫ x in torusCube, (z x i * z x j) * gradMat θ x i j) =
      -(∑ i, ∑ j, ∫ x in torusCube, θ x i * (z x j * gradMat z x i j)) := by
  simp only [Fin.sum_univ_two]
  have h00 := quad_ibp_component hz hzp hθ hθp 0 0
  have h01 := quad_ibp_component hz hzp hθ hθp 0 1
  have h10 := quad_ibp_component hz hzp hθ hθp 1 0
  have h11 := quad_ibp_component hz hzp hθ hθp 1 1
  have d0 := quad_ibp_div_zero hz hzd hθ 0
  have d1 := quad_ibp_div_zero hz hzd hθ 1
  linarith

theorem pd_half_sq_sum {z : Vec 2 → Vec 2} (hz : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => z x i)) (j : Fin 2) (x : Vec 2) :
    pd j (fun y => (1 / 2) * (z y 0 * z y 0 + z y 1 * z y 1)) x =
      z x 0 * gradMat z x 0 j + z x 1 * gradMat z x 1 j := by
  have hd : ∀ k, Differentiable ℝ (fun x => z x k) := fun k => (hz k).differentiable (by simp)
  have h0 : HasFDerivAt (fun y => z y 0 * z y 0)
      (z x 0 • fderiv ℝ (fun y => z y 0) x + z x 0 • fderiv ℝ (fun y => z y 0) x) x :=
    ((hd 0) x).hasFDerivAt.mul ((hd 0) x).hasFDerivAt
  have h1 : HasFDerivAt (fun y => z y 1 * z y 1)
      (z x 1 • fderiv ℝ (fun y => z y 1) x + z x 1 • fderiv ℝ (fun y => z y 1) x) x :=
    ((hd 1) x).hasFDerivAt.mul ((hd 1) x).hasFDerivAt
  have h : HasFDerivAt (fun y => (1 / 2 : ℝ) * (z y 0 * z y 0 + z y 1 * z y 1))
      ((1 / 2 : ℝ) • ((z x 0 • fderiv ℝ (fun y => z y 0) x + z x 0 • fderiv ℝ (fun y => z y 0) x) +
        (z x 1 • fderiv ℝ (fun y => z y 1) x + z x 1 • fderiv ℝ (fun y => z y 1) x))) x :=
    (h0.add h1).const_mul (1 / 2 : ℝ)
  rw [pd_def, h.fderiv]
  simp only [gradMat, pd_def, add_apply, smul_apply, smul_eq_mul]
  ring

theorem smooth_energy_identity {z w : Vec 2 → Vec 2} (hz : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => z x i))
    (hzp : IsTorusPeriodic z) (hw : ∀ i, AEStronglyMeasurable (fun x => w x i) (volume.restrict torusCube))
    {C : ℝ} (hC : ∀ᵐ x ∂(volume.restrict torusCube), ∀ i, |w x i| ≤ C)
    (hdiv : ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → IsTorusPeriodic ψ →
      ∫ x in torusCube, vecDot (w x) (fun j => pd j ψ x) = 0) :
    (∑ i, ∑ j, ∫ x in torusCube, w x j * (z x i * gradMat z x i j)) = 0 := by
  set ψ : Vec 2 → ℝ := fun y => (1 / 2) * (z y 0 * z y 0 + z y 1 * z y 1) with hψ
  have hψs : ContDiff ℝ (⊤ : ℕ∞) ψ :=
    contDiff_const.mul (((hz 0).mul (hz 0)).add ((hz 1).mul (hz 1)))
  have hψp : IsTorusPeriodic ψ := by
    intro k x
    simp only [hψ]
    rw [hzp k x]
  have h := hdiv ψ hψs hψp
  have hint : ∀ j i, Integrable (fun x => w x j * (z x i * gradMat z x i j)) (volume.restrict torusCube) := by
    intro j i
    have hc : Continuous fun x => z x i * gradMat z x i j :=
      (hz i).continuous.mul (continuous_gradMat_apply hz i j)
    obtain ⟨K, hK⟩ := (isCompact_Icc : IsCompact torusCube).exists_bound_of_continuousOn hc.continuousOn
    have hwi : Integrable (fun x => w x j) (volume.restrict torusCube) :=
      Integrable.of_bound (hw j) C (hC.mono fun x hx => by simpa [Real.norm_eq_abs] using hx j)
    refine (hwi.mul_bdd hc.aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall hK)))
  have hpd : ∀ j x, pd j ψ x = z x 0 * gradMat z x 0 j + z x 1 * gradMat z x 1 j :=
    fun j x => pd_half_sq_sum hz j x
  simp only [vecDot, Fin.sum_univ_two, hpd] at h
  simp only [Fin.sum_univ_two]
  have e : ∀ x, w x 0 * (z x 0 * gradMat z x 0 0 + z x 1 * gradMat z x 1 0) +
      w x 1 * (z x 0 * gradMat z x 0 1 + z x 1 * gradMat z x 1 1) =
      (w x 0 * (z x 0 * gradMat z x 0 0) + w x 1 * (z x 0 * gradMat z x 0 1)) +
      (w x 0 * (z x 1 * gradMat z x 1 0) + w x 1 * (z x 1 * gradMat z x 1 1)) := fun x => by ring
  simp only [e] at h
  have k1 : Integrable (fun x => w x 0 * (z x 0 * gradMat z x 0 0) + w x 1 * (z x 0 * gradMat z x 0 1))
      (volume.restrict torusCube) := (hint 0 0).add (hint 1 0)
  have k2 : Integrable (fun x => w x 0 * (z x 1 * gradMat z x 1 0) + w x 1 * (z x 1 * gradMat z x 1 1))
      (volume.restrict torusCube) := (hint 0 1).add (hint 1 1)
  rw [integral_add k1 k2, integral_add (hint 0 0) (hint 1 0), integral_add (hint 0 1) (hint 1 1)] at h
  linarith

end PDE
