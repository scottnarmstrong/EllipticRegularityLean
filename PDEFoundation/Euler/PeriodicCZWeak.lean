module

public import PDEFoundation.Euler.SmoothIdentities
public import PDEFoundation.PDE.WeakDivergenceForm
public import PDEFoundation.Sobolev.H1.Smooth
public import PDEFoundation.Geometry.ConvexDomain
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
# Smooth fields as weak solutions on the unit ball

For smooth `g, h` on `Vec 2` with `Δ g = -∂_k h`, the translate `x ↦ g (z + x)` is a weak solution of
`-Δ w = div F` on the unit ball with `F = h(z + ·) e_k`, in the repo's `H1Function` vocabulary.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

theorem pd_comp_add_left (f : Vec 2 → ℝ) (z : Vec 2) (j : Fin 2) :
    pd j (fun x => f (z + x)) = fun x => pd j f (z + x) := by
  funext x
  simp only [pd]
  rw [fderiv_comp_add_left]

theorem contDiff_translate {g : Vec 2 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (z : Vec 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => g (z + x)) :=
  ContDiff.comp hg (ContDiff.add contDiff_const contDiff_id)

theorem torusLap_comp_add_left (f : Vec 2 → ℝ) (z : Vec 2) (x : Vec 2) :
    torusLap (fun y => f (z + y)) x = torusLap f (z + x) := by
  simp only [torusLap, pd_comp_add_left]

/-- Integration by parts on `Vec 2` against a compactly supported smooth test function. -/
theorem integral_mul_pd_eq_neg {g φ : Vec 2 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) (j : Fin 2) :
    ∫ x, φ x * pd j g x = -∫ x, pd j φ x * g x := by
  have hgc : Continuous g := hg.continuous
  have hφc : Continuous φ := hφ.continuous
  have hpg : Continuous (pd j g) := (contDiff_pd_top hg j).continuous
  have hpφ : Continuous (pd j φ) := (contDiff_pd_top hφ j).continuous
  have h1 : Integrable (fun x => pd j φ x * g x) :=
    Continuous.integrable_of_hasCompactSupport (hpφ.mul hgc)
      (HasCompactSupport.mul_right (hc.fderiv_apply (𝕜 := ℝ) (basisVec j)) )
  have h2 : Integrable (fun x => φ x * pd j g x) :=
    Continuous.integrable_of_hasCompactSupport (hφc.mul hpg) (HasCompactSupport.mul_right hc)
  have h3 : Integrable (fun x => φ x * g x) :=
    Continuous.integrable_of_hasCompactSupport (hφc.mul hgc) (HasCompactSupport.mul_right hc)
  exact integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (v := basisVec j) h1 h2 h3
    (fun x _ => (hφ.differentiable (by simp)) x) (fun x _ => (hg.differentiable (by simp)) x)


/-- The unit ball, as the domain of the repo's CZ estimate. -/
theorem unitBall_isOpenBoundedConvex : IsOpenBoundedConvexDomain (euclideanBall (0 : Vec 2) 1) :=
  isOpenBoundedConvexDomain_euclideanBall 0 one_pos

/-- The `H¹(B₁)` representative of a smooth function. -/
noncomputable def smoothH1 {g : Vec 2 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    H1Function (euclideanBall (0 : Vec 2) 1) :=
  H1Function.ofContDiffOnIsOpenBoundedConvexDomain unitBall_isOpenBoundedConvex
    (hg.of_le (by exact_mod_cast le_top))

theorem smoothH1_toFun {g : Vec 2 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) : (smoothH1 hg).toFun = g :=
  rfl

theorem smoothH1_grad {g : Vec 2 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x : Vec 2) (j : Fin 2) :
    (smoothH1 hg).grad x j = pd j g x :=
  rfl

/-- The forcing `h e_k`. -/
def unitForce (k : Fin 2) (h : Vec 2 → ℝ) : Vec 2 → Vec 2 := fun x => Pi.single k (h x)

/-- Smooth `g, h` with `Δ g = -∂_k h` give a weak solution of `-Δ g = div (h e_k)` on the unit ball. -/
theorem smoothH1_isWeakSolution {g h : Vec 2 → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (k : Fin 2) (hlap : ∀ x, torusLap g x = -pd k h x) :
    IsWeakDivergenceFormSolutionOn (fun _ => (1 : Mat 2)) (euclideanBall (0 : Vec 2) 1)
      (smoothH1 hg) (0 : Vec 2 → ℝ) (unitForce k h) := by
  intro φ
  have hφd : ContDiff ℝ (⊤ : ℕ∞) φ.toFun := φ.contDiff
  have hφc := φ.hasCompactSupport
  have hout : ∀ x, x ∉ euclideanBall (0 : Vec 2) 1 → φ.toFun x = 0 ∧ ∀ j, pd j φ.toFun x = 0 := by
    intro x hx
    have hx' : x ∉ tsupport φ.toFun := fun h' => hx (φ.tsupport_subset h')
    refine ⟨image_eq_zero_of_notMem_tsupport hx', fun j => ?_⟩
    simp [pd, fderiv_of_notMem_tsupport (𝕜 := ℝ) hx']
  have hgrad : ∀ x j, φ.grad x j = pd j φ.toFun x := fun x j => by
    rw [WeakTestFunction.grad_apply]; rfl
  have hcontφ : ∀ j, Continuous (pd j φ.toFun) := fun j => (contDiff_pd_top hφd j).continuous
  have hcg : ∀ j, Continuous (pd j g) := fun j => (contDiff_pd_top hg j).continuous
  have hch : Continuous h := hh.continuous
  have hcc : ∀ j, HasCompactSupport (pd j φ.toFun) := fun j => hφc.fderiv_apply (𝕜 := ℝ) (basisVec j)
  have hflux : ∀ x, vecDot (matVecMul (1 : Mat 2) ((smoothH1 hg).grad x)) (φ.grad x) =
      ∑ j, pd j g x * pd j φ.toFun x := by
    intro x
    simp only [vecDot, matVecMul, Matrix.one_apply, ite_mul, one_mul, zero_mul, smoothH1_grad, hgrad]
    simp
  have hforce : ∀ x, vecDot (unitForce k h x) (φ.grad x) = h x * pd k φ.toFun x := by
    intro x
    simp only [vecDot, unitForce, Fin.sum_univ_two, hgrad]
    fin_cases k <;> simp
  have hint1 : ∀ j, Integrable (fun x => pd j g x * pd j φ.toFun x) :=
    fun j => Continuous.integrable_of_hasCompactSupport ((hcg j).mul (hcontφ j))
      (HasCompactSupport.mul_left (hcc j))
  have hint2 : Integrable (fun x => h x * pd k φ.toFun x) :=
    Continuous.integrable_of_hasCompactSupport (hch.mul (hcontφ k)) (HasCompactSupport.mul_left (hcc k))
  have hintφ : ∀ j, Integrable (fun x => φ.toFun x * pd j (pd j g) x) := fun j =>
    Continuous.integrable_of_hasCompactSupport (hφd.continuous.mul (contDiff_pd_top (contDiff_pd_top hg j) j).continuous)
      (HasCompactSupport.mul_right hφc)
  have hset1 : ∫ x in euclideanBall (0 : Vec 2) 1, ∑ j, pd j g x * pd j φ.toFun x =
      ∫ x, ∑ j, pd j g x * pd j φ.toFun x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp [(hout x hx).2]
  have hset2 : ∫ x in euclideanBall (0 : Vec 2) 1, h x * pd k φ.toFun x =
      ∫ x, h x * pd k φ.toFun x := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    simp [(hout x hx).2]
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · simp only [hflux]
      exact (integrable_finsetSum _ fun j _ => hint1 j).integrableOn
    · simp
    · simp only [hforce]
      exact hint2.integrableOn
  · simp only [hflux, hforce, Pi.zero_apply, zero_mul, integral_zero, zero_sub]
    rw [hset1, hset2, integral_finsetSum _ (fun j _ => hint1 j)]
    have hj : ∀ j, ∫ x, pd j g x * pd j φ.toFun x = -∫ x, φ.toFun x * pd j (pd j g) x := by
      intro j
      have := integral_mul_pd_eq_neg (contDiff_pd_top hg j) hφd hφc j
      rw [this]
      simp only [mul_comm (pd j g _)]
      simp only [neg_neg]
    have hk := integral_mul_pd_eq_neg hh hφd hφc k
    have hsum : ∑ j, ∫ x, φ.toFun x * pd j (pd j g) x = ∫ x, φ.toFun x * torusLap g x := by
      rw [← integral_finsetSum _ (fun j _ => hintφ j)]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp [torusLap, Fin.sum_univ_two, mul_add]
    simp only [hj, Finset.sum_neg_distrib, hsum]
    have : ∫ x, φ.toFun x * torusLap g x = -∫ x, φ.toFun x * pd k h x := by
      rw [← integral_neg]
      exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp [hlap x])
    rw [this, hk]
    simp only [neg_neg, mul_comm (h _)]

end PDE
