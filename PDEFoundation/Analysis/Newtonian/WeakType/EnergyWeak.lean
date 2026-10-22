module

public import PDEFoundation.Analysis.Newtonian.WeakType.EnergyFubini

/-!
# The weak form `∫ ∇u_h · ∇ψ = ∫ h · ∇ψ` of `Δu_h = div h`

Conditional on the representation statement (D2): for smooth compactly supported `w`, `F` with
`Δw = div F`, `w = u_F`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE.NewtonWeakType

noncomputable section

variable {d : ℕ}

theorem vecDot_smul_basisVec (c : ℝ) (i : Fin d) (x : Vec d) :
    vecDot x (c • basisVec i) = c * x i := by
  simp only [vecDot, Pi.smul_apply, smul_eq_mul, basisVec_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  ring

theorem coordDeriv_mul {f g : Vec d → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (k : Fin d) (x : Vec d) :
    euclideanCoordDeriv k (fun y => f y * g y) x =
      euclideanCoordDeriv k f x * g x + f x * euclideanCoordDeriv k g x := by
  unfold euclideanCoordDeriv
  have hfd : DifferentiableAt ℝ f x := (hf.differentiable (by simp)) x
  have hgd : DifferentiableAt ℝ g x := (hg.differentiable (by simp)) x
  rw [fderiv_fun_mul hfd hgd]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem coordDeriv_finsetSum {g : Fin d → Vec d → ℝ} (hg : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (g j))
    (k : Fin d) (x : Vec d) :
    euclideanCoordDeriv k (fun y => ∑ j, g j y) x = ∑ j, euclideanCoordDeriv k (g j) x := by
  unfold euclideanCoordDeriv
  rw [fderiv_fun_sum (fun j _ => ((hg j).differentiable (by simp)) x)]
  simp

theorem contDiff_coordLaplacian {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (euclideanCoordLaplacian ψ) := by
  have : euclideanCoordLaplacian ψ = fun x => ∑ i : Fin d, euclideanCoordSecondDeriv i i ψ x :=
    rfl
  rw [this]
  exact ContDiff.sum fun i _ => contDiff_euclideanCoordSecondDeriv hψ i i

theorem hasCompactSupport_coordLaplacian {ψ : Vec d → ℝ} (hψ : HasCompactSupport ψ) :
    HasCompactSupport (euclideanCoordLaplacian ψ) := by
  have : euclideanCoordLaplacian ψ = fun x => ∑ i : Fin d, euclideanCoordSecondDeriv i i ψ x :=
    rfl
  rw [this]
  have key : ∀ s : Finset (Fin d), HasCompactSupport
      (fun x => ∑ i ∈ s, euclideanCoordSecondDeriv i i ψ x) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      simp only [Finset.sum_empty]
      exact HasCompactSupport.zero
    | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (hasCompactSupport_euclideanCoordSecondDeriv hψ a a).add ih
  exact key Finset.univ

theorem newtonPotential_eq_sum_integral (hd : 0 < d) {F : Vec d → Vec d}
    (hF : Continuous F) (hFc : HasCompactSupport F) (x : Vec d) :
    newtonPotential F x = ∑ i : Fin d, ∫ y, newtonKernel (x - y) i * F y i := by
  unfold newtonPotential vecDot
  refine integral_finsetSum _ fun i _ => ?_
  have h := (hasCompactSupport_apply hFc i).convolutionExists_right
      (ContinuousLinearMap.mul ℝ ℝ) (locallyIntegrable_newtonKernel_apply hd i)
      ((continuous_apply i).comp hF) x
  exact ConvolutionExistsAt.integrable_swap h

/-- Integration by parts for the gradient pairing against a compactly supported test function. -/
theorem integral_vecDot_gradient_eq {u ψ : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, vecDot (classicalGradient u x) (classicalGradient ψ x) =
      -∫ x, u x * euclideanCoordLaplacian ψ x := by
  have hpsi1 : ∀ k : Fin d, ContDiff ℝ (⊤ : ℕ∞) (euclideanCoordDeriv k ψ) :=
    fun k => contDiff_euclideanCoordDeriv hψ k
  have hpsi1c : ∀ k : Fin d, HasCompactSupport (euclideanCoordDeriv k ψ) :=
    fun k => hasCompactSupport_euclideanCoordDeriv hψc k
  have hu1 : ∀ k : Fin d, ContDiff ℝ (⊤ : ℕ∞) (euclideanCoordDeriv k u) :=
    fun k => contDiff_euclideanCoordDeriv hu k
  have hpsi2 : ∀ k : Fin d, ContDiff ℝ (⊤ : ℕ∞) (euclideanCoordDeriv k (euclideanCoordDeriv k ψ)) :=
    fun k => contDiff_euclideanCoordDeriv (hpsi1 k) k
  have hpsi2c : ∀ k : Fin d, HasCompactSupport (euclideanCoordDeriv k (euclideanCoordDeriv k ψ)) :=
    fun k => hasCompactSupport_euclideanCoordDeriv (hpsi1c k) k
  have hI1 : ∀ k : Fin d, Integrable (fun x => euclideanCoordDeriv k u x * euclideanCoordDeriv k ψ x)
      volume := fun k =>
    ((hu1 k).continuous.mul (hpsi1 k).continuous).integrable_of_hasCompactSupport
      ((hpsi1c k).mul_left)
  have hI2 : ∀ k : Fin d,
      Integrable (fun x => u x * euclideanCoordDeriv k (euclideanCoordDeriv k ψ) x) volume :=
    fun k => (hu.continuous.mul (hpsi2 k).continuous).integrable_of_hasCompactSupport
      ((hpsi2c k).mul_left)
  have hk : ∀ k : Fin d, ∫ x, euclideanCoordDeriv k u x * euclideanCoordDeriv k ψ x =
      -∫ x, u x * euclideanCoordDeriv k (euclideanCoordDeriv k ψ) x := by
    intro k
    have h0 := integral_euclideanCoordDeriv_eq_zero (g := fun y => u y * euclideanCoordDeriv k ψ y)
      (hu.mul (hpsi1 k)) ((hpsi1c k).mul_left) k
    have h1 : (fun y => euclideanCoordDeriv k (fun y => u y * euclideanCoordDeriv k ψ y) y) =
        fun y => euclideanCoordDeriv k u y * euclideanCoordDeriv k ψ y +
          u y * euclideanCoordDeriv k (euclideanCoordDeriv k ψ) y :=
      funext fun y => coordDeriv_mul hu (hpsi1 k) k y
    rw [h1, integral_add (hI1 k) (hI2 k)] at h0
    linarith
  have hlap : (fun x => u x * euclideanCoordLaplacian ψ x) = fun x => ∑ k : Fin d,
      u x * euclideanCoordDeriv k (euclideanCoordDeriv k ψ) x := by
    funext x
    rw [← Finset.mul_sum]
    rfl
  rw [hlap, integral_finsetSum _ (fun k _ => hI2 k), ← Finset.sum_neg_distrib]
  have : (fun x => vecDot (classicalGradient u x) (classicalGradient ψ x)) = fun x =>
      ∑ k : Fin d, euclideanCoordDeriv k u x * euclideanCoordDeriv k ψ x := rfl
  rw [this, integral_finsetSum _ (fun k _ => hI1 k)]
  exact Finset.sum_congr rfl fun k _ => hk k

theorem exists_radius_of_hasCompactSupport {β : Type*} [Zero β] {f : Vec d → β}
    (hf : HasCompactSupport f) : ∃ R : ℝ, 0 < R ∧ ∀ y, f y ≠ 0 → vecEuclideanNorm y < R := by
  obtain ⟨r, hr⟩ := hf.isCompact.isBounded.subset_closedBall (0 : Vec d)
  refine ⟨Real.sqrt d * |r| + 1, by positivity, fun y hy => ?_⟩
  have hmem : y ∈ Metric.closedBall (0 : Vec d) r :=
    hr (subset_tsupport f (Function.mem_support.mpr hy))
  have h1 : ‖y‖ ≤ r := by simpa using hmem
  calc vecEuclideanNorm y ≤ Real.sqrt d * ‖y‖ := vecEuclideanNorm_le_sqrt_natCast_mul_norm y
    _ ≤ Real.sqrt d * |r| := by
        gcongr
        exact h1.trans (le_abs_self r)
    _ < _ := by linarith

/-- The key identity: `∫ E_i(x - y) Δψ(x) dx = -∂_i ψ(y)`, from the representation statement. -/
theorem integral_newtonKernel_laplacian
    (hD2 : ∀ (w : Vec d → ℝ) (F : Vec d → Vec d), ContDiff ℝ (⊤ : ℕ∞) w → HasCompactSupport w →
      ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      (∀ x, euclideanCoordLaplacian w x = classicalDivergence F x) → w = newtonPotential F)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (i : Fin d) (y : Vec d) :
    ∫ x, newtonKernel (x - y) i * euclideanCoordLaplacian ψ x = -euclideanCoordDeriv i ψ y := by
  set b := euclideanCoordLaplacian ψ with hbdef
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := contDiff_coordLaplacian hψ
  have hbc : HasCompactSupport b := hasCompactSupport_coordLaplacian hψc
  set F : Vec d → Vec d := fun x => b x • basisVec i with hF
  have hFs : ContDiff ℝ (⊤ : ℕ∞) F := by
    refine contDiff_pi.mpr fun k => ?_
    simp only [hF, Pi.smul_apply, smul_eq_mul]
    exact hb.mul contDiff_const
  have hFc : HasCompactSupport F :=
    hbc.comp_left (g := fun r : ℝ => r • basisVec i) (by simp)
  have hdiv : ∀ x, euclideanCoordLaplacian (euclideanCoordDeriv i ψ) x =
      classicalDivergence F x := by
    intro x
    have h1 : classicalDivergence F x = euclideanCoordDeriv i b x := by
      unfold classicalDivergence
      rw [Finset.sum_eq_single i]
      · have : (fun y => F y i) = b := by
          funext z
          simp [hF, basisVec_apply]
        rw [this]
      · intro k _ hki
        have : (fun y => F y k) = fun _ => (0 : ℝ) := by
          funext z
          simp [hF, basisVec_apply, hki]
        rw [this]
        unfold euclideanCoordDeriv
        simp
      · simp
    rw [h1]
    have hbsum : b = fun z => ∑ k : Fin d, euclideanCoordDeriv k (euclideanCoordDeriv k ψ) z := rfl
    rw [hbsum, coordDeriv_finsetSum (fun k => contDiff_euclideanCoordDeriv
      (contDiff_euclideanCoordDeriv hψ k) k)]
    have : euclideanCoordLaplacian (euclideanCoordDeriv i ψ) x =
        ∑ k : Fin d, euclideanCoordThirdDeriv i k k ψ x := rfl
    rw [this]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact euclideanCoordThirdDeriv_diag_right_comm hψ i k x
  have hrep := congrFun (hD2 (euclideanCoordDeriv i ψ) F (contDiff_euclideanCoordDeriv hψ i)
    (hasCompactSupport_euclideanCoordDeriv hψc i) hFs hFc hdiv) y
  have hpot : newtonPotential F y = ∫ x, newtonKernel (y - x) i * b x := by
    unfold newtonPotential
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hF]
    rw [vecDot_smul_basisVec]
    ring
  rw [hpot] at hrep
  have hneg : ∀ x, newtonKernel (x - y) i * b x = -(newtonKernel (y - x) i * b x) := by
    intro x
    rw [← neg_sub y x, newtonKernel_neg]
    simp
  simp_rw [hneg]
  rw [integral_neg, ← hrep]

/-- `∫ u_h Δψ = - ∫ h · ∇ψ`. -/
theorem integral_newtonPotential_mul_laplacian (hd : 0 < d)
    (hD2 : ∀ (w : Vec d → ℝ) (F : Vec d → Vec d), ContDiff ℝ (⊤ : ℕ∞) w → HasCompactSupport w →
      ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      (∀ x, euclideanCoordLaplacian w x = classicalDivergence F x) → w = newtonPotential F)
    {h : Vec d → Vec d} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, newtonPotential h x * euclideanCoordLaplacian ψ x =
      -∫ y, vecDot (h y) (classicalGradient ψ y) := by
  set b := euclideanCoordLaplacian ψ with hbdef
  have hb : ContDiff ℝ (⊤ : ℕ∞) b := contDiff_coordLaplacian hψ
  have hbc : HasCompactSupport b := hasCompactSupport_coordLaplacian hψc
  obtain ⟨R1, hR1, hs1⟩ := exists_radius_of_hasCompactSupport hhc
  obtain ⟨R2, hR2, hs2⟩ := exists_radius_of_hasCompactSupport hbc
  set R := max R1 R2 with hR
  have hRpos : 0 < R := lt_max_of_lt_left hR1
  have hha : ∀ i : Fin d, ∀ y, h y i ≠ 0 → vecEuclideanNorm y < R := by
    intro i y hy
    refine lt_max_of_lt_left (hs1 y fun h0 => hy ?_)
    simp [h0]
  have hhb : ∀ x, b x ≠ 0 → vecEuclideanNorm x < R := fun x hx =>
    lt_max_of_lt_right (hs2 x hx)
  have hhi : ∀ i : Fin d, Continuous (fun y => h y i) := fun i =>
    (continuous_apply i).comp hh.continuous
  have hhic : ∀ i : Fin d, HasCompactSupport (fun y => h y i) := fun i =>
    hasCompactSupport_apply hhc i
  have hu : (fun x => newtonPotential h x * b x) = fun x => ∑ i : Fin d,
      (∫ y, newtonKernel (x - y) i * h y i) * b x := by
    funext x
    rw [newtonPotential_eq_sum_integral hd hh.continuous hhc x, Finset.sum_mul]
  rw [hu, integral_finsetSum _ (fun i _ => integrable_integral_newtonKernel_mul hd i (hhi i)
    (hhic i) hb.continuous hbc hRpos (hha i) hhb)]
  have hi : ∀ i : Fin d, ∫ x, (∫ y, newtonKernel (x - y) i * h y i) * b x =
      -∫ y, h y i * euclideanCoordDeriv i ψ y := by
    intro i
    rw [integral_newtonKernel_swap hd i (hhi i) (hhic i) hb.continuous hbc hRpos (hha i) hhb,
      ← integral_neg]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only
    rw [integral_newtonKernel_laplacian hD2 hψ hψc i y]
    ring
  simp_rw [hi]
  rw [Finset.sum_neg_distrib]
  congr 1
  have hint : ∀ i : Fin d, Integrable (fun y => h y i * euclideanCoordDeriv i ψ y) volume :=
    fun i => ((hhi i).mul (contDiff_euclideanCoordDeriv hψ i).continuous).integrable_of_hasCompactSupport
      ((hasCompactSupport_euclideanCoordDeriv hψc i).mul_left)
  rw [← integral_finsetSum _ (fun i _ => hint i)]
  rfl

/-- The weak form of `Δu_h = div h`: `∫ ∇u_h · ∇ψ = ∫ h · ∇ψ` for smooth compactly supported `ψ`. -/
theorem integral_vecDot_gradient_newtonPotential (hd : 0 < d)
    (hD2 : ∀ (w : Vec d → ℝ) (F : Vec d → Vec d), ContDiff ℝ (⊤ : ℕ∞) w → HasCompactSupport w →
      ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      (∀ x, euclideanCoordLaplacian w x = classicalDivergence F x) → w = newtonPotential F)
    {h : Vec d → Vec d} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h)
    {ψ : Vec d → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ) :
    ∫ x, vecDot (classicalGradient (newtonPotential h) x) (classicalGradient ψ x) =
      ∫ y, vecDot (h y) (classicalGradient ψ y) := by
  rw [integral_vecDot_gradient_eq (contDiff_newtonPotential hd hh hhc) hψ hψc,
    integral_newtonPotential_mul_laplacian hd hD2 hh hhc hψ hψc, neg_neg]

end

end PDE.NewtonWeakType
