module

public import EllipticRegularity.Ch4.GreenFunction.Caccioppoli
public import EllipticRegularity.Ch4.GreenFunction.WeakLimit

/-!
# The Green function is `H¹` and `a`-harmonic away from the pole (Step 6 of Proposition 4.40)

On `U = B_R \ B̄_ε`, the gradients `∇Gₙ` are bounded in `L²(U)` (Caccioppoli), and their pairings
with test functions converge (weak derivative + approximation property).  Their weak limit `F`
is the weak gradient of `G`; hence `G ∈ H¹(U)`, `∫_U ∇Gₙ·Ψ → ∫_U F·Ψ` for all `Ψ ∈ L²(U;ℝᵈ)`
(4.156), and `G` is `a`-harmonic in `U`.
-/

@[expose] public section

open scoped Topology ENNReal

namespace PDE.Ch4Green

open MeasureTheory PDE Filter

variable {d : ℕ}

/-- The pairing of two vector `L²` fields as a sum of coordinate pairings. -/
theorem integral_vecDot_eq_sum {U : Set (Vec d)} {F Ψ : Vec d → Vec d}
    (hF : MemVectorL2On U F) (hΨ : MemVectorL2On U Ψ) :
    ∫ x in U, vecDot (F x) (Ψ x) = ∑ i, ∫ x in U, F x i * Ψ x i := by
  change (∫ x in U, ∑ i, F x i * Ψ x i) = _
  rw [integral_finsetSum]
  intro i _
  exact integrableOn_mul_of_memL2On (hF i) (hΨ i)

namespace ApproxSetting

variable {Λ R : ℝ} {a : CoeffField d}

/-- **Weak gradient of `G` away from the pole** and the gradient convergence
(4.156). -/
theorem exists_weakGradient (S : ApproxSetting d Λ R a) (hd : 3 ≤ d) {G : Vec d → ℝ}
    (hG : IsGreenFunction a R G) {ε : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    ∃ F : Vec d → Vec d,
      MemVectorL2On (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) ε) F ∧
      HasWeakGradientOn (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) ε) G F ∧
      ∀ Ψ : Vec d → Vec d,
        MemVectorL2On (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) ε) Ψ →
        Tendsto (fun n => ∫ x in euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) ε,
            vecDot ((S.G n).toH1Function.grad x) (Ψ x)) atTop
          (𝓝 (∫ x in euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) ε,
            vecDot (F x) (Ψ x))) := by
  set B := euclideanBall (0 : Vec d) R
  have hBo : IsOpen B := isOpen_euclideanBall _ _
  set U := B \ euclideanClosedBall (0 : Vec d) ε
  have hUo : IsOpen U := hBo.sdiff (isClosed_euclideanClosedBall _ _)
  have hUB : U ⊆ B := Set.sdiff_subset
  obtain ⟨C, -, hgradL2⟩ := S.integral_vecNormSq_grad_le hd
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_approxRadius_le S.hR (by positivity : 0 < ε / 4))
  set M2 := 4 * Λ * (2 / ε) ^ 2 * poleConst C Λ (ε / 2) S.E d ^ 2
  -- coordinatewise weak limits
  have hcoord : ∀ i : Fin d, ∃ Fi : Vec d → ℝ, MemL2On U Fi ∧ ∀ f : Vec d → ℝ, MemL2On U f →
      Tendsto (fun n => ∫ x in U, (S.G (n + N)).toH1Function.grad x i * f x) atTop
        (𝓝 (∫ x in U, Fi x * f x)) := by
    intro i
    have hh : ∀ n, MemL2On U (fun x => (S.G (n + N)).toH1Function.grad x i) := fun n =>
      ((S.G (n + N)).toH1Function.gradMemL2 i).mono_measure (Measure.restrict_mono hUB le_rfl)
    refine exists_weakLimit_of_test hUo hh (M := Real.sqrt M2) (fun n => ?_) (fun ψ hψ hc hsub =>
        ?_)
    · rw [Real.le_sqrt ENNReal.toReal_nonneg (le_trans (by positivity) (le_trans
        (integral_nonneg fun x => vecNormSq_nonneg _)
        (hgradL2 hε hεR.le (n + N) (hN (n + N) (by omega))))),
        toReal_eLpNorm_two_sq_eq_integral_sq (hh n)]
      refine le_trans ?_ (hgradL2 hε hεR.le (n + N) (hN (n + N) (by omega)))
      exact integral_mono_of_nonneg (Eventually.of_forall fun x => sq_nonneg _)
        (integrableOn_vecNormSq_of_memVectorL2On fun j =>
          ((S.G (n + N)).toH1Function.gradMemL2 j).mono_measure (Measure.restrict_mono hUB le_rfl))
        (Eventually.of_forall fun x => sq_apply_le_vecNormSq _ i)
    · -- pairing with a test function supported in `U`
      set g : Vec d → ℝ := fun x => fderiv ℝ ψ x (basisVec i)
      let φ : WeakTestFunction B := ⟨ψ, hψ, hc, hsub.trans hUB⟩
      have hgB : MemL2On B g := φ.memLp_partialDeriv i 2
      have hg0 : ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) ε)), g x = 0 := by
        refine (ae_restrict_iff' (measurableSet_euclideanBall _ _)).2
          (Eventually.of_forall fun x hx => ?_)
        have hxt : x ∉ tsupport ψ := fun h => (hsub h).2
          (euclideanBall_subset_euclideanClosedBall _ _ hx)
        simp [g, fderiv_of_notMem_tsupport ℝ hxt]
      have hlim := S.tendsto_integral_of_isGreen hd hG hε hεR hgB hg0
      refine ⟨-∫ x in B, G x * g x, ?_⟩
      have heq : ∀ n, ∫ x in U, (S.G (n + N)).toH1Function.grad x i * ψ x =
          -∫ x in B, (S.G (n + N)).toH1Function.toFun x * g x := by
        intro n
        rw [(S.G (n + N)).toH1Function.hasWeakGradient i ψ hψ hc (hsub.trans hUB), neg_neg]
        refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hBo.measurableSet hUB
          fun x hx => ?_).symm
        have hxt : x ∉ tsupport ψ := fun h => hx.2 (hsub h)
        simp [image_eq_zero_of_notMem_tsupport hxt]
      simp_rw [heq]
      exact ((tendsto_add_atTop_iff_nat N).2 hlim).neg
  choose Fc hFcL hFclim using hcoord
  set F : Vec d → Vec d := fun x i => Fc i x
  have hFL : MemVectorL2On U F := fun i => hFcL i
  refine ⟨F, hFL, fun i => ?_, fun Ψ hΨ => ?_⟩
  · -- weak derivative
    intro ψ hψ hc hsub
    set g : Vec d → ℝ := fun x => fderiv ℝ ψ x (basisVec i)
    let φ : WeakTestFunction B := ⟨ψ, hψ, hc, hsub.trans hUB⟩
    have hgB : MemL2On B g := φ.memLp_partialDeriv i 2
    have hg0 : ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) ε)), g x = 0 := by
      refine (ae_restrict_iff' (measurableSet_euclideanBall _ _)).2
        (Eventually.of_forall fun x hx => ?_)
      have hxt : x ∉ tsupport ψ := fun h => (hsub h).2
        (euclideanBall_subset_euclideanClosedBall _ _ hx)
      simp [g, fderiv_of_notMem_tsupport ℝ hxt]
    have hlim := S.tendsto_integral_of_isGreen hd hG hε hεR hgB hg0
    have hψU : MemL2On U ψ := memL2On_of_contDiff hψ hc
    have hlim2 := hFclim i ψ hψU
    have heq : ∀ n, ∫ x in U, (S.G (n + N)).toH1Function.grad x i * ψ x =
        -∫ x in B, (S.G (n + N)).toH1Function.toFun x * g x := by
      intro n
      rw [(S.G (n + N)).toH1Function.hasWeakGradient i ψ hψ hc (hsub.trans hUB), neg_neg]
      refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hBo.measurableSet hUB
        fun x hx => ?_).symm
      have hxt : x ∉ tsupport ψ := fun h => hx.2 (hsub h)
      simp [image_eq_zero_of_notMem_tsupport hxt]
    simp_rw [heq] at hlim2
    have hval := tendsto_nhds_unique hlim2 ((tendsto_add_atTop_iff_nat N).2 hlim).neg
    have hGU : ∫ x in U, G x * g x = ∫ x in B, G x * g x := by
      refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hBo.measurableSet hUB
        fun x hx => ?_).symm
      have hxt : x ∉ tsupport ψ := fun h => hx.2 (hsub h)
      simp [g, fderiv_of_notMem_tsupport ℝ hxt]
    change ∫ x in U, G x * g x = -∫ x in U, Fc i x * ψ x
    rw [hGU, hval, neg_neg]
  · -- gradient convergence
    have hsum : ∀ n, ∫ x in U, vecDot ((S.G (n + N)).toH1Function.grad x) (Ψ x) =
        ∑ i, ∫ x in U, (S.G (n + N)).toH1Function.grad x i * Ψ x i := fun n =>
      integral_vecDot_eq_sum (fun j => ((S.G (n + N)).toH1Function.gradMemL2 j).mono_measure
        (Measure.restrict_mono hUB le_rfl)) hΨ
    rw [integral_vecDot_eq_sum hFL hΨ]
    refine (tendsto_add_atTop_iff_nat N).1 ?_
    simp_rw [hsum]
    exact tendsto_finsetSum _ fun i _ => hFclim i _ (hΨ i)

/-- **Part (iii), first half**: `G ∈ H¹(B_R \ B̄_ε)` is `a`-harmonic there, with gradient
convergence (4.156). -/
theorem exists_harmonic (S : ApproxSetting d Λ R a) (hd : 3 ≤ d) {G : Vec d → ℝ}
    (hG : IsGreenFunction a R G) {ε : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    ∃ H : H1Function (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) ε),
      H.toFun = G ∧
      IsWeakDivergenceFormSolutionOn a
        (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) ε) H 0 0 ∧
      ∀ Ψ : Vec d → Vec d,
        MemVectorL2On (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) ε) Ψ →
        Tendsto (fun n => ∫ x in euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) ε,
            vecDot ((S.G n).toH1Function.grad x) (Ψ x)) atTop
          (𝓝 (∫ x in euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) ε,
            vecDot (H.grad x) (Ψ x))) := by
  set B := euclideanBall (0 : Vec d) R
  have hBo : IsOpen B := isOpen_euclideanBall _ _
  set U := B \ euclideanClosedBall (0 : Vec d) ε
  have hUo : IsOpen U := hBo.sdiff (isClosed_euclideanClosedBall _ _)
  have hUB : U ⊆ B := Set.sdiff_subset
  obtain ⟨F, hFL, hFw, hconv⟩ := S.exists_weakGradient hd hG hε hεR
  have hsubU : U ⊆ B \ euclideanBall (0 : Vec d) ε :=
    fun x hx => ⟨hx.1, fun h => hx.2 (euclideanBall_subset_euclideanClosedBall _ _ h)⟩
  have hGL : MemL2On U G :=
    (hG.2.1 ε hε hεR).mono_measure (Measure.restrict_mono hsubU le_rfl)
  let H : H1Function U := ⟨G, F, hGL, hFL, hFw⟩
  refine ⟨H, rfl, ?_, hconv⟩
  rw [DGNM.solutionOn_iff]
  intro φ
  have hmeasU : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U) :=
    fun i j => (S.hmeas i j).mono_measure (Measure.restrict_mono hUB le_rfl)
  have hellU : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x) := fun x hx => S.hell x (hUB hx)
  have haF : MemVectorL2On U (fun x => matVecMul (a x) (F x)) :=
    DGNM.memVectorL2On_matVecMul_of_aemeasurable hUo.measurableSet hmeasU hellU hFL
  refine ⟨integrableOn_vecDot_of_memVectorL2On haF φ.grad_memVectorL2On, ?_⟩
  set Ψ : Vec d → Vec d := fun x => matVecMul (adjointCoeffField a x) (φ.grad x)
  have hΨ : MemVectorL2On U Ψ :=
    DGNM.memVectorL2On_matVecMul_of_aemeasurable hUo.measurableSet (aemeasurable_adjoint hmeasU)
      (elliptic_adjoint hellU) φ.grad_memVectorL2On
  have hswap : ∀ ξ : Vec d → Vec d, ∀ x,
      vecDot (matVecMul (a x) (ξ x)) (φ.grad x) = vecDot (ξ x) (Ψ x) := by
    intro ξ x
    rw [vecDot_comm, ← vecDot_matVecMul_matTranspose, vecDot_comm]
  change ∫ x in U, vecDot (matVecMul (a x) (F x)) (φ.grad x) = 0
  simp_rw [hswap F]
  have hlim := hconv Ψ hΨ
  refine tendsto_nhds_unique hlim (tendsto_const_nhds.congr' ?_)
  filter_upwards [eventually_approxRadius_le S.hR hε] with n hn
  have hsrc : ∀ᵐ x ∂(volumeOn U), approxSource d (approxRadius R n) x = 0 := by
    refine (ae_restrict_iff' hUo.measurableSet).2 (Eventually.of_forall fun x hx => ?_)
    refine approxSource_eq_zero_of_notMem fun hxb => hx.2 ?_
    rw [mem_euclideanClosedBall_iff_vecEuclideanNorm_le hε.le]
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (approxRadius_pos S.hR n)] at hxb
    linarith
  have hsol := solutionOn_of_source_ae_zero hBo hUo hUB (S.solG n) hsrc
  rw [DGNM.solutionOn_iff] at hsol
  have := (hsol φ).2
  simp only [H1Function.restrict_grad] at this
  simp_rw [hswap] at this
  exact this.symm

end ApproxSetting

end PDE.Ch4Green
