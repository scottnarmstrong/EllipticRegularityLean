module

public import EllipticRegularity.Ch4.GreenFunction.Harmonic
public import PDEFoundation.Sobolev.Ch4.LipschitzH1

/-!
# The flux identity (Step 7 of Proposition 4.40, part (iv))

For `φ` Lipschitz with compact support in `B_R` and constant in `B_ε`,
`∫_{B_R \ B_ε} ∇φ · a ∇G = φ(0)`: test the equation of `Gₙ` with `φ`, and pass to the limit with
the gradient convergence (4.156) on `B_R \ B̄_{ε/2}`.
-/

@[expose] public section

open scoped Topology ENNReal

namespace PDE.Ch4Green

open MeasureTheory PDE Filter

variable {d : ℕ}

/-- A function constant on an open set has vanishing classical gradient there. -/
theorem classicalGradient_eq_zero_of_const {φ : Vec d → ℝ} {V : Set (Vec d)} (hV : IsOpen V)
    {c : ℝ} (hc : ∀ x ∈ V, φ x = c) {x : Vec d} (hx : x ∈ V) : classicalGradient φ x = 0 := by
  have hev : φ =ᶠ[𝓝 x] fun _ => c := by
    filter_upwards [hV.mem_nhds hx] with y hy using hc y hy
  funext i
  simp [classicalGradient, hev.fderiv_eq]

/-- Weak gradients of a.e.-equal functions agree a.e. on an open set. -/
theorem grad_ae_eq_of_ae_eq {U : Set (Vec d)} (hU : IsOpen U) {H H' : H1Function U}
    (hHH' : H.toFun =ᵐ[volumeOn U] H'.toFun) : H.grad =ᵐ[volumeOn U] H'.grad := by
  have hcoord : ∀ i : Fin d, (fun x => H.grad x i) =ᵐ[volumeOn U] fun x => H'.grad x i := by
    intro i
    have hw : HasWeakPartialDerivOn U i H.toFun (fun x => H'.grad x i) := by
      intro φ hφ hc hsub
      rw [← H'.hasWeakGradient i φ hφ hc hsub]
      refine integral_congr_ae ?_
      filter_upwards [hHH'] with x hx
      rw [hx]
    exact HasWeakPartialDerivOn.ae_eq hU
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        ((H.gradMemL2 i).locallyIntegrable one_le_two))
      (locallyIntegrableOn_of_locallyIntegrable_restrict
        ((H'.gradMemL2 i).locallyIntegrable one_le_two))
      (H.hasWeakGradient i) hw
  have hall := ae_all_iff.2 hcoord
  filter_upwards [hall] with x hx
  funext i
  exact hx i

namespace ApproxSetting

variable {Λ R : ℝ} {a : CoeffField d}

/-- **Flux identity** (4.152). -/
theorem isGreen_flux (S : ApproxSetting d Λ R a) (hd : 3 ≤ d) {G : Vec d → ℝ}
    (hG : IsGreenFunction a R G) {ε : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (H : H1Function (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (ε / 2)))
    (hHG : H.toFun =ᵐ[volumeOn (euclideanBall (0 : Vec d) R \
      euclideanClosedBall (0 : Vec d) (ε / 2))] G)
    (φ : Vec d → ℝ) (hφL : ∃ K : NNReal, LipschitzWith K φ) (hφc : HasCompactSupport φ)
    (hφB : tsupport φ ⊆ euclideanBall (0 : Vec d) R)
    (hφconst : ∃ c : ℝ, ∀ x ∈ euclideanBall (0 : Vec d) ε, φ x = c) :
    ∫ x in euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) ε,
        vecDot (fun i => fderiv ℝ φ x (basisVec i)) (matVecMul (a x) (H.grad x)) = φ 0 := by
  -- the harmonic representative on `B_R \ B̄_{ε/2}` and its gradient convergence
  obtain ⟨H', hH'G, -, hconv⟩ := S.exists_harmonic hd hG (half_pos hε) (by linarith)
  have hBo : IsOpen (euclideanBall (0 : Vec d) R) := isOpen_euclideanBall _ _
  have hUo : IsOpen (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (ε / 2)) :=
    hBo.sdiff (isClosed_euclideanClosedBall _ _)
  have hUB : (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (ε / 2)) ⊆
      (euclideanBall (0 : Vec d) R) := Set.sdiff_subset
  have hTm : MeasurableSet (euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) ε) :=
      hBo.measurableSet.diff (measurableSet_euclideanBall _ _)
  have hTU : (euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) ε) ⊆ (euclideanBall (0 : Vec
      d) R \ euclideanClosedBall (0 : Vec d) (ε / 2)) := by
    intro x hx
    refine ⟨hx.1, fun h => hx.2 ?_⟩
    rw [mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)] at h
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hε]
    linarith
  obtain ⟨K, hK⟩ := hφL
  obtain ⟨c, hc⟩ := hφconst
  have hη : Ch4Infra.EucLip (K : ℝ) φ := Ch4Infra.EucLip.of_norm K.2 fun x y => by
    have := hK.dist_le_mul x y
    rwa [Real.dist_eq, dist_eq_norm] at this
  have hφ0 : φ 0 = c := hc 0 (center_mem_euclideanBall _ hε)
  have hgrad0 : ∀ x ∈ euclideanBall (0 : Vec d) ε, classicalGradient φ x = 0 :=
    fun x hx => classicalGradient_eq_zero_of_const (isOpen_euclideanBall _ _) hc hx
  set ψ := Ch4Infra.lipH10 hBo hη K.2 hφc hφB
  -- `Ψ = 1_T aᵗ ∇φ`
  have hmeasU : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) R \
      euclideanClosedBall (0 : Vec d) (ε / 2))) :=
    fun i j => (S.hmeas i j).mono_measure (Measure.restrict_mono hUB le_rfl)
  have hellU : ∀ x ∈ (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (ε / 2)),
      IsEllipticMatrix 1 Λ (a x) := fun x hx => S.hell x (hUB hx)
  have hgradU : MemVectorL2On
      (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (ε / 2))
      (classicalGradient φ) := fun i =>
    (ψ.toH1Function.gradMemL2 i).mono_measure (Measure.restrict_mono hUB le_rfl)
  set Ψ₀ : Vec d → Vec d := fun x => matVecMul (adjointCoeffField a x) (classicalGradient φ x)
  have hΨ₀ : MemVectorL2On (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (ε / 2))
      Ψ₀ :=
    DGNM.memVectorL2On_matVecMul_of_aemeasurable hUo.measurableSet (aemeasurable_adjoint hmeasU)
      (elliptic_adjoint hellU) hgradU
  set Ψ : Vec d → Vec d := (euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) ε).indicator Ψ₀
  have hΨ : MemVectorL2On (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (ε / 2)) Ψ
      := fun i => by
    have : (fun x => Ψ x i) = (euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) ε).indicator
        (fun x => Ψ₀ x i) := by
      funext x
      by_cases hx : x ∈ (euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) ε) <;> simp [Ψ, hx]
    rw [this]
    exact (hΨ₀ i).indicator hTm
  have hswap : ∀ ξ : Vec d → Vec d, ∀ x,
      vecDot (ξ x) (Ψ₀ x) = vecDot (classicalGradient φ x) (matVecMul (a x) (ξ x)) := by
    intro ξ x
    rw [vecDot_comm, vecDot_matVecMul_matTranspose]
  have hred : ∀ ξ : Vec d → Vec d,
      ∫ x in (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (ε / 2)), vecDot (ξ x)
          (Ψ x) =
        ∫ x in (euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) ε), vecDot
            (classicalGradient φ x) (matVecMul (a x) (ξ x)) := by
    intro ξ
    have : (fun x => vecDot (ξ x) (Ψ x)) =
        (euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) ε).indicator (fun x => vecDot
            (classicalGradient φ x) (matVecMul (a x) (ξ x))) := by
      funext x
      by_cases hx : x ∈ (euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) ε)
      · change vecDot (ξ x) ((euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) ε).indicator
          Ψ₀ x) = _
        rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, hswap]
      · change vecDot (ξ x) ((euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) ε).indicator
          Ψ₀ x) = _
        rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, vecDot_zero_right]
    rw [this, integral_indicator hTm, Measure.restrict_restrict hTm, Set.inter_eq_left.2 hTU]
  have hlim := hconv Ψ hΨ
  simp_rw [hred] at hlim
  -- the value along the sequence
  have hval : ∀ᶠ n in atTop, ∫ x in (euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) ε),
      vecDot (classicalGradient φ x)
      (matVecMul (a x) ((S.G n).toH1Function.grad x)) = φ 0 := by
    filter_upwards [eventually_approxRadius_le S.hR (half_pos hε)] with n hn
    have hρ := approxRadius_pos S.hR n
    obtain ⟨-, heq⟩ := S.solG n ψ
    simp only [Pi.zero_apply, vecDot_zero_left, integral_zero, sub_zero] at heq
    rw [integral_approxSource_mul (approxRadius_lt S.hR n).le hρ.le] at heq
    have havg : integralAverage (euclideanBall (0 : Vec d) (approxRadius R n))
        ψ.toH1Function.toFun = φ 0 := by
      have hsub : euclideanBall (0 : Vec d) (approxRadius R n) ⊆ euclideanBall (0 : Vec d) ε :=
        euclideanBall_mono hρ.le (by linarith)
      change integralAverage (euclideanBall (0 : Vec d) (approxRadius R n)) φ = φ 0
      rw [integralAverage, setIntegral_congr_fun (measurableSet_euclideanBall _ _)
        (fun x hx => hc x (hsub hx)), setIntegral_const, smul_eq_mul, Measure.real, ← mul_assoc,
        inv_mul_cancel₀ (volume_euclideanBall_toReal_pos _ hρ).ne', one_mul, hφ0]
    rw [havg] at heq
    rw [← heq]
    refine (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hBo.measurableSet Set.sdiff_subset
      fun x hx => ?_).symm.trans ?_
    · have hxε : x ∈ euclideanBall (0 : Vec d) ε := by
        by_contra h
        exact hx.2 ⟨hx.1, h⟩
      simp [hgrad0 x hxε]
    · refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only
      rw [vecDot_comm]
      rfl
  have hlimH' : ∫ x in (euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) ε), vecDot
      (classicalGradient φ x) (matVecMul (a x) (H'.grad x)) =
      φ 0 := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' (hval.mono fun n hn => hn.symm))
  -- replace `H'` by `H`
  have hae : H.grad =ᵐ[volumeOn
      (euclideanBall (0 : Vec d) R \ euclideanClosedBall (0 : Vec d) (ε / 2))] H'.grad := by
    refine grad_ae_eq_of_ae_eq hUo ?_
    rw [hH'G]
    exact hHG
  rw [← hlimH']
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hTU hae] with x hx
  rw [hx]
  rfl

end ApproxSetting

end PDE.Ch4Green
