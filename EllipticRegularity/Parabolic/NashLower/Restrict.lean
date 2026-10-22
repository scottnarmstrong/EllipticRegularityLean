module

public import EllipticRegularity.Parabolic.Rescale.SpatialRestrict
public import EllipticRegularity.Parabolic.Moser.SliceOrderTimeSets
public import EllipticRegularity.Parabolic.CauchyDef

/-!
# Restriction and scaling of parabolic energy functions (Nash-Aronson lower bound)

Space-time restriction of a `ParH1Function` and of its weak-solution property to a
sub-cylinder `V × J ⊆ U × I`, restriction of the coefficient hypothesis, and scalar multiples of
energy functions and Cauchy solutions.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE.Parabolic.NashLower

/-- Restrict a parabolic energy function to a sub-cylinder (same representatives). -/
def restrictParH1 {d : ℕ} {U V : Set (Vec d)} {I J : Set ℝ} (hVU : V ⊆ U) (hJI : J ⊆ I)
    (u : ParH1Function U I) : ParH1Function V J :=
  Rescale.restrictParH1Space hVU (Moser.restrictParH1TimeSet u hJI)

@[simp] theorem restrictParH1_toFun {d : ℕ} {U V : Set (Vec d)} {I J : Set ℝ} (hVU : V ⊆ U)
    (hJI : J ⊆ I) (u : ParH1Function U I) : (restrictParH1 hVU hJI u).toFun = u.toFun := rfl

@[simp] theorem restrictParH1_grad {d : ℕ} {U V : Set (Vec d)} {I J : Set ℝ} (hVU : V ⊆ U)
    (hJI : J ⊆ I) (u : ParH1Function U I) : (restrictParH1 hVU hJI u).grad = u.grad := rfl

/-- Integrals over `S ⊆ T` of a function vanishing outside a measurable `K ⊆ S` agree. -/
theorem setIntegral_eq_of_zero_off' {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {S T K : Set α} (hST : S ⊆ T) (hK : MeasurableSet K) (hKS : K ⊆ S) {F : α → ℝ}
    (hF : ∀ x, x ∉ K → F x = 0) : ∫ x in S, F x ∂μ = ∫ x in T, F x ∂μ := by
  have key : ∀ W : Set α, K ⊆ W → ∫ x in W, F x ∂μ = ∫ x in K, F x ∂μ := by
    intro W hKW
    have hind : F = K.indicator F := by
      funext x
      by_cases hx : x ∈ K
      · simp [hx]
      · simp [hx, hF x hx]
    calc ∫ x in W, F x ∂μ = ∫ x in W, K.indicator F x ∂μ := by rw [← hind]
      _ = ∫ x in W ∩ K, F x ∂μ := setIntegral_indicator hK
      _ = ∫ x in K, F x ∂μ := by rw [inter_eq_right.2 hKW]
  rw [key S hKS, key T (hKS.trans hST)]

/-- The weak-formulation integrand vanishes off the topological support of the test function. -/
theorem parWeakIntegrand_eq_zero_of_notMem_tsupport {d : ℕ} {a : ParCoeffField d}
    {U : Set (Vec d)} {I : Set ℝ} (u : ParH1Function U I) {φ : Vec d × ℝ → ℝ} {z : Vec d × ℝ}
    (hz : z ∉ tsupport φ) : parWeakIntegrand a u φ z = 0 := by
  have h0 : fderiv ℝ φ z = 0 := fderiv_of_notMem_tsupport (𝕜 := ℝ) hz
  simp [parWeakIntegrand, parTimeDeriv, parSpaceGrad, h0, vecDot]

/-- A weak solution restricts to every sub-cylinder `V × J ⊆ U × I`. -/
theorem isParabolicWeakSolution_restrict {d : ℕ} {a : ParCoeffField d} {U V : Set (Vec d)}
    {I J : Set ℝ} (hVU : V ⊆ U) (hJI : J ⊆ I) {u : ParH1Function U I}
    (hu : IsParabolicWeakSolution a U I u) :
    IsParabolicWeakSolution a V J (restrictParH1 hVU hJI u) := by
  intro φ
  let φ' : ParTestFunction U (interior I) :=
    ⟨φ.toFun, φ.contDiff, φ.hasCompactSupport,
      φ.tsupport_subset.trans (prod_mono hVU (interior_mono hJI))⟩
  obtain ⟨hint, hzero⟩ := hu φ'
  have hsub : V ×ˢ J ⊆ U ×ˢ I := prod_mono hVU hJI
  refine ⟨hint.mono_set hsub, ?_⟩
  have hKm : MeasurableSet (tsupport φ.toFun) := (isClosed_tsupport _).measurableSet
  have hKS : tsupport φ.toFun ⊆ V ×ˢ J :=
    φ.tsupport_subset.trans (prod_mono subset_rfl interior_subset)
  have heq := setIntegral_eq_of_zero_off' (μ := (volume : Measure (Vec d × ℝ))) hsub hKm hKS
    (F := parWeakIntegrand a u φ.toFun)
    (fun z hz => parWeakIntegrand_eq_zero_of_notMem_tsupport u hz)
  exact heq.trans hzero

/-- The coefficient hypotheses restrict to sub-cylinders. -/
theorem isParabolicCoeff_mono {d : ℕ} {lam Lam : ℝ} {a : ParCoeffField d} {U V : Set (Vec d)}
    {I J : Set ℝ} (h : IsParabolicCoeff lam Lam a U I) (hVU : V ⊆ U) (hJI : J ⊆ I) :
    IsParabolicCoeff lam Lam a V J :=
  ⟨fun i j => (h.measurable i j).mono_measure
      (Measure.restrict_mono (prod_mono hVU hJI) le_rfl),
    ae_mono (Measure.restrict_mono (prod_mono hVU hJI) le_rfl) h.elliptic⟩

/-! ### Scalar multiples -/

theorem hasWeakGradientOn_const_mul {d : ℕ} {U : Set (Vec d)} {f : Vec d → ℝ}
    {Df : Vec d → Vec d} (c : ℝ) (h : HasWeakGradientOn U f Df) :
    HasWeakGradientOn U (fun x => c * f x) (fun x => c • Df x) := by
  intro i φ hφ hc hsub
  have h1 := h i φ hφ hc hsub
  have e1 : ∫ x in U, c * f x * (fderiv ℝ φ x) (basisVec i) =
      c * ∫ x in U, f x * (fderiv ℝ φ x) (basisVec i) := by
    rw [← integral_const_mul]; exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only [mul_assoc])
  have e2 : ∫ x in U, (c • Df x) i * φ x = c * ∫ x in U, Df x i * φ x := by
    rw [← integral_const_mul]; exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc])
  rw [e1, e2, h1]
  ring

/-- Scalar multiple of a parabolic energy function. -/
def smulParH1 {d : ℕ} {U : Set (Vec d)} {I : Set ℝ} (c : ℝ) (u : ParH1Function U I) :
    ParH1Function U I where
  toFun z := c * u.toFun z
  grad z := c • u.grad z
  memL2 := u.memL2.const_mul c
  gradMemL2 i := by
    have := (u.gradMemL2 i).const_mul c
    simpa only [Pi.smul_apply, smul_eq_mul] using this
  sliceWeakGradient := by
    filter_upwards [u.sliceWeakGradient] with t ht
    exact hasWeakGradientOn_const_mul c ht
  sliceL2loc t ht K hK hKU := (u.sliceL2loc t ht K hK hKU).const_mul c
  weakCont ψ hψ := by
    have h := (u.weakCont ψ hψ).const_smul c
    refine h.congr fun t _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)

@[simp] theorem smulParH1_toFun {d : ℕ} {U : Set (Vec d)} {I : Set ℝ} (c : ℝ)
    (u : ParH1Function U I) (z : Vec d × ℝ) : (smulParH1 c u).toFun z = c * u.toFun z := rfl

/-- Scalar multiples of weak solutions are weak solutions. -/
theorem isParabolicWeakSolution_smul {d : ℕ} {a : ParCoeffField d} {U : Set (Vec d)}
    {I : Set ℝ} (c : ℝ) {u : ParH1Function U I} (hu : IsParabolicWeakSolution a U I u) :
    IsParabolicWeakSolution a U I (smulParH1 c u) := by
  intro φ
  obtain ⟨hint, hzero⟩ := hu φ
  have hfun : parWeakIntegrand a (smulParH1 c u) φ.toFun =
      fun z => c * parWeakIntegrand a u φ.toFun z := by
    funext z
    have hm : matVecMul (a z) (c • u.grad z) = c • matVecMul (a z) (u.grad z) := by
      funext i
      simp only [matVecMul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hv : vecDot (c • matVecMul (a z) (u.grad z)) (parSpaceGrad φ.toFun z) =
        c * vecDot (matVecMul (a z) (u.grad z)) (parSpaceGrad φ.toFun z) := by
      simp only [vecDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp only [parWeakIntegrand, smulParH1]
    rw [hm, hv]
    ring
  rw [hfun]
  exact ⟨hint.const_mul c, by rw [integral_const_mul, hzero, mul_zero]⟩

/-- Scalar multiples of Cauchy solutions solve the Cauchy problem with the scaled datum. -/
theorem isCauchySolution_smul {d : ℕ} {a : ParCoeffField d} {s T : ℝ} {f : Vec d → ℝ}
    {u : ParH1Function (univ : Set (Vec d)) (Icc s T)} (c : ℝ) (hu : IsCauchySolution a s T f u) :
    IsCauchySolution a s T (fun x => c * f x) (smulParH1 c u) := by
  refine ⟨isParabolicWeakSolution_smul c hu.1, ?_⟩
  filter_upwards [hu.2] with x hx
  simp [hx]

end PDE.Parabolic.NashLower
