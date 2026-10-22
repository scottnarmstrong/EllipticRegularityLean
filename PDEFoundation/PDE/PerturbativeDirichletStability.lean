module

public import PDEFoundation.PDE.PerturbativeTesting
public import PDEFoundation.Sobolev.H1.VectorL2Bounds

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

noncomputable section

variable {d : ℕ} {U : Set (Vec d)}

private theorem matVecMul_sub_apply (A B : Mat d) (x : Vec d) :
    matVecMul (A - B) x = matVecMul A x - matVecMul B x := by
  change (A - B).mulVec x = A.mulVec x - B.mulVec x
  exact Matrix.sub_mulVec A B x

private theorem vecDot_sub_left (x y q : Vec d) :
    vecDot (x - y) q = vecDot x q - vecDot y q := by
  simp only [vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private theorem vecDot_add_left (x y q : Vec d) :
    vecDot (x + y) q = vecDot x q + vecDot y q := by
  simp only [vecDot, Pi.add_apply, add_mul, Finset.sum_add_distrib]

/-- The residual forcing obtained by subtracting two coefficient equations. -/
def perturbativeDirichletResidual (a b : CoeffField d)
    (F G : Vec d → Vec d) (v : H1Function U) : Vec d → Vec d :=
  fun x => F x - G x + matVecMul (a x - b x) (v.grad x)

theorem vectorDifferenceMemL2 (F G : Vec d → Vec d)
    (hF : MemVectorL2On U F) (hG : MemVectorL2On U G) :
    MemVectorL2On U (fun x => F x - G x) := fun i => (hF i).sub (hG i)

theorem coefficientDifferenceGradientMemL2
    (a b : CoeffField d) (deltaA deltaB : ℝ)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hb : ∀ i j, AEMeasurable (fun x => b x i j) (volumeOn U))
    (hcloseA : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE deltaA (a x) (1 : Mat d))
    (hcloseB : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE deltaB (b x) (1 : Mat d))
    (v : H1Function U) :
    MemVectorL2On U (fun x => matVecMul (a x - b x) (v.grad x)) := by
  have haI := memVectorL2On_matVecMul_sub_identity_of_isMatrixPerturbationLE
    ha hcloseA v.gradMemL2
  have hbI := memVectorL2On_matVecMul_sub_identity_of_isMatrixPerturbationLE
    hb hcloseB v.gradMemL2
  intro i
  have hrewrite : (fun x => matVecMul (a x - b x) (v.grad x) i) =
      fun x => matVecMul (a x - 1) (v.grad x) i -
        matVecMul (b x - 1) (v.grad x) i := by
    funext x
    rw [show a x - b x = (a x - 1) - (b x - 1) by abel,
      matVecMul_sub_apply]
    rfl
  rw [hrewrite]
  exact (haI i).sub (hbI i)

theorem coefficientDifferenceGradientMemL2OfNonneg
    (a b : CoeffField d) (deltaA deltaB : ℝ)
    (_hdeltaA : 0 ≤ deltaA) (_hdeltaB : 0 ≤ deltaB)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hb : ∀ i j, AEMeasurable (fun x => b x i j) (volumeOn U))
    (hcloseA : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE deltaA (a x) (1 : Mat d))
    (hcloseB : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE deltaB (b x) (1 : Mat d))
    (v : H1Function U) :
    MemVectorL2On U (fun x => matVecMul (a x - b x) (v.grad x)) :=
  coefficientDifferenceGradientMemL2 a b deltaA deltaB ha hb hcloseA hcloseB v

private theorem perturbativeDirichletResidual_memL2
    (a b : CoeffField d) (deltaA deltaB : ℝ)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hb : ∀ i j, AEMeasurable (fun x => b x i j) (volumeOn U))
    (hcloseA : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE deltaA (a x) (1 : Mat d))
    (hcloseB : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE deltaB (b x) (1 : Mat d))
    (F G : Vec d → Vec d) (hF : MemVectorL2On U F) (hG : MemVectorL2On U G)
    (v : H1Function U) :
    MemVectorL2On U (perturbativeDirichletResidual a b F G v) := by
  exact fun i => (vectorDifferenceMemL2 F G hF hG i).add
    (coefficientDifferenceGradientMemL2 a b deltaA deltaB ha hb hcloseA hcloseB v i)

/-- Subtracting two genuine weak equations gives the actual residual equation
for an explicit zero-boundary difference representative. -/
theorem perturbativeDirichletResidual_isH10Solution
    (a b : CoeffField d) (deltaA deltaB : ℝ)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hb : ∀ i j, AEMeasurable (fun x => b x i j) (volumeOn U))
    (hcloseA : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE deltaA (a x) (1 : Mat d))
    (hcloseB : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE deltaB (b x) (1 : Mat d))
    (F G : Vec d → Vec d) (hF : MemVectorL2On U F) (hG : MemVectorL2On U G)
    (u v : H1Function U)
    (hu : IsWeakDivergenceFormSolutionOn a U u 0 F)
    (hv : IsWeakDivergenceFormSolutionOn b U v 0 G)
    (w : H10Function U) (hw : w.toH1Function = u - v) :
    IsWeakDivergenceFormH10SolutionOn a U w.toH1Function 0
      (perturbativeDirichletResidual a b F G v) := by
  have hua : IsWeakDivergenceFormH10SolutionOn a U u 0 F :=
    hu.toH10SolutionOn_of_isMatrixPerturbationLE ha hcloseA hF
  have hvb : IsWeakDivergenceFormH10SolutionOn b U v 0 G :=
    hv.toH10SolutionOn_of_isMatrixPerturbationLE hb hcloseB hG
  have hres := perturbativeDirichletResidual_memL2 a b deltaA deltaB ha hb
    hcloseA hcloseB F G hF hG v
  have hwgrad : w.toH1Function.grad = fun x => u.grad x - v.grad x := by
    simpa only [H1Function.sub_grad] using congrArg H1Function.grad hw
  intro φ
  have hflux := memVectorL2On_matVecMul_of_isMatrixPerturbationLE
    ha hcloseA w.toH1Function.gradMemL2
  refine ⟨{
    flux_integrable := integrableOn_vecDot_of_memVectorL2On hflux
      φ.toH1Function.gradMemL2
    source_integrable := by simp
    forcing_integrable := integrableOn_vecDot_of_memVectorL2On hres
      φ.toH1Function.gradMemL2 }, ?_⟩
  have huEq := (hua φ).2
  have hvEq := (hvb φ).2
  simp only [Pi.zero_apply, zero_mul, integral_zero, zero_sub] at huEq hvEq ⊢
  rw [hwgrad]
  have hpoint : ∀ x,
      vecDot (matVecMul (a x) (u.grad x - v.grad x)) (φ.toH1Function.grad x) =
        vecDot (matVecMul (a x) (u.grad x)) (φ.toH1Function.grad x) -
          vecDot (matVecMul (b x) (v.grad x)) (φ.toH1Function.grad x) -
          vecDot (perturbativeDirichletResidual a b F G v x)
            (φ.toH1Function.grad x) +
          vecDot (F x) (φ.toH1Function.grad x) -
          vecDot (G x) (φ.toH1Function.grad x) := by
    intro x
    simp only [perturbativeDirichletResidual]
    rw [show matVecMul (a x) (u.grad x - v.grad x) =
      matVecMul (a x) (u.grad x) - matVecMul (a x) (v.grad x) by
        change (a x).mulVec (u.grad x - v.grad x) = _
        exact Matrix.mulVec_sub _ _ _]
    rw [vecDot_sub_left]
    rw [vecDot_add_left, vecDot_sub_left, matVecMul_sub_apply,
      vecDot_sub_left]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint)]
  have hAu := memVectorL2On_matVecMul_of_isMatrixPerturbationLE ha hcloseA u.gradMemL2
  have hBv := memVectorL2On_matVecMul_of_isMatrixPerturbationLE hb hcloseB v.gradMemL2
  have iAu := integrableOn_vecDot_of_memVectorL2On hAu φ.toH1Function.gradMemL2
  have iBv := integrableOn_vecDot_of_memVectorL2On hBv φ.toH1Function.gradMemL2
  have iRes := integrableOn_vecDot_of_memVectorL2On hres φ.toH1Function.gradMemL2
  have iF := integrableOn_vecDot_of_memVectorL2On hF φ.toH1Function.gradMemL2
  have iG := integrableOn_vecDot_of_memVectorL2On hG φ.toH1Function.gradMemL2
  let Au : Vec d → ℝ := fun x =>
    vecDot (matVecMul (a x) (u.grad x)) (φ.toH1Function.grad x)
  let Bv : Vec d → ℝ := fun x =>
    vecDot (matVecMul (b x) (v.grad x)) (φ.toH1Function.grad x)
  let Res : Vec d → ℝ := fun x =>
    vecDot (perturbativeDirichletResidual a b F G v x) (φ.toH1Function.grad x)
  let FF : Vec d → ℝ := fun x => vecDot (F x) (φ.toH1Function.grad x)
  let GG : Vec d → ℝ := fun x => vecDot (G x) (φ.toH1Function.grad x)
  change (∫ x in U, (((Au x - Bv x) - Res x) + FF x) - GG x) =
    -∫ x in U, Res x
  rw [show (∫ x in U, (((Au x - Bv x) - Res x) + FF x) - GG x) =
      (∫ x in U, ((Au x - Bv x) - Res x) + FF x) - ∫ x in U, GG x from
        integral_sub ((iAu.sub iBv).sub iRes |>.add iF) iG,
    show (∫ x in U, ((Au x - Bv x) - Res x) + FF x) =
      (∫ x in U, (Au x - Bv x) - Res x) + ∫ x in U, FF x from
        integral_add ((iAu.sub iBv).sub iRes) iF,
    show (∫ x in U, (Au x - Bv x) - Res x) =
      (∫ x in U, Au x - Bv x) - ∫ x in U, Res x from
        integral_sub (iAu.sub iBv) iRes,
    show (∫ x in U, Au x - Bv x) =
      (∫ x in U, Au x) - ∫ x in U, Bv x from integral_sub iAu iBv]
  rw [huEq, hvEq]
  ring

/-- Quantitative `L²` stability, with both residual pieces constructed from
their genuine native `L²` membership proofs. -/
theorem norm_gradient_sub_le_perturbative_data
    (a b : CoeffField d) (deltaA deltaB : ℝ)
    (hdeltaA : 0 ≤ deltaA) (hdeltaAOne : deltaA < 1) (hdeltaB : 0 ≤ deltaB)
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hb : ∀ i j, AEMeasurable (fun x => b x i j) (volumeOn U))
    (hcloseA : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE deltaA (a x) (1 : Mat d))
    (hcloseB : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE deltaB (b x) (1 : Mat d))
    (F G : Vec d → Vec d) (hF : MemVectorL2On U F) (hG : MemVectorL2On U G)
    (u v : H1Function U)
    (hu : IsWeakDivergenceFormSolutionOn a U u 0 F)
    (hv : IsWeakDivergenceFormSolutionOn b U v 0 G)
    (w : H10Function U) (hw : w.toH1Function = u - v) :
    ‖w.toH1Function.gradMemL2.toHilbertVectorLp‖ ≤
      (1 - deltaA)⁻¹ *
        (‖(vectorDifferenceMemL2 F G hF hG).toHilbertVectorLp‖ +
          ‖(coefficientDifferenceGradientMemL2OfNonneg a b deltaA deltaB
            hdeltaA hdeltaB ha hb hcloseA hcloseB v).toHilbertVectorLp‖) := by
  let H := perturbativeDirichletResidual a b F G v
  let hDiff := vectorDifferenceMemL2 F G hF hG
  let hCoeff := coefficientDifferenceGradientMemL2OfNonneg a b deltaA deltaB
    hdeltaA hdeltaB ha hb hcloseA hcloseB v
  let hH := perturbativeDirichletResidual_memL2 a b deltaA deltaB ha hb
    hcloseA hcloseB F G hF hG v
  have hsol := perturbativeDirichletResidual_isH10Solution a b deltaA deltaB
    ha hb hcloseA hcloseB F G hF hG u v hu hv w hw
  have heq := (hsol w).2
  simp only [Pi.zero_apply, zero_mul, integral_zero, zero_sub] at heq
  have hpoint : ∀ᵐ x ∂volumeOn U,
      (1 - deltaA) * vecNormSq (w.toH1Function.grad x) ≤
        vecDot (matVecMul (a x) (w.toH1Function.grad x))
          (w.toH1Function.grad x) := by
    filter_upwards [hcloseA] with x hx
    simpa only [vecDot_comm] using
      one_sub_delta_mul_vecNormSq_le_vecDot_matVecMul_of_isMatrixPerturbationLE
        hx (w.toH1Function.grad x)
  have hflux := memVectorL2On_matVecMul_of_isMatrixPerturbationLE
    ha hcloseA w.toH1Function.gradMemL2
  have henergy :
      (1 - deltaA) * ∫ x in U, vecNormSq (w.toH1Function.grad x) ≤
        ∫ x in U, vecDot (matVecMul (a x) (w.toH1Function.grad x))
          (w.toH1Function.grad x) := by
    rw [← integral_const_mul]
    exact integral_mono_ae
      ((integrableOn_vecNormSq_of_memVectorL2On w.toH1Function.gradMemL2).const_mul _)
      (integrableOn_vecDot_of_memVectorL2On hflux w.toH1Function.gradMemL2)
      hpoint
  rw [heq] at henergy
  have hpair := abs_setIntegral_vecDot_le_sqrt_setIntegral_vecNormSq_mul
    hH w.toH1Function.gradMemL2
  have hneg :
      -(∫ x in U, vecDot (H x) (w.toH1Function.grad x)) ≤
        |∫ x in U, vecDot (H x) (w.toH1Function.grad x)| := neg_le_abs _
  have hmain := henergy.trans (hneg.trans hpair)
  rw [setIntegral_vecNormSq_eq_sq_norm_toHilbertVectorLp
      w.toH1Function.gradMemL2,
    setIntegral_vecNormSq_eq_sq_norm_toHilbertVectorLp hH,
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _)] at hmain
  have hbase : ‖w.toH1Function.gradMemL2.toHilbertVectorLp‖ ≤
      (1 - deltaA)⁻¹ * ‖hH.toHilbertVectorLp‖ := by
    by_cases hz : ‖w.toH1Function.gradMemL2.toHilbertVectorLp‖ = 0
    · simp [hz, mul_nonneg (inv_nonneg.mpr (sub_nonneg.mpr hdeltaAOne.le))
          (norm_nonneg _)]
    · have hp : 0 < ‖w.toH1Function.gradMemL2.toHilbertVectorLp‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      have hcancel : (1 - deltaA) *
          ‖w.toH1Function.gradMemL2.toHilbertVectorLp‖ ≤
          ‖hH.toHilbertVectorLp‖ := by
        apply le_of_mul_le_mul_right ?_ hp
        simpa only [pow_two, mul_assoc] using hmain
      exact (le_inv_mul_iff₀ (sub_pos.mpr hdeltaAOne)).2 hcancel
  have htriangle := sqrt_setIntegral_vecNormSq_add_le hDiff hCoeff
  change Real.sqrt (∫ x in U, vecNormSq (H x)) ≤
    Real.sqrt (∫ x in U, vecNormSq ((fun x => F x - G x) x)) +
      Real.sqrt (∫ x in U,
        vecNormSq ((fun x => matVecMul (a x - b x) (v.grad x)) x)) at htriangle
  rw [setIntegral_vecNormSq_eq_sq_norm_toHilbertVectorLp hH,
    setIntegral_vecNormSq_eq_sq_norm_toHilbertVectorLp hDiff,
    setIntegral_vecNormSq_eq_sq_norm_toHilbertVectorLp hCoeff,
    Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (norm_nonneg _),
    Real.sqrt_sq (norm_nonneg _)] at htriangle
  have hclasses : ‖hH.toHilbertVectorLp‖ ≤
      ‖hDiff.toHilbertVectorLp‖ + ‖hCoeff.toHilbertVectorLp‖ := by
    simpa only [H, hDiff, hCoeff, hH, perturbativeDirichletResidual] using htriangle
  exact hbase.trans (mul_le_mul_of_nonneg_left hclasses
    (inv_nonneg.mpr (sub_nonneg.mpr (by linarith [hdeltaA]))))

end

end PDE
