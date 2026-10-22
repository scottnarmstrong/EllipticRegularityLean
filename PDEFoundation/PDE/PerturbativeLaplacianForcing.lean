module

public import PDEFoundation.PDE.PerturbationL2
public import PDEFoundation.PDE.WeakDivergenceForm
public import PDEFoundation.Sobolev.W1p.EuclideanGradient

/-! # Rewriting perturbative equations as Laplacian equations -/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

noncomputable section

/-- A coefficient perturbation preserves coordinatewise `Lᵖ` membership for
every extended exponent. -/
theorem gradMemLpOn_matVecMul_sub_identity_of_isMatrixPerturbationLE
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {g : Vec d → Vec d}
    {delta : ℝ} {p : ENNReal}
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hclose : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (hg : GradMemLpOn U p g) :
    GradMemLpOn U p (fun x => matVecMul (a x - 1) (g x)) := by
  classical
  intro i
  let P : Vec d → Vec d := fun x => matVecMul (a x - 1) (g x)
  have hmeas : AEStronglyMeasurable (fun x => P x i) (volumeOn U) := by
    have hs := Finset.aestronglyMeasurable_sum Finset.univ (fun j _ =>
        ((ha i j).sub (aemeasurable_const : AEMeasurable
          (fun _ : Vec d => (1 : Mat d) i j) (volumeOn U))).aestronglyMeasurable.mul
          (hg j).aestronglyMeasurable)
    convert hs using 1
    funext x
    dsimp only [P, matVecMul]
    rw [Finset.sum_apply]
    rfl
  have hmag := hg.memLp_vecEuclideanNorm
  apply MemLp.of_le_mul hmag hmeas
  filter_upwards [hclose] with x hx
  calc
    ‖P x i‖ = |P x i| := Real.norm_eq_abs _
    _ ≤ vecEuclideanNorm (P x) := abs_apply_le_vecEuclideanNorm _ _
    _ ≤ delta * vecEuclideanNorm (g x) := hx (g x)
    _ = delta * ‖vecEuclideanNorm (g x)‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (vecEuclideanNorm_nonneg _)]

/-- The perturbation flux has the exact, dimension-free Euclidean `Lᵖ`
bound for every extended exponent. -/
theorem eLpNorm_vecEuclideanNorm_matVecMul_sub_identity_le
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {g : Vec d → Vec d}
    {delta : ℝ} {p : ENNReal} (hdelta : 0 ≤ delta)
    (hclose : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (hP : AEStronglyMeasurable
      (fun x => vecEuclideanNorm (matVecMul (a x - 1) (g x))) (volumeOn U)) :
    eLpNorm (fun x => vecEuclideanNorm (matVecMul (a x - 1) (g x))) p
        (volumeOn U) ≤
      ENNReal.ofReal delta *
        eLpNorm (fun x => vecEuclideanNorm (g x)) p (volumeOn U) := by
  let c : NNReal := ⟨delta, hdelta⟩
  have hc : (c : ENNReal) = ENNReal.ofReal delta := by
    rw [ENNReal.coe_nnreal_eq]
    rfl
  have hscale := eLpNorm_le_nnreal_smul_eLpNorm_of_ae_le_mul'
    (μ := volumeOn U)
    (f := fun x => vecEuclideanNorm (matVecMul (a x - 1) (g x)))
    (g := fun x => vecEuclideanNorm (g x)) (c := c) (p := p) hP (by
      filter_upwards [hclose] with x hx
      simpa only [Real.enorm_eq_ofReal (vecEuclideanNorm_nonneg _), hc,
        ENNReal.ofReal_mul hdelta] using
        ENNReal.ofReal_le_ofReal (hx (g x)))
  simpa only [ENNReal.smul_def, smul_eq_mul, hc] using! hscale

/-- Moving the coefficient perturbation to the forcing rewrites the original
weak equation as a Laplacian equation. The new forcing is the literal sum
`F + (a - I) ∇u`. -/
theorem IsWeakDivergenceFormSolutionOn.toLaplacian_of_isMatrixPerturbationLE
    {d : ℕ} {U : Set (Vec d)} {a : CoeffField d} {delta : ℝ}
    {u : H1Function U} {F : Vec d → Vec d}
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U))
    (hclose : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE delta (a x) (1 : Mat d))
    (hF : MemVectorL2On U F)
    (hsol : IsWeakDivergenceFormSolutionOn a U u 0 F) :
    IsWeakDivergenceFormSolutionOn (fun _ => (1 : Mat d)) U u 0
      (fun x => F x + matVecMul (a x - 1) (u.grad x)) := by
  let P : Vec d → Vec d := fun x => matVecMul (a x - 1) (u.grad x)
  let G : Vec d → Vec d := fun x => F x + P x
  have hP : MemVectorL2On U P := by
    exact memVectorL2On_matVecMul_sub_identity_of_isMatrixPerturbationLE
      ha hclose u.gradMemL2
  have hG : MemVectorL2On U G := fun i => (hF i).add (hP i)
  have hone : (fun x => matVecMul (1 : Mat d) (u.grad x)) = u.grad := by
    funext x
    exact Matrix.one_mulVec (u.grad x)
  intro φ
  have hdata : DivergenceFormL2DataOn (fun _ => (1 : Mat d)) U u 0 G := by
    refine ⟨?_, MeasureTheory.MemLp.zero, hG⟩
    rw [hone]
    exact u.gradMemL2
  refine ⟨hdata.testable φ, ?_⟩
  have hgradInt := integrableOn_vecDot_weakTestFunction_grad u.gradMemL2 φ
  have hPInt := integrableOn_vecDot_weakTestFunction_grad hP φ
  have hsplit : (∫ x in U,
      vecDot (matVecMul (a x) (u.grad x)) (φ.grad x)) =
      (∫ x in U, vecDot (u.grad x) (φ.grad x)) +
        ∫ x in U, vecDot (P x) (φ.grad x) := by
    rw [← integral_add hgradInt hPInt]
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [P]
    classical
    change vecDot ((a x).mulVec (u.grad x)) (φ.grad x) =
      vecDot (u.grad x) (φ.grad x) +
        vecDot ((a x - 1).mulVec (u.grad x)) (φ.grad x)
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    simp only [vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    ring
  have horig := (hsol φ).2
  simp only [Pi.zero_apply, zero_mul, integral_zero, zero_sub] at horig ⊢
  have hGInt : (∫ x in U, vecDot (G x) (φ.grad x)) =
      (∫ x in U, vecDot (F x) (φ.grad x)) +
        ∫ x in U, vecDot (P x) (φ.grad x) := by
    rw [← integral_add
      (integrableOn_vecDot_weakTestFunction_grad hF φ) hPInt]
    apply integral_congr_ae
    filter_upwards with x
    dsimp only [G]
    simp only [vecDot, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  rw [hsplit] at horig
  simp_rw [show ∀ x, matVecMul (1 : Mat d) (u.grad x) = u.grad x from
    fun x => Matrix.one_mulVec (u.grad x)]
  change (∫ x in U, vecDot (u.grad x) (φ.grad x)) =
    -(∫ x in U, vecDot (G x) (φ.grad x))
  rw [hGInt]
  linarith

end

end PDE
