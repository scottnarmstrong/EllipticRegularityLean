module

public import EllipticRegularity.Ch4.GreenDecay.Riesz
public import EllipticRegularity.Ch4.GreenDecay.Algebra
public import EllipticRegularity.Meyers.DualityAux
public import PDEFoundation.Sobolev.Ch4.H10Algebra
public import PDEFoundation.Sobolev.Inequalities.ZeroBoundaryBall

/-!
# The Dirichlet problem on `B_R` (Lemma 4.33): existence

Existence of an `H¹₀(B_R)` solution of `-div (b ∇v) = g + div F` for an elliptic coefficient field
`b`, an `L²` source `g` and an `L²` forcing `F`.  The source is converted into a divergence forcing by the
Riesz representation `Riesz.lean`; the resulting divergence-form problem is solved by the perturbative
Lax--Milgram operator after the rescaling `b ↦ Λ⁻² b`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4GreenDecay

open MeasureTheory PDE PDE.MeyersDuality

noncomputable section

variable {d : ℕ}

/-- **Existence for the Dirichlet problem** on `B_R`. -/
theorem exists_dirichlet_solution (hd : 0 < d) {Λ R : ℝ} (hR : 0 < R) {b : CoeffField d}
    (hbm : ∀ i j : Fin d,
      AEMeasurable (fun x => b x i j) (volumeOn (euclideanBall (0 : Vec d) R)))
    (hbell : ∀ x ∈ euclideanBall (0 : Vec d) R, IsEllipticMatrix 1 Λ (b x))
    {g : Vec d → ℝ} {F : Vec d → Vec d}
    (hg : MemL2On (euclideanBall (0 : Vec d) R) g)
    (hF : MemVectorL2On (euclideanBall (0 : Vec d) R) F) :
    ∃ v : H10Function (euclideanBall (0 : Vec d) R),
      IsWeakDivergenceFormH10SolutionOn b (euclideanBall (0 : Vec d) R) v.toH1Function g F := by
  set U := euclideanBall (0 : Vec d) R with hUdef
  have hU : IsOpen U := isOpen_euclideanBall 0 R
  have hUm : MeasurableSet U := measurableSet_euclideanBall _ _
  have h0 : (0 : Vec d) ∈ U := by
    rw [hUdef, mem_euclideanBall_iff_vecEuclideanNorm_lt hR]
    simp [vecEuclideanNorm, vecNormSq, vecDot, hR]
  have hA0 := hbell 0 h0
  have hΛ : 0 < Λ := hA0.Lam_pos
  set s : ℝ := (Λ ^ 2)⁻¹ with hs
  have hspos : 0 < s := by rw [hs]; positivity
  have hs1 : s ≤ 1 := by
    have hΛ1 : 1 ≤ Λ := hA0.lam_le_Lam
    rw [hs]
    have : 1 ≤ Λ ^ 2 := by nlinarith
    exact inv_le_one_of_one_le₀ this
  have hδ0 : 0 ≤ Real.sqrt (1 - s) := Real.sqrt_nonneg _
  have hδ1 : Real.sqrt (1 - s) < 1 := by
    rw [Real.sqrt_lt' one_pos]; nlinarith
  obtain ⟨G, hG, hGφ⟩ := exists_riesz_source hd hR hg
  have hb' : ∀ i j, AEMeasurable (fun x => (s • b x) i j) (volumeOn U) := by
    intro i j
    simpa only [Matrix.smul_apply, smul_eq_mul] using (hbm i j).const_mul s
  have hclose : ∀ᵐ x ∂volumeOn U,
      IsMatrixPerturbationLE (Real.sqrt (1 - s)) (s • b x) (1 : Mat d) := by
    have hmem : ∀ᵐ x ∂ volumeOn U, x ∈ U :=
      (MeasureTheory.ae_restrict_iff' hUm).2 (Filter.Eventually.of_forall fun x hx => hx)
    filter_upwards [hmem] with x hx
    exact isMatrixPerturbationLE_inv_sq_smul_of_isEllipticMatrix (hbell x hx)
  have hFG : MemVectorL2On U (fun x => s • (F x - G x)) := by
    refine memVectorL2On_smul ?_ s
    intro i
    exact (hF i).sub (hG i)
  obtain ⟨w, -, hw⟩ := exists_ballDirichletGradient_solution hd 0 R hR
    (fun x => s • b x) (Real.sqrt (1 - s)) hδ0 hδ1 hb' hclose
    (fun x => s • (F x - G x)) hFG
  refine ⟨w, fun φ => ?_⟩
  have hφ := hw φ
  have hflux : IntegrableOn
      (fun x => vecDot (matVecMul (b x) (w.toH1Function.grad x)) (φ.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2On
      (memVectorL2On_matVecMul_of_ae_elliptic hUm hbm hbell w.toH1Function.gradMemL2)
      φ.toH1Function.gradMemL2
  have hFint : IntegrableOn (fun x => vecDot (F x) (φ.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2On hF φ.toH1Function.gradMemL2
  have hGint : IntegrableOn (fun x => vecDot (G x) (φ.toH1Function.grad x)) U :=
    integrableOn_vecDot_of_memVectorL2On hG φ.toH1Function.gradMemL2
  have hgint : IntegrableOn (fun x => g x * φ.toH1Function x) U :=
    integrableOn_mul_of_memL2On hg φ.toH1Function.memL2
  refine ⟨⟨hflux, hgint, hFint⟩, ?_⟩
  have heq := hφ.2
  have e1 : (∫ x in U, vecDot (matVecMul ((fun x => s • b x) x) (w.toH1Function.grad x))
        (φ.toH1Function.grad x)) =
      s * ∫ x in U, vecDot (matVecMul (b x) (w.toH1Function.grad x)) (φ.toH1Function.grad x) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [matVecMul_smul_left', vecDot_smul_left']
  have e2 : (∫ x in U, vecDot ((fun x => s • (F x - G x)) x) (φ.toH1Function.grad x)) =
      s * ((∫ x in U, vecDot (F x) (φ.toH1Function.grad x)) -
        ∫ x in U, vecDot (G x) (φ.toH1Function.grad x)) := by
    rw [← integral_sub hFint hGint, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [vecDot_smul_left', vecDot_sub_left']
  rw [e1, e2] at heq
  simp only [Pi.zero_apply, zero_mul, integral_zero, zero_sub] at heq
  have hgG := hGφ φ
  have : s * (∫ x in U, vecDot (matVecMul (b x) (w.toH1Function.grad x))
      (φ.toH1Function.grad x)) =
      s * ((∫ x in U, g x * φ.toH1Function.toFun x) -
        ∫ x in U, vecDot (F x) (φ.toH1Function.grad x)) := by
    rw [heq, hgG]; ring
  exact mul_left_cancel₀ hspos.ne' this

end

end PDE.Ch4GreenDecay
