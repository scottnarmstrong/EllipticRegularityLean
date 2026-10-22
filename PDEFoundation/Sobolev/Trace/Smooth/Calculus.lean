module

public import PDEFoundation.Sobolev.Trace.Chart.FactsTopology
public import PDEFoundation.Sobolev.ClassicalGradient

/-!
# Derivative of the chart map

The Fréchet derivative of `Ψ(x', t) = insertNth i (γ x' + sgn t) x'` is
`(h, s) ↦ insertNth i (γ'(x') h + sgn s) h`; a Lipschitz function has directional derivatives
bounded by `L |h|`, and `insertNth` is controlled in the Euclidean norm.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set

variable {n : ℕ} {i : Fin (n + 1)} {γ : Vec n → ℝ} {sgn L : ℝ}

theorem vecEuclideanNorm_insertNth_le (a : ℝ) (x : Vec n) :
    vecEuclideanNorm (Fin.insertNth (α := fun _ => ℝ) i a x : Vec (n + 1)) ≤
      |a| + vecEuclideanNorm x := by
  have hx := vecEuclideanNorm_nonneg x
  have hsq : vecNormSq (Fin.insertNth (α := fun _ => ℝ) i a x : Vec (n + 1)) =
      a ^ 2 + vecEuclideanNorm x ^ 2 := by
    rw [vecEuclideanNorm_sq, vecNormSq_eq_sum_sq, vecNormSq_eq_sum_sq, Fin.sum_univ_succAbove _ i]
    simp
  have hdef : vecEuclideanNorm (Fin.insertNth (α := fun _ => ℝ) i a x : Vec (n + 1)) =
      Real.sqrt (vecNormSq (Fin.insertNth (α := fun _ => ℝ) i a x : Vec (n + 1))) := rfl
  rw [hdef, hsq]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  nlinarith [abs_nonneg a, sq_abs a, mul_nonneg (abs_nonneg a) hx]

/-- A Lipschitz function has directional derivatives bounded by `L |h|`. -/
theorem abs_fderiv_apply_le_of_lip (hγ : ContDiff ℝ 1 γ) (hL0 : 0 ≤ L)
    (hL : ∀ x' y' : Vec n, |γ x' - γ y'| ≤ L * vecEuclideanNorm (x' - y')) (x' h : Vec n) :
    |fderiv ℝ γ x' h| ≤ L * vecEuclideanNorm h := by
  set g : ℝ → ℝ := fun t => γ (x' + t • h) with hg
  have hlip : LipschitzWith (Real.toNNReal (L * vecEuclideanNorm h)) g := by
    refine LipschitzWith.of_dist_le_mul fun s t => ?_
    rw [Real.coe_toNNReal _ (by have := vecEuclideanNorm_nonneg h; positivity), Real.dist_eq]
    refine (hL _ _).trans ?_
    have : x' + s • h - (x' + t • h) = (s - t) • h := by rw [sub_smul]; abel
    rw [this, vecEuclideanNorm_smul, Real.dist_eq]
    nlinarith
  have h1 : HasDerivAt (fun t : ℝ => x' + t • h) h 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const h).const_add x'
  have h2 : HasFDerivAt γ (fderiv ℝ γ x') (x' + (0 : ℝ) • h) := by
    simpa using (hγ.differentiable (by simp)).differentiableAt.hasFDerivAt
  have h3 : HasDerivAt g (fderiv ℝ γ x' h) 0 := by
    have h4 := h2.comp_hasDerivAt (0 : ℝ) h1
    exact h4
  have := norm_deriv_le_of_lipschitz (x₀ := 0) hlip
  rw [h3.deriv, Real.norm_eq_abs, Real.coe_toNNReal _ (by
    have := vecEuclideanNorm_nonneg h; positivity)] at this
  exact this

/-- The derivative of the chart map. -/
theorem fderiv_graphMap_apply (hγ : ContDiff ℝ 1 γ) (z h : Vec n × ℝ) :
    fderiv ℝ (graphMap i γ sgn) z h =
      Fin.insertNth (α := fun _ => ℝ) i (fderiv ℝ γ z.1 h.1 + sgn * h.2) h.1 := by
  have hd : DifferentiableAt ℝ (graphMap i γ sgn) z :=
    ((contDiff_graphMap (sgn := sgn) hγ).differentiable (by simp)) z
  have hγd : DifferentiableAt ℝ γ z.1 := (hγ.differentiable (by simp)) z.1
  have hpi := hasFDerivAt_pi'.1 hd.hasFDerivAt
  funext j
  refine Fin.succAboveCases i ?_ ?_ j
  · have h2 := hpi i
    have h1 : HasFDerivAt (fun x : Vec n × ℝ => γ x.1 + sgn * x.2)
        ((fderiv ℝ γ z.1).comp (ContinuousLinearMap.fst ℝ (Vec n) ℝ) +
          sgn • ContinuousLinearMap.snd ℝ (Vec n) ℝ) z :=
      (hγd.hasFDerivAt.comp z (hasFDerivAt_fst)).add (hasFDerivAt_snd.const_mul sgn)
    have h1' := h1.congr_of_eventuallyEq (f₁ := fun x => graphMap i γ sgn x i)
      (Filter.Eventually.of_forall fun x => by simp [graphMap])
    have h3 := h2.unique h1'
    have := congrArg (fun L => L h) h3
    simpa using this
  · intro k
    have h2 := hpi (i.succAbove k)
    have h1 : HasFDerivAt (fun x : Vec n × ℝ => x.1 k)
        ((ContinuousLinearMap.proj k).comp (ContinuousLinearMap.fst ℝ (Vec n) ℝ)) z :=
      (hasFDerivAt_apply (𝕜 := ℝ) k z.1).comp z hasFDerivAt_fst
    have h1' := h1.congr_of_eventuallyEq (f₁ := fun x => graphMap i γ sgn x (i.succAbove k))
      (Filter.Eventually.of_forall fun x => by simp [graphMap])
    have h3 := h2.unique h1'
    have := congrArg (fun L => L h) h3
    simpa using this

end PDE.TraceLane
