module

public import PDEFoundation.Analysis.NativeLpInjectedDuality
public import PDEFoundation.Analysis.HilbertLpPairingNorm

/-! # Minimality of native densities for injective `Lᵖ` embeddings -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

noncomputable section

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Every native density representing a functional through an injective
conjugate-`Lᵖ` embedding has `Lᵖ` norm at least the functional norm. This is a
conditional comparison helper: the candidate density and its representation
identity are explicit inputs. -/
theorem norm_le_nativeLp_density_of_represents_injective
    [IsFiniteMeasure μ] {d : ℕ} {p : ℝ} (hp : 1 < p)
    [Fact (1 ≤ ENNReal.ofReal p)]
    [Fact (1 ≤ ENNReal.ofReal (p / (p - 1)))]
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : E →ₗ[ℝ]
      Lp (HilbertVec d) (ENNReal.ofReal (p / (p - 1))) μ)
    (hA : Function.Injective A) :
    letI : NormedAddCommGroup E :=
      NormedAddCommGroup.induced E
        (Lp (HilbertVec d) (ENNReal.ofReal (p / (p - 1))) μ) A hA
    letI : NormedSpace ℝ E :=
      NormedSpace.induced ℝ E
        (Lp (HilbertVec d) (ENNReal.ofReal (p / (p - 1))) μ) A
    ∀ (L : E →L[ℝ] ℝ) (G : α → Vec d),
      (∀ i : Fin d, AEStronglyMeasurable (fun x => G x i) μ) →
      MemLp (fun x => vecEuclideanNorm (G x)) (ENNReal.ofReal p) μ →
      (∀ u : E, L u = -∫ x, vecDot (G x) ((A u x).toVec) ∂μ) →
      ‖L‖ ≤ (eLpNorm (fun x => vecEuclideanNorm (G x))
        (ENNReal.ofReal p) μ).toReal := by
  let _ : NormedAddCommGroup E :=
    NormedAddCommGroup.induced E
      (Lp (HilbertVec d) (ENNReal.ofReal (p / (p - 1))) μ) A hA
  let _ : NormedSpace ℝ E :=
    NormedSpace.induced ℝ E
      (Lp (HilbertVec d) (ENNReal.ofReal (p / (p - 1))) μ) A
  intro L G hGmeas hGnorm hrep
  have hGcoord (i : Fin d) :
      MemLp (fun x => G x i) (ENNReal.ofReal p) μ := by
    apply hGnorm.of_le (hGmeas i)
    filter_upwards with x
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (vecEuclideanNorm_nonneg _)] using
      abs_apply_le_vecEuclideanNorm (G x) i
  let GH : α → HilbertVec d := fun x => WithLp.toLp 2 (G x)
  have hGH : MemLp GH (ENNReal.ofReal p) μ :=
    MemLp.of_eval_piLp hGcoord
  let g : Lp (HilbertVec d) (ENNReal.ofReal p) μ := hGH.toLp GH
  let Ac : E →L[ℝ]
      Lp (HilbertVec d) (ENNReal.ofReal (p / (p - 1))) μ :=
    A.mkContinuous 1 (fun u => by
      change ‖A u‖ ≤ 1 * ‖A u‖
      rw [one_mul])
  have hAcNorm : ‖Ac‖ ≤ 1 := by
    exact A.mkContinuous_norm_le zero_le_one _
  let _ : ENNReal.HolderConjugate (ENNReal.ofReal p)
      (ENNReal.ofReal (p / (p - 1))) :=
    (Real.HolderConjugate.conjExponent hp).ennrealOfReal
  let J : Lp (HilbertVec d) (ENNReal.ofReal (p / (p - 1))) μ →L[ℝ] ℝ :=
    -((innerSL ℝ).lpPairing μ (ENNReal.ofReal p)
      (ENNReal.ofReal (p / (p - 1))) g)
  have hL : L = J.comp Ac := by
    ext u
    rw [hrep u]
    change -∫ x, vecDot (G x) ((A u x).toVec) ∂μ =
      -((innerSL ℝ).lpPairing μ (ENNReal.ofReal p)
        (ENNReal.ofReal (p / (p - 1))) g (A u))
    rw [ContinuousLinearMap.lpPairing_eq_integral]
    congr 1
    apply integral_congr_ae
    filter_upwards [hGH.coeFn_toLp] with x hx
    rw [hx]
    change vecDot (G x) ((A u x).toVec) =
      inner ℝ (WithLp.toLp 2 (G x)) (A u x)
    rw [PiLp.inner_apply]
    simp only [RCLike.inner_apply, conj_trivial, HilbertVec.toVec_apply, vecDot]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  have hJNorm : ‖J‖ = ‖g‖ := by
    dsimp only [J]
    rw [norm_neg]
    exact norm_hilbertLpPairing_eq hp g
  have hgNorm : ‖g‖ =
      (eLpNorm (fun x => vecEuclideanNorm (G x))
        (ENNReal.ofReal p) μ).toReal := by
    dsimp only [g]
    rw [Lp.norm_toLp]
    apply congrArg ENNReal.toReal
    apply eLpNorm_congr_norm_ae hGH.aestronglyMeasurable
      hGnorm.aestronglyMeasurable
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (vecEuclideanNorm_nonneg (G x))]
    exact HilbertVec.norm_eq_vecEuclideanNorm (WithLp.toLp 2 (G x))
  rw [hL]
  calc
    ‖J.comp Ac‖ ≤ ‖J‖ * ‖Ac‖ := J.opNorm_comp_le Ac
    _ ≤ ‖J‖ * 1 := mul_le_mul_of_nonneg_left hAcNorm (norm_nonneg J)
    _ = ‖J‖ := mul_one _
    _ = ‖g‖ := hJNorm
    _ = _ := hgNorm

end

end PDE
