module

public import PDEFoundation.Analysis.HahnBanachInjectedNorm
public import PDEFoundation.Measure.HilbertVectorLpDuality
public import PDEFoundation.Ambient.EuclideanNorm

/-! # Native finite-vector duality through an injective `Lᵖ` embedding -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal RealInnerProductSpace

noncomputable section

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}

/-- An injective linear embedding into a conjugate Hilbert-vector `Lᵖ` space
represents every continuous functional by an actual native vector field. This
is a conditional functional-analytic helper: the embedding and its injectivity
remain explicit inputs. -/
theorem exists_nativeLp_density_through_injective
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
    ∀ L : E →L[ℝ] ℝ, ∃ F : α → Vec d,
      (∀ i : Fin d, AEStronglyMeasurable (fun x => F x i) μ) ∧
      MemLp (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p) μ ∧
      (∀ u : E, L u = -∫ x, vecDot (F x) ((A u x).toVec) ∂μ) ∧
      (eLpNorm (fun x => vecEuclideanNorm (F x))
        (ENNReal.ofReal p) μ).toReal = ‖L‖ := by
  let _ : NormedAddCommGroup E :=
    NormedAddCommGroup.induced E
      (Lp (HilbertVec d) (ENNReal.ofReal (p / (p - 1))) μ) A hA
  let _ : NormedSpace ℝ E :=
    NormedSpace.induced ℝ E
      (Lp (HilbertVec d) (ENNReal.ofReal (p / (p - 1))) μ) A
  intro L
  rcases exists_extension_through_injective_linearMap A hA L with
    ⟨J, hJrep, hJnorm⟩
  rcases Internal.exists_hilbertVectorLp_dual_density hp J with
    ⟨g, hgrep, hgnorm⟩
  let F : α → Vec d := fun x => -(g x).toVec
  refine ⟨F, ?_, ?_, ?_, ?_⟩
  · intro i
    have hgmeas : AEStronglyMeasurable (fun x => g x) μ :=
      Lp.aestronglyMeasurable g
    have hcoord : AEStronglyMeasurable (fun x => g x i) μ :=
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin d => ℝ) i).continuous.comp_aestronglyMeasurable
        hgmeas
    have hneg : AEStronglyMeasurable (fun x => -(g x i)) μ := hcoord.neg
    simpa only [F, Pi.neg_apply, HilbertVec.toVec_apply] using hneg
  · have hgmem : MemLp (fun x => -(g x)) (ENNReal.ofReal p) μ :=
      (Lp.memLp g).neg
    have hnorm : (fun x => vecEuclideanNorm (F x)) = fun x => ‖-(g x)‖ := by
      funext x
      rw [HilbertVec.norm_eq_vecEuclideanNorm]
      rfl
    rw [hnorm]
    exact hgmem.norm
  · intro u
    calc
      L u = J (A u) := (hJrep u).symm
      _ = ∫ x, inner ℝ (g x) (A u x) ∂μ := hgrep (A u)
      _ = -∫ x, vecDot (F x) ((A u x).toVec) ∂μ := by
        rw [← integral_neg]
        apply integral_congr_ae
        filter_upwards with x
        simp only [F, vecDot, Pi.neg_apply, neg_mul,
          Finset.sum_neg_distrib, neg_neg, PiLp.inner_apply,
          RCLike.inner_apply, conj_trivial, HilbertVec.toVec_apply]
        exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  · have hnorm : (fun x => vecEuclideanNorm (F x)) = fun x => ‖g x‖ := by
      funext x
      simp only [F, vecEuclideanNorm_neg]
      exact (HilbertVec.norm_eq_vecEuclideanNorm (g x)).symm
    rw [hnorm, eLpNorm_norm _ (Lp.aestronglyMeasurable g)]
    change ‖g‖ = ‖L‖
    exact hgnorm.trans hJnorm

end

end PDE
