module

public import PDEFoundation.Measure.LinearNormalizedVolume
public import PDEFoundation.Measure.AffineNormalizedVolume
public import PDEFoundation.Measure.EuclideanFieldMeasurability
public import PDEFoundation.Sobolev.Mean
public import PDEFoundation.Sobolev.W1p.Affine
public import PDEFoundation.Sobolev.W1p.LinearChange

/-!
# `W^{1,p}` under invertible affine maps

For `T x = e x + b` the pushforward `u ∘ T⁻¹` of a representative-level
`W^{1,p}` function on `U` is a `W^{1,p}` function on `T '' U` whose gradient is
`(e.symm)ᵀ (Du ∘ T⁻¹)`.  Normalized `L^q` norms and averages are invariant, and
Euclidean gradient bounds are controlled by the Euclidean operator bound of
`e.symm`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal Pointwise

namespace PDE

variable {d : ℕ}

/-- The affine image `T '' U` with `T x = e x + b` is the translate of `e '' U`. -/
theorem image_affine_eq_translateSet (e : Vec d ≃L[ℝ] Vec d) (b : Vec d)
    (U : Set (Vec d)) :
    (fun x => e x + b) '' U = translateSet b (e '' U) := by
  rw [← image_addRight_eq_translateSet, Set.image_image]

/-- The affine map `x ↦ e x + b` as a homeomorphism. -/
noncomputable def affineHomeomorph (e : Vec d ≃L[ℝ] Vec d) (b : Vec d) :
    Vec d ≃ₜ Vec d :=
  e.toHomeomorph.trans (Homeomorph.addRight b)

@[simp]
theorem affineHomeomorph_apply (e : Vec d ≃L[ℝ] Vec d) (b x : Vec d) :
    affineHomeomorph e b x = e x + b :=
  rfl

/-- Affine maps carry normalized volume on `U` to normalized volume on the image. -/
theorem measurePreserving_affine_normalizedVolumeOn (e : Vec d ≃L[ℝ] Vec d)
    (b : Vec d) (U : Set (Vec d)) :
    MeasurePreserving (fun x => e x + b) (normalizedVolumeOn U)
      (normalizedVolumeOn ((fun x => e x + b) '' U)) := by
  rw [image_affine_eq_translateSet]
  exact (measurePreserving_addRight_normalizedVolumeOn_translateSet b (e '' U)).comp
    (measurePreserving_linearEquiv_normalizedVolumeOn e U)

/-- Normalized `L^q` seminorms are invariant under affine pushforward. -/
theorem eLpMeanNormOn_comp_affine_symm {E : Type*} [NormedAddCommGroup E]
    (e : Vec d ≃L[ℝ] Vec d) (b : Vec d) (U : Set (Vec d)) (q : ℝ≥0∞)
    (f : Vec d → E) :
    eLpMeanNormOn ((fun x => e x + b) '' U) q (fun y => f (e.symm (y - b))) =
      eLpMeanNormOn U q f := by
  have hmp := measurePreserving_affine_normalizedVolumeOn e b U
  have hemb : MeasurableEmbedding (fun x => e x + b) :=
    (affineHomeomorph e b).measurableEmbedding
  unfold eLpMeanNormOn
  rw [← hmp.map_eq, hemb.eLpNorm_map_measure]
  congr 1
  funext x
  simp

/-- Normalized Euclidean gradient norms are invariant under affine pushforward
of the vector field (without applying any matrix). -/
theorem euclideanFieldELpMeanNormOn_comp_affine_symm
    (e : Vec d ≃L[ℝ] Vec d) (b : Vec d) (U : Set (Vec d)) (q : ℝ≥0∞)
    (F : Vec d → Vec d) :
    euclideanFieldELpMeanNormOn ((fun x => e x + b) '' U) q
        (fun y => F (e.symm (y - b))) =
      euclideanFieldELpMeanNormOn U q F :=
  eLpMeanNormOn_comp_affine_symm e b U q (fun x => vecEuclideanNorm (F x))

/-- Integral averages are invariant under affine pushforward. -/
theorem integralAverage_comp_affine_symm (e : Vec d ≃L[ℝ] Vec d) (b : Vec d)
    {U : Set (Vec d)} (hUpos : 0 < volume U) (hUtop : volume U < ∞)
    (f : Vec d → ℝ) :
    integralAverage ((fun x => e x + b) '' U) (fun y => f (e.symm (y - b))) =
      integralAverage U f := by
  rw [image_affine_eq_translateSet,
    integralAverage_comp_subRight_translateSet b (e '' U) (fun y => f (e.symm y))]
  have := integralAverage_comp_linearEquiv e hUpos hUtop (fun y => f (e.symm y))
  simpa using this.symm

namespace W1pFunction

variable {U : Set (Vec d)} {p : ℝ≥0∞}

/-- Push a representative-level Sobolev function forward along an invertible
linear map: `v = u ∘ e.symm`, `Dv = (e.symm)ᵀ (Du ∘ e.symm)`. -/
noncomputable def linearPush (hp : 1 ≤ p) (u : W1pFunction U p)
    (e : Vec d ≃L[ℝ] Vec d) : W1pFunction (e '' U) p where
  toFun y := u.toFun (e.symm y)
  grad y := transposeAction e.symm (u.grad (e.symm y))
  memLp := by
    have hset : e.symm '' (e '' U) = U := by
      rw [← Set.image_comp]; simp
    have := memLpOn_comp_linearEquiv e.symm (U := e '' U) (f := u.toFun)
      (by rw [hset]; exact u.memLp)
    exact this
  gradMemLp := by
    intro i
    have hset : e.symm '' (e '' U) = U := by
      rw [← Set.image_comp]; simp
    have hj : ∀ j, MemLp (fun y => u.grad (e.symm y) j) p (volumeOn (e '' U)) := by
      intro j
      exact memLpOn_comp_linearEquiv e.symm (U := e '' U) (f := fun x => u.grad x j)
        (by rw [hset]; exact u.gradMemLp j)
    have hsum := memLp_finsetSum' (Finset.univ : Finset (Fin d))
      (fun j _ => (hj j).const_mul ((e.symm (basisVec i)) j))
    convert hsum using 1
    funext y
    simp [transposeAction_apply, vecDot, mul_comm]
  hasWeakGradient :=
    u.hasWeakGradient.comp_linearEquiv_symm
      (u.memLp.locallyIntegrable hp) (fun j => (u.gradMemLp j).locallyIntegrable hp) e

/-- Transport a Sobolev function along an equality of domains. -/
def congrSet {V V' : Set (Vec d)} (h : V = V') (u : W1pFunction V p) :
    W1pFunction V' p := h ▸ u

@[simp]
theorem congrSet_toFun {V V' : Set (Vec d)} (h : V = V') (u : W1pFunction V p) :
    (u.congrSet h).toFun = u.toFun := by subst h; rfl

@[simp]
theorem congrSet_grad {V V' : Set (Vec d)} (h : V = V') (u : W1pFunction V p) :
    (u.congrSet h).grad = u.grad := by subst h; rfl

/-- Push a representative-level Sobolev function on `U` forward along the
invertible affine map `T x = e x + b`: `v = u ∘ T⁻¹` with
`Dv = (e.symm)ᵀ (Du ∘ T⁻¹)`. -/
noncomputable def affinePush (hp : 1 ≤ p) (u : W1pFunction U p)
    (e : Vec d ≃L[ℝ] Vec d) (b : Vec d) :
    W1pFunction ((fun x => e x + b) '' U) p :=
  ((u.linearPush hp e).translate b).congrSet (image_affine_eq_translateSet e b U).symm

@[simp]
theorem affinePush_toFun (hp : 1 ≤ p) (u : W1pFunction U p)
    (e : Vec d ≃L[ℝ] Vec d) (b y : Vec d) :
    (u.affinePush hp e b).toFun y = u.toFun (e.symm (y - b)) := by
  simp [affinePush, linearPush]

@[simp]
theorem affinePush_grad (hp : 1 ≤ p) (u : W1pFunction U p)
    (e : Vec d ≃L[ℝ] Vec d) (b y : Vec d) :
    (u.affinePush hp e b).grad y =
      transposeAction e.symm (u.grad (e.symm (y - b))) := by
  simp [affinePush, linearPush]

/-- Normalized `L^q` norm of the pushforward value equals that of `u`. -/
theorem eLpMeanNormOn_affinePush_toFun (hp : 1 ≤ p) (u : W1pFunction U p)
    (e : Vec d ≃L[ℝ] Vec d) (b : Vec d) (q : ℝ≥0∞) :
    eLpMeanNormOn ((fun x => e x + b) '' U) q (u.affinePush hp e b).toFun =
      eLpMeanNormOn U q u.toFun := by
  have hfun : (u.affinePush hp e b).toFun = fun y => u.toFun (e.symm (y - b)) :=
    funext (affinePush_toFun hp u e b)
  rw [hfun]
  exact eLpMeanNormOn_comp_affine_symm e b U q u.toFun

/-- Pointwise Euclidean bound on the pushed gradient. -/
theorem vecEuclideanNorm_affinePush_grad_le (hp : 1 ≤ p) (u : W1pFunction U p)
    (e : Vec d ≃L[ℝ] Vec d) (b : Vec d) {L : ℝ}
    (hL : ∀ z, vecEuclideanNorm (transposeAction e.symm z) ≤ L * vecEuclideanNorm z)
    (y : Vec d) :
    vecEuclideanNorm ((u.affinePush hp e b).grad y) ≤
      L * vecEuclideanNorm (u.grad (e.symm (y - b))) := by
  rw [affinePush_grad]; exact hL _

/-- The normalized Euclidean gradient norm of the pushforward is bounded by
`L` times that of `u`, when `L` bounds the Euclidean operator norm of the
transpose of `e.symm`. -/
theorem euclideanFieldELpMeanNormOn_affinePush_grad_le (hp : 1 ≤ p)
    (u : W1pFunction U p) (e : Vec d ≃L[ℝ] Vec d) (b : Vec d) {L : ℝ}
    (hL0 : 0 ≤ L)
    (hL : ∀ z, vecEuclideanNorm (transposeAction e.symm z) ≤ L * vecEuclideanNorm z) :
    euclideanFieldELpMeanNormOn ((fun x => e x + b) '' U) p (u.affinePush hp e b).grad ≤
      ENNReal.ofReal L * euclideanFieldELpMeanNormOn U p u.grad := by
  have h1 : euclideanFieldELpMeanNormOn ((fun x => e x + b) '' U) p
      (u.affinePush hp e b).grad ≤
      eLpMeanNormOn ((fun x => e x + b) '' U) p
        (fun y => L • vecEuclideanNorm (u.grad (e.symm (y - b)))) := by
    unfold euclideanFieldELpMeanNormOn eLpMeanNormOn
    have hmeas : AEStronglyMeasurable
        (fun y => vecEuclideanNorm ((u.affinePush hp e b).grad y))
        (normalizedVolumeOn ((fun x => e x + b) '' U)) :=
      aestronglyMeasurable_vecEuclideanNorm_of_coord fun i => by
        rw [normalizedVolumeOn]
        exact ((u.affinePush hp e b).gradMemLp i).aestronglyMeasurable.smul_measure _
    refine eLpNorm_mono_ae hmeas (Filter.Eventually.of_forall fun y => ?_)
    have := vecEuclideanNorm_affinePush_grad_le hp u e b hL y
    have hn := vecEuclideanNorm_nonneg (u.grad (e.symm (y - b)))
    rw [Real.norm_of_nonneg (vecEuclideanNorm_nonneg _),
      Real.norm_of_nonneg (by simpa [smul_eq_mul] using mul_nonneg hL0 hn)]
    simpa [smul_eq_mul] using this
  refine h1.trans ?_
  have h2 : eLpMeanNormOn ((fun x => e x + b) '' U) p
      (fun y => L • vecEuclideanNorm (u.grad (e.symm (y - b)))) =
      ENNReal.ofReal L * eLpMeanNormOn ((fun x => e x + b) '' U) p
        (fun y => vecEuclideanNorm (u.grad (e.symm (y - b)))) := by
    unfold eLpMeanNormOn
    have := eLpNorm_const_smul (μ := normalizedVolumeOn ((fun x => e x + b) '' U))
      (p := p) L (fun y => vecEuclideanNorm (u.grad (e.symm (y - b))))
    rw [show (fun y => L • vecEuclideanNorm (u.grad (e.symm (y - b)))) =
      L • (fun y => vecEuclideanNorm (u.grad (e.symm (y - b)))) from rfl, this,
      Real.enorm_eq_ofReal hL0]
  rw [h2]
  exact le_of_eq (by
    rw [euclideanFieldELpMeanNormOn]
    exact congrArg _ (eLpMeanNormOn_comp_affine_symm e b U p
      (fun x => vecEuclideanNorm (u.grad x))))

end W1pFunction

end PDE
