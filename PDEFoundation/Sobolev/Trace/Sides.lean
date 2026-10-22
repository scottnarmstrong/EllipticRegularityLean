module

public import PDEFoundation.Sobolev.Trace.Square
public import PDEFoundation.Sobolev.Trace.VectorErrorLimit

/-!
# Fixed traces on the sides of a square

Each theorem transfers enlarged-interval `L²` data to its actual closed side
and then applies the native-vector one-dimensional limit theorem.  The side
parameters are increasing Cartesian coordinates, so every displayed weak
derivative has the positive corresponding gradient coordinate.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open Filter MeasureTheory Set

noncomputable section

/-- The right-side canonical limit inherits continuity, its raw side value
almost everywhere, and the vertical coordinate of the raw gradient as weak
derivative. -/
theorem squareLoopRightUniformLimit_of_tendsto_sq_vector_error
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {x₀ : Vec 2} {r ρ : ℝ}
    (hρ : ρ ∈ Ioo r (2 * r))
    (hF : ∀ n, ContDiff ℝ 1 (F n))
    (hu : MemLp (squareLoopRightRestriction u x₀ ρ) 2
      (volume.restrict (Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r))))
    (hg : MemLp (squareLoopRightTangentialRestriction g x₀ ρ) 2
      (volume.restrict (Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r))))
    (hValueEnlarged : ∀ n, MemLp
      (fun t => squareLoopRightRestriction (F n) x₀ ρ t -
        squareLoopRightRestriction u x₀ ρ t) 2
      (volume.restrict (Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r))))
    (hGradientEnlarged : ∀ n, MemLp
      (fun t => vecEuclideanNorm
        (classicalGradient (F n) (squareLoopRightSide x₀ ρ t) -
          g (squareLoopRightSide x₀ ρ t))) 2
      (volume.restrict (Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r))))
    (hValue : Tendsto (fun n => ∫ t in Icc (x₀ 1 - ρ) (x₀ 1 + ρ),
      |squareLoopRightRestriction (F n) x₀ ρ t -
        squareLoopRightRestriction u x₀ ρ t| ^ 2) atTop (𝓝 0))
    (hGradient : Tendsto (fun n => ∫ t in Icc (x₀ 1 - ρ) (x₀ 1 + ρ),
      vecEuclideanNorm
        (classicalGradient (F n) (squareLoopRightSide x₀ ρ t) -
          g (squareLoopRightSide x₀ ρ t)) ^ 2) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun n => squareLoopRightRestriction (F n) x₀ ρ)
      (squareLoopRightUniformLimit F x₀ ρ) atTop
      (Icc (x₀ 1 - ρ) (x₀ 1 + ρ)) ∧
      ContinuousOn (squareLoopRightUniformLimit F x₀ ρ)
        (Icc (x₀ 1 - ρ) (x₀ 1 + ρ)) ∧
      squareLoopRightUniformLimit F x₀ ρ =ᵐ[
        volume.restrict (Icc (x₀ 1 - ρ) (x₀ 1 + ρ))]
        squareLoopRightRestriction u x₀ ρ ∧
      HasWeakDerivOnIoo (x₀ 1 - ρ) (x₀ 1 + ρ)
        (squareLoopRightUniformLimit F x₀ ρ)
        (squareLoopRightTangentialRestriction g x₀ ρ) := by
  change r < ρ ∧ ρ < 2 * r at hρ
  have hab : x₀ 1 - ρ < x₀ 1 + ρ := by linarith [hρ.1, hρ.2]
  have hactual : Icc (x₀ 1 - ρ) (x₀ 1 + ρ) ⊆
      Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r) := by
    intro t ht
    constructor <;> linarith [hρ.2, ht.1, ht.2]
  have hFRight : ∀ n, ContDiff ℝ 1
      (squareLoopRightRestriction (F n) x₀ ρ) := by
    intro n
    exact contDiff_squareLoopRightRestriction (hF n) x₀ ρ
  have huActual : MemLp (squareLoopRightRestriction u x₀ ρ) 2
      (volume.restrict (Icc (x₀ 1 - ρ) (x₀ 1 + ρ)) ) :=
    hu.mono_measure (Measure.restrict_mono hactual le_rfl)
  have hgActual : MemLp (squareLoopRightTangentialRestriction g x₀ ρ) 2
      (volume.restrict (Icc (x₀ 1 - ρ) (x₀ 1 + ρ)) ) :=
    hg.mono_measure (Measure.restrict_mono hactual le_rfl)
  have hValueActual : ∀ n, MemLp
      (fun t => squareLoopRightRestriction (F n) x₀ ρ t -
        squareLoopRightRestriction u x₀ ρ t) 2
      (volume.restrict (Icc (x₀ 1 - ρ) (x₀ 1 + ρ))) := by
    intro n
    exact (hValueEnlarged n).mono_measure
      (Measure.restrict_mono hactual le_rfl)
  have hGradientActual : ∀ n, MemLp
      (fun t => vecEuclideanNorm
        (classicalGradient (F n) (squareLoopRightSide x₀ ρ t) -
          g (squareLoopRightSide x₀ ρ t))) 2
      (volume.restrict (Icc (x₀ 1 - ρ) (x₀ 1 + ρ))) := by
    intro n
    exact (hGradientEnlarged n).mono_measure
      (Measure.restrict_mono hactual le_rfl)
  let E : ℕ → ℝ → Vec 2 := fun n t =>
    classicalGradient (F n) (squareLoopRightSide x₀ ρ t) -
      g (squareLoopRightSide x₀ ρ t)
  have hDerivativeError : ∀ n t,
      deriv (squareLoopRightRestriction (F n) x₀ ρ) t -
        squareLoopRightTangentialRestriction g x₀ ρ t = E n t 1 := by
    intro n t
    rw [deriv_squareLoopRightRestriction (hF n) x₀ ρ t]
    rfl
  change TendstoUniformlyOn (fun n => squareLoopRightRestriction (F n) x₀ ρ)
      (uniformCauchySeqLimit fun n => squareLoopRightRestriction (F n) x₀ ρ)
      atTop (Icc (x₀ 1 - ρ) (x₀ 1 + ρ)) ∧
      ContinuousOn (uniformCauchySeqLimit fun n =>
        squareLoopRightRestriction (F n) x₀ ρ) (Icc (x₀ 1 - ρ) (x₀ 1 + ρ)) ∧
      uniformCauchySeqLimit (fun n => squareLoopRightRestriction (F n) x₀ ρ) =ᵐ[
        volume.restrict (Icc (x₀ 1 - ρ) (x₀ 1 + ρ))]
        squareLoopRightRestriction u x₀ ρ ∧
      HasWeakDerivOnIoo (x₀ 1 - ρ) (x₀ 1 + ρ)
        (uniformCauchySeqLimit fun n => squareLoopRightRestriction (F n) x₀ ρ)
        (squareLoopRightTangentialRestriction g x₀ ρ)
  exact uniformCauchySeqLimit_hasWeakDerivOnIoo_of_tendsto_setIntegral_sq_vector_error
    (i := 1) hab hFRight huActual hgActual hValueActual hGradientActual
    hValue hGradient hDerivativeError

/-- The left-side canonical limit inherits continuity, its raw side value
almost everywhere, and the vertical coordinate of the raw gradient as weak
derivative. -/
theorem squareLoopLeftUniformLimit_of_tendsto_sq_vector_error
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {x₀ : Vec 2} {r ρ : ℝ}
    (hρ : ρ ∈ Ioo r (2 * r))
    (hF : ∀ n, ContDiff ℝ 1 (F n))
    (hu : MemLp (squareLoopLeftRestriction u x₀ ρ) 2
      (volume.restrict (Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r))))
    (hg : MemLp (squareLoopLeftTangentialRestriction g x₀ ρ) 2
      (volume.restrict (Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r))))
    (hValueEnlarged : ∀ n, MemLp
      (fun t => squareLoopLeftRestriction (F n) x₀ ρ t -
        squareLoopLeftRestriction u x₀ ρ t) 2
      (volume.restrict (Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r))))
    (hGradientEnlarged : ∀ n, MemLp
      (fun t => vecEuclideanNorm
        (classicalGradient (F n) (squareLoopLeftSide x₀ ρ t) -
          g (squareLoopLeftSide x₀ ρ t))) 2
      (volume.restrict (Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r))))
    (hValue : Tendsto (fun n => ∫ t in Icc (x₀ 1 - ρ) (x₀ 1 + ρ),
      |squareLoopLeftRestriction (F n) x₀ ρ t -
        squareLoopLeftRestriction u x₀ ρ t| ^ 2) atTop (𝓝 0))
    (hGradient : Tendsto (fun n => ∫ t in Icc (x₀ 1 - ρ) (x₀ 1 + ρ),
      vecEuclideanNorm
        (classicalGradient (F n) (squareLoopLeftSide x₀ ρ t) -
          g (squareLoopLeftSide x₀ ρ t)) ^ 2) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun n => squareLoopLeftRestriction (F n) x₀ ρ)
      (squareLoopLeftUniformLimit F x₀ ρ) atTop
      (Icc (x₀ 1 - ρ) (x₀ 1 + ρ)) ∧
      ContinuousOn (squareLoopLeftUniformLimit F x₀ ρ)
        (Icc (x₀ 1 - ρ) (x₀ 1 + ρ)) ∧
      squareLoopLeftUniformLimit F x₀ ρ =ᵐ[
        volume.restrict (Icc (x₀ 1 - ρ) (x₀ 1 + ρ))]
        squareLoopLeftRestriction u x₀ ρ ∧
      HasWeakDerivOnIoo (x₀ 1 - ρ) (x₀ 1 + ρ)
        (squareLoopLeftUniformLimit F x₀ ρ)
        (squareLoopLeftTangentialRestriction g x₀ ρ) := by
  change r < ρ ∧ ρ < 2 * r at hρ
  have hab : x₀ 1 - ρ < x₀ 1 + ρ := by linarith [hρ.1, hρ.2]
  have hactual : Icc (x₀ 1 - ρ) (x₀ 1 + ρ) ⊆
      Ioo (x₀ 1 - 2 * r) (x₀ 1 + 2 * r) := by
    intro t ht
    constructor <;> linarith [hρ.2, ht.1, ht.2]
  have hFLeft : ∀ n, ContDiff ℝ 1
      (squareLoopLeftRestriction (F n) x₀ ρ) := by
    intro n
    exact contDiff_squareLoopLeftRestriction (hF n) x₀ ρ
  have huActual : MemLp (squareLoopLeftRestriction u x₀ ρ) 2
      (volume.restrict (Icc (x₀ 1 - ρ) (x₀ 1 + ρ))) :=
    hu.mono_measure (Measure.restrict_mono hactual le_rfl)
  have hgActual : MemLp (squareLoopLeftTangentialRestriction g x₀ ρ) 2
      (volume.restrict (Icc (x₀ 1 - ρ) (x₀ 1 + ρ))) :=
    hg.mono_measure (Measure.restrict_mono hactual le_rfl)
  have hValueActual : ∀ n, MemLp
      (fun t => squareLoopLeftRestriction (F n) x₀ ρ t -
        squareLoopLeftRestriction u x₀ ρ t) 2
      (volume.restrict (Icc (x₀ 1 - ρ) (x₀ 1 + ρ))) := by
    intro n
    exact (hValueEnlarged n).mono_measure
      (Measure.restrict_mono hactual le_rfl)
  have hGradientActual : ∀ n, MemLp
      (fun t => vecEuclideanNorm
        (classicalGradient (F n) (squareLoopLeftSide x₀ ρ t) -
          g (squareLoopLeftSide x₀ ρ t))) 2
      (volume.restrict (Icc (x₀ 1 - ρ) (x₀ 1 + ρ))) := by
    intro n
    exact (hGradientEnlarged n).mono_measure
      (Measure.restrict_mono hactual le_rfl)
  let E : ℕ → ℝ → Vec 2 := fun n t =>
    classicalGradient (F n) (squareLoopLeftSide x₀ ρ t) -
      g (squareLoopLeftSide x₀ ρ t)
  have hDerivativeError : ∀ n t,
      deriv (squareLoopLeftRestriction (F n) x₀ ρ) t -
        squareLoopLeftTangentialRestriction g x₀ ρ t = E n t 1 := by
    intro n t
    rw [deriv_squareLoopLeftRestriction (hF n) x₀ ρ t]
    rfl
  change TendstoUniformlyOn (fun n => squareLoopLeftRestriction (F n) x₀ ρ)
      (uniformCauchySeqLimit fun n => squareLoopLeftRestriction (F n) x₀ ρ)
      atTop (Icc (x₀ 1 - ρ) (x₀ 1 + ρ)) ∧
      ContinuousOn (uniformCauchySeqLimit fun n =>
        squareLoopLeftRestriction (F n) x₀ ρ) (Icc (x₀ 1 - ρ) (x₀ 1 + ρ)) ∧
      uniformCauchySeqLimit (fun n => squareLoopLeftRestriction (F n) x₀ ρ) =ᵐ[
        volume.restrict (Icc (x₀ 1 - ρ) (x₀ 1 + ρ))]
        squareLoopLeftRestriction u x₀ ρ ∧
      HasWeakDerivOnIoo (x₀ 1 - ρ) (x₀ 1 + ρ)
        (uniformCauchySeqLimit fun n => squareLoopLeftRestriction (F n) x₀ ρ)
        (squareLoopLeftTangentialRestriction g x₀ ρ)
  exact uniformCauchySeqLimit_hasWeakDerivOnIoo_of_tendsto_setIntegral_sq_vector_error
    (i := 1) hab hFLeft huActual hgActual hValueActual hGradientActual
    hValue hGradient hDerivativeError

/-- The top-side canonical limit inherits continuity, its raw side value
almost everywhere, and the horizontal coordinate of the raw gradient as weak
derivative. -/
theorem squareLoopTopUniformLimit_of_tendsto_sq_vector_error
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {x₀ : Vec 2} {r ρ : ℝ}
    (hρ : ρ ∈ Ioo r (2 * r))
    (hF : ∀ n, ContDiff ℝ 1 (F n))
    (hu : MemLp (squareLoopTopRestriction u x₀ ρ) 2
      (volume.restrict (Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r))))
    (hg : MemLp (squareLoopTopTangentialRestriction g x₀ ρ) 2
      (volume.restrict (Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r))))
    (hValueEnlarged : ∀ n, MemLp
      (fun t => squareLoopTopRestriction (F n) x₀ ρ t -
        squareLoopTopRestriction u x₀ ρ t) 2
      (volume.restrict (Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r))))
    (hGradientEnlarged : ∀ n, MemLp
      (fun t => vecEuclideanNorm
        (classicalGradient (F n) (squareLoopTopSide x₀ ρ t) -
          g (squareLoopTopSide x₀ ρ t))) 2
      (volume.restrict (Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r))))
    (hValue : Tendsto (fun n => ∫ t in Icc (x₀ 0 - ρ) (x₀ 0 + ρ),
      |squareLoopTopRestriction (F n) x₀ ρ t -
        squareLoopTopRestriction u x₀ ρ t| ^ 2) atTop (𝓝 0))
    (hGradient : Tendsto (fun n => ∫ t in Icc (x₀ 0 - ρ) (x₀ 0 + ρ),
      vecEuclideanNorm
        (classicalGradient (F n) (squareLoopTopSide x₀ ρ t) -
          g (squareLoopTopSide x₀ ρ t)) ^ 2) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun n => squareLoopTopRestriction (F n) x₀ ρ)
      (squareLoopTopUniformLimit F x₀ ρ) atTop
      (Icc (x₀ 0 - ρ) (x₀ 0 + ρ)) ∧
      ContinuousOn (squareLoopTopUniformLimit F x₀ ρ)
        (Icc (x₀ 0 - ρ) (x₀ 0 + ρ)) ∧
      squareLoopTopUniformLimit F x₀ ρ =ᵐ[
        volume.restrict (Icc (x₀ 0 - ρ) (x₀ 0 + ρ))]
        squareLoopTopRestriction u x₀ ρ ∧
      HasWeakDerivOnIoo (x₀ 0 - ρ) (x₀ 0 + ρ)
        (squareLoopTopUniformLimit F x₀ ρ)
        (squareLoopTopTangentialRestriction g x₀ ρ) := by
  change r < ρ ∧ ρ < 2 * r at hρ
  have hab : x₀ 0 - ρ < x₀ 0 + ρ := by linarith [hρ.1, hρ.2]
  have hactual : Icc (x₀ 0 - ρ) (x₀ 0 + ρ) ⊆
      Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r) := by
    intro t ht
    constructor <;> linarith [hρ.2, ht.1, ht.2]
  have hFTop : ∀ n, ContDiff ℝ 1
      (squareLoopTopRestriction (F n) x₀ ρ) := by
    intro n
    exact contDiff_squareLoopTopRestriction (hF n) x₀ ρ
  have huActual : MemLp (squareLoopTopRestriction u x₀ ρ) 2
      (volume.restrict (Icc (x₀ 0 - ρ) (x₀ 0 + ρ))) :=
    hu.mono_measure (Measure.restrict_mono hactual le_rfl)
  have hgActual : MemLp (squareLoopTopTangentialRestriction g x₀ ρ) 2
      (volume.restrict (Icc (x₀ 0 - ρ) (x₀ 0 + ρ))) :=
    hg.mono_measure (Measure.restrict_mono hactual le_rfl)
  have hValueActual : ∀ n, MemLp
      (fun t => squareLoopTopRestriction (F n) x₀ ρ t -
        squareLoopTopRestriction u x₀ ρ t) 2
      (volume.restrict (Icc (x₀ 0 - ρ) (x₀ 0 + ρ))) := by
    intro n
    exact (hValueEnlarged n).mono_measure
      (Measure.restrict_mono hactual le_rfl)
  have hGradientActual : ∀ n, MemLp
      (fun t => vecEuclideanNorm
        (classicalGradient (F n) (squareLoopTopSide x₀ ρ t) -
          g (squareLoopTopSide x₀ ρ t))) 2
      (volume.restrict (Icc (x₀ 0 - ρ) (x₀ 0 + ρ))) := by
    intro n
    exact (hGradientEnlarged n).mono_measure
      (Measure.restrict_mono hactual le_rfl)
  let E : ℕ → ℝ → Vec 2 := fun n t =>
    classicalGradient (F n) (squareLoopTopSide x₀ ρ t) -
      g (squareLoopTopSide x₀ ρ t)
  have hDerivativeError : ∀ n t,
      deriv (squareLoopTopRestriction (F n) x₀ ρ) t -
        squareLoopTopTangentialRestriction g x₀ ρ t = E n t 0 := by
    intro n t
    rw [deriv_squareLoopTopRestriction (hF n) x₀ ρ t]
    rfl
  change TendstoUniformlyOn (fun n => squareLoopTopRestriction (F n) x₀ ρ)
      (uniformCauchySeqLimit fun n => squareLoopTopRestriction (F n) x₀ ρ)
      atTop (Icc (x₀ 0 - ρ) (x₀ 0 + ρ)) ∧
      ContinuousOn (uniformCauchySeqLimit fun n =>
        squareLoopTopRestriction (F n) x₀ ρ) (Icc (x₀ 0 - ρ) (x₀ 0 + ρ)) ∧
      uniformCauchySeqLimit (fun n => squareLoopTopRestriction (F n) x₀ ρ) =ᵐ[
        volume.restrict (Icc (x₀ 0 - ρ) (x₀ 0 + ρ))]
        squareLoopTopRestriction u x₀ ρ ∧
      HasWeakDerivOnIoo (x₀ 0 - ρ) (x₀ 0 + ρ)
        (uniformCauchySeqLimit fun n => squareLoopTopRestriction (F n) x₀ ρ)
        (squareLoopTopTangentialRestriction g x₀ ρ)
  exact uniformCauchySeqLimit_hasWeakDerivOnIoo_of_tendsto_setIntegral_sq_vector_error
    (i := 0) hab hFTop huActual hgActual hValueActual hGradientActual
    hValue hGradient hDerivativeError

/-- The bottom-side canonical limit inherits continuity, its raw side value
almost everywhere, and the horizontal coordinate of the raw gradient as weak
derivative. -/
theorem squareLoopBottomUniformLimit_of_tendsto_sq_vector_error
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {x₀ : Vec 2} {r ρ : ℝ}
    (hρ : ρ ∈ Ioo r (2 * r))
    (hF : ∀ n, ContDiff ℝ 1 (F n))
    (hu : MemLp (squareLoopBottomRestriction u x₀ ρ) 2
      (volume.restrict (Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r))))
    (hg : MemLp (squareLoopBottomTangentialRestriction g x₀ ρ) 2
      (volume.restrict (Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r))))
    (hValueEnlarged : ∀ n, MemLp
      (fun t => squareLoopBottomRestriction (F n) x₀ ρ t -
        squareLoopBottomRestriction u x₀ ρ t) 2
      (volume.restrict (Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r))))
    (hGradientEnlarged : ∀ n, MemLp
      (fun t => vecEuclideanNorm
        (classicalGradient (F n) (squareLoopBottomSide x₀ ρ t) -
          g (squareLoopBottomSide x₀ ρ t))) 2
      (volume.restrict (Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r))))
    (hValue : Tendsto (fun n => ∫ t in Icc (x₀ 0 - ρ) (x₀ 0 + ρ),
      |squareLoopBottomRestriction (F n) x₀ ρ t -
        squareLoopBottomRestriction u x₀ ρ t| ^ 2) atTop (𝓝 0))
    (hGradient : Tendsto (fun n => ∫ t in Icc (x₀ 0 - ρ) (x₀ 0 + ρ),
      vecEuclideanNorm
        (classicalGradient (F n) (squareLoopBottomSide x₀ ρ t) -
          g (squareLoopBottomSide x₀ ρ t)) ^ 2) atTop (𝓝 0)) :
    TendstoUniformlyOn (fun n => squareLoopBottomRestriction (F n) x₀ ρ)
      (squareLoopBottomUniformLimit F x₀ ρ) atTop
      (Icc (x₀ 0 - ρ) (x₀ 0 + ρ)) ∧
      ContinuousOn (squareLoopBottomUniformLimit F x₀ ρ)
        (Icc (x₀ 0 - ρ) (x₀ 0 + ρ)) ∧
      squareLoopBottomUniformLimit F x₀ ρ =ᵐ[
        volume.restrict (Icc (x₀ 0 - ρ) (x₀ 0 + ρ))]
        squareLoopBottomRestriction u x₀ ρ ∧
      HasWeakDerivOnIoo (x₀ 0 - ρ) (x₀ 0 + ρ)
        (squareLoopBottomUniformLimit F x₀ ρ)
        (squareLoopBottomTangentialRestriction g x₀ ρ) := by
  change r < ρ ∧ ρ < 2 * r at hρ
  have hab : x₀ 0 - ρ < x₀ 0 + ρ := by linarith [hρ.1, hρ.2]
  have hactual : Icc (x₀ 0 - ρ) (x₀ 0 + ρ) ⊆
      Ioo (x₀ 0 - 2 * r) (x₀ 0 + 2 * r) := by
    intro t ht
    constructor <;> linarith [hρ.2, ht.1, ht.2]
  have hFBottom : ∀ n, ContDiff ℝ 1
      (squareLoopBottomRestriction (F n) x₀ ρ) := by
    intro n
    exact contDiff_squareLoopBottomRestriction (hF n) x₀ ρ
  have huActual : MemLp (squareLoopBottomRestriction u x₀ ρ) 2
      (volume.restrict (Icc (x₀ 0 - ρ) (x₀ 0 + ρ))) :=
    hu.mono_measure (Measure.restrict_mono hactual le_rfl)
  have hgActual : MemLp (squareLoopBottomTangentialRestriction g x₀ ρ) 2
      (volume.restrict (Icc (x₀ 0 - ρ) (x₀ 0 + ρ))) :=
    hg.mono_measure (Measure.restrict_mono hactual le_rfl)
  have hValueActual : ∀ n, MemLp
      (fun t => squareLoopBottomRestriction (F n) x₀ ρ t -
        squareLoopBottomRestriction u x₀ ρ t) 2
      (volume.restrict (Icc (x₀ 0 - ρ) (x₀ 0 + ρ))) := by
    intro n
    exact (hValueEnlarged n).mono_measure
      (Measure.restrict_mono hactual le_rfl)
  have hGradientActual : ∀ n, MemLp
      (fun t => vecEuclideanNorm
        (classicalGradient (F n) (squareLoopBottomSide x₀ ρ t) -
          g (squareLoopBottomSide x₀ ρ t))) 2
      (volume.restrict (Icc (x₀ 0 - ρ) (x₀ 0 + ρ))) := by
    intro n
    exact (hGradientEnlarged n).mono_measure
      (Measure.restrict_mono hactual le_rfl)
  let E : ℕ → ℝ → Vec 2 := fun n t =>
    classicalGradient (F n) (squareLoopBottomSide x₀ ρ t) -
      g (squareLoopBottomSide x₀ ρ t)
  have hDerivativeError : ∀ n t,
      deriv (squareLoopBottomRestriction (F n) x₀ ρ) t -
        squareLoopBottomTangentialRestriction g x₀ ρ t = E n t 0 := by
    intro n t
    rw [deriv_squareLoopBottomRestriction (hF n) x₀ ρ t]
    rfl
  change TendstoUniformlyOn (fun n => squareLoopBottomRestriction (F n) x₀ ρ)
      (uniformCauchySeqLimit fun n => squareLoopBottomRestriction (F n) x₀ ρ)
      atTop (Icc (x₀ 0 - ρ) (x₀ 0 + ρ)) ∧
      ContinuousOn (uniformCauchySeqLimit fun n =>
        squareLoopBottomRestriction (F n) x₀ ρ) (Icc (x₀ 0 - ρ) (x₀ 0 + ρ)) ∧
      uniformCauchySeqLimit (fun n => squareLoopBottomRestriction (F n) x₀ ρ) =ᵐ[
        volume.restrict (Icc (x₀ 0 - ρ) (x₀ 0 + ρ))]
        squareLoopBottomRestriction u x₀ ρ ∧
      HasWeakDerivOnIoo (x₀ 0 - ρ) (x₀ 0 + ρ)
        (uniformCauchySeqLimit fun n => squareLoopBottomRestriction (F n) x₀ ρ)
        (squareLoopBottomTangentialRestriction g x₀ ρ)
  exact uniformCauchySeqLimit_hasWeakDerivOnIoo_of_tendsto_setIntegral_sq_vector_error
    (i := 0) hab hFBottom huActual hgActual hValueActual hGradientActual
    hValue hGradient hDerivativeError

end

end PDE
