module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# The Campanato characterization of Hölder spaces

Challenge: a function whose scaled mean oscillations on small balls are bounded has a Hölder
representative, and conversely, with one dimensional constant `C(d)`.

Conventions.  `ℝ^d` is modelled by `Vec d = Fin d → ℝ` with Lebesgue measure; the explicit
Euclidean norm and balls are defined below (the norm inherited by `Vec d` from Mathlib is the
supremum norm, and `Metric.ball` is never used).
-/

@[expose] public section

open scoped BigOperators ENNReal Topology

namespace PDE

open MeasureTheory Filter

/-- The native coordinate model of `ℝ^d`. -/
abbrev Vec (d : ℕ) := Fin d → ℝ


/-- The Euclidean dot product on `Vec d`. -/
def vecDot {d : ℕ} (x y : Vec d) : ℝ :=
  ∑ i, x i * y i


/-- The square of the Euclidean norm on `Vec d`. -/
def vecNormSq {d : ℕ} (x : Vec d) : ℝ :=
  vecDot x x


/-- The Euclidean norm on `Vec d`. -/
noncomputable def vecEuclideanNorm {d : ℕ} (x : Vec d) : ℝ :=
  Real.sqrt (vecNormSq x)


/-- The `i`th coordinate basis vector. -/
def basisVec {d : ℕ} (i : Fin d) : Vec d :=
  Pi.single i (1 : ℝ)


/-- Euclidean squared distance on `Vec d`. -/
def euclideanSqDist {d : ℕ} (x y : Vec d) : ℝ :=
  vecNormSq (x - y)


/-- The round Euclidean open ball of centre `x₀` and radius `R`. -/
def euclideanBall {d : ℕ} (x₀ : Vec d) (R : ℝ) : Set (Vec d) :=
  {x | euclideanSqDist x x₀ < R ^ 2}


/-- Lebesgue volume restricted to a domain `U`. -/
noncomputable abbrev volumeOn {d : ℕ} (U : Set (Vec d)) :=
  MeasureTheory.volume.restrict U


/-- The arithmetic integral average on `U`: `|U|⁻¹ ∫_U u`.  This is a total definition; its
mathematical meaning as an average requires `0 < |U| < ∞`. -/
noncomputable def integralAverage {d : ℕ}
    (U : Set (Vec d)) (u : Vec d → ℝ) : ℝ :=
  (volume U).toReal⁻¹ * ∫ x in U, u x ∂volume


/-- A Hölder-seminorm bound using the explicit Euclidean magnitude on `Vec d`, rather than its
inherited supremum norm. -/
def EuclideanHolderSeminormLE {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ)
    (α K : ℝ) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U,
    |u x - u y| ≤ K * vecEuclideanNorm (x - y) ^ α

/-- A Euclidean Hölder representative together with its a.e. agreement on the stated set. -/
def HasEuclideanHolderRepresentativeOn {d : ℕ}
    (U : Set (Vec d)) (u : Vec d → ℝ) (α K : ℝ) : Prop :=
  ∃ representative : Vec d → ℝ,
    representative =ᵐ[volumeOn U] u ∧
      EuclideanHolderSeminormLE U representative α K


/-- Campanato characterisation of Hölder spaces (Lemma 1.19).  Let
`A = sup_{x ∈ B_{1/2}} sup_{0<r<1/4} r^{-α} ⨍_{B_r(x)} |u - (u)_{B_r(x)}|`.
(1) `A ≤ K` gives a Hölder representative on `B_{1/2}` with seminorm `≤ C α⁻¹ K`
    (`C⁻¹ α [u]_{C^{0,α}(B_{1/2})} ≤ A`, with `[u]` of the representative);
(2) a Hölder representative on `B_1` with seminorm `≤ K` gives `A ≤ C K`.
One constant `C(d)`, chosen before `α` and `u`. -/
theorem exists_campanato_characterization_constant (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, 0 < α → α ≤ 1 →
      ∀ u : Vec d → ℝ, IntegrableOn u (euclideanBall (0 : Vec d) 1) →
        (∀ K : ℝ, 0 ≤ K →
          (∀ x ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ, 0 < r → r < 1 / 4 →
            r ^ (-α) * integralAverage (euclideanBall x r)
              (fun y => |u y - integralAverage (euclideanBall x r) u|) ≤ K) →
          HasEuclideanHolderRepresentativeOn (euclideanBall (0 : Vec d) (1 / 2)) u α
            (C * α⁻¹ * K)) ∧
        (∀ K : ℝ, 0 ≤ K →
          HasEuclideanHolderRepresentativeOn (euclideanBall (0 : Vec d) 1) u α K →
          ∀ x ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ, 0 < r → r < 1 / 4 →
            r ^ (-α) * integralAverage (euclideanBall x r)
              (fun y => |u y - integralAverage (euclideanBall x r) u|) ≤ C * K) := by
  sorry

end PDE
