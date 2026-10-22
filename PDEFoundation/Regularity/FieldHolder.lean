module

public import PDEFoundation.Regularity.Holder
public import PDEFoundation.Ambient.MatrixPerturbation
public import PDEFoundation.Ambient.CoefficientField

/-!
# Euclidean Hölder bounds for vector and matrix fields

The vector target uses its explicit Euclidean magnitude, and the matrix
target uses its Euclidean operator action. The inherited product norms do
not enter these definitions.
-/

@[expose] public section

namespace PDE

variable {d k : ℕ}

/-- The literal Euclidean Hölder-seminorm bound for a native vector field. -/
def EuclideanFieldHolderSeminormLE (U : Set (Vec d)) (F : Vec d → Vec k)
    (α K : ℝ) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U,
    vecEuclideanNorm (F x - F y) ≤ K * vecEuclideanNorm (x - y) ^ α

/-- The literal Hölder bound in Euclidean matrix operator norm. -/
def EuclideanMatrixHolderSeminormLE (U : Set (Vec d)) (a : CoeffField d)
    (α K : ℝ) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U,
    IsMatrixPerturbationLE (K * vecEuclideanNorm (x - y) ^ α) (a x) (a y)

theorem EuclideanFieldHolderSeminormLE.coordinate
    {U : Set (Vec d)} {F : Vec d → Vec k} {α K : ℝ}
    (h : EuclideanFieldHolderSeminormLE U F α K) (i : Fin k) :
    EuclideanHolderSeminormLE U (fun x => F x i) α K := by
  intro x hx y hy
  exact (abs_apply_le_vecEuclideanNorm (F x - F y) i).trans (h x hx y hy)

/-- Coordinate Hölder bounds reconstruct a vector bound with explicit
dimension dependence. -/
theorem euclideanFieldHolderSeminormLE_of_coordinates
    {U : Set (Vec d)} {F : Vec d → Vec k} {α K : ℝ}
    (h : ∀ i, EuclideanHolderSeminormLE U (fun x => F x i) α K) :
    EuclideanFieldHolderSeminormLE U F α ((k : ℝ) * K) := by
  intro x hx y hy
  calc
    vecEuclideanNorm (F x - F y) ≤ ∑ i : Fin k, |F x i - F y i| :=
      vecEuclideanNorm_le_sum_abs (F x - F y)
    _ ≤ ∑ _i : Fin k, K * vecEuclideanNorm (x - y) ^ α :=
      Finset.sum_le_sum (fun i _ => h i x hx y hy)
    _ = ((k : ℝ) * K) * vecEuclideanNorm (x - y) ^ α := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

theorem EuclideanFieldHolderSeminormLE.continuousOn
    {U : Set (Vec d)} {F : Vec d → Vec k} {α K : ℝ}
    (h : EuclideanFieldHolderSeminormLE U F α K)
    (hα : 0 < α) (hK : 0 ≤ K) :
    ContinuousOn F U := by
  apply continuousOn_pi.mpr
  intro i
  exact (h.coordinate i).continuousOn hα hK

theorem EuclideanFieldHolderSeminormLE.mono_set
    {U V : Set (Vec d)} {F : Vec d → Vec k} {α K : ℝ}
    (h : EuclideanFieldHolderSeminormLE U F α K) (hVU : V ⊆ U) :
    EuclideanFieldHolderSeminormLE V F α K :=
  fun x hx y hy => h x (hVU hx) y (hVU hy)

theorem EuclideanMatrixHolderSeminormLE.coordinate
    {U : Set (Vec d)} {a : CoeffField d} {α K : ℝ}
    (h : EuclideanMatrixHolderSeminormLE U a α K) (i j : Fin d) :
    EuclideanHolderSeminormLE U (fun x => a x i j) α K := by
  intro x hx y hy
  have hb := h x hx y hy (basisVec j)
  rw [vecEuclideanNorm_basisVec, mul_one] at hb
  have hcoord : matVecMul (a x - a y) (basisVec j) i = a x i j - a y i j := by
    change (a x - a y).mulVec (Pi.single j 1) i = _
    simp [Matrix.mulVec_single, Matrix.col]
  calc
    |a x i j - a y i j| = |matVecMul (a x - a y) (basisVec j) i| := by rw [hcoord]
    _ ≤ vecEuclideanNorm (matVecMul (a x - a y) (basisVec j)) :=
      abs_apply_le_vecEuclideanNorm _ i
    _ ≤ K * vecEuclideanNorm (x - y) ^ α := hb

theorem EuclideanMatrixHolderSeminormLE.continuousOn
    {U : Set (Vec d)} {a : CoeffField d} {α K : ℝ}
    (h : EuclideanMatrixHolderSeminormLE U a α K)
    (hα : 0 < α) (hK : 0 ≤ K) :
    ContinuousOn a U := by
  apply continuousOn_pi.mpr
  intro i
  apply continuousOn_pi.mpr
  intro j
  exact (h.coordinate i j).continuousOn hα hK

end PDE
