module

public import PDEFoundation.Regularity.FieldHolder

/-!
# Literal Euclidean Hölder seminorms for fields

The definitions in this file take the infimum over all certified nonnegative
Hölder constants.  A finiteness witness is an explicit argument, so the real
infimum is never applied as a fallback value for a non-Hölder field.
-/

@[expose] public section

namespace PDE

noncomputable section

variable {d k : ℕ}

/-- The least nonnegative Euclidean Hölder constant of a native vector field,
on the explicitly certified finite-Hölder carrier. -/
noncomputable def euclideanFieldHolderSeminormOn
    (U : Set (Vec d)) (F : Vec d → Vec k) (alpha : ℝ)
    (_hHolder : ∃ K : ℝ, 0 ≤ K ∧ EuclideanFieldHolderSeminormLE U F alpha K) : ℝ :=
  sInf {K : ℝ | 0 ≤ K ∧ EuclideanFieldHolderSeminormLE U F alpha K}

private theorem fieldHolderConstants_nonempty
    {U : Set (Vec d)} {F : Vec d → Vec k} {alpha : ℝ}
    (hHolder : ∃ K : ℝ, 0 ≤ K ∧ EuclideanFieldHolderSeminormLE U F alpha K) :
    {K : ℝ | 0 ≤ K ∧ EuclideanFieldHolderSeminormLE U F alpha K}.Nonempty :=
  hHolder

private theorem fieldHolderConstants_bddBelow
    {U : Set (Vec d)} {F : Vec d → Vec k} {alpha : ℝ} :
    BddBelow {K : ℝ | 0 ≤ K ∧ EuclideanFieldHolderSeminormLE U F alpha K} :=
  ⟨0, fun _ hK => hK.1⟩

theorem euclideanFieldHolderSeminormOn_nonneg
    {U : Set (Vec d)} {F : Vec d → Vec k} {alpha : ℝ}
    (hHolder : ∃ K : ℝ, 0 ≤ K ∧ EuclideanFieldHolderSeminormLE U F alpha K) :
    0 ≤ euclideanFieldHolderSeminormOn U F alpha hHolder := by
  apply le_csInf (fieldHolderConstants_nonempty hHolder)
  intro K hK
  exact hK.1

theorem euclideanFieldHolderSeminormOn_le
    {U : Set (Vec d)} {F : Vec d → Vec k} {alpha K : ℝ}
    (hHolder : ∃ C : ℝ, 0 ≤ C ∧ EuclideanFieldHolderSeminormLE U F alpha C)
    (hK : 0 ≤ K) (hFK : EuclideanFieldHolderSeminormLE U F alpha K) :
    euclideanFieldHolderSeminormOn U F alpha hHolder ≤ K := by
  exact csInf_le fieldHolderConstants_bddBelow ⟨hK, hFK⟩

theorem euclideanFieldHolderSeminormOn_bound
    {U : Set (Vec d)} {F : Vec d → Vec k} {alpha : ℝ}
    (hHolder : ∃ K : ℝ, 0 ≤ K ∧ EuclideanFieldHolderSeminormLE U F alpha K) :
    EuclideanFieldHolderSeminormLE U F alpha
      (euclideanFieldHolderSeminormOn U F alpha hHolder) := by
  intro x hx y hy
  by_cases hxy : x = y
  · subst y
    rw [sub_self]
    have hzero : vecEuclideanNorm (0 : Vec k) = 0 :=
      vecEuclideanNorm_eq_zero_iff.mpr rfl
    rw [hzero]
    exact mul_nonneg (euclideanFieldHolderSeminormOn_nonneg hHolder)
      (Real.rpow_nonneg (vecEuclideanNorm_nonneg (x - x)) alpha)
  · have hbase : 0 < vecEuclideanNorm (x - y) ^ alpha :=
      Real.rpow_pos_of_pos ((vecEuclideanNorm_pos_iff.mpr (sub_ne_zero.mpr hxy))) alpha
    have hquot :
        vecEuclideanNorm (F x - F y) / vecEuclideanNorm (x - y) ^ alpha ≤
          euclideanFieldHolderSeminormOn U F alpha hHolder := by
      apply le_csInf (fieldHolderConstants_nonempty hHolder)
      intro K hK
      exact (div_le_iff₀ hbase).2 (hK.2 x hx y hy)
    exact (div_le_iff₀ hbase).1 hquot

theorem euclideanFieldHolderSeminormOn_isLeast
    {U : Set (Vec d)} {F : Vec d → Vec k} {alpha : ℝ}
    (hHolder : ∃ K : ℝ, 0 ≤ K ∧ EuclideanFieldHolderSeminormLE U F alpha K) :
    IsLeast {K : ℝ | 0 ≤ K ∧ EuclideanFieldHolderSeminormLE U F alpha K}
      (euclideanFieldHolderSeminormOn U F alpha hHolder) :=
  ⟨⟨euclideanFieldHolderSeminormOn_nonneg hHolder,
      euclideanFieldHolderSeminormOn_bound hHolder⟩,
    fun _K hK => euclideanFieldHolderSeminormOn_le hHolder hK.1 hK.2⟩

theorem euclideanFieldHolderSeminormOn_le_iff
    {U : Set (Vec d)} {F : Vec d → Vec k} {alpha K : ℝ}
    (hHolder : ∃ C : ℝ, 0 ≤ C ∧ EuclideanFieldHolderSeminormLE U F alpha C)
    (hK : 0 ≤ K) :
    euclideanFieldHolderSeminormOn U F alpha hHolder ≤ K ↔
      EuclideanFieldHolderSeminormLE U F alpha K := by
  constructor
  · intro h x hx y hy
    exact (euclideanFieldHolderSeminormOn_bound hHolder x hx y hy).trans <|
      mul_le_mul_of_nonneg_right h
        (Real.rpow_nonneg (vecEuclideanNorm_nonneg (x - y)) alpha)
  · exact euclideanFieldHolderSeminormOn_le hHolder hK

theorem euclideanFieldHolderSeminormOn_proof_irrel
    {U : Set (Vec d)} {F : Vec d → Vec k} {alpha : ℝ}
    (hHolder hHolder' :
      ∃ K : ℝ, 0 ≤ K ∧ EuclideanFieldHolderSeminormLE U F alpha K) :
    euclideanFieldHolderSeminormOn U F alpha hHolder =
      euclideanFieldHolderSeminormOn U F alpha hHolder' := by
  rfl

/-- The least nonnegative Euclidean operator Hölder constant of a native
matrix field, on the explicitly certified finite-Hölder carrier. -/
noncomputable def euclideanMatrixHolderSeminormOn
    (U : Set (Vec d)) (a : CoeffField d) (alpha : ℝ)
    (_hHolder : ∃ K : ℝ, 0 ≤ K ∧ EuclideanMatrixHolderSeminormLE U a alpha K) : ℝ :=
  sInf {K : ℝ | 0 ≤ K ∧ EuclideanMatrixHolderSeminormLE U a alpha K}

private theorem matrixHolderConstants_nonempty
    {U : Set (Vec d)} {a : CoeffField d} {alpha : ℝ}
    (hHolder : ∃ K : ℝ, 0 ≤ K ∧ EuclideanMatrixHolderSeminormLE U a alpha K) :
    {K : ℝ | 0 ≤ K ∧ EuclideanMatrixHolderSeminormLE U a alpha K}.Nonempty :=
  hHolder

private theorem matrixHolderConstants_bddBelow
    {U : Set (Vec d)} {a : CoeffField d} {alpha : ℝ} :
    BddBelow {K : ℝ | 0 ≤ K ∧ EuclideanMatrixHolderSeminormLE U a alpha K} :=
  ⟨0, fun _ hK => hK.1⟩

theorem euclideanMatrixHolderSeminormOn_nonneg
    {U : Set (Vec d)} {a : CoeffField d} {alpha : ℝ}
    (hHolder : ∃ K : ℝ, 0 ≤ K ∧ EuclideanMatrixHolderSeminormLE U a alpha K) :
    0 ≤ euclideanMatrixHolderSeminormOn U a alpha hHolder := by
  apply le_csInf (matrixHolderConstants_nonempty hHolder)
  intro K hK
  exact hK.1

theorem euclideanMatrixHolderSeminormOn_le
    {U : Set (Vec d)} {a : CoeffField d} {alpha K : ℝ}
    (hHolder : ∃ C : ℝ, 0 ≤ C ∧ EuclideanMatrixHolderSeminormLE U a alpha C)
    (hK : 0 ≤ K) (haK : EuclideanMatrixHolderSeminormLE U a alpha K) :
    euclideanMatrixHolderSeminormOn U a alpha hHolder ≤ K := by
  exact csInf_le matrixHolderConstants_bddBelow ⟨hK, haK⟩

theorem euclideanMatrixHolderSeminormOn_bound
    {U : Set (Vec d)} {a : CoeffField d} {alpha : ℝ}
    (hHolder : ∃ K : ℝ, 0 ≤ K ∧ EuclideanMatrixHolderSeminormLE U a alpha K) :
    EuclideanMatrixHolderSeminormLE U a alpha
      (euclideanMatrixHolderSeminormOn U a alpha hHolder) := by
  intro x hx y hy xi
  by_cases hxy : x = y
  · subst y
    rw [sub_self]
    have hzero : matVecMul (0 : Mat d) xi = 0 := by
      ext i
      simp [matVecMul]
    rw [hzero, vecEuclideanNorm_eq_zero_iff.mpr rfl]
    exact mul_nonneg
      (mul_nonneg (euclideanMatrixHolderSeminormOn_nonneg hHolder)
        (Real.rpow_nonneg (vecEuclideanNorm_nonneg (x - x)) alpha))
      (vecEuclideanNorm_nonneg xi)
  · by_cases hxi : xi = 0
    · subst xi
      simp [matVecMul, vecEuclideanNorm, vecNormSq, vecDot]
    · have hbase : 0 < vecEuclideanNorm (x - y) ^ alpha :=
        Real.rpow_pos_of_pos (vecEuclideanNorm_pos_iff.mpr (sub_ne_zero.mpr hxy)) alpha
      have hxinorm : 0 < vecEuclideanNorm xi := vecEuclideanNorm_pos_iff.mpr hxi
      have hdenom : 0 < vecEuclideanNorm (x - y) ^ alpha * vecEuclideanNorm xi :=
        mul_pos hbase hxinorm
      have hquot :
          vecEuclideanNorm (matVecMul (a x - a y) xi) /
              (vecEuclideanNorm (x - y) ^ alpha * vecEuclideanNorm xi) ≤
            euclideanMatrixHolderSeminormOn U a alpha hHolder := by
        apply le_csInf (matrixHolderConstants_nonempty hHolder)
        intro K hK
        apply (div_le_iff₀ hdenom).2
        have hbound := hK.2 x hx y hy xi
        calc
          vecEuclideanNorm (matVecMul (a x - a y) xi) ≤
              (K * vecEuclideanNorm (x - y) ^ alpha) * vecEuclideanNorm xi := hbound
          _ = K * (vecEuclideanNorm (x - y) ^ alpha * vecEuclideanNorm xi) := by ring
      have hfinal := (div_le_iff₀ hdenom).1 hquot
      calc
        vecEuclideanNorm (matVecMul (a x - a y) xi) ≤
            euclideanMatrixHolderSeminormOn U a alpha hHolder *
              (vecEuclideanNorm (x - y) ^ alpha * vecEuclideanNorm xi) := hfinal
        _ = (euclideanMatrixHolderSeminormOn U a alpha hHolder *
              vecEuclideanNorm (x - y) ^ alpha) * vecEuclideanNorm xi := by ring

theorem euclideanMatrixHolderSeminormOn_isLeast
    {U : Set (Vec d)} {a : CoeffField d} {alpha : ℝ}
    (hHolder : ∃ K : ℝ, 0 ≤ K ∧ EuclideanMatrixHolderSeminormLE U a alpha K) :
    IsLeast {K : ℝ | 0 ≤ K ∧ EuclideanMatrixHolderSeminormLE U a alpha K}
      (euclideanMatrixHolderSeminormOn U a alpha hHolder) :=
  ⟨⟨euclideanMatrixHolderSeminormOn_nonneg hHolder,
      euclideanMatrixHolderSeminormOn_bound hHolder⟩,
    fun _K hK => euclideanMatrixHolderSeminormOn_le hHolder hK.1 hK.2⟩

theorem euclideanMatrixHolderSeminormOn_le_iff
    {U : Set (Vec d)} {a : CoeffField d} {alpha K : ℝ}
    (hHolder : ∃ C : ℝ, 0 ≤ C ∧ EuclideanMatrixHolderSeminormLE U a alpha C)
    (hK : 0 ≤ K) :
    euclideanMatrixHolderSeminormOn U a alpha hHolder ≤ K ↔
      EuclideanMatrixHolderSeminormLE U a alpha K := by
  constructor
  · intro h x hx y hy xi
    calc
      vecEuclideanNorm (matVecMul (a x - a y) xi) ≤
          (euclideanMatrixHolderSeminormOn U a alpha hHolder *
            vecEuclideanNorm (x - y) ^ alpha) * vecEuclideanNorm xi :=
        euclideanMatrixHolderSeminormOn_bound hHolder x hx y hy xi
      _ ≤ (K * vecEuclideanNorm (x - y) ^ alpha) * vecEuclideanNorm xi :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right h
            (Real.rpow_nonneg (vecEuclideanNorm_nonneg (x - y)) alpha))
          (vecEuclideanNorm_nonneg xi)
  · exact euclideanMatrixHolderSeminormOn_le hHolder hK

theorem euclideanMatrixHolderSeminormOn_proof_irrel
    {U : Set (Vec d)} {a : CoeffField d} {alpha : ℝ}
    (hHolder hHolder' :
      ∃ K : ℝ, 0 ≤ K ∧ EuclideanMatrixHolderSeminormLE U a alpha K) :
    euclideanMatrixHolderSeminormOn U a alpha hHolder =
      euclideanMatrixHolderSeminormOn U a alpha hHolder' := by
  rfl

end

end PDE
