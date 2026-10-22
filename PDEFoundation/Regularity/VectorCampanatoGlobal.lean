module

public import PDEFoundation.Regularity.VectorCampanatoBound
public import PDEFoundation.Regularity.CampanatoConstant
public import PDEFoundation.Regularity.FieldHolder

/-!
# Global Hölder bounds for canonical vector Campanato representatives
-/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

variable {d : ℕ}

private theorem euclideanFieldHolder_of_local_of_bound
    {F : Vec d → Vec d} {S : Set (Vec d)} {alpha L M rho : ℝ}
    (halpha : 0 < alpha) (hL : 0 ≤ L) (hM : 0 ≤ M) (hrho : 0 < rho)
    (hlocal : ∀ x ∈ S, ∀ y ∈ S,
      vecEuclideanNorm (x - y) ≤ rho →
        vecEuclideanNorm (F x - F y) ≤
          L * vecEuclideanNorm (x - y) ^ alpha)
    (hbound : ∀ x ∈ S, vecEuclideanNorm (F x) ≤ M) :
    EuclideanFieldHolderSeminormLE S F alpha
      (L + 2 * M / rho ^ alpha) := by
  intro x hx y hy
  by_cases hxy : vecEuclideanNorm (x - y) ≤ rho
  · exact (hlocal x hx y hy hxy).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (by positivity))
        (Real.rpow_nonneg (vecEuclideanNorm_nonneg _) alpha))
  · have hdist : rho < vecEuclideanNorm (x - y) := lt_of_not_ge hxy
    have hpowPos : 0 < rho ^ alpha := Real.rpow_pos_of_pos hrho alpha
    have hpow : rho ^ alpha ≤ vecEuclideanNorm (x - y) ^ alpha :=
      Real.rpow_le_rpow hrho.le hdist.le halpha.le
    have hdiff : vecEuclideanNorm (F x - F y) ≤ 2 * M := by
      calc
        vecEuclideanNorm (F x - F y) ≤
            vecEuclideanNorm (F x) + vecEuclideanNorm (F y) :=
          calc
            vecEuclideanNorm (F x - F y) =
                vecEuclideanNorm (F x + (-F y)) := by rw [sub_eq_add_neg]
            _ ≤ vecEuclideanNorm (F x) + vecEuclideanNorm (-F y) :=
              vecEuclideanNorm_add_le _ _
            _ = vecEuclideanNorm (F x) + vecEuclideanNorm (F y) := by
              rw [vecEuclideanNorm_neg]
        _ ≤ M + M := add_le_add (hbound x hx) (hbound y hy)
        _ = 2 * M := by ring
    calc
      vecEuclideanNorm (F x - F y) ≤ 2 * M := hdiff
      _ ≤ (2 * M / rho ^ alpha) *
          vecEuclideanNorm (x - y) ^ alpha := by
        rw [div_mul_eq_mul_div, le_div_iff₀ hpowPos]
        exact mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ (L + 2 * M / rho ^ alpha) *
          vecEuclideanNorm (x - y) ^ alpha :=
        mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hL)
          (Real.rpow_nonneg (vecEuclideanNorm_nonneg _) alpha)

/-- A dimension-only constant sufficient for both the local Campanato bound,
the long-pair argument, and the pointwise representative bound. -/
def vectorCampanatoGlobalCoefficient (d : ℕ) : ℝ :=
  (d : ℝ) * vectorBallCampanatoCoefficient d *
    (32 * Real.sqrt ((2 : ℝ) ^ d) + 8 * Real.sqrt d + 1)

theorem vectorCampanatoGlobalCoefficient_pos (hd : 0 < d) :
    0 < vectorCampanatoGlobalCoefficient d := by
  have hdR : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hroot : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdR
  have hunit : 0 < (volume (euclideanBall (0 : Vec d) 1)).toReal :=
    volume_euclideanBall_toReal_pos _ (by norm_num)
  unfold vectorCampanatoGlobalCoefficient vectorBallCampanatoCoefficient
  positivity

/-- The dimension-only global Campanato conclusion for the canonical vector
representative, retaining the scales `K` and `B / r₀ ^ α`. -/
theorem exists_vectorCampanatoGlobalCoefficient
    (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {r₀ α K B : ℝ},
        0 < r₀ → r₀ ≤ 1 / 4 →
        0 < α → α < 1 → 0 ≤ K → 0 ≤ B →
        ∀ {g : Vec d → Vec d},
          MemVectorL2On (euclideanBall (0 : Vec d) 1) g →
          (∀ z ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ,
            0 < r → r ≤ r₀ →
              centeredVectorMeanL2 (euclideanBall z r) g ≤ K * r ^ α) →
          (∀ z ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ,
            0 < r → r ≤ r₀ →
              Real.sqrt (integralAverage (euclideanBall z r)
                (fun y => vecNormSq (g y))) ≤ B) →
          ∃ G : Vec d → Vec d,
            G = vectorCampanatoRepresentative r₀ g ∧
            G =ᵐ[volumeOn (euclideanBall (0 : Vec d) (1 / 2))] g ∧
            (∀ x ∈ euclideanBall (0 : Vec d) (1 / 2),
              vecEuclideanNorm (G x) ≤ C * B) ∧
            EuclideanFieldHolderSeminormLE
              (euclideanBall (0 : Vec d) (1 / 2)) G α
              ((C / α) * (K + B / r₀ ^ α)) := by
  let C := vectorCampanatoGlobalCoefficient d
  refine ⟨C, vectorCampanatoGlobalCoefficient_pos hd, ?_⟩
  intro r₀ α K B hr₀ hr₀le hα0 hα1 hK hB g hg hscale henergy
  let A := vectorBallCampanatoCoefficient d
  let H := dyadicCampanatoHolderConst d α
  let R := vectorBallCampanatoBaseRadius d r₀
  let G := vectorCampanatoRepresentative r₀ g
  have hroot : 0 < Real.sqrt d :=
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd)
  have hA : 0 < A := by
    dsimp [A, vectorBallCampanatoCoefficient]
    have hunit : 0 < (volume (euclideanBall (0 : Vec d) 1)).toReal :=
      volume_euclideanBall_toReal_pos _ (by norm_num)
    positivity
  have hR : 0 < R := by
    dsimp [R]
    exact vectorBallCampanatoBaseRadius_pos hd hr₀
  obtain ⟨G', hG', hGae, hlocal⟩ :=
    exists_vectorCampanatoRepresentative_of_vectorBallScale
      hd hr₀ hr₀le hα0 hα1 hK hg hscale
  have hG'eq : G' = G := by simpa only [G] using hG'
  subst G'
  have hpointRaw := vectorCampanatoRepresentative_pointwise_le_of_vectorBallEnergy
    hd hr₀ hr₀le hα0 hα1 hK hB hg hscale henergy
  have hpoint : ∀ x ∈ euclideanBall (0 : Vec d) (1 / 2),
      vecEuclideanNorm (G x) ≤ C * B := by
    intro x hx
    refine (hpointRaw x hx).trans ?_
    apply mul_le_mul_of_nonneg_right _ hB
    dsimp [C, vectorCampanatoGlobalCoefficient]
    have hone : 1 ≤ 32 * Real.sqrt ((2 : ℝ) ^ d) +
        8 * Real.sqrt d + 1 := by
      nlinarith [Real.sqrt_nonneg ((2 : ℝ) ^ d), Real.sqrt_nonneg d]
    have hbase : Real.sqrt ((Real.sqrt d) ^ d *
        (volume (euclideanBall (0 : Vec d) 1)).toReal) ≤ A := by
      dsimp [A, vectorBallCampanatoCoefficient]
      have htwo : 1 ≤ 2 * Real.sqrt d := by
        have hdR : (1 : ℝ) ≤ d := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hd)
        have hs : 1 ≤ Real.sqrt d := by simpa using Real.sqrt_le_sqrt hdR
        nlinarith
      nlinarith [Real.sqrt_nonneg ((Real.sqrt d) ^ d *
        (volume (euclideanBall (0 : Vec d) 1)).toReal)]
    change (d : ℝ) * Real.sqrt ((Real.sqrt d) ^ d *
        (volume (euclideanBall (0 : Vec d) 1)).toReal) ≤
      (d : ℝ) * A *
        (32 * Real.sqrt ((2 : ℝ) ^ d) + 8 * Real.sqrt d + 1)
    calc
      _ ≤ (d : ℝ) * A := mul_le_mul_of_nonneg_left hbase (by positivity)
      _ ≤ (d : ℝ) * A *
          (32 * Real.sqrt ((2 : ℝ) ^ d) + 8 * Real.sqrt d + 1) := by
        nlinarith [mul_nonneg (by positivity : 0 ≤ (d : ℝ)) hA.le]
  have hH : H ≤ (32 * Real.sqrt ((2 : ℝ) ^ d)) / α := by
    dsimp [H]
    exact dyadicCampanatoHolderConst_le_inv_alpha d hα0 hα1
  have hlocal' : ∀ x ∈ euclideanBall (0 : Vec d) (1 / 2),
      ∀ y ∈ euclideanBall (0 : Vec d) (1 / 2),
        vecEuclideanNorm (x - y) ≤ R / 2 →
          vecEuclideanNorm (G x - G y) ≤
            ((d : ℝ) * H * A * K) * vecEuclideanNorm (x - y) ^ α := by
    simpa only [G, H, A, R, mul_assoc] using hlocal
  have hglobal := euclideanFieldHolder_of_local_of_bound
    hα0 (mul_nonneg (mul_nonneg (mul_nonneg (by positivity)
      (dyadicCampanatoHolderConst_nonneg d hα0)) hA.le) hK)
    (by positivity : 0 ≤ (d : ℝ) * A * B) (by positivity : 0 < R / 2)
    hlocal'
    (fun x hx => by
      have hp := hpointRaw x hx
      dsimp [G]
      refine hp.trans (mul_le_mul_of_nonneg_right ?_ hB)
      dsimp [A, vectorBallCampanatoCoefficient]
      have htwo : 1 ≤ 2 * Real.sqrt d := by
        have hdR : (1 : ℝ) ≤ d := by
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hd)
        have hs : 1 ≤ Real.sqrt d := by simpa using Real.sqrt_le_sqrt hdR
        nlinarith
      have hsnonneg : 0 ≤ Real.sqrt ((Real.sqrt d) ^ d *
          (volume (euclideanBall (0 : Vec d) 1)).toReal) := Real.sqrt_nonneg _
      have hdpos : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
      exact mul_le_mul_of_nonneg_left
        (le_mul_of_one_le_right hsnonneg htwo) hdpos.le)
  have hfactor : 1 ≤ 4 * Real.sqrt d := by
    have hdR : (1 : ℝ) ≤ d := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hd)
    have hs : 1 ≤ Real.sqrt d := by simpa using Real.sqrt_le_sqrt hdR
    nlinarith
  have hfactorPow : (4 * Real.sqrt d) ^ α ≤ 4 * Real.sqrt d := by
    calc
      (4 * Real.sqrt d) ^ α ≤ (4 * Real.sqrt d) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hfactor hα1.le
      _ = 4 * Real.sqrt d := Real.rpow_one _
  have hr₀pow : 0 < r₀ ^ α := Real.rpow_pos_of_pos hr₀ α
  have hRpow : (R / 2) ^ α = r₀ ^ α / (4 * Real.sqrt d) ^ α := by
    have heq : R / 2 = r₀ / (4 * Real.sqrt d) := by
      dsimp [R, vectorBallCampanatoBaseRadius]
      field_simp
      ring
    rw [heq, Real.div_rpow hr₀.le (by positivity)]
  have hcoeff :
      (d : ℝ) * H * A * K +
          2 * ((d : ℝ) * A * B) / (R / 2) ^ α ≤
        (C / α) * (K + B / r₀ ^ α) := by
    have hαle : α ≤ 1 := hα1.le
    have hαpos : 0 < α := hα0
    have hlocalCoeff : (d : ℝ) * H * A * K ≤
        (C / α) * K := by
      apply mul_le_mul_of_nonneg_right _ hK
      have hnum : (d : ℝ) * (32 * Real.sqrt ((2 : ℝ) ^ d)) * A ≤ C := by
        have hpart : 32 * Real.sqrt ((2 : ℝ) ^ d) ≤
            32 * Real.sqrt ((2 : ℝ) ^ d) + 8 * Real.sqrt d + 1 := by
          nlinarith [Real.sqrt_nonneg d]
        dsimp [C, vectorCampanatoGlobalCoefficient]
        calc
          (d : ℝ) * (32 * Real.sqrt ((2 : ℝ) ^ d)) * A =
              ((d : ℝ) * A) * (32 * Real.sqrt ((2 : ℝ) ^ d)) := by ring
          _ ≤ ((d : ℝ) * A) *
              (32 * Real.sqrt ((2 : ℝ) ^ d) + 8 * Real.sqrt d + 1) :=
            mul_le_mul_of_nonneg_left hpart (mul_nonneg (by positivity) hA.le)
      calc
        (d : ℝ) * H * A ≤
            (d : ℝ) * ((32 * Real.sqrt ((2 : ℝ) ^ d)) / α) * A := by
          gcongr
        _ = ((d : ℝ) * (32 * Real.sqrt ((2 : ℝ) ^ d)) * A) / α := by ring
        _ ≤ C / α := div_le_div_of_nonneg_right hnum hα0.le
    have hlongCoeff : 2 * ((d : ℝ) * A * B) / (R / 2) ^ α ≤
        (C / α) * (B / r₀ ^ α) := by
      rw [hRpow]
      have hfacpos : 0 < (4 * Real.sqrt d) ^ α :=
        Real.rpow_pos_of_pos (by positivity) α
      have hCpart : 8 * Real.sqrt d ≤
          32 * Real.sqrt ((2 : ℝ) ^ d) + 8 * Real.sqrt d + 1 := by
        nlinarith [Real.sqrt_nonneg ((2 : ℝ) ^ d)]
      have hcoef : 2 * (d : ℝ) * A * (4 * Real.sqrt d) ^ α ≤ C / α := by
        apply (le_div_iff₀ hα0).2
        have hleft : 2 * (4 * Real.sqrt d) ^ α * α ≤
            8 * Real.sqrt d := by
          calc
            2 * (4 * Real.sqrt d) ^ α * α ≤
                2 * (4 * Real.sqrt d) * α := by gcongr
            _ ≤ 8 * Real.sqrt d := by nlinarith
        dsimp [C, vectorCampanatoGlobalCoefficient]
        calc
          2 * (d : ℝ) * A * (4 * Real.sqrt d) ^ α * α =
              ((d : ℝ) * A) *
                (2 * (4 * Real.sqrt d) ^ α * α) := by ring
          _ ≤ ((d : ℝ) * A) * (8 * Real.sqrt d) :=
            mul_le_mul_of_nonneg_left hleft (mul_nonneg (by positivity) hA.le)
          _ ≤ ((d : ℝ) * A) *
              (32 * Real.sqrt ((2 : ℝ) ^ d) + 8 * Real.sqrt d + 1) :=
            mul_le_mul_of_nonneg_left hCpart (mul_nonneg (by positivity) hA.le)
      calc
        2 * ((d : ℝ) * A * B) /
            (r₀ ^ α / (4 * Real.sqrt d) ^ α) =
            (2 * (d : ℝ) * A * (4 * Real.sqrt d) ^ α) *
              (B / r₀ ^ α) := by
          field_simp [hr₀pow.ne', hfacpos.ne']
        _ ≤ (C / α) * (B / r₀ ^ α) :=
          mul_le_mul_of_nonneg_right hcoef (div_nonneg hB hr₀pow.le)
    calc
      _ ≤ (C / α) * K + (C / α) * (B / r₀ ^ α) :=
        add_le_add hlocalCoeff hlongCoeff
      _ = _ := by ring
  refine ⟨G, rfl, hGae, hpoint, ?_⟩
  intro x hx y hy
  exact (hglobal x hx y hy).trans
    (mul_le_mul_of_nonneg_right hcoeff
      (Real.rpow_nonneg (vecEuclideanNorm_nonneg _) α))

end

end PDE
