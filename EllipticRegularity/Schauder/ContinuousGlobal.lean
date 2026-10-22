module

public import PDEFoundation.Regularity.InteriorCampanatoHolder
public import PDEFoundation.Sobolev.H1.InteriorBallEnergy

/-! # Global assembly for continuous-coefficient gradient bounds -/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

/-- Local gradient bounds at one fixed scale imply an interior Hölder
representative. This is the global Campanato assembly step; applications must
separately prove the local bounds. -/
theorem exists_continuousCalpha_constant_of_local_gradient_bounds
    {d : ℕ} (hd : 2 ≤ d) {alpha R K₀ : ℝ}
    (halpha : 0 < alpha) (halpha1 : alpha < 1)
    (hR : 0 < R) (hRle : R ≤ 1 / 4) (hK₀ : 0 ≤ K₀) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (u : H1Function (euclideanBall (0 : Vec d) 1)) {N : ℝ}, 0 ≤ N →
      (∀ z ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ,
        0 < r → r ≤ R →
        r ^ (1 - alpha) *
            Real.sqrt (integralAverage (euclideanBall z r)
              (fun x => vecNormSq (u.grad x))) ≤
          K₀ * (Real.sqrt (∫ x in euclideanBall (0 : Vec d) 1,
              vecNormSq (u.grad x)) + N / (1 - alpha))) →
      HasEuclideanHolderRepresentativeOn
        (euclideanBall (0 : Vec d) (1 / 2)) u.toFun alpha
        ((C / alpha) *
          (Real.sqrt (∫ x in euclideanBall (0 : Vec d) 1,
              vecNormSq (u.grad x)) + N / (1 - alpha))) := by
  have hdpos : 0 < d := lt_of_lt_of_le Nat.zero_lt_two hd
  obtain ⟨Ccamp, hCcamp, hcamp⟩ :=
    exists_interiorCampanato_holder_constant hdpos
  let e : ℝ := 1 - alpha - (d : ℝ) / 2
  let P : ℝ := R ^ e /
    Real.sqrt (volume (euclideanBall (0 : Vec d) 1)).toReal
  let Ktotal : ℝ := K₀ + P + 1
  let C : ℝ := Ccamp * Ktotal
  have hvol : 0 < Real.sqrt
      (volume (euclideanBall (0 : Vec d) 1)).toReal :=
    Real.sqrt_pos.mpr (volume_euclideanBall_toReal_pos (0 : Vec d) (by norm_num))
  have hP : 0 ≤ P := div_nonneg (Real.rpow_nonneg hR.le _) hvol.le
  have hKtotal : 0 < Ktotal := by dsimp [Ktotal]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro u N hN hlocal
  let Graw := Real.sqrt (∫ x in euclideanBall (0 : Vec d) 1,
    vecNormSq (u.grad x))
  let Q := Graw + N / (1 - alpha)
  have hgap : 0 < 1 - alpha := sub_pos.mpr halpha1
  have hGraw : 0 ≤ Graw := Real.sqrt_nonneg _
  have hQ : 0 ≤ Q := add_nonneg hGraw (div_nonneg hN hgap.le)
  have he : e ≤ 0 := by
    dsimp [e]
    have hdreal : (2 : ℝ) ≤ d := by exact_mod_cast hd
    nlinarith
  have hscale : ∀ z ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ,
      0 < r → r ≤ 1 / 2 →
      r ^ (1 - alpha) * Real.sqrt (integralAverage (euclideanBall z r)
        (fun x => vecNormSq (u.grad x))) ≤ Ktotal * Q := by
    intro z hz r hr hrhalf
    by_cases hrR : r ≤ R
    · exact (hlocal z hz r hr hrR).trans <| by
        exact mul_le_mul_of_nonneg_right
          (by dsimp [Ktotal]; linarith) hQ
    · have hRr : R ≤ r := le_of_not_ge hrR
      have henergy := sqrt_integralAverage_vecNormSq_interiorBall_le
        hz hr hrhalf u.gradMemL2
      have hre : r ^ e ≤ R ^ e :=
        Real.rpow_le_rpow_of_nonpos hR hRr he
      have hmeanUnit : Real.sqrt (integralAverage
          (euclideanBall (0 : Vec d) 1) (fun x => vecNormSq (u.grad x))) =
          Graw / Real.sqrt (volume (euclideanBall (0 : Vec d) 1)).toReal := by
        exact sqrt_integralAverage_vecNormSq_eq _ _
      have hlarge : r ^ (1 - alpha) *
          Real.sqrt (integralAverage (euclideanBall z r)
            (fun x => vecNormSq (u.grad x))) ≤ P * Graw := by
        calc
          _ ≤ r ^ (1 - alpha) *
              (r ^ (-(d : ℝ) / 2) * Real.sqrt (integralAverage
                (euclideanBall (0 : Vec d) 1)
                  (fun x => vecNormSq (u.grad x)))) :=
            mul_le_mul_of_nonneg_left henergy (Real.rpow_nonneg hr.le _)
          _ = r ^ e * (Graw /
              Real.sqrt (volume (euclideanBall (0 : Vec d) 1)).toReal) := by
            rw [hmeanUnit, ← mul_assoc, ← Real.rpow_add hr]
            dsimp [e]
            ring_nf
          _ ≤ R ^ e * (Graw /
              Real.sqrt (volume (euclideanBall (0 : Vec d) 1)).toReal) :=
            mul_le_mul_of_nonneg_right hre (div_nonneg hGraw hvol.le)
          _ = P * Graw := by dsimp [P]; ring
      calc
        _ ≤ P * Graw := hlarge
        _ ≤ Ktotal * Q := by
          have hPK : P ≤ Ktotal := by dsimp [Ktotal]; linarith
          have hGrawQ : Graw ≤ Q := by
            dsimp [Q]
            exact le_add_of_nonneg_right (div_nonneg hN hgap.le)
          exact mul_le_mul hPK hGrawQ hGraw hKtotal.le
  have hresult := hcamp halpha halpha1
    (mul_nonneg hKtotal.le hQ) u hscale
  convert hresult using 1
  dsimp [C, Ktotal, Q, Graw]
  ring

end

end PDE
