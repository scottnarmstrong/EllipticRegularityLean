module

public import EllipticRegularity.Parabolic.Cauchy.OnDiag.TailBound
public import EllipticRegularity.Parabolic.Cauchy.OnDiag.Mass
public import EllipticRegularity.Parabolic.Cauchy.Weights.NashGeometry
public import EllipticRegularity.Parabolic.Cauchy.Energy.Positivity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# On-diagonal lower bound from mass concentration

The Gaussian weighted square estimate gives a small `L¹` tail outside a
dimensional multiple of the Nash scale.  Conservation of mass then puts at
least half the mass inside that ball, and Cauchy--Schwarz gives the claimed
whole-space `L²` lower bound.
-/

@[expose] public section

namespace PDE.Parabolic.Cauchy.OnDiag

open MeasureTheory Set

/-- The coefficient in the on-diagonal radius depends only on the dimension. -/
noncomputable def onDiagRadiusCoefficient (d : ℕ) (hd : 0 < d) : ℝ :=
  nashOnDiagRadiusConstant d hd

/-- The coefficient in the on-diagonal square-integral lower bound depends
only on the dimension. -/
noncomputable def onDiagSquareCoefficient (d : ℕ) (hd : 0 < d) : ℝ :=
  1 / (4 * (volume (euclideanBall (0 : Vec d) 1)).toReal *
    onDiagRadiusCoefficient d hd ^ d)

private theorem onDiagRadiusCoefficient_gt_two (d : ℕ) (hd : 0 < d) :
    2 < onDiagRadiusCoefficient d hd := by
  exact nashOnDiagRadiusConstant_gt_two d hd

private theorem onDiagSquareCoefficient_pos (d : ℕ) (hd : 0 < d) :
    0 < onDiagSquareCoefficient d hd := by
  have hC : 0 < onDiagRadiusCoefficient d hd := by
    unfold onDiagRadiusCoefficient
    linarith [nashOnDiagRadiusConstant_gt_two d hd]
  unfold onDiagSquareCoefficient
  have hV := PDE.volume_euclideanBall_toReal_pos (0 : Vec d) (R := 1) (by norm_num)
  positivity

/-- The Nash--Aronson on-diagonal lower estimate. -/
theorem onDiagLower (d : ℕ) (hd : 0 < d) :
    ∃ C₁ c : ℝ, 0 < C₁ ∧ 0 < c ∧ ∀ Lam : ℝ, 1 ≤ Lam →
      ∀ (a : ParCoeffField d) (s t : ℝ), s < t →
      IsParabolicCoeff 1 Lam a univ (Icc s t) →
      ∀ (y : Vec d) (ε : ℝ) (f : Vec d → ℝ),
      Integrable f volume → MemLp f 2 volume →
      (∀ᵐ x : Vec d, 0 ≤ f x) → ∫ x, f x = 1 →
      (∀ᵐ x : Vec d, x ∉ euclideanBall y ε → f x = 0) →
      ε ^ 2 ≤ Lam * (t - s) →
      ∀ u : ParH1Function (univ : Set (Vec d)) (Icc s t),
        IsCauchySolution a s t f u →
        ε ≤ C₁ * Real.sqrt (Lam * (t - s) * Real.log (Real.exp 1 * Lam)) ∧
        (1 / 2 : ℝ) ≤ ∫ x in euclideanBall y
          (C₁ * Real.sqrt (Lam * (t - s) * Real.log (Real.exp 1 * Lam))),
            u.toFun (x, t) ∧
        ENNReal.ofReal
          (c * (Lam * Real.log (Real.exp 1 * Lam) * (t - s)) ^ (-(d : ℝ) / 2)) ≤
          ∫⁻ x : Vec d, ENNReal.ofReal (u.toFun (x, t) ^ 2) := by
  refine ⟨onDiagRadiusCoefficient d hd, onDiagSquareCoefficient d hd,
    ?_, onDiagSquareCoefficient_pos d hd, ?_⟩
  · exact lt_trans (by norm_num) (onDiagRadiusCoefficient_gt_two d hd)
  intro Lam hLam a s t hst ha y ε f hf1 hf2 hfnonneg hfmass hfsupp hε u hu
  obtain ⟨H, hT⟩ : ∃ H : ℝ, t = s + H := ⟨t - s, by ring⟩
  have hH : 0 < H := by rw [hT] at hst; linarith
  cases hT
  let C₁ : ℝ := onDiagRadiusCoefficient d hd
  let c : ℝ := onDiagSquareCoefficient d hd
  let I : ℝ := ∫ x : Vec d, f x ^ 2
  let κ : ℝ := ((d : ℝ) + 2) / 2
  let σ : ℝ := min (H / 2) (min 1 (H / (I + 1)))
  let Kscale : ℝ := Lam * H * Real.log (Real.exp 1 * Lam)
  let R : ℝ := C₁ * Real.sqrt Kscale
  have hI : 0 ≤ I := by
    dsimp [I]
    exact integral_nonneg_of_ae (ae_of_all _ fun x => sq_nonneg (f x))
  have hκ : 1 ≤ κ := by
    dsimp [κ]
    have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
    linarith
  have hσpos : 0 < σ := by
    dsimp [σ]
    apply lt_min
    · linarith
    · apply lt_min
      · norm_num
      · exact div_pos hH (by linarith)
  have hσH : σ ≤ H / 2 := by
    dsimp [σ]
    exact min_le_left _ _
  have hσone : σ ≤ 1 := by
    dsimp [σ]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hσI : σ ≤ H / (I + 1) := by
    dsimp [σ]
    exact le_trans (min_le_right _ _) (min_le_right _ _)
  have hσData : σ ^ κ * I ≤ H := by
    have hpow : σ ^ κ ≤ σ := by
      calc
        σ ^ κ ≤ σ ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_ge hσpos hσone hκ
        _ = σ := Real.rpow_one σ
    have hσmul : σ * (I + 1) ≤ H :=
      (le_div_iff₀ (by linarith : 0 < I + 1)).mp hσI
    calc
      σ ^ κ * I ≤ σ * I := mul_le_mul_of_nonneg_right hpow hI
      _ ≤ σ * (I + 1) := by linarith [hσpos.le]
      _ ≤ H := hσmul
  have hMomentWeighted := cauchy_unit_mass_weighted_square_bound
    (d := d) hd hH hLam hσpos hσH a ha y f hf1 hf2 hσData
    hfnonneg hfmass hfsupp u hu
  have hMass := cauchy_unit_mass_conservation_of_ball_support hst ha y f
    hf1 hf2 hfmass hfsupp u hu (t := s + H) ⟨le_of_lt hst, le_rfl⟩
  let v : Vec d → ℝ := fun x => u.toFun (x, s + H)
  have hv1 : Integrable v volume := by
    change Integrable (parSlice u.toFun (s + H)) volume
    exact hMass.1
  have hv2 : MemLp v 2 volume := by
    simpa [v] using PDE.Parabolic.Cauchy.Weights.cauchy_slice_memLp_of_solution
      hst ⟨le_of_lt hst, le_rfl⟩ ha hf2 u hu
  have hvnonneg : 0 ≤ᵐ[volume] v := by
    have hpos := PDE.Parabolic.Cauchy.Energy.cauchyPositivity
      d 1 Lam a s (s + H) hst ha f hf2 hfnonneg u hu (s + H)
        ⟨le_of_lt hst, le_rfl⟩
    change ∀ᵐ x : Vec d, 0 ≤ v x
    simpa [v] using hpos
  have hmassEq : ∫ x : Vec d, v x = 1 := by
    simpa [v] using hMass.2
  have hlog := nashLogFactor_ge_one hLam
  have hLamH : 0 < Lam * H := by
    exact mul_pos (lt_of_lt_of_le (by norm_num) hLam) hH
  have hKscale : 0 < Kscale := by
    dsimp [Kscale]
    exact mul_pos hLamH (lt_of_lt_of_le (by norm_num) hlog)
  have hC₁gt : 2 < C₁ := by
    dsimp [C₁]
    exact onDiagRadiusCoefficient_gt_two d hd
  have hC₁pos : 0 < C₁ := by linarith
  have hRpos : 0 < R := by dsimp [R]; positivity
  have hrootLamH : 0 ≤ Real.sqrt (Lam * H) := by positivity
  have hrootScale : Real.sqrt (Lam * H) ≤ Real.sqrt Kscale := by
    apply Real.sqrt_le_sqrt
    dsimp [Kscale]
    have hlog' := nashLogFactor_ge_one hLam
    exact le_mul_of_one_le_right hLamH.le hlog'
  have hεabs : |ε| ≤ Real.sqrt (Lam * H) := by
    have hεsqrt : Real.sqrt (ε ^ 2) ≤ Real.sqrt (Lam * H) :=
      Real.sqrt_le_sqrt (by simpa [sub_add_cancel] using hε)
    simpa [Real.sqrt_sq_eq_abs] using hεsqrt
  have hRε : 2 * |ε| ≤ R := by
    dsimp [R]
    calc
      2 * |ε| ≤ 2 * Real.sqrt (Lam * H) := by linarith [hεabs]
      _ ≤ C₁ * Real.sqrt Kscale := by
        have hCmul : 2 * Real.sqrt Kscale ≤ C₁ * Real.sqrt Kscale :=
          mul_le_mul_of_nonneg_right (le_of_lt hC₁gt) (Real.sqrt_nonneg _)
        exact (mul_le_mul_of_nonneg_left hrootScale (by norm_num)).trans hCmul
  have hRformula : R = nashOnDiagRadiusConstant d hd *
      Real.sqrt (Lam * H * Real.log (Real.exp 1 * Lam)) := by
    rfl
  have hweighted : ∫⁻ x : Vec d, ENNReal.ofReal
      (Real.exp (PDE.Parabolic.Cauchy.Weights.euclideanSetDistance
        (euclideanClosedBall y |ε|) x ^ 2 / (6 * Lam * H)) * v x ^ 2) ≤
      ENNReal.ofReal
        (nashWeightedSquareConstant d hd * H ^ (-(d : ℝ) / 2)) := by
    simpa [v, parSlice] using hMomentWeighted
  have htail := nash_weighted_square_tail_mass_bound hd hLam hH hRpos hRε
    hRformula y v hv1 hvnonneg hweighted
  let B : Set (Vec d) := euclideanBall y R
  let tail : Set (Vec d) := {x : Vec d | R ^ 2 ≤ vecNormSq (x - y)}
  have hBcompl : Bᶜ = tail := by
    ext x
    change (x ∉ euclideanBall y R) ↔ R ^ 2 ≤ vecNormSq (x - y)
    change (¬ vecNormSq (x - y) < R ^ 2) ↔ R ^ 2 ≤ vecNormSq (x - y)
    exact not_lt
  have htail' : ∫ x in Bᶜ, v x ≤ 1 / 2 := by
    simpa [B, hBcompl, tail] using htail
  have hdecomp := integral_add_compl (isOpen_euclideanBall y R).measurableSet hv1
  rw [hBcompl, hmassEq] at hdecomp
  have hballMass : (1 / 2 : ℝ) ≤ ∫ x in B, v x := by
    linarith
  have hεH : ε ^ 2 ≤ Lam * H := by simpa [sub_add_cancel] using hε
  have hRadiusBound : ε ≤ C₁ * Real.sqrt Kscale := by
    simpa [Kscale] using support_radius_le_onDiag_scale hLam hH hεH
      (by linarith [hC₁gt])
  have hmassAtScale : (1 / 2 : ℝ) ≤ ∫ x in euclideanBall y
      (C₁ * Real.sqrt (Lam * H * Real.log (Real.exp 1 * Lam))), v x := by
    simpa [B, R, Kscale] using hballMass
  have hL2lower := lintegral_square_lower_at_nash_scale y hLam hH
    (by linarith [hC₁gt]) v hv2 hvnonneg hmassAtScale
  have hCoefficientIdentity :
      (1 / (4 * (volume (euclideanBall (0 : Vec d) 1)).toReal * C₁ ^ d)) *
          (Lam * H * Real.log (Real.exp 1 * Lam)) ^ (-(d : ℝ) / 2) =
      c * (Lam * Real.log (Real.exp 1 * Lam) * H) ^ (-(d : ℝ) / 2) := by
    dsimp [c, C₁, onDiagSquareCoefficient, onDiagRadiusCoefficient]
    rw [show Lam * H * Real.log (Real.exp 1 * Lam) =
      Lam * Real.log (Real.exp 1 * Lam) * H by ring]
  refine ⟨?_, ?_, ?_⟩
  · simpa [Kscale, sub_add_cancel] using hRadiusBound
  · simpa [v, B, R, Kscale] using hmassAtScale
  · rw [hCoefficientIdentity] at hL2lower
    simpa [v] using hL2lower

end PDE.Parabolic.Cauchy.OnDiag
