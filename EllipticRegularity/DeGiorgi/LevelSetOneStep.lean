module

public import EllipticRegularity.DeGiorgi.CutoffSobolev
public import PDEFoundation.Measure.BallVolume
public import PDEFoundation.Measure.HolderRestriction
public import PDEFoundation.Measure.Superlevel
public import PDEFoundation.Sobolev.Inequalities.LocalCriticalSobolev

/-!
# One De Giorgi level-set step in dimensions at least three

This module combines the local critical Sobolev estimate, restricted Hölder,
and the quadratic superlevel bound.  The mixed inner-energy factor is retained
in the main theorem; replacing it by the outer energy is a later, deliberately
coarser iteration step.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open Filter MeasureTheory Set

private theorem memLp_positivePartSubConst_two_on_euclideanBall
    {d : ℕ} {U : Set (Vec d)} {u : H1Function U}
    {x₀ : Vec d} {k r R : ℝ}
    (hU : IsOpenBoundedConvexDomain U)
    (hr : 0 < r) (hrR : r < R)
    (hball : euclideanBall x₀ R ⊆ U) :
    MemLp (fun x => max (u x - k) 0) 2
      (volume.restrict (euclideanBall x₀ r)) := by
  have hinnerU : euclideanBall x₀ r ⊆ U :=
    (euclideanBall_mono hr.le hrR.le).trans hball
  simpa only [H1Function.positivePartSubConst_toFun] using
    memLpOn_mono hinnerU (u.positivePartSubConst hU k).memL2

private theorem nullMeasurableSet_superlevel_on_euclideanBall
    {d : ℕ} {U : Set (Vec d)} {u : H1Function U}
    {x₀ : Vec d} {ell r R : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hball : euclideanBall x₀ R ⊆ U) :
    NullMeasurableSet {x | ell < u x}
      (volume.restrict (euclideanBall x₀ r)) := by
  have hinnerU : euclideanBall x₀ r ⊆ U :=
    (euclideanBall_mono hr.le hrR.le).trans hball
  have hu : MemLp u 2 (volume.restrict (euclideanBall x₀ r)) :=
    memLpOn_mono hinnerU u.memL2
  exact aestronglyMeasurable_const.nullMeasurableSet_lt hu.aestronglyMeasurable

/-- The exact mixed-energy De Giorgi level-set step.  The exponent `2 / d`
comes from the measure factor in restricted Hölder, while the Sobolev exponent
`(d - 2) / d` is consumed before the final estimate is formed. -/
theorem setIntegral_positivePartSubConst_sq_ball_le_of_h10Subharmonic
    {d : ℕ} {lam Lam k ell r R : ℝ} {U : Set (Vec d)}
    {x₀ : Vec d} {a : CoeffField d} {u : H1Function U}
    (hd : 3 ≤ d) (hU : IsOpenBoundedConvexDomain U)
    (hr : 0 < r) (hrR : r < R)
    (hball : euclideanBall x₀ R ⊆ U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hlam : 0 < lam) (hLam : 0 ≤ Lam)
    (hsub : IsWeakDivergenceFormH10SubharmonicOn a U u)
    (hkell : k < ell) :
    (∫ x in euclideanBall x₀ r, max (u x - ell) 0 ^ 2) ≤
      (zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
          ((8 * Lam / lam) + 2) * (32 / (R - r)) ^ 2 *
          (∫ x in euclideanBall x₀ R, max (u x - ell) 0 ^ 2) *
          ((∫ x in euclideanBall x₀ r, max (u x - k) 0 ^ 2) /
            (ell - k) ^ 2) ^ (2 / (d : ℝ)) := by
  let inner : Set (Vec d) := euclideanBall x₀ r
  let outer : Set (Vec d) := euclideanBall x₀ R
  let A : Set (Vec d) := inner ∩ {x | ell < u x}
  let wk : Vec d → ℝ := fun x => max (u x - k) 0
  let well : Vec d → ℝ := fun x => max (u x - ell) 0
  let q : ℝ := (2 : ℝ) * d / ((d : ℝ) - 2)
  let θ : ℝ := ((d : ℝ) - 2) / (d : ℝ)
  let β : ℝ := 2 / (d : ℝ)
  have hAinner : A ⊆ inner := inter_subset_left
  have hinnerMeas : MeasurableSet inner := by
    dsimp only [inner]
    exact (isOpen_euclideanBall x₀ r).measurableSet
  have hAfin : volume A < ∞ :=
    lt_of_le_of_lt (measure_mono hAinner)
      (volume_euclideanBall_ne_top x₀ hr.le).lt_top
  have hwkL2 : MemLp wk 2 (volume.restrict inner) := by
    simpa only [wk, inner] using
      memLp_positivePartSubConst_two_on_euclideanBall hU hr hrR hball (u := u) (k := k)
  have hwkSqInt : IntegrableOn (fun x => wk x ^ 2) inner := by
    simpa only [pow_two] using integrableOn_mul_of_memL2On hwkL2 hwkL2
  have hlevel : NullMeasurableSet {x | ell < u x} (volume.restrict inner) := by
    simpa only [inner] using
      nullMeasurableSet_superlevel_on_euclideanBall hr hrR hball (u := u) (ell := ell)
  have hcriticalInner : MemLp well (ENNReal.ofReal q) (volume.restrict inner) := by
    simpa only [well, q] using
      H1Function.memLp_positivePartSubConst_two_mul_div_sub_two_on_euclideanBall
        (u := u) (k := ell) hd hU hr hrR hball
  have hcriticalA : MemLp well (ENNReal.ofReal q) (volume.restrict A) :=
    hcriticalInner.mono_measure (Measure.restrict_mono hAinner le_rfl)
  have hq_pos : 0 < q := by
    dsimp only [q]
    have hd_two : (2 : ℝ) < d := by
      exact_mod_cast lt_of_lt_of_le (by norm_num : 2 < 3) hd
    exact div_pos (mul_pos (by norm_num) (by positivity)) (sub_pos.mpr hd_two)
  have hqInt : IntegrableOn (fun x => |well x| ^ q) inner := by
    have h := hcriticalInner.integrable_norm_rpow
      (ENNReal.ofReal_ne_zero_iff.mpr hq_pos) ENNReal.ofReal_ne_top
    simpa only [IntegrableOn, Real.norm_eq_abs,
      ENNReal.toReal_ofReal hq_pos.le] using h
  have hholder :=
    setIntegral_sq_le_setIntegral_abs_rpow_two_mul_div_sub_two_rpow_sub_div_mul_measure_toReal_rpow
      (μ := volume) (A := A) hd hAfin hcriticalA
  have hqA_le :
      (∫ x in A, |well x| ^ q) ≤ ∫ x in inner, |well x| ^ q := by
    apply MeasureTheory.setIntegral_mono_set hqInt
    · exact Filter.Eventually.of_forall fun x =>
        Real.rpow_nonneg (abs_nonneg (well x)) _
    · exact Filter.Eventually.of_forall fun x hx => hAinner hx
  have hqA_nonneg : 0 ≤ ∫ x in A, |well x| ^ q := by
    exact integral_nonneg fun x => Real.rpow_nonneg (abs_nonneg (well x)) _
  have hθ_nonneg : 0 ≤ θ := by
    dsimp only [θ]
    have hd_two : (2 : ℝ) ≤ d := by
      exact_mod_cast le_trans (by norm_num : 2 ≤ 3) hd
    exact div_nonneg (sub_nonneg.mpr hd_two) (by positivity)
  have hqPow :
      (∫ x in A, |well x| ^ q) ^ θ ≤
        (∫ x in inner, |well x| ^ q) ^ θ :=
    Real.rpow_le_rpow hqA_nonneg hqA_le hθ_nonneg
  have hcutoff :
      (∫ x in inner, well x ^ q) ^ θ ≤
        (zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
          ((8 * Lam / lam) + 2) * (32 / (R - r)) ^ 2 *
          ∫ x in outer, well x ^ 2 := by
    simpa only [inner, outer, well, q, θ] using
      setIntegral_positivePartSubConst_rpow_ball_le_of_h10Subharmonic
        (u := u) (x₀ := x₀) (k := ell) hd hU hr hrR hball hEll hlam hLam hsub
  have hsuper :=
    sq_mul_measure_inter_superlevel_toReal_le_setIntegral_sq
      (μ := volume) (f := u) (S := inner) (k := k) (ell := ell)
      hkell hlevel (by simpa only [wk] using! hwkSqInt)
  have hδ : 0 < ell - k := sub_pos.mpr hkell
  have hδsq : 0 < (ell - k) ^ 2 := sq_pos_of_pos hδ
  have hmeasure :
      (volume A).toReal ≤
        (∫ x in inner, wk x ^ 2) / (ell - k) ^ 2 := by
    apply (le_div_iff₀ hδsq).2
    simpa only [A, wk, mul_comm] using hsuper
  have hβ_nonneg : 0 ≤ β := by
    dsimp only [β]
    apply div_nonneg
    · norm_num
    · exact_mod_cast (show 0 ≤ d by omega : 0 ≤ d)
  have hmeasurePow :
      (volume A).toReal ^ β ≤
        ((∫ x in inner, wk x ^ 2) / (ell - k) ^ 2) ^ β :=
    Real.rpow_le_rpow ENNReal.toReal_nonneg hmeasure hβ_nonneg
  have hleft_eq :
      (∫ x in inner, well x ^ 2) = ∫ x in A, well x ^ 2 := by
    apply MeasureTheory.setIntegral_eq_of_subset_of_forall_sdiff_eq_zero
      hinnerMeas hAinner
    intro x hx
    have hxle : u x ≤ ell := by
      apply not_lt.mp
      intro hxlt
      exact hx.2 ⟨hx.1, hxlt⟩
    have hzero : well x = 0 := by
      dsimp only [well]
      exact max_eq_right (sub_nonpos.mpr hxle)
    rw [hzero]
    norm_num
  have hmeasurePow_nonneg : 0 ≤ (volume A).toReal ^ β :=
    Real.rpow_nonneg ENNReal.toReal_nonneg _
  have habs_inner :
      (∫ x in inner, |well x| ^ q) = ∫ x in inner, well x ^ q := by
    apply MeasureTheory.setIntegral_congr_fun hinnerMeas
    intro x _
    change |well x| ^ q = well x ^ q
    rw [abs_of_nonneg]
    dsimp only [well]
    exact le_max_right _ _
  have hcutoffRight_nonneg :
      0 ≤ (zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
          ((8 * Lam / lam) + 2) * (32 / (R - r)) ^ 2 *
          ∫ x in outer, well x ^ 2 := by
    have hratio : 0 ≤ 8 * Lam / lam :=
      div_nonneg (mul_nonneg (by norm_num) hLam) hlam.le
    have hinterior : 0 ≤ ∫ x in outer, well x ^ 2 := by
      exact integral_nonneg fun x => sq_nonneg (well x)
    positivity
  calc
    (∫ x in euclideanBall x₀ r, max (u x - ell) 0 ^ 2) =
        ∫ x in inner, well x ^ 2 := by rfl
    _ = ∫ x in A, well x ^ 2 := hleft_eq
    _ ≤ (∫ x in A, |well x| ^ q) ^ θ * (volume A).toReal ^ β := by
      simpa only [β, θ, q, Real.rpow_two, sq_abs] using hholder
    _ ≤ (∫ x in inner, |well x| ^ q) ^ θ * (volume A).toReal ^ β :=
      mul_le_mul_of_nonneg_right hqPow hmeasurePow_nonneg
    _ = (∫ x in inner, well x ^ q) ^ θ * (volume A).toReal ^ β := by
      rw [habs_inner]
    _ ≤ ((zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
          ((8 * Lam / lam) + 2) * (32 / (R - r)) ^ 2 *
          ∫ x in outer, well x ^ 2) * (volume A).toReal ^ β :=
      mul_le_mul_of_nonneg_right hcutoff hmeasurePow_nonneg
    _ ≤ ((zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
          ((8 * Lam / lam) + 2) * (32 / (R - r)) ^ 2 *
          ∫ x in outer, well x ^ 2) *
          ((∫ x in inner, wk x ^ 2) / (ell - k) ^ 2) ^ β :=
      mul_le_mul_of_nonneg_left hmeasurePow hcutoffRight_nonneg
    _ = (zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
          ((8 * Lam / lam) + 2) * (32 / (R - r)) ^ 2 *
          (∫ x in outer, well x ^ 2) *
          ((∫ x in inner, wk x ^ 2) / (ell - k) ^ 2) ^ β := by ring
    _ = (zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
          ((8 * Lam / lam) + 2) * (32 / (R - r)) ^ 2 *
          (∫ x in euclideanBall x₀ R, max (u x - ell) 0 ^ 2) *
          ((∫ x in euclideanBall x₀ r, max (u x - k) 0 ^ 2) /
            (ell - k) ^ 2) ^ (2 / (d : ℝ)) := by rfl

/-- The all-`k` outer-energy consequence of the exact mixed De Giorgi step.
This is the form consumed by the standard scalar nonlinear recurrence. -/
theorem setIntegral_positivePartSubConst_sq_ball_le_outer_energy_of_h10Subharmonic
    {d : ℕ} {lam Lam k ell r R : ℝ} {U : Set (Vec d)}
    {x₀ : Vec d} {a : CoeffField d} {u : H1Function U}
    (hd : 3 ≤ d) (hU : IsOpenBoundedConvexDomain U)
    (hr : 0 < r) (hrR : r < R)
    (hball : euclideanBall x₀ R ⊆ U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hlam : 0 < lam) (hLam : 0 ≤ Lam)
    (hsub : IsWeakDivergenceFormH10SubharmonicOn a U u)
    (hkell : k < ell) :
    (∫ x in euclideanBall x₀ r, max (u x - ell) 0 ^ 2) ≤
      (zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
          ((8 * Lam / lam) + 2) * (32 / (R - r)) ^ 2 *
          (∫ x in euclideanBall x₀ R, max (u x - k) 0 ^ 2) *
          ((∫ x in euclideanBall x₀ r, max (u x - k) 0 ^ 2) /
            (ell - k) ^ 2) ^ (2 / (d : ℝ)) := by
  let outer : Set (Vec d) := euclideanBall x₀ R
  let wk : Vec d → ℝ := fun x => max (u x - k) 0
  let well : Vec d → ℝ := fun x => max (u x - ell) 0
  let factor : ℝ :=
    ((∫ x in euclideanBall x₀ r, max (u x - k) 0 ^ 2) /
      (ell - k) ^ 2) ^ (2 / (d : ℝ))
  have hwkOuter : MemLp wk 2 (volume.restrict outer) := by
    simpa only [wk, outer, H1Function.positivePartSubConst_toFun] using
      memLpOn_mono hball (u.positivePartSubConst hU k).memL2
  have hwellOuter : MemLp well 2 (volume.restrict outer) := by
    simpa only [well, outer, H1Function.positivePartSubConst_toFun] using
      memLpOn_mono hball (u.positivePartSubConst hU ell).memL2
  have hwkSqInt : IntegrableOn (fun x => wk x ^ 2) outer := by
    simpa only [pow_two] using integrableOn_mul_of_memL2On hwkOuter hwkOuter
  have hwellSqInt : IntegrableOn (fun x => well x ^ 2) outer := by
    simpa only [pow_two] using integrableOn_mul_of_memL2On hwellOuter hwellOuter
  have houterEnergy :
      (∫ x in outer, well x ^ 2) ≤ ∫ x in outer, wk x ^ 2 := by
    apply integral_mono_ae hwellSqInt hwkSqInt
    exact Filter.Eventually.of_forall fun x => by
      have hle : well x ≤ wk x := by
        dsimp only [well, wk]
        apply max_le_max_right
        linarith
      have hwell_nonneg : 0 ≤ well x := by
        dsimp only [well]
        exact le_max_right _ _
      have hwk_nonneg : 0 ≤ wk x := by
        dsimp only [wk]
        exact le_max_right _ _
      nlinarith
  have hbase_nonneg :
      0 ≤ (zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
        ((8 * Lam / lam) + 2) * (32 / (R - r)) ^ 2 := by
    have hratio : 0 ≤ 8 * Lam / lam :=
      div_nonneg (mul_nonneg (by norm_num) hLam) hlam.le
    positivity
  have hfactor_nonneg : 0 ≤ factor := by
    dsimp only [factor]
    exact Real.rpow_nonneg (div_nonneg
      (integral_nonneg fun x => sq_nonneg (max (u x - k) 0))
      (sq_nonneg _)) _
  have hmixed :=
    setIntegral_positivePartSubConst_sq_ball_le_of_h10Subharmonic
      (u := u) (x₀ := x₀) (k := k) (ell := ell) hd hU hr hrR hball
      hEll hlam hLam hsub hkell
  have hproduct :
      ((zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
          ((8 * Lam / lam) + 2) * (32 / (R - r)) ^ 2 *
          ∫ x in outer, well x ^ 2) * factor ≤
        ((zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
          ((8 * Lam / lam) + 2) * (32 / (R - r)) ^ 2 *
          ∫ x in outer, wk x ^ 2) * factor := by
    apply mul_le_mul_of_nonneg_right _ hfactor_nonneg
    exact mul_le_mul_of_nonneg_left houterEnergy hbase_nonneg
  calc
    (∫ x in euclideanBall x₀ r, max (u x - ell) 0 ^ 2) ≤
        ((zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
          ((8 * Lam / lam) + 2) * (32 / (R - r)) ^ 2 *
          ∫ x in outer, well x ^ 2) * factor := by
      simpa only [outer, well, factor] using hmixed
    _ ≤ ((zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
          ((8 * Lam / lam) + 2) * (32 / (R - r)) ^ 2 *
          ∫ x in outer, wk x ^ 2) * factor := hproduct
    _ = (zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
          ((8 * Lam / lam) + 2) * (32 / (R - r)) ^ 2 *
          (∫ x in euclideanBall x₀ R, max (u x - k) 0 ^ 2) *
          ((∫ x in euclideanBall x₀ r, max (u x - k) 0 ^ 2) /
            (ell - k) ^ 2) ^ (2 / (d : ℝ)) := by rfl

/-- Homogeneous-solution wrapper for the all-`k` De Giorgi level-set step. -/
theorem setIntegral_positivePartSubConst_sq_ball_le_outer_energy_of_harmonic
    {d : ℕ} {lam Lam k ell r R : ℝ} {U : Set (Vec d)}
    {x₀ : Vec d} {a : CoeffField d} {u : H1Function U}
    (hd : 3 ≤ d) (hU : IsOpenBoundedConvexDomain U)
    (hr : 0 < r) (hrR : r < R)
    (hball : euclideanBall x₀ R ⊆ U)
    (hEll : IsEllipticFieldOn lam Lam U a)
    (hlam : 0 < lam) (hLam : 0 ≤ Lam)
    (hsol : IsWeakDivergenceFormHarmonicOn a U u)
    (hkell : k < ell) :
    (∫ x in euclideanBall x₀ r, max (u x - ell) 0 ^ 2) ≤
      (zeroBoundarySobolevConstantTwo d : ℝ) ^ 2 *
          ((8 * Lam / lam) + 2) * (32 / (R - r)) ^ 2 *
          (∫ x in euclideanBall x₀ R, max (u x - k) 0 ^ 2) *
          ((∫ x in euclideanBall x₀ r, max (u x - k) 0 ^ 2) /
            (ell - k) ^ 2) ^ (2 / (d : ℝ)) :=
  setIntegral_positivePartSubConst_sq_ball_le_outer_energy_of_h10Subharmonic
    (u := u) (x₀ := x₀) (k := k) (ell := ell) hd hU hr hrR hball hEll hlam hLam
    (hsol.toH10SubharmonicOn hEll) hkell

end PDE
