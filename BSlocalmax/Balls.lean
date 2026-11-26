module

public import BSlocalmax.CubeMain
public import PDEFoundation.Geometry.EuclideanBall.FiniteInteriorCover
public import PDEFoundation.Geometry.EuclideanBall.Interior
public import PDEFoundation.PDE.DGNM.Scaling

/-!
# From cubes to round balls

This file collects the following pieces, in dependency order: BlowUpGen, ScaledCube, BallMain.
-/

-- ==== from BlowUpGen.lean ====
/-!
# Blow-up onto an arbitrary open target set

`PDE.DGNM.blowUp` rescales an `H¹` function on `euclideanBall x₀ r` to the unit ball.
Here the target is an arbitrary open set `V`, as long as the affine image
`x₀ + r • V` lies in the domain `U`:

`ũ(y) = u(r • y + x₀)`, `y ∈ V`.

If `u` is a subsolution for `a` on `U`, then `ũ` is a subsolution for
`ã(y) = a(r • y + x₀)` on `V`; the proof is the one of `PDE.DGNM.subharmonicOn_blowUp`.
-/

@[expose] public section

open scoped Pointwise

namespace PDE.BSlocalmax

open MeasureTheory PDE PDE.DGNM

variable {d : ℕ}

theorem affine_mem_translateSet (x₀ : Vec d) {r : ℝ} {V : Set (Vec d)} {y : Vec d}
    (hy : y ∈ V) : r • y + x₀ ∈ translateSet x₀ (r • V) := by
  rw [mem_translateSet_iff_sub_mem, add_sub_cancel_right]
  exact Set.smul_mem_smul_set hy

theorem subset_dilate_of_image {U V : Set (Vec d)} (x₀ : Vec d) {r : ℝ}
    (hr : 0 < r) (hW : translateSet x₀ (r • V) ⊆ U) :
    V ⊆ r⁻¹ • translateSet (-x₀) U := by
  intro y hy
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ (inv_ne_zero hr.ne'),
    mem_translateSet_iff_sub_mem, inv_inv, sub_neg_eq_add]
  exact hW (affine_mem_translateSet x₀ hy)

/-- The blow-up `ũ(y) = u(r • y + x₀)` onto the open set `V`. -/
noncomputable def blowUpV {U : Set (Vec d)} (u : H1Function U) (x₀ : Vec d) {r : ℝ}
    (hr : 0 < r) {V : Set (Vec d)} (hV : IsOpen V)
    (hW : translateSet x₀ (r • V) ⊆ U) : H1Function V :=
  H1copy (r • (((u.translate (-x₀)).dilate (inv_pos.mpr hr)).restrict
      hV (subset_dilate_of_image x₀ hr hW))) rfl
    (fun y => u (r • y + x₀))
    (fun y => by
      simp only [H1Function.smul_toFun, H1Function.restrict_toFun,
        H1Function.dilate_toFun, H1Function.translate_toFun, inv_inv,
        sub_neg_eq_add]
      field_simp)
    (fun y => r • u.grad (r • y + x₀))
    (fun y => by
      simp only [H1Function.smul_grad, H1Function.restrict_grad,
        H1Function.dilate_grad, H1Function.translate_grad, inv_inv,
        sub_neg_eq_add])

@[simp]
theorem blowUpV_toFun {U : Set (Vec d)} (u : H1Function U) (x₀ : Vec d) {r : ℝ}
    (hr : 0 < r) {V : Set (Vec d)} (hV : IsOpen V)
    (hW : translateSet x₀ (r • V) ⊆ U) (y : Vec d) :
    (blowUpV u x₀ hr hV hW).toFun y = u (r • y + x₀) :=
  rfl

@[simp]
theorem blowUpV_grad {U : Set (Vec d)} (u : H1Function U) (x₀ : Vec d) {r : ℝ}
    (hr : 0 < r) {V : Set (Vec d)} (hV : IsOpen V)
    (hW : translateSet x₀ (r • V) ⊆ U) (y : Vec d) :
    (blowUpV u x₀ hr hV hW).grad y = r • u.grad (r • y + x₀) :=
  rfl

theorem blowUpCoeff_aemeasurable_V {U V : Set (Vec d)} {a : CoeffField d}
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn U)) (x₀ : Vec d) {r : ℝ}
    (hr : 0 < r) (hW : translateSet x₀ (r • V) ⊆ U) :
    ∀ i j, AEMeasurable (fun y => blowUpCoeff a x₀ r y i j) (volumeOn V) := by
  intro i j
  have hB : AEMeasurable (fun x => a x i j) (volumeOn (translateSet x₀ (r • V))) :=
    (ha i j).mono_measure (Measure.restrict_mono hW le_rfl)
  exact aemeasurable_comp_affineScale x₀ hr hB

theorem blowUpCoeff_elliptic_V {U V : Set (Vec d)} {Λ : ℝ} {a : CoeffField d}
    (hEll : ∀ x ∈ U, IsEllipticMatrix 1 Λ (a x)) (x₀ : Vec d) {r : ℝ}
    (hW : translateSet x₀ (r • V) ⊆ U) :
    ∀ y ∈ V, IsEllipticMatrix 1 Λ (blowUpCoeff a x₀ r y) := by
  intro y hy
  exact hEll _ (hW (affine_mem_translateSet x₀ hy))

/-! ### Pulled-back tests -/

/-- A smooth test on `V`, pulled back to `x₀ + r • V`: `ψ(x) = φ(r⁻¹ • (x - x₀))`. -/
noncomputable def pullTestV (x₀ : Vec d) {r : ℝ} (hr : 0 < r) {V : Set (Vec d)}
    (φ : WeakTestFunction V) : WeakTestFunction (translateSet x₀ (r • V)) where
  toFun := fun x => φ (r⁻¹ • (x - x₀))
  contDiff := φ.contDiff.comp ((contDiff_id.sub contDiff_const).const_smul r⁻¹)
  hasCompactSupport := by
    have hfun : (fun x => φ (r⁻¹ • (x - x₀))) =
        φ.toFun ∘ (affineScale x₀ hr.ne').symm := by
      funext x
      simp only [Function.comp_apply]
      congr 1
    rw [hfun]
    exact φ.hasCompactSupport.comp_homeomorph _
  tsupport_subset := by
    have hfun : (fun x => φ (r⁻¹ • (x - x₀))) =
        φ.toFun ∘ (affineScale x₀ hr.ne').symm := by
      funext x
      simp only [Function.comp_apply]
      congr 1
    intro x hx
    rw [hfun, tsupport_comp_eq_preimage] at hx
    have hy := φ.tsupport_subset hx
    have hmem := affine_mem_translateSet x₀ (r := r) hy
    have hx' : r • ((affineScale x₀ hr.ne').symm x) + x₀ = x := by
      rw [← affineScale_apply x₀ hr.ne', Homeomorph.apply_symm_apply]
    rwa [hx'] at hmem

theorem pullTestV_apply (x₀ : Vec d) {r : ℝ} (hr : 0 < r) {V : Set (Vec d)}
    (φ : WeakTestFunction V) (x : Vec d) :
    pullTestV x₀ hr φ x = φ (r⁻¹ • (x - x₀)) :=
  rfl

theorem pullTestV_grad (x₀ : Vec d) {r : ℝ} (hr : 0 < r) {V : Set (Vec d)}
    (φ : WeakTestFunction V) (x : Vec d) :
    (pullTestV x₀ hr φ).grad x = r⁻¹ • φ.grad (r⁻¹ • (x - x₀)) := by
  have hA : HasFDerivAt (fun x : Vec d => r⁻¹ • (x - x₀))
      (r⁻¹ • ContinuousLinearMap.id ℝ (Vec d)) x :=
    ((hasFDerivAt_id x).sub_const x₀).const_smul r⁻¹
  have hφd : HasFDerivAt φ.toFun (fderiv ℝ φ.toFun (r⁻¹ • (x - x₀)))
      (r⁻¹ • (x - x₀)) :=
    ((φ.contDiff.differentiable (by simp)) _).hasFDerivAt
  have hcomp := (hφd.comp x hA).fderiv
  funext i
  simp only [WeakTestFunction.grad_apply, WeakTestFunction.partialDeriv,
    Pi.smul_apply, smul_eq_mul]
  change fderiv ℝ (φ.toFun ∘ fun x : Vec d => r⁻¹ • (x - x₀)) x (basisVec i) = _
  rw [hcomp]
  simp only [ContinuousLinearMap.comp_apply, smul_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_eq_mul]

theorem pullTestV_nonnegative (x₀ : Vec d) {r : ℝ} (hr : 0 < r) {V : Set (Vec d)}
    {φ : WeakTestFunction V} (hφ : φ.Nonnegative) :
    (pullTestV x₀ hr φ).Nonnegative :=
  fun _ => hφ _

/-! ### The flux identity -/

theorem blowUpV_flux {U V : Set (Vec d)} {a : CoeffField d} (hUOpen : IsOpen U)
    (u : H1Function U) (x₀ : Vec d) {r : ℝ}
    (hr : 0 < r) (hV : IsOpen V) (hW : translateSet x₀ (r • V) ⊆ U)
    (φ : WeakTestFunction V)
    (hint : IntegrableOn (fun x => vecDot (matVecMul (a x) (u.grad x))
      ((extendTest hW (pullTestV x₀ hr φ)).grad x)) U) :
    IntegrableOn (fun y => vecDot (matVecMul (blowUpCoeff a x₀ r y)
        ((blowUpV u x₀ hr hV hW).grad y)) (φ.grad y)) V ∧
      ∫ y in V, vecDot (matVecMul (blowUpCoeff a x₀ r y)
          ((blowUpV u x₀ hr hV hW).grad y)) (φ.grad y) =
        r ^ 2 * (r ^ d)⁻¹ * ∫ x in U, vecDot (matVecMul (a x) (u.grad x))
          ((extendTest hW (pullTestV x₀ hr φ)).grad x) := by
  set F : Vec d → ℝ := fun x => vecDot (matVecMul (a x) (u.grad x))
    ((pullTestV x₀ hr φ).grad x) with hFdef
  have hpoint : ∀ y, vecDot (matVecMul (blowUpCoeff a x₀ r y)
      ((blowUpV u x₀ hr hV hW).grad y)) (φ.grad y) = r ^ 2 * F (r • y + x₀) := by
    intro y
    have hy : r⁻¹ • (r • y + x₀ - x₀) = y := by
      rw [add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    simp only [hFdef, blowUpCoeff_apply, blowUpV_grad, pullTestV_grad, hy,
      matVecMul_smul, vecDot_smul_left, vecDot_smul_right]
    field_simp
  rw [extendTest_grad] at hint ⊢
  have hFint : IntegrableOn F (translateSet x₀ (r • V)) := hint.mono_set hW
  have hcomp := integrableOn_comp_affineScale x₀ hr hFint
  refine ⟨?_, ?_⟩
  · simp_rw [hpoint]
    exact hcomp.const_mul _
  · simp_rw [hpoint]
    rw [integral_const_mul, setIntegral_comp_affineScale x₀ hr,
      setIntegral_vecDot_extendTest hUOpen.measurableSet hW]
    ring

/-! ### Class transport -/

/-- **Blow-up of a subharmonic function onto an open set `V`.** -/
theorem subharmonicOn_blowUpV {U V : Set (Vec d)} {a : CoeffField d} (hUOpen : IsOpen U)
    {u : H1Function U} (hsub : IsWeakDivergenceFormSubharmonicOn a U u) (x₀ : Vec d)
    {r : ℝ} (hr : 0 < r) (hV : IsOpen V) (hW : translateSet x₀ (r • V) ⊆ U) :
    IsWeakDivergenceFormSubharmonicOn (blowUpCoeff a x₀ r) V (blowUpV u x₀ hr hV hW) := by
  rw [subharmonicOn_iff] at hsub ⊢
  intro φ hφ
  obtain ⟨hi, hle⟩ := hsub (extendTest hW (pullTestV x₀ hr φ))
    (extendTest_nonnegative hW (pullTestV_nonnegative x₀ hr hφ))
  obtain ⟨hi', heq⟩ := blowUpV_flux hUOpen u x₀ hr hV hW φ hi
  refine ⟨hi', ?_⟩
  rw [heq]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hle

end PDE.BSlocalmax
end

-- ==== from ScaledCube.lean ====
/-!
# The cube estimate on rescaled round balls

For a subsolution `u` on an open set `U` and a round ball `B_R(x₀) ⊆ U`, put
`r = R / (2 √d)`.  The affine image `x₀ + r • Q_1` of the unit cube lies in `B_R(x₀)`, so the
cube estimate applies to the blow-up `ũ(y) = u(r • y + x₀)` on `Q_1`.  Transferring back,

`ess sup_{B_{r/2}(x₀)} u₊ ≤ C (ℓ(Λ) Λ)^{(d-1)/4} r^{-d/2} ‖u‖_{L²(B_R(x₀))}`.
-/

@[expose] public section

open scoped Pointwise

namespace PDE.BSlocalmax

open MeasureTheory PDE PDE.DGNM

variable {d : ℕ}

theorem volumeOn_mono {S T : Set (Vec d)} (h : S ⊆ T) : volumeOn S ≤ volumeOn T :=
  Measure.restrict_mono h le_rfl

theorem translateSet_smul_mono {S T : Set (Vec d)} (x₀ : Vec d) (r : ℝ) (h : S ⊆ T) :
    translateSet x₀ (r • S) ⊆ translateSet x₀ (r • T) := by
  rintro x ⟨y, hy, rfl⟩
  exact ⟨y, Set.smul_set_mono h hy, rfl⟩

set_option maxHeartbeats 800000 in
/-- **Cube estimate on rescaled round balls.** -/
theorem exists_scaled_cube_localMax (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ {U : Set (Vec d)}, IsOpen U → ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn U)) →
      (∀ x ∈ U, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function U, IsWeakDivergenceFormSubharmonicOn a U u →
      ∀ (x₀ : Vec d) (R : ℝ), 0 < R → euclideanBall x₀ R ⊆ U →
        essSup (fun x => ENNReal.ofReal (u.toFun x))
            (volumeOn (euclideanBall x₀ (R / (2 * Real.sqrt d) / 2))) ≤
          ENNReal.ofReal (C * (ell d Λ * Λ) ^ (((d : ℝ) - 1) / 4)) *
            (ENNReal.ofReal (((R / (2 * Real.sqrt d)) ^ d)⁻¹) ^ ((1 : ℝ) / 2) *
              eLpNorm u.toFun 2 (volumeOn (euclideanBall x₀ R))) := by
  obtain ⟨C, hC0, hC⟩ := exists_sharpLocalMax_constant d hd
  refine ⟨C, hC0, ?_⟩
  intro U hUo Λ a ha hEll u hsub x₀ R hR hball
  have hd0 : 0 < d := by omega
  have hsq : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd0)
  have hs : 0 < 2 * Real.sqrt d := by linarith
  obtain ⟨s, hsdef⟩ : ∃ s : ℝ, s = 2 * Real.sqrt d := ⟨_, rfl⟩
  obtain ⟨r, hrdef⟩ : ∃ r : ℝ, r = R / s := ⟨_, rfl⟩
  rw [← hsdef] at hs ⊢
  rw [← hrdef]
  have hr : 0 < r := by rw [hrdef]; exact div_pos hR hs
  have hrs : r * s = R := by rw [hrdef]; field_simp
  have hQ : Metric.ball (0 : Vec d) 1 ⊆ euclideanBall (0 : Vec d) s := by
    have h := centeredAxisCube_subset_euclideanBall hd0 (0 : Vec d) one_pos
    rw [centeredAxisCube_eq_metric_ball _ one_pos, mul_one] at h
    rw [hsdef]
    exact h
  have hW : translateSet x₀ (r • Metric.ball (0 : Vec d) 1) ⊆ euclideanBall x₀ R := by
    calc translateSet x₀ (r • Metric.ball (0 : Vec d) 1)
        ⊆ translateSet x₀ (r • euclideanBall (0 : Vec d) s) :=
          translateSet_smul_mono x₀ r hQ
      _ = euclideanBall x₀ (r * s) := translateSet_smul_euclideanBall x₀ hr s
      _ = euclideanBall x₀ R := by rw [hrs]
  have hWU : translateSet x₀ (r • Metric.ball (0 : Vec d) 1) ⊆ U := hW.trans hball
  have hHyp := hC Λ (blowUpCoeff a x₀ r)
    (blowUpCoeff_aemeasurable_V ha x₀ hr hWU)
    (blowUpCoeff_elliptic_V hEll x₀ hWU)
    (blowUpV u x₀ hr Metric.isOpen_ball hWU)
    (subharmonicOn_blowUpV hUo hsub x₀ hr Metric.isOpen_ball hWU)
  have hfun : (blowUpV u x₀ hr Metric.isOpen_ball hWU).toFun =
      fun y => u.toFun (r • y + x₀) := by
    funext y
    rfl
  rw [hfun] at hHyp
  -- left-hand side
  have hE : essSup (fun y => ENNReal.ofReal (u.toFun (r • y + x₀)))
        (volumeOn (Metric.ball (0 : Vec d) (1 / 2))) =
      essSup (fun x => ENNReal.ofReal (u.toFun x))
        (volumeOn (translateSet x₀ (r • Metric.ball (0 : Vec d) (1 / 2)))) :=
    essSup_comp_affineScale x₀ hr _ (fun x => ENNReal.ofReal (u.toFun x))
  have hin : euclideanBall x₀ (r / 2) ⊆
      translateSet x₀ (r • Metric.ball (0 : Vec d) (1 / 2)) := by
    have h1 : euclideanBall (0 : Vec d) (1 / 2) ⊆ Metric.ball (0 : Vec d) (1 / 2) :=
      euclideanBall_subset_supBall (by norm_num)
    have h2 := translateSet_smul_euclideanBall x₀ hr (1 / 2 : ℝ)
    have h3 : r * (1 / 2) = r / 2 := by ring
    rw [h3] at h2
    rw [← h2]
    exact translateSet_smul_mono x₀ r h1
  have hLHS : essSup (fun x => ENNReal.ofReal (u.toFun x))
        (volumeOn (euclideanBall x₀ (r / 2))) ≤
      essSup (fun y => ENNReal.ofReal (u.toFun (r • y + x₀)))
        (volumeOn (Metric.ball (0 : Vec d) (1 / 2))) := by
    rw [hE]
    exact essSup_mono_measure' (volumeOn_mono hin)
  -- right-hand side
  have h12 : (1 / (2 : ENNReal)).toReal = (1 : ℝ) / 2 := by
    norm_num [ENNReal.toReal_inv]
  have hN : eLpNorm (fun y => u.toFun (r • y + x₀)) 2
        (volumeOn (Metric.ball (0 : Vec d) 1)) =
      ENNReal.ofReal ((r ^ d)⁻¹) ^ ((1 : ℝ) / 2) *
        eLpNorm u.toFun 2 (volumeOn (translateSet x₀ (r • Metric.ball (0 : Vec d) 1))) := by
    rw [eLpNorm_comp_affineScale x₀ hr _ u.toFun 2, h12]
  have hN2 : eLpNorm u.toFun 2 (volumeOn (translateSet x₀ (r • Metric.ball (0 : Vec d) 1))) ≤
      eLpNorm u.toFun 2 (volumeOn (euclideanBall x₀ R)) :=
    eLpNorm_mono_measure u.toFun (volumeOn_mono hW)
  calc essSup (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (euclideanBall x₀ (r / 2)))
      ≤ essSup (fun y => ENNReal.ofReal (u.toFun (r • y + x₀)))
          (volumeOn (Metric.ball (0 : Vec d) (1 / 2))) := hLHS
    _ ≤ ENNReal.ofReal (C * (ell d Λ * Λ) ^ (((d : ℝ) - 1) / 4)) *
          eLpNorm (fun y => u.toFun (r • y + x₀)) 2
            (volumeOn (Metric.ball (0 : Vec d) 1)) := hHyp
    _ = ENNReal.ofReal (C * (ell d Λ * Λ) ^ (((d : ℝ) - 1) / 4)) *
          (ENNReal.ofReal ((r ^ d)⁻¹) ^ ((1 : ℝ) / 2) *
            eLpNorm u.toFun 2
              (volumeOn (translateSet x₀ (r • Metric.ball (0 : Vec d) 1)))) := by
        rw [hN]
    _ ≤ ENNReal.ofReal (C * (ell d Λ * Λ) ^ (((d : ℝ) - 1) / 4)) *
          (ENNReal.ofReal ((r ^ d)⁻¹) ^ ((1 : ℝ) / 2) *
            eLpNorm u.toFun 2 (volumeOn (euclideanBall x₀ R))) :=
        mul_le_mul' le_rfl (mul_le_mul' le_rfl hN2)

end PDE.BSlocalmax
end

-- ==== from BallMain.lean ====
/-!
# Sharp `L^∞`–`L²` estimate on round balls, `d ≥ 2`

Cover the closed half ball by finitely many round balls `B_z(ρ/2)`, `ρ = 1/(4√d)`, whose
`L²` balls `B_z(1/2)` stay inside the unit ball, and apply the rescaled cube estimate on each
of them.  The number of balls and `ρ` depend only on `d`.
-/

@[expose] public section

open scoped Pointwise

namespace PDE.BSlocalmax

open MeasureTheory PDE PDE.DGNM

set_option maxHeartbeats 800000 in
/-- **Sharp `L^∞` estimate for subsolutions on round balls, `d ≥ 2`.** With
`ℓ(s) = log(e+s)` if `d = 3` and `ℓ(s) = 1` otherwise,
`ess sup_{B_{1/2}} u₊ ≤ C (ℓ(Λ) Λ)^{(d-1)/4} ‖u‖_{L²(B_1)}`. -/
theorem exists_sharpLocalMax_constant_ball (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      IsWeakDivergenceFormSubharmonicOn a (euclideanBall (0 : Vec d) 1) u →
        essSup (fun x => ENNReal.ofReal (u.toFun x))
            (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
          ENNReal.ofReal (C * (ell d Λ * Λ) ^ (((d : ℝ) - 1) / 4)) *
            eLpNorm u.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1)) := by
  obtain ⟨C, hC0, hC⟩ := exists_scaled_cube_localMax d hd
  have hd0 : 0 < d := by omega
  have hsq : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd0)
  have hsq1 : (1 : ℝ) ≤ Real.sqrt d := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by exact_mod_cast (by omega : 1 ≤ d))
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = (1 / 2) / (2 * Real.sqrt d) := ⟨_, rfl⟩
  have hρ : 0 < ρ := by rw [hρdef]; positivity
  have hρ4 : ρ ≤ 1 / 4 := by
    rw [hρdef, div_le_iff₀ (by positivity)]
    linarith
  obtain ⟨s, hsz, hscover, -⟩ := exists_finset_euclideanBall_cover_closedHalf (d := d) hρ hρ4
  have hM : 0 ≤ (ρ ^ d)⁻¹ := inv_nonneg.2 (pow_nonneg hρ.le d)
  have hMh : 0 ≤ ((ρ ^ d)⁻¹) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg hM _
  refine ⟨C * ((ρ ^ d)⁻¹) ^ ((1 : ℝ) / 2),
    mul_pos hC0 (Real.rpow_pos_of_pos (inv_pos.2 (pow_pos hρ d)) _), ?_⟩
  intro Λ a ha hEll u hsub
  have hUo : IsOpen (euclideanBall (0 : Vec d) 1) := isOpen_euclideanBall _ _
  -- the common bound
  obtain ⟨c, hcdef⟩ : ∃ c : ENNReal, c =
      ENNReal.ofReal (C * (ell d Λ * Λ) ^ (((d : ℝ) - 1) / 4)) *
        (ENNReal.ofReal ((ρ ^ d)⁻¹) ^ ((1 : ℝ) / 2) *
          eLpNorm u.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1))) := ⟨_, rfl⟩
  have hpiece : ∀ z ∈ s,
      essSup (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (euclideanBall z (ρ / 2))) ≤ c := by
    intro z hz
    have hzc : z ∈ euclideanClosedBall (0 : Vec d) (1 / 2) := hsz z hz
    have hzn : vecEuclideanNorm (z - 0) ≤ 1 / 2 :=
      (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by norm_num)).1 hzc
    have hzball : euclideanBall z (1 / 2) ⊆ euclideanBall (0 : Vec d) 1 :=
      euclideanBall_subset_of_center_norm_add_le (by norm_num) (by norm_num) (by linarith)
    have h := hC hUo Λ a ha hEll u hsub z (1 / 2) (by norm_num) hzball
    rw [← hρdef] at h
    rw [hcdef]
    refine h.trans ?_
    exact mul_le_mul' le_rfl (mul_le_mul' le_rfl
      (eLpNorm_mono_measure u.toFun (volumeOn_mono hzball)))
  have hcov : euclideanBall (0 : Vec d) (1 / 2) ⊆ ⋃ z ∈ s, euclideanBall z (ρ / 2) :=
    (euclideanBall_subset_euclideanClosedBall _ _).trans hscover
  have hae : ∀ᵐ x ∂(volumeOn (⋃ z ∈ s, euclideanBall z (ρ / 2))),
      ENNReal.ofReal (u.toFun x) ≤ c := by
    show ∀ᵐ x ∂(Measure.restrict volume (⋃ z ∈ s, euclideanBall z (ρ / 2))),
      ENNReal.ofReal (u.toFun x) ≤ c
    rw [ae_restrict_biUnion_finset_iff]
    intro z hz
    exact (ENNReal.ae_le_essSup (fun x => ENNReal.ofReal (u.toFun x))).mono
      (fun x hx => hx.trans (hpiece z hz))
  have hfin : essSup (fun x => ENNReal.ofReal (u.toFun x))
      (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤ c :=
    (essSup_mono_measure' (volumeOn_mono hcov)).trans (essSup_le_of_ae_le c hae)
  refine hfin.trans (le_of_eq ?_)
  rw [hcdef]
  set N := eLpNorm u.toFun 2 (volumeOn (euclideanBall (0 : Vec d) 1)) with hN
  set X := (ell d Λ * Λ) ^ (((d : ℝ) - 1) / 4) with hX
  have e1 : ENNReal.ofReal (C * X) = ENNReal.ofReal C * ENNReal.ofReal X :=
    ENNReal.ofReal_mul hC0.le
  have e2 : ENNReal.ofReal (C * ((ρ ^ d)⁻¹) ^ ((1 : ℝ) / 2) * X) =
      ENNReal.ofReal C * ENNReal.ofReal (((ρ ^ d)⁻¹) ^ ((1 : ℝ) / 2)) * ENNReal.ofReal X := by
    rw [ENNReal.ofReal_mul (mul_nonneg hC0.le hMh), ENNReal.ofReal_mul hC0.le]
  rw [e1, e2, ENNReal.ofReal_rpow_of_nonneg hM (by norm_num)]
  ring

end PDE.BSlocalmax
end
