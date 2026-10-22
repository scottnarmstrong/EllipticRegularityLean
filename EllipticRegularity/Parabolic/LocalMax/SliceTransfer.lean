module

public import EllipticRegularity.Parabolic.Rescale.Affine
public import EllipticRegularity.Parabolic.Rescale.EssBounds
public import EllipticRegularity.Parabolic.Rescale.SpatialRestrict
public import EllipticRegularity.Parabolic.Moser.SliceOrderTimeSets
public import PDEFoundation.Measure.BallVolume

/-!
# From the unit-cylinder Harnack inequality to the slice form on general cylinders

A space-time Harnack bound on `B₁ × (-1, 0]` (assumed for every solution there) implies the
slice form of the parabolic local Harnack inequality on the cylinders
`B_{√(2θ)}((z+z')/2) × (τ - 3θ/2, τ + 5θ/4]`, by parabolic rescaling and transfer of
space-time bounds to time slices.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Parabolic.LocalMax

variable {d : ℕ}

/-- A point at squared distance `≤ θ/16` from the center rescales into the ball of squared
radius `1/32`. -/
theorem sqDist_rescale_le {w c : Vec d} {r θ : ℝ} (hθ : 0 < θ)
    (hr2 : r ^ 2 = 2 * θ) (h : euclideanSqDist w c ≤ θ / 16) :
    euclideanSqDist (r⁻¹ • (w - c)) 0 ≤ 1 / 32 := by
  have h1 := euclideanSqDist_smul_smul r⁻¹ (w - c) 0
  rw [smul_zero] at h1
  have h2 : euclideanSqDist (w - c) 0 = euclideanSqDist w c := by simp [euclideanSqDist]
  rw [h1, h2, inv_pow, hr2, inv_mul_le_iff₀ (by positivity)]
  linarith

theorem sqDist_left_midpoint (z z' : Vec d) :
    euclideanSqDist z ((1 / 2 : ℝ) • (z + z')) = euclideanSqDist z z' / 4 := by
  have h : z - (1 / 2 : ℝ) • (z + z') = (1 / 2 : ℝ) • (z - z') := by
    ext i; simp; ring
  have h2 := euclideanSqDist_smul_smul (1 / 2 : ℝ) (z - z') 0
  rw [smul_zero] at h2
  have h3 : euclideanSqDist (z - z') 0 = euclideanSqDist z z' := by simp [euclideanSqDist]
  have h4 : euclideanSqDist (z - (1 / 2 : ℝ) • (z + z')) 0 =
      euclideanSqDist z ((1 / 2 : ℝ) • (z + z')) := by simp [euclideanSqDist]
  rw [← h4, h, h2, h3]; ring

theorem sqDist_right_midpoint (z z' : Vec d) :
    euclideanSqDist z' ((1 / 2 : ℝ) • (z + z')) = euclideanSqDist z z' / 4 := by
  have h := sqDist_left_midpoint z' z
  rw [add_comm z' z, euclideanSqDist_comm z' z] at h
  exact h

/-- A closed ball of radius `ρ` with `ρ² = 1/32` around a point of squared norm `≤ 1/32`
lies in the ball of radius `3/8`. -/
theorem closedBall_subset_three_eighths {y : Vec d} {ρ : ℝ} (hρ : ρ ^ 2 = 1 / 32)
    (hy : euclideanSqDist y 0 ≤ 1 / 32) :
    euclideanClosedBall y ρ ⊆ euclideanBall (0 : Vec d) (3 / 8) := by
  intro x hx
  change euclideanSqDist x y ≤ ρ ^ 2 at hx
  change euclideanSqDist x 0 < (3 / 8) ^ 2
  have hx' : x = (1 / 2 : ℝ) • ((2 : ℝ) • (x - y)) + (1 / 2 : ℝ) • ((2 : ℝ) • y) := by
    ext i; simp
  have h := euclideanSqDist_weighted_add_le (a := 1 / 2) (b := 1 / 2) (by norm_num)
    (by norm_num) (by norm_num) ((2 : ℝ) • (x - y)) ((2 : ℝ) • y) 0
  rw [← hx'] at h
  have e1 := euclideanSqDist_smul_smul (2 : ℝ) (x - y) 0
  have e2 := euclideanSqDist_smul_smul (2 : ℝ) y 0
  rw [smul_zero] at e1 e2
  have e3 : euclideanSqDist (x - y) 0 = euclideanSqDist x y := by simp [euclideanSqDist]
  rw [e1, e3] at h
  rw [e2] at h
  rw [hρ] at hx
  nlinarith

/-- Real a.e. bounds extracted from the unit-cylinder Harnack bound. -/
theorem unit_bounds {ũ : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0)}
    {H : ℝ} (hH : 0 ≤ H)
    (hnn : ∀ᵐ w ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)),
      0 ≤ ũ.toFun w)
    (h : essSup (fun w => ENNReal.ofReal (ũ.toFun w))
          (volume.restrict (euclideanBall (0 : Vec d) (3 / 8) ×ˢ Ioo (-11 / 16 : ℝ) (-1 / 2))) ≤
        ENNReal.ofReal H * essInf (fun w => ENNReal.ofReal (ũ.toFun w))
          (volume.restrict (euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioc (-1 / 4 : ℝ) 0))) :
    ∃ M m : ℝ, M ≤ H * m ∧
      (∀ᵐ w ∂(volume.restrict (euclideanBall (0 : Vec d) (3 / 8) ×ˢ Ioo (-11 / 16 : ℝ) (-1 / 2))),
        ũ.toFun w ≤ M) ∧
      (∀ᵐ w ∂(volume.restrict (euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioc (-1 / 4 : ℝ) 0)),
        m ≤ ũ.toFun w) := by
  set ν := volume.restrict (euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioc (-1 / 4 : ℝ) 0) with hν
  set m := essInf (fun w => ENNReal.ofReal (ũ.toFun w)) ν with hm
  set M := essSup (fun w => ENNReal.ofReal (ũ.toFun w))
    (volume.restrict (euclideanBall (0 : Vec d) (3 / 8) ×ˢ Ioo (-11 / 16 : ℝ) (-1 / 2))) with hM
  have hν0 : ν ≠ 0 := by
    rw [hν, Ne, Measure.restrict_eq_zero, Measure.volume_eq_prod, Measure.prod_prod]
    exact mul_ne_zero (volume_euclideanBall_pos _ (by norm_num)).ne'
      (by rw [Real.volume_Ioc]; exact (ENNReal.ofReal_pos.2 (by norm_num)).ne')
  have hmtop : m < ⊤ := by
    have : (ae ν).NeBot := ae_neBot.2 hν0
    obtain ⟨w, hw⟩ := (ae_essInf_le (μ := ν) (f := fun w => ENNReal.ofReal (ũ.toFun w))).exists
    exact lt_of_le_of_lt hw ENNReal.ofReal_lt_top
  have hMtop : M ≠ ⊤ :=
    (lt_of_le_of_lt h (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hmtop)).ne
  have hmne : m ≠ ⊤ := hmtop.ne
  refine ⟨M.toReal, m.toReal, ?_, ?_, ?_⟩
  · have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hmne) h
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hH] at this
  · filter_upwards [ENNReal.ae_le_essSup (μ := volume.restrict
      (euclideanBall (0 : Vec d) (3 / 8) ×ˢ Ioo (-11 / 16 : ℝ) (-1 / 2)))
      (fun w => ENNReal.ofReal (ũ.toFun w))] with w hw
    exact (ENNReal.ofReal_le_iff_le_toReal hMtop).1 hw
  · have hnn' : ∀ᵐ w ∂ν, 0 ≤ ũ.toFun w := by
      refine ae_mono (Measure.restrict_mono (prod_mono ?_ ?_) le_rfl) hnn
      · exact euclideanBall_mono (by norm_num) (by norm_num)
      · intro s hs; exact ⟨by linarith [hs.1], hs.2⟩
    filter_upwards [ae_essInf_le (μ := ν) (f := fun w => ENNReal.ofReal (ũ.toFun w)), hnn']
      with w hw hw0
    exact ENNReal.toReal_le_of_le_ofReal hw0 hw

/-- Slice form of the parabolic local Harnack inequality from the unit-cylinder bound. -/
theorem localHarnack_of_unitHarnack (d : ℕ) (Lam H : ℝ) (hH : 0 ≤ H)
    (hunit : ∀ ã : ParCoeffField d,
      IsParabolicCoeff 1 Lam ã (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) →
      ∀ ũ : ParH1Function (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0),
      IsParabolicWeakSolution ã (euclideanBall (0 : Vec d) 1) (Ioc (-1 : ℝ) 0) ũ →
      (∀ᵐ w ∂(volume.restrict (euclideanBall (0 : Vec d) 1 ×ˢ Ioc (-1 : ℝ) 0)), 0 ≤ ũ.toFun w) →
      essSup (fun w => ENNReal.ofReal (ũ.toFun w))
          (volume.restrict (euclideanBall (0 : Vec d) (3 / 8) ×ˢ Ioo (-11 / 16 : ℝ) (-1 / 2))) ≤
        ENNReal.ofReal H * essInf (fun w => ENNReal.ofReal (ũ.toFun w))
          (volume.restrict (euclideanBall (0 : Vec d) (1 / 2) ×ˢ Ioc (-1 / 4 : ℝ) 0))) :
    ∀ (a : ParCoeffField d) (τ θ : ℝ), 0 < θ → ∀ z z' : Vec d,
      euclideanSqDist z z' ≤ θ / 4 →
      IsParabolicCoeff 1 Lam a
        (euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (2 * θ)))
        (Ioc (τ - 3 * θ / 2) (τ + 5 * θ / 4)) →
      ∀ u : ParH1Function (euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (2 * θ)))
        (Ioc (τ - 3 * θ / 2) (τ + 5 * θ / 4)),
      IsParabolicWeakSolution a (euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (2 * θ)))
        (Ioc (τ - 3 * θ / 2) (τ + 5 * θ / 4)) u →
      (∀ᵐ w ∂(volume.restrict (euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (2 * θ)) ×ˢ
        Ioc (τ - 3 * θ / 2) (τ + 5 * θ / 4))), 0 ≤ u.toFun w) →
        essSup (fun x : Vec d => ENNReal.ofReal (u.toFun (x, τ)))
            (volume.restrict (euclideanBall z (Real.sqrt θ / 4))) ≤
          ENNReal.ofReal H *
            essInf (fun x : Vec d => ENNReal.ofReal (u.toFun (x, τ + θ)))
              (volume.restrict (euclideanBall z' (Real.sqrt θ / 4))) := by
  intro a τ θ hθ z z' hzz
  set c : Vec d := (1 / 2 : ℝ) • (z + z') with hc
  set r : ℝ := Real.sqrt (2 * θ) with hr_def
  intro ha u hu hpos
  have hr : 0 < r := Real.sqrt_pos.2 (by positivity)
  have hr2 : r ^ 2 = 2 * θ := Real.sq_sqrt (by positivity)
  have hI' : Ioc ((τ + 5 * θ / 4) - r ^ 2) (τ + 5 * θ / 4) ⊆ Ioc (τ - 3 * θ / 2) (τ + 5 * θ / 4) := by
    rw [hr2]
    intro s hs
    exact ⟨by linarith [hs.1], hs.2⟩
  obtain ⟨ã, ũ, hã, hũ, hval, hnn⟩ := Rescale.exists_unit_rescaling a c hr (τ + 5 * θ / 4)
    measurableSet_Ioc hI' ha u hu
  obtain ⟨M, m, hMm, hup, hlo⟩ := unit_bounds hH (hnn hpos) (hunit ã hã ũ hũ (hnn hpos))
  -- geometry
  set ρ₀ : ℝ := (Real.sqrt θ / 4) / r with hρ₀
  have hsθ : 0 < Real.sqrt θ := Real.sqrt_pos.2 hθ
  have hrρ : r * ρ₀ = Real.sqrt θ / 4 := by rw [hρ₀]; field_simp
  have hρ₀2 : ρ₀ ^ 2 = 1 / 32 := by
    rw [hρ₀, div_pow, div_pow, hr2, Real.sq_sqrt hθ.le]
    field_simp; norm_num
  have hρ₀0 : 0 ≤ ρ₀ := by positivity
  set y : Vec d := r⁻¹ • (z - c) with hy
  set y' : Vec d := r⁻¹ • (z' - c) with hy'
  have hyc : c + r • y = z := by
    rw [hy, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]; abel
  have hy'c : c + r • y' = z' := by
    rw [hy', smul_smul, mul_inv_cancel₀ hr.ne', one_smul]; abel
  have hyn : euclideanSqDist y 0 ≤ 1 / 32 := by
    refine sqDist_rescale_le hθ hr2 ?_
    rw [hc, sqDist_left_midpoint]; linarith
  have hy'n : euclideanSqDist y' 0 ≤ 1 / 32 := by
    refine sqDist_rescale_le hθ hr2 ?_
    rw [hc, sqDist_right_midpoint]; linarith
  have hK₀ := closedBall_subset_three_eighths hρ₀2 hyn
  have hK₁ := closedBall_subset_three_eighths hρ₀2 hy'n
  have hV : euclideanBall (0 : Vec d) (3 / 8) ⊆ euclideanBall (0 : Vec d) 1 :=
    euclideanBall_mono (by norm_num) (by norm_num)
  have hJ₀ : Ioo (-11 / 16 : ℝ) (-1 / 2) ⊆ Ioc (-1 : ℝ) 0 := by
    intro s hs; exact ⟨by linarith [hs.1], by linarith [hs.2]⟩
  have hJ₁ : Ioc (-1 / 4 : ℝ) 0 ⊆ Ioc (-1 : ℝ) 0 := by
    intro s hs; exact ⟨by linarith [hs.1], hs.2⟩
  have hlo' : ∀ᵐ w ∂(volume.restrict (euclideanBall (0 : Vec d) (3 / 8) ×ˢ Ioc (-1 / 4 : ℝ) 0)),
      m ≤ ũ.toFun w :=
    ae_mono (Measure.restrict_mono (prod_mono (euclideanBall_mono (by norm_num) (by norm_num))
      subset_rfl) le_rfl) hlo
  have key := Moser.parH1_two_time_slice_harnack_of_separate_time_bounds hJ₀ hJ₁
    measurableSet_Ioo measurableSet_Ioc (Rescale.restrictParH1Space hV ũ) hH hMm hup hlo'
    (isCompact_euclideanClosedBall y hρ₀0) (isCompact_euclideanClosedBall y' hρ₀0) hK₀ hK₁
    (t₀ := -5 / 8) (t₁ := -1 / 8)
    (by rw [interior_Ioo]; constructor <;> norm_num)
    (by rw [interior_Ioc]; constructor <;> norm_num)
  have ht0 : (τ + 5 * θ / 4) + r ^ 2 * (-5 / 8) = τ := by rw [hr2]; ring
  have ht1 : (τ + 5 * θ / 4) + r ^ 2 * (-1 / 8) = τ + θ := by rw [hr2]; ring
  have eS : essSup (fun x : Vec d => ENNReal.ofReal (u.toFun (x, τ)))
      (volume.restrict (euclideanBall z (Real.sqrt θ / 4))) =
      essSup (fun x : Vec d => ENNReal.ofReal (ũ.toFun (x, -5 / 8)))
        (volume.restrict (euclideanBall y ρ₀)) := by
    have := Rescale.essSup_comp_affine_euclideanBall
      (fun x : Vec d => ENNReal.ofReal (u.toFun (x, τ))) c y hr ρ₀
    rw [hyc, hrρ] at this
    rw [← this]
    congr 1
    funext x
    rw [hval, ht0]
  have eI : essInf (fun x : Vec d => ENNReal.ofReal (u.toFun (x, τ + θ)))
      (volume.restrict (euclideanBall z' (Real.sqrt θ / 4))) =
      essInf (fun x : Vec d => ENNReal.ofReal (ũ.toFun (x, -1 / 8)))
        (volume.restrict (euclideanBall y' ρ₀)) := by
    have := Rescale.essInf_comp_affine_euclideanBall
      (fun x : Vec d => ENNReal.ofReal (u.toFun (x, τ + θ))) c y' hr ρ₀
    rw [hy'c, hrρ] at this
    rw [← this]
    congr 1
    funext x
    rw [hval, ht1]
  rw [eS, eI]
  refine le_trans (essSup_mono_measure' (Measure.restrict_mono
    (euclideanBall_subset_euclideanClosedBall y ρ₀) le_rfl)) (key.trans ?_)
  refine mul_le_mul_right (essInf_antitone_measure
    (Measure.restrict_mono (euclideanBall_subset_euclideanClosedBall y' ρ₀)
      le_rfl).absolutelyContinuous) _

end PDE.Parabolic.LocalMax
