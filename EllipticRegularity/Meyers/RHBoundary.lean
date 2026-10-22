module

public import EllipticRegularity.Meyers.RHBoundaryStep

/-!
# The boundary reverse Hölder inequality (Lemma 4.5, part (ii))

For `u ∈ H¹₀(B₁)` solving `-∇⋅a∇u = ∇⋅f`, with `w = √(∇u ⬝ a∇u)` and `h = |f|²` extended
by zero outside `B₁`, every cube `Q = centeredAxisCube z r` satisfies
`∫_Q w² ≤ C₀ √Λ |Q| (avg_{4Q} w^{2θ})^{1/θ} + C₀ ∫_{4Q} h`, `θ = d/(d+1)`.

The four analytic inputs of the manuscript proof are hypotheses of the theorem:
* `hE` (energy bounds, (4.17)),
* `hSP` (the Sobolev–Poincaré inequality on cubes for the zero extension, (4.21)),
* `hcut` (the cutoff, Lemma 4.5), with a smooth cutoff and constant `Kη`,
* `hID` (the basic identity, Lemma 4.5).
-/

@[expose] public section

open MeasureTheory

namespace PDE

namespace MeyersRH

variable {d : ℕ}

/-- The constant `C₀` of the boundary reverse Hölder inequality; it depends only on `d`, the
Sobolev–Poincaré constant `S` and the cutoff constant `Kη`. -/
noncomputable def boundaryConstant (d : ℕ) (S Kη : ℝ) : ℝ :=
  24 * Kη * (1 + 2 ^ (d - 1)) * S * 4 ^ d + 1

theorem centeredAxisCube_subset_of_le (z : Vec d) {r s : ℝ} (h : r ≤ s) :
    centeredAxisCube z r ⊆ centeredAxisCube z s := by
  intro x hx i _
  have := hx i (Set.mem_univ i)
  constructor <;> dsimp <;> linarith [this.1, this.2]

theorem closedCenteredAxisCube_subset_cube (z : Vec d) {r : ℝ} (hr : 0 < r) :
    closedCenteredAxisCube z (3 * r / 2) ⊆ centeredAxisCube z (4 * r) :=
  (closedCenteredAxisCube_subset z hr).trans (centeredAxisCube_subset_of_le z (by linarith))

/-- **Boundary reverse Hölder inequality.** -/
theorem boundary_reverse_holder (hd : 2 ≤ d) (S Kη : ℝ) (hS : 0 ≤ S)
    (hcut : ∀ (z : Vec d) (r : ℝ), 0 < r → ∃ η : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧ (∀ x, 0 ≤ η x) ∧ (∀ x, η x ≤ 1) ∧
      (∀ x ∈ centeredAxisCube z r, η x = 1) ∧
      tsupport η ⊆ closedCenteredAxisCube z (3 * r / 2) ∧
      ∀ x, vecEuclideanNorm (classicalGradient η x) ≤ Kη / r)
    (Λ : ℝ) (hΛ : 1 ≤ Λ) (a : CoeffField d)
    (hA : ∀ i j : Fin d, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec d) 1)))
    (f : Vec d → Vec d)
    (hf : MemLp (fun x => vecEuclideanNorm (f x)) 2 (volumeOn (euclideanBall (0 : Vec d) 1)))
    (u : H10Function (euclideanBall (0 : Vec d) 1))
    (hE : ∀ x ∈ euclideanBall (0 : Vec d) 1,
      vecEuclideanNorm (u.grad x) ≤ wField a u x ∧
      vecEuclideanNorm (matVecMul (a x) (u.grad x)) ≤ Real.sqrt Λ * wField a u x ∧
      wField a u x ≤ Real.sqrt Λ * vecEuclideanNorm (u.grad x))
    (hSP : ∀ (z : Vec d) (ρ : ℝ), 0 < ρ →
      MemLp (fun x => uExt u x - integralAverage (centeredAxisCube z ρ) (uExt u))
        (ENNReal.ofReal (qDual d)) (volumeOn (centeredAxisCube z ρ)) ∧
      lpAvg (centeredAxisCube z ρ) (qDual d)
          (fun x => |uExt u x - integralAverage (centeredAxisCube z ρ) (uExt u)|) ≤
        S * (2 * ρ) * lpAvg (centeredAxisCube z ρ) (qExp d)
          (fun x => vecEuclideanNorm (gradExt u x)))
    (hID : ∀ (η : Vec d → ℝ) (c : ℝ), ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      (∀ x, 0 ≤ η x) →
      (∃ v : H10Function (euclideanBall (0 : Vec d) 1),
        v.toFun = fun x => η x * (u.toFun x - c)) →
      ∫ x in euclideanBall (0 : Vec d) 1, η x * wField a u x ^ 2 ≤
        2 * |∫ x in euclideanBall (0 : Vec d) 1, (u.toFun x - c) *
            vecDot (matVecMul (a x) (u.grad x) + f x) (classicalGradient η x)| +
          ∫ x in euclideanBall (0 : Vec d) 1, η x * vecEuclideanNorm (f x) ^ 2)
    (z : Vec d) (r : ℝ) (hr : 0 < r) :
    ∫ x in centeredAxisCube z r, gExt a u x ≤
      (boundaryConstant d S Kη * Real.sqrt Λ) * (volume (centeredAxisCube z r)).toReal *
          (integralAverage (centeredAxisCube z (4 * r))
            (fun x => gExt a u x ^ ((d : ℝ) / ((d : ℝ) + 1)))) ^ (((d : ℝ) + 1) / (d : ℝ)) +
        boundaryConstant d S Kη * ∫ x in centeredAxisCube z (4 * r), hExt f x := by
  have hB : MeasurableSet (euclideanBall (0 : Vec d) 1) := measurableSet_euclideanBall _ _
  have hPm : MeasurableSet (centeredAxisCube z (4 * r)) :=
    (isOpen_centeredAxisCube z _).measurableSet
  have hQm : MeasurableSet (centeredAxisCube z r) := (isOpen_centeredAxisCube z _).measurableSet
  have hPfin : volume (centeredAxisCube z (4 * r)) ≠ ⊤ := volume_centeredAxisCube_ne_top _ _
  have hV0 : 0 < (volume (centeredAxisCube z (4 * r))).toReal :=
    volume_centeredAxisCube_toReal_pos z (by positivity)
  have hd' : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  obtain ⟨hSP1, hSP2⟩ := hSP z (4 * r) (by positivity)
  obtain ⟨c, hadm, hc⟩ := exists_shift hd u z hr hSP1
  obtain ⟨η, hη, hηc, hη0, hη1, hηQ, hηs, hηg⟩ := hcut z r hr
  have hK : 0 ≤ Kη := by
    have h1 : 0 ≤ Kη / r := (vecEuclideanNorm_nonneg _).trans (hηg 0)
    have := mul_nonneg h1 hr.le
    rwa [div_mul_cancel₀ _ hr.ne'] at this
  obtain ⟨hstep, hint⟩ := boundary_step hd S hS Λ a hA f hf u
    (fun x hx => hE x hx) z r hr c hSP1 hSP2 hc
  obtain ⟨hgE, hhE, hsq⟩ := boundary_integrable hd Λ a hA f hf u
    (fun x hx => (hE x hx).2.2) _ hPfin
  have hID' := hID η c hη hηc hη0 (hadm η hη hηc hηs)
  -- support facts
  have hηP : ∀ x, x ∉ centeredAxisCube z (4 * r) → η x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport
      (fun h => hx (closedCenteredAxisCube_subset_cube z hr (hηs h)))
  have hgradP : ∀ x, x ∉ centeredAxisCube z (4 * r) → classicalGradient η x = 0 := by
    intro x hx
    funext i
    rw [classicalGradient_apply,
      fderiv_of_notMem_tsupport ℝ (fun h => hx (closedCenteredAxisCube_subset_cube z hr (hηs h)))]
    rfl
  set P := centeredAxisCube z (4 * r) with hP
  set L := Real.sqrt Λ with hLdef
  have hL1 : 1 ≤ L := by rw [hLdef]; exact Real.one_le_sqrt.mpr hΛ
  set V := (volume P).toReal with hVdef
  set H := ∫ x in P, hExt f x with hHdef
  set A := lpAvg P (qExp d) (wExt a u) with hAdef
  set Bb := lpAvg P (qExp d) (sExt f) with hBbdef
  set T := ∫ x in P, |uExt u x - c| * (L * wExt a u x + sExt f x) with hTdef
  have hA0 : 0 ≤ A := lpAvg_nonneg P _ (wExt_nonneg a u)
  have hB0 : 0 ≤ Bb := lpAvg_nonneg P _ (sExt_nonneg f)
  have hH0 : 0 ≤ H := setIntegral_nonneg hPm fun x _ => Set.indicator_nonneg
    (fun _ _ => sq_nonneg _) x
  -- (1) `∫_Q g ≤ ∫_P η g`
  have hηgE : IntegrableOn (fun x => η x * gExt a u x) P := by
    refine hgE.mono' (hη.continuous.aestronglyMeasurable.mul hgE.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => ?_)
    rw [Real.norm_of_nonneg (mul_nonneg (hη0 x) (gExt_nonneg a u x))]
    exact mul_le_of_le_one_left (gExt_nonneg a u x) (hη1 x)
  have h1 : ∫ x in centeredAxisCube z r, gExt a u x ≤ ∫ x in P, η x * gExt a u x := by
    calc ∫ x in centeredAxisCube z r, gExt a u x
        = ∫ x in centeredAxisCube z r, η x * gExt a u x :=
          setIntegral_congr_fun hQm fun x hx => by rw [hηQ x hx, one_mul]
      _ ≤ ∫ x in P, η x * gExt a u x :=
          setIntegral_mono_set hηgE
            (Filter.Eventually.of_forall fun x => mul_nonneg (hη0 x) (gExt_nonneg a u x))
            (Filter.Eventually.of_forall (centeredAxisCube_subset_of_le z (by linarith)))
  -- (2) `∫_P η g = ∫_B η w²`
  have h2 : ∫ x in P, η x * gExt a u x =
      ∫ x in euclideanBall (0 : Vec d) 1, η x * wField a u x ^ 2 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun x hx => by rw [hηP x hx, zero_mul]), ← integral_indicator hB]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ euclideanBall (0 : Vec d) 1
    · simp [gExt, Set.indicator_of_mem hx]
    · simp [gExt, Set.indicator_of_notMem hx]
  -- (3) the integral `J`
  have hD0 : ∀ x, 0 ≤ P.indicator (fun x => Kη / r *
      (|uExt u x - c| * (L * wExt a u x + sExt f x))) x := fun x =>
    Set.indicator_nonneg (fun x _ => mul_nonneg (div_nonneg hK hr.le)
      (mul_nonneg (abs_nonneg _) (add_nonneg (mul_nonneg (by linarith) (wExt_nonneg a u x))
        (sExt_nonneg f x)))) x
  have hDint : Integrable (P.indicator (fun x => Kη / r *
      (|uExt u x - c| * (L * wExt a u x + sExt f x)))) volume :=
    (integrable_indicator_iff hPm).mpr (hint.const_mul (Kη / r))
  have hpt : ∀ x, ‖(euclideanBall (0 : Vec d) 1).indicator (fun x => (u.toFun x - c) *
      vecDot (matVecMul (a x) (u.grad x) + f x) (classicalGradient η x)) x‖ ≤
      P.indicator (fun x => Kη / r *
        (|uExt u x - c| * (L * wExt a u x + sExt f x))) x := by
    intro x
    by_cases hxP : x ∈ P
    · rw [Set.indicator_of_mem hxP]
      by_cases hxB : x ∈ euclideanBall (0 : Vec d) 1
      · rw [Set.indicator_of_mem hxB]
        have hu : uExt u x = u.toFun x := by simp [uExt, Set.indicator_of_mem hxB]
        have hw : wExt a u x = wField a u x := by simp [wExt, Set.indicator_of_mem hxB]
        have hs : sExt f x = vecEuclideanNorm (f x) := by simp [sExt, Set.indicator_of_mem hxB]
        rw [hu, hw, hs, Real.norm_eq_abs, abs_mul]
        obtain ⟨_, e2, _⟩ := hE x hxB
        have hF : vecEuclideanNorm (matVecMul (a x) (u.grad x) + f x) ≤
            L * wField a u x + vecEuclideanNorm (f x) :=
          (vecEuclideanNorm_add_le _ _).trans (add_le_add e2 le_rfl)
        have hdot := abs_vecDot_le_vecEuclideanNorm_mul (matVecMul (a x) (u.grad x) + f x)
          (classicalGradient η x)
        have hgr := hηg x
        have hK' : 0 ≤ Kη / r := div_nonneg hK hr.le
        calc |u.toFun x - c| * |vecDot (matVecMul (a x) (u.grad x) + f x) (classicalGradient η x)|
            ≤ |u.toFun x - c| * ((L * wField a u x + vecEuclideanNorm (f x)) * (Kη / r)) := by
              refine mul_le_mul_of_nonneg_left (hdot.trans ?_) (abs_nonneg _)
              exact mul_le_mul hF hgr (vecEuclideanNorm_nonneg _)
                ((vecEuclideanNorm_nonneg _).trans hF)
          _ = _ := by ring
      · rw [Set.indicator_of_notMem hxB, norm_zero]
        exact (hD0 x).trans_eq (by rw [Set.indicator_of_mem hxP])
    · rw [Set.indicator_of_notMem hxP]
      by_cases hxB : x ∈ euclideanBall (0 : Vec d) 1
      · rw [Set.indicator_of_mem hxB, hgradP x hxP]
        simp [vecDot]
      · rw [Set.indicator_of_notMem hxB, norm_zero]
  have hJ : |∫ x in euclideanBall (0 : Vec d) 1, (u.toFun x - c) *
      vecDot (matVecMul (a x) (u.grad x) + f x) (classicalGradient η x)| ≤ Kη / r * T := by
    rw [← integral_indicator hB, ← Real.norm_eq_abs]
    calc _ ≤ ∫ x, P.indicator (fun x => Kη / r *
            (|uExt u x - c| * (L * wExt a u x + sExt f x))) x :=
          norm_integral_le_of_norm_le hDint (Filter.Eventually.of_forall hpt)
      _ = Kη / r * T := by
          rw [integral_indicator hPm, integral_const_mul]
  -- (4) `∫_B η h ≤ H`
  have h4 : ∫ x in euclideanBall (0 : Vec d) 1, η x * vecEuclideanNorm (f x) ^ 2 ≤ H := by
    rw [← integral_indicator hB]
    calc ∫ x, (euclideanBall (0 : Vec d) 1).indicator
          (fun x => η x * vecEuclideanNorm (f x) ^ 2) x
        ≤ ∫ x, P.indicator (hExt f) x := by
          refine integral_mono_of_nonneg
            (Filter.Eventually.of_forall fun x => Set.indicator_nonneg
              (fun x _ => mul_nonneg (hη0 x) (sq_nonneg _)) x)
            ((integrable_indicator_iff hPm).mpr hhE) (Filter.Eventually.of_forall fun x => ?_)
          by_cases hxB : x ∈ euclideanBall (0 : Vec d) 1
          · rw [Set.indicator_of_mem hxB]
            by_cases hxP : x ∈ P
            · rw [Set.indicator_of_mem hxP]
              simp only [hExt, Set.indicator_of_mem hxB]
              exact mul_le_of_le_one_left (sq_nonneg _) (hη1 x)
            · rw [Set.indicator_of_notMem hxP, hηP x hxP, zero_mul]
          · rw [Set.indicator_of_notMem hxB]
            exact Set.indicator_nonneg (fun x _ => Set.indicator_nonneg
              (fun _ _ => sq_nonneg _) x) x
      _ = H := integral_indicator hPm
  -- (5) Jensen for `s`
  have hθ0 : 0 < (d : ℝ) / ((d : ℝ) + 1) := by positivity
  have hθ1 : (d : ℝ) / ((d : ℝ) + 1) < 1 := by rw [div_lt_one (by positivity)]; linarith
  have hq2θ : qExp d = 2 * ((d : ℝ) / ((d : ℝ) + 1)) := by unfold qExp; ring
  have hJen : Bb ^ 2 ≤ V⁻¹ * H := by
    have hsq' : IntegrableOn (fun x => sExt f x ^ (2 * ((d : ℝ) / ((d : ℝ) + 1)))) P := by
      rw [← hq2θ]; exact hsq
    have := lpAvg_sq_le hθ0 hθ1 hV0 hPfin (sExt_nonneg f) hsq'
      (by simpa only [sExt_sq] using hhE)
    rw [← hq2θ] at this
    have e : ∫ x in P, sExt f x ^ (2 : ℕ) = H := by
      simp only [sExt_sq, hHdef]
    rw [e] at this
    exact this
  -- (6) identification of the averages of `g^θ`
  have hAsq : A ^ 2 = (integralAverage P
      (fun x => gExt a u x ^ ((d : ℝ) / ((d : ℝ) + 1)))) ^ (((d : ℝ) + 1) / (d : ℝ)) := by
    have h := lpAvg_sq_eq (P := P) hθ0 (wExt_nonneg a u)
    rw [← hq2θ] at h
    rw [hAdef, h, one_div_div]
    congr 1
    unfold integralAverage
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    rw [hq2θ]
    exact (gExt_rpow a u hθ0 x).symm
  have hVQ : V = 4 ^ d * (volume (centeredAxisCube z r)).toReal := by
    rw [hVdef, hP, volume_centeredAxisCube_toReal z (by positivity),
      volume_centeredAxisCube_toReal z hr.le, ← mul_pow]
    congr 1; ring
  -- assembly
  set κ : ℝ := (2 : ℝ) ^ (d - 1) with hκdef
  have hκ0 : 0 ≤ κ := by positivity
  set M := Kη * (1 + κ) * S with hMdef
  have hM0 : 0 ≤ M := by positivity
  have hJT : Kη / r * T ≤ 8 * M * V * (L * A ^ 2 + A * Bb) := by
    have := mul_le_mul_of_nonneg_left hstep (div_nonneg hK hr.le)
    refine this.trans (le_of_eq ?_)
    rw [hMdef]
    field_simp
    ring
  have hAB : A * Bb ≤ (A ^ 2 + Bb ^ 2) / 2 := by linarith [sq_nonneg (A - Bb)]
  have hA2L : A ^ 2 ≤ L * A ^ 2 := le_mul_of_one_le_left (sq_nonneg A) hL1
  have hVB : V * Bb ^ 2 ≤ H := by
    have := mul_le_mul_of_nonneg_left hJen hV0.le
    rwa [← mul_assoc, mul_inv_cancel₀ hV0.ne', one_mul] at this
  have hfinal : ∫ x in centeredAxisCube z r, gExt a u x ≤
      24 * M * V * L * A ^ 2 + 8 * M * H + H := by
    have h5 := h1.trans (h2.le.trans hID')
    have h6 : ∫ x in centeredAxisCube z r, gExt a u x ≤ 2 * (Kη / r * T) + H :=
      h5.trans (add_le_add (mul_le_mul_of_nonneg_left hJ (by norm_num)) h4)
    have hMV : 0 ≤ M * V := mul_nonneg hM0 hV0.le
    have h7 : 2 * (Kη / r * T) ≤ 16 * M * V * (L * A ^ 2 + A * Bb) := by
      linarith [hJT]
    have h16 : 0 ≤ 16 * M * V := by positivity
    have h8a := mul_le_mul_of_nonneg_left hAB h16
    have h8b := mul_le_mul_of_nonneg_left hA2L h16
    have h8 : 16 * M * V * (L * A ^ 2 + A * Bb) ≤
        24 * M * V * L * A ^ 2 + 8 * M * (V * Bb ^ 2) := by
      linarith
    have h9 : 8 * M * (V * Bb ^ 2) ≤ 8 * M * H :=
      mul_le_mul_of_nonneg_left hVB (by positivity)
    linarith
  -- comparison with `C₀`
  have hC0 : boundaryConstant d S Kη = 24 * M * 4 ^ d + 1 := by
    rw [boundaryConstant, hMdef, hκdef]; ring
  rw [← hAsq, hC0]
  have h4d : (1 : ℝ) ≤ 4 ^ d := one_le_pow₀ (by norm_num)
  have hvQ0 : 0 ≤ (volume (centeredAxisCube z r)).toReal := ENNReal.toReal_nonneg
  have hLA : 0 ≤ L * (volume (centeredAxisCube z r)).toReal * A ^ 2 := by positivity
  have hMH : 0 ≤ M * H := mul_nonneg hM0 hH0
  have e1 : 24 * M * V * L * A ^ 2 =
      24 * M * 4 ^ d * (L * (volume (centeredAxisCube z r)).toReal * A ^ 2) := by
    rw [hVQ]; ring
  have h10 := mul_nonneg hMH (sub_nonneg.mpr h4d)
  linarith [hfinal, e1, hLA, hMH, h10]

end MeyersRH

end PDE
