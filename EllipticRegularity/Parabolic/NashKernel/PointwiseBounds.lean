module

public import EllipticRegularity.Parabolic.NashKernel.PointwiseBall
public import Ch5NashStatements.NashLower

/-!
# Pointwise Gaussian bounds for a representing kernel

If a jointly measurable `P` with `0 ≤ P ≤ M` represents `cauchyOp` on indicators of bounded
measurable sets, then `P` satisfies the two-sided Gaussian bounds of the Nash-Aronson kernel
statement at a.e. `(x, y)`.  The proof averages `P` over the product cube
`closedBall (x, y) δ` (here `Metric.closedBall` on `Vec d` is a supremum-norm cube, on purpose),
applies the tested upper and lower bounds to the indicators of the two factor cubes, and lets
`δ → 0⁺` (Lebesgue differentiation on `Vec d × Vec d`).
-/

@[expose] public section

namespace PDE.Parabolic.NashKernel

open MeasureTheory Metric Set Filter Topology

variable {d : ℕ}

/-- Two-sided bounds on the average of a representing kernel over a small product cube. -/
theorem average_bounds_of_representation {C Lam c β : ℝ} (hLam : 1 ≤ Lam)
    (hup : ∀ (a : ParCoeffField d) (s t : ℝ), s < t →
      IsParabolicCoeff 1 Lam a univ (Icc s t) →
      ∀ r : ℝ, 0 ≤ r → ∀ f g : Vec d → ℝ,
      Integrable f volume → MemLp f 2 volume → Integrable g volume → MemLp g 2 volume →
      ∀ Kf Kg : Set (Vec d), (∀ᵐ x : Vec d, x ∉ Kf → f x = 0) → (∀ᵐ x : Vec d, x ∉ Kg → g x = 0) →
      (∀ x ∈ Kf, ∀ y ∈ Kg, r ^ 2 ≤ euclideanSqDist x y) →
      ∀ u : ParH1Function (univ : Set (Vec d)) (Icc s t), IsCauchySolution a s t f u →
        Integrable (fun x => g x * u.toFun (x, t)) volume ∧
        |∫ x, g x * u.toFun (x, t)| ≤
          C * (t - s) ^ (-(d : ℝ) / 2) *
            Real.exp (-r ^ 2 / (4 * Lam * (t - s)) +
              Real.sqrt (((d : ℝ) + 2) / 2) * r / Real.sqrt (Lam * (t - s))) *
            ((∫ x, |f x|) * ∫ x, |g x|))
    (hC : 0 ≤ C)
    (hlow : ∀ (a : ParCoeffField d) (s t : ℝ), s < t →
      IsParabolicCoeff 1 Lam a univ (Icc s t) →
      ∀ (x y : Vec d) (f g : Vec d → ℝ),
      Integrable f volume → MemLp f 2 volume → Integrable g volume → MemLp g 2 volume →
      (∀ᵐ z : Vec d, 0 ≤ f z) → (∀ᵐ z : Vec d, 0 ≤ g z) →
      (∀ᵐ z : Vec d, z ∉ euclideanBall y (Real.sqrt (t - s) / 8) → f z = 0) →
      (∀ᵐ z : Vec d, z ∉ euclideanBall x (Real.sqrt (t - s) / 8) → g z = 0) →
      ∀ u : ParH1Function (univ : Set (Vec d)) (Icc s t), IsCauchySolution a s t f u →
        c * (t - s) ^ (-(d : ℝ) / 2) * Real.exp (-β * euclideanSqDist x y / (t - s)) *
            ((∫ z, f z) * ∫ z, g z) ≤ ∫ z, g z * u.toFun (z, t))
    {a : ParCoeffField d} {s t : ℝ} (hst : s < t)
    (ha : IsParabolicCoeff 1 Lam a univ (Icc s t)) {P : Vec d → Vec d → ℝ} {M : ℝ}
    (hP : Measurable (Function.uncurry P)) (hM : ∀ x y, |P x y| ≤ M)
    (hrep : ∀ B : Set (Vec d), MeasurableSet B → Bornology.IsBounded B →
      cauchyOp a s t (B.indicator 1) =ᵐ[volume] fun x => ∫ y in B, P x y)
    (x y : Vec d) {δ : ℝ} (hδ : 0 < δ) (hsmall : Real.sqrt d * δ < Real.sqrt (t - s) / 8) :
    c * (t - s) ^ (-(d : ℝ) / 2) * Real.exp (-β * euclideanSqDist x y / (t - s)) ≤
        ⨍ q in closedBall (x, y) δ, Function.uncurry P q ∧
      ⨍ q in closedBall (x, y) δ, Function.uncurry P q ≤
        C * Real.exp ((d : ℝ) + 2) * (t - s) ^ (-(d : ℝ) / 2) *
          Real.exp (-(max 0 (Real.sqrt (euclideanSqDist x y) - 2 * Real.sqrt d * δ)) ^ 2 /
            (8 * Lam * (t - s))) := by
  have hh : 0 < t - s := sub_pos.2 hst
  have hV : 0 < (2 * δ) ^ d := pow_pos (by linarith) _
  have hVV : 0 < (2 * δ) ^ d * (2 * δ) ^ d := mul_pos hV hV
  obtain ⟨u, hu, hcu⟩ := exists_cauchyOp_eq hst ha (memLp_indicator_closedBall y δ)
  have hI : ∫ q in closedBall (x, y) δ, Function.uncurry P q =
      ∫ z, (closedBall x δ).indicator (1 : Vec d → ℝ) z * u.toFun (z, t) := by
    rw [setIntegral_closedBall_prod_eq hP hM hrep x y δ, hcu]
  have havg : ⨍ q in closedBall (x, y) δ, Function.uncurry P q =
      ((2 * δ) ^ d * (2 * δ) ^ d)⁻¹ *
        ∫ z, (closedBall x δ).indicator (1 : Vec d → ℝ) z * u.toFun (z, t) := by
    rw [setAverage_eq, hI, measureReal_def,
      PDE.NashKernelGeometry.volume_closedBall_prod_eq x y hδ.le, ← ENNReal.ofReal_mul hV.le,
      ENNReal.toReal_ofReal hVV.le, smul_eq_mul]
  rw [havg]
  have hIf := integral_indicator_closedBall y hδ.le
  have hIg := integral_indicator_closedBall x hδ.le
  have hAf := integral_abs_indicator_closedBall y hδ.le
  have hAg := integral_abs_indicator_closedBall x hδ.le
  constructor
  · have hl := hlow a s t hst ha x y _ _ (integrable_indicator_closedBall y δ)
      (memLp_indicator_closedBall y δ) (integrable_indicator_closedBall x δ)
      (memLp_indicator_closedBall x δ)
      (Filter.Eventually.of_forall fun z => Set.indicator_nonneg (fun _ _ => zero_le_one) z)
      (Filter.Eventually.of_forall fun z => Set.indicator_nonneg (fun _ _ => zero_le_one) z)
      (Filter.Eventually.of_forall fun z hz => Set.indicator_of_notMem
        (fun hz' => hz (PDE.NashKernelGeometry.closedBall_subset_euclideanBall hsmall hz')) _)
      (Filter.Eventually.of_forall fun z hz => Set.indicator_of_notMem
        (fun hz' => hz (PDE.NashKernelGeometry.closedBall_subset_euclideanBall hsmall hz')) _) u hu
    rw [hIf, hIg] at hl
    calc _ = ((2 * δ) ^ d * (2 * δ) ^ d)⁻¹ *
          (c * (t - s) ^ (-(d : ℝ) / 2) * Real.exp (-β * euclideanSqDist x y / (t - s)) *
            ((2 * δ) ^ d * (2 * δ) ^ d)) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hl (inv_nonneg.2 hVV.le)
  · set r := max 0 (Real.sqrt (euclideanSqDist x y) - 2 * Real.sqrt d * δ) with hr
    have hup' := hup a s t hst ha r (le_max_left _ _) _ _ (integrable_indicator_closedBall y δ)
      (memLp_indicator_closedBall y δ) (integrable_indicator_closedBall x δ)
      (memLp_indicator_closedBall x δ) (closedBall y δ) (closedBall x δ)
      (Filter.Eventually.of_forall fun z hz => Set.indicator_of_notMem hz _)
      (Filter.Eventually.of_forall fun z hz => Set.indicator_of_notMem hz _)
      (fun x' hx' y' hy' => by
        rw [euclideanSqDist_comm]
        exact PDE.NashKernelGeometry.sq_max_le_euclideanSqDist hy' hx') u hu
    rw [hAf, hAg] at hup'
    have habs := PDE.NashKernelGeometry.upper_bound_absorbed d (C := C) (r := r) (Lam := Lam)
      (h := t - s) hC (by linarith) hh
    calc _ ≤ ((2 * δ) ^ d * (2 * δ) ^ d)⁻¹ *
          (C * (t - s) ^ (-(d : ℝ) / 2) *
            Real.exp (-r ^ 2 / (4 * Lam * (t - s)) +
              Real.sqrt (((d : ℝ) + 2) / 2) * r / Real.sqrt (Lam * (t - s))) *
            ((2 * δ) ^ d * (2 * δ) ^ d)) :=
          mul_le_mul_of_nonneg_left ((le_abs_self _).trans hup'.2) (inv_nonneg.2 hVV.le)
      _ = C * (t - s) ^ (-(d : ℝ) / 2) *
            Real.exp (-r ^ 2 / (4 * Lam * (t - s)) +
              Real.sqrt (((d : ℝ) + 2) / 2) * r / Real.sqrt (Lam * (t - s))) := by field_simp
      _ ≤ _ := habs

/-- **Pointwise Gaussian bounds for a representing kernel.**  `C` depends only on `d`; `c, β` only
on `(d, Λ)`.  If a jointly measurable `P` with `0 ≤ P ≤ M` represents `cauchyOp` on indicators of
bounded measurable sets, then for a.e. `(x, y)` the Nash-Aronson Gaussian bounds hold. -/
theorem kernel_gaussian_bounds_of_representation (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ Lam : ℝ, 1 ≤ Lam → ∃ c β : ℝ, 0 < c ∧ 0 < β ∧
      ∀ (a : ParCoeffField d) (s t : ℝ), s < t → IsParabolicCoeff 1 Lam a univ (Icc s t) →
      ∀ (M : ℝ) (P : Vec d → Vec d → ℝ), Measurable (Function.uncurry P) →
      (∀ x y, 0 ≤ P x y ∧ P x y ≤ M) →
      (∀ B : Set (Vec d), MeasurableSet B → Bornology.IsBounded B →
        cauchyOp a s t (B.indicator 1) =ᵐ[volume] fun x => ∫ y in B, P x y) →
      ∀ᵐ p ∂((volume : Measure (Vec d)).prod volume),
        c * (t - s) ^ (-(d : ℝ) / 2) * Real.exp (-β * euclideanSqDist p.1 p.2 / (t - s)) ≤
            P p.1 p.2 ∧
          P p.1 p.2 ≤ C * Real.exp ((d : ℝ) + 2) * (t - s) ^ (-(d : ℝ) / 2) *
            Real.exp (-euclideanSqDist p.1 p.2 / (8 * Lam * (t - s))) := by
  obtain ⟨C, hC, hup⟩ := PDE.nashAronsonUpper d hd
  refine ⟨C, hC, fun Lam hLam => ?_⟩
  obtain ⟨c, β, hc, hβ, hlow⟩ := PDE.nashAronsonLower d hd Lam hLam
  refine ⟨c, β, hc, hβ, fun a s t hst ha M P hP hPM hrep => ?_⟩
  have hh : 0 < t - s := sub_pos.2 hst
  have hM : ∀ x y, |P x y| ≤ M := fun x y => by
    rw [abs_of_nonneg (hPM x y).1]; exact (hPM x y).2
  have hloc := locallyIntegrable_of_bounded hP (M := M) (fun q => hM q.1 q.2)
  have hε : 0 < Real.sqrt (t - s) / 8 / (Real.sqrt d + 1) := by positivity
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), 0 < δ ∧ Real.sqrt d * δ < Real.sqrt (t - s) / 8 := by
    filter_upwards [Ioo_mem_nhdsGT hε] with δ hδ
    refine ⟨hδ.1, ?_⟩
    have h1 := hδ.2
    rw [lt_div_iff₀ (by positivity)] at h1
    nlinarith [hδ.1]
  filter_upwards [PDE.NashKernelGeometry.ae_tendsto_average_closedBall_prod hloc (l := 𝓝[>] 0)
    (fun δ : ℝ => δ) tendsto_id] with p hp
  have hb := fun δ (hδ : 0 < δ ∧ Real.sqrt d * δ < Real.sqrt (t - s) / 8) =>
    average_bounds_of_representation hLam (hup Lam hLam) hC.le hlow hst ha hP hM hrep p.1 p.2 hδ.1 hδ.2
  refine ⟨ge_of_tendsto hp (hev.mono fun δ h => (hb δ h).1), ?_⟩
  have hρ : 0 ≤ Real.sqrt (euclideanSqDist p.1 p.2) := Real.sqrt_nonneg _
  have hlim := PDE.NashKernelGeometry.tendsto_upper_gaussian d (C * Real.exp ((d : ℝ) + 2)) Lam
    (t - s) hρ
  rw [Real.sq_sqrt (euclideanSqDist_nonneg _ _)] at hlim
  exact le_of_tendsto_of_tendsto hp hlim (hev.mono fun δ h => (hb δ h).2)

end PDE.Parabolic.NashKernel
