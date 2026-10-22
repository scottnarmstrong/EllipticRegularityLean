module

public import PDEFoundation.Euler.WeakProduct
public import PDEFoundation.Euler.TimeProduct

/-!
# Weak continuity at time zero

For a weak solution `u` with datum `v₀` and a smooth periodic divergence-free `ζ`, the time-mollified
pairings converge to the datum: `∫₀ᵀ χ(τ) η_n(τ) ⟨u(τ),ζ⟩ dτ → ½ χ(0) ⟨v₀,ζ⟩`.
(`η_n` is even, so only half of its mass lies in `[0,T]`.)  Proof: test the weak formulation with the
cut-off `θ_n = χ · thetaK n` (`thetaK n' = -η_n`, `thetaK n 0 = 1/2`) and use dominated convergence.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology

namespace PDE

theorem integrable_cont_mul_time {T : ℝ} {g h : ℝ → ℝ} (hg : Continuous g)
    (hh : Integrable h (volume.restrict (Icc (0 : ℝ) T))) :
    Integrable (fun τ => g τ * h τ) (volume.restrict (Icc (0 : ℝ) T)) := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).exists_bound_of_continuousOn hg.continuousOn
  exact hh.bdd_mul hg.aestronglyMeasurable
    ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall hC))

theorem weak_cont_zero {T : ℝ} (hT : 0 < T) {v₀ : Vec 2 → Vec 2} {u : Vec 2 × ℝ → Vec 2}
    (hu : IsEulerWeakSolutionWithDatum T v₀ u) {B : ℝ}
    (hB : ∀ᵐ z ∂(eulerMeasure T), vecNormSq (u z) ≤ B)
    {ζ : Vec 2 → Vec 2} (hζ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => ζ x i)) (hζp : IsTorusPeriodic ζ)
    (hζd : ∀ x, torusDiv ζ x = 0) {χ : ℝ → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) :
    Tendsto (fun n : ℕ => ∫ τ in Icc (0 : ℝ) T,
        χ τ * (etaK n τ * ∑ i, ∫ x in torusCube, u (x, τ) i * ζ x i)) atTop
      (𝓝 (χ 0 * (1 / 2) * ∑ i, ∫ x in torusCube, v₀ x i * ζ x i)) := by
  set ν : Measure ℝ := volume.restrict (Icc (0 : ℝ) T) with hν
  have hmeas := hu.1.1
  set S1 : ℝ → ℝ := fun τ => ∑ i, ∫ x in torusCube, u (x, τ) i * ζ x i with hS1
  set S2 : ℝ → ℝ := fun τ => ∑ i, ∑ j, ∫ x in torusCube,
    (u (x, τ) i * u (x, τ) j) * gradMat ζ x i j with hS2
  set D : ℝ := ∑ i, ∫ x in torusCube, v₀ x i * ζ x i with hD
  have hS1i : Integrable S1 ν := integrable_slice_pairing hmeas hB (fun i => (hζ i).continuous)
  have hS2i : Integrable S2 ν := integrable_slice_quad hmeas hB (continuous_gradMat_apply hζ)
  have hχ' : Continuous (deriv χ) := continuous_deriv_of_contDiff_top hχ
  have hχc : Continuous χ := hχ.continuous
  have hη := fun n => (etaK_contDiff n).continuous
  have hθc := fun n => (thetaK_contDiff n).continuous
  -- the remainder
  set R : ℕ → ℝ := fun n => ∫ τ, (deriv χ τ * thetaK n τ * S1 τ + χ τ * thetaK n τ * S2 τ) ∂ν with hR
  have hRlim : Tendsto R atTop (𝓝 0) := by
    have hb1 : Integrable (fun τ => |deriv χ τ * S1 τ|) ν := (integrable_cont_mul_time hχ' hS1i).abs
    have hb2 : Integrable (fun τ => |χ τ * S2 τ|) ν := (integrable_cont_mul_time hχc hS2i).abs
    have := tendsto_integral_of_dominated_convergence (μ := ν)
      (F := fun n τ => deriv χ τ * thetaK n τ * S1 τ + χ τ * thetaK n τ * S2 τ) (f := fun _ => (0 : ℝ))
      (fun τ => |deriv χ τ * S1 τ| + |χ τ * S2 τ|) ?_ (hb1.add hb2) ?_ ?_
    · simpa [hR] using this
    · intro n
      have h1 : AEStronglyMeasurable (fun τ => deriv χ τ * thetaK n τ * S1 τ) ν :=
        ((hχ'.mul (hθc n)).aestronglyMeasurable).mul hS1i.aestronglyMeasurable
      have h2 : AEStronglyMeasurable (fun τ => χ τ * thetaK n τ * S2 τ) ν :=
        ((hχc.mul (hθc n)).aestronglyMeasurable).mul hS2i.aestronglyMeasurable
      exact h1.add h2
    · intro n
      refine Filter.Eventually.of_forall fun τ => ?_
      have h0 := thetaK_nonneg n τ
      have h1 := thetaK_le_one n τ
      calc ‖deriv χ τ * thetaK n τ * S1 τ + χ τ * thetaK n τ * S2 τ‖
          ≤ |deriv χ τ * thetaK n τ * S1 τ| + |χ τ * thetaK n τ * S2 τ| := by
            rw [Real.norm_eq_abs]; exact abs_add_le _ _
        _ ≤ |deriv χ τ * S1 τ| + |χ τ * S2 τ| := by
            have e1 : |deriv χ τ * thetaK n τ * S1 τ| = thetaK n τ * |deriv χ τ * S1 τ| := by
              rw [show deriv χ τ * thetaK n τ * S1 τ = thetaK n τ * (deriv χ τ * S1 τ) by ring,
                abs_mul, abs_of_nonneg h0]
            have e2 : |χ τ * thetaK n τ * S2 τ| = thetaK n τ * |χ τ * S2 τ| := by
              rw [show χ τ * thetaK n τ * S2 τ = thetaK n τ * (χ τ * S2 τ) by ring,
                abs_mul, abs_of_nonneg h0]
            rw [e1, e2]
            nlinarith [abs_nonneg (deriv χ τ * S1 τ), abs_nonneg (χ τ * S2 τ)]
    · have hne : ∀ᵐ τ ∂(volume : Measure ℝ), τ ≠ 0 := (Set.countable_singleton (0 : ℝ)).ae_notMem _
      filter_upwards [ae_restrict_of_ae hne, ae_restrict_mem measurableSet_Icc] with τ hτ0 hτm
      have hτpos : 0 < τ := lt_of_le_of_ne hτm.1 (Ne.symm hτ0)
      have hev : ∀ᶠ n in atTop, tDelta n < τ := tendsto_tDelta.eventually (gt_mem_nhds hτpos)
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hev] with n hn
      simp [thetaK_eq_zero n hn.le]
  -- the identity at level `n`
  have hev : ∀ᶠ n in atTop, tDelta n < T := tendsto_tDelta.eventually (gt_mem_nhds hT)
  have hlim := hRlim.add_const (χ 0 * (1 / 2) * D)
  rw [zero_add] at hlim
  refine hlim.congr' ?_
  filter_upwards [hev] with n hn
  have hθ : ContDiff ℝ (⊤ : ℕ∞) (fun τ => χ τ * thetaK n τ) := hχ.mul (thetaK_contDiff n)
  have hW := weak_formulation_product hu hB hζ hζp hζd hθ hn
    (fun τ hτ => by simp [thetaK_eq_zero n hτ])
  have hder : ∀ τ, deriv (fun τ => χ τ * thetaK n τ) τ =
      deriv χ τ * thetaK n τ + χ τ * (-etaK n τ) := fun τ =>
    (((contDiff_one_le hχ) τ).hasDerivAt.mul (thetaK_hasDerivAt n τ)).deriv
  have i1 : Integrable (fun τ => deriv χ τ * thetaK n τ * S1 τ) ν :=
    integrable_cont_mul_time (hχ'.mul (hθc n)) hS1i
  have i2 : Integrable (fun τ => χ τ * etaK n τ * S1 τ) ν :=
    integrable_cont_mul_time (hχc.mul (hη n)) hS1i
  have i3 : Integrable (fun τ => χ τ * thetaK n τ * S2 τ) ν :=
    integrable_cont_mul_time (hχc.mul (hθc n)) hS2i
  have hW' : (∫ τ in Icc (0 : ℝ) T, (deriv (fun τ => χ τ * thetaK n τ) τ * S1 τ +
      χ τ * thetaK n τ * S2 τ)) + χ 0 * thetaK n 0 * D = 0 := hW
  simp only [hder] at hW'
  have e : ∀ τ, (deriv χ τ * thetaK n τ + χ τ * -etaK n τ) * S1 τ + χ τ * thetaK n τ * S2 τ =
      ((deriv χ τ * thetaK n τ * S1 τ + χ τ * thetaK n τ * S2 τ) - χ τ * etaK n τ * S1 τ) := by
    intro τ; ring
  simp only [e] at hW'
  have i13 : Integrable (fun τ => deriv χ τ * thetaK n τ * S1 τ + χ τ * thetaK n τ * S2 τ) ν :=
    i1.add i3
  rw [integral_sub i13 i2, integral_add i1 i3, thetaK_zero] at hW'
  have e2 : ∀ τ, χ τ * (etaK n τ * S1 τ) = χ τ * etaK n τ * S1 τ := fun τ => by ring
  show R n + χ 0 * (1 / 2) * D = ∫ τ in Icc (0 : ℝ) T, χ τ * (etaK n τ * S1 τ)
  simp only [e2]
  simp only [hR]
  rw [integral_add i1 i3]
  linarith

end PDE
