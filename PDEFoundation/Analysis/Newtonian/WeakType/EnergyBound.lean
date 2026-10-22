module

public import PDEFoundation.Analysis.Newtonian.WeakType.EnergyCutoff

/-!
# Cutoff energy inequality for `u_h`

Testing the weak form of `Δu_h = div h` against `ψ = χ_R² u_h` gives, for large `R`,
`∫ χ_R² |∇u_h|² ≤ ∫ |h|² + 4M / R`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE.NewtonWeakType

noncomputable section

variable {d : ℕ}

theorem vecDot_add_smul (x y z : Vec d) (a b : ℝ) :
    vecDot x (a • y + b • z) = a * vecDot x y + b * vecDot x z := by
  simp only [vecDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum]
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring

theorem continuous_vecDot_comp {f g : Vec d → Vec d} (hf : Continuous f) (hg : Continuous g) :
    Continuous fun x => vecDot (f x) (g x) := by
  unfold vecDot
  exact continuous_finsetSum _ fun i _ =>
    ((continuous_apply i).comp hf).mul ((continuous_apply i).comp hg)

theorem continuous_classicalGradient {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) :
    Continuous (classicalGradient u) :=
  continuous_pi fun k => (contDiff_euclideanCoordDeriv hu k).continuous

theorem classicalGradient_cutoff_mul {u : Vec d → ℝ} (hu : ContDiff ℝ (⊤ : ℕ∞) u) {R : ℝ}
    (hR : 0 < R) (x : Vec d) :
    classicalGradient (fun y => cutoff R y ^ 2 * u y) x =
      (cutoff R x ^ 2) • classicalGradient u x +
        (2 * cutoff R x * u x) • classicalGradient (cutoff R) x := by
  funext k
  have hχ := contDiff_cutoff (d := d) hR
  have h1 := coordDeriv_mul (f := fun y => cutoff R y ^ 2) (g := u) (hχ.pow 2) hu k x
  have h2 := euclideanCoordDeriv_sq hχ k x
  simp only [classicalGradient_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change euclideanCoordDeriv k (fun y => cutoff R y ^ 2 * u y) x = _
  rw [h1, h2]
  change _ = cutoff R x ^ 2 * euclideanCoordDeriv k u x + _ * euclideanCoordDeriv k (cutoff R) x
  ring

theorem hasCompactSupport_of_cutoff_zero {R : ℝ} (hR : 0 < R) {f : Vec d → ℝ}
    (hf : ∀ x, cutoff R x = 0 → f x = 0) : HasCompactSupport f := by
  refine HasCompactSupport.intro (hasCompactSupport_cutoff (d := d) hR) fun x hx => hf x ?_
  exact image_eq_zero_of_notMem_tsupport hx

theorem hasCompactSupport_of_field_zero {h : Vec d → Vec d} (hhc : HasCompactSupport h)
    {f : Vec d → ℝ} (hf : ∀ x, h x = 0 → f x = 0) : HasCompactSupport f := by
  refine HasCompactSupport.intro hhc fun x hx => hf x ?_
  exact image_eq_zero_of_notMem_tsupport hx

theorem cutoff_energy_le (hd : 0 < d)
    (hD2 : ∀ (w : Vec d → ℝ) (F : Vec d → Vec d), ContDiff ℝ (⊤ : ℕ∞) w → HasCompactSupport w →
      ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      (∀ x, euclideanCoordLaplacian w x = classicalDivergence F x) → w = newtonPotential F)
    {h : Vec d → Vec d} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h)
    {R₀ : ℝ} (hR₀ : 0 < R₀) (hsupp : tsupport h ⊆ euclideanBall 0 R₀) :
    ∃ M : ℝ, ∀ R : ℝ, max 1 (2 * R₀) ≤ R →
      ∫ x, cutoff R x ^ 2 * vecNormSq (classicalGradient (newtonPotential h) x) ≤
        (∫ x, vecNormSq (h x)) + 4 * M / R := by
  obtain ⟨M, hM⟩ := exists_cutoff_error_bound hd hh hhc hR₀ hsupp
  refine ⟨M, fun R hRge => ?_⟩
  have hR2 : 2 * R₀ ≤ R := (le_max_right _ _).trans hRge
  have hR1 : 1 ≤ R := (le_max_left _ _).trans hRge
  have hR : 0 < R := by linarith
  have hu := contDiff_newtonPotential hd hh hhc
  set u := newtonPotential h with hudef
  set G : Vec d → Vec d := classicalGradient u with hG
  set χ : Vec d → ℝ := cutoff R with hχdef
  have hχs : ContDiff ℝ (⊤ : ℕ∞) χ := contDiff_cutoff hR
  have hGc : Continuous G := continuous_classicalGradient hu
  have hχGc : Continuous (classicalGradient χ) := continuous_classicalGradient hχs
  -- support of h
  have hhs : ∀ y, h y ≠ 0 → vecEuclideanNorm y < R := by
    intro y hy
    have hmem : y ∈ euclideanBall (0 : Vec d) R₀ :=
      hsupp (subset_tsupport h (Function.mem_support.mpr hy))
    have := (mem_euclideanBall_iff_vecEuclideanNorm_lt hR₀).mp hmem
    rw [sub_zero] at this
    linarith
  -- test function
  set ψ : Vec d → ℝ := fun y => χ y ^ 2 * u y with hψdef
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ψ := (hχs.pow 2).mul hu
  have hψc : HasCompactSupport ψ := hasCompactSupport_of_cutoff_zero hR fun x hx => by
    have hx' : χ x = 0 := hx
    simp [hψdef, hx']
  have hweak := integral_vecDot_gradient_newtonPotential hd hD2 hh hhc hψ hψc
  have hgrad : ∀ x, classicalGradient ψ x = (χ x ^ 2) • G x + (2 * χ x * u x) • classicalGradient χ x :=
    fun x => classicalGradient_cutoff_mul hu hR x
  -- integrands
  set f1 : Vec d → ℝ := fun x => χ x ^ 2 * vecNormSq (G x) with hf1
  set f2 : Vec d → ℝ := fun x => 2 * (χ x * u x * vecDot (G x) (classicalGradient χ x)) with hf2
  have hf1c : Continuous f1 := (hχs.continuous.pow 2).mul
    (continuous_vecDot_comp hGc hGc)
  have hf2c : Continuous f2 := continuous_const.mul
    ((hχs.continuous.mul hu.continuous).mul (continuous_vecDot_comp hGc hχGc))
  have hf1s : HasCompactSupport f1 := hasCompactSupport_of_cutoff_zero hR fun x hx => by
    have hx' : χ x = 0 := hx
    simp [hf1, hx']
  have hf2s : HasCompactSupport f2 := hasCompactSupport_of_cutoff_zero hR fun x hx => by
    have hx' : χ x = 0 := hx
    simp [hf2, hx']
  have hi1 : Integrable f1 volume := hf1c.integrable_of_hasCompactSupport hf1s
  have hi2 : Integrable f2 volume := hf2c.integrable_of_hasCompactSupport hf2s
  -- left side of the weak identity
  have hL : (fun x => vecDot (G x) (classicalGradient ψ x)) = fun x => f1 x + f2 x := by
    funext x
    rw [hgrad x, vecDot_add_smul]
    simp only [hf1, hf2, vecNormSq]
    ring
  -- right side
  have hRpt : ∀ x, vecDot (h x) (classicalGradient ψ x) = vecDot (h x) (G x) := by
    intro x
    by_cases hx : h x = 0
    · simp [hx, vecDot]
    · have hxR := hhs x hx
      have h1 : χ x = 1 := cutoff_eq_one hR hxR
      have h2 : classicalGradient χ x = 0 := classicalGradient_cutoff_eq_zero hR hxR
      rw [hgrad x, vecDot_add_smul, h2, h1]
      simp [vecDot]
  have hI : ∫ x, vecDot (G x) (classicalGradient ψ x) = ∫ x, vecDot (h x) (G x) := by
    rw [hweak]
    exact integral_congr_ae (Filter.Eventually.of_forall hRpt)
  rw [hL, integral_add hi1 hi2] at hI
  -- the error term
  have hf2int : ∫ x, f2 x = 2 * ∫ x, χ x * u x * vecDot (G x) (classicalGradient χ x) := by
    simp only [hf2]
    exact integral_const_mul _ _
  have herr := hM R hRge
  -- Young inequality for the right side
  have hhGc : Continuous fun x => vecDot (h x) (G x) := continuous_vecDot_comp hh.continuous hGc
  have hhGs : HasCompactSupport fun x => vecDot (h x) (G x) :=
    hasCompactSupport_of_field_zero hhc fun x hx => by simp [hx, vecDot]
  have hH2c : Continuous fun x => vecNormSq (h x) := continuous_vecDot_comp hh.continuous hh.continuous
  have hH2s : HasCompactSupport fun x => vecNormSq (h x) :=
    hasCompactSupport_of_field_zero hhc fun x hx => by simp [hx, vecNormSq, vecDot]
  have hiH : Integrable (fun x => vecNormSq (h x)) volume :=
    hH2c.integrable_of_hasCompactSupport hH2s
  have hiI : Integrable (fun x => vecDot (h x) (G x)) volume :=
    hhGc.integrable_of_hasCompactSupport hhGs
  have hyoung : ∫ x, vecDot (h x) (G x) ≤ ∫ x, (vecNormSq (h x) / 2 + f1 x / 2) := by
    refine integral_mono hiI ((hiH.div_const 2).add (hi1.div_const 2)) fun x => ?_
    by_cases hx : h x = 0
    · simp only [hx, vecNormSq, vecDot]
      have : (0 : ℝ) ≤ f1 x := mul_nonneg (sq_nonneg _) (vecNormSq_nonneg _)
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, zero_div, zero_add]
      linarith
    · have h1 : χ x = 1 := cutoff_eq_one hR (hhs x hx)
      have := abs_vecDot_le_add_halves_vecNormSq (h x) (G x)
      have h3 := (abs_le.mp this).2
      simp only [hf1, h1]
      linarith
  rw [integral_add (hiH.div_const 2) (hi1.div_const 2), integral_div, integral_div] at hyoung
  have hbd : |∫ x, χ x * u x * vecDot (G x) (classicalGradient χ x)| ≤ M / R := herr
  have hb2 := (abs_le.mp hbd).1
  have : 4 * M / R = 4 * (M / R) := by ring
  rw [this]
  change ∫ x, f1 x ≤ _
  linarith

end

end PDE.NewtonWeakType
