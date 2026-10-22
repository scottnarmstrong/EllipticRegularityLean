module

public import EllipticRegularity.Parabolic.WeakHarnack.LogEstimateSlice
public import EllipticRegularity.Parabolic.WeakHarnack.Profiles
public import EllipticRegularity.Parabolic.WeakHarnack.Pointwise
public import EllipticRegularity.Parabolic.WeakSlice.Product

/-!
# Pointwise ingredients of the logarithmic inequality

* a global `C²` profile `G` with `G(s) = log (s + ε)` for `s ≥ 0`;
* the time-independent test weight `φ = ζ²` as a space-time function;
* the pointwise bound `½ ζ² |G'(u) ∇u|² - 2Λ |∇ζ|² ≤ -(renormalized integrand)`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace PDE.Parabolic.WeakHarnack

variable {d : ℕ}

theorem deriv_shift (f : ℝ → ℝ) (ε s : ℝ) : deriv (fun x => f (x + ε)) s = deriv f (s + ε) := by
  simpa using deriv_comp_add_const (f := f) (a := ε) (x := s)

theorem exists_shiftLogProfile {ε : ℝ} (hε : 0 < ε) :
    ∃ G : ℝ → ℝ, ContDiff ℝ 2 G ∧ (∃ C : NNReal, LipschitzWith C G) ∧
      (∃ C : NNReal, ∀ s, |deriv G s| ≤ C) ∧ (∃ C : NNReal, ∀ s, |deriv (deriv G) s| ≤ C) ∧
      (∀ s, 0 ≤ deriv G s) ∧
      ∀ s, 0 ≤ s → G s = Real.log (s + ε) ∧ deriv G s = (s + ε)⁻¹ ∧
        deriv (deriv G) s = -((s + ε)⁻¹) ^ 2 := by
  obtain ⟨F, hF2, hF1, ⟨B1, hB1⟩, ⟨B2, hB2⟩, ⟨L, hL⟩, hagree⟩ := exists_isC2Profile_log hε
  have hd' : deriv (fun x => F (x + ε)) = fun s => deriv F (s + ε) :=
    funext fun s => deriv_shift F ε s
  have htr : LipschitzWith 1 (fun x : ℝ => x + ε) :=
    LipschitzWith.of_dist_le_mul fun x y => by simp [Real.dist_eq]
  refine ⟨fun x => F (x + ε), hF2.comp (contDiff_id.add contDiff_const), ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨L * 1, hL.comp htr⟩
  · refine ⟨B1.toNNReal, fun s => ?_⟩
    rw [deriv_shift]
    exact (hB1 _).trans (Real.le_coe_toNNReal B1)
  · refine ⟨B2.toNNReal, fun s => ?_⟩
    rw [hd', deriv_shift]
    exact (hB2 _).trans (Real.le_coe_toNNReal B2)
  · intro s; rw [deriv_shift]; exact hF1 _
  · intro s hs
    have h0 : ε ≤ s + ε := by linarith
    obtain ⟨e0, e1, e2⟩ := hagree (s + ε) h0
    refine ⟨e0, ?_, ?_⟩
    · rw [deriv_shift, e1]; simp [one_div]
    · rw [hd', deriv_shift, e2]
      simp [one_div]

/-- The time-independent weight `φ(x,t) = ζ(x)²`, in the product form used by `WeakSlice`. -/
noncomputable def phiZ (d : ℕ) : Vec d × ℝ → ℝ :=
  fun w => (fun _ : ℝ => (1 : ℝ)) w.2 * (radialCutoff d w.1 ^ 2)

theorem phiZ_apply (z : Vec d × ℝ) : phiZ d z = radialCutoff d z.1 ^ 2 := by
  simp [phiZ]

theorem phiZ_nonneg (z : Vec d × ℝ) : 0 ≤ phiZ d z := by
  rw [phiZ_apply]; exact sq_nonneg _

theorem contDiff_radialCutoff_one (d : ℕ) : ContDiff ℝ 1 (radialCutoff d) :=
  (radialCutoff_contDiff d).of_le (by exact_mod_cast le_top)

theorem contDiff_zeta2 (d : ℕ) : ContDiff ℝ 1 (fun x : Vec d => radialCutoff d x ^ 2) :=
  (contDiff_radialCutoff_one d).pow 2

theorem contDiff_phiZ (d : ℕ) : ContDiff ℝ 1 (phiZ d) :=
  PDE.Parabolic.WeakSlice.contDiff_prod contDiff_const (contDiff_zeta2 d)

theorem parTimeDeriv_phiZ (z : Vec d × ℝ) : parTimeDeriv (phiZ d) z = 0 := by
  unfold phiZ
  rw [PDE.Parabolic.WeakSlice.parTimeDeriv_prod contDiff_const (contDiff_zeta2 d)]
  simp

theorem parSpaceGrad_phiZ (z : Vec d × ℝ) :
    parSpaceGrad (phiZ d) z =
      (2 * radialCutoff d z.1) • spaceGradC1 (radialCutoff d) z.1 := by
  unfold phiZ
  rw [PDE.Parabolic.WeakSlice.parSpaceGrad_prod contDiff_const (contDiff_zeta2 d)]
  ext i
  have hd : DifferentiableAt ℝ (radialCutoff d) z.1 :=
    ((contDiff_radialCutoff_one d).differentiable one_ne_zero) z.1
  have := (hd.hasFDerivAt.pow 2).fderiv
  simp only [spaceGradC1, Pi.smul_apply, smul_eq_mul]
  rw [this]
  simp

/-- Pointwise form of the logarithmic test: with `v = u + ε`, `g = ∇u`, `m = ∇ζ`. -/
theorem logPoint {Λ : ℝ} {A : Mat d} (hA : IsEllipticMatrix 1 Λ A) (g m : Vec d) {v ζ : ℝ}
    (hv : 0 < v) :
    1 / 2 * ζ ^ 2 * vecNormSq (v⁻¹ • g) - 2 * Λ * vecNormSq m ≤
      -(-(v⁻¹) ^ 2) * ζ ^ 2 * vecDot (matVecMul A g) g -
        v⁻¹ * vecDot (matVecMul A g) ((2 * ζ) • m) := by
  have h := neg_gradPart_log_ge hA g m (v := v) (ψ := 1) (ζ := ζ) hv zero_le_one
  unfold gradPart at h
  simp only [one_mul, one_div, inv_pow] at h ⊢
  linarith

end PDE.Parabolic.WeakHarnack
