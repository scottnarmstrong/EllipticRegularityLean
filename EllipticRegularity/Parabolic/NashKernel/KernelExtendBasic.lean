module

public import EllipticRegularity.Parabolic.NashKernel.DyadicCube
public import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Linear a.e.-bounded operators and kernel agreement: closure properties

`LinearBounded M Tf` records the three genuine properties of an operator `Tf` on `L¹(Vec d)`
(a.e. additivity, a.e. homogeneity, and the bound `|Tf f| ≤ M ‖f‖₁` a.e.).  For a bounded kernel
`0 ≤ P ≤ M` the integral operator `f ↦ ∫ P x y f y dy` has the same properties, and the set of
`f` on which `Tf` agrees with it is closed under sums, scalar multiples, a.e. changes and
`L¹` limits.
-/

@[expose] public section

namespace PDE.NashKernelExtend

open MeasureTheory Set Filter Topology

variable {d : ℕ}

/-- The a.e.-linear, a.e.-additive operator on `L¹` bounded `L¹ → L^∞` with constant `M`. -/
structure LinearBounded (M : ℝ) (Tf : (PDE.Vec d → ℝ) → PDE.Vec d → ℝ) : Prop where
  add : ∀ f g : PDE.Vec d → ℝ, Integrable f → Integrable g →
    Tf (f + g) =ᵐ[volume] fun x => Tf f x + Tf g x
  smul : ∀ (c : ℝ) (f : PDE.Vec d → ℝ), Integrable f →
    Tf (c • f) =ᵐ[volume] fun x => c * Tf f x
  bound : ∀ f : PDE.Vec d → ℝ, Integrable f → ∀ᵐ x, |Tf f x| ≤ M * ∫ y, |f y|

/-- The integral operator with kernel `P`. -/
noncomputable def kerOp (P : PDE.Vec d → PDE.Vec d → ℝ) (f : PDE.Vec d → ℝ) (x : PDE.Vec d) : ℝ :=
  ∫ y, P x y * f y

/-- `Tf f` is a.e. the integral operator of `P` applied to `f`. -/
def Agree (P : PDE.Vec d → PDE.Vec d → ℝ) (Tf : (PDE.Vec d → ℝ) → PDE.Vec d → ℝ)
    (f : PDE.Vec d → ℝ) : Prop :=
  Tf f =ᵐ[volume] kerOp P f

section Kernel

variable {M : ℝ} {P : PDE.Vec d → PDE.Vec d → ℝ}

theorem integrable_kernel_mul (hPm : Measurable (Function.uncurry P))
    (hPb : ∀ x y, 0 ≤ P x y ∧ P x y ≤ M) (x : PDE.Vec d) {f : PDE.Vec d → ℝ}
    (hf : Integrable f) : Integrable (fun y => P x y * f y) :=
  hf.bdd_mul (c := M) hPm.of_uncurry_left.aestronglyMeasurable (ae_of_all _ fun y => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hPb x y).1]; exact (hPb x y).2)

theorem kerOp_add (hPm : Measurable (Function.uncurry P)) (hPb : ∀ x y, 0 ≤ P x y ∧ P x y ≤ M)
    {f g : PDE.Vec d → ℝ} (hf : Integrable f) (hg : Integrable g) (x : PDE.Vec d) :
    kerOp P (f + g) x = kerOp P f x + kerOp P g x := by
  simp only [kerOp, Pi.add_apply, mul_add]
  exact integral_add (integrable_kernel_mul hPm hPb x hf) (integrable_kernel_mul hPm hPb x hg)

theorem kerOp_smul (c : ℝ) (f : PDE.Vec d → ℝ) (x : PDE.Vec d) :
    kerOp P (c • f) x = c * kerOp P f x := by
  simp only [kerOp, Pi.smul_apply, smul_eq_mul]
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ fun y => by ring)

theorem abs_kerOp_le (hPb : ∀ x y, 0 ≤ P x y ∧ P x y ≤ M) {f : PDE.Vec d → ℝ} (hf : Integrable f)
    (x : PDE.Vec d) : |kerOp P f x| ≤ M * ∫ y, |f y| := by
  have h := norm_integral_le_of_norm_le (μ := volume) (f := fun y => P x y * f y)
    (g := fun y => M * |f y|) (hf.abs.const_mul M) (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hPb x y).1]
      exact mul_le_mul_of_nonneg_right (hPb x y).2 (abs_nonneg _))
  rw [integral_const_mul] at h
  simpa [kerOp, Real.norm_eq_abs] using h

theorem kerOp_congr_ae {f g : PDE.Vec d → ℝ} (h : f =ᵐ[volume] g) :
    kerOp P f = kerOp P g := by
  funext x
  exact integral_congr_ae (by filter_upwards [h] with y hy; rw [hy])

end Kernel

section Agree

variable {M : ℝ} {P : PDE.Vec d → PDE.Vec d → ℝ} {Tf : (PDE.Vec d → ℝ) → PDE.Vec d → ℝ}

theorem agree_add (hPm : Measurable (Function.uncurry P)) (hPb : ∀ x y, 0 ≤ P x y ∧ P x y ≤ M)
    (hL : LinearBounded M Tf) {f g : PDE.Vec d → ℝ} (hf : Integrable f) (hg : Integrable g)
    (h1 : Agree P Tf f) (h2 : Agree P Tf g) : Agree P Tf (f + g) := by
  filter_upwards [hL.add f g hf hg, h1, h2] with x ha hb hc
  rw [ha, hb, hc, kerOp_add hPm hPb hf hg]

theorem agree_smul (hL : LinearBounded M Tf) (c : ℝ) {f : PDE.Vec d → ℝ} (hf : Integrable f)
    (h1 : Agree P Tf f) : Agree P Tf (c • f) := by
  filter_upwards [hL.smul c f hf, h1] with x ha hb
  rw [ha, hb, kerOp_smul]

theorem agree_zero (hL : LinearBounded M Tf) : Agree P Tf (0 : PDE.Vec d → ℝ) := by
  have h := hL.smul 0 (0 : PDE.Vec d → ℝ) (integrable_zero _ _ _)
  filter_upwards [h] with x hx
  have h0 : (0 : ℝ) • (0 : PDE.Vec d → ℝ) = 0 := zero_smul _ _
  rw [h0] at hx
  rw [hx]
  have : kerOp P (0 : PDE.Vec d → ℝ) x = 0 := by simp [kerOp]
  rw [this]; ring

theorem agree_sub (hPm : Measurable (Function.uncurry P)) (hPb : ∀ x y, 0 ≤ P x y ∧ P x y ≤ M)
    (hL : LinearBounded M Tf) {f g : PDE.Vec d → ℝ} (hf : Integrable f) (hg : Integrable g)
    (h1 : Agree P Tf f) (h2 : Agree P Tf g) : Agree P Tf (f - g) := by
  have h3 := agree_smul hL (-1) hg h2
  have h4 := agree_add hPm hPb hL hf (hg.smul (-1)) h1 h3
  have : f + (-1 : ℝ) • g = f - g := by
    funext y; simp [sub_eq_add_neg]
  rwa [this] at h4

theorem tf_sub_ae_le (hL : LinearBounded M Tf) {f g : PDE.Vec d → ℝ} (hf : Integrable f)
    (hg : Integrable g) : ∀ᵐ x, |Tf f x - Tf g x| ≤ M * ∫ y, |f y - g y| := by
  have h1 := hL.add g (f - g) hg (hf.sub hg)
  have h2 := hL.bound (f - g) (hf.sub hg)
  have : g + (f - g) = f := by funext y; simp
  rw [this] at h1
  filter_upwards [h1, h2] with x ha hb
  rw [ha]
  have : Tf g x + Tf (f - g) x - Tf g x = Tf (f - g) x := by ring
  rw [this]
  simpa using hb

theorem agree_congr_ae (hL : LinearBounded M Tf) {f g : PDE.Vec d → ℝ}
    (hfg : f =ᵐ[volume] g) (hf : Integrable f) (h1 : Agree P Tf f) : Agree P Tf g := by
  have hg : Integrable g := hf.congr hfg
  have h2 := tf_sub_ae_le hL hg hf
  have h3 : ∫ y, |g y - f y| = 0 := by
    rw [integral_eq_zero_of_ae]
    filter_upwards [hfg] with y hy
    simp [hy]
  rw [h3, mul_zero] at h2
  have e := kerOp_congr_ae (P := P) hfg
  filter_upwards [h2, h1] with x ha hb
  have : Tf g x = Tf f x := by
    have h4 : Tf g x - Tf f x = 0 := abs_nonpos_iff.mp ha
    linarith
  show Tf g x = kerOp P g x
  rw [this, ← e]
  exact hb

theorem agree_of_tendsto (hPm : Measurable (Function.uncurry P))
    (hPb : ∀ x y, 0 ≤ P x y ∧ P x y ≤ M) (hL : LinearBounded M Tf)
    {u : ℕ → PDE.Vec d → ℝ} {f : PDE.Vec d → ℝ} (hf : Integrable f)
    (hu : ∀ n, Integrable (u n)) (hlim : Tendsto (fun n => ∫ y, |u n y - f y|) atTop (𝓝 0))
    (hagree : ∀ n, Agree P Tf (u n)) : Agree P Tf f := by
  have hall : ∀ᵐ x, ∀ n, |Tf f x - kerOp P f x| ≤ 2 * M * ∫ y, |u n y - f y| := by
    rw [ae_all_iff]
    intro n
    filter_upwards [tf_sub_ae_le hL hf (hu n), hagree n] with x h1 h2
    have h3 := abs_kerOp_le hPb (hf.sub (hu n)) x
    have h4 : kerOp P (f - u n) x = kerOp P f x - kerOp P (u n) x := by
      have := kerOp_add hPm hPb hf ((hu n).smul (-1 : ℝ)) x
      have h5 := kerOp_smul (P := P) (-1) (u n) x
      have h6 : f + (-1 : ℝ) • u n = f - u n := by funext y; simp [sub_eq_add_neg]
      rw [h6] at this; rw [this, h5]; ring
    rw [h4] at h3
    simp only [Pi.sub_apply] at h3
    have h7 : ∫ y, |f y - u n y| = ∫ y, |u n y - f y| :=
      integral_congr_ae (ae_of_all _ fun y => abs_sub_comm _ _)
    rw [h7] at h1 h3
    have h2' : Tf (u n) x = kerOp P (u n) x := h2
    rw [abs_le] at h1 h3 ⊢
    constructor <;> linarith [h1.1, h1.2, h3.1, h3.2]
  filter_upwards [hall] with x hx
  have hlim' : Tendsto (fun n => 2 * M * ∫ y, |u n y - f y|) atTop (𝓝 0) := by
    simpa using hlim.const_mul (2 * M)
  have := ge_of_tendsto' hlim' hx
  exact sub_eq_zero.mp (abs_nonpos_iff.mp this)

end Agree

end PDE.NashKernelExtend
