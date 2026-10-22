module

public import EllipticRegularity.Parabolic.NashKernel.KernelExtendBasic

/-!
# Agreement of a kernel operator on the domain `L¹ ∩ L²`

Variant of `KernelExtendBasic` for an operator `Tf` that is only meaningful on the domain
`Dom f := Integrable f ∧ MemLp f 2` (the Cauchy solution operator needs `L²` data).  The domain is
closed under sums, scalar multiples and a.e. changes; `LinearBoundedD M Tf` asks for the a.e.
linearity and the `L¹ → L^∞` bound on `Dom` only, and the closure lemmas for `Agree` hold with the
same proofs.
-/

@[expose] public section

namespace PDE.NashKernelExtend

open MeasureTheory Set Filter Topology

variable {d : ℕ}

/-- The domain `L¹ ∩ L²`. -/
def Dom (f : PDE.Vec d → ℝ) : Prop := Integrable f ∧ MemLp f 2 volume

theorem Dom.add {f g : PDE.Vec d → ℝ} (hf : Dom f) (hg : Dom g) : Dom (f + g) :=
  ⟨hf.1.add hg.1, hf.2.add hg.2⟩

theorem Dom.smul (c : ℝ) {f : PDE.Vec d → ℝ} (hf : Dom f) : Dom (c • f) :=
  ⟨hf.1.smul c, hf.2.const_smul c⟩

theorem Dom.sub {f g : PDE.Vec d → ℝ} (hf : Dom f) (hg : Dom g) : Dom (f - g) :=
  ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩

theorem Dom.congr {f g : PDE.Vec d → ℝ} (hf : Dom f) (h : f =ᵐ[volume] g) : Dom g :=
  ⟨hf.1.congr h, hf.2.ae_eq h⟩

theorem dom_zero : Dom (0 : PDE.Vec d → ℝ) := ⟨integrable_zero _ _ _, MemLp.zero⟩

theorem dom_indicator_one {s : Set (PDE.Vec d)} (hs : MeasurableSet s) (hfin : volume s < ⊤) :
    Dom (s.indicator fun _ => (1 : ℝ)) :=
  ⟨(integrableOn_const (C := (1 : ℝ)) hfin.ne).integrable_indicator hs,
    memLp_indicator_const 2 hs (1 : ℝ) (Or.inr hfin.ne)⟩

/-- The operator is a.e. additive, a.e. homogeneous and `L¹ → L^∞` bounded on `L¹ ∩ L²`. -/
structure LinearBoundedD (M : ℝ) (Tf : (PDE.Vec d → ℝ) → PDE.Vec d → ℝ) : Prop where
  add : ∀ f g : PDE.Vec d → ℝ, Dom f → Dom g →
    Tf (f + g) =ᵐ[volume] fun x => Tf f x + Tf g x
  smul : ∀ (c : ℝ) (f : PDE.Vec d → ℝ), Dom f →
    Tf (c • f) =ᵐ[volume] fun x => c * Tf f x
  bound : ∀ f : PDE.Vec d → ℝ, Dom f → ∀ᵐ x, |Tf f x| ≤ M * ∫ y, |f y|

section Agree

variable {M : ℝ} {P : PDE.Vec d → PDE.Vec d → ℝ} {Tf : (PDE.Vec d → ℝ) → PDE.Vec d → ℝ}

theorem agreeD_add (hPm : Measurable (Function.uncurry P)) (hPb : ∀ x y, 0 ≤ P x y ∧ P x y ≤ M)
    (hL : LinearBoundedD M Tf) {f g : PDE.Vec d → ℝ} (hf : Dom f) (hg : Dom g)
    (h1 : Agree P Tf f) (h2 : Agree P Tf g) : Agree P Tf (f + g) := by
  filter_upwards [hL.add f g hf hg, h1, h2] with x ha hb hc
  rw [ha, hb, hc, kerOp_add hPm hPb hf.1 hg.1]

theorem agreeD_smul (hL : LinearBoundedD M Tf) (c : ℝ) {f : PDE.Vec d → ℝ} (hf : Dom f)
    (h1 : Agree P Tf f) : Agree P Tf (c • f) := by
  filter_upwards [hL.smul c f hf, h1] with x ha hb
  rw [ha, hb, kerOp_smul]

theorem agreeD_zero (hL : LinearBoundedD M Tf) : Agree P Tf (0 : PDE.Vec d → ℝ) := by
  have h := hL.smul 0 (0 : PDE.Vec d → ℝ) dom_zero
  filter_upwards [h] with x hx
  have h0 : (0 : ℝ) • (0 : PDE.Vec d → ℝ) = 0 := zero_smul _ _
  rw [h0] at hx
  rw [hx]
  have : kerOp P (0 : PDE.Vec d → ℝ) x = 0 := by simp [kerOp]
  rw [this]; ring

theorem agreeD_sub (hPm : Measurable (Function.uncurry P)) (hPb : ∀ x y, 0 ≤ P x y ∧ P x y ≤ M)
    (hL : LinearBoundedD M Tf) {f g : PDE.Vec d → ℝ} (hf : Dom f) (hg : Dom g)
    (h1 : Agree P Tf f) (h2 : Agree P Tf g) : Agree P Tf (f - g) := by
  have h3 := agreeD_smul hL (-1) hg h2
  have h4 := agreeD_add hPm hPb hL hf (hg.smul (-1)) h1 h3
  have : f + (-1 : ℝ) • g = f - g := by
    funext y; simp [sub_eq_add_neg]
  rwa [this] at h4

theorem tfD_sub_ae_le (hL : LinearBoundedD M Tf) {f g : PDE.Vec d → ℝ} (hf : Dom f)
    (hg : Dom g) : ∀ᵐ x, |Tf f x - Tf g x| ≤ M * ∫ y, |f y - g y| := by
  have h1 := hL.add g (f - g) hg (hf.sub hg)
  have h2 := hL.bound (f - g) (hf.sub hg)
  have : g + (f - g) = f := by funext y; simp
  rw [this] at h1
  filter_upwards [h1, h2] with x ha hb
  rw [ha]
  have : Tf g x + Tf (f - g) x - Tf g x = Tf (f - g) x := by ring
  rw [this]
  simpa using hb

theorem agreeD_congr_ae (hL : LinearBoundedD M Tf) {f g : PDE.Vec d → ℝ}
    (hfg : f =ᵐ[volume] g) (hf : Dom f) (h1 : Agree P Tf f) : Agree P Tf g := by
  have hg : Dom g := hf.congr hfg
  have h2 := tfD_sub_ae_le hL hg hf
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

theorem agreeD_of_tendsto (hPm : Measurable (Function.uncurry P))
    (hPb : ∀ x y, 0 ≤ P x y ∧ P x y ≤ M) (hL : LinearBoundedD M Tf)
    {u : ℕ → PDE.Vec d → ℝ} {f : PDE.Vec d → ℝ} (hf : Dom f)
    (hu : ∀ n, Dom (u n)) (hlim : Tendsto (fun n => ∫ y, |u n y - f y|) atTop (𝓝 0))
    (hagree : ∀ n, Agree P Tf (u n)) : Agree P Tf f := by
  have hall : ∀ᵐ x, ∀ n, |Tf f x - kerOp P f x| ≤ 2 * M * ∫ y, |u n y - f y| := by
    rw [ae_all_iff]
    intro n
    filter_upwards [tfD_sub_ae_le hL hf (hu n), hagree n] with x h1 h2
    have h3 := abs_kerOp_le hPb (hf.1.sub (hu n).1) x
    have h4 : kerOp P (f - u n) x = kerOp P f x - kerOp P (u n) x := by
      have := kerOp_add hPm hPb hf.1 ((hu n).1.smul (-1 : ℝ)) x
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
