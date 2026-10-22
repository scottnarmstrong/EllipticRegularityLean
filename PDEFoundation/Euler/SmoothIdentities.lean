module

public import PDEFoundation.Euler.SmoothPartial

/-!
# Identities for smooth periodic divergence-free fields on the torus

For a smooth `ℤ²`-periodic field `u`, with `ω = ∂₁u₂ - ∂₂u₁` and `div u = 0`:
* `∫_{torusCube} |∇u|² = ∫_{torusCube} ω²`;
* `-Δ u₁ = ∂₂ ω`, `-Δ u₂ = -∂₁ ω` pointwise.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

/-- Vorticity `∂₁u₂ - ∂₂u₁` of a planar field. -/
noncomputable def torusCurl (u : Vec 2 → Vec 2) : Vec 2 → ℝ :=
  fun x => pd 0 (fun y => u y 1) x - pd 1 (fun y => u y 0) x

/-- Divergence `∂₁u₁ + ∂₂u₂` of a planar field. -/
noncomputable def torusDiv (u : Vec 2 → Vec 2) : Vec 2 → ℝ :=
  fun x => pd 0 (fun y => u y 0) x + pd 1 (fun y => u y 1) x

/-- Laplacian `∂₁∂₁ f + ∂₂∂₂ f`. -/
noncomputable def torusLap (f : Vec 2 → ℝ) : Vec 2 → ℝ :=
  fun x => pd 0 (pd 0 f) x + pd 1 (pd 1 f) x

section

variable {u : Vec 2 → Vec 2}

/-- The null-Lagrangian identity `∫ ∂₁u₁ ∂₂u₂ = ∫ ∂₂u₁ ∂₁u₂`. -/
theorem integral_null_lagrangian {a b : Vec 2 → ℝ} (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hap : IsTorusPeriodic a) (hbp : IsTorusPeriodic b) :
    ∫ x in torusCube, pd 0 a x * pd 1 b x = ∫ x in torusCube, pd 1 a x * pd 0 b x := by
  have h1 : ∫ x in torusCube, pd 0 a x * pd 1 b x =
      -∫ x in torusCube, a x * pd 0 (pd 1 b) x := torus_integral_by_parts (f := a) (g := pd 1 b) (ha.of_le (by simp))
    ((contDiff_pd_top hb 1).of_le (by simp)) hap (hbp.pd 1) 0
  have h2 : ∫ x in torusCube, pd 1 a x * pd 0 b x =
      -∫ x in torusCube, a x * pd 1 (pd 0 b) x := torus_integral_by_parts (f := a) (g := pd 0 b) (ha.of_le (by simp))
    ((contDiff_pd_top hb 0).of_le (by simp)) hap (hbp.pd 0) 1
  have hc := pd_comm (hb.of_le (by simp : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))) 0 1
  rw [h1, h2, hc]

theorem differentiable_of_contDiff_top {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Differentiable ℝ f := hf.differentiable (by simp)

theorem contDiff_two_of_top {f : Vec 2 → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ 2 f :=
  hf.of_le (by simp)

/-- Energy identity for a pair of smooth periodic components with `∂₁a + ∂₂b = 0`. -/
theorem integral_sq_grad_pair {a b : Vec 2 → ℝ} (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hap : IsTorusPeriodic a) (hbp : IsTorusPeriodic b)
    (hd : ∀ x, pd 0 a x + pd 1 b x = 0) :
    ∫ x in torusCube, (pd 0 a x ^ 2 + pd 1 a x ^ 2 + (pd 0 b x ^ 2 + pd 1 b x ^ 2)) =
      ∫ x in torusCube, (pd 0 b x - pd 1 a x) ^ 2 := by
  have hnl := integral_null_lagrangian ha hb hap hbp
  have c : ∀ (j : Fin 2) (f : Vec 2 → ℝ), ContDiff ℝ (⊤ : ℕ∞) f → Continuous (pd j f) :=
    fun j f hf => (contDiff_pd_top hf j).continuous
  have pt : ∀ x, pd 0 a x ^ 2 + pd 1 a x ^ 2 + (pd 0 b x ^ 2 + pd 1 b x ^ 2) =
      (pd 0 b x - pd 1 a x) ^ 2 + 2 * (pd 1 a x * pd 0 b x) - 2 * (pd 0 a x * pd 1 b x) := by
    intro x
    have h : pd 1 b x = - pd 0 a x := by linarith [hd x]
    rw [h]; ring
  simp only [pt]
  have i1 : IntegrableOn (fun x => (pd 0 b x - pd 1 a x) ^ 2) torusCube :=
    (((c 0 b hb).sub (c 1 a ha)).pow 2).integrableOn_Icc
  have i2 : IntegrableOn (fun x => 2 * (pd 1 a x * pd 0 b x)) torusCube :=
    (continuous_const.mul ((c 1 a ha).mul (c 0 b hb))).integrableOn_Icc
  have i3 : IntegrableOn (fun x => 2 * (pd 0 a x * pd 1 b x)) torusCube :=
    (continuous_const.mul ((c 0 a ha).mul (c 1 b hb))).integrableOn_Icc
  have h12 := integral_add i1 i2
  have h123 := integral_sub (i1.add i2) i3
  simp only [Pi.add_apply] at h123
  rw [h123, h12, integral_const_mul, integral_const_mul, hnl]
  ring

/-- **Energy identity**: `∫ |∇u|² = ∫ ω²` for smooth periodic divergence-free `u`. -/
theorem integral_sq_gradient_eq_integral_sq_curl
    (hu : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => u x i)) (hup : IsTorusPeriodic u)
    (hdiv : ∀ x, torusDiv u x = 0) :
    ∫ x in torusCube, ∑ i, ∑ j, pd j (fun y => u y i) x ^ 2 =
      ∫ x in torusCube, torusCurl u x ^ 2 := by
  simp only [Fin.sum_univ_two, torusCurl]
  exact integral_sq_grad_pair (hu 0) (hu 1) (hup.comp (fun v => v 0)) (hup.comp (fun v => v 1))
    (fun x => hdiv x)

theorem torusLap_fst_aux {a b : Vec 2 → ℝ} (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hd : ∀ x, pd 0 a x + pd 1 b x = 0) (x : Vec 2) :
    pd 0 (pd 0 a) x + pd 1 (pd 1 a) x = -pd 1 (fun x => pd 0 b x - pd 1 a x) x := by
  have hda := differentiable_of_contDiff_top (contDiff_pd_top ha 1)
  have hdb := differentiable_of_contDiff_top (contDiff_pd_top hb 0)
  have h1 : pd 0 a = fun x => - pd 1 b x := by
    funext x; linarith [hd x]
  have hcomm := pd_comm (contDiff_two_of_top hb) 0 1
  rw [pd_sub hdb hda, h1, pd_neg, hcomm]
  ring

theorem torusLap_snd_aux {a b : Vec 2 → ℝ} (ha : ContDiff ℝ (⊤ : ℕ∞) a)
    (hb : ContDiff ℝ (⊤ : ℕ∞) b) (hd : ∀ x, pd 0 a x + pd 1 b x = 0) (x : Vec 2) :
    pd 0 (pd 0 b) x + pd 1 (pd 1 b) x = pd 0 (fun x => pd 0 b x - pd 1 a x) x := by
  have hda := differentiable_of_contDiff_top (contDiff_pd_top ha 1)
  have hdb := differentiable_of_contDiff_top (contDiff_pd_top hb 0)
  have h2 : pd 1 b = fun x => - pd 0 a x := by
    funext x; linarith [hd x]
  have hcomm := pd_comm (contDiff_two_of_top ha) 0 1
  rw [pd_sub hdb hda, h2, pd_neg, hcomm]
  ring

/-- `-Δ u₁ = ∂₂ ω` for smooth divergence-free fields. -/
theorem torusLap_fst (hu : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => u x i))
    (hdiv : ∀ x, torusDiv u x = 0) (x : Vec 2) :
    torusLap (fun y => u y 0) x = - pd 1 (torusCurl u) x :=
  torusLap_fst_aux (hu 0) (hu 1) (fun x => hdiv x) x

/-- `-Δ u₂ = -∂₁ ω` for smooth divergence-free fields (stated as `Δ u₂ = ∂₁ ω`). -/
theorem torusLap_snd (hu : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => u x i))
    (hdiv : ∀ x, torusDiv u x = 0) (x : Vec 2) :
    torusLap (fun y => u y 1) x = pd 0 (torusCurl u) x :=
  torusLap_snd_aux (hu 0) (hu 1) (fun x => hdiv x) x

end

end PDE
