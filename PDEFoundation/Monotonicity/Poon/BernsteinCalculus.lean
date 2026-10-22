module

public import PDEFoundation.Sobolev.ClassicalLaplacian
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Joint space-time calculus for the Bernstein argument

Directional derivatives `jd u f = (q ↦ fderiv ℝ f q u)` of scalar functions on `ℝ × Vec d`
(time first), the spatial coordinate derivatives `jEx i`, the time derivative `jEt`, and the joint
spatial Laplacian `jLap`, together with the product, sum and symmetry rules valid on an open
set where the function is `C^∞`.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace PDE

noncomputable section

variable {d : ℕ}

/-- Directional derivative on the joint space. -/
def jd (u : ℝ × Vec d) (f : ℝ × Vec d → ℝ) : ℝ × Vec d → ℝ := fun q => fderiv ℝ f q u

/-- Spatial coordinate derivative on the joint space. -/
def jEx (i : Fin d) (f : ℝ × Vec d → ℝ) : ℝ × Vec d → ℝ := jd (0, basisVec i) f

/-- Time derivative on the joint space. -/
def jEt (f : ℝ × Vec d → ℝ) : ℝ × Vec d → ℝ := jd ((1 : ℝ), (0 : Vec d)) f

/-- Spatial Laplacian on the joint space. -/
def jLap (f : ℝ × Vec d → ℝ) : ℝ × Vec d → ℝ := fun q => ∑ k : Fin d, jEx k (jEx k f) q

/-- `f` is `C^∞` on `Ω`. -/
abbrev JSm (Ω : Set (ℝ × Vec d)) (f : ℝ × Vec d → ℝ) : Prop := ContDiffOn ℝ (⊤ : ℕ∞) f Ω

variable {Ω : Set (ℝ × Vec d)} {f g : ℝ × Vec d → ℝ}

theorem JSm.jd (hΩ : IsOpen Ω) (hf : JSm Ω f) (u : ℝ × Vec d) : JSm Ω (jd u f) := by
  have h : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ f) Ω :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen hΩ).mp hf).2
  exact h.clm_apply contDiffOn_const

theorem JSm.jEx (hΩ : IsOpen Ω) (hf : JSm Ω f) (i : Fin d) : JSm Ω (jEx i f) :=
  hf.jd hΩ _

theorem JSm.jEt (hΩ : IsOpen Ω) (hf : JSm Ω f) : JSm Ω (jEt f) :=
  hf.jd hΩ _

theorem JSm.jLap (hΩ : IsOpen Ω) (hf : JSm Ω f) : JSm Ω (jLap f) := by
  unfold PDE.jLap
  exact ContDiffOn.sum fun k _ => (hf.jEx hΩ k).jEx hΩ k

theorem JSm.differentiableAt (hΩ : IsOpen Ω) (hf : JSm Ω f) {p : ℝ × Vec d} (hp : p ∈ Ω) :
    DifferentiableAt ℝ f p :=
  (hf.contDiffAt (hΩ.mem_nhds hp)).differentiableAt (by simp)

theorem jd_congr (hΩ : IsOpen Ω) (u : ℝ × Vec d) (h : EqOn f g Ω) {p : ℝ × Vec d} (hp : p ∈ Ω) :
    jd u f p = jd u g p := by
  have : f =ᶠ[𝓝 p] g := eventuallyEq_of_mem (hΩ.mem_nhds hp) h
  simp only [jd, this.fderiv_eq]

theorem jd_add (hΩ : IsOpen Ω) (u : ℝ × Vec d) (hf : JSm Ω f) (hg : JSm Ω g) {p : ℝ × Vec d}
    (hp : p ∈ Ω) : jd u (fun q => f q + g q) p = jd u f p + jd u g p := by
  simp only [jd]
  rw [fderiv_fun_add (hf.differentiableAt hΩ hp) (hg.differentiableAt hΩ hp)]
  rfl

theorem jd_sub (hΩ : IsOpen Ω) (u : ℝ × Vec d) (hf : JSm Ω f) (hg : JSm Ω g) {p : ℝ × Vec d}
    (hp : p ∈ Ω) : jd u (fun q => f q - g q) p = jd u f p - jd u g p := by
  simp only [jd]
  rw [fderiv_fun_sub (hf.differentiableAt hΩ hp) (hg.differentiableAt hΩ hp)]
  rfl

theorem jd_mul (hΩ : IsOpen Ω) (u : ℝ × Vec d) (hf : JSm Ω f) (hg : JSm Ω g) {p : ℝ × Vec d}
    (hp : p ∈ Ω) : jd u (fun q => f q * g q) p = f p * jd u g p + g p * jd u f p := by
  simp only [jd]
  rw [fderiv_fun_mul (hf.differentiableAt hΩ hp) (hg.differentiableAt hΩ hp)]
  simp [smul_eq_mul]

theorem jd_const_mul (hΩ : IsOpen Ω) (u : ℝ × Vec d) (c : ℝ) (hf : JSm Ω f) {p : ℝ × Vec d}
    (hp : p ∈ Ω) : jd u (fun q => c * f q) p = c * jd u f p := by
  simp only [jd]
  rw [fderiv_const_mul (hf.differentiableAt hΩ hp)]
  simp

theorem jd_const (u : ℝ × Vec d) (c : ℝ) (p : ℝ × Vec d) : jd u (fun _ => c) p = 0 := by
  simp [jd]

theorem jd_sum {ι : Type*} (s : Finset ι) (hΩ : IsOpen Ω) (u : ℝ × Vec d) {F : ι → ℝ × Vec d → ℝ}
    (hF : ∀ i ∈ s, JSm Ω (F i)) {p : ℝ × Vec d} (hp : p ∈ Ω) :
    jd u (fun q => ∑ i ∈ s, F i q) p = ∑ i ∈ s, jd u (F i) p := by
  simp only [jd]
  rw [fderiv_fun_sum (fun i hi => (hF i hi).differentiableAt hΩ hp)]
  simp

theorem jd_comm (hΩ : IsOpen Ω) (hf : JSm Ω f) {p : ℝ × Vec d} (hp : p ∈ Ω) (u v : ℝ × Vec d) :
    jd v (jd u f) p = jd u (jd v f) p := by
  have hcd : ContDiffAt ℝ (⊤ : ℕ∞) f p := hf.contDiffAt (hΩ.mem_nhds hp)
  have hsymm : IsSymmSndFDerivAt ℝ f p :=
    hcd.isSymmSndFDerivAt (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.2 (show (2 : ℕ∞) ≤ ⊤ from le_top))
  have hfd : DifferentiableAt ℝ (fderiv ℝ f) p :=
    ((hcd.fderiv_right (m := 1) (WithTop.coe_le_coe.2
      (show (1 : ℕ∞) + 1 ≤ ⊤ from le_top))).differentiableAt (by norm_num))
  have key : ∀ a b : ℝ × Vec d, jd b (jd a f) p = fderiv ℝ (fderiv ℝ f) p b a := by
    intro a b
    show fderiv ℝ (fun y => fderiv ℝ f y a) p b = _
    rw [fderiv_clm_apply hfd (differentiableAt_const _)]
    simp
  rw [key, key]
  exact hsymm.eq v u

end

end PDE
