module

public import PDEFoundation.Monotonicity.Poon.BernsteinRules

/-!
# The Bernstein identity for `a |∇w|² + λ w²`

For a caloric `F` on an open set `Ω`, with `P = |∇F|²`:
`(∂_t - Δ) P = -2 |∇²F|²`, `(∂_t - Δ) F² = -2 P`, and the product rule for `(∂_t - Δ)(a P)`.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace PDE

noncomputable section

variable {d : ℕ} {Ω : Set (ℝ × Vec d)} {F : ℝ × Vec d → ℝ}

/-- The squared spatial gradient `|∇F|²` on the joint space. -/
def jGradSq (F : ℝ × Vec d → ℝ) : ℝ × Vec d → ℝ :=
  fun q => ∑ i : Fin d, jEx i F q * jEx i F q

theorem JSm.jGradSq (hΩ : IsOpen Ω) (hF : JSm Ω F) : JSm Ω (jGradSq F) := by
  unfold PDE.jGradSq
  exact ContDiffOn.sum fun i _ => (hF.jEx hΩ i).mul (hF.jEx hΩ i)

theorem jEt_jGradSq (hΩ : IsOpen Ω) (hF : JSm Ω F) {p : ℝ × Vec d} (hp : p ∈ Ω) :
    jEt (jGradSq F) p = ∑ i : Fin d, 2 * (jEx i F p * jEt (jEx i F) p) := by
  unfold jEt jGradSq
  rw [jd_sum Finset.univ hΩ _ (fun i _ => (hF.jEx hΩ i).mul (hF.jEx hΩ i)) hp]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := jd_mul hΩ ((1 : ℝ), (0 : Vec d)) (hF.jEx hΩ i) (hF.jEx hΩ i) hp
  rw [this]
  change _ = 2 * (jEx i F p * jd _ (jEx i F) p)
  ring

theorem jLap_jGradSq (hΩ : IsOpen Ω) (hF : JSm Ω F) {p : ℝ × Vec d} (hp : p ∈ Ω) :
    jLap (jGradSq F) p = ∑ i : Fin d, (2 * (jEx i F p * jLap (jEx i F) p) +
      2 * ∑ k : Fin d, jEx k (jEx i F) p * jEx k (jEx i F) p) := by
  unfold jGradSq
  rw [jLap_sum Finset.univ hΩ (fun i _ => (hF.jEx hΩ i).mul (hF.jEx hΩ i)) hp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [jLap_mul hΩ (hF.jEx hΩ i) (hF.jEx hΩ i) hp]
  ring

/-- `(∂_t - Δ) |∇F|² = -2 |∇²F|²` for caloric `F`. -/
theorem jEt_sub_jLap_jGradSq (hΩ : IsOpen Ω) (hF : JSm Ω F)
    (hheat : EqOn (jEt F) (jLap F) Ω) {p : ℝ × Vec d} (hp : p ∈ Ω) :
    jEt (jGradSq F) p - jLap (jGradSq F) p =
      -2 * ∑ k : Fin d, ∑ i : Fin d, jEx k (jEx i F) p * jEx k (jEx i F) p := by
  rw [jEt_jGradSq hΩ hF hp, jLap_jGradSq hΩ hF hp, ← Finset.sum_sub_distrib]
  have : ∀ i : Fin d, 2 * (jEx i F p * jEt (jEx i F) p) -
      (2 * (jEx i F p * jLap (jEx i F) p) +
        2 * ∑ k : Fin d, jEx k (jEx i F) p * jEx k (jEx i F) p) =
      -2 * ∑ k : Fin d, jEx k (jEx i F) p * jEx k (jEx i F) p := by
    intro i
    rw [jEt_jEx_eq_jLap hΩ hF hheat i hp]
    ring
  rw [Finset.sum_congr rfl fun i _ => this i, ← Finset.mul_sum, Finset.sum_comm]

theorem jLap_const (c : ℝ) (p : ℝ × Vec d) : jLap (fun _ => c) p = 0 := by
  have h : ∀ u : ℝ × Vec d, jd u (fun _ : ℝ × Vec d => c) = fun _ => 0 := by
    intro u; funext q; simp [jd]
  simp [jLap, jEx, h, jd]

theorem jLap_const_mul (hΩ : IsOpen Ω) (c : ℝ) {f : ℝ × Vec d → ℝ} (hf : JSm Ω f)
    {p : ℝ × Vec d} (hp : p ∈ Ω) : jLap (fun q => c * f q) p = c * jLap f p := by
  have := jLap_mul hΩ (f := fun _ => c) (g := f) contDiffOn_const hf hp
  rw [this, jLap_const]
  simp [jEx, jd]

/-- `(∂_t - Δ) F² = -2 |∇F|²` for caloric `F`. -/
theorem jEt_sub_jLap_sq (hΩ : IsOpen Ω) (hF : JSm Ω F)
    (hheat : EqOn (jEt F) (jLap F) Ω) {p : ℝ × Vec d} (hp : p ∈ Ω) :
    jEt (fun q => F q * F q) p - jLap (fun q => F q * F q) p = -2 * jGradSq F p := by
  have h1 := jd_mul hΩ ((1 : ℝ), (0 : Vec d)) hF hF hp
  have h2 := jLap_mul hΩ hF hF hp
  have h3 := hheat hp
  change jd _ (fun q => F q * F q) p - _ = _
  rw [h1, h2]
  change F p * jEt F p + F p * jEt F p - _ = _
  rw [h3]
  unfold jGradSq
  ring

theorem jEx_jGradSq (hΩ : IsOpen Ω) (hF : JSm Ω F) (k : Fin d) {p : ℝ × Vec d} (hp : p ∈ Ω) :
    jEx k (jGradSq F) p = ∑ i : Fin d, 2 * (jEx i F p * jEx k (jEx i F) p) := by
  unfold jEx jGradSq
  rw [jd_sum Finset.univ hΩ _ (fun i _ => (hF.jEx hΩ i).mul (hF.jEx hΩ i)) hp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [jd_mul hΩ _ (hF.jEx hΩ i) (hF.jEx hΩ i) hp]
  change _ = 2 * (jEx i F p * jd _ (jEx i F) p)
  ring

/-- The Bernstein quantity `G = a |∇F|² + λ F²` satisfies
`(∂_t - Δ) G = a (-2 |∇²F|²) + |∇F|² (∂_t a - Δ a) - 2 Σ_k ∂_k a ∂_k |∇F|² - 2 λ |∇F|²`. -/
theorem jEt_sub_jLap_bernstein (hΩ : IsOpen Ω) (hF : JSm Ω F)
    (hheat : EqOn (jEt F) (jLap F) Ω) {a : ℝ × Vec d → ℝ} (ha : JSm Ω a) (lam : ℝ)
    {p : ℝ × Vec d} (hp : p ∈ Ω) :
    jEt (fun q => a q * jGradSq F q + lam * (F q * F q)) p -
        jLap (fun q => a q * jGradSq F q + lam * (F q * F q)) p =
      a p * (-2 * ∑ k : Fin d, ∑ i : Fin d, jEx k (jEx i F) p * jEx k (jEx i F) p) +
        jGradSq F p * (jEt a p - jLap a p) -
        2 * ∑ k : Fin d, jEx k a p * jEx k (jGradSq F) p - 2 * lam * jGradSq F p := by
  have hP := hF.jGradSq hΩ
  have hFF : JSm Ω (fun q => F q * F q) := hF.mul hF
  have hlam : JSm Ω (fun q => lam * (F q * F q)) := contDiffOn_const.mul hFF
  have haP : JSm Ω (fun q => a q * jGradSq F q) := ha.mul hP
  have t1 : jEt (fun q => a q * jGradSq F q + lam * (F q * F q)) p =
      jEt (fun q => a q * jGradSq F q) p + jEt (fun q => lam * (F q * F q)) p :=
    jd_add hΩ _ haP hlam hp
  have t2 : jEt (fun q => a q * jGradSq F q) p =
      a p * jEt (jGradSq F) p + jGradSq F p * jEt a p := jd_mul hΩ _ ha hP hp
  have t3 : jEt (fun q => lam * (F q * F q)) p = lam * jEt (fun q => F q * F q) p :=
    jd_const_mul hΩ _ lam hFF hp
  have l1 : jLap (fun q => a q * jGradSq F q + lam * (F q * F q)) p =
      jLap (fun q => a q * jGradSq F q) p + jLap (fun q => lam * (F q * F q)) p :=
    jLap_add hΩ haP hlam hp
  have l2 := jLap_mul hΩ ha hP hp
  have l3 := jLap_const_mul hΩ lam hFF hp
  have e1 := jEt_sub_jLap_jGradSq hΩ hF hheat hp
  have e2 := jEt_sub_jLap_sq hΩ hF hheat hp
  rw [t1, t2, t3, l1, l2, l3]
  linear_combination (a p) * e1 + lam * e2
