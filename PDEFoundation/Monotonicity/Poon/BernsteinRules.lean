module

public import PDEFoundation.Monotonicity.Poon.BernsteinCalculus

/-!
# Second-order rules for the Bernstein argument

Laplacian of products, sums, and the heat-equation transfer to spatial derivatives.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace PDE

noncomputable section

variable {d : ℕ} {Ω : Set (ℝ × Vec d)} {f g : ℝ × Vec d → ℝ}

theorem jEx_mul (hΩ : IsOpen Ω) (k : Fin d) (hf : JSm Ω f) (hg : JSm Ω g) {p : ℝ × Vec d}
    (hp : p ∈ Ω) : jEx k (fun q => f q * g q) p = f p * jEx k g p + g p * jEx k f p :=
  jd_mul hΩ _ hf hg hp

theorem jEx_jEx_mul (hΩ : IsOpen Ω) (k : Fin d) (hf : JSm Ω f) (hg : JSm Ω g) {p : ℝ × Vec d}
    (hp : p ∈ Ω) :
    jEx k (jEx k (fun q => f q * g q)) p =
      f p * jEx k (jEx k g) p + g p * jEx k (jEx k f) p + 2 * (jEx k f p * jEx k g p) := by
  have h1 : EqOn (jEx k (fun q => f q * g q))
      (fun q => f q * jEx k g q + g q * jEx k f q) Ω := fun q hq => jEx_mul hΩ k hf hg hq
  have h2 : JSm Ω (fun q => f q * jEx k g q) := hf.mul (hg.jEx hΩ k)
  have h3 : JSm Ω (fun q => g q * jEx k f q) := hg.mul (hf.jEx hΩ k)
  have e1 : jEx k (jEx k (fun q => f q * g q)) p =
      jEx k (fun q => f q * jEx k g q + g q * jEx k f q) p := jd_congr hΩ _ h1 hp
  rw [e1]
  change jd _ (fun q => (fun q => f q * jEx k g q) q + (fun q => g q * jEx k f q) q) p = _
  rw [jd_add hΩ _ h2 h3 hp]
  have e2 := jd_mul hΩ (0, basisVec k) hf (hg.jEx hΩ k) hp
  have e3 := jd_mul hΩ (0, basisVec k) hg (hf.jEx hΩ k) hp
  rw [e2, e3]
  change f p * jEx k (jEx k g) p + jEx k g p * jEx k f p +
    (g p * jEx k (jEx k f) p + jEx k f p * jEx k g p) = _
  ring

theorem jLap_mul (hΩ : IsOpen Ω) (hf : JSm Ω f) (hg : JSm Ω g) {p : ℝ × Vec d} (hp : p ∈ Ω) :
    jLap (fun q => f q * g q) p =
      f p * jLap g p + g p * jLap f p + 2 * ∑ k : Fin d, jEx k f p * jEx k g p := by
  unfold jLap
  simp only [jEx_jEx_mul hΩ _ hf hg hp, Finset.sum_add_distrib, Finset.mul_sum]

theorem jLap_sum {ι : Type*} (s : Finset ι) (hΩ : IsOpen Ω) {F : ι → ℝ × Vec d → ℝ}
    (hF : ∀ i ∈ s, JSm Ω (F i)) {p : ℝ × Vec d} (hp : p ∈ Ω) :
    jLap (fun q => ∑ i ∈ s, F i q) p = ∑ i ∈ s, jLap (F i) p := by
  unfold jLap
  have step : ∀ k : Fin d, jEx k (jEx k (fun q => ∑ i ∈ s, F i q)) p =
      ∑ i ∈ s, jEx k (jEx k (F i)) p := by
    intro k
    have h1 : EqOn (jEx k (fun q => ∑ i ∈ s, F i q)) (fun q => ∑ i ∈ s, jEx k (F i) q) Ω :=
      fun q hq => jd_sum s hΩ _ hF hq
    rw [show jEx k (jEx k (fun q => ∑ i ∈ s, F i q)) p =
      jEx k (fun q => ∑ i ∈ s, jEx k (F i) q) p from jd_congr hΩ _ h1 hp]
    exact jd_sum s hΩ _ (fun i hi => (hF i hi).jEx hΩ k) hp
  simp only [step]
  exact Finset.sum_comm

theorem jLap_add (hΩ : IsOpen Ω) (hf : JSm Ω f) (hg : JSm Ω g) {p : ℝ × Vec d} (hp : p ∈ Ω) :
    jLap (fun q => f q + g q) p = jLap f p + jLap g p := by
  have := jLap_sum (Finset.univ : Finset (Fin 2)) hΩ
    (F := fun i => if i = 0 then f else g) (fun i _ => by split_ifs <;> assumption) hp
  simpa [Fin.sum_univ_two] using this

/-- The heat equation for `f` is inherited by each spatial partial derivative. -/
theorem jEt_jEx_eq_jLap (hΩ : IsOpen Ω) (hf : JSm Ω f) (hheat : EqOn (jEt f) (jLap f) Ω)
    (i : Fin d) {p : ℝ × Vec d} (hp : p ∈ Ω) : jEt (jEx i f) p = jLap (jEx i f) p := by
  have h1 : jEt (jEx i f) p = jEx i (jEt f) p := jd_comm hΩ hf hp _ _
  have h2 : jEx i (jEt f) p = jEx i (jLap f) p := jd_congr hΩ _ hheat hp
  have h3 : jEx i (jLap f) p = ∑ k : Fin d, jEx i (jEx k (jEx k f)) p :=
    jd_sum Finset.univ hΩ _ (fun k _ => (hf.jEx hΩ k).jEx hΩ k) hp
  have h4 : ∀ k : Fin d, jEx i (jEx k (jEx k f)) p = jEx k (jEx k (jEx i f)) p := by
    intro k
    have a1 : jEx i (jEx k (jEx k f)) p = jEx k (jEx i (jEx k f)) p :=
      jd_comm hΩ (hf.jEx hΩ k) hp _ _
    have a2 : EqOn (jEx i (jEx k f)) (jEx k (jEx i f)) Ω := fun q hq => jd_comm hΩ hf hq _ _
    rw [a1]
    exact jd_congr hΩ _ a2 hp
  rw [h1, h2, h3]
  unfold jLap
  exact Finset.sum_congr rfl fun k _ => h4 k

end

end PDE
