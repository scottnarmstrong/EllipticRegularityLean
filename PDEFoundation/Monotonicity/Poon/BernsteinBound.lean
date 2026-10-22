module

public import PDEFoundation.Monotonicity.Poon.BernsteinCutoff

/-!
# The Bernstein quantity is a subsolution on the cylinder

With `Z = 1 - |x - x₀|²/ρ²`, `a = Z² (t - t₀)` and `λ = (25 + 4d)/2`, the function
`G = a |∇F|² + λ F²` satisfies `(∂_t - Δ) G ≤ 0` on `{t₀ ≤ t ≤ t₀ + ρ², |x - x₀| ≤ ρ}`.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace PDE

noncomputable section

variable {d : ℕ}

/-- Completion of squares: `0 ≤ Σ_{k,i} 2 (Z S_{ki} + 2 Z_k W_i)²`, expanded. -/
theorem bernstein_complete_square (Zk W : Fin d → ℝ) (S : Fin d → Fin d → ℝ) (Z : ℝ) :
    0 ≤ 2 * Z * Z * (∑ k : Fin d, ∑ i : Fin d, S k i * S k i) +
      8 * Z * (∑ k : Fin d, Zk k * ∑ i : Fin d, W i * S k i) +
      8 * (∑ k : Fin d, Zk k * Zk k) * (∑ i : Fin d, W i * W i) := by
  have h : 0 ≤ ∑ k : Fin d, ∑ i : Fin d, 2 * (Z * S k i + 2 * Zk k * W i) ^ 2 :=
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun i _ => by positivity
  have e : ∑ k : Fin d, ∑ i : Fin d, 2 * (Z * S k i + 2 * Zk k * W i) ^ 2 =
      2 * Z * Z * (∑ k : Fin d, ∑ i : Fin d, S k i * S k i) +
      8 * Z * (∑ k : Fin d, Zk k * ∑ i : Fin d, W i * S k i) +
      8 * (∑ k : Fin d, Zk k * Zk k) * (∑ i : Fin d, W i * W i) := by
    rw [mul_assoc (8 : ℝ) (∑ k : Fin d, Zk k * Zk k), Finset.sum_mul_sum]
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [← e]
  exact h

/-- The real-number core of the Bernstein subsolution estimate. -/
theorem bernstein_algebra {Z τ c dd Pp Sq X Zk2 : ℝ} (hkey : 0 ≤ 2 * Z * Z * Sq + 8 * Z * X + 8 * Zk2 * Pp)
    (hτ : 0 ≤ τ) (hP : 0 ≤ Pp) (hZ0 : 0 ≤ Z) (hZ1 : Z ≤ 1) (hcτ : c * τ ≤ 1)
    (hdd : 0 ≤ dd) (hZk2 : Zk2 ≤ 4 * c) :
    (Z * Z * τ) * (-2 * Sq) + Pp * (Z * Z - τ * (2 * Z * (-2 * c * dd) + 2 * Zk2)) -
      2 * (4 * τ * Z * X) - 2 * ((25 + 4 * dd) / 2) * Pp ≤ 0 := by
  have b1 : Z * Z ≤ 1 := by
    calc Z * Z ≤ 1 * 1 := mul_le_mul hZ1 hZ1 hZ0 zero_le_one
      _ = 1 := one_mul 1
  have b2 : c * τ * Z ≤ 1 := by
    calc c * τ * Z ≤ 1 * 1 := mul_le_mul hcτ hZ1 hZ0 zero_le_one
      _ = 1 := one_mul 1
  have b3 : τ * Zk2 ≤ 4 := by
    calc τ * Zk2 ≤ τ * (4 * c) := mul_le_mul_of_nonneg_left hZk2 hτ
      _ = 4 * (c * τ) := by ring
      _ ≤ 4 * 1 := by linarith
      _ = 4 := by ring
  have b4 : dd * (c * τ * Z) ≤ dd := mul_le_of_le_one_right hdd b2
  have hb : Z * Z + 4 * c * dd * τ * Z + 6 * (τ * Zk2) - 2 * ((25 + 4 * dd) / 2) ≤ 0 := by
    have : 4 * c * dd * τ * Z = 4 * (dd * (c * τ * Z)) := by ring
    rw [this]
    linarith
  have h1 : Pp * (Z * Z + 4 * c * dd * τ * Z + 6 * (τ * Zk2) - 2 * ((25 + 4 * dd) / 2)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hP hb
  have h2 : 0 ≤ τ * (2 * Z * Z * Sq + 8 * Z * X + 8 * Zk2 * Pp) := mul_nonneg hτ hkey
  have e : (Z * Z * τ) * (-2 * Sq) + Pp * (Z * Z - τ * (2 * Z * (-2 * c * dd) + 2 * Zk2)) -
      2 * (4 * τ * Z * X) - 2 * ((25 + 4 * dd) / 2) * Pp =
      Pp * (Z * Z + 4 * c * dd * τ * Z + 6 * (τ * Zk2) - 2 * ((25 + 4 * dd) / 2)) -
        τ * (2 * Z * Z * Sq + 8 * Z * X + 8 * Zk2 * Pp) := by
    ring
  rw [e]
  linarith

/-- The Bernstein quantity `G = Z² (t - t₀) |∇F|² + ((25 + 4d)/2) F²`, `Z = 1 - |x - x₀|²/ρ²`. -/
def jBernstein (F : ℝ × Vec d → ℝ) (x₀ : Vec d) (t₀ ρ : ℝ) : ℝ × Vec d → ℝ :=
  fun q => jCutA x₀ t₀ (ρ ^ 2)⁻¹ q * jGradSq F q + ((25 + 4 * (d : ℝ)) / 2) * (F q * F q)

theorem JSm.jBernstein {Ω : Set (ℝ × Vec d)} (hΩ : IsOpen Ω) {F : ℝ × Vec d → ℝ}
    (hF : JSm Ω F) (x₀ : Vec d) (t₀ ρ : ℝ) : JSm Ω (jBernstein F x₀ t₀ ρ) := by
  unfold PDE.jBernstein
  exact (((jsm_cutA x₀ t₀ _).mono (Set.subset_univ _)).mul (hF.jGradSq hΩ)).add
    (contDiffOn_const.mul (hF.mul hF))

theorem jBernstein_sub_nonpos {Ω : Set (ℝ × Vec d)} (hΩ : IsOpen Ω) {F : ℝ × Vec d → ℝ}
    (hF : JSm Ω F) (hheat : EqOn (jEt F) (jLap F) Ω) {x₀ : Vec d} {t₀ ρ : ℝ} (hρ : 0 < ρ)
    {p : ℝ × Vec d} (hp : p ∈ Ω) (ht : t₀ ≤ p.1) (hτ : p.1 - t₀ ≤ ρ ^ 2)
    (hx : jDistSq x₀ p ≤ ρ ^ 2) :
    jEt (jBernstein F x₀ t₀ ρ) p - jLap (jBernstein F x₀ t₀ ρ) p ≤ 0 := by
  set c : ℝ := (ρ ^ 2)⁻¹ with hc
  have hρ2 : 0 < ρ ^ 2 := pow_pos hρ 2
  have hc0 : 0 < c := inv_pos.2 hρ2
  have hcρ : c * ρ ^ 2 = 1 := inv_mul_cancel₀ hρ2.ne'
  have main := jEt_sub_jLap_bernstein hΩ hF hheat (a := jCutA x₀ t₀ c)
    ((jsm_cutA x₀ t₀ c).mono (Set.subset_univ _)) ((25 + 4 * (d : ℝ)) / 2) hp
  unfold jBernstein
  rw [← hc, main]
  set Z : ℝ := jCutZ x₀ c p with hZ
  set τ : ℝ := p.1 - t₀ with hτdef
  set Zk : Fin d → ℝ := fun k => -2 * c * (p.2 k - x₀ k) with hZk
  set W : Fin d → ℝ := fun i => jEx i F p with hW
  set S : Fin d → Fin d → ℝ := fun k i => jEx k (jEx i F) p with hS
  have hD0 : 0 ≤ jDistSq x₀ p :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hZ1 : Z ≤ 1 := by
    have : 0 ≤ c * jDistSq x₀ p := mul_nonneg hc0.le hD0
    simp only [hZ, jCutZ]
    linarith
  have hcD : c * jDistSq x₀ p ≤ 1 := by
    calc c * jDistSq x₀ p ≤ c * ρ ^ 2 := mul_le_mul_of_nonneg_left hx hc0.le
      _ = 1 := hcρ
  have hZ0 : 0 ≤ Z := by
    simp only [hZ, jCutZ]
    linarith
  have hcτ : c * τ ≤ 1 := by
    calc c * τ ≤ c * ρ ^ 2 := mul_le_mul_of_nonneg_left hτ hc0.le
      _ = 1 := hcρ
  have hZk2eq : ∑ k : Fin d, Zk k * Zk k = 4 * c * (c * jDistSq x₀ p) := by
    unfold jDistSq
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [hZk]
    ring
  have hZk2 : ∑ k : Fin d, Zk k * Zk k ≤ 4 * c := by
    rw [hZk2eq]
    calc 4 * c * (c * jDistSq x₀ p) ≤ 4 * c * 1 :=
          mul_le_mul_of_nonneg_left hcD (by positivity)
      _ = 4 * c := mul_one _
  have hPp : jGradSq F p = ∑ i : Fin d, W i * W i := rfl
  have hP0 : 0 ≤ jGradSq F p := by
    rw [hPp]; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hX : ∑ k : Fin d, jEx k (jCutA x₀ t₀ c) p * jEx k (jGradSq F) p =
      4 * τ * Z * ∑ k : Fin d, Zk k * ∑ i : Fin d, W i * S k i := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [jEx_cutA, jEx_jGradSq hΩ hF k hp]
    have : ∑ i : Fin d, 2 * (jEx i F p * jEx k (jEx i F) p) =
        2 * ∑ i : Fin d, W i * S k i := by
      rw [Finset.mul_sum]
    rw [this]
    simp only [hZk]
    ring
  have hkey := bernstein_complete_square Zk W S Z
  rw [← hPp] at hkey
  have hjEt := jEt_cutA x₀ t₀ c p
  have hjLap := jLap_cutA x₀ t₀ c p
  have hA : jCutA x₀ t₀ c p = (Z * Z) * τ := rfl
  rw [hX, hjEt, hjLap, hA]
  have halg := bernstein_algebra (c := c) (dd := (d : ℝ)) (Pp := jGradSq F p)
    (Sq := ∑ k : Fin d, ∑ i : Fin d, S k i * S k i)
    (X := ∑ k : Fin d, Zk k * ∑ i : Fin d, W i * S k i) (Zk2 := ∑ k : Fin d, Zk k * Zk k)
    hkey (sub_nonneg.2 ht) hP0 hZ0 hZ1 hcτ (Nat.cast_nonneg d) hZk2
  exact halg

end

end PDE
