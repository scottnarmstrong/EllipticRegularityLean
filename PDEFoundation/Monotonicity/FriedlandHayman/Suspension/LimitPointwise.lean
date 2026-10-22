module

public import PDEFoundation.Monotonicity.FriedlandHayman.Suspension.Rayleigh
public import PDEFoundation.Monotonicity.FriedlandHayman.Suspension.Beta

/-!
# Friedland--Hayman: pointwise behaviour of the angular integrands

Pointwise limits (as the cutoff `ε → 0`), domination, and the reduction of the limiting integrands to the
Beta-type integrands `sin^{N-1} cos^q`.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PDE.FHLane

noncomputable section

namespace Susp

/-- The Beta-type integrand `sin^{N-1} θ cos^q θ`. -/
def sinCosInt (N : ℕ) (q θ : ℝ) : ℝ := Real.sin θ ^ (N - 1) * Real.cos θ ^ q

/-- The limiting numerator integrand. -/
def numLim (n N : ℕ) (a I J θ : ℝ) : ℝ :=
  Real.sin θ ^ (N - 1) * (Real.cos θ ^ (n - 1) *
    ((1 - Real.cos θ ^ 2) * ((a * Real.cos θ ^ (a - 1)) ^ 2 * I) +
      (Real.cos θ ^ a / Real.cos θ) ^ 2 * J))

/-- The limiting denominator integrand. -/
def denLim (n N : ℕ) (a I θ : ℝ) : ℝ :=
  Real.sin θ ^ (N - 1) * (Real.cos θ ^ (n - 1) * ((Real.cos θ ^ a) ^ 2 * I))

theorem rpow_pow_mul {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    c ^ (n - 1) * (c ^ x) ^ 2 = c ^ ((n : ℝ) - 1 + 2 * x) := by
  have hcast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by rw [Nat.cast_sub hn]; simp
  rw [← Real.rpow_natCast c (n - 1), hcast, ← Real.rpow_natCast (c ^ x) 2, ← Real.rpow_mul hc.le,
    ← Real.rpow_add hc]
  norm_num
  ring_nf

theorem rpow_sq_div {c : ℝ} (hc : 0 < c) (a : ℝ) : (c ^ a / c) ^ 2 = (c ^ (a - 1)) ^ 2 := by
  rw [Real.rpow_sub_one hc.ne']

theorem numLim_eq {n N : ℕ} (hn : 1 ≤ n) {a I J θ : ℝ} (hc : 0 < Real.cos θ) :
    numLim n N a I J θ =
      a ^ 2 * I * (sinCosInt N ((n : ℝ) + 2 * a - 3) θ - sinCosInt N ((n : ℝ) + 2 * a - 3 + 2) θ) +
        J * sinCosInt N ((n : ℝ) + 2 * a - 3) θ := by
  unfold numLim sinCosInt
  generalize Real.cos θ = c at hc ⊢
  have h1 := rpow_pow_mul hc hn (a - 1)
  have h2 : c ^ ((n : ℝ) + 2 * a - 3 + 2) = c ^ 2 * c ^ ((n : ℝ) + 2 * a - 3) := by
    rw [Real.rpow_add hc, Real.rpow_two, mul_comm]
  have hE : c ^ (n - 1) * (c ^ (a - 1)) ^ 2 = c ^ ((n : ℝ) + 2 * a - 3) := by
    rw [h1]; congr 1; ring
  rw [rpow_sq_div hc, h2]
  calc _ = Real.sin θ ^ (N - 1) * ((1 - c ^ 2) * a ^ 2 * I * (c ^ (n - 1) * (c ^ (a - 1)) ^ 2) +
        J * (c ^ (n - 1) * (c ^ (a - 1)) ^ 2)) := by ring
    _ = _ := by rw [hE]; ring

theorem denLim_eq {n N : ℕ} (hn : 1 ≤ n) {a I θ : ℝ} (hc : 0 < Real.cos θ) :
    denLim n N a I θ = I * sinCosInt N ((n : ℝ) + 2 * a - 3 + 2) θ := by
  unfold denLim sinCosInt
  generalize Real.cos θ = c at hc ⊢
  have h1 := rpow_pow_mul hc hn a
  have h2 : c ^ ((n : ℝ) + 2 * a - 3 + 2) = c ^ ((n : ℝ) - 1 + 2 * a) := by
    congr 1; ring
  rw [h2, ← h1]
  ring

theorem tendsto_numInt {n N : ℕ} {a I J θ : ℝ} (hc : 0 < Real.cos θ) :
    Tendsto (fun ε => numInt n N a I J ε θ) (𝓝[>] 0) (𝓝 (numLim n N a I J θ)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < Real.cos θ / 2 by positivity)] with ε hε
  have h1 : 2 * ε < Real.cos θ := by linarith [hε.2]
  unfold numInt numLim
  rw [radProf_eq_rpow hε.1 h1.le, radProfD_eq hε.1 h1]

theorem tendsto_denInt {n N : ℕ} {a I θ : ℝ} (hc : 0 < Real.cos θ) :
    Tendsto (fun ε => denInt n N a I ε θ) (𝓝[>] 0) (𝓝 (denLim n N a I θ)) := by
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < Real.cos θ / 2 by positivity)] with ε hε
  have h1 : 2 * ε < Real.cos θ := by linarith [hε.2]
  unfold denInt denLim
  rw [radProf_eq_rpow hε.1 h1.le]

theorem numInt_le {n N : ℕ} (hn : 1 ≤ n) {a I J ε θ K : ℝ} (hε : 0 < ε) (ha : 0 ≤ a)
    (hI : 0 ≤ I) (hJ : 0 ≤ J) (hK : ∀ x, |deriv Real.smoothTransition x| ≤ K) (hK0 : 0 ≤ K)
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |numInt n N a I J ε θ| ≤
      sinCosInt N ((n : ℝ) + 2 * a - 3) θ * ((2 * K + a) ^ 2 * I + J + I) := by
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hgd := abs_radProfD_le hε ha hc hK hK0
  have hg := abs_radProf_le (ε := ε) (a := a) hc.le
  unfold numInt sinCosInt
  have h1 := rpow_pow_mul hc hn (a - 1)
  have hE : Real.cos θ ^ (n - 1) * (Real.cos θ ^ (a - 1)) ^ 2 =
      Real.cos θ ^ ((n : ℝ) + 2 * a - 3) := by rw [h1]; congr 1; ring
  generalize Real.cos θ = c at hc hc1 hgd hg hE ⊢
  generalize radProfD ε a c = gd at hgd ⊢
  generalize radProf ε a c = g at hg ⊢
  have hq : 0 ≤ c ^ (a - 1) := Real.rpow_nonneg hc.le _
  have hsn : 0 ≤ Real.sin θ ^ (N - 1) := by positivity
  have hcn : 0 ≤ c ^ (n - 1) := by positivity
  have hgd2 : gd ^ 2 ≤ ((2 * K + a) * c ^ (a - 1)) ^ 2 := by
    rw [← sq_abs gd]; exact pow_le_pow_left₀ (abs_nonneg _) hgd 2
  have hg2 : (g / c) ^ 2 ≤ (c ^ (a - 1)) ^ 2 := by
    rw [← rpow_sq_div hc, ← sq_abs (g / c), abs_div, abs_of_pos hc]
    exact pow_le_pow_left₀ (by positivity) (div_le_div_of_nonneg_right hg hc.le) 2
  have hterm : 0 ≤ (1 - c ^ 2) * (gd ^ 2 * I) + (g / c) ^ 2 * J := by
    have : 0 ≤ 1 - c ^ 2 := by nlinarith
    positivity
  rw [abs_of_nonneg (by positivity)]
  have hmain : (1 - c ^ 2) * (gd ^ 2 * I) + (g / c) ^ 2 * J ≤
      ((2 * K + a) ^ 2 * I + J + I) * (c ^ (a - 1)) ^ 2 := by
    have h2 : (1 - c ^ 2) * (gd ^ 2 * I) ≤ ((2 * K + a) * c ^ (a - 1)) ^ 2 * I := by
      have : 0 ≤ 1 - c ^ 2 := by nlinarith
      calc (1 - c ^ 2) * (gd ^ 2 * I) ≤ 1 * (gd ^ 2 * I) :=
            mul_le_mul_of_nonneg_right (by nlinarith) (by positivity)
        _ ≤ _ := by rw [one_mul]; exact mul_le_mul_of_nonneg_right hgd2 hI
    have h3 : (g / c) ^ 2 * J ≤ (c ^ (a - 1)) ^ 2 * J := mul_le_mul_of_nonneg_right hg2 hJ
    have h4 : 0 ≤ (c ^ (a - 1)) ^ 2 * I := by positivity
    nlinarith
  calc Real.sin θ ^ (N - 1) * (c ^ (n - 1) * ((1 - c ^ 2) * (gd ^ 2 * I) + (g / c) ^ 2 * J))
      ≤ Real.sin θ ^ (N - 1) * (c ^ (n - 1) * (((2 * K + a) ^ 2 * I + J + I) * (c ^ (a - 1)) ^ 2)) := by
        gcongr
    _ = Real.sin θ ^ (N - 1) * c ^ ((n : ℝ) + 2 * a - 3) * ((2 * K + a) ^ 2 * I + J + I) := by
        rw [← hE]; ring

theorem denInt_le {n N : ℕ} (hn : 1 ≤ n) {a I J ε θ K : ℝ}
    (hI : 0 ≤ I) (hJ : 0 ≤ J) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    |denInt n N a I ε θ| ≤
      sinCosInt N ((n : ℝ) + 2 * a - 3) θ * ((2 * K + a) ^ 2 * I + J + I) := by
  have hc : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩
  have hs : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 (by linarith [hθ.2, Real.pi_pos])
  have hc1 : Real.cos θ ≤ 1 := Real.cos_le_one θ
  have hg := abs_radProf_le (ε := ε) (a := a) hc.le
  unfold denInt sinCosInt
  have h1 := rpow_pow_mul hc hn a
  have hE : Real.cos θ ^ (n - 1) * (Real.cos θ ^ a) ^ 2 =
      Real.cos θ ^ ((n : ℝ) + 2 * a - 3 + 2) := by rw [h1]; congr 1; ring
  have hle : Real.cos θ ^ ((n : ℝ) + 2 * a - 3 + 2) ≤ Real.cos θ ^ ((n : ℝ) + 2 * a - 3) :=
    Real.rpow_le_rpow_of_exponent_ge hc hc1 (by linarith)
  generalize Real.cos θ = c at hc hc1 hg hE hle ⊢
  generalize radProf ε a c = g at hg ⊢
  have hsn : 0 ≤ Real.sin θ ^ (N - 1) := by positivity
  have hcn : 0 ≤ c ^ (n - 1) := by positivity
  have hg2 : g ^ 2 ≤ (c ^ a) ^ 2 := by
    rw [← sq_abs g]; exact pow_le_pow_left₀ (abs_nonneg _) hg 2
  have hpq : 0 ≤ c ^ ((n : ℝ) + 2 * a - 3) := Real.rpow_nonneg hc.le _
  rw [abs_of_nonneg (by positivity)]
  have hM : I ≤ (2 * K + a) ^ 2 * I + J + I := by
    have : 0 ≤ (2 * K + a) ^ 2 * I := by positivity
    linarith
  calc Real.sin θ ^ (N - 1) * (c ^ (n - 1) * (g ^ 2 * I))
      ≤ Real.sin θ ^ (N - 1) * (c ^ (n - 1) * ((c ^ a) ^ 2 * I)) := by gcongr
    _ = Real.sin θ ^ (N - 1) * (c ^ ((n : ℝ) + 2 * a - 3 + 2) * I) := by rw [← hE]; ring
    _ ≤ Real.sin θ ^ (N - 1) * (c ^ ((n : ℝ) + 2 * a - 3) * ((2 * K + a) ^ 2 * I + J + I)) := by
        gcongr
    _ = _ := by ring

end Susp

end

end PDE.FHLane
