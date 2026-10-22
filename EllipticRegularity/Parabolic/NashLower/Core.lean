module

public import EllipticRegularity.Parabolic.NashLower.Step
public import EllipticRegularity.Parabolic.NashLower.Cover
public import EllipticRegularity.Parabolic.NashLower.Geometry

/-!
# The Harnack chain for a nonnegative solution on a long cylinder

Given a nonnegative solution `w` on `ℝ^d × [s,T]` with `T ≥ 2t - s` whose mass on `B(y,ρ)` at time
`s + (t-s)/4` is at least `1/2`, the pigeonhole of `Cover` produces a small ball with large
`essSup`, and `N = ⌈22(1 + R² + |x-y|²/h)⌉` local Harnack steps transport it to time `t`, giving
`w(t,·) ≥ K H^{-N}` a.e. on `B(x, √h/8)` with `K = 1/(4|B(y,ρ)|)`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE.Parabolic.NashLower

theorem chain_to_final_time {d : ℕ} {Lam H : ℝ} (hH2 : 2 ≤ H) (hH : LocalHarnackAt d Lam H)
    {a : ParCoeffField d} {s t T : ℝ} (hst : s < t) (hT : t + (t - s) ≤ T)
    (hcoef : IsParabolicCoeff 1 Lam a univ (Icc s T))
    (w : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hw : IsParabolicWeakSolution a univ (Icc s T) w)
    (hpos : ∀ τ ∈ Icc s T, ∀ᵐ x : Vec d, 0 ≤ w.toFun (x, τ))
    (x y : Vec d) {R₁ : ℝ} (hR₁ : 0 < R₁)
    (hmass : (1 / 2 : ℝ) ≤ ∫ z in euclideanBall y (R₁ * Real.sqrt (t - s)),
      w.toFun (z, s + (t - s) / 4)) :
    ∃ N : ℕ, (N : ℝ) ≤ 22 * (1 + R₁ ^ 2 + euclideanSqDist x y / (t - s)) + 1 ∧
      ∀ᵐ x'' ∂(volume.restrict (euclideanBall x (Real.sqrt (t - s) / 8))),
        (1 / (4 * (volume (euclideanBall y (R₁ * Real.sqrt (t - s)))).toReal)) / H ^ N ≤
          w.toFun (x'', t) := by
  obtain ⟨h, hh_def⟩ : ∃ h : ℝ, h = t - s := ⟨_, rfl⟩
  rw [← hh_def] at hmass hT ⊢
  have hh : 0 < h := by rw [hh_def]; exact sub_pos.2 hst
  have hHpos : 0 < H := by linarith
  obtain ⟨Dsq, hDsq⟩ : ∃ D : ℝ, D = euclideanSqDist x y := ⟨_, rfl⟩
  rw [← hDsq]
  have hD0 : 0 ≤ Dsq := by rw [hDsq]; exact euclideanSqDist_nonneg x y
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = 1 + R₁ ^ 2 + Dsq / h := ⟨_, rfl⟩
  rw [← hq]
  have hq1 : 1 ≤ q := by
    have : 0 ≤ R₁ ^ 2 + Dsq / h := by positivity
    linarith
  obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = ⌈22 * q⌉₊ := ⟨_, rfl⟩
  have hN22 : 22 * q ≤ (N : ℝ) := by rw [hNdef]; exact Nat.le_ceil _
  have hN_le : (N : ℝ) ≤ 22 * q + 1 := by
    rw [hNdef]; exact (Nat.ceil_lt_add_one (by positivity)).le
  have hN22' : (22 : ℝ) ≤ N := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hN0 : N ≠ 0 := by
    intro h0; rw [h0] at hNpos; simp at hNpos
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = 3 * h / (4 * N) := ⟨_, rfl⟩
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = R₁ * Real.sqrt h := ⟨_, rfl⟩
  rw [← hρdef] at hmass ⊢
  obtain ⟨K, hK⟩ : ∃ K : ℝ, K = 1 / (4 * (volume (euclideanBall y ρ)).toReal) := ⟨_, rfl⟩
  rw [← hK]
  refine ⟨N, hN_le, ?_⟩
  have hθ : 0 < θ := by rw [hθdef]; positivity
  have hNθ : (N : ℝ) * θ = 3 * h / 4 := by rw [hθdef]; field_simp
  have hθh : θ ≤ h / 6 := by
    rw [hθdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    have := mul_le_mul_of_nonneg_left hN22' hh.le
    linarith
  have hρ : 0 < ρ := by rw [hρdef]; exact mul_pos hR₁ (Real.sqrt_pos.2 hh)
  have hρsq : ρ ^ 2 = R₁ ^ 2 * h := by rw [hρdef, mul_pow, Real.sq_sqrt hh.le]
  have hr : 0 < Real.sqrt θ / 4 := by positivity
  -- the pigeonhole centre
  obtain ⟨z, hzB, hzsup⟩ := exists_center_essSup_ge y hρ hr
    (fun u => w.toFun (u, s + h / 4)) hmass
  rw [← hK] at hzsup
  have hVpos : 0 < (volume (euclideanBall y ρ)).toReal :=
    ENNReal.toReal_pos (volume_euclideanBall_pos y hρ).ne' (volume_euclideanBall_ne_top y hρ.le)
  have hKpos : 0 < K := by rw [hK]; positivity
  have hmpos : 0 < K / H ^ N := by positivity
  have hzy : euclideanSqDist y z < R₁ ^ 2 * h := by
    have : euclideanSqDist z y < ρ ^ 2 := hzB
    rw [euclideanSqDist_comm]; rwa [hρsq] at this
  have hK0 : ENNReal.ofReal K ≤ essSup (fun u => ENNReal.ofReal (w.toFun (u, s + h / 4)))
      (volume.restrict (euclideanBall z (Real.sqrt θ / 4))) := hzsup
  have key : ∀ x' ∈ euclideanBall x (Real.sqrt h / 8), ENNReal.ofReal (K / H ^ N) ≤
      essInf (fun u => ENNReal.ofReal (w.toFun (u, t)))
        (volume.restrict (euclideanBall x' (Real.sqrt θ / 4))) := by
    intro x' hx'
    have hx'sq : euclideanSqDist x' x < h / 64 := by
      have h1 : euclideanSqDist x' x < (Real.sqrt h / 8) ^ 2 := hx'
      have h2 : (Real.sqrt h / 8) ^ 2 = h / 64 := by
        rw [div_pow, Real.sq_sqrt hh.le]; norm_num
      linarith
    have hSq : euclideanSqDist x' z ≤ 4 * h * q := by
      have h1 := euclideanSqDist_le_four_mul x' x y z
      have h2 : 4 * h * q = 4 * h + 4 * h * R₁ ^ 2 + 4 * Dsq := by
        rw [hq]; field_simp
      have h3 : 0 ≤ h * R₁ ^ 2 := by positivity
      linarith [hzy, hh]
    have hzz : ∀ k : ℕ, euclideanSqDist (pathPt z x' N k) (pathPt z x' N (k + 1)) ≤ θ / 4 := by
      intro k
      rw [euclideanSqDist_pathPt_succ z x' hN0 k]
      have h1 : (1 / (N : ℝ)) ^ 2 * euclideanSqDist x' z ≤ (1 / (N : ℝ)) ^ 2 * (4 * h * q) :=
        mul_le_mul_of_nonneg_left hSq (by positivity)
      have h2 : (1 / (N : ℝ)) ^ 2 * (4 * h * q) ≤ θ / 4 := by
        rw [hθdef]
        have : (1 / (N : ℝ)) ^ 2 * (4 * h * q) = 4 * h * q / (N : ℝ) ^ 2 := by
          field_simp
        rw [this, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
        have h3 := mul_nonneg (mul_pos hh hNpos).le (sub_nonneg.2 hN22)
        have h4 : 0 < h * q * N := mul_pos (mul_pos hh (by linarith)) hNpos
        linarith
      exact h1.trans h2
    have hstep : ∀ k, k < N →
        essSup (fun u => ENNReal.ofReal (w.toFun (u, s + h / 4 + (k : ℝ) * θ)))
            (volume.restrict (euclideanBall (pathPt z x' N k) (Real.sqrt θ / 4))) ≤
          ENNReal.ofReal H *
            essInf (fun u => ENNReal.ofReal (w.toFun (u, s + h / 4 + ((k + 1 : ℕ) : ℝ) * θ)))
              (volume.restrict (euclideanBall (pathPt z x' N (k + 1)) (Real.sqrt θ / 4))) := by
      intro k hk
      have hk1 : ((k : ℝ) + 1) ≤ N := by exact_mod_cast hk
      have hkθ : ((k : ℝ) + 1) * θ ≤ N * θ := mul_le_mul_of_nonneg_right hk1 hθ.le
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      have h1 : s ≤ s + h / 4 + (k : ℝ) * θ - 3 * θ / 2 := by
        have : 0 ≤ (k : ℝ) * θ := mul_nonneg hk0 hθ.le
        linarith
      have h2 : s + h / 4 + (k : ℝ) * θ + 5 * θ / 4 ≤ T := by linarith
      have hτ : s + h / 4 + ((k + 1 : ℕ) : ℝ) * θ = s + h / 4 + (k : ℝ) * θ + θ := by
        push_cast; ring
      rw [hτ]
      exact harnack_step hH hcoef w hw hpos hθ _ _ (hzz k) h1 h2
    have h0 : ENNReal.ofReal K ≤
        essSup (fun u => ENNReal.ofReal (w.toFun (u, s + h / 4 + ((0 : ℕ) : ℝ) * θ)))
          (volume.restrict (euclideanBall (pathPt z x' N 0) (Real.sqrt θ / 4))) := by
      rw [pathPt_zero]
      have : s + h / 4 + ((0 : ℕ) : ℝ) * θ = s + h / 4 := by simp
      rw [this]; exact hK0
    have hfin := chain_lower w.toFun hHpos N (fun k => s + h / 4 + (k : ℝ) * θ) (pathPt z x' N) hr K
      hstep h0 (N - 1) (Nat.sub_lt (Nat.pos_of_ne_zero hN0) one_pos)
    have hk : N - 1 + 1 = N := Nat.sub_add_cancel (Nat.pos_of_ne_zero hN0)
    have hτN : s + h / 4 + (N : ℝ) * θ = t := by rw [hNθ]; linarith
    rw [hk, pathPt_self z x' hN0, hτN] at hfin
    exact hfin
  exact ae_ge_of_local_essInf x hr (fun u => w.toFun (u, t)) hmpos key
