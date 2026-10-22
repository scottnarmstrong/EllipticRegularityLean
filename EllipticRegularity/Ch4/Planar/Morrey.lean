module

public import EllipticRegularity.Ch4.Planar.MorreyScale
public import PDEFoundation.Regularity.InteriorCampanatoHolder

/-!
# Morrey's Dirichlet growth theorem (Lemma 4.25)

The case `α < 1` is the repository's interior Campanato Hölder theorem applied to the
normalized gradient-scale bound of `MorreyScale`.  The endpoint `α = 1` is obtained by
letting the exponent tend to `1`: all the representatives are continuous and agree
almost everywhere on the open half ball, hence agree everywhere there.
-/

@[expose] public section

namespace PDE.Ch4Planar

open MeasureTheory Filter Topology

variable {d : ℕ}

/-- Morrey growth, exponent `α < 1`. -/
theorem morrey_lt_one (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α K : ℝ), 0 < α → α < 1 → 0 ≤ K →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      (∀ x ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
        ∫ y in euclideanBall x r, vecNormSq (u.grad y) ≤ K * r ^ ((d : ℝ) - 2 + 2 * α)) →
        ∃ v : Vec d → ℝ, v =ᵐ[volumeOn (euclideanBall (0 : Vec d) (1 / 2))] u.toFun ∧
          EuclideanHolderSeminormLE (euclideanBall (0 : Vec d) (1 / 2)) v α
            (C * α⁻¹ * Real.sqrt K) := by
  obtain ⟨C₀, hC₀, hC₀'⟩ := exists_interiorCampanato_holder_constant (d := d) hd
  have hω : 0 < (volume (euclideanBall (0 : Vec d) 1)).toReal :=
    volume_euclideanBall_toReal_pos _ (by norm_num)
  refine ⟨C₀ / Real.sqrt (volume (euclideanBall (0 : Vec d) 1)).toReal, by positivity, ?_⟩
  intro α K hα hα1 hK u h
  have hscale := morrey_scale_bound hK u h
  obtain ⟨v, hv, hH⟩ := hC₀' hα hα1 (Real.sqrt_nonneg _) u hscale
  refine ⟨v, hv, ?_⟩
  have : C₀ * Real.sqrt (K / (volume (euclideanBall (0 : Vec d) 1)).toReal) / α =
      C₀ / Real.sqrt (volume (euclideanBall (0 : Vec d) 1)).toReal * α⁻¹ * Real.sqrt K := by
    rw [Real.sqrt_div hK]
    field_simp
  rw [← this]
  exact hH

/-- Morrey's Dirichlet growth theorem (Lemma 4.25), in the exact form of the
statement `exists_morrey_growth_constant`. -/
theorem exists_morrey_growth_constant_full (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α K : ℝ), 0 < α → α ≤ 1 → 0 ≤ K →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      (∀ x ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
        ∫ y in euclideanBall x r, vecNormSq (u.grad y) ≤ K * r ^ ((d : ℝ) - 2 + 2 * α)) →
        ∃ (v : Vec d → ℝ) (M : ℝ), v =ᵐ[volumeOn (euclideanBall (0 : Vec d) (1 / 2))] u.toFun ∧
          0 ≤ M ∧ EuclideanHolderSeminormLE (euclideanBall (0 : Vec d) (1 / 2)) v α M ∧
          M ≤ C * α⁻¹ * Real.sqrt K := by
  obtain ⟨C, hC, hM⟩ := morrey_lt_one (d := d) (by omega)
  refine ⟨C, hC, ?_⟩
  intro α K hα hα1 hK u h
  by_cases hlt : α < 1
  · obtain ⟨v, hv, hH⟩ := hM α K hα hlt hK u h
    exact ⟨v, C * α⁻¹ * Real.sqrt K, hv, by positivity, hH, le_rfl⟩
  · have hα1' : α = 1 := le_antisymm hα1 (not_lt.mp hlt)
    subst hα1'
    set S := euclideanBall (0 : Vec d) (1 / 2) with hS
    -- exponents `a n = (n+1)/(n+2) < 1`
    let a : ℕ → ℝ := fun n => 1 - 1 / ((n : ℝ) + 2)
    have ha0 : ∀ n, 0 < a n := by
      intro n
      have : 1 / ((n : ℝ) + 2) ≤ 1 / 2 :=
        one_div_le_one_div_of_le (by norm_num) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
      simp only [a]; linarith
    have ha1 : ∀ n, a n < 1 := by
      intro n
      have : 0 < 1 / ((n : ℝ) + 2) := by positivity
      simp only [a]; linarith
    have hgrowth : ∀ n : ℕ, ∀ x ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ, 0 < r → r ≤ 1 / 2 →
        ∫ y in euclideanBall x r, vecNormSq (u.grad y) ≤
          K * r ^ ((d : ℝ) - 2 + 2 * a n) := by
      intro n x hx r hr hr2
      refine (h x hx r hr hr2).trans (mul_le_mul_of_nonneg_left ?_ hK)
      apply Real.rpow_le_rpow_of_exponent_ge hr (by linarith)
      have := ha1 n
      linarith
    choose v hv hH using fun n => hM (a n) K (ha0 n) (ha1 n) hK u (hgrowth n)
    have hopen : IsOpen S := isOpen_euclideanBall _ _
    have hcont : ∀ n, ContinuousOn (v n) S := fun n =>
      (hH n).continuousOn (ha0 n)
        (mul_nonneg (mul_nonneg hC.le (inv_nonneg.mpr (ha0 n).le)) (Real.sqrt_nonneg _))
    have heq : ∀ n, Set.EqOn (v n) (v 0) S := fun n =>
      Measure.eqOn_open_of_ae_eq ((hv n).trans (hv 0).symm) hopen (hcont n) (hcont 0)
    refine ⟨v 0, C * (1 : ℝ)⁻¹ * Real.sqrt K, hv 0, by positivity, ?_, le_rfl⟩
    intro x hx y hy
    set t := vecEuclideanNorm (x - y) with ht
    have ht0 : 0 ≤ t := Real.sqrt_nonneg _
    have hbound : ∀ n, |v 0 x - v 0 y| ≤ C * (a n)⁻¹ * Real.sqrt K * t ^ (a n) := by
      intro n
      rw [← heq n hx, ← heq n hy]
      exact hH n x hx y hy
    rcases ht0.eq_or_lt with h0 | hpos
    · have := hbound 0
      rw [← h0, Real.zero_rpow (ha0 0).ne'] at this
      rw [← h0, Real.rpow_one, mul_zero]
      simpa using this
    · have hlim : Tendsto a atTop (𝓝 1) := by
        have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
          have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
          have h2 := (tendsto_add_atTop_iff_nat 1).mpr this
          refine h2.congr (fun n => ?_)
          push_cast; ring_nf
        simpa [a] using (tendsto_const_nhds (x := (1 : ℝ))).sub h1
      have hL : Tendsto (fun n => C * (a n)⁻¹ * Real.sqrt K * t ^ (a n)) atTop
          (𝓝 (C * (1 : ℝ)⁻¹ * Real.sqrt K * t ^ (1 : ℝ))) := by
        refine Tendsto.mul (Tendsto.mul (Tendsto.mul tendsto_const_nhds
          (hlim.inv₀ one_ne_zero)) tendsto_const_nhds) ?_
        exact ((Real.continuousAt_const_rpow hpos.ne').tendsto).comp hlim
      exact le_of_tendsto_of_tendsto' tendsto_const_nhds hL hbound

end PDE.Ch4Planar
