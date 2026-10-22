module

public import EllipticRegularity.Parabolic.NashKernel.KernelLimitStep

/-!
# Abstract dyadic kernel construction

`PDE.NashKernelLimit.exists_kernel`: a family `T Q` of nonnegative measurable functions on `Vec d`,
indexed by half-open dyadic cubes `Q`, with `T Q ≤ M vol(Q)` a.e. and additive on children a.e.,
is the family of integrals `x ↦ ∫_Q P(x, y) dy` of one jointly measurable kernel `0 ≤ P ≤ M`.

Proof: for a.e. `x` (all countably many pointwise hypotheses hold) the step kernels
`y ↦ P_n(x, y)` form a bounded martingale for the dyadic filtration on each finite window; Doob's
a.e. convergence theorem gives pointwise convergence of `P_n(x, ·)`.  `P` is the clamped
`limsup` (hence jointly measurable); dominated convergence passes to the limit in the refinement
identity.
-/

@[expose] public section

namespace PDE.NashKernelLimit

open MeasureTheory Set Filter Topology PDE.NashKernelDyadic
open scoped NNReal ENNReal

variable {d : ℕ}

/-- The pointwise limsup candidate for the kernel, clamped to `[0, M]`. -/
noncomputable def limKernel (M : ℝ) (T : ℕ → (Fin d → ℤ) → PDE.Vec d → ℝ) (x y : PDE.Vec d) : ℝ :=
  min M (limsup (fun n => ENNReal.ofReal (stepKernel T n x y)) atTop).toReal

theorem measurable_limKernel {M : ℝ} {T : ℕ → (Fin d → ℤ) → PDE.Vec d → ℝ}
    (hT : ∀ n k, Measurable (T n k)) :
    Measurable (fun p : PDE.Vec d × PDE.Vec d => limKernel M T p.1 p.2) := by
  refine measurable_const.min ?_
  refine ENNReal.measurable_toReal.comp ?_
  exact Measurable.limsup fun n => ENNReal.measurable_ofReal.comp (measurable_stepKernel hT n)

theorem limKernel_bounds {M : ℝ} (hM : 0 ≤ M) (T : ℕ → (Fin d → ℤ) → PDE.Vec d → ℝ)
    (x y : PDE.Vec d) : 0 ≤ limKernel M T x y ∧ limKernel M T x y ≤ M :=
  ⟨le_min hM ENNReal.toReal_nonneg, min_le_left _ _⟩

theorem ae_tendsto_stepKernel {M : ℝ} {T : ℕ → (Fin d → ℤ) → PDE.Vec d → ℝ}
    {x : PDE.Vec d} (hx : Good M T x) :
    ∀ᵐ y, Tendsto (fun n => stepKernel T n x y) atTop (𝓝 (limKernel M T x y)) := by
  have hwin : ∀ N : ℕ, ∀ᵐ y ∂(volume.restrict (win (box (d := d) N))),
      Tendsto (fun n => stepKernel T n x y) atTop (𝓝 (limKernel M T x y)) := by
    intro N
    have hfin : IsFiniteMeasure (volume.restrict (win (box (d := d) N))) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact volume_win_lt_top _⟩
    have hmart := martingale_stepKernel hx (box (d := d) N)
    have hbdd : ∀ n, eLpNorm (stepKernel T n x) 1 (volume.restrict (win (box (d := d) N))) ≤
        ((volume.restrict (win (box (d := d) N))) univ * ENNReal.ofReal M).toNNReal := by
      intro n
      have h := eLpNorm_le_of_ae_bound (p := 1) (μ := volume.restrict (win (box (d := d) N)))
        (measurable_stepKernel_right n x).aestronglyMeasurable (C := M) (ae_of_all _ fun y => by
          have := stepKernel_bounds hx n y
          rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2)
      simp only [ENNReal.toReal_one, inv_one, ENNReal.rpow_one] at h
      rw [ENNReal.coe_toNNReal]
      · exact h
      · exact ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
    filter_upwards [hmart.submartingale.ae_tendsto_limitProcess hbdd] with y hy
    set L := (dyadicFiltration d).limitProcess (fun n => stepKernel T n x)
      (volume.restrict (win (box (d := d) N))) y
    have hL0 : 0 ≤ L := ge_of_tendsto' hy fun n => (stepKernel_bounds hx n y).1
    have hLM : L ≤ M := le_of_tendsto' hy fun n => (stepKernel_bounds hx n y).2
    have hlim : limKernel M T x y = L := by
      have h1 : Tendsto (fun n => ENNReal.ofReal (stepKernel T n x y)) atTop
          (𝓝 (ENNReal.ofReal L)) := (ENNReal.tendsto_ofReal hy)
      simp only [limKernel, h1.limsup_eq, ENNReal.toReal_ofReal hL0]
      exact min_eq_right hLM
    rw [hlim]; exact hy
  have h := (ae_restrict_iUnion_iff (fun N : ℕ => win (box (d := d) N)) _).mpr hwin
  rwa [iUnion_win_box, Measure.restrict_univ] at h

theorem setIntegral_cube_stepKernel_of_le {M : ℝ} {T : ℕ → (Fin d → ℤ) → PDE.Vec d → ℝ}
    {x : PDE.Vec d} (hx : Good M T x) {m n : ℕ} (hmn : m ≤ n) (k : Fin d → ℤ) :
    ∫ y in cube m k, stepKernel T n x y = T m k x := by
  obtain ⟨N, hN⟩ := exists_cube_subset_win_box (d := d) m k
  have hfin : IsFiniteMeasure (volume.restrict (win (box (d := d) N))) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact volume_win_lt_top _⟩
  have hmart := martingale_stepKernel hx (box (d := d) N)
  have hs : MeasurableSet[dyadicFiltration d m] (cube m k) :=
    ⟨{k}, measurableSet_singleton k, (cube_eq_preimage m k).symm⟩
  have h := hmart.setIntegral_eq hmn hs
  rw [Measure.restrict_restrict (measurableSet_cube m k), inter_eq_left.mpr hN] at h
  rw [← h, setIntegral_cube_stepKernel_self]

theorem setIntegral_limKernel {M : ℝ} {T : ℕ → (Fin d → ℤ) → PDE.Vec d → ℝ}
    {x : PDE.Vec d} (hx : Good M T x) (m : ℕ)
    (k : Fin d → ℤ) : ∫ y in cube m k, limKernel M T x y = T m k x := by
  have hfin : IsFiniteMeasure (volume.restrict (cube (d := d) m k)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact volume_cube_lt_top m k⟩
  have hlim := tendsto_integral_of_dominated_convergence (μ := volume.restrict (cube m k))
    (F := fun n y => stepKernel T n x y) (f := fun y => limKernel M T x y) (fun _ => M)
    (fun n => (measurable_stepKernel_right n x).aestronglyMeasurable) (integrable_const M)
    (fun n => ae_of_all _ fun y => by
      have := stepKernel_bounds hx n y
      rw [Real.norm_eq_abs, abs_of_nonneg this.1]; exact this.2)
    (ae_restrict_of_ae (ae_tendsto_stepKernel hx))
  have hconst : Tendsto (fun n => ∫ y in cube m k, stepKernel T n x y) atTop (𝓝 (T m k x)) :=
    tendsto_const_nhds.congr' (by
      filter_upwards [eventually_ge_atTop m] with n hn
      exact (setIntegral_cube_stepKernel_of_le hx hn k).symm)
  exact tendsto_nhds_unique hlim hconst

/-- **Abstract dyadic kernel.**  Let `M ≥ 0` and let `T n k : Vec d → ℝ` (`n : ℕ`, `k : Fin d → ℤ`
indexing the dyadic cube `cube n k` of side `2^{-n}`) be measurable, with
`0 ≤ T n k ≤ M vol(cube n k)` a.e. and `T n k = ∑_{ε} T (n+1) (child k ε)` a.e. over the `2^d`
children.  Then there is a jointly measurable `P` with `0 ≤ P ≤ M` everywhere and
`∫_{cube n k} P(x, y) dy = T n k x` for a.e. `x`, for every dyadic cube. -/
theorem exists_kernel {M : ℝ} (hM : 0 ≤ M) {T : ℕ → (Fin d → ℤ) → PDE.Vec d → ℝ}
    (hT : ∀ n k, Measurable (T n k))
    (hbd : ∀ n k, ∀ᵐ x, 0 ≤ T n k x ∧ T n k x ≤ M * (volume (cube n k)).toReal)
    (hadd : ∀ n k, ∀ᵐ x, T n k x = ∑ ε : Fin d → Bool, T (n + 1) (child k ε) x) :
    ∃ P : PDE.Vec d → PDE.Vec d → ℝ, Measurable (Function.uncurry P) ∧
      (∀ x y, 0 ≤ P x y ∧ P x y ≤ M) ∧
      ∀ n k, ∀ᵐ x, ∫ y in cube n k, P x y = T n k x := by
  have hgood : ∀ᵐ x, Good M T x :=
    ae_all_iff.mpr fun n => ae_all_iff.mpr fun k => (hbd n k).and (hadd n k)
  refine ⟨limKernel M T, measurable_limKernel hT, limKernel_bounds hM T, fun n k => ?_⟩
  filter_upwards [hgood] with x hx
  exact setIntegral_limKernel hx n k

end PDE.NashKernelLimit
