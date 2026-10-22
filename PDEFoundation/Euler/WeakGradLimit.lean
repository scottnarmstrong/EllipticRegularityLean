module

public import PDEFoundation.Euler.GradLimitBasic

/-!
# Weak gradient of an `L²` limit of smooth periodic divergence-free fields

Let `uₙ` be smooth periodic divergence-free fields whose vorticities `curl uₙ` converge in `L²(cube)`.
Then `∇uₙ` is Cauchy in `L²(cube)` (`‖∇(uₘ - uₙ)‖₂ = ‖curl uₘ - curl uₙ‖₂`), hence converges strongly to
some `G`; if moreover `uₙ → v` in `L²(cube)`, then `G` is the weak (periodic) gradient of `v`:
`∫_{cube} vᵢ ∂ⱼψ = -∫_{cube} Gᵢⱼ ψ` for every smooth periodic `ψ`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PDE

section Sub

variable {a b : Vec 2 → Vec 2}

theorem gradMat_sub (ha : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x i))
    (hb : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i)) (x : Vec 2) :
    gradMat (fun y => a y - b y) x = gradMat a x - gradMat b x := by
  funext i j
  show pd j (fun y => a y i - b y i) x = _
  rw [pd_sub (differentiable_of_contDiff_top (ha i)) (differentiable_of_contDiff_top (hb i))]
  rfl

theorem torusCurl_sub (ha : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x i))
    (hb : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i)) (x : Vec 2) :
    torusCurl (fun y => a y - b y) x = torusCurl a x - torusCurl b x := by
  unfold torusCurl
  show pd 0 (fun y => a y 1 - b y 1) x - pd 1 (fun y => a y 0 - b y 0) x = _
  rw [pd_sub (differentiable_of_contDiff_top (ha 1)) (differentiable_of_contDiff_top (hb 1)),
    pd_sub (differentiable_of_contDiff_top (ha 0)) (differentiable_of_contDiff_top (hb 0))]
  ring

theorem torusDiv_sub (ha : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x i))
    (hb : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i)) (x : Vec 2) :
    torusDiv (fun y => a y - b y) x = torusDiv a x - torusDiv b x := by
  unfold torusDiv
  show pd 0 (fun y => a y 0 - b y 0) x + pd 1 (fun y => a y 1 - b y 1) x = _
  rw [pd_sub (differentiable_of_contDiff_top (ha 0)) (differentiable_of_contDiff_top (hb 0)),
    pd_sub (differentiable_of_contDiff_top (ha 1)) (differentiable_of_contDiff_top (hb 1))]
  ring

theorem contDiff_sub_field (ha : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => a x i))
    (hb : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => b x i)) (i : Fin 2) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => (fun y => a y - b y) x i) :=
  ContDiff.sub (ha i) (hb i)

end Sub

/-- The gradient matrices of smooth periodic divergence-free fields with `L²`-convergent vorticities
converge strongly in `L²(cube)` (in the sup norm on `2 × 2` arrays). -/
theorem exists_gradMat_limit {u : ℕ → Vec 2 → Vec 2} {ω : Vec 2 → ℝ}
    (hu : ∀ n i, ContDiff ℝ (⊤ : ℕ∞) (fun x => u n x i)) (hup : ∀ n, IsTorusPeriodic (u n))
    (hdiv : ∀ n x, torusDiv (u n) x = 0)
    (hωconv : Tendsto (fun n => eLpNorm (fun x => torusCurl (u n) x - ω x) 2
      (volume.restrict torusCube)) atTop (𝓝 0)) :
    ∃ G : Vec 2 → Fin 2 → Fin 2 → ℝ, MemLp G 2 (volume.restrict torusCube) ∧
      Tendsto (fun n => eLpNorm (fun x => gradMat (u n) x - G x) 2 (volume.restrict torusCube))
        atTop (𝓝 0) := by
  have hc : ∀ n, MemLp (torusCurl (u n)) 2 (volume.restrict torusCube) :=
    fun n => memLp_cube_of_continuous (continuous_torusCurl (hu n)) 2
  refine exists_tendsto_eLpNorm_two_of_bound (f := fun n => gradMat (u n))
    (fun n => memLp_cube_of_continuous (continuous_gradMat (hu n)) 2) hωconv (fun m n => ?_)
  have hw : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => (fun y => u m y - u n y) x i) :=
    contDiff_sub_field (hu m) (hu n)
  have hwp : IsTorusPeriodic (fun y => u m y - u n y) := (hup m).sub (hup n)
  have hwd : ∀ x, torusDiv (fun y => u m y - u n y) x = 0 := fun x => by
    rw [torusDiv_sub (hu m) (hu n), hdiv m x, hdiv n x, sub_zero]
  have h1 : eLpNorm (gradMat (u m) - gradMat (u n)) 2 (volume.restrict torusCube) ≤
      eLpNorm (fun x => matFrobNorm (gradMat (fun y => u m y - u n y) x)) 2
        (volume.restrict torusCube) := by
    refine eLpNorm_mono ((continuous_gradMat (hu m)).sub (continuous_gradMat (hu n))).aestronglyMeasurable
      fun x => ?_
    have e : (gradMat (u m) - gradMat (u n)) x = gradMat (fun y => u m y - u n y) x :=
      (gradMat_sub (hu m) (hu n) x).symm
    rw [e, Real.norm_of_nonneg (matFrobNorm_nonneg _)]
    exact norm_le_matFrobNorm _
  rw [eLpNorm_matFrobNorm_gradMat_eq_curl hw hwp hwd] at h1
  refine h1.trans ?_
  have h2 : torusCurl (fun y => u m y - u n y) =
      (fun x => torusCurl (u m) x - ω x) - (fun x => torusCurl (u n) x - ω x) := by
    funext x
    rw [torusCurl_sub (hu m) (hu n)]
    simp only [Pi.sub_apply]
    ring
  rw [h2]
  exact eLpNorm_sub_le (by norm_num)

theorem memLp_apply_of_memLp_gradMat {G : Vec 2 → Fin 2 → Fin 2 → ℝ}
    (hG : MemLp G 2 (volume.restrict torusCube)) (i j : Fin 2) :
    MemLp (fun x => G x i j) 2 (volume.restrict torusCube) := by
  have hc : Continuous (fun A : Fin 2 → Fin 2 → ℝ => A i j) := by fun_prop
  refine hG.of_le ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact hc.comp_aestronglyMeasurable hG.aestronglyMeasurable
  · exact (norm_le_pi_norm (G x i) j).trans (norm_le_pi_norm (G x) i)

theorem eLpNorm_apply_le {f G : Vec 2 → Fin 2 → Fin 2 → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict torusCube))
    (hG : AEStronglyMeasurable G (volume.restrict torusCube)) (i j : Fin 2) :
    eLpNorm (fun x => f x i j - G x i j) 2 (volume.restrict torusCube) ≤
      eLpNorm (fun x => f x - G x) 2 (volume.restrict torusCube) := by
  have hc : Continuous (fun A : Fin 2 → Fin 2 → ℝ => A i j) := by fun_prop
  refine eLpNorm_mono ((hc.comp_aestronglyMeasurable hf).sub (hc.comp_aestronglyMeasurable hG)) fun x => ?_
  have := (norm_le_pi_norm ((f x - G x) i) j).trans (norm_le_pi_norm (f x - G x) i)
  simpa using this

/-- `L²` convergence gives convergence of pairings with a fixed `L²` function. -/
theorem tendsto_integral_mul_cube {f : ℕ → Vec 2 → ℝ} {g φ : Vec 2 → ℝ}
    (hf : ∀ n, MemLp (f n) 2 (volume.restrict torusCube)) (hg : MemLp g 2 (volume.restrict torusCube))
    (hφ : MemLp φ 2 (volume.restrict torusCube))
    (h : Tendsto (fun n => eLpNorm (fun x => f n x - g x) 2 (volume.restrict torusCube)) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x in torusCube, f n x * φ x) atTop (𝓝 (∫ x in torusCube, g x * φ x)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hb : Tendsto (fun n => (eLpNorm (fun x => f n x - g x) 2 (volume.restrict torusCube)).toReal *
      (eLpNorm φ 2 (volume.restrict torusCube)).toReal) atTop (𝓝 0) := by
    have := ((ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h).mul_const
      (eLpNorm φ 2 (volume.restrict torusCube)).toReal
    simpa using this
  refine squeeze_zero (fun _ => norm_nonneg _) (fun n => ?_) hb
  have hi1 : Integrable (fun x => f n x * φ x) (volume.restrict torusCube) :=
    (hf n).integrable_mul hφ
  have hi2 : Integrable (fun x => g x * φ x) (volume.restrict torusCube) := hg.integrable_mul hφ
  have : (∫ x in torusCube, f n x * φ x) - ∫ x in torusCube, g x * φ x =
      ∫ x in torusCube, (f n x - g x) * φ x := by
    rw [← integral_sub hi1 hi2]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [sub_mul]
  rw [this, Real.norm_eq_abs]
  exact abs_integral_mul_le_eLpNorm_two ((hf n).sub hg) hφ

/-- **Weak gradient on the torus.**  If smooth periodic divergence-free `uₙ → v` in `L²(cube)` componentwise
and `∇uₙ → G` in `L²(cube)`, then `G` is the weak gradient of `v`: `∫ vᵢ ∂ⱼψ = -∫ Gᵢⱼ ψ` for all smooth
periodic test functions `ψ`. -/
theorem weak_gradient_of_tendsto {u : ℕ → Vec 2 → Vec 2} {v : Vec 2 → Vec 2}
    {G : Vec 2 → Fin 2 → Fin 2 → ℝ}
    (hu : ∀ n i, ContDiff ℝ (⊤ : ℕ∞) (fun x => u n x i)) (hup : ∀ n, IsTorusPeriodic (u n))
    (hv : ∀ i, MemLp (fun x => v x i) 2 (volume.restrict torusCube))
    (hvconv : ∀ i, Tendsto (fun n => eLpNorm (fun x => u n x i - v x i) 2
      (volume.restrict torusCube)) atTop (𝓝 0))
    (hG : MemLp G 2 (volume.restrict torusCube))
    (hGconv : Tendsto (fun n => eLpNorm (fun x => gradMat (u n) x - G x) 2
      (volume.restrict torusCube)) atTop (𝓝 0))
    (i j : Fin 2) {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψp : IsTorusPeriodic ψ) :
    ∫ x in torusCube, v x i * pd j ψ x = -∫ x in torusCube, G x i j * ψ x := by
  have hψ2 : MemLp ψ 2 (volume.restrict torusCube) := memLp_cube_of_continuous hψ.continuous 2
  have hpψ : MemLp (pd j ψ) 2 (volume.restrict torusCube) :=
    memLp_cube_of_continuous (continuous_pd_of_contDiff hψ j) 2
  have hL := tendsto_integral_mul_cube (f := fun n x => u n x i) (g := fun x => v x i) (φ := pd j ψ)
    (fun n => memLp_cube_of_continuous (hu n i).continuous 2) (hv i) hpψ (hvconv i)
  have hR := tendsto_integral_mul_cube (f := fun n x => gradMat (u n) x i j)
    (g := fun x => G x i j) (φ := ψ)
    (fun n => memLp_cube_of_continuous (continuous_gradMat_apply (hu n) i j) 2)
    (memLp_apply_of_memLp_gradMat hG i j) hψ2
    (tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hGconv (fun _ => bot_le)
      (fun n => eLpNorm_apply_le (f := gradMat (u n))
      (continuous_gradMat (hu n)).aestronglyMeasurable hG.aestronglyMeasurable i j))
  have hn : ∀ n, ∫ x in torusCube, u n x i * pd j ψ x =
      -∫ x in torusCube, gradMat (u n) x i j * ψ x := by
    intro n
    have := torus_integral_by_parts (f := fun x => u n x i) (g := ψ)
      ((hu n i).of_le (by simp)) (hψ.of_le (by simp)) ((hup n).comp (fun w => w i)) hψp j
    simp only [gradMat, pd]
    rw [this, neg_neg]
  exact tendsto_nhds_unique hL (hR.neg.congr fun n => (hn n).symm)

end PDE
