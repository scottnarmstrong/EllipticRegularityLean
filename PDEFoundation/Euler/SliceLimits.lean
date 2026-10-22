module

public import PDEFoundation.Euler.SliceProduct
public import PDEFoundation.Euler.L2Prod
public import PDEFoundation.Euler.MollifyBundle
public import PDEFoundation.Euler.WeakGradLimit

/-!
# Slice identities for a field with `L²` weak gradient

`GradSlice a w G B` packages the slice data produced by the weak-gradient construction for a time slice `w = v(·,t)`:
the mollifications `w^{aₖ}` are smooth periodic divergence free and `∂ⱼ w^{aₖ}ᵢ → Gᵢⱼ` in `L²(cube)`.  Passing to the
limit in the smooth identities of `SliceProduct` gives
* `slice_quad_identity`: `∑ᵢⱼ ∫ wᵢwⱼ ∂ⱼθᵢ = - ∑ᵢⱼ ∫ θᵢ wⱼ Gᵢⱼ` for smooth periodic `θ` (the product rule `div(w⊗w) = w·∇w`),
* `slice_energy_identity`: `∑ᵢⱼ ∫ w̃ⱼ wᵢ Gᵢⱼ = 0` for weakly divergence-free bounded `w̃` (`w̃·∇|w|²/2` integrates to zero).
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PDE

structure GradSlice (a : ℕ → ℝ) (w : Vec 2 → Vec 2) (G : Vec 2 → Fin 2 → Fin 2 → ℝ) (B : ℝ) : Prop where
  pos : ∀ k, 0 < a k
  le_one : ∀ k, a k ≤ 1
  tends : Tendsto a atTop (𝓝 0)
  per : IsTorusPeriodic w
  meas : ∀ i, AEStronglyMeasurable (fun x => w x i) (volume.restrict torusCube)
  bdd : ∀ᵐ x ∂(volume.restrict torusCube), vecNormSq (w x) ≤ B
  smooth : ∀ k i, ContDiff ℝ (⊤ : ℕ∞) (fun x => mollifyVec (a k) w x i)
  mper : ∀ k, IsTorusPeriodic (mollifyVec (a k) w)
  mdiv : ∀ k x, torusDiv (mollifyVec (a k) w) x = 0
  Gl2 : ∀ i j, MemLp (fun x => G x i j) 2 (volume.restrict torusCube)
  grad_conv : ∀ i j, Tendsto (fun k => eLpNorm (fun x => gradMat (mollifyVec (a k) w) x i j - G x i j) 2
    (volume.restrict torusCube)) atTop (𝓝 0)

namespace GradSlice

variable {a : ℕ → ℝ} {w : Vec 2 → Vec 2} {G : Vec 2 → Fin 2 → Fin 2 → ℝ} {B : ℝ}

theorem wL2 (h : GradSlice a w G B) (i : Fin 2) :
    MemLp (fun x => w x i) 2 (volume.restrict torusCube) :=
  MemLp.of_bound (h.meas i) (Real.sqrt B)
    (h.bdd.mono fun x hx => by simpa [Real.norm_eq_abs] using abs_coord_le_sqrt hx i)

theorem mol_conv (h : GradSlice a w G B) (i : Fin 2) :
    Tendsto (fun k => eLpNorm (fun x => mollifyVec (a k) w x i - w x i) 2
      (volume.restrict torusCube)) atTop (𝓝 0) :=
  tendsto_eLpNorm_mollify_cube (h.per.comp (fun r => r i)) (h.wL2 i) h.pos h.le_one h.tends

theorem mol_memLp (h : GradSlice a w G B) (k : ℕ) (i : Fin 2) :
    MemLp (fun x => mollifyVec (a k) w x i) 2 (volume.restrict torusCube) :=
  memLp_cube_of_continuous (h.smooth k i).continuous 2

theorem grad_memLp (h : GradSlice a w G B) (k : ℕ) (i j : Fin 2) :
    MemLp (fun x => gradMat (mollifyVec (a k) w) x i j) 2 (volume.restrict torusCube) :=
  memLp_cube_of_continuous (continuous_gradMat_apply (h.smooth k) i j) 2

end GradSlice

theorem exists_bound_cube {f : Vec 2 → ℝ} (hf : Continuous f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ torusCube, |f x| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact torusCube).exists_bound_of_continuousOn hf.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
  have := hC x hx
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

theorem ae_abs_le_cube {f : Vec 2 → ℝ} {C : ℝ} (h : ∀ x ∈ torusCube, |f x| ≤ C) :
    ∀ᵐ x ∂(volume.restrict torusCube), |f x| ≤ C :=
  (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall h)

/-- Limit step for a bounded measurable weight `β` and mollified factors. -/
theorem tendsto_slice_term {a : ℕ → ℝ} {w : Vec 2 → Vec 2} {G : Vec 2 → Fin 2 → Fin 2 → ℝ} {B : ℝ}
    (h : GradSlice a w G B) {β : Vec 2 → ℝ} {C : ℝ} (hC0 : 0 ≤ C)
    (hβ : AEStronglyMeasurable β (volume.restrict torusCube))
    (hC : ∀ᵐ x ∂(volume.restrict torusCube), |β x| ≤ C) (i j k' : Fin 2) :
    Tendsto (fun k => ∫ x in torusCube, β x * (mollifyVec (a k) w x i *
        gradMat (mollifyVec (a k) w) x k' j)) atTop
      (𝓝 (∫ x in torusCube, β x * (w x i * G x k' j))) :=
  tendsto_integral_weight_mul_of_L2 (f := fun k x => mollifyVec (a k) w x i)
    (g := fun k x => gradMat (mollifyVec (a k) w) x k' j) hC0 hβ hC
    (h.mol_memLp · i) (h.wL2 i) (fun k => h.grad_memLp k k' j) (h.Gl2 k' j) (h.mol_conv i)
    (h.grad_conv k' j)

/-- **Product rule on a slice**: `div (w ⊗ w) = w·∇w` tested against a smooth periodic field. -/
theorem slice_quad_identity {a : ℕ → ℝ} {w : Vec 2 → Vec 2} {G : Vec 2 → Fin 2 → Fin 2 → ℝ} {B : ℝ}
    (h : GradSlice a w G B) {θ : Vec 2 → Vec 2} (hθ : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => θ x i))
    (hθp : IsTorusPeriodic θ) :
    (∑ i, ∑ j, ∫ x in torusCube, (w x i * w x j) * gradMat θ x i j) =
      -(∑ i, ∑ j, ∫ x in torusCube, θ x i * (w x j * G x i j)) := by
  have hk : ∀ k, (∑ i, ∑ j, ∫ x in torusCube, (mollifyVec (a k) w x i * mollifyVec (a k) w x j) *
      gradMat θ x i j) = -(∑ i, ∑ j, ∫ x in torusCube, θ x i * (mollifyVec (a k) w x j *
        gradMat (mollifyVec (a k) w) x i j)) := fun k =>
    torus_quad_identity (h.smooth k) (h.mper k) (h.mdiv k) hθ hθp
  have hL : Tendsto (fun k => ∑ i, ∑ j, ∫ x in torusCube, (mollifyVec (a k) w x i *
      mollifyVec (a k) w x j) * gradMat θ x i j) atTop
      (𝓝 (∑ i, ∑ j, ∫ x in torusCube, (w x i * w x j) * gradMat θ x i j)) := by
    refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
    have hc := continuous_gradMat_apply hθ i j
    obtain ⟨C, hC0, hC⟩ := exists_bound_cube hc
    have := tendsto_integral_weight_mul_of_L2 (f := fun k x => mollifyVec (a k) w x i)
      (g := fun k x => mollifyVec (a k) w x j) hC0 hc.aestronglyMeasurable (ae_abs_le_cube hC)
      (h.mol_memLp · i) (h.wL2 i) (h.mol_memLp · j) (h.wL2 j) (h.mol_conv i) (h.mol_conv j)
    have e : ∫ x in torusCube, (w x i * w x j) * gradMat θ x i j =
        ∫ x in torusCube, gradMat θ x i j * (w x i * w x j) :=
      integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only; ring)
    rw [e]
    refine this.congr (fun k => integral_congr_ae (Filter.Eventually.of_forall fun x => ?_))
    simp only
    ring
  have hR : Tendsto (fun k => ∑ i, ∑ j, ∫ x in torusCube, θ x i * (mollifyVec (a k) w x j *
      gradMat (mollifyVec (a k) w) x i j)) atTop
      (𝓝 (∑ i, ∑ j, ∫ x in torusCube, θ x i * (w x j * G x i j))) := by
    refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
    have hc := (hθ i).continuous
    obtain ⟨C, hC0, hC⟩ := exists_bound_cube hc
    exact tendsto_slice_term h hC0 hc.aestronglyMeasurable (ae_abs_le_cube hC) j j i
  have hR' := hR.neg
  rw [show (fun k => -(∑ i, ∑ j, ∫ x in torusCube, θ x i * (mollifyVec (a k) w x j *
      gradMat (mollifyVec (a k) w) x i j))) = fun k => ∑ i, ∑ j, ∫ x in torusCube,
        (mollifyVec (a k) w x i * mollifyVec (a k) w x j) * gradMat θ x i j from funext fun k => (hk k).symm]
    at hR'
  exact tendsto_nhds_unique hL hR'

/-- **Energy identity on a slice**: `∫ w̃ · ∇ (|w|²/2) = 0` for weakly divergence-free bounded `w̃`. -/
theorem slice_energy_identity {a : ℕ → ℝ} {w : Vec 2 → Vec 2} {G : Vec 2 → Fin 2 → Fin 2 → ℝ} {B : ℝ}
    (h : GradSlice a w G B) {w' : Vec 2 → Vec 2} {C : ℝ} (hC0 : 0 ≤ C)
    (hw' : ∀ i, AEStronglyMeasurable (fun x => w' x i) (volume.restrict torusCube))
    (hC : ∀ᵐ x ∂(volume.restrict torusCube), ∀ i, |w' x i| ≤ C)
    (hdiv : ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → IsTorusPeriodic ψ →
      ∫ x in torusCube, vecDot (w' x) (fun j => pd j ψ x) = 0) :
    (∑ i, ∑ j, ∫ x in torusCube, w' x j * (w x i * G x i j)) = 0 := by
  have hk : ∀ k, (∑ i, ∑ j, ∫ x in torusCube, w' x j * (mollifyVec (a k) w x i *
      gradMat (mollifyVec (a k) w) x i j)) = 0 := fun k =>
    smooth_energy_identity (h.smooth k) (h.mper k) hw' hC hdiv
  have hL : Tendsto (fun k => ∑ i, ∑ j, ∫ x in torusCube, w' x j * (mollifyVec (a k) w x i *
      gradMat (mollifyVec (a k) w) x i j)) atTop
      (𝓝 (∑ i, ∑ j, ∫ x in torusCube, w' x j * (w x i * G x i j))) := by
    refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
    exact tendsto_slice_term h hC0 (hw' j) (hC.mono fun x hx => hx j) i j i
  simp only [hk] at hL
  exact tendsto_nhds_unique hL tendsto_const_nhds

end PDE
