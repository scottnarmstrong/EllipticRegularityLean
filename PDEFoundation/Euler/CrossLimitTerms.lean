module

public import PDEFoundation.Euler.CrossMollified
public import PDEFoundation.Euler.MollifyL2Conv
public import PDEFoundation.Euler.TimeSlice
public import PDEFoundation.Euler.SliceLimits
public import PDEFoundation.Euler.CrossDatum

/-!
# Passing to the limit `a = tDelta k → 0` in the terms of the cross identity

`SpaceTimeGrad T B v G` records that `G` is a jointly measurable `L²(eulerMeasure)` field, the limit of
`∇ (vᵃᵏ)`, whose slices are the weak gradients of the slices of `v` (in the `GradSlice` sense).  Each of the
terms `crossF`, `crossH`, `crossK` (diagonal values) and the datum term converges as `k → ∞`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PDE

structure SpaceTimeGrad (T B : ℝ) (v : Vec 2 × ℝ → Vec 2) (G : Vec 2 × ℝ → Fin 2 → Fin 2 → ℝ) : Prop where
  aesm : ∀ i j, AEStronglyMeasurable (fun z => G z i j) (eulerMeasure T)
  memLp : ∀ i j, MemLp (fun z => G z i j) 2 (eulerMeasure T)
  conv : ∀ i j, Tendsto (fun k => eLpNorm (fun z => gradMollST (tDelta k) v z i j - G z i j) 2
    (eulerMeasure T)) atTop (𝓝 0)
  slice : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)),
    GradSlice tDelta (fun x => v (x, t)) (fun x => G (x, t)) B

theorem ae_abs_comp_snd_le {T : ℝ} {g : ℝ → ℝ} (hg : Continuous g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ z ∂(eulerMeasure T), |g z.2| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).exists_bound_of_continuousOn hg.continuousOn
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  have : ∀ᵐ z ∂(eulerMeasure T), z ∈ torusCube ×ˢ Icc (0 : ℝ) T := by
    unfold eulerMeasure
    exact ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)
  filter_upwards [this] with z hz
  have := hC z.2 hz.2
  rw [Real.norm_eq_abs] at this
  exact this.trans (le_max_left _ _)

theorem integrable_of_bdd_E {T : ℝ} {f : Vec 2 × ℝ → ℝ} (hf : AEStronglyMeasurable f (eulerMeasure T))
    {C : ℝ} (hC : ∀ᵐ z ∂(eulerMeasure T), |f z| ≤ C) : Integrable f (eulerMeasure T) :=
  integrable_of_ae_abs_le hf hC

section Terms

variable {T B1 B2 : ℝ} {u v : Vec 2 × ℝ → Vec 2}

theorem tendsto_crossF_diag (hbu : EulerBdd T B1 u) (hbv : EulerBdd T B2 v) {g : ℝ → ℝ}
    (hg : Continuous g) :
    Tendsto (fun k => ∫ τ in Icc (0 : ℝ) T, g τ * crossF (tDelta k) u v τ τ) atTop
      (𝓝 (∑ i, ∫ z, g z.2 * (u z i * v z i) ∂(eulerMeasure T))) := by
  obtain ⟨C, hC0, hC⟩ := ae_abs_comp_snd_le (T := T) hg
  have hint : ∀ k (i : Fin 2), Integrable (fun z => u z i * mollifyVecST (tDelta k) v z i) (eulerMeasure T) :=
    fun k i => integrable_of_bdd_E ((hbu.coord_aesm i).mul (hbv.mol_aesm _ i)) (C := Real.sqrt B1 * Real.sqrt B2)
      ((hbu.abs_coord_le i).and (hbv.abs_mol_le (tDelta_pos k) i) |>.mono fun z ⟨h1, h2⟩ => by
        rw [abs_mul]; exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1))
  have hk : ∀ k, ∫ τ in Icc (0 : ℝ) T, g τ * crossF (tDelta k) u v τ τ =
      ∑ i, ∫ z, g z.2 * (u z i * mollifyVecST (tDelta k) v z i) ∂(eulerMeasure T) := fun k => by
    exact time_slice_sum (Finset.univ : Finset (Fin 2))
      (h := fun i z => u z i * mollifyVecST (tDelta k) v z i) (fun i _ => hint k i) hg
  simp_rw [hk]
  refine tendsto_finsetSum _ fun i _ => ?_
  have := tendsto_integral_weight_mul_left (μ := eulerMeasure T) (β := fun z => g z.2) hC0
    (hg.comp continuous_snd).aestronglyMeasurable hC (f := fun k z => mollifyVecST (tDelta k) v z i)
    (F := fun z => v z i) (g := fun z => u z i)
    (fun k => memLp_two_of_bdd (hbv.mol_aesm _ i) (hbv.abs_mol_le (tDelta_pos k) i))
    (memLp_two_of_bdd (hbv.coord_aesm i) (hbv.abs_coord_le i))
    (memLp_two_of_bdd (hbu.coord_aesm i) (hbu.abs_coord_le i))
    (tendsto_eLpNorm_mollifyVecST hbv i)
  have e1 : ∀ k, ∫ z, g z.2 * (mollifyVecST (tDelta k) v z i * u z i) ∂(eulerMeasure T) =
      ∫ z, g z.2 * (u z i * mollifyVecST (tDelta k) v z i) ∂(eulerMeasure T) := fun k =>
    integral_congr_ae (Filter.Eventually.of_forall fun z => by simp only; ring)
  have e2 : ∫ z, g z.2 * (v z i * u z i) ∂(eulerMeasure T) =
      ∫ z, g z.2 * (u z i * v z i) ∂(eulerMeasure T) :=
    integral_congr_ae (Filter.Eventually.of_forall fun z => by simp only; ring)
  have h3 := this.congr e1
  rw [e2] at h3
  exact h3

theorem tendsto_crossH_diag (hbu : EulerBdd T B1 u) (hbv : EulerBdd T B2 v) {G : Vec 2 × ℝ → Fin 2 → Fin 2 → ℝ}
    (hG : SpaceTimeGrad T B2 v G) {g : ℝ → ℝ} (hg : Continuous g) :
    Tendsto (fun k => ∫ τ in Icc (0 : ℝ) T, g τ * crossH (tDelta k) u v τ τ) atTop
      (𝓝 (∑ i, ∑ j, ∫ z, g z.2 * ((u z i * u z j) * G z i j) ∂(eulerMeasure T))) := by
  obtain ⟨C, hC0, hC⟩ := ae_abs_comp_snd_le (T := T) hg
  have hint : ∀ k (p : Fin 2 × Fin 2), Integrable
      (fun z => (u z p.1 * u z p.2) * gradMollST (tDelta k) v z p.1 p.2) (eulerMeasure T) := fun k p =>
    integrable_of_bdd_E ((hbu.prod_aesm p.1 p.2).mul (hbv.grad_aesm (tDelta_pos k) p.1 p.2))
      (C := B1 * (pdMolKNorm (tDelta k) p.2 * Real.sqrt B2))
      ((hbu.abs_prod_le p.1 p.2).and (hbv.abs_grad_le (tDelta_pos k) p.1 p.2) |>.mono fun z ⟨h1, h2⟩ => by
        rw [abs_mul]; exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1))
  have hk : ∀ k, ∫ τ in Icc (0 : ℝ) T, g τ * crossH (tDelta k) u v τ τ =
      ∑ p : Fin 2 × Fin 2, ∫ z, g z.2 * ((u z p.1 * u z p.2) * gradMollST (tDelta k) v z p.1 p.2)
        ∂(eulerMeasure T) := fun k => by
    simp only [crossH_eq_sum]
    exact time_slice_sum (Finset.univ : Finset (Fin 2 × Fin 2))
      (h := fun p z => (u z p.1 * u z p.2) * gradMollST (tDelta k) v z p.1 p.2) (fun p _ => hint k p) hg
  simp_rw [hk, Fintype.sum_prod_type]
  refine tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_
  have hmem : MemLp (fun z => u z i * u z j) 2 (eulerMeasure T) :=
    memLp_two_of_bdd (hbu.prod_aesm i j) (hbu.abs_prod_le i j)
  have := tendsto_integral_weight_mul_left (μ := eulerMeasure T) (β := fun z => g z.2) hC0
    (hg.comp continuous_snd).aestronglyMeasurable hC
    (f := fun k z => gradMollST (tDelta k) v z i j) (F := fun z => G z i j) (g := fun z => u z i * u z j)
    (fun k => memLp_two_of_bdd (hbv.grad_aesm (tDelta_pos k) i j) (hbv.abs_grad_le (tDelta_pos k) i j))
    (hG.memLp i j) hmem (hG.conv i j)
  have e1 : ∀ k, ∫ z, g z.2 * (gradMollST (tDelta k) v z i j * (u z i * u z j)) ∂(eulerMeasure T) =
      ∫ z, g z.2 * ((u z i * u z j) * gradMollST (tDelta k) v z i j) ∂(eulerMeasure T) := fun k =>
    integral_congr_ae (Filter.Eventually.of_forall fun z => by simp only; ring)
  have e2 : ∫ z, g z.2 * (G z i j * (u z i * u z j)) ∂(eulerMeasure T) =
      ∫ z, g z.2 * ((u z i * u z j) * G z i j) ∂(eulerMeasure T) :=
    integral_congr_ae (Filter.Eventually.of_forall fun z => by simp only; ring)
  have h3 := this.congr e1
  rw [e2] at h3
  exact h3

theorem memLp_coord_mul {T B2 : ℝ} {v : Vec 2 × ℝ → Vec 2} (hbv : EulerBdd T B2 v)
    {G : Vec 2 × ℝ → Fin 2 → Fin 2 → ℝ} (hG : SpaceTimeGrad T B2 v G) (i j : Fin 2) :
    MemLp (fun z => v z j * G z i j) 2 (eulerMeasure T) :=
  (hG.memLp i j).of_le_mul (c := Real.sqrt B2) ((hbv.coord_aesm j).mul (hG.aesm i j))
    ((hbv.abs_coord_le j).mono fun z hz => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right hz (abs_nonneg _))

theorem tendsto_crossK_diag (hT : 0 < T) (hbu : EulerBdd T B1 u) (hbv : EulerBdd T B2 v)
    (hdivu : ∀ ψ : Vec 2 × ℝ → ℝ, IsPeriodicSmooth ψ → VanishesOutsideInterior T ψ →
      ∫ z, vecDot (u z) (fun j => fderiv ℝ ψ z (basisVec j, 0)) ∂(eulerMeasure T) = 0)
    {G : Vec 2 × ℝ → Fin 2 → Fin 2 → ℝ} (hG : SpaceTimeGrad T B2 v G) {g : ℝ → ℝ} (hg : Continuous g) :
    Tendsto (fun k => ∫ τ in Icc (0 : ℝ) T, g τ * crossK (tDelta k) u v τ τ) atTop
      (𝓝 (-(∑ i, ∑ j, ∫ z, g z.2 * (u z i * (v z j * G z i j)) ∂(eulerMeasure T)))) := by
  obtain ⟨C, hC0, hC⟩ := ae_abs_comp_snd_le (T := T) hg
  have Hdiv := ae_mollify_slice_div hT hbu.meas hbu.per hbu.bdd hdivu
  have hint : ∀ k (p : Fin 2 × Fin 2), Integrable
      (fun z => mollifyVecST (tDelta k) u z p.1 * (v z p.2 * G z p.1 p.2)) (eulerMeasure T) := fun k p =>
    ((memLp_coord_mul hbv hG p.1 p.2).integrable (by norm_num)).bdd_mul (hbu.mol_aesm _ p.1)
      ((hbu.abs_mol_le (tDelta_pos k) p.1).mono fun z hz => by simpa [Real.norm_eq_abs] using hz)
  have hpt : ∀ k, ∀ᵐ τ ∂(volume.restrict (Icc (0 : ℝ) T)), crossK (tDelta k) u v τ τ =
      -(∑ p : Fin 2 × Fin 2, ∫ x in torusCube,
        mollifyVecST (tDelta k) u (x, τ) p.1 * (v (x, τ) p.2 * G (x, τ) p.1 p.2)) := by
    intro k
    filter_upwards [hG.slice, Hdiv] with τ hs hd
    obtain ⟨hsm, hper, -, -⟩ := hd (tDelta k) (tDelta_pos k)
    have := slice_quad_identity hs (θ := fun y => mollifyVecST (tDelta k) u (y, τ)) hsm hper
    simp only [Fintype.sum_prod_type]
    exact this
  have hk : ∀ k, ∫ τ in Icc (0 : ℝ) T, g τ * crossK (tDelta k) u v τ τ =
      -(∑ p : Fin 2 × Fin 2, ∫ z, g z.2 * (mollifyVecST (tDelta k) u z p.1 * (v z p.2 * G z p.1 p.2))
        ∂(eulerMeasure T)) := fun k => by
    rw [← time_slice_sum (Finset.univ : Finset (Fin 2 × Fin 2))
      (h := fun p z => mollifyVecST (tDelta k) u z p.1 * (v z p.2 * G z p.1 p.2)) (fun p _ => hint k p) hg,
      ← integral_neg]
    refine integral_congr_ae ?_
    filter_upwards [hpt k] with τ hτ
    rw [hτ, mul_neg]
  simp_rw [hk, Fintype.sum_prod_type]
  refine (tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun j _ => ?_).neg
  have := tendsto_integral_weight_mul_left (μ := eulerMeasure T) (β := fun z => g z.2) hC0
    (hg.comp continuous_snd).aestronglyMeasurable hC
    (f := fun k z => mollifyVecST (tDelta k) u z i) (F := fun z => u z i)
    (g := fun z => v z j * G z i j)
    (fun k => memLp_two_of_bdd (hbu.mol_aesm _ i) (hbu.abs_mol_le (tDelta_pos k) i))
    (memLp_two_of_bdd (hbu.coord_aesm i) (hbu.abs_coord_le i)) (memLp_coord_mul hbv hG i j)
    (tendsto_eLpNorm_mollifyVecST hbu i)
  exact this

end Terms

theorem tendsto_datum_term {v₀ : Vec 2 → Vec 2} (hv₀ : MemLp v₀ 2 (volume.restrict torusCube)) :
    Tendsto (fun k => ∑ i, ∫ x in torusCube, v₀ x i * mollifyVec (tDelta k) (periodExt v₀) x i) atTop
      (𝓝 (∑ i, ∫ x in torusCube, v₀ x i * v₀ x i)) := by
  refine tendsto_finsetSum _ fun i _ => ?_
  have hpe : MemLp (fun x => periodExt v₀ x i) 2 (volume.restrict torusCube) :=
    (hv₀.eval i).ae_eq ((ae_periodExt_eq v₀).mono fun x hx => by show v₀ x i = periodExt v₀ x i; rw [hx])
  have hconv := tendsto_eLpNorm_mollify_cube ((isTorusPeriodic_periodExt v₀).comp (fun r => r i)) hpe
    tDelta_pos tDelta_le_one tendsto_tDelta
  have hconv' : Tendsto (fun k => eLpNorm ((fun x => mollifyVec (tDelta k) (periodExt v₀) x i) -
      fun x => v₀ x i) 2 (volume.restrict torusCube)) atTop (𝓝 0) := by
    refine hconv.congr (fun k => eLpNorm_congr_ae ?_)
    filter_upwards [ae_periodExt_eq v₀] with x hx
    simp only [Pi.sub_apply, hx, mollifyVec_apply]
  have := tendsto_integral_weight_mul_left (μ := volume.restrict torusCube) (β := fun _ => (1 : ℝ))
    (C := 1) zero_le_one aestronglyMeasurable_const
    (Filter.Eventually.of_forall fun x => by simp)
    (f := fun k x => mollifyVec (tDelta k) (periodExt v₀) x i) (F := fun x => v₀ x i)
    (g := fun x => v₀ x i)
    (fun k => memLp_cube_of_continuous
      (mollify_contDiff (tDelta_pos k) (datum_periodExt_locInt hv₀ i)).continuous 2)
    (hv₀.eval i) (hv₀.eval i) hconv'
  have e1 : ∀ k, ∫ x in torusCube, (1 : ℝ) * (mollifyVec (tDelta k) (periodExt v₀) x i * v₀ x i) =
      ∫ x in torusCube, v₀ x i * mollifyVec (tDelta k) (periodExt v₀) x i := fun k =>
    integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only; ring)
  have e2 : ∫ x in torusCube, (1 : ℝ) * (v₀ x i * v₀ x i) = ∫ x in torusCube, v₀ x i * v₀ x i :=
    integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only; ring)
  have h3 := this.congr e1
  rw [e2] at h3
  exact h3

end PDE
