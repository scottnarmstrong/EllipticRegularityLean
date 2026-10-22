module

public import EllipticRegularity.Euler.SpaceTimeGradient
public import PDEFoundation.Euler.CrossTime

/-!
# Slice algebra for the relative energy inequality

For a.e. `s`, `sliceR v₁ v₂ G s` (with `w = v₁ - v₂`) equals `Λ(s) = ∑ᵢⱼ ∫_cube wⱼ wᵢ Gᵢⱼ`: the remaining term
`∑ᵢⱼ ∫ wⱼ (v₂)ᵢ Gᵢⱼ` is `∫ w·∇(|v₂|²/2) = 0` by `slice_energy_identity` (`w` weakly divergence free).
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PDE

/-- `Λ(s) = ∫_cube ∑ᵢⱼ wⱼ wᵢ Gᵢⱼ`, with `w = v₁ - v₂`. -/
noncomputable def relLam (v₁ v₂ : Vec 2 × ℝ → Vec 2) (G : Vec 2 × ℝ → Fin 2 → Fin 2 → ℝ) (s : ℝ) : ℝ :=
  ∑ i, ∑ j, ∫ x in torusCube, (v₁ (x, s) j - v₂ (x, s) j) * (v₁ (x, s) i - v₂ (x, s) i) * G (x, s) i j

theorem integrable_mul_L2_cube {f g : Vec 2 → ℝ} {C : ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict torusCube)) (hC : ∀ᵐ x ∂(volume.restrict torusCube), |f x| ≤ C)
    (hg : MemLp g 2 (volume.restrict torusCube)) :
    Integrable (fun x => f x * g x) (volume.restrict torusCube) :=
  (hg.integrable (by norm_num)).bdd_mul hf (hC.mono fun x hx => by simpa [Real.norm_eq_abs] using hx)

theorem slice_sliceR_eq {B1 B2 : ℝ} {v₁ v₂ : Vec 2 × ℝ → Vec 2} {G : Vec 2 × ℝ → Fin 2 → Fin 2 → ℝ}
    {s : ℝ} (hs : GradSlice tDelta (fun x => v₂ (x, s)) (fun x => G (x, s)) B2)
    (hm1 : ∀ i, AEStronglyMeasurable (fun x => v₁ (x, s) i) (volume.restrict torusCube))
    (hb1 : ∀ᵐ x ∂(volume.restrict torusCube), vecNormSq (v₁ (x, s)) ≤ B1)
    (hd1 : ∀ φ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → IsTorusPeriodic φ →
      ∫ x in torusCube, vecDot (v₁ (x, s)) (fun j => pd j φ x) = 0)
    (hd2 : ∀ φ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → IsTorusPeriodic φ →
      ∫ x in torusCube, vecDot (v₂ (x, s)) (fun j => pd j φ x) = 0) :
    sliceR v₁ v₂ G s = relLam v₁ v₂ G s := by
  set μc : Measure (Vec 2) := volume.restrict torusCube with hμc
  have hm2 : ∀ i, AEStronglyMeasurable (fun x => v₂ (x, s) i) μc := hs.meas
  have hb2 : ∀ᵐ x ∂μc, vecNormSq (v₂ (x, s)) ≤ B2 := hs.bdd
  have hC1 : ∀ i, ∀ᵐ x ∂μc, |v₁ (x, s) i| ≤ Real.sqrt B1 := fun i =>
    hb1.mono fun x hx => abs_coord_le_sqrt hx i
  have hC2 : ∀ i, ∀ᵐ x ∂μc, |v₂ (x, s) i| ≤ Real.sqrt B2 := fun i =>
    hb2.mono fun x hx => abs_coord_le_sqrt hx i
  have hwm : ∀ i, AEStronglyMeasurable (fun x => v₁ (x, s) i - v₂ (x, s) i) μc := fun i => (hm1 i).sub (hm2 i)
  have hwC : ∀ i, ∀ᵐ x ∂μc, |v₁ (x, s) i - v₂ (x, s) i| ≤ Real.sqrt B1 + Real.sqrt B2 := fun i => by
    filter_upwards [hC1 i, hC2 i] with x h1 h2
    exact (abs_sub _ _).trans (add_le_add h1 h2)
  have hG := hs.Gl2
  -- integrability of the two pieces
  have i1 : ∀ i j, Integrable (fun x => ((v₁ (x, s) j - v₂ (x, s) j) * (v₁ (x, s) i - v₂ (x, s) i)) *
      G (x, s) i j) μc := by
    intro i j
    refine integrable_mul_L2_cube (C := (Real.sqrt B1 + Real.sqrt B2) * (Real.sqrt B1 + Real.sqrt B2))
      ((hwm j).mul (hwm i)) ?_ (hG i j)
    filter_upwards [hwC i, hwC j] with x h1 h2
    rw [abs_mul]
    exact mul_le_mul h2 h1 (abs_nonneg _) ((abs_nonneg _).trans h2)
  have i2 : ∀ i j, Integrable (fun x => (v₁ (x, s) j - v₂ (x, s) j) * (v₂ (x, s) i * G (x, s) i j)) μc := by
    intro i j
    have hg2 : MemLp (fun x => v₂ (x, s) i * G (x, s) i j) 2 μc :=
      (hG i j).of_le_mul (c := Real.sqrt B2) ((hm2 i).mul (hG i j).aestronglyMeasurable)
        ((hC2 i).mono fun x hx => by
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right hx (abs_nonneg _))
    exact integrable_mul_L2_cube (C := Real.sqrt B1 + Real.sqrt B2) (hwm j) (hwC j) hg2
  have hsplit : ∀ i j, ∫ x in torusCube, ((v₁ (x, s) j - v₂ (x, s) j) * v₁ (x, s) i) * G (x, s) i j =
      (∫ x in torusCube, (v₁ (x, s) j - v₂ (x, s) j) * (v₁ (x, s) i - v₂ (x, s) i) * G (x, s) i j) +
        ∫ x in torusCube, (v₁ (x, s) j - v₂ (x, s) j) * (v₂ (x, s) i * G (x, s) i j) := by
    intro i j
    rw [← integral_add (i1 i j) (i2 i j)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    ring
  have hdiv : ∀ φ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → IsTorusPeriodic φ →
      ∫ x in torusCube, vecDot ((fun x => v₁ (x, s) - v₂ (x, s)) x) (fun j => pd j φ x) = 0 := by
    intro φ hφ hφp
    have hc : ∀ j, Continuous fun x => pd j φ x := fun j => continuous_pd_of_contDiff hφ j
    have hi : ∀ (w : Vec 2 → Vec 2) (C : ℝ), (∀ i, AEStronglyMeasurable (fun x => w x i) μc) →
        (∀ i, ∀ᵐ x ∂μc, |w x i| ≤ C) →
        Integrable (fun x => vecDot (w x) (fun j => pd j φ x)) μc := by
      intro w C hw hC
      have : ∀ j, Integrable (fun x => w x j * pd j φ x) μc := by
        intro j
        obtain ⟨K, hK0, hK⟩ := exists_bound_cube (hc j)
        refine Integrable.of_bound ((hw j).mul (hc j).aestronglyMeasurable) (C * K) ?_
        filter_upwards [hC j, ae_abs_le_cube hK] with x h1 h2
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul h1 h2 (abs_nonneg _) ((abs_nonneg _).trans h1)
      have hsum : Integrable (fun x => w x 0 * pd 0 φ x + w x 1 * pd 1 φ x) μc := (this 0).add (this 1)
      simp only [vecDot, Fin.sum_univ_two]
      exact hsum
    have h1 := hi (fun x => v₁ (x, s)) (Real.sqrt B1) hm1 hC1
    have h2 := hi (fun x => v₂ (x, s)) (Real.sqrt B2) hm2 hC2
    have e : ∀ x, vecDot ((fun x => v₁ (x, s) - v₂ (x, s)) x) (fun j => pd j φ x) =
        vecDot (v₁ (x, s)) (fun j => pd j φ x) - vecDot (v₂ (x, s)) (fun j => pd j φ x) := by
      intro x
      simp only [vecDot, Fin.sum_univ_two, Pi.sub_apply]
      ring
    simp only [e]
    rw [integral_sub h1 h2, hd1 φ hφ hφp, hd2 φ hφ hφp, sub_zero]
  have hE := slice_energy_identity hs (w' := fun x => v₁ (x, s) - v₂ (x, s))
    (C := Real.sqrt B1 + Real.sqrt B2) (by positivity) hwm (Filter.Eventually.mono
      ((hwC 0).and (hwC 1)) fun x ⟨h0, h1⟩ i => by fin_cases i <;> simpa using ‹_›) hdiv
  unfold sliceR relLam
  simp only [hsplit, Finset.sum_add_distrib]
  rw [show (∑ i, ∑ j, ∫ x in torusCube, (v₁ (x, s) j - v₂ (x, s) j) * (v₂ (x, s) i * G (x, s) i j)) = 0 from hE,
    add_zero]

theorem slice_relLam_eq {B1 B2 : ℝ} {v₁ v₂ : Vec 2 × ℝ → Vec 2} {G : Vec 2 × ℝ → Fin 2 → Fin 2 → ℝ}
    {s : ℝ} (hs : GradSlice tDelta (fun x => v₂ (x, s)) (fun x => G (x, s)) B2)
    (hm1 : ∀ i, AEStronglyMeasurable (fun x => v₁ (x, s) i) (volume.restrict torusCube))
    (hb1 : ∀ᵐ x ∂(volume.restrict torusCube), vecNormSq (v₁ (x, s)) ≤ B1) :
    relLam v₁ v₂ G s = ∫ x in torusCube, ∑ i, ∑ j,
      (v₁ (x, s) - v₂ (x, s)) j * (v₁ (x, s) - v₂ (x, s)) i * G (x, s) i j := by
  set μc : Measure (Vec 2) := volume.restrict torusCube with hμc
  have hm2 : ∀ i, AEStronglyMeasurable (fun x => v₂ (x, s) i) μc := hs.meas
  have hb2 : ∀ᵐ x ∂μc, vecNormSq (v₂ (x, s)) ≤ B2 := hs.bdd
  have hC1 : ∀ i, ∀ᵐ x ∂μc, |v₁ (x, s) i| ≤ Real.sqrt B1 := fun i =>
    hb1.mono fun x hx => abs_coord_le_sqrt hx i
  have hC2 : ∀ i, ∀ᵐ x ∂μc, |v₂ (x, s) i| ≤ Real.sqrt B2 := fun i =>
    hb2.mono fun x hx => abs_coord_le_sqrt hx i
  have hwm : ∀ i, AEStronglyMeasurable (fun x => v₁ (x, s) i - v₂ (x, s) i) μc := fun i => (hm1 i).sub (hm2 i)
  have hwC : ∀ i, ∀ᵐ x ∂μc, |v₁ (x, s) i - v₂ (x, s) i| ≤ Real.sqrt B1 + Real.sqrt B2 := fun i => by
    filter_upwards [hC1 i, hC2 i] with x h1 h2
    exact (abs_sub _ _).trans (add_le_add h1 h2)
  have i1 : ∀ i j, Integrable (fun x => ((v₁ (x, s) j - v₂ (x, s) j) * (v₁ (x, s) i - v₂ (x, s) i)) *
      G (x, s) i j) μc := by
    intro i j
    refine integrable_mul_L2_cube (C := (Real.sqrt B1 + Real.sqrt B2) * (Real.sqrt B1 + Real.sqrt B2))
      ((hwm j).mul (hwm i)) ?_ (hs.Gl2 i j)
    filter_upwards [hwC i, hwC j] with x h1 h2
    rw [abs_mul]
    exact mul_le_mul h2 h1 (abs_nonneg _) ((abs_nonneg _).trans h2)
  unfold relLam
  simp only [Pi.sub_apply]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ => i1 i j)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ (fun j _ => i1 i j)]

end PDE
