module

public import PDEFoundation.Regularity.VectorCampanatoGlobal
public import PDEFoundation.Regularity.FieldLpInfinity
public import PDEFoundation.Regularity.FieldHolderSeminorm

/-! # Gradient estimates from actual bounds at all centers and radii -/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

noncomputable section

variable {d : ℕ}

/-- Convert uniform mean and weighted oscillation bounds to an actual bounded
Hölder representative. The mean bounds are explicit premises of this internal
conversion lemma; the PDE application must prove them. -/
theorem exists_gradientEstimateFromMeans_constant (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ {α r₀ A : ℝ},
      0 < α → α < 1 → 0 < r₀ → r₀ ≤ 1 / 4 → 0 ≤ A →
      ∀ {g : Vec d → Vec d}, MemVectorL2On (euclideanBall (0 : Vec d) 1) g →
      (∀ z ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ,
        0 < r → r ≤ r₀ →
        Real.sqrt (integralAverage (euclideanBall z r) (fun x => vecNormSq (g x))) ≤ A / α ∧
        (r₀ / r) ^ α * centeredVectorMeanL2 (euclideanBall z r) g ≤ A / α) →
      ∃ G : Vec d → Vec d,
      ∃ hG : ∃ K : ℝ, 0 ≤ K ∧
        EuclideanFieldHolderSeminormLE (euclideanBall (0 : Vec d) (1 / 2)) G α K,
      ∃ hgTop : MemLp (fun x => vecEuclideanNorm (g x)) ∞
        (volumeOn (euclideanBall (0 : Vec d) (1 / 2))),
      G =ᵐ[volumeOn (euclideanBall (0 : Vec d) (1 / 2))] g ∧
      euclideanFieldLpNormOn (euclideanBall (0 : Vec d) (1 / 2)) ∞ g hgTop +
        r₀ ^ α * euclideanFieldHolderSeminormOn
          (euclideanBall (0 : Vec d) (1 / 2)) G α hG ≤ (C / α ^ 2) * A := by
  obtain ⟨Cc, hCc, hcamp⟩ := exists_vectorCampanatoGlobalCoefficient hd
  refine ⟨3 * Cc, mul_pos (by norm_num) hCc, ?_⟩
  intro α r₀ A hα0 hα1 hr₀ hr₀le hA g hg hmeans
  let B := A / α
  let K := B / r₀ ^ α
  have hB : 0 ≤ B := div_nonneg hA hα0.le
  have hp : 0 < r₀ ^ α := Real.rpow_pos_of_pos hr₀ _
  have hK : 0 ≤ K := div_nonneg hB hp.le
  have hscale : ∀ z ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ,
      0 < r → r ≤ r₀ → centeredVectorMeanL2 (euclideanBall z r) g ≤ K * r ^ α := by
    intro z hz r hr hrr₀
    have hbound := (hmeans z hz r hr hrr₀).2
    have hrp : 0 < r ^ α := Real.rpow_pos_of_pos hr _
    rw [Real.div_rpow hr₀.le hr.le] at hbound
    apply (mul_le_mul_iff_right₀ hp).mp
    have hmul := (div_le_iff₀ hrp).1 (show
      r₀ ^ α * centeredVectorMeanL2 (euclideanBall z r) g / r ^ α ≤ B by
        simpa only [B, div_mul_eq_mul_div] using hbound)
    calc
      r₀ ^ α * centeredVectorMeanL2 (euclideanBall z r) g ≤ B * r ^ α := by
        simpa only [mul_comm] using hmul
      _ = r₀ ^ α * (K * r ^ α) := by dsimp only [K]; field_simp
  have henergy : ∀ z ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ,
      0 < r → r ≤ r₀ →
      Real.sqrt (integralAverage (euclideanBall z r) (fun x => vecNormSq (g x))) ≤ B := by
    intro z hz r hr hrr₀
    exact (hmeans z hz r hr hrr₀).1
  obtain ⟨G, _hcanonical, hGae, hpoint, hholder⟩ :=
    hcamp hr₀ hr₀le hα0 hα1 hK hB hg hscale henergy
  let L := (Cc / α) * (K + B / r₀ ^ α)
  have hL : 0 ≤ L := mul_nonneg (div_nonneg hCc.le hα0.le)
    (add_nonneg hK (div_nonneg hB hp.le))
  have hG : ∃ K' : ℝ, 0 ≤ K' ∧
      EuclideanFieldHolderSeminormLE (euclideanBall (0 : Vec d) (1 / 2)) G α K' :=
    ⟨L, hL, hholder⟩
  have hhalf : euclideanBall (0 : Vec d) (1 / 2) ⊆ euclideanBall (0 : Vec d) 1 :=
    euclideanBall_mono (by norm_num) (by norm_num)
  have hgHalf : MemVectorL2On (euclideanBall (0 : Vec d) (1 / 2)) g := fun i =>
    (hg i).mono_measure (Measure.restrict_mono hhalf le_rfl)
  obtain ⟨hgTop, hnorm⟩ := exists_memLp_top_euclideanFieldLpNormOn_le_of_ae_representative
    (isOpen_euclideanBall _ _).measurableSet hgHalf hGae (mul_nonneg hCc.le hB) hpoint
  refine ⟨G, hG, hgTop, hGae, ?_⟩
  have hseminorm := euclideanFieldHolderSeminormOn_le hG hL hholder
  have hfirst : Cc * B ≤ Cc * A / α ^ 2 := by
    have hαsq : 0 < α ^ 2 := sq_pos_of_pos hα0
    apply (le_div_iff₀ hαsq).2
    dsimp only [B]
    have hreduce : (Cc * (A / α)) * α ^ 2 = (Cc * A) * α := by
      field_simp
    rw [hreduce]
    exact mul_le_of_le_one_right (mul_nonneg hCc.le hA) hα1.le
  calc
    _ ≤ Cc * B + r₀ ^ α * L :=
      add_le_add hnorm (mul_le_mul_of_nonneg_left hseminorm hp.le)
    _ = Cc * B + 2 * Cc * A / α ^ 2 := by
      dsimp only [L, K, B]
      field_simp
      ring
    _ ≤ Cc * A / α ^ 2 + 2 * Cc * A / α ^ 2 := add_le_add hfirst le_rfl
    _ = _ := by ring

end

end PDE
