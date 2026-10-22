module

public import PDEFoundation.Euler.TorusTranslate
public import PDEFoundation.Geometry.EuclideanBall.Basic
public import PDEFoundation.Geometry.EuclideanBall.Topology

/-!
# Periodic tiling bound for the unit ball

For a continuous nonnegative `ℤ²`-periodic `f` and `z ∈ [0,1]²`, `∫_{B₁} f (z + x) dx ≤ 9 ∫_{[0,1]²} f`:
`z + B₁ ⊆ (-1,2)²` is covered by the nine unit-cube translates `a + [0,1]²`, `a ∈ {-1,0,1}²`.
-/

@[expose] public section

open MeasureTheory Set

namespace PDE

/-- The integer lattice vector `∑ nᵢ eᵢ`. -/
noncomputable def latVec (n : Fin 2 → ℤ) : Vec 2 := ∑ i, (n i : ℝ) • basisVec i

theorem latVec_apply (n : Fin 2 → ℤ) (i : Fin 2) : latVec n i = n i := by
  simp [latVec, Finset.sum_apply, basisVec, Pi.single_apply]

theorem coord_cover (y : ℝ) (h1 : -1 < y) (h2 : y < 2) :
    ∃ m : Fin 3, (((m : ℕ) : ℤ) - 1 : ℤ) ≤ y ∧ y < (((m : ℕ) : ℤ) - 1 : ℤ) + 1 := by
  rcases lt_or_ge y 0 with h | h
  · exact ⟨0, by simp; linarith, by simp; linarith⟩
  rcases lt_or_ge y 1 with h' | h'
  · exact ⟨1, by simp; linarith, by simp; linarith⟩
  · exact ⟨2, by simp; linarith, by simp; linarith⟩

theorem setIntegral_ball_comp_add_le {f : Vec 2 → ℝ} (hc : Continuous f) (hp : IsTorusPeriodic f)
    (h0 : ∀ x, 0 ≤ f x) {z : Vec 2} (hz : z ∈ torusCube) :
    ∫ x in euclideanBall (0 : Vec 2) 1, f (z + x) ≤ 9 * ∫ x in torusCube, f x := by
  set B := euclideanBall (0 : Vec 2) 1 with hB
  set G : Vec 2 → ℝ := torusCube.indicator f with hG
  have hGnn : ∀ x, 0 ≤ G x := fun x => Set.indicator_nonneg (fun y _ => h0 y) x
  have hGint : Integrable G :=
    (hc.continuousOn.integrableOn_Icc (a := (0 : Vec 2)) (b := 1)).integrable_indicator
      (by exact measurableSet_Icc)
  let w : (Fin 2 → Fin 3) → Vec 2 := fun idx =>
    z - latVec (fun i => (((idx i : ℕ) : ℤ) - 1))
  have hshift : ∀ idx : Fin 2 → Fin 3, ∫ x, G (x + w idx) = ∫ x, G x := fun idx =>
    (measurePreserving_add_right (volume : Measure (Vec 2)) (w idx)).integral_comp
      (measurableEmbedding_addRight (w idx)) G
  have hsum : Integrable (fun x => ∑ idx : Fin 2 → Fin 3, G (x + w idx)) :=
    integrable_finsetSum _ fun idx _ => (measurePreserving_add_right (volume : Measure (Vec 2)) (w idx)).integrable_comp_of_integrable hGint
  have hBint : Integrable (B.indicator fun x => f (z + x)) := by
    have hsub : B ⊆ Icc (-1 : Vec 2) 1 := by
      intro x hx
      have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt one_pos).1 hx
      rw [sub_zero] at hx'
      constructor <;> intro i <;>
        have := abs_apply_le_vecEuclideanNorm x i <;> have := abs_le.mp this <;>
        simp <;> linarith [(abs_le.mp (abs_apply_le_vecEuclideanNorm x i))]
    have hcont : Continuous fun x => f (z + x) := hc.comp (continuous_const.add continuous_id)
    refine IntegrableOn.integrable_indicator ?_ (isOpen_euclideanBall _ _).measurableSet
    exact (hcont.continuousOn.integrableOn_Icc (a := (-1 : Vec 2)) (b := 1)).mono_set hsub
  have hpt : ∀ x, B.indicator (fun x => f (z + x)) x ≤ ∑ idx : Fin 2 → Fin 3, G (x + w idx) := by
    intro x
    by_cases hx : x ∈ B
    · rw [Set.indicator_of_mem hx]
      have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt one_pos).1 hx
      rw [sub_zero] at hx'
      have hxi : ∀ i, |x i| < 1 := fun i => lt_of_le_of_lt (abs_apply_le_vecEuclideanNorm x i) hx'
      have hzi : ∀ i, 0 ≤ z i ∧ z i ≤ 1 := fun i => ⟨hz.1 i, hz.2 i⟩
      have hex : ∀ i, ∃ m : Fin 3, (((m : ℕ) : ℤ) - 1 : ℤ) ≤ z i + x i ∧
          z i + x i < (((m : ℕ) : ℤ) - 1 : ℤ) + 1 := fun i => by
        have := abs_lt.mp (hxi i)
        exact coord_cover _ (by linarith [(hzi i).1]) (by linarith [(hzi i).2])
      choose m hm using hex
      have hmem : x + w m ∈ torusCube := by
        constructor <;> intro i <;> simp only [w, Pi.add_apply, Pi.sub_apply, latVec_apply] <;>
          simp only [Pi.zero_apply, Pi.one_apply] <;> push_cast at hm ⊢ <;>
          linarith [(hm i).1, (hm i).2]
      have hval : f (x + w m) = f (z + x) := by
        have := hp.add_lattice (fun i => (((m i : ℕ) : ℤ) - 1)) (x + w m)
        rw [← this]
        congr 1
        simp only [w, latVec]
        abel
      calc f (z + x) = G (x + w m) := by
            rw [hG, Set.indicator_of_mem hmem, hval]
        _ ≤ _ := Finset.single_le_sum (f := fun idx => G (x + w idx)) (fun i _ => hGnn _)
            (Finset.mem_univ m)
    · rw [Set.indicator_of_notMem hx]
      exact Finset.sum_nonneg fun idx _ => hGnn _
  calc ∫ x in B, f (z + x) = ∫ x, B.indicator (fun x => f (z + x)) x :=
        (integral_indicator (isOpen_euclideanBall _ _).measurableSet).symm
    _ ≤ ∫ x, ∑ idx : Fin 2 → Fin 3, G (x + w idx) := integral_mono hBint hsum hpt
    _ = ∑ idx : Fin 2 → Fin 3, ∫ x, G (x + w idx) := integral_finsetSum _ fun idx _ =>
          (measurePreserving_add_right (volume : Measure (Vec 2)) (w idx)).integrable_comp_of_integrable hGint
    _ = 9 * ∫ x in torusCube, f x := by
        simp only [hshift]
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun]
        simp [hG, integral_indicator (measurableSet_Icc (a := (0 : Vec 2)) (b := 1)), torusCube]

/-- The four ball centres `(1/4 or 3/4, 1/4 or 3/4)`. -/
noncomputable def ballCentre (idx : Fin 2 → Fin 2) : Vec 2 :=
  fun i => if idx i = 0 then 1 / 4 else 3 / 4

theorem ballCentre_mem (idx : Fin 2 → Fin 2) : ballCentre idx ∈ torusCube := by
  constructor <;> intro i <;> simp only [ballCentre] <;> split_ifs <;> norm_num

/-- The four balls `B_{1/2}(z)` cover the unit cube, in integral form. -/
theorem setIntegral_cube_le_sum_balls {f : Vec 2 → ℝ} (hc : Continuous f) (h0 : ∀ x, 0 ≤ f x) :
    ∫ x in torusCube, f x ≤
      ∑ idx : Fin 2 → Fin 2, ∫ x in euclideanBall (0 : Vec 2) (1 / 2 : ℝ), f (ballCentre idx + x) := by
  set B := euclideanBall (0 : Vec 2) (1 / 2 : ℝ) with hB
  have hBm : MeasurableSet B := (isOpen_euclideanBall (0 : Vec 2) (1 / 2 : ℝ)).measurableSet
  let H : (Fin 2 → Fin 2) → Vec 2 → ℝ := fun idx x => B.indicator (fun x => f (ballCentre idx + x)) x
  have hBsub : B ⊆ Icc (-1 : Vec 2) 1 := by
    intro x hx
    have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).1 hx
    rw [sub_zero] at hx'
    constructor <;> intro i <;> simp <;> linarith [(abs_le.mp (abs_apply_le_vecEuclideanNorm x i))]
  have hHint : ∀ idx, Integrable (H idx) := fun idx => by
    have hcont : Continuous fun x => f (ballCentre idx + x) :=
      hc.comp (continuous_const.add continuous_id)
    refine IntegrableOn.integrable_indicator ?_ hBm
    exact (hcont.continuousOn.integrableOn_Icc (a := (-1 : Vec 2)) (b := 1)).mono_set hBsub
  have hfint : Integrable (torusCube.indicator f) :=
    (hc.continuousOn.integrableOn_Icc (a := (0 : Vec 2)) (b := 1)).integrable_indicator
      measurableSet_Icc
  have hpt : ∀ y, torusCube.indicator f y ≤ ∑ idx : Fin 2 → Fin 2, H idx (y - ballCentre idx) := by
    intro y
    by_cases hy : y ∈ torusCube
    · rw [Set.indicator_of_mem hy]
      let idx : Fin 2 → Fin 2 := fun i => if y i ≤ 1 / 2 then 0 else 1
      have hmem : y - ballCentre idx ∈ B := by
        rw [hB, mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num), sub_zero]
        have hsq : vecNormSq (y - ballCentre idx) < (1 / 2 : ℝ) ^ 2 := by
          have hi : ∀ i, (y i - ballCentre idx i) ^ 2 ≤ 1 / 16 := by
            intro i
            have h1 := hy.1 i
            have h2 := hy.2 i
            simp only [Pi.zero_apply] at h1
            simp only [Pi.one_apply] at h2
            by_cases hh : y i ≤ 1 / 2
            · simp only [ballCentre, idx, hh, ite_true]
              nlinarith
            · simp only [ballCentre, idx, hh, ite_false]
              have : (1 : Fin 2) ≠ 0 := by decide
              simp only [this, ite_false]
              nlinarith
          simp only [vecNormSq, vecDot, Fin.sum_univ_two, Pi.sub_apply]
          nlinarith [hi 0, hi 1]
        rw [vecEuclideanNorm]
        calc Real.sqrt (vecNormSq (y - ballCentre idx)) < Real.sqrt ((1 / 2 : ℝ) ^ 2) :=
              Real.sqrt_lt_sqrt (vecNormSq_nonneg _) hsq
          _ = 1 / 2 := Real.sqrt_sq (by norm_num)
      have : H idx (y - ballCentre idx) = f y := by
        simp only [H, Set.indicator_of_mem hmem]
        congr 1
        abel
      calc f y = H idx (y - ballCentre idx) := this.symm
        _ ≤ _ := Finset.single_le_sum (f := fun idx => H idx (y - ballCentre idx))
            (fun i _ => Set.indicator_nonneg (fun w _ => h0 _) _) (Finset.mem_univ idx)
    · rw [Set.indicator_of_notMem hy]
      exact Finset.sum_nonneg fun idx _ => Set.indicator_nonneg (fun w _ => h0 _) _
  have hmp : ∀ idx, MeasurePreserving (fun y : Vec 2 => y - ballCentre idx) volume volume :=
    fun idx => measurePreserving_sub_right (volume : Measure (Vec 2)) (ballCentre idx)
  have hshift : ∀ idx, ∫ y, H idx (y - ballCentre idx) = ∫ x in B, f (ballCentre idx + x) := by
    intro idx
    rw [(hmp idx).integral_comp (measurableEmbedding_subRight (ballCentre idx)) (H idx)]
    exact integral_indicator hBm
  calc ∫ x in torusCube, f x = ∫ y, torusCube.indicator f y :=
        (integral_indicator measurableSet_Icc).symm
    _ ≤ ∫ y, ∑ idx : Fin 2 → Fin 2, H idx (y - ballCentre idx) :=
        integral_mono hfint (integrable_finsetSum _ fun idx _ =>
          (hmp idx).integrable_comp_of_integrable (hHint idx)) hpt
    _ = ∑ idx : Fin 2 → Fin 2, ∫ y, H idx (y - ballCentre idx) :=
        integral_finsetSum _ fun idx _ => (hmp idx).integrable_comp_of_integrable (hHint idx)
    _ = _ := Finset.sum_congr rfl fun idx _ => hshift idx

end PDE
