module

public import PDEFoundation.Analysis.Newtonian.WeakType.HormanderIntegral
public import PDEFoundation.Analysis.Newtonian.WeakType.DecompositionGoodBadL1
public import PDEFoundation.Analysis.Newtonian.WeakType.DecompositionExceptional

/-! # The Hörmander integral for the bad parts

The abstract Hörmander integral bound applied to the bad parts `b_k` of the Calderón–Zygmund
decomposition, over the complement of the dilated cube `Q_k*`, and summed over `k`.
-/

@[expose] public section

open BoxIntegral MeasureTheory Set
open scoped ENNReal

namespace PDE.NewtonWeakType

noncomputable section

variable {d : ℕ} {I : Box (Fin d)} {F : Vec d → Vec d} {lam : ℝ} {S : CZStopping I F lam}

/-- The bad part vanishes outside the closed circumscribed ball of its cube. -/
theorem czBad_eq_zero_of_czRadius_lt (hd : 0 < d) (k : S.ι) {y : Vec d}
    (hy : czRadius S k < vecEuclideanNorm (y - czCenter S k)) : czBad S k y = 0 :=
  czBad_of_notMem S (fun h => absurd (vecEuclideanNorm_sub_czCenter_le S hd h) (not_le.mpr hy))

/-- **Hörmander integral for one bad part**: outside `Q_k*`, the Hörmander integrand has
integral at most `C(d) A · 2 ‖F‖_{L¹(Q_k)}`. -/
theorem lintegral_hormander_czBad_le (hd : 0 < d) {K : Vec d → Mat d} {A : ℝ} (hA : 0 ≤ A)
    (hK : KernelHolder d K A) (hF : ∀ i, IntegrableOn (fun x => F x i) (I : Set (Vec d)))
    (k : S.ι) :
    ∫⁻ x in (czDilate S k)ᶜ,
        ENNReal.ofReal (vecEuclideanNorm
          (fun i => ∫ y, matVecMul (K (x - y) - K (x - czCenter S k)) (czBad S k y) i)) ≤
      ENNReal.ofReal (hormanderConst d * A) *
        (2 * ∫⁻ x in (S.cube k : Set (Vec d)), ENNReal.ofReal (vecEuclideanNorm (F x))) := by
  have : NeZero d := ⟨hd.ne'⟩
  have hb := integrable_czBad_coord hF (S := S) k
  have hmain := lintegral_exterior_hormander_le hA hK (czRadius_pos S hd k) hb
    (fun y hy => czBad_eq_zero_of_czRadius_lt hd k hy)
  refine hmain.trans ?_
  have hint : Integrable (fun y => vecEuclideanNorm (czBad S k y)) :=
    integrable_vecEuclideanNorm_of_coord (czBad S k) hb
  rw [ENNReal.ofReal_mul (mul_nonneg (hormanderConst_nonneg d) hA),
    ofReal_integral_eq_lintegral_ofReal hint
      (Filter.Eventually.of_forall fun y => vecEuclideanNorm_nonneg _)]
  exact mul_le_mul_right (lintegral_vecEuclideanNorm_czBad_le hF k) _

/-- **Hörmander integral summed over the stopping cubes**:
`Σ_k ∫_{(Q_k*)ᶜ} |∫ (K(x-y) - K(x-c_k)) b_k(y) dy| dx ≤ C(d) A · 2 ‖F‖₁`. -/
theorem tsum_lintegral_hormander_czBad_le (hd : 0 < d) {K : Vec d → Mat d} {A : ℝ} (hA : 0 ≤ A)
    (hK : KernelHolder d K A) (hF : ∀ i, IntegrableOn (fun x => F x i) (I : Set (Vec d))) :
    ∑' k, ∫⁻ x in (czDilate S k)ᶜ,
        ENNReal.ofReal (vecEuclideanNorm
          (fun i => ∫ y, matVecMul (K (x - y) - K (x - czCenter S k)) (czBad S k y) i)) ≤
      ENNReal.ofReal (hormanderConst d * A) *
        (2 * ∫⁻ x in (I : Set (Vec d)), ENNReal.ofReal (vecEuclideanNorm (F x))) := by
  have hmeas : ∀ k, MeasurableSet (S.cube k : Set (Vec d)) := fun k => (S.cube k).measurableSet_coe
  calc
    _ ≤ ∑' k, ENNReal.ofReal (hormanderConst d * A) *
        (2 * ∫⁻ x in (S.cube k : Set (Vec d)), ENNReal.ofReal (vecEuclideanNorm (F x))) :=
      ENNReal.tsum_le_tsum fun k => lintegral_hormander_czBad_le hd hA hK hF k
    _ = ENNReal.ofReal (hormanderConst d * A) *
        (2 * ∫⁻ x in ⋃ k, (S.cube k : Set (Vec d)), ENNReal.ofReal (vecEuclideanNorm (F x))) := by
      rw [ENNReal.tsum_mul_left, ENNReal.tsum_mul_left,
        lintegral_iUnion hmeas S.pairwise_disjoint]
    _ ≤ _ := mul_le_mul_right (mul_le_mul_right
      (lintegral_mono_set (iUnion_subset fun k => czCube_subset_root S k)) _) _

end

end PDE.NewtonWeakType
