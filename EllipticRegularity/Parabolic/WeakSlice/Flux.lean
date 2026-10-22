module

public import EllipticRegularity.Parabolic.ParabolicDef

/-!
# Integrability of the flux `a ∇u · ∇ζ` on `U × J`

For a parabolic coefficient field, `u ∈ H¹_par`, and `ζ ∈ C¹_c(U)`, the flux
`(x,τ) ↦ a(x,τ) ∇u(x,τ) · ∇ζ(x)` is integrable on `U ×ˢ J` for every measurable `J ⊆ I` of
finite measure.  Also the elementary matrix bounds from (5.1) are re-exported.
-/

@[expose] public section

namespace PDE.Parabolic.WeakSlice

open MeasureTheory Set Filter Topology PDE

/-! ### Elementary matrix bounds (5.1), re-exported from the foundation. -/

/-- `|A e|² ≤ Λ e · A e`. -/
theorem matrix_normSq_le_mul_dot {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (e : Vec d) :
    vecNormSq (matVecMul A e) ≤ Lam * vecDot e (matVecMul A e) :=
  vecNormSq_matVecMul_le_mul_vecDot_of_isEllipticMatrix hA e

/-- `|A e|² ≤ Λ² |e|²`. -/
theorem matrix_normSq_le_sq {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (e : Vec d) :
    vecNormSq (matVecMul A e) ≤ Lam ^ 2 * vecNormSq e :=
  vecNormSq_matVecMul_le_of_isEllipticMatrix hA e

/-- `|A_{ij}| ≤ Λ`. -/
theorem matrix_abs_entry_le {d : ℕ} {lam Lam : ℝ} {A : Mat d}
    (hA : IsEllipticMatrix lam Lam A) (i j : Fin d) : |A i j| ≤ Lam :=
  abs_apply_le_of_isEllipticMatrix hA i j

theorem spaceGradC1_eq_zero_of_notMem {d : ℕ} {ζ : Vec d → ℝ} {x : Vec d}
    (hx : x ∉ tsupport ζ) : spaceGradC1 ζ x = 0 := by
  have h : fderiv ℝ ζ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun hh => hx (tsupport_fderiv_subset ℝ hh))
  ext i; simp [spaceGradC1, h]

theorem spaceGradC1_continuous {d : ℕ} {ζ : Vec d → ℝ} (hζ : ContDiff ℝ 1 ζ) (i : Fin d) :
    Continuous fun x => spaceGradC1 ζ x i :=
  (hζ.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem spaceGradC1_bound {d : ℕ} {ζ : Vec d → ℝ} (hζ : ContDiff ℝ 1 ζ)
    (hζc : HasCompactSupport ζ) : ∃ W : ℝ, 0 ≤ W ∧ ∀ i x, |spaceGradC1 ζ x i| ≤ W := by
  have : ∀ i : Fin d, ∃ C : ℝ, ∀ x, ‖spaceGradC1 ζ x i‖ ≤ C := by
    intro i
    refine (spaceGradC1_continuous hζ i).bounded_above_of_compact_support ?_
    refine HasCompactSupport.of_support_subset_isCompact (K := tsupport ζ) hζc ?_
    intro x hx
    by_contra hn
    exact hx (by simp [spaceGradC1_eq_zero_of_notMem hn])
  choose C hC using this
  refine ⟨∑ i, |C i|, Finset.sum_nonneg fun i _ => abs_nonneg _, fun i x => ?_⟩
  calc |spaceGradC1 ζ x i| ≤ C i := hC i x
    _ ≤ |C i| := le_abs_self _
    _ ≤ ∑ i, |C i| := Finset.single_le_sum (f := fun i => |C i|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ i)

/-- The flux is integrable on `U ×ˢ J` for measurable `J ⊆ I` of finite measure. -/
theorem integrableOn_flux {d : ℕ} {lam Lam : ℝ} {U : Set (Vec d)} (hU : IsOpen U)
    {I : Set ℝ} {a : ParCoeffField d} (ha : IsParabolicCoeff lam Lam a U I)
    (u : ParH1Function U I) {ζ : Vec d → ℝ} (hζ : ContDiff ℝ 1 ζ) (hζc : HasCompactSupport ζ)
    (hζU : tsupport ζ ⊆ U) {J : Set ℝ} (hJI : J ⊆ I) (hJm : MeasurableSet J)
    (hJ : volume J < ⊤) :
    IntegrableOn (fun z : Vec d × ℝ => vecDot (matVecMul (a z) (u.grad z)) (spaceGradC1 ζ z.1))
      (U ×ˢ J) := by
  set K := tsupport ζ with hK
  have hKc : IsCompact K := hζc
  set F : Vec d × ℝ → ℝ :=
    fun z => vecDot (matVecMul (a z) (u.grad z)) (spaceGradC1 ζ z.1) with hF
  -- reduce to `K ×ˢ J`
  suffices hKJ : IntegrableOn F (K ×ˢ J) from by
    refine hKJ.of_forall_sdiff_eq_zero (hU.measurableSet.prod hJm) ?_
    rintro ⟨x, τ⟩ ⟨hz, hn⟩
    have hx : x ∉ K := fun hx => hn ⟨hx, hz.2⟩
    simp only [hF, spaceGradC1_eq_zero_of_notMem hx]
    simp [vecDot]
  have hKJU : K ×ˢ J ⊆ U ×ˢ I := prod_mono hζU hJI
  set ν := volume.restrict (K ×ˢ J) with hν
  have hνle : ν ≤ volume.restrict (U ×ˢ I) := Measure.restrict_mono hKJU le_rfl
  have hfin : IsFiniteMeasure ν := by
    refine ⟨?_⟩
    rw [hν, Measure.restrict_apply_univ, Measure.volume_eq_prod, Measure.prod_prod]
    exact ENNReal.mul_lt_top hKc.measure_lt_top hJ
  obtain ⟨W, hW0, hW⟩ := spaceGradC1_bound hζ hζc
  have hell : ∀ᵐ z ∂ν, IsEllipticMatrix lam Lam (a z) := ha.elliptic.filter_mono (ae_mono hνle)
  have hgrad : ∀ j : Fin d, MemLp (fun z => u.grad z j) 2 ν := fun j =>
    (u.gradMemL2 j).mono_measure hνle
  have hgrad1 : ∀ j : Fin d, Integrable (fun z => |u.grad z j|) ν := fun j =>
    ((hgrad j).integrable one_le_two).abs
  -- the bound
  have hB : Integrable (fun z => ∑ i : Fin d, ∑ j : Fin d, Lam * W * |u.grad z j|) ν := by
    refine integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => ?_
    exact (hgrad1 j).const_mul _
  have hmeas : AEStronglyMeasurable F ν := by
    have hme : ∀ i j : Fin d, AEMeasurable (fun z : Vec d × ℝ => a z i j) ν := fun i j =>
      (ha.measurable i j).mono_measure hνle
    have : AEMeasurable F ν := by
      have hFeq : F = fun z => ∑ i : Fin d, (∑ j : Fin d, a z i j * u.grad z j) *
          spaceGradC1 ζ z.1 i := by
        ext z; simp [hF, vecDot, matVecMul]
      rw [hFeq]
      refine Finset.aemeasurable_fun_sum _ fun i _ => AEMeasurable.mul ?_ ?_
      · exact Finset.aemeasurable_fun_sum _ fun j _ => (hme i j).mul
          (hgrad j).aestronglyMeasurable.aemeasurable
      · exact ((spaceGradC1_continuous hζ i).comp continuous_fst).aemeasurable
    exact this.aestronglyMeasurable
  refine Integrable.mono' hB hmeas ?_
  filter_upwards [hell] with z hz
  have hb : ∀ i j : Fin d, |a z i j| ≤ Lam := fun i j => matrix_abs_entry_le hz i j
  simp only [hF, vecDot, matVecMul, Real.norm_eq_abs]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [abs_mul]
  have h1 : |∑ j, a z i j * u.grad z j| ≤ ∑ j, Lam * |u.grad z j| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right (hb i j) (abs_nonneg _)
  have h2 := hW i z.1
  calc |∑ j, a z i j * u.grad z j| * |spaceGradC1 ζ z.1 i|
      ≤ (∑ j, Lam * |u.grad z j|) * W :=
        mul_le_mul h1 h2 (abs_nonneg _) (Finset.sum_nonneg fun j _ =>
          mul_nonneg ((abs_nonneg _).trans (hb i i) ) (abs_nonneg _))
    _ = ∑ j, Lam * W * |u.grad z j| := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun j _ => by ring

end PDE.Parabolic.WeakSlice
