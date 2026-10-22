module

public import EllipticRegularity.Parabolic.NashKernel.KernelDomainMain
public import EllipticRegularity.Parabolic.NashKernel.OperatorBounds

/-!
# A bounded kernel representing the Cauchy solution operator on `L¹ ∩ L²`

`exists_cauchyOp_kernel`: for parabolic coefficients, the dyadic data
`T n k = cauchyOpMk (1_{cube n k})` satisfy the hypotheses of
`exists_kernel_representationD`, which yields a jointly measurable kernel `0 ≤ P ≤ M`,
`M = C (t-s)^{-d/2}` (`C = C(d)`), with `cauchyOp a s t f = ∫ P(·,y) f(y) dy` a.e. for every
`f ∈ L¹ ∩ L²`.
-/

@[expose] public section

namespace PDE.Parabolic.NashKernel

open MeasureTheory Set PDE.NashKernelDyadic PDE.NashKernelExtend

variable {d : ℕ} {Lam : ℝ} {a : ParCoeffField d} {s t : ℝ}

/-- Additivity of `cauchyOp` over a finite sum, a.e. -/
theorem cauchyOp_sum_ae (hst : s < t) (ha : IsParabolicCoeff 1 Lam a univ (Icc s t))
    {ι : Type*} [DecidableEq ι] (S : Finset ι) {f : ι → Vec d → ℝ} (hf : ∀ i, MemLp (f i) 2 volume) :
    cauchyOp a s t (∑ i ∈ S, f i) =ᵐ[volume] ∑ i ∈ S, cauchyOp a s t (f i) := by
  induction S using Finset.induction_on with
  | empty =>
    have h := cauchyOp_smul_ae hst ha (0 : ℝ) (f := (0 : Vec d → ℝ)) MemLp.zero
    simp only [Finset.sum_empty]
    filter_upwards [h] with x hx
    simpa using hx
  | insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hS : MemLp (∑ j ∈ S, f j) 2 volume := memLp_finsetSum' S fun j _ => hf j
    filter_upwards [cauchyOp_add_ae hst ha (hf i) hS, ih] with x h1 h2
    rw [h1, Pi.add_apply, Pi.add_apply, h2]

theorem indicator_cube_succ_eq_sum (n : ℕ) (k : Fin d → ℤ) :
    (cube n k).indicator (fun _ => (1 : ℝ)) =
      ∑ ε : Fin d → Bool, (cube (n + 1) (child k ε)).indicator fun _ => (1 : ℝ) := by
  funext y
  rw [Finset.sum_apply]
  by_cases hy : y ∈ cube n k
  · rw [cube_succ_eq_iUnion] at hy
    obtain ⟨ε, hε⟩ := mem_iUnion.mp hy
    rw [Set.indicator_of_mem (by rw [cube_succ_eq_iUnion]; exact mem_iUnion.mpr ⟨ε, hε⟩)]
    rw [Finset.sum_eq_single ε]
    · simp [hε]
    · intro ε' _ hne
      have : y ∉ cube (n + 1) (child k ε') := fun h =>
        Set.disjoint_left.mp (pairwise_disjoint_child n k hne.symm) hε h
      simp [this]
    · simp
  · rw [Set.indicator_of_notMem hy]
    symm
    refine Finset.sum_eq_zero fun ε _ => ?_
    have : y ∉ cube (n + 1) (child k ε) := fun h => hy (by
      rw [cube_succ_eq_iUnion]; exact mem_iUnion.mpr ⟨ε, h⟩)
    simp [this]

theorem memLp_indicator_cube (n : ℕ) (k : Fin d → ℤ) :
    MemLp ((cube n k).indicator fun _ => (1 : ℝ)) 2 volume :=
  (dom_indicator_one (measurableSet_cube n k) (volume_cube_lt_top n k)).2

/-- A bounded jointly measurable kernel representing `cauchyOp` on `L¹ ∩ L²`. -/
theorem exists_cauchyOp_kernel (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ Lam : ℝ, 1 ≤ Lam → ∀ (a : ParCoeffField d) (s t : ℝ), s < t →
      IsParabolicCoeff 1 Lam a univ (Icc s t) →
      ∃ P : Vec d → Vec d → ℝ, Measurable (Function.uncurry P) ∧
        (∀ x y, 0 ≤ P x y ∧ P x y ≤ C * (t - s) ^ (-(d : ℝ) / 2)) ∧
        ∀ f : Vec d → ℝ, Dom f → cauchyOp a s t f =ᵐ[volume] kerOp P f := by
  obtain ⟨C, hC, hbd⟩ := cauchyOp_abs_le_ae hd
  refine ⟨C, hC, fun Lam hLam a s t hst ha => ?_⟩
  have hM : 0 ≤ C * (t - s) ^ (-(d : ℝ) / 2) :=
    mul_nonneg hC.le (Real.rpow_nonneg (sub_pos.2 hst).le _)
  have hmk : ∀ n k, cauchyOpMk a s t ((cube n k).indicator fun _ => (1 : ℝ)) =ᵐ[volume]
      cauchyOp a s t ((cube n k).indicator fun _ => (1 : ℝ)) := fun n k =>
    cauchyOpMk_ae_eq hst ha (memLp_indicator_cube n k)
  have hL : LinearBoundedD (C * (t - s) ^ (-(d : ℝ) / 2)) (cauchyOp a s t) :=
    { add := fun f g hf hg => cauchyOp_add_ae hst ha hf.2 hg.2
      smul := fun c f hf => cauchyOp_smul_ae hst ha c hf.2
      bound := fun f hf => by
        filter_upwards [hbd Lam hLam a s t hst ha f hf.1 hf.2] with x hx
        exact hx }
  obtain ⟨P, hPm, hPb, hrep⟩ := exists_kernel_representationD hM
    (T := fun n k => cauchyOpMk a s t ((cube n k).indicator fun _ => (1 : ℝ)))
    (fun n k => (stronglyMeasurable_cauchyOpMk hst ha (memLp_indicator_cube n k)).aemeasurable)
    (fun n k => by
      have h0 := cauchyOp_nonneg_ae hst ha (memLp_indicator_cube n k)
        (ae_of_all _ fun y => Set.indicator_nonneg (fun _ _ => zero_le_one) y)
      have h1 := hbd Lam hLam a s t hst ha _
        (dom_indicator_one (measurableSet_cube n k) (volume_cube_lt_top n k)).1
        (memLp_indicator_cube n k)
      have hint : ∫ y, |(cube n k).indicator (fun _ => (1 : ℝ)) y| = (volume (cube n k)).toReal := by
        have : (fun y => |(cube n k).indicator (fun _ => (1 : ℝ)) y|) =
            (cube n k).indicator (fun _ => (1 : ℝ)) := by
          ext y; by_cases hy : y ∈ cube n k <;> simp [hy]
        rw [this, integral_indicator (measurableSet_cube n k)]
        simp [Measure.real]
      rw [hint] at h1
      filter_upwards [hmk n k, h0, h1] with x e a1 a2
      rw [e]
      refine ⟨a1, ?_⟩
      have := (abs_le.mp a2).2
      linarith)
    (fun n k => by
      have hs : ∀ ε : Fin d → Bool, MemLp ((cube (n + 1) (child k ε)).indicator fun _ => (1 : ℝ))
          2 volume := fun ε => memLp_indicator_cube _ _
      have h1 := cauchyOp_sum_ae hst ha (Finset.univ : Finset (Fin d → Bool)) hs
      rw [← indicator_cube_succ_eq_sum] at h1
      have h2 : ∀ᵐ x, ∀ ε : Fin d → Bool,
          cauchyOpMk a s t ((cube (n + 1) (child k ε)).indicator fun _ => (1 : ℝ)) x =
            cauchyOp a s t ((cube (n + 1) (child k ε)).indicator fun _ => (1 : ℝ)) x :=
        ae_all_iff.2 fun ε => hmk _ _
      filter_upwards [hmk n k, h1, h2] with x e e1 e2
      rw [e, e1, Finset.sum_apply]
      exact Finset.sum_congr rfl fun ε _ => (e2 ε).symm)
    hL (fun n k => (hmk n k).symm)
  exact ⟨P, hPm, hPb, hrep⟩

end PDE.Parabolic.NashKernel
