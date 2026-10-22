module

public import EllipticRegularity.Parabolic.CauchyDef
public import Ch5NashStatements.CauchyExistence
public import Ch5NashStatements.CauchyUniqueness

/-!
# The Cauchy solution operator: definition, characterization, measurability

`cauchyOp a s t f` is the time-`t` slice of a Cauchy solution with datum `f`, chosen by
`Classical.choose` when one exists (and `0` otherwise).  For `f ∈ L²` and parabolic coefficients a
solution exists (`cauchyExistence`) and every other solution has the same time-`t` slice a.e.
(`cauchyUniqueness`).  The slice is a.e.-strongly measurable because every solution has
`L²_loc` slices (`ParH1Function.sliceL2loc`) on the compact cubes exhausting `ℝ^d`.
-/

@[expose] public section

namespace PDE.Parabolic.NashKernel

open MeasureTheory Set

/-- The Cauchy solution operator: the time-`t` slice of a chosen Cauchy solution with datum `f`
on `[s,t]`; `0` if there is none. -/
noncomputable def cauchyOp {d : ℕ} (a : ParCoeffField d) (s t : ℝ) (f : Vec d → ℝ) : Vec d → ℝ :=
  open Classical in
  if h : ∃ u : ParH1Function (univ : Set (Vec d)) (Icc s t), IsCauchySolution a s t f u then
    fun x => (Classical.choose h).toFun (x, t)
  else 0

variable {d : ℕ} {Lam : ℝ} {a : ParCoeffField d} {s t : ℝ}

/-- A solution with datum `f` exists and `cauchyOp` is (literally) its time-`t` slice. -/
theorem exists_cauchyOp_eq (hst : s < t) (ha : IsParabolicCoeff 1 Lam a univ (Icc s t))
    {f : Vec d → ℝ} (hf : MemLp f 2 volume) :
    ∃ u : ParH1Function (univ : Set (Vec d)) (Icc s t), IsCauchySolution a s t f u ∧
      cauchyOp a s t f = fun x => u.toFun (x, t) := by
  have h := cauchyExistence d 1 Lam a s t hst ha f hf
  refine ⟨Classical.choose h, Classical.choose_spec h, ?_⟩
  simp only [cauchyOp, h, dite_true]

/-- Characterization: every Cauchy solution with datum `f` has time-`t` slice a.e. equal to
`cauchyOp a s t f`. -/
theorem cauchyOp_ae_eq (hst : s < t) (ha : IsParabolicCoeff 1 Lam a univ (Icc s t))
    {f : Vec d → ℝ} (hf : MemLp f 2 volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s t)) (hu : IsCauchySolution a s t f u) :
    (fun x => u.toFun (x, t)) =ᵐ[volume] cauchyOp a s t f := by
  obtain ⟨v, hv, hveq⟩ := exists_cauchyOp_eq hst ha hf
  rw [hveq]
  exact (cauchyUniqueness d 1 Lam a s t hst ha f hf u v hu hv).1 t ⟨hst.le, le_rfl⟩

/-- Slices of solutions are a.e.-strongly measurable. -/
theorem aestronglyMeasurable_slice
    (u : ParH1Function (univ : Set (Vec d)) (Icc s t)) (hst : s ≤ t) :
    AEStronglyMeasurable (fun x => u.toFun (x, t)) volume := by
  have hK : ∀ n : ℕ, AEStronglyMeasurable (fun x => u.toFun (x, t))
      (volume.restrict (Metric.closedBall (0 : Vec d) n)) := fun n =>
    (u.sliceL2loc t ⟨hst, le_rfl⟩ _ (isCompact_closedBall _ _) (subset_univ _)).aestronglyMeasurable
  have h := aestronglyMeasurable_iUnion_iff.mpr hK
  have hU : (⋃ n : ℕ, Metric.closedBall (0 : Vec d) n) = univ := by
    refine eq_univ_of_forall fun x => ?_
    obtain ⟨n, hn⟩ := exists_nat_ge ‖x‖
    exact mem_iUnion.2 ⟨n, by simpa using hn⟩
  rwa [hU, Measure.restrict_univ] at h

/-- `cauchyOp` is a.e.-strongly measurable. -/
theorem aestronglyMeasurable_cauchyOp (hst : s < t)
    (ha : IsParabolicCoeff 1 Lam a univ (Icc s t)) {f : Vec d → ℝ} (hf : MemLp f 2 volume) :
    AEStronglyMeasurable (cauchyOp a s t f) volume := by
  obtain ⟨u, -, hu⟩ := exists_cauchyOp_eq hst ha hf
  rw [hu]
  exact aestronglyMeasurable_slice u hst.le

/-- A measurable representative of `cauchyOp` (via `AEStronglyMeasurable.mk`). -/
noncomputable def cauchyOpMk (a : ParCoeffField d) (s t : ℝ) (f : Vec d → ℝ) : Vec d → ℝ :=
  open Classical in
  if h : AEStronglyMeasurable (cauchyOp a s t f) volume then h.mk _ else 0

theorem stronglyMeasurable_cauchyOpMk (hst : s < t)
    (ha : IsParabolicCoeff 1 Lam a univ (Icc s t)) {f : Vec d → ℝ} (hf : MemLp f 2 volume) :
    StronglyMeasurable (cauchyOpMk a s t f) := by
  have h := aestronglyMeasurable_cauchyOp hst ha hf
  simp only [cauchyOpMk, h, dite_true]
  exact h.stronglyMeasurable_mk

theorem cauchyOpMk_ae_eq (hst : s < t) (ha : IsParabolicCoeff 1 Lam a univ (Icc s t))
    {f : Vec d → ℝ} (hf : MemLp f 2 volume) :
    cauchyOpMk a s t f =ᵐ[volume] cauchyOp a s t f := by
  have h := aestronglyMeasurable_cauchyOp hst ha hf
  simp only [cauchyOpMk, h, dite_true]
  exact h.ae_eq_mk.symm

/-- Invariance under a.e.-equal data. -/
theorem cauchyOp_congr_ae (hst : s < t) (ha : IsParabolicCoeff 1 Lam a univ (Icc s t))
    {f g : Vec d → ℝ} (hf : MemLp f 2 volume) (hfg : f =ᵐ[volume] g) :
    cauchyOp a s t f =ᵐ[volume] cauchyOp a s t g := by
  have hg : MemLp g 2 volume := hf.ae_eq hfg
  obtain ⟨u, ⟨hu1, hu2⟩, hu⟩ := exists_cauchyOp_eq hst ha hf
  have hu' : IsCauchySolution a s t g u := ⟨hu1, by
    filter_upwards [hu2, hfg] with x h1 h2 using h1.trans h2⟩
  have h2 := cauchyOp_ae_eq hst ha hg u hu'
  rw [hu]
  exact h2

end PDE.Parabolic.NashKernel
