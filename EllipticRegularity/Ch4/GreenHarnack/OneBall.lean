module

public import DGNMStatements.Harnack
public import PDEFoundation.PDE.DGNM.Scaling
public import PDEFoundation.PDE.DGNM.ClassAlgebra
public import PDEFoundation.Measure.BallVolume
public import EllipticRegularity.Ch4.GreenHarnack.Shift

/-!
# The Harnack inequality on one ball `B_s(y)` with `B_{2s}(y) ⊆ V`

For `u ≥ 0` a solution in an open set `V ⊇ B_{2s}(y)`, the essential supremum of `u` over
`B_s(y)` is at most `exp(C_H √Λ)` times the essential infimum, where `C_H` is the constant of
the Harnack inequality (Theorem 4.18). Proof: blow up `u` to the unit ball (`PDE.DGNM.blowUp`), add `δ > 0`,
apply the Harnack inequality, undo the scaling on the essential extrema, and let `δ → 0`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Ch4GreenHarnack

open PDE MeasureTheory

variable {d : ℕ}

/-- Harnack inequality on one ball, in `ℝ≥0∞` essential extrema form. -/
theorem harnack_one_ball (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (a : CoeffField d) (V : Set (Vec d)), IsOpen V →
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn V)) →
      (∀ x ∈ V, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function V, (∀ᵐ x ∂volumeOn V, 0 ≤ u.toFun x) →
      IsWeakDivergenceFormSolutionOn a V u (0 : Vec d → ℝ) 0 →
      ∀ (y : Vec d) (s : ℝ), 0 < s → euclideanBall y (2 * s) ⊆ V →
        essSup (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (euclideanBall y s)) ≤
          ENNReal.ofReal (Real.exp (C * Real.sqrt Λ)) *
            essInf (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (euclideanBall y s)) := by
  obtain ⟨C, hC, hH⟩ := PDE.exists_harnack_constant d hd
  refine ⟨C, hC, ?_⟩
  intro Λ a V hV ha hEll u hu0 hsol y s hs hball
  have hr : 0 < 2 * s := by positivity
  have hfin : IsFiniteMeasure (volumeOn (euclideanBall (0 : Vec d) 1)) :=
    isFiniteMeasure_volumeOn_euclideanBall _ zero_le_one
  have hB : euclideanBall y s ⊆ V :=
    (euclideanBall_mono hs.le (by linarith)).trans hball
  have hposB : 0 < volume (euclideanBall y s) :=
    (isOpen_euclideanBall y s).measure_pos volume ⟨y, center_mem_euclideanBall y hs⟩
  have : NeZero (volumeOn (euclideanBall y s)) :=
    ⟨by
      intro h
      have := Measure.restrict_apply_self volume (euclideanBall y s)
      rw [show volume.restrict (euclideanBall y s) = 0 from h] at this
      simp at this; exact hposB.ne' this.symm⟩
  have hu0B : ∀ᵐ x ∂volumeOn (euclideanBall y s), 0 ≤ u.toFun x :=
    ae_restrict_of_ae_restrict_of_subset hB hu0
  set Hr := Real.exp (C * Real.sqrt Λ) with hHr
  have hHpos : 0 < Hr := Real.exp_pos _
  apply le_of_add_pos_le_mul hHpos
  intro δ hδ
  have := hfin
  set ut : H1Function (euclideanBall (0 : Vec d) 1) :=
    (DGNM.blowUp u y hr hball).addConst δ with hut
  have hutfun : ∀ z, ut.toFun z = u.toFun ((2 * s) • z + y) + δ := fun z =>
    H1Function.addConst_apply (DGNM.blowUp u y hr hball) δ z
  have hpos : ∀ᵐ z ∂volumeOn (euclideanBall (0 : Vec d) 1), 0 < ut.toFun z := by
    have h1 := DGNM.ae_blowUp_of_ae u y hr hball (P := fun t => 0 ≤ t) hu0
    filter_upwards [h1] with z hz
    rw [hutfun]
    have : 0 ≤ u.toFun ((2 * s) • z + y) := hz
    linarith
  have hsolt := DGNM.solutionOn_addConst (DGNM.solutionOn_blowUp hV hsol y hr hball) δ
  have hmeas := DGNM.blowUpCoeff_aemeasurable ha y hr hball
  have hell := DGNM.blowUpCoeff_elliptic hEll y hr hball
  have H := hH Λ _ hmeas hell ut hpos hsolt
  have e1 : (fun z => ENNReal.ofReal (ut.toFun z)) =
      fun z => (fun x => ENNReal.ofReal (u.toFun x + δ)) ((2 * s) • z + y) := funext fun z => by rw [hutfun]
  rw [e1, DGNM.essSup_comp_affineScale_ball y hr (1 / 2) (fun x => ENNReal.ofReal (u.toFun x + δ)),
    DGNM.essInf_comp_affineScale_ball y hr (1 / 2) (fun x => ENNReal.ofReal (u.toFun x + δ)),
    show 2 * s * (1 / 2) = s by ring] at H
  have hae : (fun x => ENNReal.ofReal (u.toFun x + δ)) =ᵐ[volumeOn (euclideanBall y s)]
      fun x => ENNReal.ofReal (u.toFun x) + ENNReal.ofReal δ := by
    filter_upwards [hu0B] with x hx
    exact ENNReal.ofReal_add hx hδ.le
  calc essSup (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (euclideanBall y s)) +
        ENNReal.ofReal δ
      ≤ essSup (fun x => ENNReal.ofReal (u.toFun x) + ENNReal.ofReal δ)
          (volumeOn (euclideanBall y s)) := essSup_add_const_le _ ENNReal.ofReal_ne_top
    _ = essSup (fun x => ENNReal.ofReal (u.toFun x + δ)) (volumeOn (euclideanBall y s)) :=
        (essSup_congr_ae hae).symm
    _ ≤ _ := H
    _ = ENNReal.ofReal Hr * essInf (fun x => ENNReal.ofReal (u.toFun x) + ENNReal.ofReal δ)
          (volumeOn (euclideanBall y s)) := by rw [essInf_congr_ae hae]
    _ ≤ _ := by gcongr; exact essInf_add_const_le _

end PDE.Ch4GreenHarnack
