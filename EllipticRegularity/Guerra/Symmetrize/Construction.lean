module

public import EllipticRegularity.Guerra.Symmetrize.Bounds
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# The symmetrization `S(C,p)` and its measurability
-/

@[expose] public section

open scoped BigOperators

namespace PDE.GuerraSymmetrizeProof

variable {d : ℕ}

/-- The unit vector `p / |p|`. -/
noncomputable def symE (p : Vec d) : Vec d := (Real.sqrt (vecNormSq p))⁻¹ • p

/-- `σ = e · C e`. -/
noncomputable def symσ (C : Mat d) (p : Vec d) : ℝ := vecDot (symE p) (matVecMul C (symE p))

/-- `z = C e - σ e`. -/
noncomputable def symZ (C : Mat d) (p : Vec d) : Vec d :=
  matVecMul C (symE p) - symσ C p • symE p

/-- The symmetrization. -/
noncomputable def symS (k : ℝ) (C : Mat d) (p : Vec d) : Mat d :=
  if p = 0 then Matrix.of fun i j => if i = j then k⁻¹ else 0
  else form (symσ C p) (symE p) (symZ C p)

lemma measurable_symS (k : ℝ) (i j : Fin d) :
    Measurable (fun q : (Fin d → Fin d → ℝ) × Vec d => symS k (Matrix.of q.1) q.2 i j) := by
  have hE : ∀ l, Measurable (fun q : (Fin d → Fin d → ℝ) × Vec d => symE q.2 l) := by
    intro l
    simp only [symE, vecNormSq, vecDot, Pi.smul_apply, smul_eq_mul]
    fun_prop
  have hCE : ∀ l, Measurable (fun q : (Fin d → Fin d → ℝ) × Vec d =>
      matVecMul (Matrix.of q.1) (symE q.2) l) := by
    intro l
    simp only [matVecMul, Matrix.of_apply]
    exact Finset.measurable_sum _ fun m _ => (show Measurable fun q : (Fin d → Fin d → ℝ) × Vec d => q.1 l m by fun_prop).mul (hE m)
  have hσ : Measurable (fun q : (Fin d → Fin d → ℝ) × Vec d => symσ (Matrix.of q.1) q.2) := by
    simp only [symσ, vecDot]
    exact Finset.measurable_sum _ fun m _ => (hE m).mul (hCE m)
  have hZ : ∀ l, Measurable (fun q : (Fin d → Fin d → ℝ) × Vec d =>
      symZ (Matrix.of q.1) q.2 l) := by
    intro l
    simp only [symZ, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    exact (hCE l).sub (hσ.mul (hE l))
  have hset : MeasurableSet {q : (Fin d → Fin d → ℝ) × Vec d | q.2 = 0} :=
    measurableSet_eq_fun measurable_snd measurable_const
  have hfun : (fun q : (Fin d → Fin d → ℝ) × Vec d => symS k (Matrix.of q.1) q.2 i j) =
      fun q => if q.2 = 0 then (if i = j then k⁻¹ else 0)
        else form (symσ (Matrix.of q.1) q.2) (symE q.2) (symZ (Matrix.of q.1) q.2) i j := by
    funext q
    unfold symS
    split_ifs <;> simp_all
  rw [hfun]
  refine Measurable.ite hset ?_ ?_
  · exact measurable_const
  · simp only [form, Matrix.of_apply]
    by_cases hij : i = j
    · simp only [hij, ite_true]
      have := hE j
      fun_prop
    · simp only [hij, ite_false]
      fun_prop

end PDE.GuerraSymmetrizeProof
