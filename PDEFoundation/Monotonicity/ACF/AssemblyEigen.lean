module

public import PDEFoundation.Monotonicity.Defs
public import PDEFoundation.Geometry.EuclideanBall.Topology

/-!
# ACF-A: eigenvalue bookkeeping

* `sphereDirichletEigenvalue_congr_inter`: the first Dirichlet eigenvalue only depends on
  `Ω ∩ ∂B₁`.
* `exists_degree_real`: for finite `λ`, the homogeneity exponent is `ofReal t` with
  `t ≥ 0` and `t (t + d - 2) = λ`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE

namespace ACFAssembly

noncomputable section

variable {d : ℕ}

/-- If every admissible test function for `Ω` is admissible for `Ω'`, then `λ(Ω') ≤ λ(Ω)`. -/
theorem sphereDirichletEigenvalue_le_of_transfer {Ω Ω' : Set (Vec d)}
    (h : ∀ f : Vec d → ℝ,
      closure {x | x ∈ euclideanSphere (0 : Vec d) 1 ∧ f x ≠ 0} ⊆ Ω →
        closure {x | x ∈ euclideanSphere (0 : Vec d) 1 ∧ f x ≠ 0} ⊆ Ω') :
    sphereDirichletEigenvalue d Ω' ≤ sphereDirichletEigenvalue d Ω := by
  unfold sphereDirichletEigenvalue
  refine le_iInf fun f => le_iInf fun hf => ?_
  exact iInf_le_of_le f (iInf_le_of_le ⟨hf.1, h f hf.2.1, hf.2.2⟩ le_rfl)

/-- The first Dirichlet eigenvalue only depends on `Ω ∩ ∂B₁`. -/
theorem sphereDirichletEigenvalue_congr_inter {Ω Ω' : Set (Vec d)}
    (h : Ω ∩ euclideanSphere (0 : Vec d) 1 = Ω' ∩ euclideanSphere (0 : Vec d) 1) :
    sphereDirichletEigenvalue d Ω = sphereDirichletEigenvalue d Ω' := by
  have key : ∀ {A B : Set (Vec d)},
      A ∩ euclideanSphere (0 : Vec d) 1 = B ∩ euclideanSphere (0 : Vec d) 1 →
      ∀ f : Vec d → ℝ,
      closure {x | x ∈ euclideanSphere (0 : Vec d) 1 ∧ f x ≠ 0} ⊆ A →
        closure {x | x ∈ euclideanSphere (0 : Vec d) 1 ∧ f x ≠ 0} ⊆ B := by
    intro A B hAB f hsub x hx
    have hcl : closure {x | x ∈ euclideanSphere (0 : Vec d) 1 ∧ f x ≠ 0} ⊆
        euclideanSphere (0 : Vec d) 1 :=
      closure_minimal (fun y hy => hy.1) (isClosed_euclideanSphere _ _)
    have : x ∈ A ∩ euclideanSphere (0 : Vec d) 1 := ⟨hsub hx, hcl hx⟩
    rw [hAB] at this
    exact this.1
  exact le_antisymm (sphereDirichletEigenvalue_le_of_transfer (key h.symm))
    (sphereDirichletEigenvalue_le_of_transfer (key h))

/-- For finite `λ`, the homogeneity exponent is `ofReal t` with `t ≥ 0`, `t (t + d - 2) = λ`. -/
theorem exists_degree_real (d : ℕ) {l : ℝ≥0∞} (hl : l ≠ ⊤) :
    ∃ t : ℝ, 0 ≤ t ∧ eigenvalueDegree d l = ENNReal.ofReal t ∧
      t * (t + ((d - 2 : ℕ) : ℝ)) = l.toReal := by
  set κ : ℝ := ((d - 2 : ℕ) : ℝ) with hκdef
  have hκ : 0 ≤ κ := Nat.cast_nonneg _
  set L : ℝ := l.toReal with hL
  have hL0 : 0 ≤ L := ENNReal.toReal_nonneg
  have hD : 0 ≤ κ ^ 2 + 4 * L := by positivity
  set t : ℝ := (-κ + Real.sqrt (κ ^ 2 + 4 * L)) / 2 with htdef
  have hsq : Real.sqrt (κ ^ 2 + 4 * L) ^ 2 = κ ^ 2 + 4 * L := Real.sq_sqrt hD
  have hsκ : κ ≤ Real.sqrt (κ ^ 2 + 4 * L) :=
    Real.le_sqrt_of_sq_le (by nlinarith only [hL0])
  have ht0 : 0 ≤ t := by rw [htdef]; linarith only [hsκ]
  have htL : t * (t + κ) = L := by
    rw [htdef]; nlinarith only [hsq]
  refine ⟨t, ht0, ?_, htL⟩
  have hκe : (((d - 2 : ℕ) : ℝ≥0∞)) = ENNReal.ofReal κ := (ENNReal.ofReal_natCast _).symm
  unfold eigenvalueDegree
  refine le_antisymm (sSup_le fun a ha => ?_) (le_sSup ?_)
  · have ha : a * (a + ((d - 2 : ℕ) : ℝ≥0∞)) ≤ l := ha
    have hatop : a ≠ ⊤ := by
      rintro rfl
      rw [top_add, ENNReal.top_mul_top] at ha
      exact hl (top_le_iff.mp ha)
    have ha0 : 0 ≤ a.toReal := ENNReal.toReal_nonneg
    rw [← ENNReal.ofReal_toReal hatop, hκe, ← ENNReal.ofReal_add ha0 hκ,
      ← ENNReal.ofReal_mul ha0, ← ENNReal.ofReal_toReal hl, ← hL,
      ENNReal.ofReal_le_ofReal_iff hL0] at ha
    rw [← ENNReal.ofReal_toReal hatop]
    refine ENNReal.ofReal_le_ofReal ?_
    by_contra hlt
    push Not at hlt
    nlinarith only [hlt, ha, htL, ht0, hκ]
  · show ENNReal.ofReal t * (ENNReal.ofReal t + ((d - 2 : ℕ) : ℝ≥0∞)) ≤ l
    rw [hκe, ← ENNReal.ofReal_add ht0 hκ, ← ENNReal.ofReal_mul ht0, htL, hL,
      ENNReal.ofReal_toReal hl]

end

end ACFAssembly

end PDE
