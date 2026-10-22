module

public import PDEFoundation.Analysis.Newtonian.WeakType.MollifyScalar
public import PDEFoundation.Measure.EuclideanVectorIntegral
public import Mathlib.MeasureTheory.Function.L2Space

/-!
# Mollification of bounded compactly supported vector fields

`mollVec a f` mollifies each coordinate.  For a field with `BddSupp` coordinates it is smooth and
compactly supported, linear in `f`, preserves the coordinate means, does not increase the squared
`L²` norm, and increases the `L¹` norm by at most the factor `d`.
-/

@[expose] public section

open MeasureTheory
open scoped Convolution ENNReal

namespace PDE.NewtonWeakType

noncomputable section

variable {d : ℕ}

/-- Coordinatewise whole-space mollification of a vector field. -/
def mollVec (a : ℝ) (f : Vec d → Vec d) : Vec d → Vec d :=
  fun x i => wholeSpaceMollify a (fun z => f z i) x

/-- All coordinates are measurable, bounded, and vanish outside a bounded set. -/
def VBdd (f : Vec d → Vec d) : Prop := ∀ i, BddSupp (fun z => f z i)

theorem VBdd.add {f g : Vec d → Vec d} (hf : VBdd f) (hg : VBdd g) : VBdd (fun x => f x + g x) :=
  fun i => (hf i).add (hg i)

theorem VBdd.sub {f g : Vec d → Vec d} (hf : VBdd f) (hg : VBdd g) : VBdd (fun x => f x - g x) :=
  fun i => (hf i).sub (hg i)

theorem VBdd.finsetSum {ι : Type*} (s : Finset ι) {f : ι → Vec d → Vec d}
    (hf : ∀ k ∈ s, VBdd (f k)) : VBdd (fun x => ∑ k ∈ s, f k x) := by
  intro i
  have := BddSupp.finsetSum s (f := fun k z => f k z i) (fun k hk => hf k hk i)
  convert this using 1
  funext x
  simp

theorem VBdd.exists_supp {f : Vec d → Vec d} (hf : VBdd f) :
    ∃ R, ∀ x, R ≤ ‖x‖ → f x = 0 := by
  choose R hR using fun i => (hf i).supp
  refine ⟨∑ i, |R i|, fun x hx => ?_⟩
  funext i
  have hle : R i ≤ ∑ j, |R j| := (le_abs_self (R i)).trans
    (Finset.single_le_sum (f := fun j => |R j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i))
  exact hR i x (hle.trans hx)

theorem VBdd.mollVec {a : ℝ} (ha : 0 < a) {f : Vec d → Vec d} (hf : VBdd f) :
    VBdd (mollVec a f) := fun i => bddSupp_wholeSpaceMollify ha (hf i)

theorem contDiff_mollVec {a : ℝ} (ha : 0 < a) {f : Vec d → Vec d} (hf : VBdd f) :
    ContDiff ℝ (⊤ : ℕ∞) (mollVec a f) :=
  contDiff_pi.mpr fun i => contDiff_wholeSpaceMollify ha (hf i)

theorem hasCompactSupport_mollVec {a : ℝ} (ha : 0 < a) {f : Vec d → Vec d} (hf : VBdd f) :
    HasCompactSupport (mollVec a f) := by
  obtain ⟨R, hR⟩ := (hf.mollVec ha).exists_supp
  exact HasCompactSupport.intro (isCompact_closedBall (0 : Vec d) R) fun x hx => hR x (by
    have : R < ‖x‖ := by simpa using hx
    exact this.le)

theorem mollVec_add {a : ℝ} (ha : 0 < a) {f g : Vec d → Vec d} (hf : VBdd f) (hg : VBdd g) :
    mollVec a (fun x => f x + g x) = fun x => mollVec a f x + mollVec a g x := by
  funext x i
  exact congrFun (wholeSpaceMollify_add ha (hf i) (hg i)) x

theorem mollVec_sub {a : ℝ} (ha : 0 < a) {f g : Vec d → Vec d} (hf : VBdd f) (hg : VBdd g) :
    mollVec a (fun x => f x - g x) = fun x => mollVec a f x - mollVec a g x := by
  funext x i
  exact congrFun (wholeSpaceMollify_sub ha (hf i) (hg i)) x

theorem mollVec_finsetSum {a : ℝ} (ha : 0 < a) {ι : Type*} (s : Finset ι) {f : ι → Vec d → Vec d}
    (hf : ∀ k ∈ s, VBdd (f k)) :
    mollVec a (fun x => ∑ k ∈ s, f k x) = fun x => ∑ k ∈ s, mollVec a (f k) x := by
  funext x i
  have e : (fun z => ∑ k ∈ s, f k z i) = ∑ k ∈ s, (fun z => f k z i) := by
    funext z; simp [Finset.sum_apply]
  have := congrFun (wholeSpaceMollify_finsetSum ha s (f := fun k z => f k z i)
    (fun k hk => hf k hk i)) x
  simp only [mollVec, Finset.sum_apply]
  rw [e]
  simpa [Finset.sum_apply] using this

theorem integral_mollVec_coord {a : ℝ} (ha : 0 < a) {f : Vec d → Vec d} (hf : VBdd f) (i : Fin d) :
    ∫ x, mollVec a f x i = ∫ x, f x i :=
  integral_wholeSpaceMollify ha (hf i)

theorem integral_vecNormSq_mollVec_le {a : ℝ} (ha : 0 < a) {f : Vec d → Vec d} (hf : VBdd f) :
    ∫ x, vecNormSq (mollVec a f x) ≤ ∫ x, vecNormSq (f x) := by
  simp_rw [vecNormSq_eq_sum_sq]
  show ∫ x, ∑ i, wholeSpaceMollify a (fun z => f z i) x ^ 2 ≤ _
  rw [integral_finsetSum _ fun i _ => MemLp.integrable_sq ((bddSupp_wholeSpaceMollify ha (hf i)).memLp 2),
    integral_finsetSum _ fun i _ => MemLp.integrable_sq ((hf i).memLp 2)]
  exact Finset.sum_le_sum fun i _ => integral_sq_wholeSpaceMollify_le ha (hf i)

theorem integral_vecEuclideanNorm_mollVec_le {a : ℝ} (ha : 0 < a) {f : Vec d → Vec d}
    (hf : VBdd f) :
    ∫ x, vecEuclideanNorm (mollVec a f x) ≤ d * ∫ x, vecEuclideanNorm (f x) := by
  have hi : ∀ i, Integrable (fun x => |wholeSpaceMollify a (fun z => f z i) x|) :=
    fun i => (bddSupp_wholeSpaceMollify ha (hf i)).integrable.abs
  have hfi : ∀ i, Integrable (fun x => |f x i|) := fun i => (hf i).integrable.abs
  have hn : Integrable (fun x => vecEuclideanNorm (f x)) :=
    integrable_vecEuclideanNorm_of_coord f fun i => (hf i).integrable
  have hm : Integrable (fun x => vecEuclideanNorm (mollVec a f x)) :=
    integrable_vecEuclideanNorm_of_coord _ fun i => (bddSupp_wholeSpaceMollify ha (hf i)).integrable
  calc ∫ x, vecEuclideanNorm (mollVec a f x)
      ≤ ∫ x, ∑ i : Fin d, |wholeSpaceMollify a (fun z => f z i) x| :=
        integral_mono hm (integrable_finsetSum _ fun i _ => hi i)
          fun x => vecEuclideanNorm_le_sum_abs _
    _ = ∑ i : Fin d, ∫ x, |wholeSpaceMollify a (fun z => f z i) x| :=
        integral_finsetSum _ fun i _ => hi i
    _ ≤ ∑ i : Fin d, ∫ x, |f x i| :=
        Finset.sum_le_sum fun i _ => integral_abs_wholeSpaceMollify_le ha (hf i)
    _ ≤ ∑ _i : Fin d, ∫ x, vecEuclideanNorm (f x) :=
        Finset.sum_le_sum fun i _ => integral_mono (hfi i) hn fun x => abs_apply_le_vecEuclideanNorm _ _
    _ = d * ∫ x, vecEuclideanNorm (f x) := by simp

/-- Support of the mollification in a Euclidean ball. -/
theorem mollVec_eq_zero_of_support {a : ℝ} (ha : 0 < a) {f : Vec d → Vec d} {c : Vec d} {r : ℝ}
    (hsupp : ∀ y, r < vecEuclideanNorm (y - c) → f y = 0)
    {x : Vec d} (hx : r + Real.sqrt d * a < vecEuclideanNorm (x - c)) :
    mollVec a f x = 0 := by
  funext i
  refine wholeSpaceMollify_eq_zero ha fun t ht => ?_
  have h1 : vecEuclideanNorm t ≤ Real.sqrt d * a :=
    (vecEuclideanNorm_le_sqrt_natCast_mul_norm t).trans
      (mul_le_mul_of_nonneg_left ht (Real.sqrt_nonneg _))
  have h2 : vecEuclideanNorm (x - c) ≤ vecEuclideanNorm (x - t - c) + vecEuclideanNorm t := by
    have := vecEuclideanNorm_add_le (x - t - c) t
    simpa [sub_add_cancel, sub_right_comm] using this
  have h3 : f (x - t) = 0 := hsupp _ (by
    have : x - t - c = (x - t) - c := rfl
    linarith)
  simp [h3]

end

end PDE.NewtonWeakType
