module

public import PDEFoundation.Monotonicity.Poon.Differentiate

/-!
# Gaussian-tame functions for the Poon identities

`PDom a f` says that `f` is continuous and bounded by `K (1 + |x|²)^k exp (a |x|²)`.  The class is
closed under sums, products (exponents add), finite sums and multiplication by polynomials, and a
function in `PDom (A' + A')` is integrable against the heat kernel as soon as the weights
`(1 + |x|²)^k exp (2 A' |x|²) Φ(s, x)` are integrable.
-/

@[expose] public section

open MeasureTheory

namespace PDE

noncomputable section

variable {d : ℕ}

/-- Continuous with polynomial-times-`exp (a |x|²)` growth. -/
def PDom (a : ℝ) (f : Vec d → ℝ) : Prop :=
  Continuous f ∧ ∃ K : ℝ, ∃ k : ℕ, 0 ≤ K ∧ ∀ x, |f x| ≤ K * (1 + vecNormSq x) ^ k * Real.exp (a * vecNormSq x)

theorem PDom.continuous {a : ℝ} {f : Vec d → ℝ} (h : PDom a f) : Continuous f := h.1

theorem one_le_one_add_vecNormSq (x : Vec d) : 1 ≤ 1 + vecNormSq x := by
  have := vecNormSq_nonneg x
  linarith

theorem PDom.add {a : ℝ} {f g : Vec d → ℝ} (hf : PDom a f) (hg : PDom a g) :
    PDom a (fun x => f x + g x) := by
  obtain ⟨hfc, K1, k1, hK1, h1⟩ := hf
  obtain ⟨hgc, K2, k2, hK2, h2⟩ := hg
  refine ⟨hfc.add hgc, K1 + K2, max k1 k2, by positivity, fun x => ?_⟩
  have hP := one_le_one_add_vecNormSq x
  have hE := Real.exp_pos (a * vecNormSq x)
  have p1 : (1 + vecNormSq x) ^ k1 ≤ (1 + vecNormSq x) ^ max k1 k2 :=
    pow_le_pow_right₀ hP (le_max_left _ _)
  have p2 : (1 + vecNormSq x) ^ k2 ≤ (1 + vecNormSq x) ^ max k1 k2 :=
    pow_le_pow_right₀ hP (le_max_right _ _)
  calc |f x + g x| ≤ |f x| + |g x| := abs_add_le _ _
    _ ≤ K1 * (1 + vecNormSq x) ^ k1 * Real.exp (a * vecNormSq x) +
        K2 * (1 + vecNormSq x) ^ k2 * Real.exp (a * vecNormSq x) := add_le_add (h1 x) (h2 x)
    _ ≤ K1 * (1 + vecNormSq x) ^ max k1 k2 * Real.exp (a * vecNormSq x) +
        K2 * (1 + vecNormSq x) ^ max k1 k2 * Real.exp (a * vecNormSq x) := by gcongr
    _ = (K1 + K2) * (1 + vecNormSq x) ^ max k1 k2 * Real.exp (a * vecNormSq x) := by ring

theorem PDom.const_mul {a : ℝ} {f : Vec d → ℝ} (c : ℝ) (hf : PDom a f) :
    PDom a (fun x => c * f x) := by
  obtain ⟨hfc, K, k, hK, h⟩ := hf
  refine ⟨hfc.const_mul c, |c| * K, k, by positivity, fun x => ?_⟩
  rw [abs_mul]
  calc |c| * |f x| ≤ |c| * (K * (1 + vecNormSq x) ^ k * Real.exp (a * vecNormSq x)) := by
        gcongr; exact h x
    _ = _ := by ring

theorem PDom.neg {a : ℝ} {f : Vec d → ℝ} (hf : PDom a f) : PDom a (fun x => -f x) := by
  simpa using hf.const_mul (-1)

theorem PDom.sub {a : ℝ} {f g : Vec d → ℝ} (hf : PDom a f) (hg : PDom a g) :
    PDom a (fun x => f x - g x) := by
  simpa [sub_eq_add_neg] using hf.add hg.neg

theorem PDom.mul {a b : ℝ} {f g : Vec d → ℝ} (hf : PDom a f) (hg : PDom b g) :
    PDom (a + b) (fun x => f x * g x) := by
  obtain ⟨hfc, K1, k1, hK1, h1⟩ := hf
  obtain ⟨hgc, K2, k2, hK2, h2⟩ := hg
  refine ⟨hfc.mul hgc, K1 * K2, k1 + k2, by positivity, fun x => ?_⟩
  have e : Real.exp ((a + b) * vecNormSq x) =
      Real.exp (a * vecNormSq x) * Real.exp (b * vecNormSq x) := by
    rw [← Real.exp_add]; ring_nf
  rw [abs_mul, e, pow_add]
  calc |f x| * |g x| ≤ (K1 * (1 + vecNormSq x) ^ k1 * Real.exp (a * vecNormSq x)) *
        (K2 * (1 + vecNormSq x) ^ k2 * Real.exp (b * vecNormSq x)) :=
        mul_le_mul (h1 x) (h2 x) (abs_nonneg _) (by
          have := (abs_nonneg (f x)).trans (h1 x); exact this)
    _ = _ := by ring

theorem PDom.mul_poly {a : ℝ} {f g : Vec d → ℝ} (hf : PDom a f) (hg : PDom 0 g) :
    PDom a (fun x => f x * g x) := by
  simpa using hf.mul hg

theorem PDom.mul_poly' {a : ℝ} {f g : Vec d → ℝ} (hg : PDom 0 g) (hf : PDom a f) :
    PDom a (fun x => g x * f x) := by
  simpa using hg.mul hf

theorem PDom.congr {a : ℝ} {f g : Vec d → ℝ} (h : ∀ x, f x = g x) (hf : PDom a f) : PDom a g := by
  have : f = g := funext h
  exact this ▸ hf

theorem PDom.zero (a : ℝ) : PDom a (fun _ : Vec d => (0 : ℝ)) :=
  ⟨continuous_const, 0, 0, le_refl _, fun x => by simp⟩

theorem PDom.sum {ι : Type*} {a : ℝ} (s : Finset ι) (f : ι → Vec d → ℝ)
    (h : ∀ i ∈ s, PDom a (f i)) : PDom a (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using PDom.zero a
  | insert i s hi ih =>
    have := (h i (Finset.mem_insert_self i s)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
    simpa [Finset.sum_insert hi] using this

theorem PDom.const (c : ℝ) : PDom (0 : ℝ) (fun _ : Vec d => c) := by
  refine ⟨continuous_const, |c|, 0, abs_nonneg _, fun x => ?_⟩
  simp

theorem PDom.coord (i : Fin d) : PDom (0 : ℝ) (fun x : Vec d => x i) := by
  refine ⟨continuous_apply i, 1, 1, zero_le_one, fun x => ?_⟩
  have h := sq_apply_le_vecNormSq x i
  simp only [zero_mul, Real.exp_zero, mul_one, one_mul, pow_one]
  nlinarith [abs_nonneg (x i), sq_abs (x i), sq_nonneg (|x i| - 1)]

theorem PDom.normSq : PDom (0 : ℝ) (fun x : Vec d => vecNormSq x) := by
  refine ⟨?_, 1, 1, zero_le_one, fun x => ?_⟩
  · exact contDiff_vecNormSq.continuous
  · have := vecNormSq_nonneg x
    simp only [zero_mul, Real.exp_zero, mul_one, one_mul, pow_one]
    rw [abs_of_nonneg this]; linarith

/-- Integrability of the weights `(1 + |x|²)^k exp (2 A' |x|²) Φ(s, x)`. -/
def WeightInt (d : ℕ) (s A' : ℝ) : Prop :=
  ∀ k : ℕ, Integrable (fun x : Vec d =>
    (1 + vecNormSq x) ^ k * (Real.exp ((A' + A') * vecNormSq x) * heatKernel d s x)) volume

theorem PDom.integrable_mul_heatKernel {s A' : ℝ} (hs : 0 < s) (hw : WeightInt d s A')
    {f : Vec d → ℝ} (hf : PDom (A' + A') f) :
    Integrable (fun x => f x * heatKernel d s x) volume := by
  obtain ⟨hfc, K, k, hK, h⟩ := hf
  refine Integrable.mono' ((hw k).const_mul K)
    (hfc.mul continuous_heatKernel_space).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => ?_)
  have hΦ := heatKernel_pos d hs x
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hΦ]
  calc |f x| * heatKernel d s x
      ≤ (K * (1 + vecNormSq x) ^ k * Real.exp ((A' + A') * vecNormSq x)) * heatKernel d s x :=
        mul_le_mul_of_nonneg_right (h x) hΦ.le
    _ = _ := by ring

end

end PDE
