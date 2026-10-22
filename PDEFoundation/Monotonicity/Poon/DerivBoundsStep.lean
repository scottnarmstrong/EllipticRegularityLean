module

public import PDEFoundation.Monotonicity.Poon.BernsteinRules
public import PDEFoundation.Ambient.EuclideanNorm
public import Mathlib.Analysis.Complex.Exponential
public import PDEFoundation.Monotonicity.Poon.BernsteinBridge
import PDEFoundation.Monotonicity.Poon.Bernstein

/-!
# One step of the interior derivative estimate with Gaussian growth

If `g` is caloric and smooth on the slab `(a, b) × ℝᵈ` and `|g(t,x)| ≤ C exp (A |x|²)` for
`t ∈ [t₁, t₂] ⊂ (a, b)`, then for every `A' > A` and `ρ > 0` the spatial gradient satisfies
`|∇g(t,x)| ≤ C' exp (A' |x|²)` for `t ∈ [t₁ + ρ², t₂]`.  The constant depends only on
`d, A, A', C, ρ`.  The argument is the Bernstein estimate on the cylinder of radius `ρ` ending at
`(t, x)`, and the cross term `A (|y|² - |x|²)` over the cylinder is absorbed.
-/

@[expose] public section

open Set Filter

namespace PDE

noncomputable section

variable {d : ℕ}

/-- Two-sided comparison of squared norms of nearby points. -/
theorem abs_vecNormSq_sub_le {x y : Vec d} {η : ℝ} (hη : 0 < η) :
    |vecNormSq y - vecNormSq x| ≤ η * vecNormSq x + (1 + η⁻¹) * vecNormSq (y - x) := by
  have key : ∀ a b : ℝ, |(a + b) ^ 2 - a ^ 2| ≤ η * a ^ 2 + (1 + η⁻¹) * b ^ 2 := by
    intro a b
    have hk : 0 ≤ η⁻¹ := inv_nonneg.2 hη.le
    have e1 : η⁻¹ * (η * a - b) ^ 2 = η * a ^ 2 - 2 * a * b + η⁻¹ * b ^ 2 := by
      field_simp
      ring
    have e2 : η⁻¹ * (η * a + b) ^ 2 = η * a ^ 2 + 2 * a * b + η⁻¹ * b ^ 2 := by
      field_simp
      ring
    have h1 := mul_nonneg hk (sq_nonneg (η * a - b))
    have h2 := mul_nonneg hk (sq_nonneg (η * a + b))
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg b]
  have hy : y = x + (y - x) := by abel
  rw [vecNormSq_eq_sum_sq, vecNormSq_eq_sum_sq, vecNormSq_eq_sum_sq, ← Finset.sum_sub_distrib,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  have := key (x i) ((y - x) i)
  have e : x i + (y - x) i = y i := by simp
  rw [e] at this
  exact this

/-- The slab `(a, b) × ℝᵈ`. -/
abbrev slab (d : ℕ) (a b : ℝ) : Set (ℝ × Vec d) := Ioo a b ×ˢ univ

theorem isOpen_slab (a b : ℝ) : IsOpen (slab d a b) := isOpen_Ioo.prod isOpen_univ

/-- Caloric and `C^∞` on the slab. -/
def CaloricOn (a b : ℝ) (g : ℝ × Vec d → ℝ) : Prop :=
  JSm (slab d a b) g ∧ EqOn (jEt g) (jLap g) (slab d a b)

theorem CaloricOn.jEx {a b : ℝ} {g : ℝ × Vec d → ℝ} (h : CaloricOn a b g) (i : Fin d) :
    CaloricOn a b (jEx i g) :=
  ⟨h.1.jEx (isOpen_slab a b) i, fun _ hp => jEt_jEx_eq_jLap (isOpen_slab a b) h.1 h.2 i hp⟩

/-- Gaussian growth of `g` on the time interval `[t₁, t₂]`. -/
def Grow (g : ℝ × Vec d → ℝ) (t₁ t₂ A C : ℝ) : Prop :=
  ∀ t ∈ Icc t₁ t₂, ∀ x : Vec d, |g (t, x)| ≤ C * Real.exp (A * vecNormSq x)

theorem Grow.mono {g : ℝ × Vec d → ℝ} {t₁ t₂ s₁ s₂ A C : ℝ} (h : Grow g t₁ t₂ A C)
    (h1 : t₁ ≤ s₁) (h2 : s₂ ≤ t₂) : Grow g s₁ s₂ A C :=
  fun t ht x => h t ⟨h1.trans ht.1, ht.2.trans h2⟩ x

/-- Bernstein step: gradient bound with the same Gaussian weight at a slightly larger exponent. -/
theorem grad_growth_step {a b : ℝ} {t₁ t₂ A A' C ρ : ℝ} (hsub : Icc t₁ t₂ ⊆ Ioo a b)
    (hρ : 0 < ρ) (hC : 0 ≤ C) (hAA : A < A') :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ g : ℝ × Vec d → ℝ, CaloricOn a b g → Grow g t₁ t₂ A C →
      ∀ t ∈ Icc (t₁ + ρ ^ 2) t₂, ∀ x : Vec d,
        vecEuclideanNorm (classicalGradient (fun y => g (t, y)) x) ≤
          C' * Real.exp (A' * vecNormSq x) := by
  set η : ℝ := (A' - A) / (|A| + 1) with hη
  have hA1 : 0 < |A| + 1 := by positivity
  have hη0 : 0 < η := div_pos (by linarith) hA1
  have hAη : |A| * η ≤ A' - A := by
    rw [hη, mul_div_assoc', div_le_iff₀ hA1]
    nlinarith [abs_nonneg A]
  set K : ℝ := Real.exp (|A| * ((1 + η⁻¹) * ρ ^ 2)) with hK
  refine ⟨(5 + (d : ℝ)) / ρ * (C * K), by positivity, fun g hg hgrow t ht x => ?_⟩
  have hΩ := isOpen_slab (d := d) a b
  have hcyl : Icc (t - ρ ^ 2) (t - ρ ^ 2 + ρ ^ 2) ×ˢ euclideanClosedBall x ρ ⊆ slab d a b := by
    intro p hp
    have h1 : t₁ ≤ p.1 := by linarith [hp.1.1, ht.1]
    have h2 : p.1 ≤ t₂ := by linarith [hp.1.2, ht.2]
    exact ⟨hsub ⟨h1, h2⟩, mem_univ _⟩
  have hX := vecNormSq_nonneg x
  have hM : ∀ s ∈ Icc (t - ρ ^ 2) (t - ρ ^ 2 + ρ ^ 2), ∀ y ∈ euclideanClosedBall x ρ,
      |g (s, y)| ≤ C * K * Real.exp (A' * vecNormSq x) := by
    intro s hs y hy
    have hs' : s ∈ Icc t₁ t₂ := ⟨by linarith [hs.1, ht.1], by linarith [hs.2, ht.2]⟩
    have hy' : vecNormSq (y - x) ≤ ρ ^ 2 := hy
    have hd := abs_vecNormSq_sub_le (x := x) (y := y) hη0
    have hR : η * vecNormSq x + (1 + η⁻¹) * vecNormSq (y - x) ≤
        η * vecNormSq x + (1 + η⁻¹) * ρ ^ 2 :=
      add_le_add_right (mul_le_mul_of_nonneg_left hy' (by positivity)) _
    have h3 : A * (vecNormSq y - vecNormSq x) ≤ |A| * (η * vecNormSq x + (1 + η⁻¹) * ρ ^ 2) :=
      calc A * (vecNormSq y - vecNormSq x) ≤ |A * (vecNormSq y - vecNormSq x)| := le_abs_self _
        _ = |A| * |vecNormSq y - vecNormSq x| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_left (hd.trans hR) (abs_nonneg A)
    have h4 : |A| * η * vecNormSq x ≤ (A' - A) * vecNormSq x :=
      mul_le_mul_of_nonneg_right hAη hX
    have h5 : A * vecNormSq y ≤ A' * vecNormSq x + |A| * ((1 + η⁻¹) * ρ ^ 2) := by
      have : |A| * (η * vecNormSq x + (1 + η⁻¹) * ρ ^ 2) =
          |A| * η * vecNormSq x + |A| * ((1 + η⁻¹) * ρ ^ 2) := by ring
      linarith
    calc |g (s, y)| ≤ C * Real.exp (A * vecNormSq y) := hgrow s hs' y
      _ ≤ C * Real.exp (A' * vecNormSq x + |A| * ((1 + η⁻¹) * ρ ^ 2)) :=
          mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 h5) hC
      _ = C * K * Real.exp (A' * vecNormSq x) := by
          rw [Real.exp_add, hK]; ring
  have hheat : ∀ s : ℝ, ∀ y : Vec d, (s, y) ∈ slab d a b →
      deriv (fun τ : ℝ => (fun τ y => g (τ, y)) τ y) s =
        euclideanCoordLaplacian ((fun τ y => g (τ, y)) s) y := by
    intro s y hp
    have h1 := deriv_slice_time (g := g) (hg.1.differentiableAt hΩ hp)
    have h2 := euclideanCoordLaplacian_slice hΩ hg.1 hp
    change deriv (fun τ : ℝ => g (τ, y)) s = euclideanCoordLaplacian (fun z : Vec d => g (s, z)) y
    rw [h1, h2]
    exact hg.2 hp
  have hB := bernstein_gradient_estimate (fun τ y => g (τ, y)) hΩ hg.1 hheat hρ hcyl hM
  rw [sub_add_cancel] at hB
  refine hB.trans (le_of_eq ?_)
  ring

end

end PDE
