module

public import PDEFoundation.Analysis.Gehring.WhitneyFamilyExists
public import PDEFoundation.Analysis.Gehring.WeakRefined
public import PDEFoundation.Analysis.Gehring.LebesgueDiff

/-!
# The Gehring tail estimate: constants and the per-cube reverse Hölder step

Constants `H = (9/2)^(d+1)`, `D_d = 2 · 3^d · H`, `G = 4 (d+1) 3^d H`, `N_σ = 3 (σ+1)^d`
and the reverse Hölder predicate `GehringRH`, with the estimate on a single Whitney cube.
-/

@[expose] public section

namespace PDE.Gehring

open MeasureTheory Set
open scoped ENNReal

variable {d : ℕ}

/-- The constant `D_d = 2 · 3^d · H` of the tail estimate. -/
noncomputable def gehringD (d : ℕ) : ℝ := 2 * 3 ^ d * gehringH d

/-- The constant `G = 4 (d+1) 3^d H` controlling the absorption. -/
noncomputable def gehringG (d : ℕ) : ℝ := 4 * ((d : ℝ) + 1) * 3 ^ d * gehringH d

/-- The overlap constant `N_σ = 3 (σ+1)^d`. -/
noncomputable def gehringN (σ : ℝ) (d : ℕ) : ℝ := 3 * (σ + 1) ^ d

/-- The reverse Hölder inequality (4.27) on the cube of center `z` and half-side `r`,
in exactly the form of the statement `exists_gehring_constant`. -/
def GehringRH (d : ℕ) (σ A B : ℝ) (g h : Vec d → ℝ) (z : Vec d) (r : ℝ) : Prop :=
  ∫ x in centeredAxisCube z r, g x ≤
    A * (volume (centeredAxisCube z r)).toReal *
        (integralAverage (centeredAxisCube z (σ * r))
          (fun x => g x ^ ((d : ℝ) / ((d : ℝ) + 1)))) ^ (((d : ℝ) + 1) / (d : ℝ)) +
      B * ∫ x in centeredAxisCube z (σ * r), h x

theorem gehringH_pos (d : ℕ) : 0 < gehringH d := by unfold gehringH; positivity

theorem one_le_gehringH (d : ℕ) : 1 ≤ gehringH d := by
  unfold gehringH
  exact one_le_pow₀ (by norm_num)

theorem isCompact_closedCenteredAxisCube' (c : Vec d) (r : ℝ) :
    IsCompact (closedCenteredAxisCube c r) :=
  isCompact_univ_pi fun _ => isCompact_Icc

theorem centeredAxisCube_subset_closed (c : Vec d) (r : ℝ) :
    centeredAxisCube c r ⊆ closedCenteredAxisCube c r :=
  fun _ hx i hi => ⟨(hx i hi).1.le, (hx i hi).2.le⟩

/-- `ofReal` of a set integral of a nonnegative integrable function is the lintegral. -/
theorem ofReal_setIntegral_eq {f : Vec d → ℝ} {S : Set (Vec d)} (hf0 : ∀ x, 0 ≤ f x)
    (hf : IntegrableOn f S volume) :
    ENNReal.ofReal (∫ x in S, f x) = ∫⁻ x in S, ENNReal.ofReal (f x) :=
  ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall hf0)

/-- **Per-cube step** of the tail estimate. On a cube `Q` of center `c` and side `ℓ` whose
dilate satisfies the Whitney averaging bound and for which the reverse Hölder inequality holds,
`∫_Q g ≤ A H t |Q| + B ∫_{σQ} h` (in `ℝ≥0∞`). -/
theorem lintegral_cube_le_of_rh {g h : Vec d → ℝ} (hg0 : ∀ x, 0 ≤ g x)
    (hh0 : ∀ x, 0 ≤ h x) (hg : Integrable g volume) (hh : LocallyIntegrable h volume)
    {σ A B t : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (ht : 0 ≤ t) (c : Vec d) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (hav : (integralAverage (centeredAxisCube c (σ * ℓ / 2))
        (fun x => g x ^ gehringTheta d)) ^ (((d : ℝ) + 1) / d) ≤ gehringH d * t)
    (hrh : GehringRH d σ A B g h c (ℓ / 2)) :
    ∫⁻ x in centeredAxisCube c (ℓ / 2), ENNReal.ofReal (g x) ≤
      ENNReal.ofReal (A * gehringH d * t) * volume (centeredAxisCube c (ℓ / 2)) +
        ENNReal.ofReal B * ∫⁻ x in centeredAxisCube c (σ * (ℓ / 2)), ENNReal.ofReal (h x) := by
  have hℓ2 : 0 < ℓ / 2 := by positivity
  have hvfin := volume_centeredAxisCube_ne_top c (ℓ / 2)
  have hS : σ * (ℓ / 2) = σ * ℓ / 2 := by ring
  have hhS : IntegrableOn h (centeredAxisCube c (σ * (ℓ / 2))) volume :=
    (hh.integrableOn_isCompact (isCompact_closedCenteredAxisCube' c (σ * (ℓ / 2)))).mono_set
      (centeredAxisCube_subset_closed _ _)
  rw [← ofReal_setIntegral_eq hg0 hg.integrableOn, ← ofReal_setIntegral_eq hh0 hhS]
  have havm : 0 ≤ (integralAverage (centeredAxisCube c (σ * ℓ / 2))
        (fun x => g x ^ gehringTheta d)) := by
    refine integralAverage_nonneg (isOpen_centeredAxisCube _ _).measurableSet fun x _ => ?_
    exact Real.rpow_nonneg (hg0 x) _
  have h1 : 0 ≤ ∫ x in centeredAxisCube c (σ * (ℓ / 2)), h x := setIntegral_nonneg
    (isOpen_centeredAxisCube _ _).measurableSet fun x _ => hh0 x
  unfold GehringRH at hrh
  rw [hS] at hrh
  have hA'' : A * (volume (centeredAxisCube c (ℓ / 2))).toReal *
      (integralAverage (centeredAxisCube c (σ * ℓ / 2))
        (fun x => g x ^ ((d : ℝ) / ((d : ℝ) + 1)))) ^ (((d : ℝ) + 1) / (d : ℝ)) ≤
      A * (volume (centeredAxisCube c (ℓ / 2))).toReal * (gehringH d * t) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact hav
  have hH := gehringH_pos d
  calc ENNReal.ofReal (∫ x in centeredAxisCube c (ℓ / 2), g x)
      ≤ ENNReal.ofReal (A * (volume (centeredAxisCube c (ℓ / 2))).toReal * (gehringH d * t) +
          B * ∫ x in centeredAxisCube c (σ * (ℓ / 2)), h x) := by
        refine ENNReal.ofReal_le_ofReal (hrh.trans ?_)
        rw [hS] at h1 ⊢
        linarith
    _ = ENNReal.ofReal (A * gehringH d * t) * volume (centeredAxisCube c (ℓ / 2)) +
          ENNReal.ofReal B * ENNReal.ofReal (∫ x in centeredAxisCube c (σ * (ℓ / 2)), h x) := by
        rw [ENNReal.ofReal_add (by positivity) (mul_nonneg hB h1), ENNReal.ofReal_mul hB]
        congr 1
        rw [show A * (volume (centeredAxisCube c (ℓ / 2))).toReal * (gehringH d * t) =
          (A * gehringH d * t) * (volume (centeredAxisCube c (ℓ / 2))).toReal by ring,
          ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_toReal hvfin]

end PDE.Gehring
