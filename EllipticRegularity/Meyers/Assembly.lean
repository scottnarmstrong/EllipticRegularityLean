module

public import PDEFoundation.PDE.WeakDivergenceForm
public import PDEFoundation.Sobolev.H1.ZeroBoundary
public import PDEFoundation.Sobolev.H1.MeanEnergyOperator
public import PDEFoundation.Measure.NormalizedLp
public import PDEFoundation.Measure.BallVolume
public import PDEFoundation.Geometry.AxisBox
public import PDEFoundation.Geometry.EuclideanBall

/-!
# Assembly of the Meyers estimate: constants and the interior estimate

The Gehring lemma and the reverse Hölder
inequalities are taken as explicit interface hypotheses (`GehringConclusion`,
`MeyersRHInterior`, `MeyersRHBoundary`); this file proves the constant
bookkeeping, the energy-density bounds, the conversion between
`eLpMeanNormOn` of `w` and of `g = w ^ 2`, and the interior clause of the
Meyers estimate.
-/

@[expose] public section

open scoped ENNReal

namespace PDE

open MeasureTheory

namespace MeyersAssembly

/-- The body of the statement `exists_gehring_constant d hd` for a fixed
constant `C`. -/
def GehringWith (d : ℕ) (C : ℝ) : Prop :=
      ∀ (σ : ℝ), (σ = 2 ∨ σ = 4) →
      ∀ (A B ε : ℝ), 1 ≤ A → 0 ≤ B → 0 < ε → ε ≤ 1 / (C * A) →
      ∀ g h : Vec d → ℝ, (∀ x, 0 ≤ g x) → (∀ x, 0 ≤ h x) →
        ((Integrable g volume ∧ HasCompactSupport g ∧
            MemLp h (ENNReal.ofReal (1 + ε)) volume ∧
            ∀ (z : Vec d) (r : ℝ), 0 < r →
              ∫ x in centeredAxisCube z r, g x ≤
                A * (volume (centeredAxisCube z r)).toReal *
                    (integralAverage (centeredAxisCube z (σ * r))
                      (fun x => g x ^ ((d : ℝ) / ((d : ℝ) + 1)))) ^
                        (((d : ℝ) + 1) / (d : ℝ)) +
                  B * ∫ x in centeredAxisCube z (σ * r), h x) →
          eLpNorm g (ENNReal.ofReal (1 + ε)) volume ≤
            ENNReal.ofReal (C * B) *
              eLpNorm h (ENNReal.ofReal (1 + ε)) volume) ∧
        ((IntegrableOn g (euclideanBall (0 : Vec d) 1) volume ∧
            MemLp h (ENNReal.ofReal (1 + ε))
              (volumeOn (euclideanBall (0 : Vec d) 1)) ∧
            ∀ (z : Vec d) (r : ℝ), 0 < r →
              centeredAxisCube z (σ * r) ⊆ euclideanBall (0 : Vec d) 1 →
              ∫ x in centeredAxisCube z r, g x ≤
                A * (volume (centeredAxisCube z r)).toReal *
                    (integralAverage (centeredAxisCube z (σ * r))
                      (fun x => g x ^ ((d : ℝ) / ((d : ℝ) + 1)))) ^
                        (((d : ℝ) + 1) / (d : ℝ)) +
                  B * ∫ x in centeredAxisCube z (σ * r), h x) →
          eLpMeanNormOn (euclideanBall (0 : Vec d) (1 / 2))
              (ENNReal.ofReal (1 + ε)) g ≤
            ENNReal.ofReal (C * integralAverage (euclideanBall (0 : Vec d) 1) g) +
              ENNReal.ofReal (C * B) *
                eLpMeanNormOn (euclideanBall (0 : Vec d) 1)
                  (ENNReal.ofReal (1 + ε)) h)

/-- The conclusion of the statement `exists_gehring_constant d hd`,
stated as a `Prop` so that it can be taken as a hypothesis. -/
def GehringConclusion (d : ℕ) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ GehringWith d C

/-- Interface (RHI) for a fixed constant `C₀`: the interior reverse Hölder inequality of Lemma 4.5(i), with `w = (∇u · a ∇u)^{1/2}`, `g = w ^ 2`, `h = |f| ^ 2`,
`θ = d / (d + 1)` and `2Q = centeredAxisCube z (2 * r)`. -/
def MeyersRHInteriorWith (d : ℕ) (C₀ : ℝ) : Prop :=
    ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d,
        AEMeasurable (fun x => a x i j)
          (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ (f : Vec d → Vec d),
        (∀ i : Fin d,
          AEStronglyMeasurable (fun x => f x i)
            (volumeOn (euclideanBall (0 : Vec d) 1))) →
        MemLp (fun x => vecEuclideanNorm (f x)) 2
          (volumeOn (euclideanBall (0 : Vec d) 1)) →
        ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
        IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u
            (0 : Vec d → ℝ) f →
        ∀ (z : Vec d) (r : ℝ), 0 < r →
          centeredAxisCube z (2 * r) ⊆ euclideanBall (0 : Vec d) 1 →
          ∫ x in centeredAxisCube z r,
              Real.sqrt (vecDot (u.grad x) (matVecMul (a x) (u.grad x))) ^ 2 ≤
            (C₀ * Real.sqrt Λ) * (volume (centeredAxisCube z r)).toReal *
                (integralAverage (centeredAxisCube z (2 * r))
                  (fun x => (Real.sqrt (vecDot (u.grad x)
                      (matVecMul (a x) (u.grad x))) ^ 2) ^
                    ((d : ℝ) / ((d : ℝ) + 1)))) ^ (((d : ℝ) + 1) / (d : ℝ)) +
              C₀ * ∫ x in centeredAxisCube z (2 * r),
                vecEuclideanNorm (f x) ^ 2

/-- Interface (RHI): the interior reverse Hölder inequality with some
constant `C₀ ≥ 1` depending only on `d`. -/
def MeyersRHInterior (d : ℕ) : Prop :=
  ∃ C₀ : ℝ, 1 ≤ C₀ ∧ MeyersRHInteriorWith d C₀

/-- Interface (RHB) for a fixed constant `C₀`: the boundary reverse Hölder inequality of Lemma 4.5(ii), for `u ∈ H¹₀(B₁)` with `w` and `h = |f|²` extended by zero
outside `B₁`, valid for every cube (`4Q = centeredAxisCube z (4 * r)`). -/
def MeyersRHBoundaryWith (d : ℕ) (C₀ : ℝ) : Prop :=
    ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d,
        AEMeasurable (fun x => a x i j)
          (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ (f : Vec d → Vec d),
        (∀ i : Fin d,
          AEStronglyMeasurable (fun x => f x i)
            (volumeOn (euclideanBall (0 : Vec d) 1))) →
        MemLp (fun x => vecEuclideanNorm (f x)) 2
          (volumeOn (euclideanBall (0 : Vec d) 1)) →
        ∀ u : H10Function (euclideanBall (0 : Vec d) 1),
        IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1)
            u.toH1Function (0 : Vec d → ℝ) f →
        ∀ (z : Vec d) (r : ℝ), 0 < r →
          ∫ x in centeredAxisCube z r,
              (euclideanBall (0 : Vec d) 1).indicator (fun y =>
                Real.sqrt (vecDot (u.grad y) (matVecMul (a y) (u.grad y))) ^ 2) x ≤
            (C₀ * Real.sqrt Λ) * (volume (centeredAxisCube z r)).toReal *
                (integralAverage (centeredAxisCube z (4 * r))
                  (fun x => ((euclideanBall (0 : Vec d) 1).indicator (fun y =>
                      Real.sqrt (vecDot (u.grad y) (matVecMul (a y) (u.grad y))) ^ 2) x) ^
                    ((d : ℝ) / ((d : ℝ) + 1)))) ^ (((d : ℝ) + 1) / (d : ℝ)) +
              C₀ * ∫ x in centeredAxisCube z (4 * r),
                (euclideanBall (0 : Vec d) 1).indicator
                  (fun y => vecEuclideanNorm (f y) ^ 2) x

/-- Interface (RHB): the boundary reverse Hölder inequality with some
constant `C₀ ≥ 1` depending only on `d`. -/
def MeyersRHBoundary (d : ℕ) : Prop :=
  ∃ C₀ : ℝ, 1 ≤ C₀ ∧ MeyersRHBoundaryWith d C₀


variable {d : ℕ}

section Constants

/-- Constant bookkeeping (Theorem 4.4): with `c = 2 / (C₁ C₀)`, the
condition `p ≤ 2 + c / √Λ` gives `ε = (p - 2) / 2 ≤ 1 / (C₁ A)` for
`A = C₀ √Λ ≥ 1`. -/
theorem epsilon_le_of_le_exponent {C₁ C₀ Λ p : ℝ} (hC₁ : 1 ≤ C₁) (hC₀ : 1 ≤ C₀)
    (hΛ : 1 ≤ Λ) (hp : p ≤ 2 + (2 / (C₁ * C₀)) / Real.sqrt Λ) :
    (p - 2) / 2 ≤ 1 / (C₁ * (C₀ * Real.sqrt Λ)) ∧ 1 ≤ C₀ * Real.sqrt Λ := by
  have hs : 1 ≤ Real.sqrt Λ := by
    simpa using Real.sqrt_le_sqrt hΛ
  have hC₁0 : 0 < C₁ := by linarith
  have hC₀0 : 0 < C₀ := by linarith
  refine ⟨?_, by nlinarith⟩
  have h1 : (p - 2) / 2 ≤ ((2 / (C₁ * C₀)) / Real.sqrt Λ) / 2 := by linarith
  have h2 : ((2 / (C₁ * C₀)) / Real.sqrt Λ) / 2 = 1 / (C₁ * (C₀ * Real.sqrt Λ)) := by
    have : Real.sqrt Λ ≠ 0 := by positivity
    field_simp
  linarith

end Constants

section Energy

variable {a : CoeffField d} {Λ : ℝ}

theorem ball_measurableSet : MeasurableSet (euclideanBall (0 : Vec d) 1) :=
  measurableSet_euclideanBall _ _

theorem vecEuclideanNorm_le_energy {A : Mat d} (hA : IsEllipticMatrix 1 Λ A) (ξ : Vec d) :
    vecEuclideanNorm ξ ≤ Real.sqrt (vecDot ξ (matVecMul A ξ)) := by
  have h : vecEuclideanNorm ξ ^ 2 ≤ vecDot ξ (matVecMul A ξ) := by
    have := hA.coercive ξ
    rw [vecEuclideanNorm_sq]
    linarith
  calc vecEuclideanNorm ξ = Real.sqrt (vecEuclideanNorm ξ ^ 2) :=
        (Real.sqrt_sq (vecEuclideanNorm_nonneg ξ)).symm
    _ ≤ _ := Real.sqrt_le_sqrt h

theorem energy_nonneg {A : Mat d} (hA : IsEllipticMatrix 1 Λ A) (ξ : Vec d) :
    0 ≤ vecDot ξ (matVecMul A ξ) := by
  have := hA.coercive ξ
  have h0 := vecNormSq_nonneg ξ
  linarith

theorem energy_sq {A : Mat d} (hA : IsEllipticMatrix 1 Λ A) (ξ : Vec d) :
    Real.sqrt (vecDot ξ (matVecMul A ξ)) ^ 2 = vecDot ξ (matVecMul A ξ) :=
  Real.sq_sqrt (energy_nonneg hA ξ)

theorem one_le_of_elliptic
    (hell : ∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) :
    1 ≤ Λ :=
  (hell 0 (center_mem_euclideanBall 0 one_pos)).lam_le_Lam

theorem memVectorL2On_flux
    (ha : ∀ i j : Fin d,
      AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1)))
    (hell : ∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x))
    {G : Vec d → Vec d} (hG : MemVectorL2On (euclideanBall (0 : Vec d) 1) G) :
    MemVectorL2On (euclideanBall (0 : Vec d) 1) (fun x => matVecMul (a x) (G x)) := by
  refine memVectorL2On_matVecMul_of_ae_operator_bound hG
    (fun i j => (ha i j).aestronglyMeasurable) (delta := Λ)
    (by linarith [one_le_of_elliptic hell]) ?_
  exact ae_restrict_of_forall_mem ball_measurableSet fun x hx v =>
    vecEuclideanNorm_matVecMul_le_of_isEllipticMatrix (hell x hx) v

theorem integrableOn_energy
    (ha : ∀ i j : Fin d,
      AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1)))
    (hell : ∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x))
    {G : Vec d → Vec d} (hG : MemVectorL2On (euclideanBall (0 : Vec d) 1) G) :
    IntegrableOn (fun x => vecDot (G x) (matVecMul (a x) (G x)))
      (euclideanBall (0 : Vec d) 1) :=
  integrableOn_vecDot_of_memVectorL2On hG (memVectorL2On_flux ha hell hG)

theorem integrableOn_w_sq
    (ha : ∀ i j : Fin d,
      AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1)))
    (hell : ∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x))
    {G : Vec d → Vec d} (hG : MemVectorL2On (euclideanBall (0 : Vec d) 1) G) :
    IntegrableOn (fun x => Real.sqrt (vecDot (G x) (matVecMul (a x) (G x))) ^ 2)
      (euclideanBall (0 : Vec d) 1) :=
  (integrableOn_energy ha hell hG).congr_fun
    (fun x hx => (energy_sq (hell x hx) (G x)).symm) ball_measurableSet

theorem aestronglyMeasurable_w
    (ha : ∀ i j : Fin d,
      AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1)))
    (hell : ∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x))
    {G : Vec d → Vec d} (hG : MemVectorL2On (euclideanBall (0 : Vec d) 1) G) :
    AEStronglyMeasurable (fun x => Real.sqrt (vecDot (G x) (matVecMul (a x) (G x))))
      (volumeOn (euclideanBall (0 : Vec d) 1)) :=
  Real.continuous_sqrt.comp_aestronglyMeasurable
    (integrableOn_energy ha hell hG).aestronglyMeasurable

end Energy

section NormConversion

theorem eLpNorm_sq_eq {μ : Measure (Vec d)} {φ : Vec d → ℝ}
    (hφ : AEStronglyMeasurable φ μ) (hnn : ∀ x, 0 ≤ φ x) {s : ℝ} (hs : 0 < s) :
    eLpNorm (fun x => φ x ^ 2) (ENNReal.ofReal s) μ =
      eLpNorm φ (ENNReal.ofReal (2 * s)) μ ^ 2 := by
  have h := eLpNorm_norm_rpow φ hφ (p := ENNReal.ofReal s) (q := 2) two_pos
  have e1 : (fun x => ‖φ x‖ ^ (2 : ℝ)) = fun x => φ x ^ 2 := by
    funext x
    rw [Real.norm_of_nonneg (hnn x), Real.rpow_two]
  rw [e1] at h
  rw [h, ← ENNReal.ofReal_mul hs.le, mul_comm, ENNReal.rpow_two]

theorem ofReal_integralAverage_eq {U : Set (Vec d)} {g : Vec d → ℝ}
    (hg : IntegrableOn g U) (hnn : ∀ x, 0 ≤ g x)
    (hUpos : 0 < volume U) :
    ENNReal.ofReal (integralAverage U g) = eLpMeanNormOn U 1 g := by
  have hint : Integrable g (normalizedVolumeOn U) :=
    integrable_normalizedVolumeOn_of_integrableOn hg hUpos
  rw [← integral_normalizedVolumeOn_eq_integralAverage, eLpMeanNormOn,
    eLpNorm_one_eq_lintegral_enorm,
    ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn)]
  · refine lintegral_congr fun x => ?_
    rw [Real.enorm_of_nonneg (hnn x)]
  · exact hint.aestronglyMeasurable


theorem euclideanBall_half_subset : euclideanBall (0 : Vec d) (1 / 2) ⊆ euclideanBall (0 : Vec d) 1 := by
  exact euclideanBall_mono (by norm_num) (by norm_num)

theorem eLpMeanNormOn_half_le (φ : Vec d → ℝ) :
    eLpMeanNormOn (euclideanBall (0 : Vec d) (1 / 2)) 2 φ ≤
      ENNReal.ofReal ((2 : ℝ) ^ d) * eLpMeanNormOn (euclideanBall (0 : Vec d) 1) 2 φ := by
  have hT1 : volume (euclideanBall (0 : Vec d) 1) < ⊤ :=
    lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top _ zero_le_one)
  have hTh : volume (euclideanBall (0 : Vec d) (1 / 2)) < ⊤ :=
    lt_top_iff_ne_top.mpr (volume_euclideanBall_ne_top _ (by norm_num))
  rw [eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn hTh,
    eLpMeanNormOn_eq_volume_inv_rpow_mul_eLpNormOn hT1]
  have hvol : volume (euclideanBall (0 : Vec d) (1 / 2)) =
      ENNReal.ofReal (((1:ℝ) / 2) ^ d) * volume (euclideanBall (0 : Vec d) 1) :=
    volume_euclideanBall_eq_unit_mul_of_pos _ (by norm_num)
  have hpos : (0:ℝ) < ((1:ℝ) / 2) ^ d := by positivity
  have hinv : (volume (euclideanBall (0 : Vec d) (1 / 2)))⁻¹ =
      ENNReal.ofReal ((2:ℝ) ^ d) * (volume (euclideanBall (0 : Vec d) 1))⁻¹ := by
    rw [hvol, ENNReal.mul_inv (Or.inl (by simp)) (Or.inl ENNReal.ofReal_ne_top),
      ← ENNReal.ofReal_inv_of_pos hpos]
    congr 3
    rw [one_div, inv_pow, inv_inv]
  have hexp : (1 / (2 : ℝ≥0∞)).toReal = 1 / 2 := by
    simp
  rw [hinv, hexp, ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  have h1 : ENNReal.ofReal ((2:ℝ) ^ d) ^ (1 / 2 : ℝ) ≤ ENNReal.ofReal ((2:ℝ) ^ d) :=
    (ENNReal.rpow_le_rpow_of_exponent_le (by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (one_le_pow₀ (by norm_num)))
      (by norm_num : (1 / 2 : ℝ) ≤ 1)).trans_eq (ENNReal.rpow_one _)
  have h2 : eLpNormOn (euclideanBall (0 : Vec d) (1 / 2)) 2 φ ≤
      eLpNormOn (euclideanBall (0 : Vec d) 1) 2 φ :=
    eLpNorm_mono_measure _ (Measure.restrict_mono euclideanBall_half_subset le_rfl)
  calc _ ≤ (ENNReal.ofReal ((2:ℝ) ^ d) * (volume (euclideanBall (0 : Vec d) 1))⁻¹ ^ (1 / 2 : ℝ)) *
        eLpNormOn (euclideanBall (0 : Vec d) 1) 2 φ := by
        gcongr
    _ = _ := by ring


theorem le_of_sq_le_add {X Y Z : ℝ≥0∞} {a b K : ℝ} (ha : a ≤ K ^ 2) (hb : b ≤ K ^ 2)
    (hK : 0 ≤ K)
    (h : X ^ 2 ≤ ENNReal.ofReal a * Y ^ 2 + ENNReal.ofReal b * Z ^ 2) :
    X ≤ ENNReal.ofReal K * (Y + Z) := by
  have h1 : ENNReal.ofReal a ≤ ENNReal.ofReal K ^ 2 := by
    rw [← ENNReal.ofReal_pow hK]; exact ENNReal.ofReal_le_ofReal ha
  have h2 : ENNReal.ofReal b ≤ ENNReal.ofReal K ^ 2 := by
    rw [← ENNReal.ofReal_pow hK]; exact ENNReal.ofReal_le_ofReal hb
  have h3 : X ^ 2 ≤ (ENNReal.ofReal K * (Y + Z)) ^ 2 := by
    calc X ^ 2 ≤ ENNReal.ofReal K ^ 2 * Y ^ 2 + ENNReal.ofReal K ^ 2 * Z ^ 2 :=
          h.trans (add_le_add (by gcongr) (by gcongr))
      _ ≤ ENNReal.ofReal K ^ 2 * (Y + Z) ^ 2 := by
          rw [← mul_add]; gcongr; rw [add_sq]
          calc Y ^ 2 + Z ^ 2 ≤ Y ^ 2 + 2 * Y * Z + Z ^ 2 := by gcongr; exact le_self_add
            _ = _ := by ring
      _ = _ := by ring
  rw [← ENNReal.rpow_two, ← ENNReal.rpow_two] at h3
  exact (ENNReal.rpow_le_rpow_iff two_pos).1 h3

end NormConversion

section Interior

theorem aestronglyMeasurable_normalizedVolumeOn {V : Set (Vec d)} {φ : Vec d → ℝ}
    (h : AEStronglyMeasurable φ (volumeOn V)) :
    AEStronglyMeasurable φ (normalizedVolumeOn V) :=
  h.smul_measure _

theorem ofReal_two_mul_one_add {p : ℝ} :
    ENNReal.ofReal (2 * (1 + (p - 2) / 2)) = ENNReal.ofReal p := by
  congr 1; ring

theorem memLp_sq_of_memLp {μ : Measure (Vec d)} {φ : Vec d → ℝ} {p : ℝ} (hp : 2 < p)
    (hφ : MemLp φ (ENNReal.ofReal p) μ) (hnn : ∀ x, 0 ≤ φ x) :
    MemLp (fun x => φ x ^ 2) (ENNReal.ofReal (1 + (p - 2) / 2)) μ := by
  have hm : AEStronglyMeasurable φ μ := hφ.aestronglyMeasurable
  rw [memLp_iff, eLpNorm_sq_eq hm hnn (by linarith), ofReal_two_mul_one_add]
  exact ENNReal.pow_lt_top hφ.eLpNorm_lt_top

/-- Interior clause of the Meyers estimate for fixed constants. -/
theorem interior_clause {C₁ C₀ : ℝ} (hC₁ : 1 ≤ C₁) (hC₀ : 1 ≤ C₀)
    (hG : GehringWith d C₁) (hR : MeyersRHInteriorWith d C₀)
    (Λ : ℝ) (a : CoeffField d)
    (ha : ∀ i j : Fin d,
      AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1)))
    (hell : ∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x))
    (p : ℝ) (hp : 2 ≤ p) (hpΛ : p ≤ 2 + (2 / (C₁ * C₀)) / Real.sqrt Λ)
    (f : Vec d → Vec d)
    (hfm : ∀ i : Fin d,
      AEStronglyMeasurable (fun x => f x i) (volumeOn (euclideanBall (0 : Vec d) 1)))
    (hfp : MemLp (fun x => vecEuclideanNorm (f x)) (ENNReal.ofReal p)
      (volumeOn (euclideanBall (0 : Vec d) 1)))
    (u : H1Function (euclideanBall (0 : Vec d) 1))
    (hsol : IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u
      (0 : Vec d → ℝ) f) :
    eLpMeanNormOn (euclideanBall (0 : Vec d) (1 / 2)) (ENNReal.ofReal p)
        (fun x => Real.sqrt (vecDot (u.grad x) (matVecMul (a x) (u.grad x)))) ≤
      ENNReal.ofReal (C₁ * C₀ * 2 ^ d) *
        (eLpMeanNormOn (euclideanBall (0 : Vec d) 1) 2
            (fun x => Real.sqrt (vecDot (u.grad x) (matVecMul (a x) (u.grad x)))) +
          euclideanFieldELpMeanNormOn (euclideanBall (0 : Vec d) 1)
            (ENNReal.ofReal p) f) := by
  set w : Vec d → ℝ := fun x => Real.sqrt (vecDot (u.grad x) (matVecMul (a x) (u.grad x)))
    with hw_def
  have hw0 : ∀ x, 0 ≤ w x := fun x => Real.sqrt_nonneg _
  have hwm : AEStronglyMeasurable w (volumeOn (euclideanBall (0 : Vec d) 1)) :=
    aestronglyMeasurable_w ha hell u.gradMemL2
  have hΛ := one_le_of_elliptic hell
  have hK : 1 ≤ C₁ * C₀ := by nlinarith
  have hpow : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
  rcases hp.eq_or_lt with h2 | h2
  · -- the case p = 2
    subst h2
    have e2 : ENNReal.ofReal (2 : ℝ) = 2 := by simp
    rw [e2]
    have := eLpMeanNormOn_half_le (d := d) w
    refine this.trans ?_
    have hle : ENNReal.ofReal ((2:ℝ) ^ d) ≤ ENNReal.ofReal (C₁ * C₀ * 2 ^ d) :=
      ENNReal.ofReal_le_ofReal (by nlinarith)
    calc _ ≤ ENNReal.ofReal (C₁ * C₀ * 2 ^ d) * eLpMeanNormOn (euclideanBall (0 : Vec d) 1) 2 w := by
          gcongr
      _ ≤ _ := by
          gcongr
          exact le_self_add
  · set ε : ℝ := (p - 2) / 2 with hε_def
    have hε : 0 < ε := by rw [hε_def]; linarith
    obtain ⟨hεle, hA⟩ := epsilon_le_of_le_exponent hC₁ hC₀ hΛ hpΛ
    have hf0 : ∀ x, 0 ≤ vecEuclideanNorm (f x) := fun x => vecEuclideanNorm_nonneg _
    have hfm2 : AEStronglyMeasurable (fun x => vecEuclideanNorm (f x))
        (volumeOn (euclideanBall (0 : Vec d) 1)) := hfp.aestronglyMeasurable
    have hf2 : MemLp (fun x => vecEuclideanNorm (f x)) 2
        (volumeOn (euclideanBall (0 : Vec d) 1)) := by
      have := isFiniteMeasure_volumeOn_euclideanBall (0 : Vec d) (R := 1) zero_le_one
      refine hfp.mono_exponent ?_
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp]
      exact ENNReal.ofReal_le_ofReal hp
    have hint : IntegrableOn (fun x => w x ^ 2) (euclideanBall (0 : Vec d) 1) :=
      integrableOn_w_sq ha hell u.gradMemL2
    have hhmem : MemLp (fun x => vecEuclideanNorm (f x) ^ 2)
        (ENNReal.ofReal (1 + ε)) (volumeOn (euclideanBall (0 : Vec d) 1)) :=
      memLp_sq_of_memLp h2 hfp hf0
    have hrh : ∀ (z : Vec d) (r : ℝ), 0 < r →
        centeredAxisCube z (2 * r) ⊆ euclideanBall (0 : Vec d) 1 →
        ∫ x in centeredAxisCube z r, (fun x => w x ^ 2) x ≤
          (C₀ * Real.sqrt Λ) * (volume (centeredAxisCube z r)).toReal *
              (integralAverage (centeredAxisCube z (2 * r))
                (fun x => (fun x => w x ^ 2) x ^ ((d : ℝ) / ((d : ℝ) + 1)))) ^
                  (((d : ℝ) + 1) / (d : ℝ)) +
            C₀ * ∫ x in centeredAxisCube z (2 * r), (fun x => vecEuclideanNorm (f x) ^ 2) x :=
      fun z r hr hsub => hR Λ a ha hell f hfm hf2 u hsol z r hr hsub
    have hmain := (hG 2 (Or.inl rfl) (C₀ * Real.sqrt Λ) C₀ ε hA (by linarith) hε hεle
      (fun x => w x ^ 2) (fun x => vecEuclideanNorm (f x) ^ 2)
      (fun x => sq_nonneg _) (fun x => sq_nonneg _)).2 ⟨hint, hhmem, hrh⟩
    -- convert the three norms
    have hwB : AEStronglyMeasurable w (normalizedVolumeOn (euclideanBall (0 : Vec d) 1)) :=
      aestronglyMeasurable_normalizedVolumeOn hwm
    have hwH : AEStronglyMeasurable w (normalizedVolumeOn (euclideanBall (0 : Vec d) (1 / 2))) :=
      aestronglyMeasurable_normalizedVolumeOn
        (hwm.mono_measure (Measure.restrict_mono
          (euclideanBall_mono (by norm_num) (by norm_num)) le_rfl))
    have hfB : AEStronglyMeasurable (fun x => vecEuclideanNorm (f x))
        (normalizedVolumeOn (euclideanBall (0 : Vec d) 1)) :=
      aestronglyMeasurable_normalizedVolumeOn hfm2
    have hs : 0 < 1 + ε := by linarith
    have e1 : eLpMeanNormOn (euclideanBall (0 : Vec d) (1 / 2)) (ENNReal.ofReal (1 + ε))
        (fun x => w x ^ 2) =
        eLpMeanNormOn (euclideanBall (0 : Vec d) (1 / 2)) (ENNReal.ofReal p) w ^ 2 := by
      unfold eLpMeanNormOn
      rw [eLpNorm_sq_eq hwH hw0 hs, ofReal_two_mul_one_add]
    have e2 : eLpMeanNormOn (euclideanBall (0 : Vec d) 1) (ENNReal.ofReal (1 + ε))
        (fun x => vecEuclideanNorm (f x) ^ 2) =
        euclideanFieldELpMeanNormOn (euclideanBall (0 : Vec d) 1) (ENNReal.ofReal p) f ^ 2 := by
      unfold eLpMeanNormOn euclideanFieldELpMeanNormOn eLpMeanNormOn
      rw [eLpNorm_sq_eq hfB hf0 hs, ofReal_two_mul_one_add]
    have e3 : ENNReal.ofReal (integralAverage (euclideanBall (0 : Vec d) 1) (fun x => w x ^ 2)) =
        eLpMeanNormOn (euclideanBall (0 : Vec d) 1) 2 w ^ 2 := by
      rw [ofReal_integralAverage_eq hint (fun x => sq_nonneg _)
        (volume_euclideanBall_pos _ one_pos)]
      unfold eLpMeanNormOn
      have := eLpNorm_sq_eq hwB hw0 (one_pos : (0:ℝ) < 1)
      rw [ENNReal.ofReal_one, show 2 * (1:ℝ) = 2 by norm_num] at this
      rw [this]
      simp
    rw [e1, e2, ENNReal.ofReal_mul (by linarith), e3] at hmain
    refine le_trans (le_of_sq_le_add (a := C₁) (b := C₁ * C₀) (K := C₁ * C₀)
      (by nlinarith) (by nlinarith) (by linarith) hmain) ?_
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (by nlinarith)) le_rfl

end Interior

end MeyersAssembly

end PDE
