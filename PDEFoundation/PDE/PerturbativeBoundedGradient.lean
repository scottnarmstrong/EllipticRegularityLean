module

public import PDEFoundation.PDE.PerturbativeFixedNormBound
public import PDEFoundation.Measure.HalfBallNormalization

@[expose] public section

namespace PDE

open MeasureTheory
open scoped _root_.ENNReal

/-- The high-exponent perturbative estimate with one dimension constant,
under the explicit temporary interior gradient bound. The normalization and
absorption condition are discharged internally. -/
theorem exists_perturbativeLaplacian_boundedGradient_constants
    (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 1 ≤ C ∧
    ∀ (p delta M : ℝ), 4 ≤ p → 0 ≤ delta → 0 ≤ M →
    ∀ (a : CoeffField d) (F : Vec d → Vec d)
      (u : H1Function (euclideanBall (0 : Vec d) 1)),
    (∀ i j, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec d) 1))) →
    (∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) 1),
      IsMatrixPerturbationLE delta (a x) (1 : Mat d)) →
    (∀ i, AEStronglyMeasurable (fun x => F x i)
      (volumeOn (euclideanBall (0 : Vec d) 1))) →
    MemLp (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p)
      (volumeOn (euclideanBall (0 : Vec d) 1)) →
    IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u 0 F →
    (∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec d) (3 / 4)),
      vecEuclideanNorm (u.grad x) ≤ M) →
    delta ≤ 1 / (C * p) →
    MemLp (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
      (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ∧
    (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
      (normalizedVolumeOn (euclideanBall (0 : Vec d) (1 / 2)))).toReal ≤
    C * (Real.sqrt (integralAverage (euclideanBall (0 : Vec d) 1)
      (fun x => vecNormSq (u.grad x))) + p *
      (eLpNorm (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p)
        (normalizedVolumeOn (euclideanBall (0 : Vec d) 1))).toReal) := by
  obtain ⟨A, K, hA, hK, hfixed⟩ :=
    exists_perturbativeLaplacian_fixedNorm_bound_constants d hd
  let D := (2 : ℝ)^((d : ℝ)/4)
  let J := (4 / (1 - calderonZygmundIterationSigma d))^((d : ℝ)/2) /
    (1 - Real.sqrt 2 / 2)
  have hD : 0 ≤ D := Real.rpow_nonneg (by norm_num) _
  have hgap : 0 < 1 - Real.sqrt 2 / 2 := by
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ)≤2)
    have hsn := Real.sqrt_nonneg 2
    nlinarith
  have hJ : 0 ≤ J := div_nonneg (Real.rpow_nonneg (by
    exact div_nonneg (by norm_num) (sub_pos.mpr (calderonZygmundIterationSigma_lt_one hd)).le) _) hgap.le
  let C := 1 + 2 * K + D * (A * J + 2 * K)
  have hC : 1 ≤ C := by
    have hterm := mul_nonneg hD (add_nonneg (mul_nonneg hA hJ) (by positivity : 0≤2*K))
    dsimp only [C]
    linarith
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  have h2K : 2 * K ≤ C := by
    have hterm := mul_nonneg hD (add_nonneg (mul_nonneg hA hJ) (by positivity : 0≤2*K))
    dsimp only [C]
    linarith
  have henergy : D * (A * J) ≤ C := by
    have hdk := mul_nonneg hD (by positivity : 0≤2*K)
    dsimp only [C]
    nlinarith
  have hforcing : D * (2*K) ≤ C := by
    have hdaj := mul_nonneg hD (mul_nonneg hA hJ)
    dsimp only [C]
    nlinarith
  refine ⟨C, hC, ?_⟩
  intro p delta M hp hdelta hM a F u ha hclose hFcoord hFp hsol hbound hsmall
  have hp0 : 0 < p := by linarith
  have hsmallmul : delta * (C * p) ≤ 1 := (le_div_iff₀ (mul_pos hCpos hp0)).mp hsmall
  have habs : K*p*delta ≤ 1/2 := by
    have h := mul_le_mul_of_nonneg_right h2K (mul_nonneg hp0.le hdelta)
    nlinarith only [h, hsmallmul]
  have hgrad := (exists_uniform_interior_eLpNorm_of_ae_bound u
    (by linarith : 1≤p) hM hbound (1/2) (by norm_num) (by norm_num)).1
  refine ⟨hgrad, ?_⟩
  have hf := hfixed p delta M hp hdelta hM a F u ha hclose hFcoord hFp hsol hbound habs
  have hn := eLpNorm_normalized_halfBall_toReal_le
    (fun x => vecEuclideanNorm (u.grad x)) hp hgrad
  let U := Real.sqrt (integralAverage (euclideanBall (0:Vec d) 1)
    (fun x=>vecNormSq (u.grad x)))
  let NF := (eLpNorm (fun x=>vecEuclideanNorm (F x)) (ENNReal.ofReal p)
    (normalizedVolumeOn (euclideanBall (0:Vec d) 1))).toReal
  have hU : 0 ≤ U := Real.sqrt_nonneg _
  have hNF : 0 ≤ NF := ENNReal.toReal_nonneg
  calc
    _ ≤ D * (eLpNorm (fun x=>vecEuclideanNorm (u.grad x)) (ENNReal.ofReal p)
        ((volume (euclideanBall (0:Vec d) 1))⁻¹ •
          volumeOn (euclideanBall (0:Vec d) (1/2)))).toReal := hn
    _ ≤ D * ((A * J) * U + (2*K)*p*NF) := by
      apply mul_le_mul_of_nonneg_left _ hD
      convert hf using 1; dsimp only [J, U, NF]; ring
    _ = (D*(A*J))*U + (D*(2*K))*(p*NF) := by ring
    _ ≤ C*U + C*(p*NF) := add_le_add
      (mul_le_mul_of_nonneg_right henergy hU)
      (mul_le_mul_of_nonneg_right hforcing (mul_nonneg hp0.le hNF))
    _ = _ := by dsimp only [U, NF]; ring

end PDE
