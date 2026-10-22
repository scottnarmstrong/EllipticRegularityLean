module

public import EllipticRegularity.Energy.CubeHoleFillingDecay
public import EllipticRegularity.Energy.CoefficientEnergyCaccioppoli
public import PDEFoundation.Sobolev.Cutoff.Ball
public import PDEFoundation.Geometry.ConvexDomain
public import PDEFoundation.Geometry.EuclideanBall.Interior

/-! # Ball and cube geometry for general-dimensional hole filling -/

@[expose] public section

namespace PDE

open MeasureTheory

/-- The largest centered cube half-side used inside the half-unit round ball. -/
noncomputable def cubeHoleFillingRootRadius (d : ℕ) : ℝ :=
  1 / (2 * Real.sqrt d)

/-- The root cube radius is positive in dimension at least two. -/
theorem cubeHoleFillingRootRadius_pos {d : ℕ} (hd : 2 ≤ d) :
    0 < cubeHoleFillingRootRadius d := by
  unfold cubeHoleFillingRootRadius
  have hdreal : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  positivity

/-- The root cube radius is at most one half. -/
theorem cubeHoleFillingRootRadius_le_half {d : ℕ} (hd : 2 ≤ d) :
    cubeHoleFillingRootRadius d ≤ 1 / 2 := by
  have hdone : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
  have hsqrt : 1 ≤ Real.sqrt d := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hdone
  unfold cubeHoleFillingRootRadius
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.sqrt d)).2
  nlinarith only [hsqrt]

/-- A round ball fits in the centered native axis cube with the same radius. -/
theorem euclideanBall_subset_centeredAxisCube
    {d : ℕ} (z : Vec d) {r : ℝ} (hr : 0 < r) :
    euclideanBall z r ⊆ centeredAxisCube z r := by
  rw [centeredAxisCube_eq_metric_ball z hr]
  exact euclideanBall_subset_supBall hr

/-- The centered root cube is contained in the half-unit round ball. -/
theorem rootCube_subset_halfBall
    {d : ℕ} (hd : 2 ≤ d) :
    centeredAxisCube (0 : Vec d) (cubeHoleFillingRootRadius d) ⊆
      euclideanBall (0 : Vec d) (1 / 2) := by
  let R₀ := cubeHoleFillingRootRadius d
  have hR₀ : 0 < R₀ := cubeHoleFillingRootRadius_pos hd
  have hdreal : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 hdreal
  have hprod : Real.sqrt d * R₀ = 1 / 2 := by
    dsimp [R₀, cubeHoleFillingRootRadius]
    field_simp [hsqrt.ne']
  intro x hx
  have hxCube : ‖x - (0 : Vec d)‖ < R₀ := by
    rw [centeredAxisCube_eq_metric_ball (0 : Vec d) hR₀,
      Metric.mem_ball, dist_eq_norm] at hx
    exact hx
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt
    (by norm_num : (0 : ℝ) < 1 / 2)).2
  calc
    vecEuclideanNorm (x - (0 : Vec d)) ≤
        Real.sqrt d * ‖x - (0 : Vec d)‖ :=
      vecEuclideanNorm_le_sqrt_natCast_mul_norm _
    _ < Real.sqrt d * R₀ := mul_lt_mul_of_pos_left hxCube hsqrt
    _ = 1 / 2 := hprod

/-- Coefficient energy is monotone under measurable set inclusion inside
the ellipticity domain, by normalized coercivity. -/
theorem setIntegral_coefficientEnergy_mono
    {d : ℕ} {Λ : ℝ} {U S T : Set (Vec d)}
    {a : CoeffField d} {u : H1Function U}
    (hEll : IsEllipticFieldOn 1 Λ U a)
    (hST : S ⊆ T) (hTU : T ⊆ U)
    (hTmeas : MeasurableSet T) :
    (∫ x in S, vecDot (u.grad x) (matVecMul (a x) (u.grad x))) ≤
      ∫ x in T, vecDot (u.grad x) (matVecMul (a x) (u.grad x)) := by
  have hIntT : IntegrableOn
      (fun x => vecDot (u.grad x) (matVecMul (a x) (u.grad x))) T :=
    (integrableOn_coefficientEnergy_of_isEllipticFieldOn hEll u.gradMemL2).mono_set
      hTU
  apply setIntegral_mono_set hIntT
  · filter_upwards [ae_restrict_mem hTmeas] with x hx
    exact (vecNormSq_nonneg (u.grad x)).trans
      (by simpa only [one_mul] using
        ((hEll.elliptic (hTU hx)).coercive (u.grad x)))
  · exact Filter.Eventually.of_forall hST

/-- Coefficient energy on the half-unit ball is controlled by the value
`L²` energy on the unit ball, with one factor of `Λ`. -/
theorem coefficientEnergy_halfBall_le_unit_value_sq
    {d : ℕ} {Λ : ℝ} {a : CoeffField d}
    {u : H1Function (euclideanBall (0 : Vec d) 1)}
    (hEll : IsEllipticFieldOn 1 Λ (euclideanBall (0 : Vec d) 1) a)
    (hsol : IsWeakDivergenceFormHarmonicOn a
      (euclideanBall (0 : Vec d) 1) u) :
    (∫ x in euclideanBall (0 : Vec d) (1 / 2),
      vecDot (u.grad x) (matVecMul (a x) (u.grad x))) ≤
      16384 * Λ *
        ∫ x in euclideanBall (0 : Vec d) 1, u x ^ 2 := by
  have hΛ : 0 ≤ Λ :=
    (hEll.elliptic (center_mem_euclideanBall (0 : Vec d)
      (by norm_num : (0 : ℝ) < 1))).Lam_pos.le
  have hbase := caccioppoli_coefficient_energy_on_inner
    (isOpenBoundedConvexDomain_euclideanBall (0 : Vec d)
      (by norm_num : (0 : ℝ) < 1))
    (measurableSet_euclideanBall (0 : Vec d) (1 / 2))
    (measurableSet_euclideanBall (0 : Vec d) 1)
    hEll (by norm_num : (0 : ℝ) < 1) hΛ hsol
    (quantitativeBallCutoff (0 : Vec d)
      (r := (1 / 2 : ℝ)) (R := 1) (by norm_num) (by norm_num))
    (Set.Subset.rfl) (k := 0)
  have hcoef : (4 * Λ / 1) * (32 / (1 - (1 / 2 : ℝ))) ^ 2 =
      16384 * Λ := by ring
  rw [hcoef] at hbase
  simpa only [div_one, sub_zero] using hbase

end PDE
