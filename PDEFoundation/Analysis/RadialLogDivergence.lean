module

public import PDEFoundation.Analysis.RadialFluxSmooth
public import PDEFoundation.Analysis.RadialVectorDivergence

@[expose] public section

namespace PDE
open scoped BigOperators

private theorem log_radius_eq_half_log_square {d : ℕ} :
    (fun x : Vec d => Real.log (vecEuclideanNorm x)) =
      fun x => (1 / 2 : ℝ) * Real.log (vecNormSq x) := by
  funext x
  rw [← vecEuclideanNorm_sq, Real.log_pow]
  ring

private theorem differentiableAt_log_radius
    {d : ℕ} (x : Vec d) (hx : x ≠ 0) :
    DifferentiableAt ℝ (fun x : Vec d => Real.log (vecEuclideanNorm x)) x := by
  rw [log_radius_eq_half_log_square]
  have hq : DifferentiableAt ℝ vecNormSq x := by unfold vecNormSq vecDot; fun_prop
  exact (hq.log (vecNormSq_eq_zero_iff.not.mpr hx)).const_mul _

/-- The actual coordinate gradient of the logarithm of the Euclidean radius. -/
theorem classicalGradient_log_vecEuclideanNorm
    {d : ℕ} (x : Vec d) (hx : x ≠ 0) :
    classicalGradient (fun y : Vec d => Real.log (vecEuclideanNorm y)) x =
      fun i => x i / vecNormSq x := by
  have hq : DifferentiableAt ℝ vecNormSq x := by unfold vecNormSq vecDot; fun_prop
  have hne : vecNormSq x ≠ 0 := vecNormSq_eq_zero_iff.not.mpr hx
  have hgrad : classicalGradient vecNormSq x = fun i => 2 * x i := by
    simpa only [Real.rpow_one, sub_self, Real.rpow_zero, one_mul] using
      classicalGradient_vecNormSq_rpow 1 x hx
  rw [log_radius_eq_half_log_square]
  funext i
  rw [classicalGradient_apply, fderiv_const_mul (hq.log hne), fderiv.log hq hne]
  simp only [smul_apply, smul_eq_mul, ← classicalGradient_apply]
  rw [hgrad]
  simp only [div_eq_mul_inv]
  ring

private theorem radialLogGradientField_eq_log_plus_radial
    {d : ℕ} (k : Fin d) (x : Vec d) :
    radialLogGradientField k x =
      Real.log (vecEuclideanNorm x) • basisVec k + radialVectorField 0 1 0 k x := by
  ext i
  simp only [radialLogGradientField, radialVectorField, zero_mul, one_mul,
    zero_sub, Real.rpow_neg_one, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, zero_add, div_eq_mul_inv]
  ring

/-- The logarithmic coordinate mode has the classical Laplacian prescribed
by its dimension, away from zero. -/
theorem sum_classicalGradient_radialLogGradientField
    {d : ℕ} (k : Fin d) (x : Vec d) (hx : x ≠ 0) :
    (∑ i : Fin d, classicalGradient
      (fun y : Vec d => radialLogGradientField k y i) x i) =
      (d : ℝ) * x k / vecNormSq x := by
  have hq : DifferentiableAt ℝ vecNormSq x := by unfold vecNormSq vecDot; fun_prop
  have hne : vecNormSq x ≠ 0 := vecNormSq_eq_zero_iff.not.mpr hx
  have hlog := differentiableAt_log_radius x hx
  have hcomponent (i : Fin d) :
      classicalGradient (fun y : Vec d => radialLogGradientField k y i) x i =
        basisVec k i * (x i / vecNormSq x) +
        classicalGradient (fun y : Vec d => radialVectorField 0 1 0 k y i) x i := by
    have hrad : DifferentiableAt ℝ
        (fun y : Vec d => radialVectorField 0 1 0 k y i) x := by
      simp only [radialVectorField, zero_mul, one_mul, zero_sub,
        Real.rpow_neg_one, Pi.add_apply, Pi.smul_apply, smul_eq_mul, zero_add]
      have hinv := hq.inv hne
      exact ((hasFDerivAt_apply (𝕜 := ℝ) k x).differentiableAt.mul hinv).mul
        (hasFDerivAt_apply (𝕜 := ℝ) i x).differentiableAt
    have heq : (fun y : Vec d => radialLogGradientField k y i) =
        fun y => basisVec k i * Real.log (vecEuclideanNorm y) +
          radialVectorField 0 1 0 k y i := by
      funext y
      rw [radialLogGradientField_eq_log_plus_radial]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hadd : fderiv ℝ (fun y : Vec d => basisVec k i * Real.log (vecEuclideanNorm y) +
        radialVectorField 0 1 0 k y i) x =
        fderiv ℝ (fun y : Vec d => basisVec k i * Real.log (vecEuclideanNorm y)) x +
        fderiv ℝ (fun y : Vec d => radialVectorField 0 1 0 k y i) x := by
      simpa only [Pi.add_apply] using! fderiv_add (hlog.const_mul (basisVec k i)) hrad
    rw [heq, classicalGradient_apply, hadd]
    rw [fderiv_const_mul hlog]
    simp only [add_apply, smul_apply,
      smul_eq_mul, ← classicalGradient_apply]
    rw [classicalGradient_log_vecEuclideanNorm x hx]
  simp_rw [hcomponent]
  rw [Finset.sum_add_distrib,
    sum_classicalGradient_radialVectorField_component 0 1 0 k x hx]
  have hbasis : (∑ i : Fin d, basisVec k i * (x i / vecNormSq x)) =
      x k / vecNormSq x := by simp [basisVec_apply]
  rw [hbasis]
  simp only [mul_zero, zero_add, one_mul, add_zero, zero_sub, Real.rpow_neg_one]
  rw [div_eq_mul_inv, div_eq_mul_inv]
  ring

/-- The total logarithmic gradient and forcing flux is classically divergence
free in the plane away from zero. -/
theorem sum_classicalGradient_radialLogGradientField_add_radialForcing_fin_two
    (k : Fin 2) (x : Vec 2) (hx : x ≠ 0) :
    (∑ i : Fin 2, classicalGradient
      (fun y : Vec 2 => radialLogGradientField k y i + radialForcing k y i) x i) = 0 := by
  have hdiff (i : Fin 2) :
      classicalGradient (fun y : Vec 2 => radialLogGradientField k y i + radialForcing k y i) x i =
      classicalGradient (fun y : Vec 2 => radialLogGradientField k y i) x i +
      classicalGradient (fun y : Vec 2 => radialForcing k y i) x i := by
    have hopen : IsOpen (({0} : Set (Vec 2))ᶜ) := isClosed_singleton.isOpen_compl
    have hxmem : x ∈ ({0} : Set (Vec 2))ᶜ := hx
    have hG := (contDiffOn_radialLogGradientField_apply k i).contDiffAt (hopen.mem_nhds hxmem)
    have hF := (contDiffOn_radialForcing_apply k i).contDiffAt (hopen.mem_nhds hxmem)
    have hadd : fderiv ℝ (fun y : Vec 2 => radialLogGradientField k y i + radialForcing k y i) x =
        fderiv ℝ (fun y : Vec 2 => radialLogGradientField k y i) x +
        fderiv ℝ (fun y : Vec 2 => radialForcing k y i) x := by
      simpa only [Pi.add_apply] using!
        fderiv_add (hG.differentiableAt (by simp)) (hF.differentiableAt (by simp))
    rw [classicalGradient_apply, classicalGradient_apply, classicalGradient_apply, hadd]
    rfl
  simp_rw [hdiff]
  rw [Finset.sum_add_distrib, sum_classicalGradient_radialLogGradientField k x hx,
    sum_classicalGradient_radialForcing_component k x hx]
  norm_num
  ring

end PDE
