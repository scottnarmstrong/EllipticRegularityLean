module

public import EllipticRegularity.Parabolic.Cauchy.Duality.MassCutoff
public import EllipticRegularity.Parabolic.Cauchy.Energy.Cutoff

/-! # Mass from an exponential weighted flux bound -/

@[expose] public section

set_option linter.style.haveILetI false

namespace PDE.Parabolic.Duality

open MeasureTheory Set Filter Topology PDE PDE.Parabolic

/-- Exponential weighted `L²` control of the flux makes the spatial cutoff
error vanish. Together with endpoint `L¹` integrability, this yields mass
conservation. The weighted energy argument for compactly supported data is
responsible for the two explicit weighted `L²` hypotheses. -/
theorem cauchy_mass_of_exponential_flux {d : ℕ} {lam Lam ε : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : Integrable f volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) {t : ℝ}
    (ht : t ∈ Icc s T) (hst : s < t)
    (hut : Integrable (parSlice u.toFun t) volume)
    (hflux : MemLp
      (fun z : Vec d × ℝ =>
        Real.exp (ε * vecEuclideanNorm z.1) *
          vecEuclideanNorm (matVecMul (a z) (u.grad z)))
      2 (volume.restrict (univ ×ˢ Ioc s t)))
    (hinv : MemLp
      (fun z : Vec d × ℝ => Real.exp (-ε * vecEuclideanNorm z.1))
      2 (volume.restrict (univ ×ˢ Ioc s t))) :
    ∫ x : Vec d, u.toFun (x, t) = ∫ x : Vec d, f x := by
  let Q : Set (Vec d × ℝ) := univ ×ˢ Ioc s t
  let μ : Measure (Vec d × ℝ) := volume.restrict Q
  let N : Vec d × ℝ → ℝ := fun z => vecEuclideanNorm (matVecMul (a z) (u.grad z))
  let W : Vec d × ℝ → ℝ := fun z => Real.exp (ε * vecEuclideanNorm z.1)
  let Winv : Vec d × ℝ → ℝ := fun z => Real.exp (-ε * vecEuclideanNorm z.1)
  have hHolder : Real.HolderTriple 2 2 1 := by
    constructor <;> norm_num
  letI : Real.HolderTriple 2 2 1 := hHolder
  have hprod : MemLp (fun z => W z * N z * Winv z) 1 μ := by
    change MemLp ((W * N) * Winv) 1 μ
    exact hflux.mul hinv
  have hprodEq : (fun z => W z * N z * Winv z) = N := by
    funext z
    dsimp [W, N, Winv]
    calc
      Real.exp (ε * vecEuclideanNorm z.1) *
          vecEuclideanNorm (matVecMul (a z) (u.grad z)) *
          Real.exp (-ε * vecEuclideanNorm z.1) =
          (Real.exp (ε * vecEuclideanNorm z.1) *
            Real.exp (-ε * vecEuclideanNorm z.1)) *
            vecEuclideanNorm (matVecMul (a z) (u.grad z)) := by ring
      _ = vecEuclideanNorm (matVecMul (a z) (u.grad z)) := by
        rw [← Real.exp_add]
        simp
  have hNmem : MemLp N 1 μ :=
    (memLp_congr_ae (ae_of_all μ fun z => congrFun hprodEq z)).mp hprod
  have hNint : Integrable N μ := memLp_one_iff_integrable.mp hNmem
  have hNnonneg : ∀ z, 0 ≤ N z := fun z => vecEuclideanNorm_nonneg _
  have hMnonneg : 0 ≤ ∫ z in Q, N z := by
    apply integral_nonneg_of_ae
    exact ae_of_all _ hNnonneg
  have hR : ∀ n : ℕ, 0 < (n : ℝ) + 1 := by intro n; positivity
  let ζ : ℕ → Vec d → ℝ := fun n =>
    (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff ((n : ℝ) + 1) (hR n)).toFun
  have hζ : ∀ n, ContDiff ℝ 1 (ζ n) := by
    intro n
    exact (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff ((n : ℝ) + 1) (hR n)).smooth.of_le
      (by norm_num)
  have hζc : ∀ n, HasCompactSupport (ζ n) := by
    intro n
    exact (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff ((n : ℝ) + 1) (hR n)).hasCompactSupport
  have hζbound : ∀ n x, |ζ n x| ≤ 1 := by
    intro n x
    rw [abs_le]
    exact ⟨by
      have := (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff
        ((n : ℝ) + 1) (hR n)).nonneg x
      linarith,
      by
      have := (PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff
        ((n : ℝ) + 1) (hR n)).le_one x
      simpa [ζ] using this⟩
  have hR_tendsto : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hζtendsto : ∀ x, Tendsto (fun n => ζ n x) atTop (𝓝 1) := by
    intro x
    have hev : (fun _ : ℕ => (1 : ℝ)) =ᶠ[atTop] fun n => ζ n x := by
      filter_upwards [hR_tendsto.eventually_gt_atTop (vecEuclideanNorm x)] with n hn
      have hball : x ∈ euclideanBall (0 : Vec d) ((n : ℝ) + 1) :=
        (mem_euclideanBall_iff_vecEuclideanNorm_lt (hR n)).2 (by
          simpa using hn)
      exact ((PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff
        ((n : ℝ) + 1) (hR n)).eq_one_on_inner x hball).symm
    exact tendsto_const_nhds.congr' hev
  have hflux_tendsto : Tendsto (fun n => ∫ z in Q,
      vecDot (matVecMul (a z) (u.grad z)) (spaceGradC1 (ζ n) z.1)) atTop (𝓝 0) := by
    let C : ℕ → ℝ := fun n => (32 : ℝ) / ((n : ℝ) + 1)
    have hC : Tendsto C atTop (𝓝 0) := by
      have h := (tendsto_const_div_atTop_nhds_zero_nat (32 : ℝ)).comp
        (tendsto_add_atTop_nat 1)
      have heq : C = fun n => (32 : ℝ) / (n + 1 : ℕ) := by
        funext n
        simp [C, Nat.cast_add]
      rw [heq]
      exact h
    have hbound : ∀ n, ‖∫ z in Q,
        vecDot (matVecMul (a z) (u.grad z)) (spaceGradC1 (ζ n) z.1)‖ ≤
          C n * ∫ z in Q, N z := by
      intro n
      let χ := PDE.Parabolic.Cauchy.Energy.cauchySpatialCutoff (d := d)
        ((n : ℝ) + 1) (hR n)
      let G : Vec d × ℝ → ℝ := fun z =>
        vecDot (matVecMul (a z) (u.grad z)) (spaceGradC1 (ζ n) z.1)
      obtain ⟨hGint, _⟩ := cauchy_compact_pairing_change hsT ha f u hu
        (ζ n) (hζ n) (hζc n) ht hst
      have hGnorm : Integrable (fun z => ‖G z‖) μ := by
        simpa [G, μ, Q] using hGint.norm
      have hpoint : ∀ z, ‖G z‖ ≤ C n * N z := by
        intro z
        have hgrad : vecEuclideanNorm (spaceGradC1 (ζ n) z.1) ≤
            32 / ((n : ℝ) + 1) := by
          have hgrad' : spaceGradC1 (ζ n) z.1 = classicalGradient χ.toFun z.1 := by
            ext i
            rfl
          rw [hgrad']
          exact χ.gradient_bound z.1
        have hdot := abs_vecDot_le_vecEuclideanNorm_mul
          (matVecMul (a z) (u.grad z)) (spaceGradC1 (ζ n) z.1)
        rw [Real.norm_eq_abs]
        dsimp [G, C, N]
        calc
          |vecDot (matVecMul (a z) (u.grad z)) (spaceGradC1 (ζ n) z.1)| ≤
              vecEuclideanNorm (matVecMul (a z) (u.grad z)) *
                vecEuclideanNorm (spaceGradC1 (ζ n) z.1) := hdot
          _ ≤ vecEuclideanNorm (matVecMul (a z) (u.grad z)) *
                (32 / ((n : ℝ) + 1)) := by
              exact mul_le_mul_of_nonneg_left hgrad (vecEuclideanNorm_nonneg _)
          _ = (32 / ((n : ℝ) + 1)) *
                vecEuclideanNorm (matVecMul (a z) (u.grad z)) := by ring
      have hscaled : Integrable (fun z => C n * N z) μ := hNint.const_mul _
      have hmono : ∫ z, ‖G z‖ ∂μ ≤ ∫ z, C n * N z ∂μ :=
        integral_mono_ae hGnorm hscaled (ae_of_all μ hpoint)
      have hnorm : ‖∫ z, G z ∂μ‖ ≤ ∫ z, ‖G z‖ ∂μ :=
        norm_integral_le_integral_norm G
      have hconst : ∫ z, C n * N z ∂μ = C n * ∫ z, N z ∂μ :=
        integral_const_mul _ _
      simpa [μ, Q, G, C, setIntegral_univ] using hnorm.trans (hmono.trans_eq hconst)
    have htail : Tendsto (fun n => C n * ∫ z in Q, N z) atTop (𝓝 0) := by
      simpa only [zero_mul] using hC.mul_const (∫ z in Q, N z)
    exact squeeze_zero_norm hbound htail
  exact cauchy_mass_of_cutoff_flux_limit hsT ha f hf u hu ht hst hut ζ hζ hζc
    hζbound hζtendsto hflux_tendsto

end PDE.Parabolic.Duality
