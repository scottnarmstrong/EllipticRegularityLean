module

public import PDEFoundation.Monotonicity.ACF.AssemblySlice
public import PDEFoundation.Monotonicity.ACF.AssemblyPolar
public import PDEFoundation.Monotonicity.ACF.AssemblyBump
public import PDEFoundation.Monotonicity.ACF.AssemblyAlg

/-!
# ACF-A: the single-function package

For one nonnegative weakly subharmonic `u ∈ H¹(B_R)`, continuous on the ball (`3 ≤ d`), with
`J(r) = ∫₀ʳ dens(u.grad)`:

* `single_energy`: `acfWeightedEnergy u.grad r = ofReal (J r)` and `dens` is interval integrable;
* `single_openSlice`: `{y | 0 < u (r y)} ∩ ∂B₁` is relatively open;
* `single_ae`: for a.e. `r`, `J r > 0` gives a real `t ≥ 0` with
  `eigenvalueDegree λ(Ω(r)) = ofReal t` and `2 t J(r) ≤ r · dens(r)`.
-/

@[expose] public section

open MeasureTheory Set Filter

namespace PDE

namespace ACFAssembly

noncomputable section

variable {d : ℕ} {R : ℝ}

/-- The weighted energy is `ofReal` of the integral of the slice density. -/
theorem single_energy (hd : 3 ≤ d) (u : H1Function (euclideanBall (0 : Vec d) R))
    (hcont : ContinuousOn u.toFun (euclideanBall (0 : Vec d) R))
    (hnn : ∀ x ∈ euclideanBall (0 : Vec d) R, 0 ≤ u.toFun x)
    (hsub : IsWeakDivergenceFormSubharmonicOn (fun _ => (1 : Mat d))
      (euclideanBall (0 : Vec d) R) u) {r : ℝ} (hr : r ∈ Ioo (0 : ℝ) R) :
    acfWeightedEnergy u.grad r = ENNReal.ofReal (∫ ρ in (0 : ℝ)..r, dens u.grad ρ) ∧
      IntervalIntegrable (dens u.grad) volume 0 r := by
  have : NeZero d := ⟨by omega⟩
  have hfin := acfWeightedEnergy_ne_top hd u hcont hnn hsub hr
  exact acfWeightedEnergy_eq hr.1 (integrableOn_weighted u hr.1 hr.2.le hfin)

/-- The positivity set of a slice is relatively open in the sphere. -/
theorem single_openSlice (u : H1Function (euclideanBall (0 : Vec d) R))
    (hcont : ContinuousOn u.toFun (euclideanBall (0 : Vec d) R)) {r : ℝ}
    (hr : r ∈ Ioo (0 : ℝ) R) :
    ∃ U : Set (Vec d), IsOpen U ∧
      {y | 0 < u.toFun (r • y)} ∩ euclideanSphere (0 : Vec d) 1 =
        U ∩ euclideanSphere (0 : Vec d) 1 := by
  have hcs : Continuous (fun y : Vec d => r • y) := continuous_const_smul r
  refine ⟨(fun y : Vec d => r • y) ⁻¹' (euclideanBall (0 : Vec d) R ∩ u.toFun ⁻¹' Ioi 0), ?_, ?_⟩
  · exact (hcont.isOpen_inter_preimage (isOpen_euclideanBall (0 : Vec d) R) isOpen_Ioi).preimage hcs
  · ext y
    constructor
    · rintro ⟨hy, hyS⟩
      exact ⟨⟨smul_mem_ball_of_mem_sphere hr.1.le hr.2 hyS, hy⟩, hyS⟩
    · rintro ⟨⟨_, hy⟩, hyS⟩
      exact ⟨hy, hyS⟩

/-- The a.e. differential inequality for one function. -/
theorem single_ae (hd : 3 ≤ d) (hR : 0 < R) (u : H1Function (euclideanBall (0 : Vec d) R))
    (hcont : ContinuousOn u.toFun (euclideanBall (0 : Vec d) R))
    (hnn : ∀ x ∈ euclideanBall (0 : Vec d) R, 0 ≤ u.toFun x)
    (hsub : IsWeakDivergenceFormSubharmonicOn (fun _ => (1 : Mat d))
      (euclideanBall (0 : Vec d) R) u) :
    ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R)),
      0 < (∫ ρ in (0 : ℝ)..r, dens u.grad ρ) →
      ∃ t : ℝ, 0 ≤ t ∧
        eigenvalueDegree d (sphereDirichletEigenvalue d {y | 0 < u.toFun (r • y)}) =
          ENNReal.ofReal t ∧
        2 * t * (∫ ρ in (0 : ℝ)..r, dens u.grad ρ) ≤ r * dens u.grad r := by
  have : NeZero d := ⟨by omega⟩
  filter_upwards [acf_weighted_bound_ae hd u hcont hnn hsub, slice_rayleigh_ae_ball hR u hcont hnn,
    ae_restrict_mem measurableSet_Ioo] with r hWr hSr hr hJpos
  obtain ⟨-, -, -, hW⟩ := hWr
  obtain ⟨-, hS⟩ := hSr
  set J := ∫ ρ in (0 : ℝ)..r, dens u.grad ρ with hJ
  rw [(single_energy hd u hcont hnn hsub hr).1] at hW
  have hX := ((ENNReal.ofReal_le_ofReal_iff' (p := J)).1 hW).resolve_right (not_le.2 hJpos)
  have ha : 0 ≤ acfSliceMass u.toFun r :=
    sphereIntegral_zero_nonneg hr.1.le fun x _ => sq_nonneg _
  have hb : 0 ≤ acfSliceRadial u.grad r :=
    sphereIntegral_zero_nonneg hr.1.le fun x _ => sq_nonneg _
  have hapos : 0 < acfSliceMass u.toFun r := by
    refine lt_of_le_of_ne ha fun h0 => ?_
    rw [← h0] at hX
    simp only [zero_mul, Real.sqrt_zero, mul_zero, zero_div, add_zero] at hX
    linarith
  obtain ⟨y0, hy0S, hy0⟩ : ∃ y ∈ euclideanSphere (0 : Vec d) 1, 0 < u.toFun (r • y) := by
    by_contra hcon
    push Not at hcon
    refine hapos.ne' ?_
    have : acfSliceMass u.toFun r = sphereIntegral (0 : Vec d) r (fun _ => 0) := by
      refine sphereIntegral_zero_congr fun x hx => ?_
      have hn := vecEuclideanNorm_of_mem_sphere hr.1.le hx
      have hr0 : r ≠ 0 := hr.1.ne'
      have hyS : r⁻¹ • x ∈ euclideanSphere (0 : Vec d) 1 := by
        rw [mem_euclideanSphere_zero_iff, vecNormSq_smul, mem_euclideanSphere_zero_iff.1 hx]
        field_simp
      have hxe : r • (r⁻¹ • x) = x := smul_inv_smul₀ hr0 x
      have h1 := hcon _ hyS
      rw [hxe] at h1
      have hxb : x ∈ euclideanBall (0 : Vec d) R := by
        rw [mem_euclideanBall_zero_iff, mem_euclideanSphere_zero_iff.1 hx]
        nlinarith only [hr.1, hr.2]
      have h2 := hnn x hxb
      have h3 : u.toFun x = 0 := le_antisymm h1 h2
      show u.toFun x ^ 2 = 0
      rw [h3]; norm_num
    rw [this]
    simp [sphereIntegral]
  obtain ⟨U, hU, hUeq⟩ := single_openSlice u hcont hr
  have hy0U : y0 ∈ U ∩ euclideanSphere (0 : Vec d) 1 := by
    rw [← hUeq]; exact ⟨hy0, hy0S⟩
  have hlam : sphereDirichletEigenvalue d {y | 0 < u.toFun (r • y)} ≠ ⊤ := by
    rw [sphereDirichletEigenvalue_congr_inter (Ω' := U ∩ euclideanSphere (0 : Vec d) 1)
      (by rw [hUeq, inter_assoc, inter_self])]
    exact sphereDirichletEigenvalue_ne_top hU hy0U.1 hy0U.2
  obtain ⟨t, ht0, hdeg, htL⟩ := exists_degree_real d hlam
  refine ⟨t, ht0, hdeg, ?_⟩
  have hκ : ((d : ℝ) - 2) = ((d - 2 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]; norm_num
  rw [hκ] at hX
  rw [← htL] at hS
  have := amgm_step (n := d - 2) hr.1 ha hb ht0 hX hS
  rw [dens_eq u.grad hr.1]
  exact this

end

end ACFAssembly

end PDE
