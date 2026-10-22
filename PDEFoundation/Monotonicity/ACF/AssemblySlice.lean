module

public import PDEFoundation.Monotonicity.ACF.AssemblyCutoff

/-!
# ACF-A: the slice Rayleigh bound on the ball

For `u ∈ H¹(B_R)` continuous and nonnegative on the open ball: for a.e. `r ∈ (0, R)` the slice of
`|∇u|²` is integrable and `b(r) + λ(Ω(r)) r⁻² a(r) ≤ c(r)`, where `Ω(r) = {y | 0 < u(r y)}`.
-/

@[expose] public section

open MeasureTheory Set Filter

namespace PDE

namespace ACFAssembly

noncomputable section

variable {d : ℕ}

theorem smul_mem_ball_of_mem_sphere {r R' : ℝ} (hr0 : 0 ≤ r) (hr : r < R') {y : Vec d}
    (hy : y ∈ euclideanSphere (0 : Vec d) 1) : r • y ∈ euclideanBall (0 : Vec d) R' := by
  rw [mem_euclideanBall_zero_iff, vecNormSq_smul, mem_euclideanSphere_zero_iff.1 hy]
  nlinarith only [hr0, hr]

/-- **Slice Rayleigh bound on the ball** (a.e. `r ∈ (0, R)`). -/
theorem slice_rayleigh_ae_ball [NeZero d] {R : ℝ} (hR : 0 < R)
    (u : H1Function (euclideanBall (0 : Vec d) R))
    (hcont : ContinuousOn u.toFun (euclideanBall (0 : Vec d) R))
    (hnn : ∀ x ∈ euclideanBall (0 : Vec d) R, 0 ≤ u.toFun x) :
    ∀ᵐ r ∂(volume.restrict (Ioo (0 : ℝ) R)),
      SphereIntegrable r (fun x => vecNormSq (u.grad x)) ∧
      acfSliceRadial u.grad r +
          (sphereDirichletEigenvalue d {y | 0 < u.toFun (r • y)}).toReal * (r ^ 2)⁻¹ *
            acfSliceMass u.toFun r ≤ acfSliceGrad u.grad r := by
  refine ae_Ioo_of_exhaustion hR fun R' hR' hRR' => ?_
  have hv := acf_slice_rayleigh_interface hR' (cutoffH1 u hR' hRR')
    (continuous_cutoffH1 u hcont hR' hRR') (nonneg_cutoffH1 u hnn hR' hRR')
  filter_upwards [hv, ae_restrict_mem measurableSet_Ioo] with r ⟨h1, h2⟩ hr
  have hf : ∀ x ∈ euclideanBall (0 : Vec d) R',
      (cutoffH1 u hR' hRR').toFun x = u.toFun x := fun x hx => cutoffH1_toFun_eq u hR' hRR' hx
  have hg : ∀ x ∈ euclideanBall (0 : Vec d) R',
      (cutoffH1 u hR' hRR').grad x = u.grad x := fun x hx => cutoffH1_grad_eq u hR' hRR' hx
  have e1 : ∀ x ∈ euclideanBall (0 : Vec d) R',
      vecNormSq ((cutoffH1 u hR' hRR').grad x) = vecNormSq (u.grad x) := fun x hx => by
    rw [hg x hx]
  have e2 : ∀ x ∈ euclideanBall (0 : Vec d) R',
      radialDeriv (cutoffH1 u hR' hRR').grad x ^ 2 = radialDeriv u.grad x ^ 2 := fun x hx => by
    simp only [radialDeriv, hg x hx]
  have e3 : ∀ x ∈ euclideanBall (0 : Vec d) R',
      (cutoffH1 u hR' hRR').toFun x ^ 2 = u.toFun x ^ 2 := fun x hx => by
    rw [hf x hx]
  refine ⟨sphereIntegrable_congr_ball hr.1.le hr.2 e1 h1, ?_⟩
  have hlam : sphereDirichletEigenvalue d {y | 0 < (cutoffH1 u hR' hRR').toFun (r • y)} =
      sphereDirichletEigenvalue d {y | 0 < u.toFun (r • y)} := by
    refine sphereDirichletEigenvalue_congr_inter ?_
    ext y
    constructor
    · rintro ⟨hy, hyS⟩
      refine ⟨?_, hyS⟩
      have := smul_mem_ball_of_mem_sphere hr.1.le hr.2 hyS
      simpa only [mem_ofPred_eq, hf _ this] using hy
    · rintro ⟨hy, hyS⟩
      refine ⟨?_, hyS⟩
      have := smul_mem_ball_of_mem_sphere hr.1.le hr.2 hyS
      simpa only [mem_ofPred_eq, hf _ this] using hy
  rw [hlam] at h2
  have s1 := sphereIntegral_congr_ball hr.1.le hr.2 e1
  have s2 := sphereIntegral_congr_ball hr.1.le hr.2 e2
  have s3 := sphereIntegral_congr_ball hr.1.le hr.2 e3
  change sphereIntegral (0 : Vec d) r (fun x => radialDeriv u.grad x ^ 2) +
      _ * (r ^ 2)⁻¹ * sphereIntegral (0 : Vec d) r (fun x => u.toFun x ^ 2) ≤
      sphereIntegral (0 : Vec d) r (fun x => vecNormSq (u.grad x))
  rw [← s1, ← s2, ← s3]
  exact h2

end

end ACFAssembly

end PDE
