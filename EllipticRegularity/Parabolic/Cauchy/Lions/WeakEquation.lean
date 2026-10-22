module

public import EllipticRegularity.Parabolic.Cauchy.Lions.SliceWeakGradient
public import EllipticRegularity.Parabolic.Chain.Calculus

/-! # The undamped weak equation represented by the Lions pair

The concrete Lions operator contains a positive zero-order term. Multiplying an interior test by
the corresponding exponential converts its operator to the undamped parabolic operator. The same
exponential is then transferred to the value and spatial-gradient components.
-/

@[expose] public section

set_option autoImplicit false

open MeasureTheory Set
open scoped InnerProductSpace

namespace PDE.Parabolic.Lions

/-- The exponential rescaling used to remove the Lions damping. -/
noncomputable def cauchyWeight {d : ℕ} {s : ℝ} (z : Vec d × ℝ) : ℝ :=
  Real.exp (z.2 - s)

/-- The value representative obtained from the damped Lions limit. -/
noncomputable def cauchyEnergyValue {d : ℕ} {s T : ℝ} (u : CauchyX d s T)
    (z : Vec d × ℝ) : ℝ := cauchyWeight (s := s) z * cauchyJointValue u z

/-- The spatial-gradient representative obtained from the damped Lions limit. -/
noncomputable def cauchyEnergyGradient {d : ℕ} {s T : ℝ} (u : CauchyX d s T)
    (z : Vec d × ℝ) : Vec d := cauchyWeight (s := s) z • cauchyJointGradient u z

private theorem cauchy_vecDot_matVecMul_transpose {d : ℕ} (x y : Vec d) (A : Mat d) :
    vecDot x (matVecMul (matTranspose A) y) = vecDot (matVecMul A x) y := by
  calc
    vecDot x (matVecMul (matTranspose A) y) =
      ∑ i : Fin d, ∑ j : Fin d, x i * (A j i * y j) := by
      unfold vecDot matVecMul matTranspose
      congr with i
      rw [Finset.mul_sum]
      simp only [Matrix.transpose_apply]
    _ = ∑ j, ∑ i, (A j i * x i) * y j := by
      rw [Finset.sum_comm]
      congr with j
      congr with i
      ring
    _ = ∑ j, (∑ i, A j i * x i) * y j := by
      congr with j
      exact (Finset.sum_mul Finset.univ (fun i => A j i * x i) (y j)).symm
    _ = vecDot (matVecMul A x) y := rfl

private theorem cauchy_real_inner (x y : ℝ) : inner ℝ x y = x * y := by
  simp [inner]
  ring

private theorem cauchyTimeShift_contDiff {d : ℕ} {s : ℝ} :
    ContDiff ℝ 1 (fun z : Vec d × ℝ => z.2 - s) := by
  have hfst : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec d × ℝ => z.2) := contDiff_snd
  have hc : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec d × ℝ => s) := contDiff_const
  exact (hfst.sub hc).of_le (by norm_num)

private theorem cauchyWeight_contDiff {d : ℕ} {s : ℝ} :
    ContDiff ℝ 1 (cauchyWeight (s := s) : Vec d × ℝ → ℝ) := by
  change ContDiff ℝ 1 (Real.exp ∘ fun z : Vec d × ℝ => z.2 - s)
  have hexpTop : ContDiff ℝ (⊤ : ℕ∞) Real.exp := Real.contDiff_exp
  exact (hexpTop.of_le (by norm_num)).comp cauchyTimeShift_contDiff

private theorem cauchyWeight_timeDeriv {d : ℕ} {s : ℝ} (z : Vec d × ℝ) :
    parTimeDeriv (cauchyWeight (s := s) : Vec d × ℝ → ℝ) z =
      cauchyWeight (s := s) z := by
  have hw := cauchyTimeShift_contDiff (d := d) (s := s)
  have hexp : ContDiff ℝ 1 Real.exp :=
    (Real.contDiff_exp : ContDiff ℝ (⊤ : ℕ∞) Real.exp).of_le (by norm_num)
  change parTimeDeriv (Real.exp ∘ fun y : Vec d × ℝ => y.2 - s) z = _
  rw [PDE.Parabolic.Chain.parTimeDeriv_comp
    hexp hw z]
  simp [cauchyWeight, parTimeDeriv, fderiv_sub_const, fderiv_snd, Real.deriv_exp]

private theorem cauchyWeight_spaceGrad {d : ℕ} {s : ℝ} (z : Vec d × ℝ) :
    parSpaceGrad (cauchyWeight (s := s) : Vec d × ℝ → ℝ) z = 0 := by
  have hw := cauchyTimeShift_contDiff (d := d) (s := s)
  have hexp : ContDiff ℝ 1 Real.exp :=
    (Real.contDiff_exp : ContDiff ℝ (⊤ : ℕ∞) Real.exp).of_le (by norm_num)
  change parSpaceGrad (Real.exp ∘ fun y : Vec d × ℝ => y.2 - s) z = _
  rw [PDE.Parabolic.Chain.parSpaceGrad_comp
    hexp hw z]
  have hwspace : parSpaceGrad (fun y : Vec d × ℝ => y.2 - s) z = 0 := by
    ext i
    simp [parSpaceGrad, fderiv_sub_const, fderiv_snd]
  simp [hwspace]

private theorem cauchyWeightedTestSpaceGrad {d : ℕ} {s : ℝ}
    (φ : Vec d × ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) (z : Vec d × ℝ) :
    parSpaceGrad (fun y => cauchyWeight (s := s) y * φ y) z =
      cauchyWeight (s := s) z • parSpaceGrad φ z := by
  rw [PDE.Parabolic.Chain.parSpaceGrad_mul cauchyWeight_contDiff hφ z,
    cauchyWeight_spaceGrad]
  simp

private theorem cauchyWeightedTestTimeDeriv {d : ℕ} {s : ℝ}
    (φ : Vec d × ℝ → ℝ) (hφ : ContDiff ℝ 1 φ) (z : Vec d × ℝ) :
    parTimeDeriv (fun y => cauchyWeight (s := s) y * φ y) z =
      cauchyWeight (s := s) z * parTimeDeriv φ z +
        cauchyWeight (s := s) z * φ z := by
  rw [PDE.Parabolic.Chain.parTimeDeriv_mul cauchyWeight_contDiff hφ z,
    cauchyWeight_timeDeriv (s := s) z]
  ring

private theorem cauchyWeightedTest_hasCompactSupport {d : ℕ} {s : ℝ}
    {φ : Vec d × ℝ → ℝ} (hφ : HasCompactSupport φ) :
    HasCompactSupport (fun z => cauchyWeight (s := s) z * φ z) := by
  apply HasCompactSupport.of_support_subset_isCompact hφ.isCompact
  intro z hz
  by_contra hzφ
  exact hz (by simp [image_eq_zero_of_notMem_tsupport hzφ])

/-- The Lions representation gives the undamped weak identity, including the initial trace term,
for exponentially rescaled value and gradient fields. -/
theorem cauchyLions_testIdentity {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 (volume : Measure (Vec d)))
    (u : CauchyX d s T)
    (hrep : ∀ ψ : CauchyTestSpace d s T,
      inner ℝ u (cauchyT (c := 1) ha ψ) =
        inner ℝ (hf.toLp f) (cauchyGamma ψ))
    (φ : CauchyTestSpace d s T) :
    ∫ z in (univ : Set (Vec d)) ×ˢ Icc s T,
      -(cauchyEnergyValue u z * parTimeDeriv (φ : Vec d × ℝ → ℝ) z) +
        vecDot (matVecMul (a z) (cauchyEnergyGradient u z))
          (parSpaceGrad (φ : Vec d × ℝ → ℝ) z) =
      ∫ x, f x * (φ : Vec d × ℝ → ℝ) (x, s) := by
  let φfun : Vec d × ℝ → ℝ := φ
  let Φ : CauchyTestSpace d s T := ⟨
    (fun z => cauchyWeight (s := s) z * φfun z), by
      refine ⟨(cauchyWeight_contDiff.mul φ.property.1),
        cauchyWeightedTest_hasCompactSupport φ.property.2.1, ?_⟩
      intro x
      simp [φfun, cauchyWeight, φ.property.2.2 x]
    ⟩
  have htrace : inner ℝ (hf.toLp f) (cauchyGamma Φ) =
      ∫ x, f x * φfun (x, s) := by
    rw [cauchyGamma_apply, MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, (cauchyTraceFun_memLp Φ).coeFn_toLp] with x hx hftrace
    rw [hx, hftrace]
    simp [cauchyTraceFun, Φ, φfun, cauchyWeight]
    ring
  have hTmem := cauchyTFun_memLp (c := 1) ha Φ
  have hinner : inner ℝ u (cauchyT (c := 1) ha Φ) =
      ∫ z, inner ℝ (u z) (cauchyTFun 1 a (Φ : Vec d × ℝ → ℝ) z)
        ∂slabMeasure d s T := by
    rw [cauchyT_apply, MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hTmem.coeFn_toLp] with z hz
    rw [hz]
  have hpoint (z : Vec d × ℝ) :
      inner ℝ (u z) (cauchyTFun 1 a (Φ : Vec d × ℝ → ℝ) z) =
        -(cauchyEnergyValue u z * parTimeDeriv φfun z) +
          vecDot (matVecMul (a z) (cauchyEnergyGradient u z))
            (parSpaceGrad φfun z) := by
    rw [cauchyTFun, WithLp.prod_inner_apply]
    simp only [Φ, cauchyEnergyValue, cauchyEnergyGradient,
      cauchyJointValue, cauchyJointGradient]
    have hspace := cauchyWeightedTestSpaceGrad (s := s) φfun φ.property.1 z
    have htime := cauchyWeightedTestTimeDeriv (s := s) φfun φ.property.1 z
    rw [htime, hspace]
    rw [← PDE.Vec.toHilbertVec_toVec ((u z).ofLp.2), PDE.inner_toHilbertVec_eq_vecDot,
      cauchy_vecDot_matVecMul_transpose]
    have hmatrix : matVecMul (a z) (cauchyWeight (s := s) z • (u z).snd.toVec) =
        cauchyWeight (s := s) z • matVecMul (a z) (u z).snd.toVec := by
      ext i
      simp only [matVecMul, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [hmatrix]
    have hvec (m g : Vec d) (w : ℝ) : vecDot (w • m) g = w * vecDot m g := by
      rw [vecDot_comm, PDE.Parabolic.WeakSlice.vecDot_smul_right', vecDot_comm]
    rw [PDE.Parabolic.WeakSlice.vecDot_smul_right', hvec]
    rw [cauchy_real_inner]
    simp only [WithLp.fst, WithLp.snd]
    ring_nf
  have hglobal : ∫ z, -(cauchyEnergyValue u z * parTimeDeriv φfun z) +
      vecDot (matVecMul (a z) (cauchyEnergyGradient u z))
        (parSpaceGrad φfun z) ∂slabMeasure d s T =
      ∫ x, f x * φfun (x, s) := by
    calc
      ∫ z, -(cauchyEnergyValue u z * parTimeDeriv φfun z) +
          vecDot (matVecMul (a z) (cauchyEnergyGradient u z))
            (parSpaceGrad φfun z) ∂slabMeasure d s T =
        ∫ z, inner ℝ (u z) (cauchyTFun 1 a (Φ : Vec d × ℝ → ℝ) z)
            ∂slabMeasure d s T := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun z => (hpoint z).symm
      _ = inner ℝ u (cauchyT (c := 1) ha Φ) := hinner.symm
      _ = inner ℝ (hf.toLp f) (cauchyGamma Φ) := hrep Φ
      _ = ∫ x, f x * φfun (x, s) := htrace
  simpa only [slabMeasure] using hglobal

/-- Compactly supported interior tests have zero initial trace, so the initial trace identity
specializes to the homogeneous interior weak equation. -/
theorem cauchyLions_interiorWeakEquation {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (hsT : s < T) (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 (volume : Measure (Vec d)))
    (u : CauchyX d s T)
    (hrep : ∀ ψ : CauchyTestSpace d s T,
      inner ℝ u (cauchyT (c := 1) ha ψ) =
        inner ℝ (hf.toLp f) (cauchyGamma ψ))
    (φ : ParTestFunction (univ : Set (Vec d)) (interior (Icc s T))) :
    ∫ z in (univ : Set (Vec d)) ×ˢ Icc s T,
      -(cauchyEnergyValue u z * parTimeDeriv φ.toFun z) +
        vecDot (matVecMul (a z) (cauchyEnergyGradient u z))
          (parSpaceGrad φ.toFun z) = 0 := by
  let ψ : CauchyTestSpace d s T := ⟨φ.toFun, by
    refine ⟨φ.contDiff, φ.hasCompactSupport, ?_⟩
    intro x
    have hTnot : T ∉ interior (Icc s T) := by
      rw [interior_Icc]
      simp [hsT]
    have hznot : (x, T) ∉ tsupport φ.toFun := fun hz => hTnot
      ((φ.tsupport_subset hz).2)
    exact image_eq_zero_of_notMem_tsupport hznot
    ⟩
  have h := cauchyLions_testIdentity ha f hf u hrep ψ
  have htrace : ∀ x : Vec d, (ψ : Vec d × ℝ → ℝ) (x, s) = 0 := by
    intro x
    have hsnot : (x, s) ∉ tsupport φ.toFun := by
      intro hz
      have hsnot' : s ∉ interior (Icc s T) := by
        rw [interior_Icc]
        simp [hsT]
      exact hsnot' ((φ.tsupport_subset hz).2)
    exact image_eq_zero_of_notMem_tsupport hsnot
  have hz : ∫ x, f x * (ψ : Vec d × ℝ → ℝ) (x, s) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards with x
    simp [htrace x]
  simpa [ψ] using h.trans hz

/-- Product tests reduce the Lions identity to a one-dimensional weak equation for every fixed
compactly supported spatial test. The right-hand side is the initial pairing with `f`. -/
theorem cauchyLions_tensorTestIdentity {d : ℕ} {lam Lam s T : ℝ} {a : ParCoeffField d}
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 (volume : Measure (Vec d)))
    (u : CauchyX d s T)
    (hrep : ∀ ψ : CauchyTestSpace d s T,
      inner ℝ u (cauchyT (c := 1) ha ψ) =
        inner ℝ (hf.toLp f) (cauchyGamma ψ))
    (ψ : Vec d → ℝ) (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (θ : ℝ → ℝ) (hθ : ContDiff ℝ 1 θ) (hθc : HasCompactSupport θ)
    (hθT : θ T = 0) :
    ∫ z in (univ : Set (Vec d)) ×ˢ Icc s T,
      -(cauchyEnergyValue u z * (deriv θ z.2 * ψ z.1)) +
        θ z.2 * vecDot (matVecMul (a z) (cauchyEnergyGradient u z))
          (spaceGradC1 ψ z.1) =
      ∫ x, f x * (θ s * ψ x) := by
  let Φ : CauchyTestSpace d s T := ⟨
    (fun z => θ z.2 * ψ z.1), by
      refine ⟨PDE.Parabolic.WeakSlice.contDiff_prod hθ hψ,
        PDE.Parabolic.WeakSlice.hasCompactSupport_prod hθc hψc, ?_⟩
      intro x
      simp [hθT]
    ⟩
  have h := cauchyLions_testIdentity ha f hf u hrep Φ
  have htime (z : Vec d × ℝ) :
      parTimeDeriv (Φ : Vec d × ℝ → ℝ) z = deriv θ z.2 * ψ z.1 := by
    change parTimeDeriv (fun w : Vec d × ℝ => θ w.2 * ψ w.1) z = _
    exact PDE.Parabolic.WeakSlice.parTimeDeriv_prod hθ hψ z
  have hspace (z : Vec d × ℝ) :
      parSpaceGrad (Φ : Vec d × ℝ → ℝ) z = θ z.2 • spaceGradC1 ψ z.1 := by
    change parSpaceGrad (fun w : Vec d × ℝ => θ w.2 * ψ w.1) z = _
    exact PDE.Parabolic.WeakSlice.parSpaceGrad_prod hθ hψ z
  have hrewrite :
      (fun z : Vec d × ℝ =>
        -(cauchyEnergyValue u z * parTimeDeriv (Φ : Vec d × ℝ → ℝ) z) +
          vecDot (matVecMul (a z) (cauchyEnergyGradient u z))
            (parSpaceGrad (Φ : Vec d × ℝ → ℝ) z)) =
      (fun z => -(cauchyEnergyValue u z * (deriv θ z.2 * ψ z.1)) +
        θ z.2 * vecDot (matVecMul (a z) (cauchyEnergyGradient u z))
          (spaceGradC1 ψ z.1)) := by
    funext z
    rw [htime, hspace, PDE.Parabolic.WeakSlice.vecDot_smul_right']
  have htrace : (fun x : Vec d => (Φ : Vec d × ℝ → ℝ) (x, s)) =
      (fun x => θ s * ψ x) := by
    funext x
    rfl
  rw [hrewrite] at h
  calc
    _ = ∫ x, f x * (Φ : Vec d × ℝ → ℝ) (x, s) := h
    _ = ∫ x, f x * (θ s * ψ x) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        change f x * (Φ : Vec d × ℝ → ℝ) (x, s) = f x * (θ s * ψ x)
        rw [congrFun htrace x]

end PDE.Parabolic.Lions
