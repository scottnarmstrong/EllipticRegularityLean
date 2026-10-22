/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import EllipticRegularity.Parabolic.Cauchy.Energy.GlobalIdentity
public import EllipticRegularity.Parabolic.Energy.Slab
public import PDEFoundation.Sobolev.H1.Algebra
public import PDEFoundation.Sobolev.Ch4.Truncation

/-! # Uniqueness of whole-space Cauchy energy solutions -/

@[expose] public section

namespace PDE.Parabolic.Cauchy.Energy

open MeasureTheory Set

private theorem matVecMul_sub {d : ℕ} (A : Mat d) (x y : Vec d) :
    matVecMul A (x - y) = matVecMul A x - matVecMul A y := by
  ext i
  simp [matVecMul, Finset.sum_sub_distrib, mul_sub]

private theorem vecDot_sub_right {d : ℕ} (x y z : Vec d) :
    vecDot x (y - z) = vecDot x y - vecDot x z := by
  simp [vecDot, Finset.sum_sub_distrib, mul_sub]

private theorem vecDot_sub_left {d : ℕ} (x y z : Vec d) :
    vecDot (x - y) z = vecDot x z - vecDot y z := by
  rw [vecDot_comm (x - y) z, vecDot_comm x z, vecDot_comm y z]
  exact vecDot_sub_right z x y

theorem ae_slice_memLp {d : ℕ} {s T : ℝ} {g : Vec d × ℝ → ℝ}
    (hg : MemLp g 2 (volume.restrict ((univ : Set (Vec d)) ×ˢ Icc s T))) :
    ∀ᵐ t ∂(volume.restrict (Icc s T)), MemLp (fun x : Vec d => g (x, t)) 2 volume := by
  have h := PDE.Parabolic.Energy.ae_slice_memLp (K1 := (univ : Set (Vec d)))
    MeasurableSet.univ hg
  filter_upwards [h] with t ht
  simpa using ht

/-- The difference of two parabolic energy functions. -/
noncomputable def cauchyParH1Sub {d : ℕ} {s T : ℝ}
    (u v : ParH1Function (univ : Set (Vec d)) (Icc s T)) :
    ParH1Function (univ : Set (Vec d)) (Icc s T) := by
  refine {
    toFun := u.toFun - v.toFun
    grad := u.grad - v.grad
    memL2 := u.memL2.sub v.memL2
    gradMemL2 := fun i => (u.gradMemL2 i).sub (v.gradMemL2 i)
    sliceWeakGradient := ?_
    sliceL2loc := ?_
    weakCont := ?_ }
  · have huVal := ae_slice_memLp u.memL2
    have hvVal := ae_slice_memLp v.memL2
    have huGrad : ∀ i : Fin d, ∀ᵐ t ∂(volume.restrict (Icc s T)),
        MemLp (fun x : Vec d => u.grad (x, t) i) 2 volume := by
      intro i
      exact ae_slice_memLp (g := fun z => u.grad z i) (u.gradMemL2 i)
    have hvGrad : ∀ i : Fin d, ∀ᵐ t ∂(volume.restrict (Icc s T)),
        MemLp (fun x : Vec d => v.grad (x, t) i) 2 volume := by
      intro i
      exact ae_slice_memLp (g := fun z => v.grad z i) (v.gradMemL2 i)
    filter_upwards [u.sliceWeakGradient, v.sliceWeakGradient, huVal, hvVal,
      (ae_all_iff.mpr huGrad), (ae_all_iff.mpr hvGrad)] with t huW hvW huV hvV huG hvG
    let U : H1Function (univ : Set (Vec d)) := {
      toFun := fun x => u.toFun (x, t)
      grad := fun x => u.grad (x, t)
      memL2 := by simpa [MemL2On, MemLpOn, volumeOn] using huV
      gradMemL2 := by
        intro i
        simpa [GradMemL2On, MemLpOn, volumeOn] using huG i
      hasWeakGradient := by
        exact huW }
    let V : H1Function (univ : Set (Vec d)) := {
      toFun := fun x => v.toFun (x, t)
      grad := fun x => v.grad (x, t)
      memL2 := by simpa [MemL2On, MemLpOn, volumeOn] using hvV
      gradMemL2 := by
        intro i
        simpa [GradMemL2On, MemLpOn, volumeOn] using hvG i
      hasWeakGradient := by
        exact hvW }
    have hsubW := U.hasWeakGradient.sub V.hasWeakGradient
      (U.memL2.locallyIntegrable (by norm_num))
      (V.memL2.locallyIntegrable (by norm_num))
      (fun i => (U.gradMemL2 i).locallyIntegrable (by norm_num))
      (fun i => (V.gradMemL2 i).locallyIntegrable (by norm_num))
    change HasWeakGradientOn (univ : Set (Vec d))
      ((fun x => u.toFun (x, t)) - (fun x => v.toFun (x, t)))
      ((fun x => u.grad (x, t)) - (fun x => v.grad (x, t)))
    exact hsubW
  · intro t ht K hKc hKU
    exact (u.sliceL2loc t ht K hKc hKU).sub (v.sliceL2loc t ht K hKc hKU)
  · intro ψ hψ
    rcases hψ with ⟨hψL2, K, hKc, hKU, hψ0⟩
    have hψK : MemLp ψ 2 (volume.restrict K) :=
      hψL2.mono_measure (Measure.restrict_mono hKU le_rfl)
    have hcontU := u.weakCont ψ ⟨hψL2, K, hKc, hKU, hψ0⟩
    have hcontV := v.weakCont ψ ⟨hψL2, K, hKc, hKU, hψ0⟩
    refine (hcontU.sub hcontV).congr ?_
    intro t ht
    have huK := u.sliceL2loc t ht K hKc hKU
    have hvK := v.sliceL2loc t ht K hKc hKU
    have huProdK : IntegrableOn (fun x : Vec d => u.toFun (x, t) * ψ x) K :=
      PDE.integrableOn_mul_of_memL2On huK hψK
    have hvProdK : IntegrableOn (fun x : Vec d => v.toFun (x, t) * ψ x) K :=
      PDE.integrableOn_mul_of_memL2On hvK hψK
    have huProd : IntegrableOn (fun x : Vec d => u.toFun (x, t) * ψ x) univ :=
      huProdK.of_forall_sdiff_eq_zero MeasurableSet.univ (by
        intro x hx
        simp [hψ0 x hx.2])
    have hvProd : IntegrableOn (fun x : Vec d => v.toFun (x, t) * ψ x) univ :=
      hvProdK.of_forall_sdiff_eq_zero MeasurableSet.univ (by
        intro x hx
        simp [hψ0 x hx.2])
    calc
      (∫ x in (univ : Set (Vec d)), (u.toFun (x, t) - v.toFun (x, t)) * ψ x) =
          ∫ x in (univ : Set (Vec d)),
            (u.toFun (x, t) * ψ x - v.toFun (x, t) * ψ x) := by
              apply integral_congr_ae
              exact ae_of_all _ fun x => by ring
      _ = (∫ x in (univ : Set (Vec d)), u.toFun (x, t) * ψ x) -
          ∫ x in (univ : Set (Vec d)), v.toFun (x, t) * ψ x := by
            exact integral_sub huProd hvProd

/-- A difference of Cauchy solutions is a Cauchy solution with the difference datum. -/
theorem cauchyDifference_isSolution {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (_hsT : s < T)
    (_ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    {f g : Vec d → ℝ} {u v : ParH1Function (univ : Set (Vec d)) (Icc s T)}
    (hu : IsCauchySolution a s T f u) (hv : IsCauchySolution a s T g v) :
    IsCauchySolution a s T (f - g) (cauchyParH1Sub u v) := by
  refine ⟨?_, ?_⟩
  · intro φ
    have hU := hu.1 φ
    have hV := hv.1 φ
    have hEqPoint : ∀ z, parWeakIntegrand a (cauchyParH1Sub u v) φ.toFun z =
        parWeakIntegrand a u φ.toFun z - parWeakIntegrand a v φ.toFun z := by
      intro z
      simp [parWeakIntegrand, cauchyParH1Sub, matVecMul_sub, vecDot_sub_left,
        sub_mul]
      ring
    have hEq : parWeakIntegrand a (cauchyParH1Sub u v) φ.toFun =ᵐ[
        volume.restrict ((univ : Set (Vec d)) ×ˢ Icc s T)]
        (parWeakIntegrand a u φ.toFun - parWeakIntegrand a v φ.toFun) :=
      ae_of_all _ hEqPoint
    have hInt : IntegrableOn (parWeakIntegrand a (cauchyParH1Sub u v) φ.toFun)
        ((univ : Set (Vec d)) ×ˢ Icc s T) := by
      exact (hU.1.sub hV.1).congr hEq.symm
    refine ⟨hInt, ?_⟩
    calc
      ∫ z in (univ : Set (Vec d)) ×ˢ Icc s T,
          parWeakIntegrand a (cauchyParH1Sub u v) φ.toFun z =
        ∫ z in (univ : Set (Vec d)) ×ˢ Icc s T,
          (parWeakIntegrand a u φ.toFun z - parWeakIntegrand a v φ.toFun z) :=
            integral_congr_ae hEq
      _ = (∫ z in (univ : Set (Vec d)) ×ˢ Icc s T, parWeakIntegrand a u φ.toFun z) -
          ∫ z in (univ : Set (Vec d)) ×ˢ Icc s T, parWeakIntegrand a v φ.toFun z :=
            integral_sub hU.1 hV.1
      _ = 0 := by rw [hU.2, hV.2, sub_self]
  · change ∀ᵐ x : Vec d, u.toFun (x, s) - v.toFun (x, s) = f x - g x
    filter_upwards [hu.2, hv.2] with x hux hvx
    rw [hux, hvx]

/-- Uniqueness for the Cauchy problem follows from global energy contraction. -/
theorem cauchyUniqueness (d : ℕ) (lam Lam : ℝ) (a : ParCoeffField d)
    (s T : ℝ) (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (f : Vec d → ℝ)
    (_hf : MemLp f 2 volume)
    (u v : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) (hv : IsCauchySolution a s T f v) :
    (∀ t ∈ Icc s T, ∀ᵐ x : Vec d, u.toFun (x, t) = v.toFun (x, t)) ∧
      ∀ᵐ z ∂(volume.restrict ((univ : Set (Vec d)) ×ˢ Icc s T)),
        u.grad z = v.grad z := by
  let w := cauchyParH1Sub u v
  have hw : IsCauchySolution a s T (fun _ : Vec d => 0) w := by
    have hdiff := cauchyDifference_isSolution hsT ha hu hv
    refine ⟨?_, ?_⟩
    · simpa [w] using hdiff.1
    · change ∀ᵐ x : Vec d, u.toFun (x, s) - v.toFun (x, s) = 0
      filter_upwards [hu.2, hv.2] with x hux hvx
      rw [hux, hvx]
      simp
  constructor
  · intro t ht
    have hreal := cauchy_energy_identity_real hsT ha (fun _ : Vec d => 0)
      MemLp.zero w hw ht
    have hEq : (∫ x : Vec d, w.toFun (x, t) ^ 2) +
        2 * ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
          cauchyEnergyDensity a w z = 0 := by
      simpa using hreal
    have hU : 0 ≤ ∫ x : Vec d, w.toFun (x, t) ^ 2 :=
      integral_nonneg fun x => sq_nonneg _
    have hQsub : (univ : Set (Vec d)) ×ˢ Ioc s t ⊆
        (univ : Set (Vec d)) ×ˢ Icc s T :=
      prod_mono subset_rfl fun τ hτ => ⟨hτ.1.le, hτ.2.trans ht.2⟩
    have hQae : ∀ᵐ z ∂(volume.restrict ((univ : Set (Vec d)) ×ˢ Ioc s t)),
        0 ≤ cauchyEnergyDensity a w z :=
      (cauchyEnergyDensity_nonneg_ae ha w).filter_mono
        (ae_mono (Measure.restrict_mono hQsub le_rfl))
    have hQ : 0 ≤ ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s t,
        cauchyEnergyDensity a w z := setIntegral_nonneg_of_ae_restrict hQae
    have hUzero : ∫ x : Vec d, w.toFun (x, t) ^ 2 = 0 := by nlinarith
    have hUint := cauchy_slice_square_integrable hsT ha (fun _ : Vec d => 0)
      MemLp.zero w hw ht
    have hUae := (integral_eq_zero_iff_of_nonneg_ae
      (ae_of_all _ fun x => sq_nonneg (w.toFun (x, t))) hUint).mp hUzero
    filter_upwards [hUae] with x hx
    have hx' : w.toFun (x, t) = 0 := by
      apply sq_eq_zero_iff.mp
      simpa using hx
    change u.toFun (x, t) = v.toFun (x, t)
    exact sub_eq_zero.mp hx'
  · have hreal := cauchy_energy_identity_real hsT ha (fun _ : Vec d => 0)
      MemLp.zero w hw ⟨hsT.le, le_rfl⟩
    have hQ : 0 ≤ ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s T,
        cauchyEnergyDensity a w z := by
      apply setIntegral_nonneg_of_ae_restrict
      have hsub : (univ : Set (Vec d)) ×ˢ Ioc s T ⊆
          (univ : Set (Vec d)) ×ˢ Icc s T :=
        prod_mono subset_rfl Ioc_subset_Icc_self
      exact (cauchyEnergyDensity_nonneg_ae ha w).filter_mono
        (ae_mono (Measure.restrict_mono hsub le_rfl))
    have hQzero : ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s T,
        cauchyEnergyDensity a w z = 0 := by
      have hU : 0 ≤ ∫ x : Vec d, w.toFun (x, T) ^ 2 :=
        integral_nonneg fun x => sq_nonneg _
      have hEq : (∫ x : Vec d, w.toFun (x, T) ^ 2) +
          2 * ∫ z in (univ : Set (Vec d)) ×ˢ Ioc s T,
            cauchyEnergyDensity a w z = 0 := by simpa using hreal
      nlinarith
    have hQint : Integrable (cauchyEnergyDensity a w)
        (volume.restrict ((univ : Set (Vec d)) ×ˢ Ioc s T)) := by
      exact cauchyEnergyDensity_integrable_Ioc ha w ⟨hsT.le, le_rfl⟩
    have hQae : ∀ᵐ z ∂(volume.restrict ((univ : Set (Vec d)) ×ˢ Ioc s T)),
        cauchyEnergyDensity a w z = 0 := by
      apply (integral_eq_zero_iff_of_nonneg_ae
        ((cauchyEnergyDensity_nonneg_ae ha w).filter_mono
          (ae_mono (Measure.restrict_mono
            (prod_mono subset_rfl Ioc_subset_Icc_self) le_rfl))) hQint).mp
      simpa using hQzero
    have hQsub : (univ : Set (Vec d)) ×ˢ Ioc s T ⊆
        (univ : Set (Vec d)) ×ˢ Icc s T :=
      prod_mono subset_rfl Ioc_subset_Icc_self
    have hEll : ∀ᵐ z ∂(volume.restrict ((univ : Set (Vec d)) ×ˢ Ioc s T)),
        IsEllipticMatrix lam Lam (a z) :=
      ha.elliptic.filter_mono (ae_mono (Measure.restrict_mono hQsub le_rfl))
    have hgradZero : ∀ᵐ z ∂(volume.restrict ((univ : Set (Vec d)) ×ˢ Ioc s T)),
        w.grad z = 0 := by
      filter_upwards [hQae, hEll] with z hz hza
      have hnorm : vecNormSq (w.grad z) = 0 := by
        have hcoercive := hza.coercive (w.grad z)
        have hle : lam * vecNormSq (w.grad z) ≤ 0 := by
          simpa [cauchyEnergyDensity] using hcoercive.trans_eq hz
        have hnormnn := vecNormSq_nonneg (w.grad z)
        nlinarith [hza.lam_pos]
      have hcoord : ∀ i : Fin d, w.grad z i = 0 := by
        intro i
        have hle := sq_apply_le_vecNormSq (w.grad z) i
        rw [hnorm] at hle
        nlinarith [sq_nonneg (w.grad z i)]
      ext i
      exact hcoord i
    have hSlabCover : (univ : Set (Vec d)) ×ˢ Icc s T ⊆
        ((univ : Set (Vec d)) ×ˢ Ioc s T) ∪
          ((univ : Set (Vec d)) ×ˢ {s}) := by
      intro z hz
      rcases lt_or_eq_of_le hz.2.1 with h | h
      · exact Or.inl ⟨hz.1, ⟨h, hz.2.2⟩⟩
      · exact Or.inr ⟨hz.1, Set.mem_singleton_iff.mpr h.symm⟩
    have hEndpointNull : volume ((univ : Set (Vec d)) ×ˢ ({s} : Set ℝ)) = 0 := by
      rw [Measure.volume_eq_prod, Measure.prod_prod]
      simp
    have hgradZeroSlab : ∀ᵐ z ∂(volume.restrict
        ((univ : Set (Vec d)) ×ˢ Icc s T)), w.grad z = 0 := by
      refine ae_restrict_of_ae_restrict_of_subset hSlabCover ?_
      rw [ae_restrict_union_iff]
      constructor
      · exact hgradZero
      · rw [Measure.restrict_eq_zero.2 hEndpointNull]
        simp
    filter_upwards [hgradZeroSlab] with z hz
    change u.grad z - v.grad z = 0 at hz
    exact sub_eq_zero.mp hz

end PDE.Parabolic.Cauchy.Energy
