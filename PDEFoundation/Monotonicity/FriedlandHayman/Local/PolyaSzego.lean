module

public import PDEFoundation.Monotonicity.FriedlandHayman.Local.PolyaSzegoCap
public import PDEFoundation.Monotonicity.FriedlandHayman.Symm.Rearrange

/-!
# Friedland--Hayman: the spherical Pólya--Szegő inequality, one-dimensional form

For a `C¹` function `f` on `Vec D` with `∫_S f² > 0` whose nonvanishing set on the unit sphere
has measure strictly less than the whole sphere, the zonal rearrangement `k` of `|f|`
(`exists_zonal_rearrangement`) is `k = h (arccos ⟪·, e₀⟫)` for a Lipschitz profile `h` supported in
`[0, θ₀]`, with the same `L²` norm, a polar cap of no larger measure, and no larger Dirichlet
energy (the nonlocal energy inequality passed to the limit with `nlEnergy_ge_zonal` and
`nlEnergy_le_tgn`).

The hypothesis `hmiss` cannot be dropped: for `f ≡ 1` the conclusion would force a nonzero
profile with `h' = 0` almost everywhere and `h (θ₀) = 0`, which is absurd.
-/

@[expose] public section

open MeasureTheory Filter Topology

namespace PDE.FHLane

noncomputable section

namespace Local

variable {D : ℕ} [NeZero D]

omit [NeZero D] in
theorem sphereIntegral_indicator_ne_zero {f : Vec D → ℝ} (hf : Continuous f) :
    sphereIntegral (0 : Vec D) 1 ({x | f x ≠ 0}.indicator fun _ => (1 : ℝ)) =
      (sphMeasure D).real {x : Sph D | 0 < absRestrict f hf x} := by
  have hmeas : MeasurableSet {x : Sph D | 0 < absRestrict f hf x} :=
    (isOpen_lt continuous_const (absRestrict f hf).continuous).measurableSet
  rw [sphereIntegral_unit, ← integral_indicator_one hmeas]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  by_cases hx : f (x : HilbertVec D).toVec = 0
  · have : x ∉ {x : Sph D | 0 < absRestrict f hf x} := by
      simp [absRestrict_apply, hx]
    simp [Set.indicator_of_notMem this, hx]
  · have : x ∈ {x : Sph D | 0 < absRestrict f hf x} := by
      simp [absRestrict_apply, hx]
    simp [Set.indicator_of_mem this, hx]

end Local

open Local

/-- Spherical Pólya--Szegő inequality in one-dimensional form, for functions whose nonvanishing
set on the sphere misses a set of positive measure. -/
theorem polya_szego_one_dim_of_miss {D : ℕ} (hD : 3 ≤ D) [NeZero D] {f : Vec D → ℝ}
    (hf : ContDiff ℝ 1 f) (hI : 0 < sphereIntegral (0 : Vec D) 1 (fun x => f x ^ 2))
    (hmiss : sphereIntegral (0 : Vec D) 1 ({x | f x ≠ 0}.indicator fun _ => (1 : ℝ)) <
      sphereArea D) :
    ∃ (h : ℝ → ℝ) (K : NNReal) (θ₀ : ℝ), LipschitzWith K h ∧ θ₀ ∈ Set.Ioc 0 Real.pi ∧
      (∀ φ, θ₀ ≤ φ → h φ = 0) ∧
      capFrac D θ₀ * sphereArea D ≤
        sphereIntegral (0 : Vec D) 1 ({x | f x ≠ 0}.indicator fun _ => (1 : ℝ)) ∧
      sphereArea (D - 1) * ∫ φ in (0 : ℝ)..Real.pi, h φ ^ 2 * sinW D φ =
        sphereIntegral (0 : Vec D) 1 (fun x => f x ^ 2) ∧
      sphereArea (D - 1) * ∫ φ in (0 : ℝ)..Real.pi, deriv h φ ^ 2 * sinW D φ ≤
        sphereIntegral (0 : Vec D) 1 (tangentialGradientNormSq f) := by
  have hD2 : 2 ≤ D := by omega
  set g := absRestrict f hf.continuous with hg
  obtain ⟨L, hL⟩ := lipschitz_absRestrict hf
  have hg0 : ∀ x, 0 ≤ g x := fun x => abs_nonneg _
  obtain ⟨k, hk0, hkL, hkmono, hk2, hkE, hkpos⟩ :=
    exists_zonal_rearrangement hD2 g hg0 hL (norm_pole D)
  obtain ⟨h, K, hh, hkh, hh0, hhanti, hhπ⟩ := exists_profile hD2 k hkL hk0 hkmono
  have hind := sphereIntegral_indicator_ne_zero (D := D) hf.continuous
  have hkint : ∫ x : Sph D, k x ^ 2 ∂(sphMeasure D) =
      sphereIntegral (0 : Vec D) 1 (fun x => f x ^ 2) := by
    rw [hk2, sphereIntegral_unit]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    show (absRestrict f hf.continuous x) ^ 2 = f _ ^ 2
    rw [absRestrict_apply, sq_abs]
  -- the profile vanishes at `π`
  have hπ0 : h Real.pi = 0 := by
    by_contra hne
    have hpos : 0 < h Real.pi := lt_of_le_of_ne (hh0 _) (Ne.symm hne)
    set z : Sph D := meridian hD2 Real.pi with hz
    have hzin : inner ℝ (z : HilbertVec D) (pole D) = -1 := by
      rw [hz, inner_meridian_pole, Real.cos_pi]
    have hkz : k z = h Real.pi := by
      rw [hkh z, hzin, ← Real.cos_pi, Real.arccos_cos Real.pi_pos.le le_rfl]
    have hall : (Set.univ : Set (Sph D)) ⊆ {x | 0 < k x} := fun x _ => by
      refine lt_of_lt_of_le ?_ (hkmono z x (by rw [hzin]; exact neg_one_le_inner x))
      rw [hkz]; exact hpos
    have h1 : (sphMeasure D).real Set.univ ≤ (sphMeasure D).real {x | 0 < g x} :=
      ENNReal.toReal_mono (measure_ne_top _ _) ((measure_mono hall).trans hkpos)
    rw [← hind, ← sphereArea_eq_real_univ] at h1
    exact absurd hmiss (not_lt.2 h1)
  -- the support threshold
  set S : Set ℝ := {φ | φ ∈ Set.Icc 0 Real.pi ∧ h φ = 0} with hS
  have hSne : S.Nonempty := ⟨Real.pi, ⟨Real.pi_pos.le, le_rfl⟩, hπ0⟩
  have hSbdd : BddBelow S := ⟨0, fun φ hφ => hφ.1.1⟩
  have hSc : IsClosed S :=
    show IsClosed (Set.Icc 0 Real.pi ∩ {φ | h φ = 0}) from
      isClosed_Icc.inter (isClosed_eq hh.continuous continuous_const)
  have hθS : sInf S ∈ S := hSc.csInf_mem hSne hSbdd
  set θ₀ := sInf S with hθ₀
  have hz : ∀ φ, θ₀ ≤ φ → h φ = 0 := by
    intro φ hφ
    by_cases hφπ : φ ≤ Real.pi
    · have := hhanti θ₀ φ hθS.1.1 hφ hφπ
      rw [hθS.2] at this
      exact le_antisymm this (hh0 φ)
    · rw [hhπ φ (not_le.1 hφπ).le, hπ0]
  have hpos : ∀ φ, 0 ≤ φ → φ < θ₀ → 0 < h φ := by
    intro φ hφ0 hφ
    refine lt_of_le_of_ne (hh0 φ) fun h0 => ?_
    have hφπ : φ ≤ Real.pi := (hφ.trans_le hθS.1.2).le
    exact absurd (csInf_le hSbdd ⟨⟨hφ0, hφπ⟩, h0.symm⟩) (not_le.2 hφ)
  have hθpos : 0 < θ₀ := by
    rcases hθS.1.1.lt_or_eq with h' | h'
    · exact h'
    · exfalso
      have hk00 : ∀ x : Sph D, k x = 0 := fun x => by
        rw [hkh x]
        exact hz _ (by rw [← h']; exact Real.arccos_nonneg _)
      have : ∫ x : Sph D, k x ^ 2 ∂(sphMeasure D) = 0 := by simp [hk00]
      rw [hkint] at this
      exact hI.ne' this
  have hθπ : θ₀ ≤ Real.pi := hθS.1.2
  have hkset : {x : Sph D | Real.arccos (inner ℝ (x : HilbertVec D) (pole D)) < θ₀} =
      {x | 0 < k x} := by
    ext x
    simp only [Set.mem_ofPred_eq]
    rw [hkh x]
    constructor
    · intro hx
      exact hpos _ (Real.arccos_nonneg _) hx
    · intro hx
      by_contra hge
      rw [hz _ (not_lt.1 hge)] at hx
      exact lt_irrefl _ hx
  refine ⟨h, K, θ₀, hh, ⟨hθpos, hθπ⟩, hz, ?_, ?_, ?_⟩
  · rw [capFrac_mul_sphereArea hD2, ← real_measure_arccos_lt hD2 hθπ hθpos, hind, hkset]
    exact ENNReal.toReal_mono (measure_ne_top _ _) hkpos
  · have hbd : ∀ φ, φ ∈ Set.Icc 0 Real.pi → |h φ ^ 2| ≤ h 0 ^ 2 := by
      intro φ hφ
      rw [abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (hh0 φ) (hhanti 0 φ le_rfl hφ.1 hφ.2) 2
    have key := integral_profile (D := D) hD2 (h := fun φ => h φ ^ 2)
      (hh.continuous.pow 2).measurable hbd
    rw [← hkint]
    simp_rw [← hkh] at key
    rw [← key]
  · simp only [sinW]
    refine le_of_forall_pos_le_add fun η hη => ?_
    have hη2 : 0 < η / 2 := half_pos hη
    have e1 := nlEnergy_ge_zonal hD2 k hh hkh hη2
    have e2 := nlEnergy_le_tgn hD2 hf hη2
    obtain ⟨ε, h1, h2, h3⟩ := (e1.and (e2.and (Ioo_mem_nhdsGT Real.pi_pos))).exists
    have hm := capMom_pos hD2 h3.1 h3.2
    have h4 := (h1.trans (hkE ε)).trans
      ((nlEnergy_abs_le hf.continuous ε).trans h2)
    have h5 : (sphereArea (D - 1) * (∫ φ in (0 : ℝ)..Real.pi, deriv h φ ^ 2 * Real.sin φ ^ (D - 2))
        - η / 2) ≤ sphereIntegral (0 : Vec D) 1 (tangentialGradientNormSq f) + η / 2 :=
      le_of_mul_le_mul_right h4 hm
    linarith

end

end PDE.FHLane
