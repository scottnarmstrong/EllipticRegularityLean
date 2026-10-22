module

public import EllipticRegularity.Parabolic.Cauchy.Duality.MassInverseWeight

/-!
# Mass conservation for compactly supported Cauchy data

An almost-everywhere support condition can be converted into a pointwise
compact-support representative without changing either the initial trace or
the weak solution.
-/

@[expose] public section

namespace PDE.Parabolic.Cauchy.OnDiag

open MeasureTheory Set

/-- A unit-mass datum supported in a translated ball has exact mass at every
time slice of its Cauchy solution.  The support assumption is only almost
everywhere, as in the on-diagonal lower bound. -/
theorem cauchy_unit_mass_conservation_of_ball_support {d : ℕ} {Lam s T ε : ℝ}
    {a : ParCoeffField d} (hsT : s < T)
    (ha : IsParabolicCoeff 1 Lam a univ (Icc s T))
    (y : Vec d) (f : Vec d → ℝ) (hf1 : Integrable f volume)
    (hf2 : MemLp f 2 volume) (hfmass : ∫ x, f x = 1)
    (hfsupp : ∀ᵐ x : Vec d, x ∉ euclideanBall y ε → f x = 0)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) {t : ℝ} (ht : t ∈ Icc s T) :
    Integrable (parSlice u.toFun t) volume ∧
      ∫ x : Vec d, u.toFun (x, t) = 1 := by
  let S : ℝ := vecEuclideanNorm y + |ε|
  let K : Set (Vec d) := euclideanClosedBall 0 S
  let f₀ : Vec d → ℝ := K.indicator f
  have hS : 0 ≤ S := by
    dsimp [S]
    exact add_nonneg (vecEuclideanNorm_nonneg _) (abs_nonneg _)
  have hK : K.Nonempty := by
    refine ⟨0, ?_⟩
    change (0 : Vec d) ∈ euclideanClosedBall 0 S
    rw [mem_euclideanClosedBall_iff_vecEuclideanNorm_le hS]
    simpa [vecEuclideanNorm, vecNormSq, vecDot] using hS
  have hball_subset : euclideanBall y ε ⊆ K := by
    intro x hx
    change vecNormSq (x - y) < ε ^ 2 at hx
    rw [mem_euclideanClosedBall_iff_vecEuclideanNorm_le hS]
    have hdist : vecEuclideanNorm (x - y) ≤ |ε| := by
      rw [← Real.sqrt_sq_eq_abs ε]
      change Real.sqrt (vecNormSq (x - y)) ≤ Real.sqrt (ε ^ 2)
      exact Real.sqrt_le_sqrt hx.le
    have htri : vecEuclideanNorm x ≤ vecEuclideanNorm (x - y) + vecEuclideanNorm y := by
      calc
        vecEuclideanNorm x = vecEuclideanNorm ((x - y) + y) := by
          congr 1
          abel
        _ ≤ vecEuclideanNorm (x - y) + vecEuclideanNorm y := vecEuclideanNorm_add_le _ _
    calc
      vecEuclideanNorm (x - 0) = vecEuclideanNorm x := by simp
      _ ≤ vecEuclideanNorm (x - y) + vecEuclideanNorm y := htri
      _ ≤ |ε| + vecEuclideanNorm y := add_le_add hdist le_rfl
      _ = S := by dsimp [S]; ring
  have hf₀ae : f₀ =ᵐ[volume] f := by
    filter_upwards [hfsupp] with x hx
    by_cases hxK : x ∈ K
    · simp [f₀, hxK]
    · have hxBall : x ∉ euclideanBall y ε := fun h => hxK (hball_subset h)
      simp [f₀, hxK, hx hxBall]
  have hf₀1 : Integrable f₀ volume := hf1.congr hf₀ae.symm
  have hf₀2 : MemLp f₀ 2 volume := (memLp_congr_ae hf₀ae).mpr hf2
  have hf₀mass : ∫ x, f₀ x = 1 := by
    calc
      ∫ x, f₀ x = ∫ x, f x := integral_congr_ae hf₀ae
      _ = 1 := hfmass
  have hu₀ : IsCauchySolution a s T f₀ u := by
    refine ⟨hu.1, ?_⟩
    filter_upwards [hu.2, hf₀ae] with x hx hx₀
    rw [hx, hx₀.symm]
  have hf₀support : ∀ x ∉ euclideanClosedBall (0 : Vec d) S, f₀ x = 0 := by
    intro x hx
    simp [f₀, K, hx]
  have hmass := PDE.Parabolic.Duality.cauchy_mass_of_ball_supported
    hsT ha f₀ hf₀1 hf₀2 hS hf₀support u hu₀ ht
  refine ⟨?_, ?_⟩
  · exact hmass.1
  · calc
      ∫ x : Vec d, u.toFun (x, t) = ∫ x : Vec d, f₀ x := hmass.2
      _ = 1 := hf₀mass

end PDE.Parabolic.Cauchy.OnDiag
