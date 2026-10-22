module

public import EllipticRegularity.Parabolic.Cauchy.Duality.MassInverseWeight
public import EllipticRegularity.Parabolic.Cauchy.Energy.Uniqueness

@[expose] public section

namespace PDE.Parabolic.Duality

open MeasureTheory Set Filter Topology

/-- Mass conservation passes from compactly supported approximating data to a given solution when
both the data and their solutions converge in the `L¹` contraction norm. -/
theorem cauchy_mass_of_ball_supported_approximations {d : ℕ} {lam Lam : ℝ}
    {a : ParCoeffField d} {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T)) (f : Vec d → ℝ)
    (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u) (fn : ℕ → Vec d → ℝ)
    (un : (n : ℕ) → ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hfn1 : ∀ n, Integrable (fn n) volume)
    (hfn2 : ∀ n, MemLp (fn n) 2 volume)
    (hfnSupport : ∀ n, ∃ S : ℝ, 0 ≤ S ∧
      ∀ x ∉ euclideanClosedBall (0 : Vec d) S, fn n x = 0)
    (hun : ∀ n, IsCauchySolution a s T (fn n) (un n))
    (happrox : Tendsto (fun n => eLpNorm (fn n - f) 1 volume) atTop (𝓝 0))
    {t : ℝ} (ht : t ∈ Icc s T) :
    Integrable (parSlice u.toFun t) volume ∧
      ∫ x, u.toFun (x, t) = ∫ x, f x := by
  have huL1 := PDE.Parabolic.Cauchy.L1.cauchyL1Contraction d lam Lam a s T hsT ha
    f hf1 hf2 u hu t ht
  have hball : ∀ n, Integrable (parSlice (un n).toFun t) volume ∧
      ∫ x, (un n).toFun (x, t) = ∫ x, fn n x := by
    intro n
    obtain ⟨S, hS, hSsupport⟩ := hfnSupport n
    exact cauchy_mass_of_ball_supported hsT ha (fn n) (hfn1 n) (hfn2 n)
      hS hSsupport (un n) (hun n) ht
  have hdiffSol : ∀ n, IsCauchySolution a s T (fn n - f)
      (PDE.Parabolic.Cauchy.Energy.cauchyParH1Sub (un n) u) := by
    intro n
    exact PDE.Parabolic.Cauchy.Energy.cauchyDifference_isSolution hsT ha (hun n) hu
  have hdiffInt : ∀ n, Integrable (fn n - f) volume := fun n => (hfn1 n).sub hf1
  have hdiffMem : ∀ n, MemLp (fn n - f) 2 volume := fun n => (hfn2 n).sub hf2
  have hcontract : ∀ n, eLpNorm
      (parSlice (PDE.Parabolic.Cauchy.Energy.cauchyParH1Sub (un n) u).toFun t)
      1 volume ≤ eLpNorm (fn n - f) 1 volume := by
    intro n
    exact (PDE.Parabolic.Cauchy.L1.cauchyL1Contraction d lam Lam a s T hsT ha
      (fn n - f) (hdiffInt n) (hdiffMem n)
      (PDE.Parabolic.Cauchy.Energy.cauchyParH1Sub (un n) u) (hdiffSol n) t ht).2
  have hsliceDiff : Tendsto (fun n => eLpNorm
      (parSlice (PDE.Parabolic.Cauchy.Energy.cauchyParH1Sub (un n) u).toFun t)
      1 volume) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds happrox
      (Eventually.of_forall fun n => bot_le) ?_
    exact Eventually.of_forall hcontract
  have hsliceConverges : Tendsto
      (fun n => ∫ x, (un n).toFun (x, t)) atTop
      (𝓝 (∫ x, u.toFun (x, t))) := by
    have hdiffA : ∀ n, (fun x => (un n).toFun (x, t) - u.toFun (x, t)) =
        parSlice (PDE.Parabolic.Cauchy.Energy.cauchyParH1Sub (un n) u).toFun t := by
      intro n
      funext x
      rfl
    have hseqEq : (fun n => eLpNorm
        ((fun x => (un n).toFun (x, t)) - parSlice u.toFun t) 1 volume) =
        (fun n => eLpNorm
          (parSlice (PDE.Parabolic.Cauchy.Energy.cauchyParH1Sub (un n) u).toFun t)
          1 volume) := by
      funext n
      apply eLpNorm_congr_ae
      exact ae_of_all volume fun x => by
        simpa [parSlice] using congrFun (hdiffA n) x
    have hL1 : Tendsto (fun n => eLpNorm
        ((fun x => (un n).toFun (x, t)) - parSlice u.toFun t) 1 volume)
        atTop (𝓝 0) := by
      rw [hseqEq]
      exact hsliceDiff
    exact tendsto_integral_of_L1' (parSlice u.toFun t)
      (Eventually.of_forall fun n => (hball n).1) hL1
  have hdataConverges : Tendsto (fun n => ∫ x, fn n x) atTop (𝓝 (∫ x, f x)) := by
    exact tendsto_integral_of_L1' f (Eventually.of_forall hfn1) happrox
  have hsequenceEq : (fun n => ∫ x, (un n).toFun (x, t)) = fun n => ∫ x, fn n x := by
    funext n
    exact (hball n).2
  refine ⟨huL1.1, ?_⟩
  have hsliceConverges' : Tendsto (fun n => ∫ x, fn n x) atTop
      (𝓝 (∫ x, u.toFun (x, t))) := by
    rw [← hsequenceEq]
    exact hsliceConverges
  exact tendsto_nhds_unique hsliceConverges' hdataConverges

end PDE.Parabolic.Duality
