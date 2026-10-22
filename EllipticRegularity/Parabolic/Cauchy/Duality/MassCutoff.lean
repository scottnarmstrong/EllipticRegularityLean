module

public import EllipticRegularity.Parabolic.WeakSlice.Result
public import EllipticRegularity.Parabolic.CauchyDef

/-! # Compact spatial test identity for the Cauchy mass argument -/

@[expose] public section

namespace PDE.Parabolic.Duality

open MeasureTheory Set PDE PDE.Parabolic

open Filter Topology

/-- The Cauchy weak equation gives the change of a compactly supported spatial
pairing as the integrated spatial flux. This is the finite-radius identity
used before passing to the whole-space mass limit. -/
theorem cauchy_compact_pairing_change {d : ℕ} {lam Lam : ℝ} {a : ParCoeffField d}
    {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u)
    (ζ : Vec d → ℝ) (hζ : ContDiff ℝ 1 ζ) (hζc : HasCompactSupport ζ)
    {t : ℝ} (ht : t ∈ Icc s T) (hst : s < t) :
    IntegrableOn
        (fun z : Vec d × ℝ =>
          vecDot (matVecMul (a z) (u.grad z)) (spaceGradC1 ζ z.1))
        (univ ×ˢ Ioc s t) ∧
      (∫ x : Vec d, u.toFun (x, t) * ζ x) -
          (∫ x : Vec d, u.toFun (x, s) * ζ x) =
        -∫ z in univ ×ˢ Ioc s t,
          vecDot (matVecMul (a z) (u.grad z)) (spaceGradC1 ζ z.1) := by
  have h := PDE.Parabolic.weak_slice d lam Lam univ isOpen_univ
    (Icc s T) ordConnected_Icc a ha u hu.1 ζ hζ hζc (by simp)
    s t ⟨le_rfl, hsT.le⟩ ht hst
  simpa [setIntegral_univ] using h

/-- If a compactly supported smooth exhaustion has vanishing integrated flux,
the compact pairing identities converge to conservation of total mass. The
integrability and flux-tail estimates needed to instantiate this limit are
kept explicit for the Cauchy mass proof. -/
theorem cauchy_mass_of_cutoff_flux_limit {d : ℕ} {lam Lam : ℝ} {a : ParCoeffField d}
    {s T : ℝ} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : Integrable f volume)
    (u : ParH1Function (univ : Set (Vec d)) (Icc s T))
    (hu : IsCauchySolution a s T f u)
    {t : ℝ} (ht : t ∈ Icc s T) (hst : s < t)
    (hut : Integrable (parSlice u.toFun t) volume)
    (ζ : ℕ → Vec d → ℝ)
    (hζ : ∀ n, ContDiff ℝ 1 (ζ n))
    (hζc : ∀ n, HasCompactSupport (ζ n))
    (hζbound : ∀ n x, |ζ n x| ≤ 1)
    (hζtendsto : ∀ x, Tendsto (fun n => ζ n x) atTop (𝓝 1))
    (hflux : Tendsto (fun n => ∫ z in univ ×ˢ Ioc s t,
      vecDot (matVecMul (a z) (u.grad z)) (spaceGradC1 (ζ n) z.1)) atTop (𝓝 0)) :
    ∫ x : Vec d, u.toFun (x, t) = ∫ x : Vec d, f x := by
  let Ut : Vec d → ℝ := parSlice u.toFun t
  let A : ℕ → ℝ := fun n => ∫ x : Vec d, Ut x * ζ n x
  let B : ℕ → ℝ := fun n => ∫ x : Vec d, f x * ζ n x
  let C : ℕ → ℝ := fun n => ∫ z in univ ×ˢ Ioc s t,
    vecDot (matVecMul (a z) (u.grad z)) (spaceGradC1 (ζ n) z.1)
  have hA : Tendsto A atTop (𝓝 <| ∫ x : Vec d, Ut x) := by
    have hmeas : ∀ n, AEStronglyMeasurable (fun x : Vec d => Ut x * ζ n x) volume := by
      intro n
      exact hut.aestronglyMeasurable.mul (hζ n).continuous.aestronglyMeasurable
    have hbound : ∀ n, ∀ᵐ x ∂volume,
        ‖Ut x * ζ n x‖ ≤ ‖Ut x‖ := by
      intro n
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_mul]
      calc
        |Ut x| * |ζ n x| ≤ |Ut x| * 1 :=
          mul_le_mul_of_nonneg_left (hζbound n x) (abs_nonneg _)
        _ = |Ut x| := by ring
    have hpoint : ∀ᵐ x ∂volume, Tendsto (fun n => Ut x * ζ n x) atTop
        (𝓝 (Ut x)) := by
      filter_upwards [] with x
      simpa [Ut] using (tendsto_const_nhds.mul (hζtendsto x))
    simpa [A] using tendsto_integral_of_dominated_convergence
      (fun x : Vec d => ‖Ut x‖) hmeas hut.norm hbound hpoint
  have hB : Tendsto B atTop (𝓝 <| ∫ x : Vec d, f x) := by
    have hmeas : ∀ n, AEStronglyMeasurable (fun x : Vec d => f x * ζ n x) volume := by
      intro n
      exact hf.aestronglyMeasurable.mul (hζ n).continuous.aestronglyMeasurable
    have hbound : ∀ n, ∀ᵐ x ∂volume, ‖f x * ζ n x‖ ≤ ‖f x‖ := by
      intro n
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_mul]
      calc
        |f x| * |ζ n x| ≤ |f x| * 1 :=
          mul_le_mul_of_nonneg_left (hζbound n x) (abs_nonneg _)
        _ = |f x| := by ring
    have hpoint : ∀ᵐ x ∂volume, Tendsto (fun n => f x * ζ n x) atTop
        (𝓝 (f x)) := by
      filter_upwards [] with x
      simpa using (tendsto_const_nhds.mul (hζtendsto x))
    simpa [B] using tendsto_integral_of_dominated_convergence
      (fun x : Vec d => ‖f x‖) hmeas hf.norm hbound hpoint
  have hidentity : ∀ n, A n - B n = -C n := by
    intro n
    obtain ⟨_, hchange⟩ := cauchy_compact_pairing_change hsT ha f u hu
      (ζ n) (hζ n) (hζc n) ht hst
    have hinit : (∫ x : Vec d, u.toFun (x, s) * ζ n x) =
        ∫ x : Vec d, f x * ζ n x := by
      apply integral_congr_ae
      filter_upwards [hu.2] with x hx
      rw [hx]
    rw [hinit] at hchange
    simpa [A, B, C, Ut, parSlice] using hchange
  have hleft := hA.sub hB
  have hright : Tendsto (fun n => -C n) atTop (𝓝 0) := by
    simpa only [neg_zero] using hflux.neg
  have hEq : (fun n => A n - B n) =ᶠ[atTop] fun n => -C n :=
    Filter.Eventually.of_forall hidentity
  have hleft' : Tendsto (fun n => -C n) atTop
      (𝓝 ((∫ x : Vec d, Ut x) - ∫ x : Vec d, f x)) := hleft.congr' hEq
  have heqzero := tendsto_nhds_unique hleft' hright
  have hmass : (∫ x : Vec d, Ut x) - ∫ x : Vec d, f x = 0 := heqzero
  dsimp [Ut, parSlice] at hmass
  linarith

end PDE.Parabolic.Duality
