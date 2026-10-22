module

public import EllipticRegularity.Parabolic.NashLower.Assembly

/-!
# Nash-Aronson lower bound, conditional on the local Harnack inequality

`PDE.Ch5NashLowerAssembly.of_localHarnack` has as its single extra hypothesis the verbatim type of
the statement `PDE.parabLocalHarnack` and as conclusion the verbatim type of the statement
`PDE.nashAronsonLower`.  See `Assembly.lean` for the adaptation of the manuscript argument (the chain is run
inside an extended Cauchy problem so that it can end exactly at time `t`).
-/

@[expose] public section

namespace PDE.Ch5NashLowerAssembly

open MeasureTheory Set PDE.Parabolic.NashLower

/-- The Nash-Aronson lower bound from the local Harnack inequality.  The hypothesis `hLocal` is
verbatim the statement of `PDE.parabLocalHarnack` (for the given `d, Λ`); the conclusion is
verbatim the statement of `PDE.nashAronsonLower`. -/
theorem of_localHarnack (d : ℕ) (hd : 0 < d) (Lam : ℝ) (hLam : 1 ≤ Lam)
    (hLocal : ∃ H : ℝ, 2 ≤ H ∧ ∀ (a : ParCoeffField d) (τ θ : ℝ), 0 < θ → ∀ z z' : Vec d,
      euclideanSqDist z z' ≤ θ / 4 →
      IsParabolicCoeff 1 Lam a
        (euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (2 * θ)))
        (Ioc (τ - 3 * θ / 2) (τ + 5 * θ / 4)) →
      ∀ u : ParH1Function (euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (2 * θ)))
        (Ioc (τ - 3 * θ / 2) (τ + 5 * θ / 4)),
      IsParabolicWeakSolution a (euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (2 * θ)))
        (Ioc (τ - 3 * θ / 2) (τ + 5 * θ / 4)) u →
      (∀ᵐ w ∂(volume.restrict (euclideanBall ((1 / 2 : ℝ) • (z + z')) (Real.sqrt (2 * θ)) ×ˢ
        Ioc (τ - 3 * θ / 2) (τ + 5 * θ / 4))), 0 ≤ u.toFun w) →
        essSup (fun x : Vec d => ENNReal.ofReal (u.toFun (x, τ)))
            (volume.restrict (euclideanBall z (Real.sqrt θ / 4))) ≤
          ENNReal.ofReal H *
            essInf (fun x : Vec d => ENNReal.ofReal (u.toFun (x, τ + θ)))
              (volume.restrict (euclideanBall z' (Real.sqrt θ / 4)))) :
    ∃ c β : ℝ, 0 < c ∧ 0 < β ∧ ∀ (a : ParCoeffField d) (s t : ℝ), s < t →
      IsParabolicCoeff 1 Lam a univ (Icc s t) →
      ∀ (x y : Vec d) (f g : Vec d → ℝ),
      Integrable f volume → MemLp f 2 volume → Integrable g volume → MemLp g 2 volume →
      (∀ᵐ z : Vec d, 0 ≤ f z) → (∀ᵐ z : Vec d, 0 ≤ g z) →
      (∀ᵐ z : Vec d, z ∉ euclideanBall y (Real.sqrt (t - s) / 8) → f z = 0) →
      (∀ᵐ z : Vec d, z ∉ euclideanBall x (Real.sqrt (t - s) / 8) → g z = 0) →
      ∀ u : ParH1Function (univ : Set (Vec d)) (Icc s t), IsCauchySolution a s t f u →
        c * (t - s) ^ (-(d : ℝ) / 2) * Real.exp (-β * euclideanSqDist x y / (t - s)) *
            ((∫ z, f z) * ∫ z, g z) ≤ ∫ z, g z * u.toFun (z, t) := by
  obtain ⟨H, hH2, hH⟩ := hLocal
  have hHat : LocalHarnackAt d Lam H := hH
  obtain ⟨C₁, c₀, hC₁, -, hOD⟩ := PDE.onDiagLower d hd
  obtain ⟨CU, -, hUp⟩ := PDE.nashAronsonUpper d hd
  have hLam0 : 0 < Lam := by linarith
  have hL : 0 < Real.log (Real.exp 1 * Lam) := by
    apply Real.log_pos
    have : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.2 one_pos
    nlinarith
  set R₁ : ℝ := C₁ * Real.sqrt (Lam * Real.log (Real.exp 1 * Lam) / 4) with hR₁def
  have hR₁ : 0 < R₁ := by
    rw [hR₁def]; exact mul_pos hC₁ (Real.sqrt_pos.2 (by positivity))
  have hω : 0 < (volume (euclideanBall (0 : Vec d) 1)).toReal :=
    ENNReal.toReal_pos (volume_euclideanBall_pos 0 one_pos).ne'
      (volume_euclideanBall_ne_top 0 zero_le_one)
  have hHpos : 0 < H := by linarith
  have hlogH : 0 < Real.log H := Real.log_pos (by linarith)
  refine ⟨1 / (4 * (volume (euclideanBall (0 : Vec d) 1)).toReal * R₁ ^ d) *
      Real.exp (-(22 * (1 + R₁ ^ 2) + 1) * Real.log H), 22 * Real.log H, by positivity,
    by positivity, ?_⟩
  intro a s t hst ha x y f g hf1 hf2 hg1 hg2 hf0 hg0 hfs hgs u hu
  have hh : 0 < t - s := sub_pos.2 hst
  have hupos : ∀ᵐ z : Vec d, 0 ≤ u.toFun (z, t) :=
    PDE.cauchyPositivity d 1 Lam a s t hst ha f hf2 hf0 u hu t (right_mem_Icc.2 hst.le)
  have hRHS0 : 0 ≤ ∫ z, g z * u.toFun (z, t) :=
    integral_nonneg_of_ae (by filter_upwards [hg0, hupos] with z h1 h2 using mul_nonneg h1 h2)
  have hm0 : 0 ≤ ∫ z, f z := integral_nonneg_of_ae hf0
  rcases hm0.eq_or_lt with hm | hm
  · rw [← hm, zero_mul, mul_zero]; exact hRHS0
  · obtain ⟨N, hN, hlow⟩ := lower_core hLam hH2 hHat hC₁
      (fun a s t hst ha y ε f hf1 hf2 hf0 hint hs hε u hu =>
        (hOD Lam hLam a s t hst ha y ε f hf1 hf2 hf0 hint hs hε u hu).2.1)
      (fun a s t hst ha f g hf1 hf2 hg1 hg2 u hu =>
        (hUp Lam hLam a s t hst ha 0 le_rfl f g hf1 hf2 hg1 hg2 univ univ
          (Filter.Eventually.of_forall fun z hz => absurd (mem_univ z) hz)
          (Filter.Eventually.of_forall fun z hz => absurd (mem_univ z) hz)
          (fun _ _ _ _ => by rw [zero_pow two_ne_zero]; exact euclideanSqDist_nonneg _ _) u hu).1)
      hst ha x y f g hf1 hf2 hg1 hg2 hf0 hg0 hfs hgs u hu _ hm rfl
    have hρ : 0 < R₁ * Real.sqrt (t - s) := mul_pos hR₁ (Real.sqrt_pos.2 hh)
    rw [volume_euclideanBall_toReal_eq_unit_mul_of_pos y hρ] at hlow
    have hconst := const_ineq (d := d) (Dsq := euclideanSqDist x y) hω hR₁ hH2 hh N hN
    have hgint : 0 ≤ ∫ z, g z := integral_nonneg_of_ae hg0
    calc _ ≤ 1 / (4 * ((R₁ * Real.sqrt (t - s)) ^ d *
            (volume (euclideanBall (0 : Vec d) 1)).toReal)) / H ^ N *
          ((∫ z, f z) * ∫ z, g z) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hm.le hgint)
          exact hconst
      _ ≤ _ := hlow

end PDE.Ch5NashLowerAssembly
