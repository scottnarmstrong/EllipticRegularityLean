module

public import EllipticRegularity.Parabolic.NashKernel.OperatorBasic
public import Ch5NashStatements.CauchyDuality
public import Ch5NashStatements.CauchyAdjCoeff

/-!
# Linearity of the Cauchy solution operator

Via adjoint duality: for a finite-measure set `A` there is one adjoint solution `w_A` (datum `1_A`)
with `∫_A cauchyOp f = ∫ f · w_A` for every `f ∈ L²`; the right side is additive and homogeneous in
`f`, so `cauchyOp` is linear a.e. (`ae_eq_of_forall_setIntegral_eq_of_sigmaFinite`).
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.NashKernel

open MeasureTheory Set

variable {d : ℕ} {Lam : ℝ} {a : ParCoeffField d} {s t : ℝ}

/-- Duality representation of the set integrals of `cauchyOp`, with the adjoint solution
independent of the datum. -/
theorem exists_setIntegral_cauchyOp (hst : s < t) (ha : IsParabolicCoeff 1 Lam a univ (Icc s t))
    {A : Set (Vec d)} (hA : MeasurableSet A) (hAfin : volume A < ∞) :
    ∃ w : Vec d → ℝ, ∀ f : Vec d → ℝ, MemLp f 2 volume →
      Integrable (fun x => f x * w x) volume ∧ IntegrableOn (cauchyOp a s t f) A volume ∧
        ∫ x in A, cauchyOp a s t f x = ∫ x, f x * w x := by
  have hg : MemLp (A.indicator (fun _ => (1 : ℝ))) 2 volume :=
    memLp_indicator_const 2 hA (1 : ℝ) (Or.inr hAfin.ne)
  have ha' := parAdjCoeff_isParabolicCoeff d 1 Lam a s t ha
  obtain ⟨W, hW⟩ := cauchyExistence d 1 Lam (parAdjCoeff a (s + t)) s t hst ha'
    (A.indicator (fun _ => (1 : ℝ))) hg
  refine ⟨fun x => W.toFun (x, t), fun f hf => ?_⟩
  obtain ⟨u, hu, hueq⟩ := exists_cauchyOp_eq hst ha hf
  obtain ⟨h1, h2, h3⟩ := cauchyDuality d 1 Lam a s t hst ha f _ hf hg u hu W hW
  have hind : (fun x => A.indicator (fun _ => (1 : ℝ)) x * u.toFun (x, t)) =
      A.indicator (cauchyOp a s t f) := by
    rw [hueq]
    ext x
    by_cases hx : x ∈ A <;> simp [hx]
  rw [hind] at h1 h3
  refine ⟨h2, (integrable_indicator_iff hA).1 h1, ?_⟩
  rw [← integral_indicator hA, h3]

/-- Additivity of `cauchyOp` a.e. -/
theorem cauchyOp_add_ae (hst : s < t) (ha : IsParabolicCoeff 1 Lam a univ (Icc s t))
    {f₁ f₂ : Vec d → ℝ} (h₁ : MemLp f₁ 2 volume) (h₂ : MemLp f₂ 2 volume) :
    cauchyOp a s t (f₁ + f₂) =ᵐ[volume] cauchyOp a s t f₁ + cauchyOp a s t f₂ := by
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (fun A hA hfin => ?_)
    (fun A hA hfin => ?_) (fun A hA hfin => ?_)
  · obtain ⟨w, hw⟩ := exists_setIntegral_cauchyOp hst ha hA hfin
    exact (hw _ (h₁.add h₂)).2.1
  · obtain ⟨w, hw⟩ := exists_setIntegral_cauchyOp hst ha hA hfin
    exact (hw _ h₁).2.1.add (hw _ h₂).2.1
  · obtain ⟨w, hw⟩ := exists_setIntegral_cauchyOp hst ha hA hfin
    obtain ⟨i₁, j₁, e₁⟩ := hw _ h₁
    obtain ⟨i₂, j₂, e₂⟩ := hw _ h₂
    obtain ⟨i₃, j₃, e₃⟩ := hw _ (h₁.add h₂)
    have hL : ∫ x in A, (cauchyOp a s t f₁ + cauchyOp a s t f₂) x =
        (∫ x in A, cauchyOp a s t f₁ x) + ∫ x in A, cauchyOp a s t f₂ x :=
      integral_add j₁ j₂
    have hR : ∫ x, (f₁ + f₂) x * w x = (∫ x, f₁ x * w x) + ∫ x, f₂ x * w x := by
      rw [← integral_add i₁ i₂]
      simp only [Pi.add_apply, add_mul]
    exact e₃.trans (hR.trans (by rw [← e₁, ← e₂]; exact hL.symm))

/-- Homogeneity of `cauchyOp` a.e. -/
theorem cauchyOp_smul_ae (hst : s < t) (ha : IsParabolicCoeff 1 Lam a univ (Icc s t))
    (c : ℝ) {f : Vec d → ℝ} (hf : MemLp f 2 volume) :
    cauchyOp a s t (c • f) =ᵐ[volume] c • cauchyOp a s t f := by
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite (fun A hA hfin => ?_)
    (fun A hA hfin => ?_) (fun A hA hfin => ?_)
  · obtain ⟨w, hw⟩ := exists_setIntegral_cauchyOp hst ha hA hfin
    exact (hw _ (hf.const_smul c)).2.1
  · obtain ⟨w, hw⟩ := exists_setIntegral_cauchyOp hst ha hA hfin
    exact (hw _ hf).2.1.smul c
  · obtain ⟨w, hw⟩ := exists_setIntegral_cauchyOp hst ha hA hfin
    obtain ⟨i₁, j₁, e₁⟩ := hw _ hf
    obtain ⟨i₃, j₃, e₃⟩ := hw _ (hf.const_smul c)
    have hL : ∫ x in A, (c • cauchyOp a s t f) x = c • ∫ x in A, cauchyOp a s t f x :=
      integral_smul c _
    have hR : ∫ x, (c • f) x * w x = c • ∫ x, f x * w x := by
      rw [← integral_smul]
      simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact e₃.trans (hR.trans (by rw [← e₁]; exact hL.symm))

/-- Subtraction. -/
theorem cauchyOp_sub_ae (hst : s < t) (ha : IsParabolicCoeff 1 Lam a univ (Icc s t))
    {f₁ f₂ : Vec d → ℝ} (h₁ : MemLp f₁ 2 volume) (h₂ : MemLp f₂ 2 volume) :
    cauchyOp a s t (f₁ - f₂) =ᵐ[volume] cauchyOp a s t f₁ - cauchyOp a s t f₂ := by
  have e : f₁ - f₂ = f₁ + (-1 : ℝ) • f₂ := by ext x; simp [sub_eq_add_neg]
  rw [e]
  filter_upwards [cauchyOp_add_ae hst ha h₁ (h₂.const_smul (-1 : ℝ)),
    cauchyOp_smul_ae hst ha (-1 : ℝ) h₂] with x h1 h2
  rw [h1, Pi.add_apply, h2]
  simp [sub_eq_add_neg]

end PDE.Parabolic.NashKernel
