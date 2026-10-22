module

public import EllipticRegularity.Parabolic.NashKernel.OperatorLinear
public import Ch5NashStatements.CauchyPositivity
public import Ch5NashStatements.CauchyL1
public import Ch5NashStatements.NashUpper

/-!
# Positivity and `L¹`/`L^∞` bounds for the Cauchy solution operator

For data in `L¹ ∩ L²`: `cauchyOp` preserves nonnegativity, is an `L¹` contraction (hence
`L¹`-Lipschitz and monotone), and satisfies the Nash--Aronson `L¹ → L^∞` bound
`|cauchyOp f| ≤ C (t-s)^{-d/2} ‖f‖₁` a.e., with `C = C(d)` (the `r = 0` case of
`nashAronsonUpper`).
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic.NashKernel

open MeasureTheory Set

variable {d : ℕ} {Lam : ℝ} {a : ParCoeffField d} {s t : ℝ}

/-- Positivity. -/
theorem cauchyOp_nonneg_ae (hst : s < t) (ha : IsParabolicCoeff 1 Lam a univ (Icc s t))
    {f : Vec d → ℝ} (hf : MemLp f 2 volume) (hf0 : ∀ᵐ x : Vec d, 0 ≤ f x) :
    ∀ᵐ x : Vec d, 0 ≤ cauchyOp a s t f x := by
  obtain ⟨u, hu, hueq⟩ := exists_cauchyOp_eq hst ha hf
  have := cauchyPositivity d 1 Lam a s t hst ha f hf hf0 u hu t ⟨hst.le, le_rfl⟩
  rw [hueq]
  exact this

/-- `cauchyOp f` is integrable and `‖cauchyOp f‖₁ ≤ ‖f‖₁`. -/
theorem cauchyOp_L1 (hst : s < t) (ha : IsParabolicCoeff 1 Lam a univ (Icc s t))
    {f : Vec d → ℝ} (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume) :
    Integrable (cauchyOp a s t f) volume ∧
      eLpNorm (cauchyOp a s t f) 1 volume ≤ eLpNorm f 1 volume := by
  obtain ⟨u, hu, hueq⟩ := exists_cauchyOp_eq hst ha hf2
  have := cauchyL1Contraction d 1 Lam a s t hst ha f hf1 hf2 u hu t ⟨hst.le, le_rfl⟩
  rw [hueq]
  exact this

theorem integrable_cauchyOp (hst : s < t) (ha : IsParabolicCoeff 1 Lam a univ (Icc s t))
    {f : Vec d → ℝ} (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume) :
    Integrable (cauchyOp a s t f) volume :=
  (cauchyOp_L1 hst ha hf1 hf2).1

theorem eLpNorm_cauchyOp_le (hst : s < t) (ha : IsParabolicCoeff 1 Lam a univ (Icc s t))
    {f : Vec d → ℝ} (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume) :
    eLpNorm (cauchyOp a s t f) 1 volume ≤ eLpNorm f 1 volume :=
  (cauchyOp_L1 hst ha hf1 hf2).2

/-- `L¹`-Lipschitz continuity: `‖U f - U g‖₁ ≤ ‖f - g‖₁`. -/
theorem eLpNorm_cauchyOp_sub_le (hst : s < t) (ha : IsParabolicCoeff 1 Lam a univ (Icc s t))
    {f g : Vec d → ℝ} (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume)
    (hg1 : Integrable g volume) (hg2 : MemLp g 2 volume) :
    eLpNorm (cauchyOp a s t f - cauchyOp a s t g) 1 volume ≤ eLpNorm (f - g) 1 volume := by
  calc eLpNorm (cauchyOp a s t f - cauchyOp a s t g) 1 volume
      = eLpNorm (cauchyOp a s t (f - g)) 1 volume :=
        eLpNorm_congr_ae (cauchyOp_sub_ae hst ha hf2 hg2).symm
    _ ≤ eLpNorm (f - g) 1 volume := eLpNorm_cauchyOp_le hst ha (hf1.sub hg1) (hf2.sub hg2)

/-- Monotonicity: `f ≤ g` a.e. gives `U f ≤ U g` a.e. -/
theorem cauchyOp_mono_ae (hst : s < t) (ha : IsParabolicCoeff 1 Lam a univ (Icc s t))
    {f g : Vec d → ℝ} (hf2 : MemLp f 2 volume) (hg2 : MemLp g 2 volume)
    (hfg : ∀ᵐ x : Vec d, f x ≤ g x) :
    ∀ᵐ x : Vec d, cauchyOp a s t f x ≤ cauchyOp a s t g x := by
  have h0 : ∀ᵐ x : Vec d, 0 ≤ (g - f) x := by
    filter_upwards [hfg] with x hx using sub_nonneg.2 hx
  filter_upwards [cauchyOp_nonneg_ae hst ha (hg2.sub hf2) h0, cauchyOp_sub_ae hst ha hg2 hf2]
    with x h1 h2
  rw [h2] at h1
  exact sub_nonneg.1 h1

/-- Nash--Aronson `L¹ → L^∞` bound for the solution operator; `C = C(d)` precedes `Λ`. -/
theorem cauchyOp_abs_le_ae (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ Lam : ℝ, 1 ≤ Lam → ∀ (a : ParCoeffField d) (s t : ℝ), s < t →
      IsParabolicCoeff 1 Lam a univ (Icc s t) → ∀ f : Vec d → ℝ,
      Integrable f volume → MemLp f 2 volume →
      ∀ᵐ x : Vec d, |cauchyOp a s t f x| ≤ C * (t - s) ^ (-(d : ℝ) / 2) * ∫ y, |f y| := by
  obtain ⟨C, hC, hup⟩ := nashAronsonUpper d hd
  refine ⟨C, hC, fun Lam hLam a s t hst ha f hf1 hf2 => ?_⟩
  obtain ⟨u, hu, hueq⟩ := exists_cauchyOp_eq hst ha hf2
  have hUint := integrable_cauchyOp hst ha hf1 hf2
  set c : ℝ := C * (t - s) ^ (-(d : ℝ) / 2) * ∫ y, |f y| with hc
  have hbound : ∀ A : Set (Vec d), MeasurableSet A → volume A < ∞ →
      |∫ x in A, cauchyOp a s t f x| ≤ c * volume.real A := by
    intro A hA hfin
    have hg : MemLp (A.indicator (fun _ => (1 : ℝ))) 2 volume :=
      memLp_indicator_const 2 hA (1 : ℝ) (Or.inr hfin.ne)
    have hg1 : Integrable (A.indicator (fun _ => (1 : ℝ))) volume :=
      (integrable_indicator_iff hA).2 (integrableOn_const hfin.ne)
    obtain ⟨-, hb⟩ := hup Lam hLam a s t hst ha 0 le_rfl f _ hf1 hf2 hg1 hg univ univ
      (Filter.Eventually.of_forall fun x hx => absurd (mem_univ x) hx)
      (Filter.Eventually.of_forall fun x hx => absurd (mem_univ x) hx)
      (fun x _ y _ => by
        have : 0 ≤ euclideanSqDist x y := vecNormSq_nonneg _
        simpa using this) u hu
    have hind : (fun x => A.indicator (fun _ => (1 : ℝ)) x * u.toFun (x, t)) =
        A.indicator (cauchyOp a s t f) := by
      rw [hueq]
      ext x
      by_cases hx : x ∈ A <;> simp [hx]
    rw [hind, integral_indicator hA] at hb
    have habs : ∫ x, |A.indicator (fun _ => (1 : ℝ)) x| = volume.real A := by
      have : (fun x => |A.indicator (fun _ => (1 : ℝ)) x|) = A.indicator (fun _ => (1 : ℝ)) := by
        ext x; by_cases hx : x ∈ A <;> simp [hx]
      rw [this, integral_indicator hA]
      simp
    rw [habs] at hb
    have hexp : Real.exp (-(0 : ℝ) ^ 2 / (4 * Lam * (t - s)) +
        Real.sqrt (((d : ℝ) + 2) / 2) * 0 / Real.sqrt (Lam * (t - s))) = 1 := by simp
    rw [hexp] at hb
    calc |∫ x in A, cauchyOp a s t f x|
        ≤ _ := hb
      _ = c * volume.real A := by rw [hc]; ring
  have hc0 : 0 ≤ c := by
    rw [hc]
    have : 0 ≤ (t - s) ^ (-(d : ℝ) / 2) := Real.rpow_nonneg (sub_pos.2 hst).le _
    have : 0 ≤ ∫ y, |f y| := integral_nonneg fun y => abs_nonneg _
    positivity
  have key : ∀ σ : ℝ, (σ = 1 ∨ σ = -1) → ∀ᵐ x : Vec d, 0 ≤ c - σ * cauchyOp a s t f x := by
    intro σ hσ
    refine ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite (fun A hA hfin => ?_)
      (fun A hA hfin => ?_)
    · have hconst : IntegrableOn (fun _ : Vec d => c) A volume := integrableOn_const hfin.ne
      exact hconst.sub (hUint.integrableOn.const_mul σ)
    · have hconst : IntegrableOn (fun _ : Vec d => c) A volume := integrableOn_const hfin.ne
      have hI : IntegrableOn (cauchyOp a s t f) A volume := hUint.integrableOn
      rw [integral_sub hconst (hI.const_mul σ), setIntegral_const, smul_eq_mul, mul_comm]
      have hb := hbound A hA hfin
      rw [abs_le] at hb
      rcases hσ with rfl | rfl
      · simp only [one_mul]; linarith [hb.1, hb.2]
      · simp only [neg_mul, one_mul, integral_neg]; linarith [hb.1, hb.2]
  filter_upwards [key 1 (Or.inl rfl), key (-1) (Or.inr rfl)] with x h1 h2
  rw [abs_le]
  constructor <;> linarith

end PDE.Parabolic.NashKernel
