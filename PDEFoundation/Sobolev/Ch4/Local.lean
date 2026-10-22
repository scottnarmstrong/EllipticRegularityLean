module

public import PDEFoundation.Sobolev.WeakDerivative
public import PDEFoundation.Measure.RestrictedVolume
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Locality of weak derivatives

A locally integrable function has weak derivative `g` on an open set `U` as soon as every
point of `U` has an open neighbourhood inside `U` on which `g` is a weak derivative.
The proof splits a test function along a finite smooth partition of unity subordinate to
finitely many such neighbourhoods.

This is the mechanism that transports the convex-domain (ball) Sobolev calculus of the
repository to arbitrary open sets (annuli, punctured balls, ...).
-/

@[expose] public section

open MeasureTheory Set
open scoped Manifold ContDiff

namespace PDE.Ch4Infra

variable {d : ℕ}

/-- A finite smooth partition of unity on a compact set, subordinate to open neighbourhoods
of its points. -/
theorem exists_finite_partition {K U : Set (Vec d)} (hK : IsCompact K) (hKU : K ⊆ U)
    (V : Vec d → Set (Vec d)) (hVo : ∀ x ∈ U, IsOpen (V x)) (hVx : ∀ x ∈ U, x ∈ V x) :
    ∃ (t : Finset K) (f : SmoothPartitionOfUnity t 𝓘(ℝ, Vec d) (Vec d) K),
      f.IsSubordinate (fun i : t => V (i : K)) := by
  obtain ⟨t, ht⟩ := hK.elim_nhds_subcover' (fun x _ => V x)
    (fun x hx => (hVo x (hKU hx)).mem_nhds (hVx x (hKU hx)))
  refine ⟨t, ?_⟩
  refine SmoothPartitionOfUnity.exists_isSubordinate 𝓘(ℝ, Vec d) hK.isClosed _
    (fun i => hVo _ (hKU i.1.2)) ?_
  intro x hx
  have := ht hx
  simp only [mem_iUnion] at this ⊢
  obtain ⟨i, hi, hxi⟩ := this
  exact ⟨⟨i, hi⟩, hxi⟩

/-- A compactly supported continuous multiplier keeps a locally integrable function
integrable on the ambient open set. -/
theorem integrableOn_mul_of_compactSupport {U : Set (Vec d)} (hU : IsOpen U)
    {u h : Vec d → ℝ} (hu : LocallyIntegrableOn u U volume)
    (hh : Continuous h) (hhc : HasCompactSupport h) (hhU : tsupport h ⊆ U) :
    IntegrableOn (fun x => u x * h x) U := by
  have h1 : IntegrableOn u (tsupport h) volume := hu.integrableOn_compact_subset hhU hhc
  have h2 : IntegrableOn (fun x => u x * h x) (tsupport h) volume :=
    h1.mul_continuousOn hh.continuousOn hhc
  refine h2.of_forall_sdiff_eq_zero hU.measurableSet ?_
  intro x hx
  have : h x = 0 := image_eq_zero_of_notMem_tsupport hx.2
  simp [this]

theorem setIntegral_eq_of_tsupport_subset {U V : Set (Vec d)} (hU : IsOpen U) (hVU : V ⊆ U)
    {f : Vec d → ℝ} (hf : ∀ x, x ∉ V → f x = 0) :
    ∫ x in U, f x = ∫ x in V, f x :=
  (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hU.measurableSet hVU
    (fun x hx => hf x hx.2))

/-- **Locality of weak partial derivatives.** -/
theorem hasWeakPartialDerivOn_of_local {U : Set (Vec d)} (hU : IsOpen U) {i : Fin d}
    {u g : Vec d → ℝ} (hu : LocallyIntegrableOn u U volume)
    (hg : LocallyIntegrableOn g U volume)
    (hloc : ∀ x ∈ U, ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ HasWeakPartialDerivOn V i u g) :
    HasWeakPartialDerivOn U i u g := by
  classical
  intro φ hφ hφc hφU
  choose! V hVo hVx hVU hVw using hloc
  obtain ⟨t, f, hf⟩ := exists_finite_partition hφc hφU V hVo hVx
  let ψ : t → Vec d → ℝ := fun j x => φ x * f j x
  have hfs : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (f j) := fun j => by
    have := (f j).contMDiff
    rw [contMDiff_iff_contDiff] at this
    exact this
  have hψs : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (ψ j) := fun j => hφ.mul (hfs j)
  have hψc : ∀ j, HasCompactSupport (ψ j) := fun j => hφc.mul_right
  have hψV : ∀ j, tsupport (ψ j) ⊆ V (j.1 : Vec d) := fun j =>
    (tsupport_mul_subset_right (f := φ) (g := f j)).trans (hf j)
  have hψU : ∀ j, tsupport (ψ j) ⊆ U := fun j =>
    (hψV j).trans (hVU _ (hφU j.1.2))
  have hsum : ∀ x, φ x = ∑ j, ψ j x := by
    intro x
    by_cases hx : x ∈ tsupport φ
    · have h1 := (f.sum_eq_one (x := x) hx)
      rw [finsum_eq_sum_of_fintype] at h1
      simp only [ψ, ← Finset.mul_sum, h1, mul_one]
    · have : φ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [this, ψ]
  have hφeq : φ = fun x => ∑ j, ψ j x := funext hsum
  have hderiv : ∀ x, (fderiv ℝ φ x) (basisVec i) = ∑ j, (fderiv ℝ (ψ j) x) (basisVec i) := by
    intro x
    have e : fderiv ℝ φ x = fderiv ℝ (fun x => ∑ j, ψ j x) x :=
      congrArg (fun F => fderiv ℝ F x) hφeq
    rw [e, fderiv_fun_sum (fun j _ => ((hψs j).differentiable (by simp)) x)]
    simp
  have hcont : ∀ j, Continuous (fun x => (fderiv ℝ (ψ j) x) (basisVec i)) := fun j =>
    ((hψs j).continuous_fderiv (by simp)).clm_apply continuous_const
  have hdsupp : ∀ j, Function.support (fun x => (fderiv ℝ (ψ j) x) (basisVec i)) ⊆ tsupport (ψ j) :=
    fun j x hx => by
      by_contra h
      apply hx
      simp [fderiv_of_notMem_tsupport ℝ h]
  have hdc : ∀ j, HasCompactSupport (fun x => (fderiv ℝ (ψ j) x) (basisVec i)) := fun j =>
    (hψc j).mono' (hdsupp j)
  have hdU : ∀ j, tsupport (fun x => (fderiv ℝ (ψ j) x) (basisVec i)) ⊆ U := fun j =>
    (closure_minimal (hdsupp j) (isClosed_tsupport _)).trans (hψU j)
  have hIu : ∀ j, IntegrableOn (fun x => u x * (fderiv ℝ (ψ j) x) (basisVec i)) U :=
    fun j => integrableOn_mul_of_compactSupport hU hu (hcont j) (hdc j) (hdU j)
  have hIg : ∀ j, IntegrableOn (fun x => g x * ψ j x) U := fun j =>
    integrableOn_mul_of_compactSupport hU hg (hψs j).continuous (hψc j) (hψU j)
  have hzero : ∀ (j : t) (F : Vec d → ℝ), (∀ x, x ∉ tsupport (ψ j) → F x = 0) →
      ∀ x, x ∉ V (j.1 : Vec d) → F x = 0 := fun j F hF x hx =>
    hF x fun h => hx (hψV j h)
  have hterm : ∀ j : t, ∫ x in U, u x * (fderiv ℝ (ψ j) x) (basisVec i) =
      -∫ x in U, g x * ψ j x := by
    intro j
    have hVj := hVU _ (hφU j.1.2)
    have h1 := hVw _ (hφU j.1.2) (ψ j) (hψs j) (hψc j) (hψV j)
    rw [setIntegral_eq_of_tsupport_subset hU hVj (f := fun x => u x * (fderiv ℝ (ψ j) x) (basisVec i))
      (hzero j _ (fun x hx => by simp [fderiv_of_notMem_tsupport ℝ hx])), h1,
      ← setIntegral_eq_of_tsupport_subset hU hVj (f := fun x => g x * ψ j x)
      (hzero j _ (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx]))]
  calc ∫ x in U, u x * (fderiv ℝ φ x) (basisVec i)
      = ∫ x in U, ∑ j : t, u x * (fderiv ℝ (ψ j) x) (basisVec i) := by
        refine setIntegral_congr_fun hU.measurableSet fun x _ => ?_
        simp only [hderiv x, Finset.mul_sum]
    _ = ∑ j : t, ∫ x in U, u x * (fderiv ℝ (ψ j) x) (basisVec i) := integral_finsetSum _ (fun j _ => hIu j)
    _ = -∑ j : t, ∫ x in U, g x * ψ j x := by simp [hterm, Finset.sum_neg_distrib]
    _ = -∫ x in U, g x * φ x := by
        rw [← integral_finsetSum _ (fun j _ => hIg j)]
        congr 1
        refine setIntegral_congr_fun hU.measurableSet fun x _ => ?_
        rw [← Finset.mul_sum, ← hsum x]
/-- **Locality of weak gradients.** -/
theorem hasWeakGradientOn_of_local {U : Set (Vec d)} (hU : IsOpen U)
    {u : Vec d → ℝ} {g : Vec d → Vec d} (hu : LocallyIntegrableOn u U volume)
    (hg : ∀ i, LocallyIntegrableOn (fun x => g x i) U volume)
    (hloc : ∀ x ∈ U, ∃ V, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ HasWeakGradientOn V u g) :
    HasWeakGradientOn U u g := fun i =>
  hasWeakPartialDerivOn_of_local hU hu (hg i) fun x hx => by
    obtain ⟨V, h1, h2, h3, h4⟩ := hloc x hx
    exact ⟨V, h1, h2, h3, h4 i⟩

/-- Locality of weak gradients, with sup-norm cubes (`Metric.ball`) as neighbourhoods; these
are open bounded convex domains, so the convex-domain Sobolev calculus applies on them. -/
theorem hasWeakGradientOn_of_local_ball {U : Set (Vec d)} (hU : IsOpen U)
    {u : Vec d → ℝ} {g : Vec d → Vec d} (hu : LocallyIntegrableOn u U volume)
    (hg : ∀ i, LocallyIntegrableOn (fun x => g x i) U volume)
    (hloc : ∀ x ∈ U, ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ U ∧
      HasWeakGradientOn (Metric.ball x r) u g) :
    HasWeakGradientOn U u g :=
  hasWeakGradientOn_of_local hU hu hg fun x hx => by
    obtain ⟨r, hr, h1, h2⟩ := hloc x hx
    exact ⟨Metric.ball x r, Metric.isOpen_ball, Metric.mem_ball_self hr, h1, h2⟩

/-- Every point of an open set has a sup-norm cube around it inside the set. -/
theorem exists_ball_subset {U : Set (Vec d)} (hU : IsOpen U) {x : Vec d} (hx : x ∈ U) :
    ∃ r : ℝ, 0 < r ∧ Metric.ball x r ⊆ U := Metric.isOpen_iff.mp hU x hx

end PDE.Ch4Infra
