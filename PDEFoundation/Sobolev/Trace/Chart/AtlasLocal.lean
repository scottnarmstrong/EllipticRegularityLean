module

public import PDEFoundation.Sobolev.Trace.Chart.Defs
public import Mathlib.Analysis.Calculus.ImplicitContDiff
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Local graph structure of a `C¹` sublevel set

Given a `C¹` function `φ` with `φ x₀ = 0` and `fderiv ℝ φ x₀ ≠ 0`, the implicit function theorem
produces a coordinate `i`, a sign `sgn = ±1` and a function `γ₀`, `C¹` near the base point, such
that for `x'` near `x₀ ∘ succAbove i` and `|t|` small, the point `Ψ(x', t) = graphMap i γ₀ sgn (x', t)`
satisfies `φ (Ψ (x', t)) < 0 ↔ 0 < t`.
-/

@[expose] public section

namespace PDE.TraceLane

open Set Filter Topology

/-- Insertion of a coordinate, as a continuous linear map. -/
noncomputable def atlasInsertCLM {n : ℕ} (i : Fin (n + 1)) : Vec n × ℝ →L[ℝ] Vec (n + 1) :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => Fin.insertNth i z.2 z.1
      map_add' := fun z w => by
        ext j
        refine Fin.succAboveCases i ?_ ?_ j <;> simp
      map_smul' := fun c z => by
        ext j
        refine Fin.succAboveCases i ?_ ?_ j <;> simp }

theorem atlasInsertCLM_apply {n : ℕ} (i : Fin (n + 1)) (z : Vec n × ℝ) :
    atlasInsertCLM i z = Fin.insertNth i z.2 z.1 := rfl

theorem atlasInsertCLM_one {n : ℕ} (i : Fin (n + 1)) :
    atlasInsertCLM i ((0 : Vec n), (1 : ℝ)) = Pi.single i 1 := by
  rw [atlasInsertCLM_apply]
  ext j
  refine Fin.succAboveCases i ?_ ?_ j <;> simp

theorem atlasInsertCLM_base {n : ℕ} (i : Fin (n + 1)) (x : Vec (n + 1)) :
    atlasInsertCLM i ((fun j => x (i.succAbove j)), x i) = x := by
  rw [atlasInsertCLM_apply]
  ext j
  refine Fin.succAboveCases i ?_ ?_ j <;> simp

theorem graphMap_eq_add {n : ℕ} (i : Fin (n + 1)) (γ : Vec n → ℝ) (sgn : ℝ) (x' : Vec n) (t : ℝ) :
    graphMap i γ sgn (x', t) =
      Fin.insertNth i (γ x') x' + t • (sgn • (Pi.single i 1 : Vec (n + 1))) := by
  unfold graphMap
  ext j
  refine Fin.succAboveCases i ?_ ?_ j <;> simp
  ring

/-- Local graph structure: see the module docstring. -/
theorem exists_localGraph {n : ℕ} {W : Set (Vec (n + 1))} (hW : IsOpen W) {φ : Vec (n + 1) → ℝ}
    (hφ : ContDiff ℝ 1 φ) {x₀ : Vec (n + 1)} (hx₀W : x₀ ∈ W) (hφx₀ : φ x₀ = 0)
    (hd : fderiv ℝ φ x₀ ≠ 0) :
    ∃ (i : Fin (n + 1)) (sgn : ℝ) (γ₀ : Vec n → ℝ) (ρ a : ℝ), sgn ^ 2 = 1 ∧ 0 < ρ ∧ 0 < a ∧
      γ₀ (fun j => x₀ (i.succAbove j)) = x₀ i ∧
      (∀ x' ∈ Metric.ball (fun j => x₀ (i.succAbove j)) ρ, ContDiffAt ℝ 1 γ₀ x') ∧
      ∀ x' ∈ Metric.ball (fun j => x₀ (i.succAbove j)) ρ, ∀ t ∈ Ioo (-a) a,
        graphMap i γ₀ sgn (x', t) ∈ W ∧ (φ (graphMap i γ₀ sgn (x', t)) < 0 ↔ 0 < t) := by
  have hdiff : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  obtain ⟨i, hi⟩ : ∃ i : Fin (n + 1), fderiv ℝ φ x₀ (Pi.single i 1) ≠ 0 := by
    by_contra h
    push Not at h
    apply hd
    refine ContinuousLinearMap.coe_injective (LinearMap.pi_ext fun j c => ?_)
    have : (Pi.single j c : Vec (n + 1)) = c • Pi.single j 1 := by
      ext k; by_cases hk : k = j <;> simp [hk]
    simp [this, h j]
  set x₀' : Vec n := fun j => x₀ (i.succAbove j) with hx₀'
  set u : Vec n × ℝ := (x₀', x₀ i) with hu
  have hιu : atlasInsertCLM i u = x₀ := atlasInsertCLM_base i x₀
  set f : Vec n × ℝ → ℝ := fun z => φ (atlasInsertCLM i z) with hf
  have hfC : ContDiff ℝ 1 f := hφ.comp (atlasInsertCLM i).contDiff
  have hfu : f u = 0 := by simp [hf, hιu, hφx₀]
  have hfd : fderiv ℝ f u = (fderiv ℝ φ x₀).comp (atlasInsertCLM i) := by
    have h := (hdiff (atlasInsertCLM i u)).hasFDerivAt.comp u (atlasInsertCLM i).hasFDerivAt
    rw [hιu] at h
    exact h.fderiv
  have hinv : (fderiv ℝ f u ∘L ContinuousLinearMap.inr ℝ (Vec n) ℝ).IsInvertible := by
    set c := fderiv ℝ φ x₀ (Pi.single i 1) with hc
    have h1 : (fderiv ℝ f u ∘L ContinuousLinearMap.inr ℝ (Vec n) ℝ) 1 = c := by
      rw [hfd]
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
      rw [atlasInsertCLM_one i]
    refine ContinuousLinearMap.IsInvertible.of_inverse
      (g := c⁻¹ • (ContinuousLinearMap.id ℝ ℝ)) ?_ ?_
    · refine ContinuousLinearMap.ext_ring ?_
      simp [h1, hi]
    · refine ContinuousLinearMap.ext_ring ?_
      simp [h1, hi]
  have hcd : ContDiffAt ℝ 1 f u := hfC.contDiffAt
  set γ₀ := hcd.implicitFunction one_ne_zero hinv with hγ₀
  have hγ₀u : γ₀ x₀' = x₀ i := hcd.implicitFunction_apply_self one_ne_zero hinv
  have hγC : ContDiffAt ℝ 1 γ₀ x₀' := hcd.contDiffAt_implicitFunction one_ne_zero hinv
  have hγE : ∀ᶠ x in 𝓝 x₀', f (x, γ₀ x) = 0 := by
    have := hcd.eventually_apply_implicitFunction one_ne_zero hinv
    simpa [hfu] using this
  have hγCe : ∀ᶠ x in 𝓝 x₀', ContDiffAt ℝ 1 γ₀ x := hγC.eventually (by simp)
  -- the sign
  have hg : ContinuousAt (fun y => fderiv ℝ φ y (Pi.single i 1)) x₀ :=
    ((hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const).continuousAt
  obtain ⟨sgn, hsgn, hsgnneg⟩ : ∃ sgn : ℝ, sgn ^ 2 = 1 ∧ sgn * fderiv ℝ φ x₀ (Pi.single i 1) < 0 := by
    rcases lt_or_gt_of_ne hi with h | h
    · exact ⟨1, by norm_num, by simpa using h⟩
    · exact ⟨-1, by norm_num, by simpa using h⟩
  set Q : Set (Vec (n + 1)) := {y | y ∈ W ∧ sgn * fderiv ℝ φ y (Pi.single i 1) < 0} with hQ
  have hQn : Q ∈ 𝓝 x₀ :=
    Filter.inter_mem (hW.mem_nhds hx₀W)
      ((continuousAt_const.mul hg).eventually_lt continuousAt_const hsgnneg)
  have hΦ : ∀ z : Vec n × ℝ, graphMap i γ₀ sgn z =
      atlasInsertCLM i (z.1, γ₀ z.1 + sgn * z.2) := fun z => rfl
  have hΦ0 : graphMap i γ₀ sgn (x₀', 0) = x₀ := by
    rw [hΦ]; simpa [hγ₀u] using hιu
  have hΦc : ContinuousAt (graphMap i γ₀ sgn) (x₀', 0) := by
    have h1 : ContinuousAt (fun z : Vec n × ℝ => (z.1, γ₀ z.1 + sgn * z.2)) (x₀', 0) :=
      continuousAt_fst.prodMk
        ((hγC.continuousAt.comp continuousAt_fst).add (continuousAt_const.mul continuousAt_snd))
    have h2 := (atlasInsertCLM i).continuous.continuousAt.comp h1
    have h3 : graphMap i γ₀ sgn = ⇑(atlasInsertCLM i) ∘ fun z : Vec n × ℝ => (z.1, γ₀ z.1 + sgn * z.2) :=
      funext hΦ
    rw [h3]
    exact h2
  have hev : ∀ᶠ z in 𝓝 (x₀', (0 : ℝ)), graphMap i γ₀ sgn z ∈ Q ∧ ContDiffAt ℝ 1 γ₀ z.1 ∧
      f (z.1, γ₀ z.1) = 0 := by
    refine (hΦc.eventually ?_).and (((continuousAt_fst (p := (x₀', (0 : ℝ)))).eventually hγCe).and
      ((continuousAt_fst (p := (x₀', (0 : ℝ)))).eventually hγE))
    rw [hΦ0]
    exact hQn
  obtain ⟨U, hU, V, hV, hUV⟩ := mem_nhds_prod_iff.1 hev
  obtain ⟨ρ, hρ, hρU⟩ := Metric.mem_nhds_iff.1 hU
  obtain ⟨a, ha, haV⟩ := Metric.mem_nhds_iff.1 hV
  have hIoo : ∀ t ∈ Ioo (-a) a, t ∈ V := fun t ht =>
    haV (by rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_lt]; exact ht)
  have hmain : ∀ x' ∈ Metric.ball x₀' ρ, ∀ t ∈ Ioo (-a) a,
      graphMap i γ₀ sgn (x', t) ∈ Q ∧ ContDiffAt ℝ 1 γ₀ x' ∧ f (x', γ₀ x') = 0 :=
    fun x' hx' t ht => hUV (mk_mem_prod (hρU hx') (hIoo t ht))
  have h0 : (0 : ℝ) ∈ Ioo (-a) a := ⟨by linarith, ha⟩
  refine ⟨i, sgn, γ₀, ρ, a, hsgn, hρ, ha, hγ₀u, fun x' hx' => (hmain x' hx' 0 h0).2.1, ?_⟩
  intro x' hx'
  set k : ℝ → ℝ := fun t => φ (graphMap i γ₀ sgn (x', t)) with hk
  have hk0 : k 0 = 0 := by
    have := (hmain x' hx' 0 h0).2.2
    simpa [hk, hf, hΦ] using this
  have hkd : ∀ t, HasDerivAt k (sgn * fderiv ℝ φ (graphMap i γ₀ sgn (x', t)) (Pi.single i 1)) t := by
    intro t
    have e : ∀ s, graphMap i γ₀ sgn (x', s) =
        Fin.insertNth i (γ₀ x') x' + s • (sgn • (Pi.single i 1 : Vec (n + 1))) :=
      fun s => graphMap_eq_add i γ₀ sgn x' s
    have h1 : HasDerivAt (fun s : ℝ => Fin.insertNth i (γ₀ x') x' + s • (sgn • (Pi.single i 1 : Vec (n + 1))))
        (sgn • (Pi.single i 1 : Vec (n + 1))) t := by
      simpa using ((hasDerivAt_id t).smul_const (sgn • (Pi.single i 1 : Vec (n + 1)))).const_add
        (Fin.insertNth i (γ₀ x') x')
    have h1' : HasDerivAt (fun s : ℝ => graphMap i γ₀ sgn (x', s))
        (sgn • (Pi.single i 1 : Vec (n + 1))) t := by
      rw [show (fun s : ℝ => graphMap i γ₀ sgn (x', s)) = _ from funext e]
      exact h1
    have h2 := (hdiff (graphMap i γ₀ sgn (x', t))).hasFDerivAt.comp_hasDerivAt t h1'
    rw [map_smul, smul_eq_mul] at h2
    exact h2
  have hanti : StrictAntiOn k (Ioo (-a) a) := by
    refine strictAntiOn_of_deriv_neg (convex_Ioo _ _)
      (fun t _ => (hkd t).continuousAt.continuousWithinAt) ?_
    intro t ht
    rw [interior_Ioo] at ht
    rw [(hkd t).deriv]
    exact (hmain x' hx' t ht).1.2
  intro t ht
  refine ⟨(hmain x' hx' t ht).1.1, ?_⟩
  constructor
  · intro hlt
    by_contra hnt
    rcases (not_lt.1 hnt).lt_or_eq with h | h
    · have := hanti ht h0 h
      linarith
    · rw [h] at hlt
      have hk0' : φ (graphMap i γ₀ sgn (x', 0)) = 0 := hk0
      rw [hk0'] at hlt
      exact lt_irrefl _ hlt
  · intro ht0
    have := hanti h0 ht ht0
    simpa [hk0] using this

end PDE.TraceLane
