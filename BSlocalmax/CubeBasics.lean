module

public import Mathlib.Analysis.Calculus.Deriv.Add
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.MeanInequalities
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Topology.EMetricSpace.Lipschitz
public import PDEFoundation.Ambient.Basis
public import PDEFoundation.Ambient.EuclideanNorm
public import PDEFoundation.Sobolev.Ch4.Cutoff
public import PDEFoundation.Sobolev.Ch4.Lipschitz
public import PDEFoundation.Sobolev.ClassicalGradient

/-!
# Cube shells, radial cutoffs and the cutoff lemma

This file collects the following pieces, in dependency order: CubeCutoff, CubeFubini, Profile, CubeLemma1, BoundaryContinuity.
-/

-- ==== from CubeCutoff.lean ====
/-!
# Lipschitz cutoffs for cubes

`cubeCutoff x₀ r₁ r₂` is the piecewise-linear cutoff in the sup norm: equal to `1` on the closed cube
`‖x - x₀‖ ≤ r₁`, `0` outside the open cube `‖x - x₀‖ < r₂`, `(r₂ - r₁)⁻¹`-Lipschitz.  The level sets
are the cube boundaries `∂Q_r`.  This is the analogue of `radialCutoff` (Euclidean ball) used in
Bella–Schäffner, *Lipschitz bounds for integral functionals with (p,q)-growth conditions*.

On `Vec d = Fin d → ℝ`, `‖·‖` is the sup norm.

-/

@[expose] public section

open Set MeasureTheory PDE PDE.Ch4Infra

namespace PDE.BSlocalmax

variable {d : ℕ}

/-- The piecewise-linear cutoff in the sup norm. -/
noncomputable def cubeCutoff (x₀ : Vec d) (r₁ r₂ : ℝ) : Vec d → ℝ := fun x =>
  max (min ((r₂ - ‖x - x₀‖) / (r₂ - r₁)) 1) 0

/-- The sup-norm distance to a point is `1`-Lipschitz for the Euclidean distance. -/
theorem eucLip_supNorm_center (x₀ : Vec d) : EucLip 1 (fun x : Vec d => ‖x - x₀‖) := by
  intro x y
  show |‖x - x₀‖ - ‖y - x₀‖| ≤ 1 * vecEuclideanNorm (x - y)
  have h1 : |‖x - x₀‖ - ‖y - x₀‖| ≤ ‖x - y‖ := by
    have h := abs_norm_sub_norm_le (x - x₀) (y - x₀)
    rwa [sub_sub_sub_cancel_right] at h
  have h2 : ‖x - y‖ ≤ vecEuclideanNorm (x - y) := norm_le_vecEuclideanNorm _
  rw [one_mul]
  exact h1.trans h2

theorem cubeCutoff_eucLip (x₀ : Vec d) {r₁ r₂ : ℝ} (h : r₁ < r₂) :
    EucLip (r₂ - r₁)⁻¹ (cubeCutoff x₀ r₁ r₂) := by
  have hc : 0 < (r₂ - r₁)⁻¹ := inv_pos.mpr (sub_pos.mpr h)
  have hlin : EucLip (|(-(r₂ - r₁)⁻¹)| * 1)
      (fun x => (-(r₂ - r₁)⁻¹) * ‖x - x₀‖) :=
    (eucLip_supNorm_center x₀).smul _
  have hlin' := hlin.add (EucLip.const (r₂ * (r₂ - r₁)⁻¹))
  have hfun : (fun x => (-(r₂ - r₁)⁻¹) * ‖x - x₀‖ + r₂ * (r₂ - r₁)⁻¹) =
      fun x => (r₂ - ‖x - x₀‖) / (r₂ - r₁) := by
    funext x; field_simp; ring
  rw [hfun] at hlin'
  have h1 := hlin'.min (EucLip.const (1 : ℝ))
  have h2 := h1.max (EucLip.const (0 : ℝ))
  refine h2.mono ?_
  simp [abs_neg, abs_of_pos hc, max_eq_left hc.le]

theorem cubeCutoff_nonneg (x₀ : Vec d) (r₁ r₂ : ℝ) (x : Vec d) : 0 ≤ cubeCutoff x₀ r₁ r₂ x :=
  le_max_right _ _

theorem cubeCutoff_le_one (x₀ : Vec d) (r₁ r₂ : ℝ) (x : Vec d) : cubeCutoff x₀ r₁ r₂ x ≤ 1 :=
  max_le (min_le_right _ _) zero_le_one

theorem abs_cubeCutoff_le_one (x₀ : Vec d) (r₁ r₂ : ℝ) (x : Vec d) :
    |cubeCutoff x₀ r₁ r₂ x| ≤ 1 := by
  rw [abs_of_nonneg (cubeCutoff_nonneg x₀ r₁ r₂ x)]; exact cubeCutoff_le_one x₀ r₁ r₂ x

theorem cubeCutoff_eq_one {x₀ x : Vec d} {r₁ r₂ : ℝ} (h : r₁ < r₂)
    (hx : ‖x - x₀‖ ≤ r₁) : cubeCutoff x₀ r₁ r₂ x = 1 := by
  have hpos : 0 < r₂ - r₁ := sub_pos.mpr h
  have : 1 ≤ (r₂ - ‖x - x₀‖) / (r₂ - r₁) := by
    rw [le_div_iff₀ hpos]; linarith
  simp [cubeCutoff, min_eq_right this]

theorem cubeCutoff_eq_zero {x₀ x : Vec d} {r₁ r₂ : ℝ} (h : r₁ < r₂)
    (hx : r₂ ≤ ‖x - x₀‖) : cubeCutoff x₀ r₁ r₂ x = 0 := by
  have hpos : 0 < r₂ - r₁ := sub_pos.mpr h
  have : (r₂ - ‖x - x₀‖) / (r₂ - r₁) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) hpos.le
  have h2 : min ((r₂ - ‖x - x₀‖) / (r₂ - r₁)) 1 ≤ 0 :=
    (min_le_left _ _).trans this
  simp [cubeCutoff, max_eq_right h2]

theorem tsupport_cubeCutoff_subset (x₀ : Vec d) {r₁ r₂ : ℝ} (h : r₁ < r₂) :
    tsupport (cubeCutoff x₀ r₁ r₂) ⊆ Metric.closedBall x₀ r₂ := by
  refine closure_minimal (fun x hx => ?_) Metric.isClosed_closedBall
  by_contra hxn
  apply hx
  rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hxn
  exact cubeCutoff_eq_zero h hxn.le

theorem hasCompactSupport_cubeCutoff (x₀ : Vec d) {r₁ r₂ : ℝ} (h : r₁ < r₂) :
    HasCompactSupport (cubeCutoff x₀ r₁ r₂) :=
  (isCompact_closedBall x₀ r₂).of_isClosed_subset (isClosed_tsupport _)
    (tsupport_cubeCutoff_subset x₀ h)

/-! ### Null sets and the gradient -/

/-- The cube boundaries `{‖x - x₀‖ = r}` are Lebesgue null sets (`d ≥ 1`). -/
theorem volume_supNorm_sphere [NeZero d] (x₀ : Vec d) (r : ℝ) :
    volume {x : Vec d | ‖x - x₀‖ = r} = 0 := by
  have e : {x : Vec d | ‖x - x₀‖ = r} = Metric.sphere x₀ r := by
    ext x
    simp [Metric.mem_sphere, dist_eq_norm]
  rw [e]
  exact Measure.addHaar_sphere volume x₀ r

theorem vecEuclideanNorm_basisVec (i : Fin d) : vecEuclideanNorm (basisVec i) = 1 := by
  unfold vecEuclideanNorm
  rw [vecNormSq_eq_sum_sq]
  simp [basisVec_apply]

/-- Some coordinate attains the sup norm. -/
theorem exists_coord_eq_norm [NeZero d] (y : Vec d) : ∃ i, |y i| = ‖y‖ := by
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_max_image Finset.univ (fun i => |y i|) Finset.univ_nonempty
  refine ⟨i, le_antisymm ?_ ?_⟩
  · have h := norm_le_pi_norm y i
    simpa [Real.norm_eq_abs] using h
  · refine (pi_norm_le_iff_of_nonneg (abs_nonneg _)).2 fun j => ?_
    simpa [Real.norm_eq_abs] using hi j (Finset.mem_univ j)

/-- At a point of differentiability, the derivative of `y ↦ ‖y - x₀‖` is `v ↦ s * v i`
for a coordinate `i` and a sign `s`. -/
theorem fderiv_supNorm_apply [NeZero d] (x₀ : Vec d) {x : Vec d}
    (hx : DifferentiableAt ℝ (fun y : Vec d => ‖y - x₀‖) x) :
    ∃ (i : Fin d) (s : ℝ), |s| = 1 ∧ ∀ v : Vec d,
      fderiv ℝ (fun y : Vec d => ‖y - x₀‖) x v = s * v i := by
  obtain ⟨i, hi⟩ := exists_coord_eq_norm (x - x₀)
  obtain ⟨s, hs1, hsa⟩ : ∃ s : ℝ, |s| = 1 ∧ s * (x - x₀) i = |(x - x₀) i| := by
    by_cases h : 0 ≤ (x - x₀) i
    · exact ⟨1, by simp, by rw [abs_of_nonneg h]; ring⟩
    · exact ⟨-1, by simp, by rw [abs_of_neg (not_le.mp h)]; ring⟩
  refine ⟨i, s, hs1, fun v => ?_⟩
  have hline : HasDerivAt (fun t : ℝ => x + t • v) v 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add x
  have hg : HasFDerivAt (fun y : Vec d => ‖y - x₀‖)
      (fderiv ℝ (fun y : Vec d => ‖y - x₀‖) x) (x + (0 : ℝ) • v) := by
    simpa using hx.hasFDerivAt
  have hcomp := hg.comp_hasDerivAt (0 : ℝ) hline
  have h2 : HasDerivAt (fun t : ℝ => s * t * v i) (s * v i) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul s).mul_const (v i)
  have hh : HasDerivAt (fun t : ℝ => ‖x + t • v - x₀‖ - s * t * v i)
      (fderiv ℝ (fun y : Vec d => ‖y - x₀‖) x v - s * v i) 0 := hcomp.sub h2
  have hmin : IsLocalMin (fun t : ℝ => ‖x + t • v - x₀‖ - s * t * v i) 0 := by
    refine Filter.Eventually.of_forall (fun t => ?_)
    have e0 : ‖x + (0 : ℝ) • v - x₀‖ = ‖x - x₀‖ := by simp
    have key : |(x + t • v - x₀) i| ≤ ‖x + t • v - x₀‖ := by
      have h := norm_le_pi_norm (x + t • v - x₀) i
      simpa [Real.norm_eq_abs] using h
    have key2 : s * (x + t • v - x₀) i ≤ |(x + t • v - x₀) i| := by
      calc s * (x + t • v - x₀) i ≤ |s * (x + t • v - x₀) i| := le_abs_self _
        _ = |(x + t • v - x₀) i| := by rw [abs_mul, hs1, one_mul]
    have e1 : (x + t • v - x₀) i = (x - x₀) i + t * v i := by simp; ring
    have e2 : s * ((x - x₀) i + t * v i) = |(x - x₀) i| + s * t * v i := by
      rw [mul_add, hsa]; ring
    rw [e1] at key key2
    show ‖x + (0 : ℝ) • v - x₀‖ - s * 0 * v i ≤ ‖x + t • v - x₀‖ - s * t * v i
    rw [e0]
    linarith [hi, key, key2, e2]
  have hd := hmin.hasDerivAt_eq_zero hh
  linarith

/-- The Euclidean norm of the gradient of `y ↦ ‖y - x₀‖` is `1` wherever it is differentiable. -/
theorem vecEuclideanNorm_gradient_supNorm [NeZero d] (x₀ : Vec d) {x : Vec d}
    (hx : DifferentiableAt ℝ (fun y : Vec d => ‖y - x₀‖) x) :
    vecEuclideanNorm (classicalGradient (fun y : Vec d => ‖y - x₀‖) x) = 1 := by
  obtain ⟨i, s, hs, hv⟩ := fderiv_supNorm_apply x₀ hx
  have hg : classicalGradient (fun y : Vec d => ‖y - x₀‖) x = s • basisVec i := by
    funext j
    rw [classicalGradient_apply, hv]
    by_cases h : j = i
    · subst h; simp
    · have h' : i ≠ j := fun e => h e.symm
      simp [h, h']
  rw [hg, vecEuclideanNorm_smul, vecEuclideanNorm_basisVec, hs, mul_one]

/-- **Gradient of the cube cutoff:** almost everywhere `|∇η| = (r₂ - r₁)⁻¹` in the shell
`r₁ < ‖x - x₀‖ < r₂` and `0` elsewhere. -/
theorem cubeCutoff_gradient_norm_ae [NeZero d] (x₀ : Vec d) {r₁ r₂ : ℝ} (h₁ : 0 < r₁)
    (h : r₁ < r₂) :
    ∀ᵐ x ∂(volume : Measure (Vec d)),
      vecEuclideanNorm (classicalGradient (cubeCutoff x₀ r₁ r₂) x) =
        if r₁ < ‖x - x₀‖ ∧ ‖x - x₀‖ < r₂ then (r₂ - r₁)⁻¹ else 0 := by
  have hN := (eucLip_supNorm_center x₀).ae_differentiableAt zero_le_one
  have hs1 : ∀ᵐ x ∂(volume : Measure (Vec d)), ‖x - x₀‖ ≠ r₁ :=
    ae_iff.2 (by simpa using volume_supNorm_sphere x₀ r₁)
  have hs2 : ∀ᵐ x ∂(volume : Measure (Vec d)), ‖x - x₀‖ ≠ r₂ :=
    ae_iff.2 (by simpa using volume_supNorm_sphere x₀ r₂)
  have hcont : Continuous (fun y : Vec d => ‖y - x₀‖) := by fun_prop
  have hr2 : 0 < r₂ - r₁ := sub_pos.mpr h
  filter_upwards [hN, hs1, hs2] with x hx hx1 hx2
  have hzero : ∀ {f : Vec d → ℝ} {c : ℝ}, f =ᶠ[nhds x] (fun _ => c) →
      vecEuclideanNorm (classicalGradient f x) = 0 := by
    intro f c hev
    have hg : classicalGradient f x = 0 := by
      funext j
      rw [classicalGradient_apply, hev.fderiv_eq]
      simp
    rw [hg]
    exact vecEuclideanNorm_eq_zero_iff.2 rfl
  rcases lt_or_gt_of_ne hx1 with hlt | hgt
  · -- inside the inner cube
    have hopen : IsOpen {y : Vec d | ‖y - x₀‖ < r₁} := isOpen_lt hcont continuous_const
    have hev : cubeCutoff x₀ r₁ r₂ =ᶠ[nhds x] (fun _ => (1 : ℝ)) :=
      Filter.eventually_of_mem (hopen.mem_nhds hlt) (fun y hy => cubeCutoff_eq_one h hy.le)
    rw [hzero hev, if_neg (by intro hh; linarith [hh.1])]
  · rcases lt_or_gt_of_ne hx2 with hlt2 | hgt2
    · -- in the shell
      have hopen : IsOpen {y : Vec d | r₁ < ‖y - x₀‖ ∧ ‖y - x₀‖ < r₂} :=
        (isOpen_lt continuous_const hcont).inter (isOpen_lt hcont continuous_const)
      have hev : cubeCutoff x₀ r₁ r₂ =ᶠ[nhds x]
          (fun y : Vec d => (r₂ - ‖y - x₀‖) / (r₂ - r₁)) := by
        refine Filter.eventually_of_mem (hopen.mem_nhds ⟨hgt, hlt2⟩) (fun y hy => ?_)
        have hy1 : (r₂ - ‖y - x₀‖) / (r₂ - r₁) ≤ 1 := by
          rw [div_le_one hr2]; linarith [hy.1]
        have hy0 : 0 ≤ (r₂ - ‖y - x₀‖) / (r₂ - r₁) :=
          div_nonneg (by linarith [hy.2]) hr2.le
        simp [cubeCutoff, min_eq_left hy1, max_eq_left hy0]
      have hd : HasFDerivAt (fun y : Vec d => (r₂ - ‖y - x₀‖) / (r₂ - r₁))
          ((r₂ - r₁)⁻¹ • (0 - fderiv ℝ (fun y : Vec d => ‖y - x₀‖) x)) x :=
        by
        have hsub : HasFDerivAt (fun y : Vec d => r₂ - ‖y - x₀‖)
            (0 - fderiv ℝ (fun y : Vec d => ‖y - x₀‖) x) x :=
          (hasFDerivAt_const r₂ x).sub hx.hasFDerivAt
        have hfun : (fun y : Vec d => (r₂ - ‖y - x₀‖) / (r₂ - r₁)) =
            fun y : Vec d => (r₂ - r₁)⁻¹ * (r₂ - ‖y - x₀‖) := by
          funext y; rw [div_eq_inv_mul]
        rw [hfun]
        exact hsub.const_mul _
      have hg : classicalGradient (cubeCutoff x₀ r₁ r₂) x =
          (-(r₂ - r₁)⁻¹) • classicalGradient (fun y : Vec d => ‖y - x₀‖) x := by
        funext j
        rw [classicalGradient_apply, hev.fderiv_eq, hd.fderiv]
        simp [classicalGradient_apply]
      rw [hg, vecEuclideanNorm_smul, vecEuclideanNorm_gradient_supNorm x₀ hx,
        if_pos ⟨hgt, hlt2⟩, abs_neg, abs_of_pos (inv_pos.mpr hr2), mul_one]
    · -- outside the outer cube
      have hopen : IsOpen {y : Vec d | r₂ < ‖y - x₀‖} := isOpen_lt continuous_const hcont
      have hev : cubeCutoff x₀ r₁ r₂ =ᶠ[nhds x] (fun _ => (0 : ℝ)) :=
        Filter.eventually_of_mem (hopen.mem_nhds hgt2) (fun y hy => cubeCutoff_eq_zero h hy.le)
      rw [hzero hev, if_neg (by intro hh; linarith [hh.2])]

end PDE.BSlocalmax
end

-- ==== from CubeFubini.lean ====
-- Fubini over cube shells:
--   ∫_{ρ<‖x‖_∞<σ} f = ∫_ρ^σ (∫_{∂Q_r} f) dr,
-- where ∂Q_r is the sum over the 2(n+1) faces.


@[expose] public section

open MeasureTheory Set PDE PDE.Ch4Infra

namespace PDE.BSlocalmax

variable {n : ℕ}

/-- Integral over the face `{x i = s r}` (`n`-dimensional cube `[-r,r]^n`). -/
noncomputable def faceIntegral (i : Fin (n + 1)) (s r : ℝ) (f : Vec (n + 1) → ℝ) : ℝ :=
  ∫ y in Set.pi Set.univ (fun _ : Fin n => Icc (-r) r), f (Fin.insertNth i (s * r) y)

/-- Surface integral over the cube boundary `∂Q_r = {‖x‖_∞ = r}`: sum over the `2(n+1)` faces.
Double counting on the edges is a null set. -/
noncomputable def cubeBoundaryIntegral (r : ℝ) (f : Vec (n + 1) → ℝ) : ℝ :=
  ∑ i : Fin (n + 1), ∑ s ∈ ({-1, 1} : Finset ℝ), faceIntegral i s r f

/-- The sign `±1` of a `Bool`. -/
noncomputable def sgn (b : Bool) : ℝ := if b then 1 else -1

lemma abs_sgn (b : Bool) : |sgn b| = 1 := by
  cases b <;> simp [sgn]

lemma integral_comp_sign (s : ℝ) (hs : |s| = 1) (G : ℝ → ℝ) :
    ∫ a, G (s * a) = ∫ r, G r := by
  rw [Measure.integral_comp_mul_left, abs_inv, hs]
  simp

/-- The face piece `{ρ < ‖x‖ < σ, s x_i = ‖x‖}` is measurable. -/
lemma measurableSet_face (i : Fin (n + 1)) (s ρ σ : ℝ) :
    MeasurableSet {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ ∧ s * x i = ‖x‖} := by
  have h1 : MeasurableSet {x : Vec (n + 1) | ρ < ‖x‖} :=
    measurableSet_lt measurable_const measurable_norm
  have h2 : MeasurableSet {x : Vec (n + 1) | ‖x‖ < σ} :=
    measurableSet_lt measurable_norm measurable_const
  have h3 : MeasurableSet {x : Vec (n + 1) | s * x i = ‖x‖} :=
    measurableSet_eq_fun (by fun_prop) measurable_norm
  exact h1.inter (h2.inter h3)

/-- Description of the face piece in coordinates `(x i, remaining)`. -/
lemma mem_face_iff (i : Fin (n + 1)) {s : ℝ} (hs : |s| = 1) {ρ σ : ℝ} (hρ : 0 < ρ) (a : ℝ)
    (y : Fin n → ℝ) :
    (ρ < ‖(Fin.insertNth i a y : Vec (n + 1))‖ ∧ ‖(Fin.insertNth i a y : Vec (n + 1))‖ < σ ∧
      s * (Fin.insertNth i a y : Vec (n + 1)) i = ‖(Fin.insertNth i a y : Vec (n + 1))‖) ↔
    (s * a ∈ Ioo ρ σ ∧ ∀ j, |y j| ≤ s * a) := by
  set x : Vec (n + 1) := Fin.insertNth i a y with hx
  have hxi : x i = a := by simp [hx]
  have hxj : ∀ j, x (i.succAbove j) = y j := fun j => by simp [hx]
  constructor
  · rintro ⟨h1, h2, h3⟩
    rw [hxi] at h3
    refine ⟨⟨by rw [h3]; exact h1, by rw [h3]; exact h2⟩, fun j => ?_⟩
    have := norm_le_pi_norm x (i.succAbove j)
    rw [hxj, Real.norm_eq_abs] at this
    rw [h3]
    exact this
  · rintro ⟨⟨h1, h2⟩, h3⟩
    have hss : |s * a| = |a| := by rw [abs_mul, hs, one_mul]
    have hpos : 0 ≤ s * a := by linarith
    have hle : ‖x‖ ≤ s * a := by
      rw [pi_norm_le_iff_of_nonneg hpos]
      intro k
      rcases Fin.eq_self_or_eq_succAbove i k with hk | ⟨j, hk⟩
      · rw [hk, hxi, Real.norm_eq_abs, ← hss]
        exact (abs_of_nonneg hpos).le
      · rw [hk, hxj, Real.norm_eq_abs]
        exact h3 j
    have hge : s * a ≤ ‖x‖ := by
      have := norm_le_pi_norm x i
      rw [hxi, Real.norm_eq_abs] at this
      calc s * a ≤ |s * a| := le_abs_self _
        _ = |a| := hss
        _ ≤ ‖x‖ := this
    have heq : ‖x‖ = s * a := le_antisymm hle hge
    exact ⟨by rw [heq]; exact h1, by rw [heq]; exact h2, by rw [hxi, heq]⟩

/-- **One face.** -/
theorem integral_face {ρ σ : ℝ} (hρ : 0 < ρ) (i : Fin (n + 1)) {s : ℝ} (hs : |s| = 1)
    {f : Vec (n + 1) → ℝ} (hf : IntegrableOn f {x | ρ < ‖x‖ ∧ ‖x‖ < σ}) :
    IntegrableOn (fun r => faceIntegral i s r f) (Ioo ρ σ) ∧
    ∫ x in {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ ∧ s * x i = ‖x‖}, f x =
      ∫ r in Ioo ρ σ, faceIntegral i s r f := by
  have hs0 : s ≠ 0 := fun h => by simp [h] at hs
  have hss : s * s = 1 := by rw [← abs_mul_abs_self, hs]; norm_num
  let e : ℝ × (Fin n → ℝ) ≃ᵐ Vec (n + 1) :=
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm
  have hem : MeasurePreserving e :=
    (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) i).symm _
  have he_apply : ∀ p : ℝ × (Fin n → ℝ), e p = Fin.insertNth i p.1 p.2 := fun p => by
    simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]
  set R : Set (Vec (n + 1)) := {x | ρ < ‖x‖ ∧ ‖x‖ < σ ∧ s * x i = ‖x‖} with hR
  have hRm : MeasurableSet R := measurableSet_face i s ρ σ
  set T : Set (ℝ × (Fin n → ℝ)) := e ⁻¹' R with hT
  have hTm : MeasurableSet T := e.measurable hRm
  have hTmem : ∀ a y, (a, y) ∈ T ↔ (s * a ∈ Ioo ρ σ ∧ ∀ j, |y j| ≤ s * a) := by
    intro a y
    rw [hT, mem_preimage, he_apply]
    exact mem_face_iff i hs hρ a y
  set g : ℝ × (Fin n → ℝ) → ℝ := fun p => f (e p) with hg
  have hgint : IntegrableOn g T := by
    have h1 : IntegrableOn f R := hf.mono_set (fun x hx => ⟨hx.1, hx.2.1⟩)
    exact (hem.integrableOn_comp_preimage e.measurableEmbedding).2 h1
  have hint : Integrable (T.indicator g) (volume.prod volume) := by
    have := (integrable_indicator_iff hTm).2 hgint
    rwa [Measure.volume_eq_prod] at this
  have hprod := integral_prod (T.indicator g) hint
  have hinner := hint.integral_prod_left
  set Φ : ℝ → ℝ := (Ioo ρ σ).indicator (fun r => faceIntegral i s r f) with hΦ
  have hinner_eq : ∀ a, ∫ y, T.indicator g (a, y) = Φ (s * a) := by
    intro a
    by_cases ha : s * a ∈ Ioo ρ σ
    · rw [hΦ, indicator_of_mem ha]
      have hsa : s * (s * a) = a := by rw [← mul_assoc, hss, one_mul]
      have hcube : MeasurableSet
          (Set.pi Set.univ (fun _ : Fin n => Icc (-(s * a)) (s * a))) :=
        MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
      have hset : ∀ y, T.indicator g (a, y) =
          (Set.pi Set.univ (fun _ : Fin n => Icc (-(s * a)) (s * a))).indicator
            (fun y => f (Fin.insertNth i (s * (s * a)) y)) y := by
        intro y
        have hy : (a, y) ∈ T ↔ y ∈ Set.pi Set.univ (fun _ : Fin n => Icc (-(s * a)) (s * a)) := by
          rw [hTmem, mem_univ_pi]
          exact ⟨fun ⟨_, h⟩ j => abs_le.1 (h j), fun h => ⟨ha, fun j => abs_le.2 (h j)⟩⟩
        by_cases hy' : y ∈ Set.pi Set.univ (fun _ : Fin n => Icc (-(s * a)) (s * a))
        · rw [indicator_of_mem (hy.2 hy'), indicator_of_mem hy']
          simp only [hg, he_apply, hsa]
        · rw [indicator_of_notMem (fun h => hy' (hy.1 h)), indicator_of_notMem hy']
      simp_rw [hset]
      rw [integral_indicator hcube]
      rfl
    · rw [hΦ, indicator_of_notMem ha]
      have h0 : ∀ y, T.indicator g (a, y) = 0 := fun y =>
        indicator_of_notMem (fun hmem => ha ((hTmem a y).1 hmem).1) _
      simp_rw [h0]
      simp
  have hΦint : Integrable Φ := by
    have h1 : Integrable (fun a => Φ (s * a)) :=
      hinner.congr (Filter.Eventually.of_forall (fun a => hinner_eq a))
    exact (integrable_comp_mul_left_iff Φ hs0).1 h1
  refine ⟨(integrable_indicator_iff measurableSet_Ioo).1 hΦint, ?_⟩
  calc ∫ x in R, f x = ∫ x in R, f x ∂(Measure.map e volume) := by rw [hem.map_eq]
    _ = ∫ p in T, g p := setIntegral_map_equiv e f R
    _ = ∫ p, T.indicator g p := (integral_indicator hTm).symm
    _ = ∫ a, ∫ y, T.indicator g (a, y) := by
        rw [Measure.volume_eq_prod]; exact hprod
    _ = ∫ a, Φ (s * a) := integral_congr_ae (Filter.Eventually.of_forall hinner_eq)
    _ = ∫ r, Φ r := integral_comp_sign s hs Φ
    _ = ∫ r in Ioo ρ σ, faceIntegral i s r f := integral_indicator measurableSet_Ioo

/-- **Fubini over cube shells** (coarea formula with |∇‖·‖_∞| = 1 almost everywhere). -/
theorem integral_shell_eq_boundaryIntegral {ρ σ : ℝ} (hρ : 0 < ρ)
    {f : Vec (n + 1) → ℝ} (hf : IntegrableOn f {x | ρ < ‖x‖ ∧ ‖x‖ < σ}) :
    ∫ x in {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ}, f x =
      ∫ r in Ioo ρ σ, cubeBoundaryIntegral r f := by
  set Fc : Fin (n + 1) × Bool → Set (Vec (n + 1)) :=
    fun q => {x | ρ < ‖x‖ ∧ ‖x‖ < σ ∧ sgn q.2 * x q.1 = ‖x‖} with hFc
  have hunion : {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ} = ⋃ q, Fc q := by
    ext x
    simp only [mem_setOf_eq, mem_iUnion, hFc]
    constructor
    · rintro ⟨h1, h2⟩
      obtain ⟨i, hi⟩ := exists_coord_eq_norm x
      by_cases h : 0 ≤ x i
      · refine ⟨(i, true), h1, h2, ?_⟩
        rw [← hi, abs_of_nonneg h]; simp [sgn]
      · refine ⟨(i, false), h1, h2, ?_⟩
        rw [← hi, abs_of_neg (not_le.mp h)]; simp [sgn]
    · rintro ⟨q, h1, h2, _⟩
      exact ⟨h1, h2⟩
  have hdisj : Pairwise (Function.onFun (AEDisjoint volume) Fc) := by
    intro q q' hne
    show volume (Fc q ∩ Fc q') = 0
    obtain ⟨i, b⟩ := q
    obtain ⟨j, c⟩ := q'
    by_cases hij : i = j
    · subst hij
      have hbc : b ≠ c := fun h => hne (by rw [h])
      have hsgn : sgn b = - sgn c := by
        cases b <;> cases c <;> simp [sgn] at hbc ⊢
      have : Fc (i, b) ∩ Fc (i, c) = ∅ := by
        ext x
        simp only [hFc, mem_inter_iff, mem_setOf_eq, mem_empty_iff_false, iff_false]
        rintro ⟨⟨h1, _, h3⟩, ⟨_, _, h4⟩⟩
        rw [hsgn] at h3
        linarith
      rw [this]; exact measure_empty
    · let L : Vec (n + 1) →ₗ[ℝ] ℝ := sgn b • LinearMap.proj i - sgn c • LinearMap.proj j
      have hsub : Fc (i, b) ∩ Fc (j, c) ⊆ (LinearMap.ker L : Set (Vec (n + 1))) := by
        rintro x ⟨⟨_, _, h3⟩, ⟨_, _, h4⟩⟩
        simp only [SetLike.mem_coe, LinearMap.mem_ker, L, LinearMap.sub_apply,
          LinearMap.smul_apply, LinearMap.proj_apply, smul_eq_mul]
        linarith
      refine measure_mono_null hsub ?_
      refine Measure.addHaar_submodule volume _ ?_
      intro htop
      have hmem : (Pi.single i (1 : ℝ) : Vec (n + 1)) ∈ LinearMap.ker L := by
        rw [htop]; exact Submodule.mem_top
      rw [LinearMap.mem_ker] at hmem
      have h' : L (Pi.single i (1 : ℝ)) = sgn b := by
        simp [L, Pi.single_eq_of_ne (Ne.symm hij)]
      rw [h'] at hmem
      have := abs_sgn b
      rw [hmem] at this
      simp at this
  have hmeas : ∀ q, NullMeasurableSet (Fc q) volume := fun q =>
    (measurableSet_face q.1 (sgn q.2) ρ σ).nullMeasurableSet
  have hf' : IntegrableOn f (⋃ q, Fc q) := by rw [← hunion]; exact hf
  rw [hunion, integral_iUnion_ae hmeas hdisj hf', tsum_fintype]
  have hfaces := fun q : Fin (n + 1) × Bool =>
    integral_face (σ := σ) hρ q.1 (abs_sgn q.2) hf
  have hsum : ∀ r, ∑ q : Fin (n + 1) × Bool, faceIntegral q.1 (sgn q.2) r f =
      cubeBoundaryIntegral r f := by
    intro r
    rw [Fintype.sum_prod_type]
    unfold cubeBoundaryIntegral
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Fintype.sum_bool, Finset.sum_pair (by norm_num : (-1 : ℝ) ≠ 1), add_comm]
    simp [sgn]
  calc ∑ q, ∫ x in Fc q, f x
      = ∑ q : Fin (n + 1) × Bool, ∫ r in Ioo ρ σ, faceIntegral q.1 (sgn q.2) r f :=
        Finset.sum_congr rfl (fun q _ => (hfaces q).2)
    _ = ∫ r in Ioo ρ σ, ∑ q : Fin (n + 1) × Bool, faceIntegral q.1 (sgn q.2) r f :=
        (integral_finsetSum _ (fun q _ => (hfaces q).1)).symm
    _ = ∫ r in Ioo ρ σ, cubeBoundaryIntegral r f :=
        integral_congr_ae (Filter.Eventually.of_forall hsum)

end PDE.BSlocalmax
end

-- ==== from Profile.lean ====
-- One-dimensional part of Lemma 1 (Bella–Schäffner):
-- optimal radial profile φ with φ' = -(G^{-1})/I on (ρ,σ) and the Hölder estimate
--   (σ-ρ)^{1+1/δ} ≤ (∫ G^{-1}) (∫ G^δ)^{1/δ}.


@[expose] public section

open MeasureTheory Set intervalIntegral Filter Topology

namespace PDE.BSlocalmax

/-- Pointwise Young inequality (weighted AM-GM) with `θ = δ/(1+δ)`. -/
lemma young_pointwise {g A B δ : ℝ} (hg : 0 < g) (hA : 0 < A) (hB : 0 < B) (hδ : 0 < δ) :
    1 ≤ A ^ (δ / (1 + δ)) * B ^ (1 - δ / (1 + δ)) *
      (δ / (1 + δ) * (g⁻¹ / A) + (1 - δ / (1 + δ)) * (g ^ δ / B)) := by
  have h1δ : (1 + δ) ≠ 0 := ne_of_gt (by linarith)
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = δ / (1 + δ) := ⟨_, rfl⟩
  rw [← hθ]
  have hθ0 : 0 < θ := by rw [hθ]; exact div_pos hδ (by linarith)
  have hθ1 : θ < 1 := by rw [hθ, div_lt_one (by linarith)]; linarith
  have hexp : δ * (1 - θ) = θ := by rw [hθ]; field_simp; try ring
  have h := Real.geom_mean_le_arith_mean2_weighted hθ0.le (by linarith : 0 ≤ 1 - θ)
    (div_nonneg (inv_nonneg.2 hg.le) hA.le) (div_nonneg (Real.rpow_nonneg hg.le δ) hB.le)
    (by ring : θ + (1 - θ) = 1)
  have e1 : (g ^ δ) ^ (1 - θ) = g ^ θ := by rw [← Real.rpow_mul hg.le, hexp]
  have hgθ : 0 < g ^ θ := Real.rpow_pos_of_pos hg θ
  have hAθ : 0 < A ^ θ := Real.rpow_pos_of_pos hA θ
  have hBθ : 0 < B ^ (1 - θ) := Real.rpow_pos_of_pos hB _
  have hkey : (g⁻¹ / A) ^ θ * (g ^ δ / B) ^ (1 - θ) * (A ^ θ * B ^ (1 - θ)) = 1 := by
    rw [Real.div_rpow (inv_nonneg.2 hg.le) hA.le, Real.div_rpow (Real.rpow_nonneg hg.le δ) hB.le,
      Real.inv_rpow hg.le, e1]
    field_simp
  calc (1 : ℝ) = (g⁻¹ / A) ^ θ * (g ^ δ / B) ^ (1 - θ) * (A ^ θ * B ^ (1 - θ)) := hkey.symm
    _ ≤ (θ * (g⁻¹ / A) + (1 - θ) * (g ^ δ / B)) * (A ^ θ * B ^ (1 - θ)) :=
        mul_le_mul_of_nonneg_right h (by positivity)
    _ = _ := mul_comm _ _

/-- **Hölder estimate for Lemma 1**: `(σ-ρ)^{1+1/δ} ≤ (∫ G⁻¹) (∫ G^δ)^{1/δ}`. -/
theorem holder_inv {ρ σ δ : ℝ} (hρσ : ρ < σ) (hδ : 0 < δ) {G : ℝ → ℝ}
    (hG : ContinuousOn G (Icc ρ σ)) (hpos : ∀ r ∈ Icc ρ σ, 0 < G r) :
    (σ - ρ) ^ (1 + 1 / δ) ≤ (∫ r in ρ..σ, (G r)⁻¹) * (∫ r in ρ..σ, G r ^ δ) ^ (1 / δ) := by
  have hL0 : 0 < σ - ρ := sub_pos.2 hρσ
  have hc1 : ContinuousOn (fun r => (G r)⁻¹) (Icc ρ σ) :=
    hG.inv₀ (fun r hr => (hpos r hr).ne')
  have hc2 : ContinuousOn (fun r => G r ^ δ) (Icc ρ σ) :=
    hG.rpow_const (fun r hr => Or.inl (hpos r hr).ne')
  have hi1 : IntervalIntegrable (fun r => (G r)⁻¹) volume ρ σ :=
    hc1.intervalIntegrable_of_Icc hρσ.le
  have hi2 : IntervalIntegrable (fun r => G r ^ δ) volume ρ σ :=
    hc2.intervalIntegrable_of_Icc hρσ.le
  obtain ⟨L, hL⟩ : ∃ L, L = σ - ρ := ⟨_, rfl⟩
  obtain ⟨I, hI⟩ : ∃ I, I = ∫ r in ρ..σ, (G r)⁻¹ := ⟨_, rfl⟩
  obtain ⟨M, hM⟩ : ∃ M, M = ∫ r in ρ..σ, G r ^ δ := ⟨_, rfl⟩
  rw [← hL, ← hI, ← hM]
  rw [← hL] at hL0
  have hI0 : 0 < I := by
    rw [hI]
    exact intervalIntegral.intervalIntegral_pos_of_pos_on hi1
      (fun r hr => inv_pos.2 (hpos r (Ioo_subset_Icc_self hr))) hρσ
  have hM0 : 0 < M := by
    rw [hM]
    exact intervalIntegral.intervalIntegral_pos_of_pos_on hi2
      (fun r hr => Real.rpow_pos_of_pos (hpos r (Ioo_subset_Icc_self hr)) δ) hρσ
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = δ / (1 + δ) := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A, A = I / L := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B, B = M / L := ⟨_, rfl⟩
  have hA : 0 < A := by rw [hAdef]; exact div_pos hI0 hL0
  have hB : 0 < B := by rw [hBdef]; exact div_pos hM0 hL0
  have hθ0 : 0 < θ := by rw [hθ]; exact div_pos hδ (by linarith)
  have hθ1 : θ < 1 := by rw [hθ, div_lt_one (by linarith)]; linarith
  have hpt : ∀ r ∈ Icc ρ σ, 1 ≤ A ^ θ * B ^ (1 - θ) *
      (θ * ((G r)⁻¹ / A) + (1 - θ) * (G r ^ δ / B)) := by
    intro r hr
    rw [hθ]
    exact young_pointwise (hpos r hr) hA hB hδ
  have hint := intervalIntegral.integral_mono_on hρσ.le
    (intervalIntegrable_const (c := (1 : ℝ)))
    ((((hi1.div_const A).const_mul θ).add ((hi2.div_const B).const_mul (1 - θ))).const_mul
      (A ^ θ * B ^ (1 - θ))) hpt
  have hrhs : ∫ r in ρ..σ, A ^ θ * B ^ (1 - θ) *
      (θ * ((G r)⁻¹ / A) + (1 - θ) * (G r ^ δ / B)) =
      A ^ θ * B ^ (1 - θ) * (θ * (I / A) + (1 - θ) * (M / B)) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add ((hi1.div_const A).const_mul θ)
        ((hi2.div_const B).const_mul (1 - θ)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_div, intervalIntegral.integral_div, ← hI, ← hM]
  rw [hrhs] at hint
  have hlhs : ∫ r in ρ..σ, (1 : ℝ) = L := by simp [hL]
  rw [hlhs] at hint
  have hIA : I / A = L := by rw [hAdef]; field_simp
  have hMB : M / B = L := by rw [hBdef]; field_simp
  rw [hIA, hMB] at hint
  have h1 : 1 ≤ A ^ θ * B ^ (1 - θ) := by
    have : 1 * L ≤ (A ^ θ * B ^ (1 - θ)) * L := by
      calc 1 * L = L := one_mul L
        _ ≤ A ^ θ * B ^ (1 - θ) * (θ * L + (1 - θ) * L) := hint
        _ = (A ^ θ * B ^ (1 - θ)) * L := by ring
    exact le_of_mul_le_mul_right this hL0
  have h2 : 1 ≤ A * B ^ (1 / δ) := by
    have h3 := Real.rpow_le_rpow zero_le_one h1 (by positivity : 0 ≤ 1 / θ)
    rw [Real.one_rpow, Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_mul hA.le, ← Real.rpow_mul hB.le] at h3
    have e1 : θ * (1 / θ) = 1 := by field_simp
    have e2 : (1 - θ) * (1 / θ) = 1 / δ := by
      rw [hθ]; field_simp; try ring
    rw [e1, e2, Real.rpow_one] at h3
    exact h3
  have h4 : A * B ^ (1 / δ) = I * M ^ (1 / δ) / (L * L ^ (1 / δ)) := by
    rw [hAdef, hBdef, Real.div_rpow hM0.le hL0.le]
    have : 0 < L ^ (1 / δ) := Real.rpow_pos_of_pos hL0 _
    field_simp
  rw [h4, le_div_iff₀ (by positivity)] at h2
  rw [Real.rpow_add hL0, Real.rpow_one]
  linarith

/-- The optimal radial profile. -/
theorem exists_profile {ρ σ m : ℝ} (hρσ : ρ < σ) (hm : 0 < m) {G : ℝ → ℝ}
    (hG : ContinuousOn G (Icc ρ σ)) (hGm : ∀ r ∈ Icc ρ σ, m ≤ G r) :
    ∃ (φ : ℝ → ℝ) (I : ℝ), 0 < I ∧ I = ∫ r in ρ..σ, (G r)⁻¹ ∧
      LipschitzWith (Real.toNNReal (1 / (m * I))) φ ∧ (∀ r, φ r ∈ Icc (0 : ℝ) 1) ∧
      (∀ r, r ≤ ρ → φ r = 1) ∧ (∀ r, σ ≤ r → φ r = 0) ∧
      (∀ r ∈ Ioo ρ σ, HasDerivAt φ (-(G r)⁻¹ / I) r) ∧
      (∀ r, r < ρ → HasDerivAt φ 0 r) ∧ (∀ r, σ < r → HasDerivAt φ 0 r) := by
  have hpos : ∀ r ∈ Icc ρ σ, 0 < G r := fun r hr => lt_of_lt_of_le hm (hGm r hr)
  have hc1 : ContinuousOn (fun r => (G r)⁻¹) (Icc ρ σ) :=
    hG.inv₀ (fun r hr => (hpos r hr).ne')
  have hint : ∀ a b, a ∈ Icc ρ σ → b ∈ Icc ρ σ →
      IntervalIntegrable (fun u => (G u)⁻¹) volume a b := fun a b ha hb =>
    (hc1.mono (uIcc_subset_Icc ha hb)).intervalIntegrable
  have hρmem : ρ ∈ Icc ρ σ := ⟨le_rfl, hρσ.le⟩
  have hσmem : σ ∈ Icc ρ σ := ⟨hρσ.le, le_rfl⟩
  obtain ⟨I, hI⟩ : ∃ I, I = ∫ r in ρ..σ, (G r)⁻¹ := ⟨_, rfl⟩
  have hI0 : 0 < I := by
    rw [hI]
    exact intervalIntegral.intervalIntegral_pos_of_pos_on (hint ρ σ hρmem hσmem)
      (fun r hr => inv_pos.2 (hpos r (Ioo_subset_Icc_self hr))) hρσ
  obtain ⟨J, hJ⟩ : ∃ J : ℝ → ℝ, ∀ t, J t = ∫ u in ρ..t, (G u)⁻¹ := ⟨fun t => ∫ u in ρ..t, (G u)⁻¹, fun _ => rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ → ℝ, ∀ r, c r = max (min r σ) ρ := ⟨fun r => max (min r σ) ρ, fun _ => rfl⟩
  have hc_mem : ∀ r, c r ∈ Icc ρ σ := fun r => by
    rw [hc r]
    exact ⟨le_max_right _ _, max_le (min_le_right _ _) hρσ.le⟩
  have hc_lip : ∀ r s, |c r - c s| ≤ |r - s| := fun r s => by
    rw [hc r, hc s]
    refine (abs_max_sub_max_le_abs (min r σ) (min s σ) ρ).trans ?_
    refine (abs_min_sub_min_le_max r σ s σ).trans (max_le le_rfl (by simp))
  have hJ0 : J ρ = 0 := by rw [hJ]; simp
  have hJσ : J σ = I := by rw [hJ σ, hI]
  have hJnn : ∀ t ∈ Icc ρ σ, 0 ≤ J t := fun t ht => by
    rw [hJ t]
    exact intervalIntegral.integral_nonneg ht.1
      (fun u hu => (inv_pos.2 (hpos u ⟨hu.1, hu.2.trans ht.2⟩)).le)
  have hJle : ∀ t ∈ Icc ρ σ, J t ≤ I := fun t ht => by
    have h := intervalIntegral.integral_interval_sub_left (f := fun u => (G u)⁻¹)
      (μ := volume) (hint ρ σ hρmem hσmem) (hint ρ t hρmem ht)
    have h2 : 0 ≤ ∫ u in t..σ, (G u)⁻¹ :=
      intervalIntegral.integral_nonneg ht.2
        (fun u hu => (inv_pos.2 (hpos u ⟨ht.1.trans hu.1, hu.2⟩)).le)
    have : J σ - J t = ∫ u in t..σ, (G u)⁻¹ := by rw [hJ σ, hJ t]; exact h
    linarith
  have hJlip : ∀ s ∈ Icc ρ σ, ∀ t ∈ Icc ρ σ, |J t - J s| ≤ m⁻¹ * |t - s| := by
    intro s hs t ht
    have h := intervalIntegral.integral_interval_sub_left (f := fun u => (G u)⁻¹)
      (μ := volume) (hint ρ t hρmem ht) (hint ρ s hρmem hs)
    have h2 : J t - J s = ∫ u in s..t, (G u)⁻¹ := by rw [hJ t, hJ s]; exact h
    rw [h2, ← Real.norm_eq_abs, ← Real.norm_eq_abs]
    refine intervalIntegral.norm_integral_le_of_norm_le_const (fun u hu => ?_)
    have hu' : u ∈ Icc ρ σ := (uIcc_subset_Icc hs ht) (uIoc_subset_uIcc hu)
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 (hpos u hu'))]
    exact inv_anti₀ hm (hGm u hu')
  obtain ⟨φ, hφ⟩ : ∃ φ : ℝ → ℝ, ∀ r, φ r = 1 - J (c r) / I := ⟨fun r => 1 - J (c r) / I, fun _ => rfl⟩
  have hφ1 : ∀ r, r ≤ ρ → φ r = 1 := fun r hr => by
    have : c r = ρ := by rw [hc r]; exact max_eq_right ((min_le_left _ _).trans hr)
    rw [hφ r, this, hJ0]; simp
  have hφ0 : ∀ r, σ ≤ r → φ r = 0 := fun r hr => by
    have : c r = σ := by rw [hc r, min_eq_right hr, max_eq_left hρσ.le]
    rw [hφ r, this, hJσ, div_self hI0.ne', sub_self]
  refine ⟨φ, I, hI0, hI, ?_, ?_, hφ1, hφ0, ?_, ?_, ?_⟩
  · refine LipschitzWith.of_dist_le_mul (fun r s => ?_)
    rw [Real.dist_eq, Real.dist_eq, hφ r, hφ s]
    have e : 1 - J (c r) / I - (1 - J (c s) / I) = (J (c s) - J (c r)) / I := by ring
    rw [e, abs_div, abs_of_pos hI0, div_le_iff₀ hI0]
    have h1 := hJlip (c r) (hc_mem r) (c s) (hc_mem s)
    have h2 := hc_lip s r
    have h3 : |s - r| = |r - s| := abs_sub_comm s r
    have hco : ((Real.toNNReal (1 / (m * I)) : NNReal) : ℝ) = 1 / (m * I) :=
      Real.coe_toNNReal _ (by positivity)
    rw [hco]
    calc |J (c s) - J (c r)| ≤ m⁻¹ * |c s - c r| := h1
      _ ≤ m⁻¹ * |r - s| :=
          mul_le_mul_of_nonneg_left ((hc_lip s r).trans (abs_sub_comm s r).le) (inv_nonneg.2 hm.le)
      _ = 1 / (m * I) * |r - s| * I := by field_simp
  · intro r
    rw [hφ r]
    have a1 := hJnn (c r) (hc_mem r)
    have a2 := hJle (c r) (hc_mem r)
    refine ⟨?_, ?_⟩
    · have : J (c r) / I ≤ 1 := (div_le_one hI0).2 a2
      linarith
    · have : 0 ≤ J (c r) / I := div_nonneg a1 hI0.le
      linarith
  · intro r hr
    have hJd : HasDerivAt J ((G r)⁻¹) r := by
      have hJf : J = fun t => ∫ u in ρ..t, (G u)⁻¹ := funext hJ
      rw [hJf]
      exact intervalIntegral.integral_hasDerivAt_right
        (hint ρ r hρmem ⟨hr.1.le, hr.2.le⟩)
        ((hc1.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo r hr)
        ((hc1.mono Ioo_subset_Icc_self).continuousAt (Ioo_mem_nhds hr.1 hr.2))
    have h := (hJd.div_const I).const_sub 1
    have heq : φ =ᶠ[𝓝 r] fun x => 1 - J x / I := by
      filter_upwards [Ioo_mem_nhds hr.1 hr.2] with x hx
      have : c x = x := by rw [hc x, min_eq_left hx.2.le, max_eq_left hx.1.le]
      rw [hφ x, this]
    have := h.congr_of_eventuallyEq heq
    simpa [neg_div] using this
  · intro r hr
    refine (hasDerivAt_const r (1 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds hr] with x hx
    exact hφ1 x hx.le
  · intro r hr
    refine (hasDerivAt_const r (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hr] with x hx
    exact hφ0 x hx.le

end PDE.BSlocalmax
end

-- ==== from CubeLemma1.lean ====
-- Lemma 1 (Bella–Schäffner) for cube shells, continuous version:
-- For continuous `g ≥ m > 0` (with continuous boundary integral) there is a cutoff `η = φ(‖x‖_∞)` with
--   ∫_{shell} g |∇η|² ≤ (σ-ρ)^{-(1+1/δ)} (∫_ρ^σ (∫_{∂Q_r} g)^δ dr)^{1/δ}.


@[expose] public section

open MeasureTheory Set PDE PDE.Ch4Infra

namespace PDE.BSlocalmax

variable {n : ℕ}

/-- `φ ∘ ‖·‖_∞` is Euclidean-Lipschitz if `φ` is Lipschitz. -/
theorem eucLip_comp_norm {d : ℕ} {φ : ℝ → ℝ} {K : NNReal} (hφ : LipschitzWith K φ) :
    EucLip (K : ℝ) (fun x : Vec d => φ ‖x‖) := by
  intro x y
  have h1 := hφ.dist_le_mul ‖x‖ ‖y‖
  have h2 := eucLip_supNorm_center (0 : Vec d) x y
  simp only [sub_zero] at h2
  rw [Real.dist_eq, Real.dist_eq] at h1
  calc |φ ‖x‖ - φ ‖y‖| ≤ K * |‖x‖ - ‖y‖| := h1
    _ ≤ K * (1 * vecEuclideanNorm (x - y)) := mul_le_mul_of_nonneg_left h2 K.coe_nonneg
    _ = K * vecEuclideanNorm (x - y) := by rw [one_mul]

/-- Gradient of `φ ∘ ‖·‖_∞` almost everywhere in the shell. -/
theorem gradient_comp_norm_ae {d : ℕ} [NeZero d] {φ dφ : ℝ → ℝ} {ρ σ : ℝ}
    (hd : ∀ r ∈ Ioo ρ σ, HasDerivAt φ (dφ r) r) :
    ∀ᵐ x ∂(volume : Measure (Vec d)), ρ < ‖x‖ → ‖x‖ < σ →
      vecNormSq (classicalGradient (fun y : Vec d => φ ‖y‖) x) = dφ ‖x‖ ^ 2 := by
  have hN := (eucLip_supNorm_center (0 : Vec d)).ae_differentiableAt zero_le_one
  filter_upwards [hN] with x hx h1 h2
  have hx' : DifferentiableAt ℝ (fun y : Vec d => ‖y‖) x := by simpa using hx
  have hφx := hd ‖x‖ ⟨h1, h2⟩
  have hc : HasFDerivAt (fun y : Vec d => φ ‖y‖)
      (dφ ‖x‖ • fderiv ℝ (fun y : Vec d => ‖y‖) x) x :=
    hφx.comp_hasFDerivAt x hx'.hasFDerivAt
  have hg : classicalGradient (fun y : Vec d => φ ‖y‖) x =
      dφ ‖x‖ • classicalGradient (fun y : Vec d => ‖y‖) x := by
    funext j
    rw [classicalGradient_apply, hc.fderiv]
    simp [classicalGradient_apply]
  have h1' : vecEuclideanNorm (classicalGradient (fun y : Vec d => ‖y‖) x) = 1 := by
    simpa using vecEuclideanNorm_gradient_supNorm (0 : Vec d) hx
  have h3 : vecNormSq (classicalGradient (fun y : Vec d => ‖y‖) x) = 1 := by
    rw [← vecEuclideanNorm_sq, h1']; norm_num
  rw [hg, vecNormSq_smul, h3, mul_one]

lemma norm_insertNth_face (i : Fin (n + 1)) {s r : ℝ} (hs : |s| = 1) (hr : 0 ≤ r)
    {y : Fin n → ℝ} (hy : y ∈ Set.pi Set.univ (fun _ : Fin n => Icc (-r) r)) :
    ‖(Fin.insertNth i (s * r) y : Vec (n + 1))‖ = r := by
  set x : Vec (n + 1) := Fin.insertNth i (s * r) y with hx
  have hxi : x i = s * r := by simp [hx]
  have hxj : ∀ j, x (i.succAbove j) = y j := fun j => by simp [hx]
  have hss : |s * r| = r := by rw [abs_mul, hs, one_mul, abs_of_nonneg hr]
  apply le_antisymm
  · rw [pi_norm_le_iff_of_nonneg hr]
    intro k
    rcases Fin.eq_self_or_eq_succAbove i k with hk | ⟨j, hk⟩
    · rw [hk, hxi, Real.norm_eq_abs, hss]
    · rw [hk, hxj, Real.norm_eq_abs]
      exact abs_le.2 (mem_univ_pi.1 hy j)
  · have := norm_le_pi_norm x i
    rw [hxi, Real.norm_eq_abs, hss] at this
    exact this

lemma faceIntegral_mul_norm (i : Fin (n + 1)) {s r : ℝ} (hs : |s| = 1) (hr : 0 ≤ r)
    (g : Vec (n + 1) → ℝ) (c : ℝ → ℝ) :
    faceIntegral i s r (fun x => g x * c ‖x‖) = faceIntegral i s r g * c r := by
  unfold faceIntegral
  have hcube : MeasurableSet (Set.pi Set.univ (fun _ : Fin n => Icc (-r) r)) :=
    MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  rw [← integral_mul_const]
  refine setIntegral_congr_fun hcube (fun y hy => ?_)
  show g (Fin.insertNth i (s * r) y) * c ‖(Fin.insertNth i (s * r) y : Vec (n + 1))‖ =
    g (Fin.insertNth i (s * r) y) * c r
  rw [norm_insertNth_face i hs hr hy]

lemma cubeBoundaryIntegral_mul_norm {r : ℝ} (hr : 0 ≤ r) (g : Vec (n + 1) → ℝ) (c : ℝ → ℝ) :
    cubeBoundaryIntegral r (fun x => g x * c ‖x‖) = cubeBoundaryIntegral r g * c r := by
  unfold cubeBoundaryIntegral
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  have hs1 : |s| = 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl <;> simp
  exact faceIntegral_mul_norm i hs1 hr g c

/-- **Lemma 1 (Bella–Schäffner), cube version, continuous form.** -/
theorem exists_cutoff_cubeShell {ρ σ δ m : ℝ} (hρ : 0 < ρ) (hρσ : ρ < σ) (hδ : 0 < δ)
    (hm : 0 < m) {g : Vec (n + 1) → ℝ} (hgc : Continuous g)
    (hG : ContinuousOn (fun r => cubeBoundaryIntegral r g) (Icc ρ σ))
    (hGm : ∀ r ∈ Icc ρ σ, m ≤ cubeBoundaryIntegral r g) :
    ∃ (K : ℝ) (η : Vec (n + 1) → ℝ), 0 ≤ K ∧
      K ≤ ((σ - ρ) ^ (-(1 + 1 / δ)) *
        (∫ r in Ioo ρ σ, (cubeBoundaryIntegral r g) ^ δ) ^ (1 / δ)) / m ∧
      EucLip K η ∧ (∀ x, η x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x, ‖x‖ ≤ ρ → η x = 1) ∧ (∀ x, σ ≤ ‖x‖ → η x = 0) ∧
      (IntegrableOn (fun x => g x * vecNormSq (classicalGradient η x))
        {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ}) ∧
      ∫ x in {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ}, g x * vecNormSq (classicalGradient η x) ≤
        (σ - ρ) ^ (-(1 + 1 / δ)) * (∫ r in Ioo ρ σ, (cubeBoundaryIntegral r g) ^ δ) ^ (1 / δ) := by
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ → ℝ, ∀ r, G r = cubeBoundaryIntegral r g :=
    ⟨fun r => cubeBoundaryIntegral r g, fun _ => rfl⟩
  have hGfun : G = fun r => cubeBoundaryIntegral r g := funext hGdef
  have hG' : ContinuousOn G (Icc ρ σ) := by rw [hGfun]; exact hG
  have hGm' : ∀ r ∈ Icc ρ σ, m ≤ G r := fun r hr => by rw [hGdef]; exact hGm r hr
  have hGpos : ∀ r ∈ Icc ρ σ, 0 < G r := fun r hr => lt_of_lt_of_le hm (hGm' r hr)
  have hL : 0 < σ - ρ := sub_pos.2 hρσ
  obtain ⟨φ, I, hI0, hIeq, hlip, hrange, hφ1, hφ0, hderiv, -, -⟩ :=
    exists_profile hρσ hm hG' hGm'
  -- Hölder
  have hH := holder_inv hρσ hδ hG' hGpos
  have hH1 := holder_inv (δ := 1) hρσ one_pos hG' hGpos
  rw [← hIeq] at hH hH1
  have hMδ : ∫ r in ρ..σ, G r ^ δ = ∫ r in Ioo ρ σ, cubeBoundaryIntegral r g ^ δ := by
    rw [intervalIntegral.integral_of_le hρσ.le, integral_Ioc_eq_integral_Ioo]
    simp_rw [hGdef]
  have hM1 : ∫ r in ρ..σ, G r ^ (1 : ℝ) = ∫ r in Ioo ρ σ, cubeBoundaryIntegral r g := by
    rw [intervalIntegral.integral_of_le hρσ.le, integral_Ioc_eq_integral_Ioo]
    simp_rw [Real.rpow_one, hGdef]
  have hI' : I = ∫ r in Ioo ρ σ, (G r)⁻¹ := by
    rw [hIeq, intervalIntegral.integral_of_le hρσ.le, integral_Ioc_eq_integral_Ioo]
  rw [hMδ] at hH
  have h2 : (σ - ρ) ^ 2 ≤ I * ∫ r in Ioo ρ σ, cubeBoundaryIntegral r g := by
    have e : (σ - ρ) ^ (1 + 1 / (1 : ℝ)) = (σ - ρ) ^ 2 := by
      rw [show (1 : ℝ) + 1 / 1 = 2 by norm_num, Real.rpow_two]
    have e2 : (∫ r in ρ..σ, G r ^ (1 : ℝ)) ^ (1 / (1 : ℝ)) =
        ∫ r in Ioo ρ σ, cubeBoundaryIntegral r g := by
      rw [hM1, div_one, Real.rpow_one]
    rw [e, e2] at hH1
    exact hH1
  have hK0 : 0 ≤ 1 / (m * I) := by positivity
  -- Integrability
  have hS_meas : MeasurableSet {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ} :=
    (measurableSet_lt measurable_const measurable_norm).inter
      (measurableSet_lt measurable_norm measurable_const)
  have hhc : ContinuousOn (fun r => ((G r)⁻¹ / I) ^ 2) (Icc ρ σ) :=
    ((hG'.inv₀ (fun r hr => (hGpos r hr).ne')).div_const I).pow 2
  have hcpt : IsCompact {x : Vec (n + 1) | ρ ≤ ‖x‖ ∧ ‖x‖ ≤ σ} := by
    refine (isCompact_closedBall (0 : Vec (n + 1)) σ).of_isClosed_subset
      ((isClosed_le continuous_const continuous_norm).inter
        (isClosed_le continuous_norm continuous_const)) ?_
    intro x hx
    simpa using hx.2
  have hcf : ContinuousOn (fun x : Vec (n + 1) => g x * ((G ‖x‖)⁻¹ / I) ^ 2)
      {x : Vec (n + 1) | ρ ≤ ‖x‖ ∧ ‖x‖ ≤ σ} :=
    hgc.continuousOn.mul (hhc.comp continuous_norm.continuousOn (fun x hx => hx))
  have hfint : IntegrableOn (fun x : Vec (n + 1) => g x * ((G ‖x‖)⁻¹ / I) ^ 2)
      {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ} :=
    (hcf.integrableOn_compact hcpt).mono_set (fun x hx => ⟨hx.1.le, hx.2.le⟩)
  -- Gradient
  have hgrad := gradient_comp_norm_ae (d := n + 1) (φ := φ)
    (dφ := fun r => -(G r)⁻¹ / I) (ρ := ρ) (σ := σ) hderiv
  have hae : ∀ᵐ x ∂(volume.restrict {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ}),
      g x * vecNormSq (classicalGradient (fun y : Vec (n + 1) => φ ‖y‖) x) =
        g x * ((G ‖x‖)⁻¹ / I) ^ 2 := by
    rw [ae_restrict_iff' hS_meas]
    filter_upwards [hgrad] with x hx hxS
    rw [hx hxS.1 hxS.2]
    ring
  have hintegr : IntegrableOn (fun x : Vec (n + 1) =>
      g x * vecNormSq (classicalGradient (fun y : Vec (n + 1) => φ ‖y‖) x))
      {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ} :=
    hfint.congr (hae.mono (fun x hx => hx.symm))
  have step1 : ∫ x in {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ},
      g x * vecNormSq (classicalGradient (fun y : Vec (n + 1) => φ ‖y‖) x) =
      ∫ x in {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ}, g x * ((G ‖x‖)⁻¹ / I) ^ 2 := by
    refine setIntegral_congr_ae hS_meas ?_
    filter_upwards [hgrad] with x hx hxS
    rw [hx hxS.1 hxS.2]
    ring
  have step2 := integral_shell_eq_boundaryIntegral hρ (σ := σ) hfint
  have step3 : ∫ r in Ioo ρ σ,
      cubeBoundaryIntegral r (fun x : Vec (n + 1) => g x * ((G ‖x‖)⁻¹ / I) ^ 2) =
      ∫ r in Ioo ρ σ, (G r)⁻¹ / I ^ 2 := by
    refine setIntegral_congr_fun measurableSet_Ioo (fun r hr => ?_)
    have hr0 : 0 ≤ r := (hρ.trans hr.1).le
    have h := cubeBoundaryIntegral_mul_norm hr0 g (fun r => ((G r)⁻¹ / I) ^ 2)
    refine h.trans ?_
    show cubeBoundaryIntegral r g * ((G r)⁻¹ / I) ^ 2 = (G r)⁻¹ / I ^ 2
    rw [← hGdef r]
    have : G r ≠ 0 := (hGpos r (Ioo_subset_Icc_self hr)).ne'
    field_simp
  have step4 : ∫ r in Ioo ρ σ, (G r)⁻¹ / I ^ 2 = 1 / I := by
    rw [integral_div, ← hI']
    field_simp
  have hval : ∫ x in {x : Vec (n + 1) | ρ < ‖x‖ ∧ ‖x‖ < σ},
      g x * vecNormSq (classicalGradient (fun y : Vec (n + 1) => φ ‖y‖) x) = 1 / I := by
    rw [step1, step2, step3, step4]
  have hfin : 1 / I ≤ (σ - ρ) ^ (-(1 + 1 / δ)) *
      (∫ r in Ioo ρ σ, (cubeBoundaryIntegral r g) ^ δ) ^ (1 / δ) := by
    rw [Real.rpow_neg hL.le, inv_mul_eq_div]
    have hLp : 0 < (σ - ρ) ^ (1 + 1 / δ) := Real.rpow_pos_of_pos hL _
    rw [div_le_div_iff₀ hI0 hLp]
    linarith
  refine ⟨1 / (m * I), fun x => φ ‖x‖, hK0, ?_, ?_, ?_, ?_, ?_, hintegr, ?_⟩
  · calc 1 / (m * I) = (1 / I) / m := by field_simp
      _ ≤ _ := by gcongr
  · have := eucLip_comp_norm (d := n + 1) hlip
    rwa [Real.coe_toNNReal _ hK0] at this
  · intro x; exact hrange _
  · intro x hx; exact hφ1 _ hx
  · intro x hx; exact hφ0 _ hx
  · rw [hval]; exact hfin

end PDE.BSlocalmax
end

-- ==== from BoundaryContinuity.lean ====
-- Continuity and lower bound of the boundary integral
-- r ↦ ∫_{∂Q_r} g for continuous g (hypotheses of `exists_cutoff_cubeShell`).


@[expose] public section

open MeasureTheory Set Filter Topology PDE PDE.Ch4Infra

namespace PDE.BSlocalmax

variable {n : ℕ}

/-- Continuity of the face integral in `r > 0` (dominated convergence). -/
theorem continuousAt_faceIntegral [NeZero n] {g : Vec (n + 1) → ℝ} (hgc : Continuous g)
    (i : Fin (n + 1)) {s : ℝ} (hs : |s| = 1) {r₀ : ℝ} (hr₀ : 0 < r₀) :
    ContinuousAt (fun r => faceIntegral i s r g) r₀ := by
  obtain ⟨B, hB⟩ : ∃ B, ∀ x ∈ Metric.closedBall (0 : Vec (n + 1)) (2 * r₀), ‖g x‖ ≤ B :=
    (isCompact_closedBall (0 : Vec (n + 1)) (2 * r₀)).exists_bound_of_continuousOn
      hgc.continuousOn
  have hB0 : 0 ≤ B := le_trans (norm_nonneg _) (hB 0 (by simp; linarith))
  have hcubem : ∀ r : ℝ, MeasurableSet (Set.pi Set.univ (fun _ : Fin n => Icc (-r) r)) :=
    fun r => MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have hcubec : ∀ r : ℝ, IsCompact (Set.pi Set.univ (fun _ : Fin n => Icc (-r) r)) :=
    fun r => isCompact_univ_pi (fun _ => isCompact_Icc)
  have hface : (fun r => faceIntegral i s r g) = fun r => ∫ y : Fin n → ℝ,
      (Set.pi Set.univ (fun _ : Fin n => Icc (-r) r)).indicator
        (fun y => g (Fin.insertNth i (s * r) y)) y := by
    funext r
    unfold faceIntegral
    exact (integral_indicator (hcubem r)).symm
  rw [hface]
  have hins : ∀ r : ℝ, Continuous (fun y : Fin n → ℝ => g (Fin.insertNth i (s * r) y)) :=
    fun r => hgc.comp (Continuous.finInsertNth i continuous_const continuous_id)
  refine continuousAt_of_dominated
    (bound := (Set.pi Set.univ (fun _ : Fin n => Icc (-(2 * r₀)) (2 * r₀))).indicator
      (fun _ => B)) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall (fun r =>
      (hins r).aestronglyMeasurable.indicator (hcubem r))
  · filter_upwards [Ioo_mem_nhds (by linarith : r₀ / 2 < r₀) (by linarith : r₀ < 2 * r₀)]
      with r hr
    refine Filter.Eventually.of_forall (fun y => ?_)
    by_cases hy : y ∈ Set.pi Set.univ (fun _ : Fin n => Icc (-r) r)
    · have hy2 : y ∈ Set.pi Set.univ (fun _ : Fin n => Icc (-(2 * r₀)) (2 * r₀)) := by
        rw [mem_univ_pi] at hy ⊢
        intro j
        have := hy j
        exact ⟨by linarith [this.1, hr.2], by linarith [this.2, hr.2]⟩
      rw [indicator_of_mem hy, indicator_of_mem hy2]
      refine hB _ ?_
      have := norm_insertNth_face i hs (by linarith [hr.1] : 0 ≤ r) hy
      simp [Metric.mem_closedBall, this]
      linarith [hr.2]
    · rw [indicator_of_notMem hy]
      simp only [norm_zero]
      exact Set.indicator_nonneg (fun _ _ => hB0) y
  · exact (integrable_indicator_iff (hcubem _)).2
      (integrableOn_const (hcubec _).measure_lt_top.ne)
  · have hs1 : ∀ᵐ y : Fin n → ℝ, ‖y‖ ≠ r₀ :=
      ae_iff.2 (by simpa using volume_supNorm_sphere (0 : Vec n) r₀)
    filter_upwards [hs1] with y hy
    rcases lt_or_gt_of_ne hy with hlt | hgt
    · have hev : ∀ᶠ r in 𝓝 r₀, (Set.pi Set.univ (fun _ : Fin n => Icc (-r) r)).indicator
          (fun y => g (Fin.insertNth i (s * r) y)) y = g (Fin.insertNth i (s * r) y) := by
        filter_upwards [Ioi_mem_nhds hlt] with r hr
        have hmem : y ∈ Set.pi Set.univ (fun _ : Fin n => Icc (-r) r) := by
          rw [mem_univ_pi]
          intro j
          have hj : |y j| ≤ ‖y‖ := by
            simpa [Real.norm_eq_abs] using norm_le_pi_norm y j
          exact abs_le.1 (hj.trans hr.le)
        exact indicator_of_mem hmem _
      have hc : ContinuousAt (fun r : ℝ => g (Fin.insertNth i (s * r) y)) r₀ :=
        (hgc.comp (Continuous.finInsertNth i (continuous_const.mul continuous_id)
          continuous_const)).continuousAt
      exact hc.congr (hev.mono (fun r h => h.symm))
    · have hev : ∀ᶠ r in 𝓝 r₀, (0 : ℝ) = (Set.pi Set.univ (fun _ : Fin n => Icc (-r) r)).indicator
          (fun y => g (Fin.insertNth i (s * r) y)) y := by
        filter_upwards [Iio_mem_nhds hgt] with r hr
        have hnot : y ∉ Set.pi Set.univ (fun _ : Fin n => Icc (-r) r) := by
          intro hmem
          obtain ⟨j, hj⟩ := exists_coord_eq_norm y
          have := abs_le.2 (mem_univ_pi.1 hmem j)
          linarith [hj, this, hr.out]
        exact (indicator_of_notMem hnot _).symm
      exact continuousAt_const.congr hev

theorem continuousOn_cubeBoundaryIntegral [NeZero n] {g : Vec (n + 1) → ℝ}
    (hgc : Continuous g) :
    ContinuousOn (fun r => cubeBoundaryIntegral r g) (Ioi 0) := by
  unfold cubeBoundaryIntegral
  refine continuousOn_finsetSum _ (fun i _ => continuousOn_finsetSum _ (fun s hs => ?_))
  have hs1 : |s| = 1 := by
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl <;> simp
  intro r hr
  exact (continuousAt_faceIntegral hgc i hs1 hr).continuousWithinAt

/-- Volume of the `n`-dimensional cube. -/
lemma volume_real_cube (r : ℝ) (hr : 0 ≤ r) :
    (volume (Set.pi Set.univ (fun _ : Fin n => Icc (-r) r))).toReal = (2 * r) ^ n := by
  have e : r - -r = 2 * r := by ring
  have h : volume (Set.pi Set.univ (fun _ : Fin n => Icc (-r) r)) =
      ENNReal.ofReal (2 * r) ^ n := by
    rw [volume_pi, Measure.pi_pi]
    simp only [Real.volume_Icc, e, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [h, ENNReal.toReal_pow, ENNReal.toReal_ofReal (by positivity)]

/-- Lower bound for the face integral. -/
lemma faceIntegral_ge {g : Vec (n + 1) → ℝ} (hgc : Continuous g) {m : ℝ}
    (hm : ∀ x, m ≤ g x) (i : Fin (n + 1)) {s r : ℝ} (hr : 0 ≤ r) :
    m * (2 * r) ^ n ≤ faceIntegral i s r g := by
  unfold faceIntegral
  have hcubem : MeasurableSet (Set.pi Set.univ (fun _ : Fin n => Icc (-r) r)) :=
    MeasurableSet.univ_pi (fun _ => measurableSet_Icc)
  have hcubec : IsCompact (Set.pi Set.univ (fun _ : Fin n => Icc (-r) r)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hfi : IntegrableOn (fun y : Fin n → ℝ => g (Fin.insertNth i (s * r) y))
      (Set.pi Set.univ (fun _ : Fin n => Icc (-r) r)) :=
    (hgc.comp (Continuous.finInsertNth i continuous_const continuous_id)).continuousOn.integrableOn_compact
      hcubec
  have hci : IntegrableOn (fun _ : Fin n → ℝ => m)
      (Set.pi Set.univ (fun _ : Fin n => Icc (-r) r)) :=
    integrableOn_const hcubec.measure_lt_top.ne
  calc m * (2 * r) ^ n = ∫ _ in Set.pi Set.univ (fun _ : Fin n => Icc (-r) r), m := by
        rw [setIntegral_const]
        simp only [Measure.real, volume_real_cube r hr, smul_eq_mul]
        ring
    _ ≤ _ := setIntegral_mono_on hci hfi hcubem (fun y _ => hm _)

/-- Lower bound for the boundary integral. -/
lemma cubeBoundaryIntegral_ge {g : Vec (n + 1) → ℝ} (hgc : Continuous g) {m : ℝ}
    (hm0 : 0 ≤ m) (hm : ∀ x, m ≤ g x) {r : ℝ} (hr : 0 ≤ r) :
    m * (2 * r) ^ n ≤ cubeBoundaryIntegral r g := by
  unfold cubeBoundaryIntegral
  have hnn : 0 ≤ m * (2 * r) ^ n := by positivity
  have hterm : ∀ i : Fin (n + 1), ∀ s : ℝ, m * (2 * r) ^ n ≤ faceIntegral i s r g :=
    fun i s => faceIntegral_ge hgc hm i hr
  calc m * (2 * r) ^ n ≤ faceIntegral (0 : Fin (n + 1)) 1 r g := hterm 0 1
    _ ≤ ∑ s ∈ ({-1, 1} : Finset ℝ), faceIntegral (0 : Fin (n + 1)) s r g :=
        Finset.single_le_sum (f := fun s => faceIntegral (0 : Fin (n + 1)) s r g)
          (fun s _ => hnn.trans (hterm 0 s)) (by simp)
    _ ≤ ∑ i : Fin (n + 1), ∑ s ∈ ({-1, 1} : Finset ℝ), faceIntegral i s r g :=
        Finset.single_le_sum
          (f := fun i : Fin (n + 1) => ∑ s ∈ ({-1, 1} : Finset ℝ), faceIntegral i s r g)
          (fun i _ => Finset.sum_nonneg (fun s _ => hnn.trans (hterm i s)))
          (Finset.mem_univ 0)

/-- Both hypotheses of `exists_cutoff_cubeShell` for continuous `g ≥ m > 0`. -/
theorem boundaryIntegral_hyps [NeZero n] {g : Vec (n + 1) → ℝ} (hgc : Continuous g) {m : ℝ}
    (hm : 0 < m) (hgm : ∀ x, m ≤ g x) {ρ σ : ℝ} (hρ : 0 < ρ) :
    ContinuousOn (fun r => cubeBoundaryIntegral r g) (Icc ρ σ) ∧
      ∀ r ∈ Icc ρ σ, m * (2 * ρ) ^ n ≤ cubeBoundaryIntegral r g := by
  refine ⟨(continuousOn_cubeBoundaryIntegral hgc).mono (fun r hr => lt_of_lt_of_le hρ hr.1),
    fun r hr => ?_⟩
  have h1 := cubeBoundaryIntegral_ge hgc hm.le hgm (hρ.le.trans hr.1)
  have h2 : (2 * ρ) ^ n ≤ (2 * r) ^ n :=
    pow_le_pow_left₀ (by positivity) (by linarith [hr.1]) n
  exact (mul_le_mul_of_nonneg_left h2 hm.le).trans h1

end PDE.BSlocalmax
end
