module

public import PDEFoundation.Monotonicity.Core.TaylorPoly
public import PDEFoundation.Sobolev.ClassicalGradient
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Homogeneous polynomials and homogeneous smooth functions on `Vec d`

* Homogeneous `MvPolynomial`s: scaling `eval (t • x) p = t ^ k * eval x p`, Euler's identity
  `x · ∇ p = k p`, and smoothness/analyticity of `eval p`.
* A function smooth near `0` with `f (t • x) = t ^ α * f x` for `t ∈ (0,1]`, not identically
  zero, has `α = k ∈ ℕ` and is a homogeneous polynomial of degree `k` on the ball.
-/

@[expose] public section

open scoped BigOperators

namespace PDE

noncomputable section

variable {d : ℕ}

/-! ### Homogeneous polynomials -/

theorem eval_smul_of_isHomogeneous {p : MvPolynomial (Fin d) ℝ} {k : ℕ}
    (hp : p.IsHomogeneous k) (t : ℝ) (x : Vec d) :
    MvPolynomial.eval (t • x) p = t ^ k * MvPolynomial.eval x p := by
  rw [MvPolynomial.eval_eq', MvPolynomial.eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : ∑ i, m i = k := by
    have := hp (MvPolynomial.mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  have : ∏ i, (t • x) i ^ m i = t ^ k * ∏ i, x i ^ m i := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow, Finset.prod_mul_distrib,
      Finset.prod_pow_eq_pow_sum, hdeg]
  rw [this]; ring

theorem analyticOnNhd_eval_mvPolynomial (p : MvPolynomial (Fin d) ℝ) :
    AnalyticOnNhd ℝ (fun x : Vec d => MvPolynomial.eval x p) Set.univ :=
  AnalyticOnNhd.eval_mvPolynomial p

theorem contDiff_eval_mvPolynomial (p : MvPolynomial (Fin d) ℝ) {n : ℕ∞} :
    ContDiff ℝ n (fun x : Vec d => MvPolynomial.eval x p) := by
  have h := (analyticOnNhd_eval_mvPolynomial p).contDiffOn (n := n)
  rw [contDiffOn_univ] at h
  exact h uniqueDiffOn_univ

theorem differentiable_eval_mvPolynomial (p : MvPolynomial (Fin d) ℝ) :
    Differentiable ℝ (fun x : Vec d => MvPolynomial.eval x p) :=
  (contDiff_eval_mvPolynomial p (n := 1)).differentiable (by simp)

/-- Euler's identity for homogeneous polynomials. -/
theorem vecDot_classicalGradient_eval_of_isHomogeneous {p : MvPolynomial (Fin d) ℝ} {k : ℕ}
    (hp : p.IsHomogeneous k) (x : Vec d) :
    vecDot x (classicalGradient (fun y => MvPolynomial.eval y p) x) =
      k * MvPolynomial.eval x p := by
  have hd := (differentiable_eval_mvPolynomial p) x
  have h1 : HasDerivAt (fun t : ℝ => MvPolynomial.eval (t • x) p)
      (fderiv ℝ (fun y => MvPolynomial.eval y p) ((1 : ℝ) • x) x) 1 := by
    have h2 : HasDerivAt (fun t : ℝ => t • x) x 1 := by
      simpa using (hasDerivAt_id (1 : ℝ)).smul_const x
    have h3 : HasFDerivAt (fun y => MvPolynomial.eval y p)
        (fderiv ℝ (fun y => MvPolynomial.eval y p) ((1 : ℝ) • x)) ((1 : ℝ) • x) := by
      rw [one_smul]; exact hd.hasFDerivAt
    exact h3.comp_hasDerivAt 1 h2
  have h4 : HasDerivAt (fun t : ℝ => MvPolynomial.eval (t • x) p)
      (k * MvPolynomial.eval x p) 1 := by
    have : (fun t : ℝ => MvPolynomial.eval (t • x) p) =
        fun t => t ^ k * MvPolynomial.eval x p := funext fun t => eval_smul_of_isHomogeneous hp t x
    rw [this]
    simpa using ((hasDerivAt_pow k (1 : ℝ)).mul_const (MvPolynomial.eval x p))
  have h5 := h1.unique h4
  rw [one_smul] at h5
  rw [vecDot_comm, ← fderiv_apply_eq_vecDot_classicalGradient]
  exact h5

/-! ### Homogeneous smooth functions -/

/-- Along a ray, a function with `f (t • x) = t ^ α * f x` on `(0,1]` has `j`-th derivative
`α (α - 1) ⋯ (α - j + 1) * s ^ (α - j) * f x` on `(0,1)`. -/
theorem iteratedDeriv_line_of_scaling {f : Vec d → ℝ} {x : Vec d} {α : ℝ}
    (h : ∀ t ∈ Set.Ioc (0 : ℝ) 1, f (t • x) = t ^ α * f x) (j : ℕ) :
    ∀ s ∈ Set.Ioo (0 : ℝ) 1, iteratedDeriv j (fun s : ℝ => f (s • x)) s =
      (∏ i ∈ Finset.range j, (α - i)) * s ^ (α - j) * f x := by
  induction j with
  | zero => intro s hs; simp [h s ⟨hs.1, hs.2.le⟩]
  | succ j ih =>
    intro s hs
    have heq : iteratedDeriv j (fun s : ℝ => f (s • x)) =ᶠ[nhds s]
        fun u => (∏ i ∈ Finset.range j, (α - i)) * u ^ (α - j) * f x := by
      filter_upwards [Ioo_mem_nhds hs.1 hs.2] with u hu using ih u hu
    rw [iteratedDeriv_succ, heq.deriv_eq]
    have hd := ((Real.hasDerivAt_rpow_const (p := α - j) (Or.inl hs.1.ne')).const_mul
      (∏ i ∈ Finset.range j, (α - i))).mul_const (f x)
    rw [hd.deriv, Finset.prod_range_succ]
    have hexp : α - ((j + 1 : ℕ) : ℝ) = α - j - 1 := by push_cast; ring
    rw [hexp]
    ring

theorem continuousAt_iteratedDeriv_line {U : Set (Vec d)} (hU : IsOpen U) {f : Vec d → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) {x : Vec d} (h0 : (0 : Vec d) ∈ U) (j : ℕ) :
    ContinuousAt (iteratedDeriv j (fun s : ℝ => f (s • x))) 0 := by
  have h0' : (0 : ℝ) • x ∈ U := by simpa using h0
  have hI : IsOpen {s : ℝ | s • x ∈ U} := hU.preimage (continuous_id.smul continuous_const)
  have heq : iteratedDeriv j (fun s : ℝ => f (s • x)) =ᶠ[nhds 0]
      fun t => iteratedFDeriv ℝ j f (t • x) (fun _ => x) := by
    filter_upwards [hI.mem_nhds h0'] with t ht using iteratedDeriv_line hU hf x j t ht
  refine ContinuousAt.congr ?_ heq.symm
  have hc : ContinuousAt (iteratedFDeriv ℝ j f) ((0 : ℝ) • x) :=
    (hf.contDiffAt (hU.mem_nhds h0')).continuousAt_iteratedFDeriv (mod_cast le_top)
  have h1 : ContinuousAt (fun t : ℝ => iteratedFDeriv ℝ j f (t • x)) 0 :=
    ContinuousAt.comp (g := iteratedFDeriv ℝ j f) (f := fun t : ℝ => t • x) hc
      (continuous_id.smul continuous_const).continuousAt
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Vec d) ℝ
    (fun _ => x)).continuous.continuousAt.comp h1

theorem zero_mem_of_star {U : Set (Vec d)}
    (hstar : ∀ x ∈ U, ∀ t ∈ Set.Icc (0 : ℝ) 1, t • x ∈ U) {x : Vec d} (hx : x ∈ U) :
    (0 : Vec d) ∈ U := by
  simpa using hstar x hx 0 ⟨le_rfl, zero_le_one⟩

/-- Smoothness at `0` forces the homogeneity exponent to be a natural number, unless the
function vanishes identically. -/
theorem exists_natCast_eq_of_scaling {U : Set (Vec d)} (hU : IsOpen U)
    (hstar : ∀ x ∈ U, ∀ t ∈ Set.Icc (0 : ℝ) 1, t • x ∈ U) {f : Vec d → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) {α : ℝ}
    (hα : ∀ x ∈ U, ∀ t ∈ Set.Ioc (0 : ℝ) 1, f (t • x) = t ^ α * f x)
    (hne : ∃ x ∈ U, f x ≠ 0) : ∃ k : ℕ, α = k := by
  by_contra hk
  push Not at hk
  obtain ⟨x, hx, hfx⟩ := hne
  have h0 := zero_mem_of_star hstar hx
  set j : ℕ := ⌊α⌋₊ + 1 with hj
  have hjα : α - j < 0 := sub_neg.2 (by rw [hj]; push_cast; exact Nat.lt_floor_add_one α)
  have hc : (∏ i ∈ Finset.range j, (α - i)) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i _ => sub_ne_zero.2 (hk i)
  have hcont := continuousAt_iteratedDeriv_line hU hf (x := x) h0 j
  have T1 := (hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))).norm
  have hpos : 0 < |(∏ i ∈ Finset.range j, (α - i))| * |f x| :=
    mul_pos (abs_pos.2 hc) (abs_pos.2 hfx)
  have T2 : Filter.Tendsto (fun s : ℝ => ‖iteratedDeriv j (fun s : ℝ => f (s • x)) s‖)
      (nhdsWithin 0 (Set.Ioi 0)) Filter.atTop := by
    have hr := (tendsto_rpow_neg_nhdsGT_zero hjα).const_mul_atTop hpos
    refine hr.congr' ?_
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with s hs
    rw [iteratedDeriv_line_of_scaling (hα x hx · · ) j s hs, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos (Real.rpow_pos_of_pos hs.1 _)]
    ring
  exact not_tendsto_nhds_of_tendsto_atTop T2 _ T1

/-- A function smooth on a star-shaped open set with `f (t • x) = t ^ k * f x` is the evaluation
of a homogeneous polynomial of degree `k`. -/
theorem exists_isHomogeneous_of_scaling_natCast {U : Set (Vec d)} (hU : IsOpen U)
    (hstar : ∀ x ∈ U, ∀ t ∈ Set.Icc (0 : ℝ) 1, t • x ∈ U) {f : Vec d → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) {k : ℕ}
    (hα : ∀ x ∈ U, ∀ t ∈ Set.Ioc (0 : ℝ) 1, f (t • x) = t ^ (k : ℝ) * f x) :
    ∃ p : MvPolynomial (Fin d) ℝ, p.IsHomogeneous k ∧ ∀ x ∈ U, f x = MvPolynomial.eval x p := by
  have hhom : (MvPolynomial.C ((k.factorial : ℝ)⁻¹) * multilinearPoly (iteratedFDeriv ℝ k f 0)
      : MvPolynomial (Fin d) ℝ).IsHomogeneous k := by
    simpa using (MvPolynomial.isHomogeneous_C (Fin d) ((k.factorial : ℝ)⁻¹)).mul
      (multilinearPoly_isHomogeneous (iteratedFDeriv ℝ k f 0))
  refine ⟨_, hhom, fun x hx => ?_⟩
  have h0 := zero_mem_of_star hstar hx
  obtain ⟨ξ, hξ, h⟩ := taylor_line hU hstar hf hx k
  have hξU : ξ • x ∈ U := hstar x hx ξ (Set.Ioo_subset_Icc_self hξ)
  have hrem : iteratedFDeriv ℝ (k + 1) f (ξ • x) (fun _ => x) = 0 := by
    rw [← iteratedDeriv_line hU hf x (k + 1) ξ hξU,
      iteratedDeriv_line_of_scaling (hα x hx) (k + 1) ξ hξ]
    have : (∏ i ∈ Finset.range (k + 1), ((k : ℝ) - i)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_range.2 (Nat.lt_succ_self k)) (by simp)
    rw [this]; simp
  have hlow : ∀ j ∈ Finset.range (k + 1), j ≠ k →
      ((j.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ j f 0 (fun _ => x)) = 0 := by
    intro j hj hjk
    have hjk' : j < k := lt_of_le_of_ne (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)) hjk
    have hE : iteratedFDeriv ℝ j f 0 (fun _ => x) =
        iteratedDeriv j (fun s : ℝ => f (s • x)) 0 := by
      have := iteratedDeriv_line hU hf x j 0 (by simpa using h0)
      simpa using this.symm
    have hcont := continuousAt_iteratedDeriv_line hU hf (x := x) h0 j
    have T1 := hcont.tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    have hexp : (0 : ℝ) < k - j := sub_pos.2 (by exact_mod_cast hjk')
    have T2 : Filter.Tendsto (iteratedDeriv j (fun s : ℝ => f (s • x)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hr : Filter.Tendsto (fun s : ℝ => (∏ i ∈ Finset.range j, ((k : ℝ) - i)) * s ^ ((k : ℝ) - j)
          * f x) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((∏ i ∈ Finset.range j, ((k : ℝ) - i)) *
            (0 : ℝ) ^ ((k : ℝ) - j) * f x)) :=
        ((((Real.continuous_rpow_const hexp.le).tendsto 0).const_mul _).mul_const _).mono_left
          nhdsWithin_le_nhds
      rw [Real.zero_rpow hexp.ne'] at hr
      simp only [mul_zero, zero_mul] at hr
      refine hr.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with s hs
      exact (iteratedDeriv_line_of_scaling (hα x hx) j s hs).symm
    rw [hE, tendsto_nhds_unique T1 T2]
    simp
  rw [map_mul, eval_multilinearPoly, MvPolynomial.eval_C]
  rw [hrem, zero_div, add_zero, Finset.sum_eq_single k hlow (by simp)] at h
  exact h

theorem exists_isHomogeneous_of_scaling {U : Set (Vec d)} (hU : IsOpen U)
    (hstar : ∀ x ∈ U, ∀ t ∈ Set.Icc (0 : ℝ) 1, t • x ∈ U) {f : Vec d → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) {α : ℝ}
    (hα : ∀ x ∈ U, ∀ t ∈ Set.Ioc (0 : ℝ) 1, f (t • x) = t ^ α * f x)
    (hne : ∃ x ∈ U, f x ≠ 0) :
    ∃ k : ℕ, α = k ∧ ∃ p : MvPolynomial (Fin d) ℝ, p.IsHomogeneous k ∧
      ∀ x ∈ U, f x = MvPolynomial.eval x p := by
  obtain ⟨k, rfl⟩ := exists_natCast_eq_of_scaling hU hstar hf hα hne
  exact ⟨k, rfl, exists_isHomogeneous_of_scaling_natCast hU hstar hf hα⟩

/-- Ball version: ball version of `exists_isHomogeneous_of_scaling`. -/
theorem exists_isHomogeneous_of_scaling_euclideanBall {R : ℝ} {f : Vec d → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (euclideanBall 0 R)) {α : ℝ}
    (hα : ∀ x ∈ euclideanBall (0 : Vec d) R, ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      f (t • x) = t ^ α * f x)
    (hne : ∃ x ∈ euclideanBall (0 : Vec d) R, f x ≠ 0) :
    ∃ k : ℕ, α = k ∧ ∃ p : MvPolynomial (Fin d) ℝ, p.IsHomogeneous k ∧
      ∀ x ∈ euclideanBall (0 : Vec d) R, f x = MvPolynomial.eval x p :=
  exists_isHomogeneous_of_scaling (isOpen_euclideanBall 0 R)
    (fun _ hx _ ht => euclideanBall_smul_mem hx ht) hf hα hne

end

end PDE
