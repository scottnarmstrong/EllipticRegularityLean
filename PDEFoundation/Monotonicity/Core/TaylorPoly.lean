module

public import PDEFoundation.Ambient.Basis
public import PDEFoundation.Geometry.EuclideanBall.Topology
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Taylor polynomials on `Vec d`

Pure calculus on the native carrier `Vec d = Fin d → ℝ`:

* a continuous `j`-linear form on `Vec d` is the evaluation of a homogeneous `MvPolynomial`
  of degree `j` (`multilinearPoly`);
* the line derivative `(d/dt)^j f (t • x) = D^j f (t • x) (x, …, x)`;
* Taylor's formula along the segment `t ↦ t • x` with Lagrange remainder;
* a smooth function whose `(k+1)`-st derivative vanishes identically is a polynomial of total
  degree at most `k`.
-/

@[expose] public section

open scoped BigOperators

namespace PDE

noncomputable section

variable {d : ℕ}

/-! ### Multilinear forms as homogeneous polynomials -/

/-- The homogeneous polynomial of degree `j` representing a continuous `j`-linear form: the sum
over multi-indices `i : Fin j → Fin d` of `A (e_{i 0}, …, e_{i (j-1)}) * ∏ X_{i l}`. -/
def multilinearPoly {j : ℕ} (A : ContinuousMultilinearMap ℝ (fun _ : Fin j => Vec d) ℝ) :
    MvPolynomial (Fin d) ℝ :=
  ∑ i : Fin j → Fin d,
    MvPolynomial.C (A fun l => basisVec (i l)) * ∏ l, MvPolynomial.X (i l)

theorem multilinearPoly_isHomogeneous {j : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin j => Vec d) ℝ) :
    (multilinearPoly A).IsHomogeneous j := by
  unfold multilinearPoly
  refine MvPolynomial.IsHomogeneous.sum _ _ _ fun i _ => ?_
  have h : (∏ l : Fin j, (MvPolynomial.X (i l) : MvPolynomial (Fin d) ℝ)).IsHomogeneous j := by
    have := MvPolynomial.IsHomogeneous.prod (Finset.univ : Finset (Fin j))
      (fun l => (MvPolynomial.X (i l) : MvPolynomial (Fin d) ℝ)) (fun _ => 1)
      (fun l _ => MvPolynomial.isHomogeneous_X ℝ (i l))
    simpa using this
  simpa using (MvPolynomial.isHomogeneous_C (Fin d) (A fun l => basisVec (i l))).mul h

theorem vec_eq_sum_basisVec (x : Vec d) : x = ∑ a, x a • basisVec a := by
  ext b
  simp [basisVec, Pi.single_apply]

theorem eval_multilinearPoly {j : ℕ}
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin j => Vec d) ℝ) (x : Vec d) :
    MvPolynomial.eval x (multilinearPoly A) = A fun _ => x := by
  classical
  have hx : (fun _ : Fin j => x) = fun _ => ∑ a, x a • basisVec a := by
    funext _; exact vec_eq_sum_basisVec x
  have hs := A.toMultilinearMap.map_sum (g := fun (_ : Fin j) (a : Fin d) => x a • basisVec a)
  simp only [ContinuousMultilinearMap.coe_coe] at hs
  rw [hx, hs]
  unfold multilinearPoly
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have := A.toMultilinearMap.map_smul_univ (fun l => x (i l)) (fun l => basisVec (i l))
  simp only [ContinuousMultilinearMap.coe_coe] at this
  rw [this]
  simp [mul_comm, smul_eq_mul]


theorem euclideanBall_smul_mem {R : ℝ} {x : Vec d} (hx : x ∈ euclideanBall (0 : Vec d) R)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) : t • x ∈ euclideanBall (0 : Vec d) R := by
  change euclideanSqDist (t • x) 0 < R ^ 2
  have h := euclideanSqDist_smul_smul t x 0
  rw [smul_zero] at h
  have hx' : euclideanSqDist x 0 < R ^ 2 := hx
  have ht2 : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  rw [h]
  calc t ^ 2 * euclideanSqDist x 0 ≤ 1 * euclideanSqDist x 0 :=
        mul_le_mul_of_nonneg_right ht2 (euclideanSqDist_nonneg x 0)
    _ < R ^ 2 := by rwa [one_mul]

/-! ### Line derivatives -/

theorem iteratedDeriv_line {U : Set (Vec d)} (hU : IsOpen U) {f : Vec d → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (x : Vec d) (j : ℕ) :
    ∀ t : ℝ, t • x ∈ U →
      iteratedDeriv j (fun s : ℝ => f (s • x)) t =
        iteratedFDeriv ℝ j f (t • x) (fun _ => x) := by
  induction j with
  | zero => intro t _; simp
  | succ j ih =>
    intro t ht
    have hI : IsOpen {s : ℝ | s • x ∈ U} := hU.preimage (continuous_id.smul continuous_const)
    have heq : iteratedDeriv j (fun s : ℝ => f (s • x)) =ᶠ[nhds t]
        fun s => iteratedFDeriv ℝ j f (s • x) (fun _ => x) := by
      filter_upwards [hI.mem_nhds ht] with s hs using ih s hs
    rw [iteratedDeriv_succ, heq.deriv_eq]
    have hcd : ContDiffAt ℝ (⊤ : ℕ∞) f (t • x) := hf.contDiffAt (hU.mem_nhds ht)
    have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ j f) (t • x) :=
      hcd.differentiableAt_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top j)
    have h1 := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin j => Vec d) ℝ
      (fun _ => x)).hasFDerivAt.comp (t • x) hdiff.hasFDerivAt
    have h2 : HasDerivAt (fun s : ℝ => s • x) x t := by
      simpa using (hasDerivAt_id t).smul_const x
    have h3 := h1.comp_hasDerivAt t h2
    have h4 : deriv (fun s : ℝ => iteratedFDeriv ℝ j f (s • x) (fun _ => x)) t =
        fderiv ℝ (iteratedFDeriv ℝ j f) (t • x) x (fun _ => x) := h3.deriv
    rw [h4]
    exact (iteratedFDeriv_succ_apply_left (𝕜 := ℝ) (f := f) (fun _ : Fin (j + 1) => x)).symm

theorem contDiffOn_line {U : Set (Vec d)} {f : Vec d → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (x : Vec d) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun s : ℝ => f (s • x)) {s : ℝ | s • x ∈ U} :=
  hf.comp (contDiff_id.smul contDiff_const).contDiffOn (fun _ hs => hs)

/-! ### Taylor's formula along a segment -/

/-- Taylor's formula with Lagrange remainder along the segment `t ↦ t • x`, `t ∈ [0,1]`, in an
open set `U` star-shaped about `0`. -/
theorem taylor_line {U : Set (Vec d)} (hU : IsOpen U)
    (hstar : ∀ x ∈ U, ∀ t ∈ Set.Icc (0 : ℝ) 1, t • x ∈ U) {f : Vec d → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) {x : Vec d} (hx : x ∈ U) (k : ℕ) :
    ∃ ξ ∈ Set.Ioo (0 : ℝ) 1,
      f x = (∑ j ∈ Finset.range (k + 1),
          ((j.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ j f 0 (fun _ => x))) +
        iteratedFDeriv ℝ (k + 1) f (ξ • x) (fun _ => x) / ((k + 1).factorial : ℝ) := by
  have hI : IsOpen {s : ℝ | s • x ∈ U} := hU.preimage (continuous_id.smul continuous_const)
  have hsub : Set.uIcc (0 : ℝ) 1 ⊆ {s : ℝ | s • x ∈ U} := by
    intro s hs
    rw [Set.uIcc_of_le zero_le_one] at hs
    exact hstar x hx s hs
  have hg := contDiffOn_line hf x
  have hg' : ContDiffOn ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (fun s : ℝ => f (s • x)) (Set.uIcc 0 1) :=
    (hg.of_le (by exact_mod_cast le_top)).mono hsub
  obtain ⟨ξ, hξ, h⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (n := k) (x₀ := 0) (x := 1)
    (f := fun s : ℝ => f (s • x)) zero_ne_one hg'
  have hξ' : ξ ∈ Set.Ioo (0 : ℝ) 1 := by
    rwa [Set.uIoo_of_le zero_le_one] at hξ
  have hξU : ξ • x ∈ U := hstar x hx ξ (Set.Ioo_subset_Icc_self hξ')
  refine ⟨ξ, hξ', ?_⟩
  rw [taylor_within_apply] at h
  have h0 : (0 : ℝ) • x ∈ U := hstar x hx 0 ⟨le_rfl, zero_le_one⟩
  have hsum : ∀ j ∈ Finset.range (k + 1),
      (((j.factorial : ℝ)⁻¹ * (1 - 0) ^ j) • iteratedDerivWithin j (fun s : ℝ => f (s • x))
        (Set.uIcc 0 1) 0) = (j.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ j f 0 (fun _ => x) := by
    intro j _
    have hc : ContDiffAt ℝ (j : WithTop ℕ∞) (fun s : ℝ => f (s • x)) 0 :=
      ((hg.of_le (by exact_mod_cast le_top)).contDiffAt
        (hI.mem_nhds h0))
    rw [iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_uIcc zero_ne_one) hc
      (by simp), iteratedDeriv_line hU hf x j 0 h0]
    simp
  rw [Finset.sum_congr rfl hsum] at h
  simp only [sub_zero, one_pow, mul_one] at h
  have hit := iteratedDeriv_line hU hf x (k + 1) ξ hξU
  rw [hit] at h
  linarith [h, show f ((1 : ℝ) • x) = f x by simp]

/-! ### Functions with vanishing high derivative are polynomials -/

/-- The degree-`k` Taylor polynomial of `f` at `0`, as an `MvPolynomial`. -/
def taylorPoly (f : Vec d → ℝ) (k : ℕ) : MvPolynomial (Fin d) ℝ :=
  ∑ j ∈ Finset.range (k + 1),
    MvPolynomial.C ((j.factorial : ℝ)⁻¹) * multilinearPoly (iteratedFDeriv ℝ j f 0)

theorem eval_taylorPoly (f : Vec d → ℝ) (k : ℕ) (x : Vec d) :
    MvPolynomial.eval x (taylorPoly f k) =
      ∑ j ∈ Finset.range (k + 1), ((j.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ j f 0 (fun _ => x)) := by
  unfold taylorPoly
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, eval_multilinearPoly, MvPolynomial.eval_C]

theorem taylorPoly_totalDegree_le (f : Vec d → ℝ) (k : ℕ) :
    (taylorPoly f k).totalDegree ≤ k := by
  refine MvPolynomial.totalDegree_finsetSum_le fun j hj => ?_
  have hj' : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have h : (MvPolynomial.C ((j.factorial : ℝ)⁻¹) * multilinearPoly (iteratedFDeriv ℝ j f 0)
      : MvPolynomial (Fin d) ℝ).IsHomogeneous j := by
    simpa using (MvPolynomial.isHomogeneous_C (Fin d) ((j.factorial : ℝ)⁻¹)).mul
      (multilinearPoly_isHomogeneous (iteratedFDeriv ℝ j f 0))
  exact h.totalDegree_le.trans hj'

/-- A smooth function on a star-shaped open set whose `(k+1)`-st derivative vanishes is a
polynomial of total degree at most `k`. -/
theorem exists_mvPolynomial_of_iteratedFDeriv_eq_zero {U : Set (Vec d)} (hU : IsOpen U)
    (hstar : ∀ x ∈ U, ∀ t ∈ Set.Icc (0 : ℝ) 1, t • x ∈ U) {f : Vec d → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) {k : ℕ}
    (hzero : ∀ x ∈ U, iteratedFDeriv ℝ (k + 1) f x = 0) :
    ∃ p : MvPolynomial (Fin d) ℝ, p.totalDegree ≤ k ∧
      ∀ x ∈ U, f x = MvPolynomial.eval x p := by
  refine ⟨taylorPoly f k, taylorPoly_totalDegree_le f k, fun x hx => ?_⟩
  obtain ⟨ξ, hξ, h⟩ := taylor_line hU hstar hf hx k
  have hξU : ξ • x ∈ U := hstar x hx ξ (Set.Ioo_subset_Icc_self hξ)
  rw [hzero _ hξU] at h
  rw [eval_taylorPoly, h]
  simp

theorem exists_mvPolynomial_of_iteratedFDeriv_eq_zero_euclideanBall {R : ℝ} {f : Vec d → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (euclideanBall 0 R)) {k : ℕ}
    (hzero : ∀ x ∈ euclideanBall (0 : Vec d) R, iteratedFDeriv ℝ (k + 1) f x = 0) :
    ∃ p : MvPolynomial (Fin d) ℝ, p.totalDegree ≤ k ∧
      ∀ x ∈ euclideanBall (0 : Vec d) R, f x = MvPolynomial.eval x p :=
  exists_mvPolynomial_of_iteratedFDeriv_eq_zero (isOpen_euclideanBall 0 R)
    (fun _ hx _ ht => euclideanBall_smul_mem hx ht) hf hzero

theorem exists_mvPolynomial_of_iteratedFDeriv_eq_zero_univ {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {k : ℕ}
    (hzero : ∀ x, iteratedFDeriv ℝ (k + 1) f x = 0) :
    ∃ p : MvPolynomial (Fin d) ℝ, p.totalDegree ≤ k ∧
      ∀ x, f x = MvPolynomial.eval x p := by
  obtain ⟨p, hp, h⟩ := exists_mvPolynomial_of_iteratedFDeriv_eq_zero (U := Set.univ)
    isOpen_univ (fun _ _ _ _ => Set.mem_univ _) hf.contDiffOn (fun x _ => hzero x)
  exact ⟨p, hp, fun x => h x (Set.mem_univ x)⟩

end

end PDE
