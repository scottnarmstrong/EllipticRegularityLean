module

public import PDEFoundation.Monotonicity.Defs
public import PDEFoundation.PDE.HarmonicMeanValueLocal
public import PDEFoundation.Sobolev.ClassicalGradient

/-!
# Chapter 2 harmonic facade: the Euler field and coordinate derivatives

Local calculus on an open set `U` for functions that are `C^∞` on `U`: the coordinate Laplacian
of `y ↦ y i * f y` and of finite sums, and the harmonicity of the Euler field `x ↦ x · ∇u`.
-/

@[expose] public section

open Filter
open scoped Topology

namespace PDE

noncomputable section

variable {d : ℕ}

theorem differentiableAt_of_contDiffOn_top {U : Set (Vec d)} (hU : IsOpen U) {f : Vec d → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) {y : Vec d} (hy : y ∈ U) : DifferentiableAt ℝ f y :=
  (hf.contDiffAt (hU.mem_nhds hy)).differentiableAt (by simp)

theorem contDiffOn_top_euclideanCoordDeriv {U : Set (Vec d)} (hU : IsOpen U) {f : Vec d → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (i : Fin d) :
    ContDiffOn ℝ (⊤ : ℕ∞) (euclideanCoordDeriv i f) U := by
  have hderiv : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ f) U :=
    (contDiffOn_infty_iff_fderiv_of_isOpen hU).mp hf |>.2
  unfold euclideanCoordDeriv
  exact hderiv.clm_apply contDiffOn_const

/-- First coordinate derivative of `y ↦ y i * f y` on an open set. -/
theorem euclideanCoordDeriv_coord_mul {U : Set (Vec d)} (hU : IsOpen U) {f : Vec d → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (i j : Fin d) {y : Vec d} (hy : y ∈ U) :
    euclideanCoordDeriv j (fun z => z i * f z) y =
      basisVec j i * f y + y i * euclideanCoordDeriv j f y := by
  have hc : HasFDerivAt (fun z : Vec d => z i) (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin d => ℝ) i) y := hasFDerivAt_apply i y
  have hfd := (differentiableAt_of_contDiffOn_top hU hf hy).hasFDerivAt
  have h1 : HasFDerivAt (fun z : Vec d => z i * f z)
      (y i • fderiv ℝ f y + f y • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i) y :=
    hc.mul hfd
  have := h1.fderiv
  unfold euclideanCoordDeriv
  rw [this]
  simp only [add_apply, smul_apply, smul_eq_mul,
    ContinuousLinearMap.proj_apply]
  ring

/-- Laplacian of `y ↦ y i * f y` at a point of an open set. -/
theorem euclideanCoordLaplacian_coord_mul {U : Set (Vec d)} (hU : IsOpen U) {f : Vec d → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U) (i : Fin d) {x : Vec d} (hx : x ∈ U) :
    euclideanCoordLaplacian (fun z => z i * f z) x =
      2 * euclideanCoordDeriv i f x + x i * euclideanCoordLaplacian f x := by
  have hc : HasFDerivAt (fun z : Vec d => z i) (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin d => ℝ) i) x := hasFDerivAt_apply i x
  have hfd := (differentiableAt_of_contDiffOn_top hU hf hx).hasFDerivAt
  have hsecond : ∀ j : Fin d,
      euclideanCoordSecondDeriv j j (fun z => z i * f z) x =
        2 * (basisVec j i * euclideanCoordDeriv j f x) +
          x i * euclideanCoordSecondDeriv j j f x := by
    intro j
    have hgj : DifferentiableAt ℝ (euclideanCoordDeriv j f) x :=
      differentiableAt_of_contDiffOn_top hU (contDiffOn_top_euclideanCoordDeriv hU hf j) hx
    have hev : euclideanCoordDeriv j (fun z => z i * f z) =ᶠ[𝓝 x]
        fun z => basisVec j i * f z + z i * euclideanCoordDeriv j f z := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact euclideanCoordDeriv_coord_mul hU hf i j hy
    unfold euclideanCoordSecondDeriv
    rw [hev.fderiv_eq]
    have hD1 : HasFDerivAt (fun z : Vec d => basisVec j i * f z + z i * euclideanCoordDeriv j f z)
        (basisVec j i • fderiv ℝ f x + (x i • fderiv ℝ (euclideanCoordDeriv j f) x +
          euclideanCoordDeriv j f x • ContinuousLinearMap.proj (R := ℝ)
            (φ := fun _ : Fin d => ℝ) i)) x :=
      (hfd.const_mul (basisVec j i)).add (hc.mul hgj.hasFDerivAt)
    have hD := hD1.fderiv
    rw [hD]
    simp only [add_apply, smul_apply, smul_eq_mul,
      ContinuousLinearMap.proj_apply]
    change basisVec j i * euclideanCoordDeriv j f x + (x i * _ + _ * basisVec j i) = _
    ring
  rw [euclideanCoordLaplacian, Finset.sum_congr rfl fun j _ => hsecond j, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]
  have hsum : ∑ j : Fin d, basisVec j i * euclideanCoordDeriv j f x =
      euclideanCoordDeriv i f x := by
    simp_rw [basisVec_apply, ite_mul, one_mul, zero_mul]
    simp
  rw [hsum]
  rfl

/-- Laplacian of a finite sum at a point of an open set. -/
theorem euclideanCoordLaplacian_finset_sum {U : Set (Vec d)} (hU : IsOpen U)
    {F : Fin d → Vec d → ℝ} (hF : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (F i) U) {x : Vec d} (hx : x ∈ U) :
    euclideanCoordLaplacian (fun z => ∑ i, F i z) x = ∑ i, euclideanCoordLaplacian (F i) x := by
  have hfirst : ∀ j : Fin d, ∀ y ∈ U,
      euclideanCoordDeriv j (fun z => ∑ i, F i z) y = ∑ i, euclideanCoordDeriv j (F i) y := by
    intro j y hy
    have h := HasFDerivAt.sum (u := Finset.univ) (A := fun i z => F i z)
      (fun i _ => (differentiableAt_of_contDiffOn_top hU (hF i) hy).hasFDerivAt)
    unfold euclideanCoordDeriv
    rw [show (fun z => ∑ i, F i z) = ∑ i, F i from by funext z; simp] 
    rw [h.fderiv]
    simp
  have hsecond : ∀ j : Fin d,
      euclideanCoordSecondDeriv j j (fun z => ∑ i, F i z) x =
        ∑ i, euclideanCoordSecondDeriv j j (F i) x := by
    intro j
    have hev : euclideanCoordDeriv j (fun z => ∑ i, F i z) =ᶠ[𝓝 x]
        fun z => ∑ i, euclideanCoordDeriv j (F i) z := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact hfirst j y hy
    unfold euclideanCoordSecondDeriv
    rw [hev.fderiv_eq]
    have h := HasFDerivAt.sum (u := Finset.univ) (A := fun i z => euclideanCoordDeriv j (F i) z)
      (fun i _ => (differentiableAt_of_contDiffOn_top hU
        (contDiffOn_top_euclideanCoordDeriv hU (hF i) j) hx).hasFDerivAt)
    rw [show (fun z => ∑ i, euclideanCoordDeriv j (F i) z) =
      ∑ i, euclideanCoordDeriv j (F i) from by funext z; simp]
    rw [h.fderiv]
    simp
  unfold euclideanCoordLaplacian
  simp_rw [hsecond]
  exact Finset.sum_comm

/-- The Euler field `x ↦ x · ∇u` of a smooth harmonic function is harmonic. -/
theorem euclideanCoordLaplacian_euler_eq_zero {U : Set (Vec d)} (hU : IsOpen U) {u : Vec d → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) (hharm : ∀ x ∈ U, euclideanCoordLaplacian u x = 0)
    {x : Vec d} (hx : x ∈ U) :
    euclideanCoordLaplacian (fun y => vecDot y (classicalGradient u y)) x = 0 := by
  have hg : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (euclideanCoordDeriv i u) U :=
    fun i => (contDiffOn_euclideanCoordDeriv_and_harmonic hU hu hharm i).1
  have hgh : ∀ i, ∀ y ∈ U, euclideanCoordLaplacian (euclideanCoordDeriv i u) y = 0 :=
    fun i => (contDiffOn_euclideanCoordDeriv_and_harmonic hU hu hharm i).2
  have hprod : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (fun z : Vec d => z i * euclideanCoordDeriv i u z) U := by
    intro i
    have hcoord : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec d => z i) :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).contDiff
    exact hcoord.contDiffOn.mul (hg i)
  change euclideanCoordLaplacian (fun z => ∑ i, z i * euclideanCoordDeriv i u z) x = 0
  rw [euclideanCoordLaplacian_finset_sum hU hprod hx]
  have : ∀ i, euclideanCoordLaplacian (fun z => z i * euclideanCoordDeriv i u z) x =
      2 * euclideanCoordSecondDeriv i i u x := by
    intro i
    rw [euclideanCoordLaplacian_coord_mul hU (hg i) i hx, hgh i x hx, mul_zero, add_zero]
    rfl
  simp_rw [this]
  rw [← Finset.mul_sum]
  have hl : ∑ i, euclideanCoordSecondDeriv i i u x = 0 := hharm x hx
  rw [hl, mul_zero]

/-- The Euler field `x ↦ x · ∇u` of a smooth function is smooth. -/
theorem contDiffOn_euler {U : Set (Vec d)} (hU : IsOpen U) {u : Vec d → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun y => vecDot y (classicalGradient u y)) U := by
  change ContDiffOn ℝ (⊤ : ℕ∞) (fun z => ∑ i, z i * euclideanCoordDeriv i u z) U
  refine ContDiffOn.sum fun i _ => ?_
  have hcoord : ContDiff ℝ (⊤ : ℕ∞) (fun z : Vec d => z i) :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).contDiff
  exact hcoord.contDiffOn.mul (contDiffOn_top_euclideanCoordDeriv hU hu i)

end

end PDE
