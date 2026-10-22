module

public import PDEFoundation.Monotonicity.Core.HarmonicFacade
public import PDEFoundation.Analysis.IteratedCoordDeriv
public import PDEFoundation.Analysis.Newtonian.Defs

/-!
# Rellich field: pointwise divergence

For a harmonic `u` the Rellich field `F = |∇u|² x - 2 (x·∇u) ∇u` has divergence
`(d - 2) |∇u|²`.
-/

@[expose] public section

open Filter
open scoped Topology

namespace PDE

noncomputable section

variable {d : ℕ}

/-- The Rellich field `|∇u|² x - 2 (x·∇u) ∇u`. -/
def rellichField (u : Vec d → ℝ) (x : Vec d) : Vec d :=
  vecNormSq (classicalGradient u x) • x -
    (2 * vecDot x (classicalGradient u x)) • classicalGradient u x

theorem euclideanCoordDeriv_add_of_dA {f g : Vec d → ℝ} {x : Vec d} (k : Fin d)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    euclideanCoordDeriv k (fun y => f y + g y) x =
      euclideanCoordDeriv k f x + euclideanCoordDeriv k g x := by
  unfold euclideanCoordDeriv
  rw [fderiv_fun_add hf hg]
  rfl

theorem euclideanCoordDeriv_sub_of_dA {f g : Vec d → ℝ} {x : Vec d} (k : Fin d)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    euclideanCoordDeriv k (fun y => f y - g y) x =
      euclideanCoordDeriv k f x - euclideanCoordDeriv k g x := by
  unfold euclideanCoordDeriv
  rw [fderiv_fun_sub hf hg]
  rfl

theorem euclideanCoordDeriv_mul_of_dA {f g : Vec d → ℝ} {x : Vec d} (k : Fin d)
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    euclideanCoordDeriv k (fun y => f y * g y) x =
      f x * euclideanCoordDeriv k g x + g x * euclideanCoordDeriv k f x := by
  unfold euclideanCoordDeriv
  rw [fderiv_fun_mul hf hg]
  simp only [add_apply, smul_apply, smul_eq_mul]

theorem euclideanCoordDeriv_const_mul_of_dA {f : Vec d → ℝ} {x : Vec d} (k : Fin d) (c : ℝ)
    (hf : DifferentiableAt ℝ f x) :
    euclideanCoordDeriv k (fun y => c * f y) x = c * euclideanCoordDeriv k f x := by
  unfold euclideanCoordDeriv
  rw [fderiv_const_mul hf]
  rfl

theorem euclideanCoordDeriv_sum_of_dA {F : Fin d → Vec d → ℝ} {x : Vec d} (k : Fin d)
    (hF : ∀ i, DifferentiableAt ℝ (F i) x) :
    euclideanCoordDeriv k (fun y => ∑ i, F i y) x = ∑ i, euclideanCoordDeriv k (F i) x := by
  unfold euclideanCoordDeriv
  rw [fderiv_fun_sum (fun i _ => hF i)]
  simp

theorem euclideanCoordDeriv_coord (k i : Fin d) (x : Vec d) :
    euclideanCoordDeriv k (fun y : Vec d => y i) x = if k = i then 1 else 0 := by
  unfold euclideanCoordDeriv
  have hc : HasFDerivAt (fun z : Vec d => z i) (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin d => ℝ) i) x := hasFDerivAt_apply i x
  rw [hc.fderiv]
  simp [basisVec_apply, eq_comm]

theorem differentiableAt_coord (i : Fin d) (x : Vec d) :
    DifferentiableAt ℝ (fun y : Vec d => y i) x :=
  (hasFDerivAt_apply i x).differentiableAt

/-- The pointwise computation, with all inputs at the single point `x`. -/
theorem classicalDivergence_rellichField_aux {u : Vec d → ℝ} {x : Vec d}
    (hg : ∀ j, DifferentiableAt ℝ (euclideanCoordDeriv j u) x)
    (hsymm : ∀ i j, euclideanCoordSecondDeriv i j u x = euclideanCoordSecondDeriv j i u x)
    (hharm : euclideanCoordLaplacian u x = 0) :
    classicalDivergence (rellichField u) x = ((d : ℝ) - 2) * vecNormSq (classicalGradient u x) := by
  set g : Fin d → Vec d → ℝ := fun j => euclideanCoordDeriv j u with hgdef
  have hgd : ∀ j, DifferentiableAt ℝ (g j) x := hg
  set T : Fin d → Fin d → ℝ := fun k j => euclideanCoordDeriv k (g j) x with hT
  have hTsym : ∀ k j, T k j = T j k := fun k j => hsymm j k
  have hlap : ∑ k, T k k = 0 := hharm
  have ha : ∀ y, vecNormSq (classicalGradient u y) = ∑ j, g j y * g j y := fun y => rfl
  have he : ∀ y, vecDot y (classicalGradient u y) = ∑ i, y i * g i y := fun y => rfl
  have hadiff : DifferentiableAt ℝ (fun y => ∑ j, g j y * g j y) x :=
    DifferentiableAt.fun_sum fun j _ => (hgd j).fun_mul (hgd j)
  have hediff : DifferentiableAt ℝ (fun y => ∑ i, y i * g i y) x :=
    DifferentiableAt.fun_sum fun i _ => (differentiableAt_coord i x).fun_mul (hgd i)
  have hDa : ∀ k, euclideanCoordDeriv k (fun y => ∑ j, g j y * g j y) x =
      ∑ j, 2 * (g j x * T k j) := by
    intro k
    rw [euclideanCoordDeriv_sum_of_dA k (fun j => (hgd j).fun_mul (hgd j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [euclideanCoordDeriv_mul_of_dA k (hgd j) (hgd j)]
    ring
  have hDe : ∀ k, euclideanCoordDeriv k (fun y => ∑ i, y i * g i y) x =
      g k x + ∑ i, x i * T k i := by
    intro k
    rw [euclideanCoordDeriv_sum_of_dA k (fun i => (differentiableAt_coord i x).fun_mul (hgd i))]
    have : ∀ i, euclideanCoordDeriv k (fun y => y i * g i y) x =
        (if k = i then g i x else 0) + x i * T k i := by
      intro i
      rw [euclideanCoordDeriv_mul_of_dA k (differentiableAt_coord i x) (hgd i),
        euclideanCoordDeriv_coord]
      split_ifs <;> (simp only [T]; ring)
    simp_rw [this]
    rw [Finset.sum_add_distrib]
    simp
  have hterm : ∀ k, euclideanCoordDeriv k (fun y => (rellichField u y) k) x =
      (∑ j, g j x * g j x) + x k * ∑ j, 2 * (g j x * T k j) -
        2 * ((∑ i, x i * g i x) * T k k + g k x * (g k x + ∑ i, x i * T k i)) := by
    intro k
    have hfun : (fun y => (rellichField u y) k) = fun y =>
        (∑ j, g j y * g j y) * y k - (2 * (∑ i, y i * g i y)) * g k y := by
      funext y
      simp only [rellichField, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rfl
    rw [hfun, euclideanCoordDeriv_sub_of_dA k (hadiff.fun_mul (differentiableAt_coord k x))
        ((hediff.const_mul 2).fun_mul (hgd k)),
      euclideanCoordDeriv_mul_of_dA k hadiff (differentiableAt_coord k x),
      euclideanCoordDeriv_mul_of_dA k (hediff.const_mul 2) (hgd k),
      euclideanCoordDeriv_const_mul_of_dA k 2 hediff, hDa, hDe, euclideanCoordDeriv_coord]
    simp only [ite_true]
    change _ * 1 + _ * _ - _ = _
    ring
  have hPQ : ∑ k, ∑ j, x k * (2 * (g j x * T k j)) = 2 * ∑ k, ∑ i, g k x * (x i * T k i) := by
    have hsw : ∑ k, ∑ i, g k x * (x i * T k i) = ∑ k, ∑ j, x k * (g j x * T k j) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      rw [hTsym k i]
      ring
    rw [hsw, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hsum : ∀ k, (∑ j, g j x * g j x) + x k * ∑ j, 2 * (g j x * T k j) -
        2 * ((∑ i, x i * g i x) * T k k + g k x * (g k x + ∑ i, x i * T k i)) =
      (∑ j, g j x * g j x) + (∑ j, x k * (2 * (g j x * T k j))) -
        2 * ((∑ i, x i * g i x) * T k k) - 2 * (g k x * g k x) -
        2 * ∑ i, g k x * (x i * T k i) := by
    intro k
    have e1 : x k * ∑ j, 2 * (g j x * T k j) = ∑ j, x k * (2 * (g j x * T k j)) :=
      Finset.mul_sum _ _ _
    have e2 : g k x * ∑ i, x i * T k i = ∑ i, g k x * (x i * T k i) := Finset.mul_sum _ _ _
    rw [e1, mul_add (g k x), e2]
    ring
  unfold classicalDivergence
  simp_rw [hterm, hsum]
  rw [ha]
  have h1 : ∑ k, 2 * ((∑ i, x i * g i x) * T k k) = 2 * ((∑ i, x i * g i x) * ∑ k, T k k) := by
    rw [← Finset.mul_sum, ← Finset.mul_sum]
  have h2 : ∑ k, 2 * (g k x * g k x) = 2 * ∑ k, g k x * g k x := (Finset.mul_sum _ _ _).symm
  have h3 : ∑ k, 2 * ∑ i, g k x * (x i * T k i) = 2 * ∑ k, ∑ i, g k x * (x i * T k i) :=
    (Finset.mul_sum _ _ _).symm
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [h1, h2, h3, hPQ, hlap]
  ring

/-- The Rellich field of a smooth function is smooth. -/
theorem contDiffOn_rellichField_top {R : ℝ} {u : Vec d → ℝ}
    (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (euclideanBall (0 : Vec d) R)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (rellichField u) (euclideanBall (0 : Vec d) R) := by
  have hU : IsOpen (euclideanBall (0 : Vec d) R) := isOpen_euclideanBall 0 R
  have hg : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (euclideanCoordDeriv j u) (euclideanBall (0 : Vec d) R) :=
    fun j => contDiffOn_top_euclideanCoordDeriv hU hu j
  have hc : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Vec d => y i) (euclideanBall (0 : Vec d) R) :=
    fun i => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).contDiff.contDiffOn
  have ha : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => ∑ j, euclideanCoordDeriv j u y *
      euclideanCoordDeriv j u y) (euclideanBall (0 : Vec d) R) :=
    ContDiffOn.sum fun j _ => (hg j).mul (hg j)
  have he : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => ∑ i, y i * euclideanCoordDeriv i u y)
      (euclideanBall (0 : Vec d) R) :=
    ContDiffOn.sum fun i _ => (hc i).mul (hg i)
  refine contDiffOn_pi.2 fun k => ?_
  have : (fun y => rellichField u y k) = fun y =>
      (∑ j, euclideanCoordDeriv j u y * euclideanCoordDeriv j u y) * y k -
        (2 * ∑ i, y i * euclideanCoordDeriv i u y) * euclideanCoordDeriv k u y := by
    funext y
    simp only [rellichField, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  rw [this]
  exact (ha.mul (hc k)).sub ((contDiffOn_const.mul he).mul (hg k))

/-- The Rellich field of a harmonic function is `C¹` on the ball. -/
theorem contDiffOn_one_rellichField_of_harmonicOn (hd : 0 < d) {R : ℝ} {u : Vec d → ℝ}
    (hu : ContDiffOn ℝ 2 u (euclideanBall (0 : Vec d) R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0) :
    ContDiffOn ℝ 1 (rellichField u) (euclideanBall (0 : Vec d) R) :=
  (contDiffOn_rellichField_top (contDiffOn_top_of_harmonicOn hd hu hharm)).of_le
    (by exact_mod_cast le_top)

/-- Pointwise: `div F = (d - 2) |∇u|²` for the Rellich field of a harmonic function. -/
theorem classicalDivergence_rellichField_of_harmonicOn (hd : 0 < d) {R : ℝ} {u : Vec d → ℝ}
    (hu : ContDiffOn ℝ 2 u (euclideanBall (0 : Vec d) R))
    (hharm : ∀ x ∈ euclideanBall (0 : Vec d) R, euclideanCoordLaplacian u x = 0)
    {x : Vec d} (hx : x ∈ euclideanBall (0 : Vec d) R) :
    classicalDivergence (rellichField u) x =
      ((d : ℝ) - 2) * vecNormSq (classicalGradient u x) := by
  have hU : IsOpen (euclideanBall (0 : Vec d) R) := isOpen_euclideanBall 0 R
  have htop := contDiffOn_top_of_harmonicOn hd hu hharm
  refine classicalDivergence_rellichField_aux (fun j => ?_) (fun i j => ?_) (hharm x hx)
  · exact differentiableAt_of_contDiffOn_top hU (contDiffOn_top_euclideanCoordDeriv hU htop j) hx
  · exact euclideanCoordSecondDeriv_comm_of_contDiffAt (htop.contDiffAt (hU.mem_nhds hx)) i j

end

end PDE
