module

public import PDEFoundation.Sobolev.ClassicalLaplacian
public import Mathlib.Analysis.Calculus.FDeriv.Congr

/-!
# Iterated coordinate derivatives on the native vector space

This module relates repeated derivatives in the shared coordinate directions
to Mathlib's iterated Fréchet derivative. In the recursive convention below,
the first listed index is applied last (as the outermost coordinate
derivative).
-/

@[expose] public section

namespace PDE

open Filter Set
open scoped Topology

noncomputable section

/-- The repeated coordinate derivative associated with a finite list of
indices. Recursion removes the first index and applies it as the outermost
coordinate derivative. -/
def iteratedCoordDeriv {d : ℕ} : (m : ℕ) → (Fin m → Fin d) →
    (Vec d → ℝ) → Vec d → ℝ
  | 0, _, v => v
  | n + 1, ι, v =>
      euclideanCoordDeriv (ι 0) (iteratedCoordDeriv n (fun k => ι k.succ) v)

/-- A smooth function on an open set has a smooth coordinate derivative there,
even though `euclideanCoordDeriv` is defined using the global `fderiv`. -/
theorem contDiffOn_euclideanCoordDeriv_of_open {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) {v : Vec d → ℝ} (hv : ContDiffOn ℝ (⊤ : ℕ∞) v U)
    (i : Fin d) : ContDiffOn ℝ (⊤ : ℕ∞) (euclideanCoordDeriv i v) U := by
  unfold euclideanCoordDeriv
  have hfd : ContDiffOn ℝ (⊤ : ℕ∞) (fderiv ℝ v) U :=
    (contDiffOn_infty_iff_fderiv_of_isOpen hU).mp hv |>.2
  exact hfd.clm_apply contDiffOn_const

/-- Equality on an open set determines the global coordinate derivatives at
every point of that set. -/
theorem euclideanCoordDeriv_congrOn_open {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) {v w : Vec d → ℝ} (hvw : EqOn v w U) (i : Fin d) :
    EqOn (euclideanCoordDeriv i v) (euclideanCoordDeriv i w) U := by
  intro x hx
  have hlocal : v =ᶠ[𝓝 x] w := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hvw hy
  have hfd := hlocal.fderiv_eq (𝕜 := ℝ)
  simpa [euclideanCoordDeriv] using
    congrArg (fun L : Vec d →L[ℝ] ℝ => L (basisVec i)) hfd

/-- Every repeated coordinate derivative of a smooth function remains smooth
on the open set. -/
theorem contDiffOn_iteratedCoordDeriv {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) {v : Vec d → ℝ} (hv : ContDiffOn ℝ (⊤ : ℕ∞) v U)
    (m : ℕ) (ι : Fin m → Fin d) :
    ContDiffOn ℝ (⊤ : ℕ∞) (iteratedCoordDeriv m ι v) U := by
  induction m with
  | zero => simpa [iteratedCoordDeriv] using hv
  | succ m ih =>
      simpa only [iteratedCoordDeriv] using
        contDiffOn_euclideanCoordDeriv_of_open hU
          (ih (fun k => ι k.succ)) (ι 0)

/-- At points of an open set, the iterated Fréchet derivative equals the
recursive coordinate derivative. This also records why the global
`fderiv`-based coordinate derivative is valid under a local smoothness
hypothesis. -/
theorem iteratedFDeriv_eq_iteratedCoordDeriv {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) {v : Vec d → ℝ} (hv : ContDiffOn ℝ (⊤ : ℕ∞) v U)
    (m : ℕ) (ι : Fin m → Fin d) :
    ∀ x ∈ U,
      iteratedFDeriv ℝ m v x (fun k => basisVec (ι k)) =
        iteratedCoordDeriv m ι v x := by
  induction m with
  | zero =>
      intro x hx
      simp [iteratedCoordDeriv]
  | succ m ih =>
      intro x hx
      have hvx : ContDiffAt ℝ (⊤ : ℕ∞) v x :=
        (hv x hx).contDiffAt (hU.mem_nhds hx)
      have hmnInner : (1 : ℕ∞) + (m : ℕ∞) < ⊤ := by
        simp
      have hmn : (1 : WithTop ℕ∞) + (m : WithTop ℕ∞) ≤ (↑(⊤ : ℕ∞)) := by
        change (↑((1 : ℕ∞) + (m : ℕ∞)) : WithTop ℕ∞) ≤ ↑(⊤ : ℕ∞)
        exact le_of_lt (WithTop.coe_lt_coe.mpr hmnInner)
      have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ m v) x :=
        (hvx.iteratedFDeriv_right (m := 1) (i := m) hmn).differentiableAt (by norm_num)
      rw [DifferentiableAt.iteratedFDeriv_succ_apply_left' hdiff]
      have hlocal :
          (fun y => iteratedFDeriv ℝ m v y
            (fun k => basisVec (ι k.succ))) =ᶠ[𝓝 x]
          iteratedCoordDeriv m (fun k => ι k.succ) v := by
        filter_upwards [hU.mem_nhds hx] with y hy
        exact ih (fun k => ι k.succ) y hy
      have hfd := hlocal.fderiv_eq (𝕜 := ℝ)
      change fderiv ℝ
          (fun y => iteratedFDeriv ℝ m v y (fun k => basisVec (ι k.succ)))
          x (basisVec (ι 0)) =
        euclideanCoordDeriv (ι 0)
          (iteratedCoordDeriv m (fun k => ι k.succ) v) x
      rw [hfd]
      rfl

/-- A list-indexed presentation of repeated coordinate differentiation. -/
def iteratedCoordDerivList {d : ℕ} : List (Fin d) →
    (Vec d → ℝ) → Vec d → ℝ
  | [], v => v
  | i :: is, v => euclideanCoordDeriv i (iteratedCoordDerivList is v)

/-- The finite-index and list-index recursive definitions agree. -/
theorem iteratedCoordDeriv_eq_list {d : ℕ} (m : ℕ)
    (ι : Fin m → Fin d) (v : Vec d → ℝ) :
    iteratedCoordDeriv m ι v = iteratedCoordDerivList (List.ofFn ι) v := by
  induction m with
  | zero => simp [iteratedCoordDeriv, iteratedCoordDerivList]
  | succ m ih =>
      simp only [iteratedCoordDeriv, iteratedCoordDerivList, List.ofFn_succ]
      rw [ih]

/-- Repeated coordinate differentiation preserves smoothness on open sets. -/
theorem contDiffOn_iteratedCoordDerivList {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) {v : Vec d → ℝ} (hv : ContDiffOn ℝ (⊤ : ℕ∞) v U)
    (is : List (Fin d)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (iteratedCoordDerivList is v) U := by
  induction is with
  | nil => exact hv
  | cons i is ih => exact contDiffOn_euclideanCoordDeriv_of_open hU ih i

/-- Rewrite one nested pair of coordinate derivatives as a second partial. -/
private theorem iteratedCoordDerivList_cons_cons_eq_second
    {d : ℕ} (i j : Fin d) (is : List (Fin d)) (v : Vec d → ℝ) (x : Vec d) :
    iteratedCoordDerivList (i :: j :: is) v x =
      euclideanCoordSecondDeriv j i (iteratedCoordDerivList is v) x := rfl

private theorem euclideanCoordSecondDeriv_eq_fderiv_fderiv_of_contDiffAt
    {d : ℕ} {v : Vec d → ℝ} {x : Vec d} (hv : ContDiffAt ℝ (⊤ : ℕ∞) v x)
    (i j : Fin d) :
    euclideanCoordSecondDeriv i j v x =
      fderiv ℝ (fderiv ℝ v) x (basisVec j) (basisVec i) := by
  unfold euclideanCoordSecondDeriv euclideanCoordDeriv
  have hfd : DifferentiableAt ℝ (fderiv ℝ v) x := by
    have hcont : ContDiffAt ℝ (1 : ℕ∞) (fderiv ℝ v) x :=
      hv.fderiv_right (m := 1) (WithTop.coe_le_coe.2
        (show (2 : ℕ∞) ≤ ⊤ from le_top))
    exact hcont.differentiableAt (by norm_num)
  rw [fderiv_clm_apply]
  · simp
  · exact hfd
  · exact differentiableAt_const _

/-- The classical second coordinate derivatives commute under local smoothness.
Only `C²` regularity at the point is used. -/
theorem euclideanCoordSecondDeriv_comm_of_contDiffAt {d : ℕ}
    {v : Vec d → ℝ} {x : Vec d} (hv : ContDiffAt ℝ (⊤ : ℕ∞) v x)
    (i j : Fin d) :
    euclideanCoordSecondDeriv i j v x = euclideanCoordSecondDeriv j i v x := by
  have hsymm : IsSymmSndFDerivAt ℝ v x :=
    hv.isSymmSndFDerivAt (by
      rw [minSmoothness_of_isRCLikeNormedField]
      exact WithTop.coe_le_coe.2 (show (2 : ℕ∞) ≤ ⊤ from le_top))
  rw [euclideanCoordSecondDeriv_eq_fderiv_fderiv_of_contDiffAt hv i j,
    euclideanCoordSecondDeriv_eq_fderiv_fderiv_of_contDiffAt hv j i]
  exact hsymm.eq (basisVec j) (basisVec i)

/-- Reordering a list of indices does not change its iterated coordinate
derivative when the function is smooth on the open set. -/
theorem iteratedCoordDerivList_perm_eqOn {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) {v : Vec d → ℝ} (hv : ContDiffOn ℝ (⊤ : ℕ∞) v U)
    {is js : List (Fin d)} (hperm : is.Perm js) :
    EqOn (iteratedCoordDerivList is v) (iteratedCoordDerivList js v) U := by
  induction hperm with
  | nil => intro x hx; rfl
  | @cons i is js hperm ih =>
      exact euclideanCoordDeriv_congrOn_open hU ih i
  | @swap i j tail =>
      intro x hx
      have htail : ContDiffAt ℝ (⊤ : ℕ∞) (iteratedCoordDerivList tail v) x :=
        (contDiffOn_iteratedCoordDerivList hU hv tail x hx).contDiffAt
          (hU.mem_nhds hx)
      rw [iteratedCoordDerivList_cons_cons_eq_second,
        iteratedCoordDerivList_cons_cons_eq_second]
      exact (euclideanCoordSecondDeriv_comm_of_contDiffAt htail j i).symm
  | @trans is ms js h₁ h₂ ih₁ ih₂ =>
      intro x hx
      exact (ih₁ hx).trans (ih₂ hx)

/-- Iterated coordinate derivatives depend only on the function in a
neighborhood of the evaluation point. -/
theorem iteratedCoordDeriv_eventuallyEq {d : ℕ} {v w : Vec d → ℝ}
    (m : ℕ) (ι : Fin m → Fin d) {x : Vec d}
    (hvw : v =ᶠ[𝓝 x] w) :
    iteratedCoordDeriv m ι v =ᶠ[𝓝 x] iteratedCoordDeriv m ι w := by
  induction m with
  | zero => simpa [iteratedCoordDeriv] using hvw
  | succ m ih =>
      have hfd := ih (fun k => ι k.succ)
      have hcoord :
          euclideanCoordDeriv (ι 0)
            (iteratedCoordDeriv m (fun k => ι k.succ) v) =ᶠ[𝓝 x]
          euclideanCoordDeriv (ι 0)
            (iteratedCoordDeriv m (fun k => ι k.succ) w) := by
        filter_upwards [hfd.fderiv (𝕜 := ℝ)] with y hy
        exact congrArg (fun L : Vec d →L[ℝ] ℝ => L (basisVec (ι 0))) hy
      simpa only [iteratedCoordDeriv] using hcoord

/-- Pointwise locality for iterated coordinate derivatives. -/
theorem iteratedCoordDeriv_eq_of_eventuallyEq {d : ℕ}
    {v w : Vec d → ℝ} (m : ℕ) (ι : Fin m → Fin d) {x : Vec d}
    (hvw : v =ᶠ[𝓝 x] w) :
    iteratedCoordDeriv m ι v x = iteratedCoordDeriv m ι w x :=
  (iteratedCoordDeriv_eventuallyEq m ι hvw).self_of_nhds

/-- For a smooth function, the iterated coordinate derivative is invariant
under every permutation of its indices. The proof uses local symmetry of the
second derivative, so it needs only smoothness rather than analyticity. -/
theorem iteratedCoordDeriv_comp_perm {d : ℕ} {U : Set (Vec d)}
    (hU : IsOpen U) {v : Vec d → ℝ} (hv : ContDiffOn ℝ (⊤ : ℕ∞) v U)
    (m : ℕ) (ι : Fin m → Fin d) (σ : Equiv.Perm (Fin m)) :
    ∀ x ∈ U,
      iteratedCoordDeriv m (fun k => ι (σ k)) v x = iteratedCoordDeriv m ι v x := by
  intro x hx
  have hperm : List.Perm (List.ofFn (fun k => ι (σ k))) (List.ofFn ι) :=
    σ.ofFn_comp_perm ι
  have hlist := iteratedCoordDerivList_perm_eqOn hU hv hperm
  rw [iteratedCoordDeriv_eq_list, iteratedCoordDeriv_eq_list]
  exact hlist hx

end

end PDE
