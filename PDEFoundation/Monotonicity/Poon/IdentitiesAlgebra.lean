module

public import PDEFoundation.Monotonicity.Poon.IdentitiesCalculus

/-!
# Pointwise divergence identities for the Poon computation

For a smooth `v`, with `v_i = ∂ᵢ v`, `S j i = ∂ᵢ ∂ⱼ v`, `L = Δ v`, the five vector fields
`x_i v²`, `v v_i`, `v_i L`, `x_i |∇v|²`, `v_i (x·∇v)` have the divergences computed below.
-/

@[expose] public section

namespace PDE

noncomputable section

variable {d : ℕ}

/-- `|∇v|²` as a sum of coordinate products. -/
def pQ2 (v : Vec d → ℝ) (x : Vec d) : ℝ :=
  ∑ i, euclideanCoordDeriv i v x * euclideanCoordDeriv i v x

/-- Euler derivative `x · ∇v`. -/
def pP (v : Vec d → ℝ) (x : Vec d) : ℝ := ∑ i, x i * euclideanCoordDeriv i v x

/-- `Σ_{ij} x_j v_i ∂ᵢ∂ⱼ v`. -/
def pR (v : Vec d → ℝ) (x : Vec d) : ℝ :=
  ∑ i, ∑ j, x j * (euclideanCoordDeriv i v x * euclideanCoordSecondDeriv j i v x)

/-- `∇v · ∇Δv`. -/
def pV3 (v : Vec d → ℝ) (x : Vec d) : ℝ :=
  ∑ i, euclideanCoordDeriv i v x * euclideanCoordDeriv i (euclideanCoordLaplacian v) x

theorem coordSecond_eq (v : Vec d → ℝ) (i j : Fin d) :
    euclideanCoordSecondDeriv i j v = euclideanCoordDeriv j (euclideanCoordDeriv i v) := rfl

section

variable {v : Vec d → ℝ}

theorem sm_S (hv : Sm v) (i j : Fin d) : Sm (euclideanCoordSecondDeriv i j v) :=
  contDiff_euclideanCoordSecondDeriv hv i j

theorem sm_L (hv : Sm v) : Sm (euclideanCoordLaplacian v) := by
  unfold euclideanCoordLaplacian
  exact ContDiff.sum fun i _ => sm_S hv i i

theorem sm_pQ2 (hv : Sm v) : Sm (pQ2 v) := by
  unfold pQ2
  exact ContDiff.sum fun i _ => (hv.coordDeriv i).mul (hv.coordDeriv i)

theorem sm_pP (hv : Sm v) : Sm (pP v) := by
  unfold pP
  exact ContDiff.sum fun i _ => (sm_coord i).mul (hv.coordDeriv i)

theorem coordDeriv_pQ2 (hv : Sm v) (i : Fin d) (x : Vec d) :
    euclideanCoordDeriv i (pQ2 v) x =
      2 * ∑ j, euclideanCoordDeriv j v x * euclideanCoordSecondDeriv j i v x := by
  unfold pQ2
  rw [coordDeriv_sum _ (fun j => (hv.coordDeriv j).mul (hv.coordDeriv j)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coordDeriv_mul (hv.coordDeriv j) (hv.coordDeriv j)]
  rw [coordSecond_eq]
  ring

theorem coordDeriv_pP (hv : Sm v) (i : Fin d) (x : Vec d) :
    euclideanCoordDeriv i (pP v) x =
      euclideanCoordDeriv i v x + ∑ j, x j * euclideanCoordSecondDeriv j i v x := by
  unfold pP
  rw [coordDeriv_sum _ (fun j => (sm_coord j).mul (hv.coordDeriv j))]
  have : ∀ j, euclideanCoordDeriv i (fun y => y j * euclideanCoordDeriv j v y) x =
      (if i = j then euclideanCoordDeriv j v x else 0) +
        x j * euclideanCoordSecondDeriv j i v x := by
    intro j
    rw [coordDeriv_mul (sm_coord j) (hv.coordDeriv j), coordDeriv_coord]
    split_ifs <;> simp [coordSecond_eq]
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem deriv1 (hv : Sm v) (i : Fin d) (x : Vec d) :
    euclideanCoordDeriv i (fun y => y i * (v y * v y)) x =
      v x * v x + 2 * v x * (x i * euclideanCoordDeriv i v x) := by
    rw [coordDeriv_mul (sm_coord i) (hv.mul hv), coordDeriv_coord, coordDeriv_mul hv hv]
    simp only [ite_true]; ring

/-- Divergence of `x_i v²`. -/
theorem div1 (hv : Sm v) (x : Vec d) :
    ∑ i, euclideanCoordDeriv i (fun y => y i * (v y * v y)) x =
      (d : ℝ) * (v x * v x) + 2 * v x * pP v x := by
  have h : ∀ i, euclideanCoordDeriv i (fun y => y i * (v y * v y)) x =
      v x * v x + 2 * v x * (x i * euclideanCoordDeriv i v x) := fun i => deriv1 hv i x

  simp only [h, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, ← Finset.mul_sum]
  rfl

theorem deriv2 (hv : Sm v) (i : Fin d) (x : Vec d) :
    euclideanCoordDeriv i (fun y => v y * euclideanCoordDeriv i v y) x =
      euclideanCoordDeriv i v x * euclideanCoordDeriv i v x +
        v x * euclideanCoordSecondDeriv i i v x := by
    rw [coordDeriv_mul hv (hv.coordDeriv i)]
    rfl

/-- Divergence of `v v_i`. -/
theorem div2 (hv : Sm v) (x : Vec d) :
    ∑ i, euclideanCoordDeriv i (fun y => v y * euclideanCoordDeriv i v y) x =
      pQ2 v x + v x * euclideanCoordLaplacian v x := by
  have h : ∀ i, euclideanCoordDeriv i (fun y => v y * euclideanCoordDeriv i v y) x =
      euclideanCoordDeriv i v x * euclideanCoordDeriv i v x +
        v x * euclideanCoordSecondDeriv i i v x := fun i => deriv2 hv i x

  simp only [h, Finset.sum_add_distrib, ← Finset.mul_sum]
  rfl

theorem deriv3 (hv : Sm v) (i : Fin d) (x : Vec d) :
    euclideanCoordDeriv i
      (fun y => euclideanCoordDeriv i v y * euclideanCoordLaplacian v y) x =
      euclideanCoordSecondDeriv i i v x * euclideanCoordLaplacian v x +
        euclideanCoordDeriv i v x * euclideanCoordDeriv i (euclideanCoordLaplacian v) x := by
    rw [coordDeriv_mul (hv.coordDeriv i) (sm_L hv)]
    rfl

/-- Divergence of `v_i Δv`. -/
theorem div3 (hv : Sm v) (x : Vec d) :
    ∑ i, euclideanCoordDeriv i (fun y => euclideanCoordDeriv i v y * euclideanCoordLaplacian v y) x =
      euclideanCoordLaplacian v x * euclideanCoordLaplacian v x + pV3 v x := by
  have h : ∀ i, euclideanCoordDeriv i
      (fun y => euclideanCoordDeriv i v y * euclideanCoordLaplacian v y) x =
      euclideanCoordSecondDeriv i i v x * euclideanCoordLaplacian v x +
        euclideanCoordDeriv i v x * euclideanCoordDeriv i (euclideanCoordLaplacian v) x := fun i => deriv3 hv i x

  simp only [h, Finset.sum_add_distrib, ← Finset.sum_mul]
  rfl

theorem deriv4 (hv : Sm v) (i : Fin d) (x : Vec d) :
    euclideanCoordDeriv i (fun y => y i * pQ2 v y) x =
      pQ2 v x + 2 * ∑ j, x i * (euclideanCoordDeriv j v x * euclideanCoordSecondDeriv j i v x) := by
    rw [coordDeriv_mul (sm_coord i) (sm_pQ2 hv), coordDeriv_coord, coordDeriv_pQ2 hv,
      ← Finset.mul_sum]
    simp only [ite_true, one_mul]
    ring

/-- Divergence of `x_i |∇v|²`. -/
theorem div4 (hv : Sm v) (x : Vec d) :
    ∑ i, euclideanCoordDeriv i (fun y => y i * pQ2 v y) x =
      (d : ℝ) * pQ2 v x + 2 * pR v x := by
  have h : ∀ i, euclideanCoordDeriv i (fun y => y i * pQ2 v y) x =
      pQ2 v x + 2 * ∑ j, x i * (euclideanCoordDeriv j v x * euclideanCoordSecondDeriv j i v x) := fun i => deriv4 hv i x

  have h' : ∑ i, euclideanCoordDeriv i (fun y => y i * pQ2 v y) x =
      ∑ i, (pQ2 v x + 2 * ∑ j, x i * (euclideanCoordDeriv j v x *
        euclideanCoordSecondDeriv j i v x)) := Finset.sum_congr rfl fun i _ => h i
  rw [h', Finset.sum_add_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  congr 2
  unfold pR
  have hc : ∀ i j, euclideanCoordSecondDeriv j i v x = euclideanCoordSecondDeriv i j v x :=
    fun i j => euclideanCoordSecondDeriv_comm hv j i x
  calc ∑ i, ∑ j, x i * (euclideanCoordDeriv j v x * euclideanCoordSecondDeriv j i v x)
      = ∑ j, ∑ i, x i * (euclideanCoordDeriv j v x * euclideanCoordSecondDeriv j i v x) :=
        Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        rw [hc]

theorem deriv5 (hv : Sm v) (i : Fin d) (x : Vec d) :
    euclideanCoordDeriv i (fun y => euclideanCoordDeriv i v y * pP v y) x =
      euclideanCoordSecondDeriv i i v x * pP v x + euclideanCoordDeriv i v x * euclideanCoordDeriv i v x +
        ∑ j, x j * (euclideanCoordDeriv i v x * euclideanCoordSecondDeriv j i v x) := by
    rw [coordDeriv_mul (hv.coordDeriv i) (sm_pP hv), coordDeriv_pP hv, mul_add,
      Finset.mul_sum]
    have : euclideanCoordDeriv i (euclideanCoordDeriv i v) x = euclideanCoordSecondDeriv i i v x := rfl
    rw [this]
    have hs : ∑ j, euclideanCoordDeriv i v x * (x j * euclideanCoordSecondDeriv j i v x) =
        ∑ j, x j * (euclideanCoordDeriv i v x * euclideanCoordSecondDeriv j i v x) :=
      Finset.sum_congr rfl fun j _ => by ring
    rw [hs]
    ring

/-- Divergence of `v_i (x·∇v)`. -/
theorem div5 (hv : Sm v) (x : Vec d) :
    ∑ i, euclideanCoordDeriv i (fun y => euclideanCoordDeriv i v y * pP v y) x =
      euclideanCoordLaplacian v x * pP v x + pQ2 v x + pR v x := by
  have h : ∀ i, euclideanCoordDeriv i (fun y => euclideanCoordDeriv i v y * pP v y) x =
      euclideanCoordSecondDeriv i i v x * pP v x + euclideanCoordDeriv i v x * euclideanCoordDeriv i v x +
        ∑ j, x j * (euclideanCoordDeriv i v x * euclideanCoordSecondDeriv j i v x) := fun i => deriv5 hv i x

  simp only [h, Finset.sum_add_distrib, ← Finset.sum_mul]
  rfl

end

end

end PDE
