module

public import PDEFoundation.PDE.WeakInequalities
public import PDEFoundation.Sobolev.H1.Algebra
public import PDEFoundation.Sobolev.H1.RepresentativeCongruence
public import PDEFoundation.Sobolev.H1.Truncation
public import PDEFoundation.Sobolev.Inequalities.ZeroBoundaryPoincare

/-!
# Weak maximum and minimum principles

This module proves the energy core of the weak maximum principle on an axis
box.  The public boundary condition is the representative-level `MemH10`
membership of the relevant positive truncation.  Internally, the resulting
`H10Function` witness has the canonical truncation gradient almost everywhere
by weak-derivative uniqueness; no literal equality between independently
chosen gradient representatives is required.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open Filter MeasureTheory

private theorem setIntegral_vecNormSq_eq_zero_of_energy_nonpos
    {d : ℕ} {lam Lam : ℝ} {U : Set (Vec d)}
    {a : CoeffField d} (hEll : IsEllipticFieldOn lam Lam U a)
    (hlam : 0 < lam) (w : H1Function U)
    (henergy :
      ∫ x in U, vecDot (w.grad x) (matVecMul (a x) (w.grad x)) ≤ 0) :
    ∫ x in U, vecNormSq (w.grad x) = 0 := by
  have hcoercive :=
    setIntegral_vecNormSq_le_coefficientEnergy_div hEll
      w.gradMemL2 (measurableSet_of_isEllipticFieldOn hEll)
      Set.Subset.rfl hlam
  have hnonpos :
      ∫ x in U, vecNormSq (w.grad x) ≤ 0 := by
    calc
      ∫ x in U, vecNormSq (w.grad x) ≤
          (∫ x in U,
            vecDot (w.grad x) (matVecMul (a x) (w.grad x))) / lam :=
        hcoercive
      _ ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg henergy hlam.le
  exact
    le_antisymm hnonpos
      (integral_nonneg fun _ => vecNormSq_nonneg _)

private theorem h10_ae_eq_zero_of_setIntegral_vecNormSq_eq_zero_axisBox
    {d : ℕ} {a b : Vec d} (hab : ∀ j, a j < b j)
    (i : Fin d) (w : H10Function (axisBox a b))
    (hgrad :
      ∫ x in axisBox a b,
        vecNormSq (w.toH1Function.grad x) = 0) :
    ∀ᵐ x ∂volumeOn (axisBox a b), w.toH1Function x = 0 := by
  let U : Set (Vec d) := axisBox a b
  have hcoordInt :
      IntegrableOn
        (fun x => (w.toH1Function.grad x i) ^ 2) U :=
    by
      simpa only [pow_two] using
        integrableOn_mul_of_memL2On
          (w.toH1Function.gradMemL2 i)
          (w.toH1Function.gradMemL2 i)
  have hvecInt :
      IntegrableOn
        (fun x => vecNormSq (w.toH1Function.grad x)) U :=
    integrableOn_vecNormSq_of_memVectorL2On
      w.toH1Function.gradMemL2
  have hcoordLe :
      (∫ x in U, (w.toH1Function.grad x i) ^ 2) ≤
        ∫ x in U, vecNormSq (w.toH1Function.grad x) := by
    exact
      setIntegral_mono_on hcoordInt hvecInt
        (isOpen_axisBox a b).measurableSet
        (fun x _ => sq_apply_le_vecNormSq
          (w.toH1Function.grad x) i)
  have hcoordZero :
      ∫ x in U, (w.toH1Function.grad x i) ^ 2 = 0 := by
    apply le_antisymm
    · simpa only [U, hgrad] using hcoordLe
    · exact integral_nonneg fun _ => sq_nonneg _
  have hvalueNonpos :
      ∫ x in U, w.toH1Function x ^ 2 ≤ 0 := by
    calc
      ∫ x in U, w.toH1Function x ^ 2 ≤
          (b i - a i) ^ 2 *
            ∫ x in U, (w.toH1Function.grad x i) ^ 2 := by
        simpa only [U] using
          h10_setIntegral_sq_le_side_sq_setIntegral_sq_grad_coord_on_axisBox
            w hab i
      _ = 0 := by rw [hcoordZero, mul_zero]
  have hvalueZero :
      ∫ x in U, w.toH1Function x ^ 2 = 0 :=
    le_antisymm hvalueNonpos
      (integral_nonneg fun _ => sq_nonneg _)
  have hvalueIntegrable :
      Integrable (fun x => w.toH1Function x ^ 2)
        (volumeOn U) :=
    by
      simpa only [pow_two] using!
        integrableOn_mul_of_memL2On
          w.toH1Function.memL2 w.toH1Function.memL2
  have hsqZero :
      ∀ᵐ x ∂volumeOn U, w.toH1Function x ^ 2 = 0 :=
    (integral_eq_zero_iff_of_nonneg
      (fun x => sq_nonneg (w.toH1Function x))
      hvalueIntegrable).mp hvalueZero
  filter_upwards [hsqZero] with x hx
  exact sq_eq_zero_iff.mp hx

/-- Weak maximum principle on an axis box.

The supplied `H10Function` must be the exact positive truncation `(u-k)₊`.
Its selected weak gradient need only agree almost everywhere with the
canonical truncation gradient, as weak gradients are unique only a.e. -/
theorem weakMaximumOn_axisBox_of_positivePartSubConst_toH10
    {d : ℕ} {lam Lam k : ℝ} {a b : Vec d}
    {coeff : CoeffField d} {u : H1Function (axisBox a b)}
    (hab : ∀ j, a j < b j) (i : Fin d)
    (hEll : IsEllipticFieldOn lam Lam (axisBox a b) coeff)
    (hlam : 0 < lam)
    (hsub :
      IsWeakDivergenceFormH10SubharmonicOn
        coeff (axisBox a b) u)
    (w : H10Function (axisBox a b))
    (hwvalue :
      w.toH1Function.toFun =
        fun x => max (u.toFun x - k) 0)
    (hwgrad :
      ∀ i : Fin d,
        (fun x => w.toH1Function.grad x i) =ᵐ[volumeOn (axisBox a b)]
          fun x => ({y | k < u.toFun y}.indicator u.grad x) i) :
    ∀ᵐ x ∂volumeOn (axisBox a b), u.toFun x ≤ k := by
  have hwNonnegative : w.AENonnegative := by
    filter_upwards with x
    rw [hwvalue]
    exact le_max_right _ _
  rcases hsub w hwNonnegative with ⟨_, hcross⟩
  simp only [Pi.zero_apply, zero_mul, integral_zero] at hcross
  have henergyEq :
      (∫ x in axisBox a b,
        vecDot (w.toH1Function.grad x)
          (matVecMul (coeff x) (w.toH1Function.grad x))) =
      ∫ x in axisBox a b,
        vecDot (matVecMul (coeff x) (u.grad x))
          (w.toH1Function.grad x) := by
    apply integral_congr_ae
    filter_upwards [Filter.eventually_all.2 hwgrad] with x hx
    have hgradx : w.toH1Function.grad x =
        {y | k < u.toFun y}.indicator u.grad x := by
      funext j
      exact hx j
    rw [hgradx]
    change
      vecDot ({y | k < u.toFun y}.indicator u.grad x)
          (matVecMul (coeff x)
            ({y | k < u.toFun y}.indicator u.grad x)) =
        vecDot (matVecMul (coeff x) (u.grad x))
          ({y | k < u.toFun y}.indicator u.grad x)
    by_cases hx : k < u.toFun x
    · have hxmem : x ∈ {y : Vec d | k < u.toFun y} := hx
      rw [Set.indicator_of_mem hxmem]
      exact vecDot_comm _ _
    · have hxnot : x ∉ {y : Vec d | k < u.toFun y} := hx
      rw [Set.indicator_of_notMem hxnot]
      simp [matVecMul, vecDot]
  have henergyNonpos :
      ∫ x in axisBox a b,
        vecDot (w.toH1Function.grad x)
          (matVecMul (coeff x) (w.toH1Function.grad x)) ≤ 0 := by
    rw [henergyEq]
    simpa [vecDot] using hcross
  have hgradZero :=
    setIntegral_vecNormSq_eq_zero_of_energy_nonpos
      hEll hlam w.toH1Function henergyNonpos
  have hwZero :=
    h10_ae_eq_zero_of_setIntegral_vecNormSq_eq_zero_axisBox
      hab i w hgradZero
  filter_upwards [hwZero] with x hx
  have hmaxZero : max (u.toFun x - k) 0 = 0 := by
    calc
      max (u.toFun x - k) 0 = w.toH1Function x :=
        (congrFun hwvalue x).symm
      _ = 0 := hx
  exact
    sub_nonpos.mp
      (by simpa [hmaxZero] using
        le_max_left (u.toFun x - k) 0)

/-- Weak maximum principle on an axis box from the representative-level
`H¹₀` membership of the exact positive truncation. -/
theorem weakMaximumOn_axisBox_of_positivePartSubConst_memH10
    {d : ℕ} {lam Lam k : ℝ} {a b : Vec d}
    {coeff : CoeffField d} {u : H1Function (axisBox a b)}
    (hab : ∀ j, a j < b j) (i : Fin d)
    (hEll : IsEllipticFieldOn lam Lam (axisBox a b) coeff)
    (hlam : 0 < lam)
    (hsub :
      IsWeakDivergenceFormH10SubharmonicOn
        coeff (axisBox a b) u)
    (hzero : MemH10 (axisBox a b)
      (u.positivePartSubConst
        (isOpenBoundedConvexDomain_axisBox a b) k).toFun) :
    ∀ᵐ x ∂volumeOn (axisBox a b), u.toFun x ≤ k := by
  let v : H1Function (axisBox a b) :=
    u.positivePartSubConst (isOpenBoundedConvexDomain_axisBox a b) k
  rcases hzero with ⟨w, hwvalue⟩
  have hwgrad : ∀ j : Fin d,
      (fun x => w.toH1Function.grad x j) =ᵐ[volumeOn (axisBox a b)]
        fun x => ({y | k < u.toFun y}.indicator u.grad x) j := by
    intro j
    have hgrad := H1Function.grad_coord_ae_eq_of_toFun_eq
      (isOpen_axisBox a b) w.toH1Function v (by simpa only [v] using hwvalue) j
    simpa only [v, H1Function.positivePartSubConst_grad] using hgrad
  exact weakMaximumOn_axisBox_of_positivePartSubConst_toH10
    hab i hEll hlam hsub w (by
      simpa only [v, H1Function.positivePartSubConst_toFun] using hwvalue) hwgrad

/-- Weak minimum principle on an axis box.

The supplied `H10Function` is the exact positive truncation `(k-u)₊`.
Its selected weak gradient need only agree almost everywhere with the
displayed negative-indicator representative. -/
theorem weakMinimumOn_axisBox_of_constSub_positivePart_toH10
    {d : ℕ} {lam Lam k : ℝ} {a b : Vec d}
    {coeff : CoeffField d} {u : H1Function (axisBox a b)}
    (hab : ∀ j, a j < b j) (i : Fin d)
    (hEll : IsEllipticFieldOn lam Lam (axisBox a b) coeff)
    (hlam : 0 < lam)
    (hsuper :
      IsWeakDivergenceFormH10SuperharmonicOn
        coeff (axisBox a b) u)
    (w : H10Function (axisBox a b))
    (hwvalue :
      w.toH1Function.toFun =
        fun x => max (k - u.toFun x) 0)
    (hwgrad :
      ∀ i : Fin d,
        (fun x => w.toH1Function.grad x i) =ᵐ[volumeOn (axisBox a b)]
          fun x => (-({y | u.toFun y < k}.indicator u.grad x)) i) :
    ∀ᵐ x ∂volumeOn (axisBox a b), k ≤ u.toFun x := by
  have hwNonnegative : w.AENonnegative := by
    filter_upwards with x
    rw [hwvalue]
    exact le_max_right _ _
  rcases hsuper w hwNonnegative with ⟨_, hcross⟩
  simp only [Pi.zero_apply, zero_mul, integral_zero] at hcross
  have hcrossNonneg :
      0 ≤ ∫ x in axisBox a b,
        vecDot (matVecMul (coeff x) (u.grad x))
          (w.toH1Function.grad x) := by
    simpa [vecDot] using hcross
  have henergyEq :
      (∫ x in axisBox a b,
        vecDot (w.toH1Function.grad x)
          (matVecMul (coeff x) (w.toH1Function.grad x))) =
      -(∫ x in axisBox a b,
        vecDot (matVecMul (coeff x) (u.grad x))
          (w.toH1Function.grad x)) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [Filter.eventually_all.2 hwgrad] with x hx
    have hgradx : w.toH1Function.grad x =
        -({y | u.toFun y < k}.indicator u.grad x) := by
      funext j
      exact hx j
    rw [hgradx]
    change
      vecDot (-({y | u.toFun y < k}.indicator u.grad x))
          (matVecMul (coeff x)
            (-({y | u.toFun y < k}.indicator u.grad x))) =
        -vecDot (matVecMul (coeff x) (u.grad x))
          (-({y | u.toFun y < k}.indicator u.grad x))
    by_cases hx : u.toFun x < k
    · have hxmem : x ∈ {y : Vec d | u.toFun y < k} := hx
      rw [Set.indicator_of_mem hxmem]
      have hleft :
          matVecMul (coeff x) (-u.grad x) =
            -(matVecMul (coeff x) (u.grad x)) := by
        change (coeff x).mulVec (-u.grad x) =
          -((coeff x).mulVec (u.grad x))
        exact Matrix.mulVec_neg (u.grad x) (coeff x)
      rw [hleft]
      simpa [vecDot] using
        vecDot_comm (u.grad x)
          (matVecMul (coeff x) (u.grad x))
    · have hxnot : x ∉ {y : Vec d | u.toFun y < k} := hx
      rw [Set.indicator_of_notMem hxnot]
      simp [matVecMul, vecDot]
  have henergyNonpos :
      ∫ x in axisBox a b,
        vecDot (w.toH1Function.grad x)
          (matVecMul (coeff x) (w.toH1Function.grad x)) ≤ 0 := by
    rw [henergyEq]
    exact neg_nonpos.mpr hcrossNonneg
  have hgradZero :=
    setIntegral_vecNormSq_eq_zero_of_energy_nonpos
      hEll hlam w.toH1Function henergyNonpos
  have hwZero :=
    h10_ae_eq_zero_of_setIntegral_vecNormSq_eq_zero_axisBox
      hab i w hgradZero
  filter_upwards [hwZero] with x hx
  have hmaxZero : max (k - u.toFun x) 0 = 0 := by
    calc
      max (k - u.toFun x) 0 = w.toH1Function x :=
        (congrFun hwvalue x).symm
      _ = 0 := hx
  exact
    sub_nonpos.mp
      (by simpa [hmaxZero] using
        le_max_left (k - u.toFun x) 0)

/-- Weak minimum principle on an axis box from the representative-level
`H¹₀` membership of the exact negative truncation. -/
theorem weakMinimumOn_axisBox_of_constSub_positivePart_memH10
    {d : ℕ} {lam Lam k : ℝ} {a b : Vec d}
    {coeff : CoeffField d} {u : H1Function (axisBox a b)}
    (hab : ∀ j, a j < b j) (i : Fin d)
    (hEll : IsEllipticFieldOn lam Lam (axisBox a b) coeff)
    (hlam : 0 < lam)
    (hsuper :
      IsWeakDivergenceFormH10SuperharmonicOn
        coeff (axisBox a b) u)
    (hzero : MemH10 (axisBox a b)
      (fun x => max (k - u.toFun x) 0)) :
    ∀ᵐ x ∂volumeOn (axisBox a b), k ≤ u.toFun x := by
  let hU : IsOpenBoundedConvexDomain (axisBox a b) :=
    isOpenBoundedConvexDomain_axisBox a b
  let v : H1Function (axisBox a b) :=
    (-u).positivePartSubConst hU (-k)
  have hvvalue : v.toFun = fun x => max (k - u.toFun x) 0 := by
    dsimp [v]
    funext x
    congr 1
    ring
  have hvgrad : v.grad =
      fun x => -({y | u.toFun y < k}.indicator u.grad x) := by
    dsimp [v]
    funext x
    by_cases hx : u.toFun x < k
    · have hxmem : x ∈ {y : Vec d | u.toFun y < k} := hx
      have hxmem' : x ∈ {y : Vec d | -k < -u.toFun y} := by
        change -k < -u.toFun x
        linarith
      rw [Set.indicator_of_mem hxmem, Set.indicator_of_mem hxmem']
    · have hxnot : x ∉ {y : Vec d | u.toFun y < k} := hx
      have hxnot' : x ∉ {y : Vec d | -k < -u.toFun y} := by
        intro h
        apply hx
        change -k < -u.toFun x at h
        linarith
      rw [Set.indicator_of_notMem hxnot, Set.indicator_of_notMem hxnot']
      simp only [neg_zero]
  rcases hzero with ⟨w, hwvalue⟩
  have hwvalue_v : w.toH1Function.toFun = v.toFun := hwvalue.trans hvvalue.symm
  have hwgrad : ∀ j : Fin d,
      (fun x => w.toH1Function.grad x j) =ᵐ[volumeOn (axisBox a b)]
        fun x => (-({y | u.toFun y < k}.indicator u.grad x)) j := by
    intro j
    have hgrad := H1Function.grad_coord_ae_eq_of_toFun_eq
      (isOpen_axisBox a b) w.toH1Function v hwvalue_v j
    simpa only [hvgrad] using hgrad
  exact weakMinimumOn_axisBox_of_constSub_positivePart_toH10
    hab i hEll hlam hsuper w hwvalue hwgrad

end PDE
