module

public import PDEFoundation.Sobolev.Inequalities.CubeShellPoincareGeometry
public import PDEFoundation.Sobolev.Inequalities.CubeShellPoincareGluing
public import PDEFoundation.Sobolev.Inequalities.ConvexPoincareL2

/-!
# Quantitative Poincaré inequality on cube shells

The shell is a connected finite cover of convex slabs when `d ≥ 2`.
Local convex estimates and positive-volume overlaps give a constant
depending only on the dimension.
-/

@[expose] public section

namespace PDE

open MeasureTheory
open scoped ENNReal

/-- A dimension-only constant for the `L²` cube-shell Poincaré inequality. -/
noncomputable def cubeShellPoincareConst (d : ℕ) : ℝ :=
  (2 * d) * (2 + 32 * (8 : ℝ) ^ d) *
    (((2 : ℝ) ^ d * Real.sqrt d * 4) ^ 2)

/-- The displayed cube-shell Poincaré constant is positive in dimension at least two. -/
theorem cubeShellPoincareConst_pos {d : ℕ} (hd : 2 ≤ d) :
    0 < cubeShellPoincareConst d := by
  unfold cubeShellPoincareConst
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 hdpos
  positivity

private theorem integrableOn_sq_sub_of_h1_restrict
    {d : ℕ} {U V : Set (Vec d)} (u : H1Function U)
    (hV : IsOpenBoundedConvexDomain V) (hVU : V ⊆ U) (c : ℝ) :
    IntegrableOn (fun x => (u x - c) ^ 2) V := by
  let v : H1Function V :=
    (u.toW1pFunction.restrict hV.isOpen hVU).toH1Function
  let w : H1Function V := v.subConst hV c
  have hw := integrableOn_mul_of_memL2On w.memL2 w.memL2
  simpa only [w, H1Function.subConst_apply, v,
    W1pFunction.toH1Function_apply, H1Function.toW1pFunction_apply,
    pow_two] using! hw

private theorem setIntegral_grad_sq_mono_of_subset
    {d : ℕ} {U V W : Set (Vec d)} (u : H1Function U)
    (hVW : V ⊆ W) (hWU : W ⊆ U) :
    ∫ x in V, vecNormSq (u.grad x) ≤
      ∫ x in W, vecNormSq (u.grad x) := by
  have hIntU : IntegrableOn (fun x => vecNormSq (u.grad x)) U :=
    integrableOn_vecNormSq_of_memVectorL2On u.gradMemL2
  apply setIntegral_mono_set (hIntU.mono_set hWU)
  · exact Filter.Eventually.of_forall fun x => vecNormSq_nonneg (u.grad x)
  · exact Filter.Eventually.of_forall hVW

private theorem cubeShellSlab_path
    {d : ℕ} (hd : 2 ≤ d) (x₀ : Vec d) {r : ℝ} (hr : 0 < r)
    (i : Fin d × Bool) :
    i = (⟨0, by omega⟩, true) ∨
      (r / 2) ^ d ≤ (volume
        (cubeShellSlab x₀ r ⟨0, by omega⟩ true ∩
          cubeShellSlab x₀ r i.1 i.2)).toReal ∨
      ∃ j : Fin d × Bool,
        (r / 2) ^ d ≤ (volume
          (cubeShellSlab x₀ r ⟨0, by omega⟩ true ∩
            cubeShellSlab x₀ r j.1 j.2)).toReal ∧
        (r / 2) ^ d ≤ (volume
          (cubeShellSlab x₀ r j.1 j.2 ∩
            cubeShellSlab x₀ r i.1 i.2)).toReal := by
  let root : Fin d := ⟨0, by omega⟩
  let bridge : Fin d := ⟨1, by omega⟩
  by_cases hir : i.1 = root
  · by_cases his : i.2 = true
    · left
      exact Prod.ext hir his
    · right; right
      refine ⟨(bridge, true), ?_, ?_⟩
      · exact cubeShellSlab_inter_volume_lower x₀ hr root bridge
          (by simp [root, bridge]) true true
      · exact cubeShellSlab_inter_volume_lower x₀ hr bridge i.1
          (by
            intro h
            have hbr : bridge ≠ root := by simp [root, bridge]
            exact hbr (h.trans hir))
          true i.2
  · right; left
    exact cubeShellSlab_inter_volume_lower x₀ hr root i.1
      (Ne.symm hir) true i.2

/-- Cube-shell Poincaré with the mean of the positive first-coordinate slab
as center. The constant depends only on `d`; `r²` carries the exact scale. -/
theorem poincare_sq_on_cubeShell_rootAverage
    {d : ℕ} (hd : 2 ≤ d) {U : Set (Vec d)}
    (u : H1Function U) (x₀ : Vec d) {r : ℝ}
    (hr : 0 < r) (hShellU : cubeShell x₀ r ⊆ U) :
    ∫ x in cubeShell x₀ r,
      (u x - integralAverage
        (cubeShellSlab x₀ r ⟨0, by omega⟩ true) u) ^ 2 ≤
      cubeShellPoincareConst d * r ^ 2 *
        ∫ x in cubeShell x₀ r, vecNormSq (u.grad x) := by
  let t : Finset (Fin d × Bool) := Finset.univ
  let s : Fin d × Bool → Set (Vec d) :=
    fun i => cubeShellSlab x₀ r i.1 i.2
  let root : Fin d × Bool := (⟨0, by omega⟩, true)
  let c : Fin d × Bool → ℝ := fun i => integralAverage (s i) u
  let E : ℝ := ∫ x in cubeShell x₀ r, vecNormSq (u.grad x)
  let A : ℝ := ((2 : ℝ) ^ d * Real.sqrt d * 4) ^ 2
  let V : ℝ := A * r ^ 2 * E
  have hSlabU (i : Fin d × Bool) : s i ⊆ U := by
    exact (cubeShellSlab_subset x₀ r i.1 i.2).trans hShellU
  have hCover : cubeShell x₀ r ⊆ ⋃ i ∈ t, s i := by
    intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (cubeShell_subset_iUnion_slabs x₀ r hx)
    obtain ⟨positive, hp⟩ := Set.mem_iUnion.mp hi
    exact Set.mem_iUnion.mpr ⟨(i, positive), Set.mem_iUnion.mpr ⟨Finset.mem_univ _, hp⟩⟩
  have hMeas (i : Fin d × Bool) : MeasurableSet (s i) :=
    (cubeShellSlab_domain x₀ r i.1 i.2).isOpen.measurableSet
  have hFinite (i : Fin d × Bool) : volume (s i) ≠ ∞ :=
    volume_axisBox_ne_top _ _
  have hInt (i : Fin d × Bool) (b : ℝ) :
      IntegrableOn (fun x => (u x - b) ^ 2) (s i) :=
    integrableOn_sq_sub_of_h1_restrict u
      (cubeShellSlab_domain x₀ r i.1 i.2) (hSlabU i) b
  have hVolume (i : Fin d × Bool) :
      (volume (s i)).toReal ≤ (4 * r) ^ d :=
    cubeShellSlab_volume_le x₀ hr i.1 i.2
  have hD : 0 ≤ Real.sqrt d * (4 * r) := by positivity
  have hCoeff :
      (((2 : ℝ) ^ d * (Real.sqrt d * (4 * r))) ^ 2) = A * r ^ 2 := by
    dsimp [A]
    ring
  have hVariance (i : Fin d × Bool) :
      (∫ x in s i, (u x - c i) ^ 2) ≤ V := by
    have hP := centeredPoincare_sq_on_boundedConvexSubdomain u
      (cubeShellSlab_domain x₀ r i.1 i.2) (hSlabU i)
      (cubeShellSlab_diameter x₀ hr.le i.1 i.2) hD
      (cubeShellSlab_nonempty x₀ hr i.1 i.2)
    have hEnergy : (∫ x in s i, vecNormSq (u.grad x)) ≤ E :=
      setIntegral_grad_sq_mono_of_subset u
        (cubeShellSlab_subset x₀ r i.1 i.2) hShellU
    calc
      (∫ x in s i, (u x - c i) ^ 2) ≤
          ((2 : ℝ) ^ d * (Real.sqrt d * (4 * r))) ^ 2 *
            ∫ x in s i, vecNormSq (u.grad x) := by
        simpa only [s, c] using hP
      _ = A * r ^ 2 * ∫ x in s i, vecNormSq (u.grad x) := by rw [hCoeff]
      _ ≤ V := by
        dsimp [V]
        gcongr
  have hPaths (i : Fin d × Bool) :
      i = root ∨ (r / 2) ^ d ≤ (volume (s root ∩ s i)).toReal ∨
        ∃ j ∈ t,
          (r / 2) ^ d ≤ (volume (s root ∩ s j)).toReal ∧
          (r / 2) ^ d ≤ (volume (s j ∩ s i)).toReal := by
    rcases cubeShellSlab_path hd x₀ hr i with h | h | ⟨j, h1, h2⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨j, Finset.mem_univ _, h1, h2⟩)
  have hm : 0 < (r / 2) ^ d := pow_pos (by positivity) _
  have hGlue := setIntegral_sq_sub_le_root_center_finset
    (μ := volume) t root (S := cubeShell x₀ r) (s := s)
    (u := u) (c := c) (V := V) (M := (4 * r) ^ d)
    (m := (r / 2) ^ d)
    (Finset.mem_univ _) hCover
    (fun i _ => hMeas i) (fun i _ => hFinite i)
    (fun i _ => hInt i (c i)) (fun i _ => hInt i (c root))
    hm (fun i _ => hVolume i) (fun i _ => hVariance i)
    (fun i _ => hPaths i)
  have hRatio : (4 * r) ^ d / (r / 2) ^ d = (8 : ℝ) ^ d := by
    rw [← div_pow]
    congr 1
    field_simp [ne_of_gt hr]
    ring
  have hCard : (t.card : ℝ) = 2 * d := by
    simp [t, Fintype.card_prod, Fintype.card_fin]
    ring
  have hAlgebra :
      (t.card : ℝ) * (2 * V + 32 * (4 * r) ^ d * V / (r / 2) ^ d) =
        cubeShellPoincareConst d * r ^ 2 * E := by
    rw [hCard]
    dsimp [V, A, cubeShellPoincareConst]
    calc
      2 * (d : ℝ) *
          (2 * (((2 : ℝ) ^ d * Real.sqrt d * 4) ^ 2 * r ^ 2 * E) +
            32 * (4 * r) ^ d *
              (((2 : ℝ) ^ d * Real.sqrt d * 4) ^ 2 * r ^ 2 * E) /
                (r / 2) ^ d) =
          2 * (d : ℝ) *
            (2 + 32 * ((4 * r) ^ d / (r / 2) ^ d)) *
              ((2 : ℝ) ^ d * Real.sqrt d * 4) ^ 2 * r ^ 2 * E := by ring
      _ = _ := by rw [hRatio]
  simpa only [root, s, c, E] using hGlue.trans_eq hAlgebra

end PDE
