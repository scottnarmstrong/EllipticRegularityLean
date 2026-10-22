module

public import PDEFoundation.Geometry.SquareShell
public import PDEFoundation.Measure.SquareShellVolume
public import PDEFoundation.Measure.L2TreeGluing
public import PDEFoundation.Sobolev.Inequalities.ConvexPoincareL2

/-!
# Quantitative `L²` Poincaré estimate on a dyadic square shell

The nonconvex shell is covered by four convex rectangles. Local centered
Poincaré estimates are glued through three positive-volume corner overlaps,
with every geometric constant retained explicitly.
-/

@[expose] public section

namespace PDE

open MeasureTheory

/-- An `H¹` representative is square-integrable after subtracting any
constant on a bounded open convex subdomain. -/
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
    ∫ x in V, vecNormSq (u.grad x) ≤ ∫ x in W, vecNormSq (u.grad x) := by
  have hIntU : IntegrableOn (fun x => vecNormSq (u.grad x)) U :=
    integrableOn_vecNormSq_of_memVectorL2On u.gradMemL2
  apply setIntegral_mono_set (hIntU.mono_set hWU)
  · exact Filter.Eventually.of_forall fun x => vecNormSq_nonneg (u.grad x)
  · exact Filter.Eventually.of_forall hVW

/-- A quantitative square-shell Poincaré estimate obtained by gluing the
four convex strips through their three corner overlaps.

The centering constant is the mean on the top strip. The explicit constant
is `82 * 4 * 512`: `82` is the overlap-gluing constant, `4` bounds the four
strip energies by the shell energy, and `512` is the dimension-two local
convex Poincaré constant for diameter `sqrt 2 * (4 * r)`. -/
theorem poincare_sq_on_dyadicSquareShell_topAverage
    {U : Set (Vec 2)} (u : H1Function U) (x₀ : Vec 2) {r : ℝ}
    (hr : 0 < r) (hShellU : dyadicSquareShell x₀ r ⊆ U) :
    ∫ x in dyadicSquareShell x₀ r,
        (u x - integralAverage (dyadicSquareShellTop x₀ r) u) ^ 2 ≤
      167936 * r ^ 2 *
        ∫ x in dyadicSquareShell x₀ r, vecNormSq (u.grad x) := by
  let T := dyadicSquareShellTop x₀ r
  let L := dyadicSquareShellLeft x₀ r
  let B := dyadicSquareShellBottom x₀ r
  let R := dyadicSquareShellRight x₀ r
  let S := dyadicSquareShell x₀ r
  let cT := integralAverage T u
  let cL := integralAverage L u
  let cB := integralAverage B u
  let cR := integralAverage R u
  let E := ∫ x in S, vecNormSq (u.grad x)
  have hTU : T ⊆ U := by
    simpa only [T, S] using (dyadicSquareShellTop_subset x₀ r).trans hShellU
  have hLU : L ⊆ U := by
    simpa only [L, S] using (dyadicSquareShellLeft_subset x₀ r).trans hShellU
  have hBU : B ⊆ U := by
    simpa only [B, S] using (dyadicSquareShellBottom_subset x₀ r).trans hShellU
  have hRU : R ⊆ U := by
    simpa only [R, S] using (dyadicSquareShellRight_subset x₀ r).trans hShellU
  have hcover : S ⊆ (T ∪ L) ∪ (B ∪ R) := by
    rw [show S = dyadicSquareShell x₀ r by rfl,
      dyadicSquareShell_eq_strips]
    rintro x ((ht | hb) | (hl | hr'))
    · exact Or.inl (Or.inl ht)
    · exact Or.inr (Or.inl hb)
    · exact Or.inl (Or.inr hl)
    · exact Or.inr (Or.inr hr')
  have hTdom : IsOpenBoundedConvexDomain T := by
    simpa only [T] using dyadicSquareShellTop_domain x₀ r
  have hLdom : IsOpenBoundedConvexDomain L := by
    simpa only [L] using dyadicSquareShellLeft_domain x₀ r
  have hBdom : IsOpenBoundedConvexDomain B := by
    simpa only [B] using dyadicSquareShellBottom_domain x₀ r
  have hRdom : IsOpenBoundedConvexDomain R := by
    simpa only [R] using dyadicSquareShellRight_domain x₀ r
  have hIntT : IntegrableOn (fun x => (u x - cT) ^ 2) T :=
    integrableOn_sq_sub_of_h1_restrict u hTdom hTU cT
  have hIntL : IntegrableOn (fun x => (u x - cL) ^ 2) L :=
    integrableOn_sq_sub_of_h1_restrict u hLdom hLU cL
  have hIntB : IntegrableOn (fun x => (u x - cB) ^ 2) B :=
    integrableOn_sq_sub_of_h1_restrict u hBdom hBU cB
  have hIntR : IntegrableOn (fun x => (u x - cR) ^ 2) R :=
    integrableOn_sq_sub_of_h1_restrict u hRdom hRU cR
  have hIntLRoot : IntegrableOn (fun x => (u x - cT) ^ 2) L :=
    integrableOn_sq_sub_of_h1_restrict u hLdom hLU cT
  have hIntBRoot : IntegrableOn (fun x => (u x - cT) ^ 2) B :=
    integrableOn_sq_sub_of_h1_restrict u hBdom hBU cT
  have hIntRRoot : IntegrableOn (fun x => (u x - cT) ^ 2) R :=
    integrableOn_sq_sub_of_h1_restrict u hRdom hRU cT
  have hfiniteT : volume T ≠ ⊤ := by
    simpa only [T, dyadicSquareShellTop] using
      volume_axisBox_ne_top
        ![x₀ 0 - 2 * r, x₀ 1 + r]
        ![x₀ 0 + 2 * r, x₀ 1 + 2 * r]
  have hfiniteL : volume L ≠ ⊤ := by
    simpa only [L, dyadicSquareShellLeft] using
      volume_axisBox_ne_top
        ![x₀ 0 - 2 * r, x₀ 1 - 2 * r]
        ![x₀ 0 - r, x₀ 1 + 2 * r]
  have hfiniteB : volume B ≠ ⊤ := by
    simpa only [B, dyadicSquareShellBottom] using
      volume_axisBox_ne_top
        ![x₀ 0 - 2 * r, x₀ 1 - 2 * r]
        ![x₀ 0 + 2 * r, x₀ 1 - r]
  have hfiniteR : volume R ≠ ⊤ := by
    simpa only [R, dyadicSquareShellRight] using
      volume_axisBox_ne_top
        ![x₀ 0 + r, x₀ 1 - 2 * r]
        ![x₀ 0 + 2 * r, x₀ 1 + 2 * r]
  have hTLmeas : MeasurableSet (T ∩ L) := hTdom.isOpen.measurableSet.inter hLdom.isOpen.measurableSet
  have hLBmeas : MeasurableSet (L ∩ B) := hLdom.isOpen.measurableSet.inter hBdom.isOpen.measurableSet
  have hTRmeas : MeasurableSet (T ∩ R) := hTdom.isOpen.measurableSet.inter hRdom.isOpen.measurableSet
  have hTLfinite : volume (T ∩ L) ≠ ⊤ :=
    measure_ne_top_of_subset Set.inter_subset_left hfiniteT
  have hLBfinite : volume (L ∩ B) ≠ ⊤ :=
    measure_ne_top_of_subset Set.inter_subset_left hfiniteL
  have hTRfinite : volume (T ∩ R) ≠ ⊤ :=
    measure_ne_top_of_subset Set.inter_subset_left hfiniteT
  have hm : 0 < r ^ 2 := sq_pos_of_pos hr
  have hTLvol : r ^ 2 ≤ volume.real (T ∩ L) := by
    simpa only [T, L] using sq_le_volumeReal_dyadicSquareShellTop_inter_left x₀ hr.le
  have hLBvol : r ^ 2 ≤ volume.real (L ∩ B) := by
    simpa only [L, B] using sq_le_volumeReal_dyadicSquareShellLeft_inter_bottom x₀ hr.le
  have hTRvol : r ^ 2 ≤ volume.real (T ∩ R) := by
    simpa only [T, R] using sq_le_volumeReal_dyadicSquareShellTop_inter_right x₀ hr.le
  have hTvol : volume.real T ≤ 4 * r ^ 2 := by
    simpa only [T, measureReal_def] using
      le_of_eq (volume_dyadicSquareShellTop_toReal x₀ hr.le)
  have hLvol : volume.real L ≤ 4 * r ^ 2 := by
    simpa only [L, measureReal_def] using
      le_of_eq (volume_dyadicSquareShellLeft_toReal x₀ hr.le)
  have hBvol : volume.real B ≤ 4 * r ^ 2 := by
    simpa only [B, measureReal_def] using
      le_of_eq (volume_dyadicSquareShellBottom_toReal x₀ hr.le)
  have hRvol : volume.real R ≤ 4 * r ^ 2 := by
    simpa only [R, measureReal_def] using
      le_of_eq (volume_dyadicSquareShellRight_toReal x₀ hr.le)
  have hTenergy : ∫ x in T, vecNormSq (u.grad x) ≤ E :=
    setIntegral_grad_sq_mono_of_subset u
      (by simpa only [T, S] using dyadicSquareShellTop_subset x₀ r)
      hShellU
  have hLenergy : ∫ x in L, vecNormSq (u.grad x) ≤ E :=
    setIntegral_grad_sq_mono_of_subset u
      (by simpa only [L, S] using dyadicSquareShellLeft_subset x₀ r)
      hShellU
  have hBenergy : ∫ x in B, vecNormSq (u.grad x) ≤ E :=
    setIntegral_grad_sq_mono_of_subset u
      (by simpa only [B, S] using dyadicSquareShellBottom_subset x₀ r)
      hShellU
  have hRenergy : ∫ x in R, vecNormSq (u.grad x) ≤ E :=
    setIntegral_grad_sq_mono_of_subset u
      (by simpa only [R, S] using dyadicSquareShellRight_subset x₀ r)
      hShellU
  have hDnonneg : 0 ≤ Real.sqrt 2 * (4 * r) :=
    mul_nonneg (Real.sqrt_nonneg _) (by positivity)
  have hCoeff : ((2 : ℝ) ^ 2 * (Real.sqrt 2 * (4 * r))) ^ 2 =
      512 * r ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  have hTPoincareRaw := centeredPoincare_sq_on_boundedConvexSubdomain u
    hTdom hTU (dyadicSquareShellTop_diameter x₀ hr) hDnonneg
    (dyadicSquareShellTop_nonempty x₀ hr)
  have hTPoincare : ∫ x in T, (u x - cT) ^ 2 ≤ 512 * r ^ 2 * E := by
    calc
      ∫ x in T, (u x - cT) ^ 2 ≤
          ((2 : ℝ) ^ 2 * (Real.sqrt 2 * (4 * r))) ^ 2 *
            ∫ x in T, vecNormSq (u.grad x) := by
        simpa only [T, cT] using hTPoincareRaw
      _ = 512 * r ^ 2 * ∫ x in T, vecNormSq (u.grad x) := by rw [hCoeff]
      _ ≤ 512 * r ^ 2 * E := by
        gcongr
  have hLPoincareRaw := centeredPoincare_sq_on_boundedConvexSubdomain u
    hLdom hLU (dyadicSquareShellLeft_diameter x₀ hr) hDnonneg
    (dyadicSquareShellLeft_nonempty x₀ hr)
  have hLPoincare : ∫ x in L, (u x - cL) ^ 2 ≤ 512 * r ^ 2 * E := by
    calc
      ∫ x in L, (u x - cL) ^ 2 ≤
          ((2 : ℝ) ^ 2 * (Real.sqrt 2 * (4 * r))) ^ 2 *
            ∫ x in L, vecNormSq (u.grad x) := by
        simpa only [L, cL] using hLPoincareRaw
      _ = 512 * r ^ 2 * ∫ x in L, vecNormSq (u.grad x) := by rw [hCoeff]
      _ ≤ 512 * r ^ 2 * E := by gcongr
  have hBPoincareRaw := centeredPoincare_sq_on_boundedConvexSubdomain u
    hBdom hBU (dyadicSquareShellBottom_diameter x₀ hr) hDnonneg
    (dyadicSquareShellBottom_nonempty x₀ hr)
  have hBPoincare : ∫ x in B, (u x - cB) ^ 2 ≤ 512 * r ^ 2 * E := by
    calc
      ∫ x in B, (u x - cB) ^ 2 ≤
          ((2 : ℝ) ^ 2 * (Real.sqrt 2 * (4 * r))) ^ 2 *
            ∫ x in B, vecNormSq (u.grad x) := by
        simpa only [B, cB] using hBPoincareRaw
      _ = 512 * r ^ 2 * ∫ x in B, vecNormSq (u.grad x) := by rw [hCoeff]
      _ ≤ 512 * r ^ 2 * E := by gcongr
  have hRPoincareRaw := centeredPoincare_sq_on_boundedConvexSubdomain u
    hRdom hRU (dyadicSquareShellRight_diameter x₀ hr) hDnonneg
    (dyadicSquareShellRight_nonempty x₀ hr)
  have hRPoincare : ∫ x in R, (u x - cR) ^ 2 ≤ 512 * r ^ 2 * E := by
    calc
      ∫ x in R, (u x - cR) ^ 2 ≤
          ((2 : ℝ) ^ 2 * (Real.sqrt 2 * (4 * r))) ^ 2 *
            ∫ x in R, vecNormSq (u.grad x) := by
        simpa only [R, cR] using hRPoincareRaw
      _ = 512 * r ^ 2 * ∫ x in R, vecNormSq (u.grad x) := by rw [hCoeff]
      _ ≤ 512 * r ^ 2 * E := by gcongr
  have hGlue := setIntegral_sq_sub_le_root_center_four_tree
    (u := u) (S := S) (sT := T) (sL := L) (sB := B) (sR := R)
    (cT := cT) (cL := cL) (cB := cB) (cR := cR)
    (VT := 512 * r ^ 2 * E) (VL := 512 * r ^ 2 * E)
    (VB := 512 * r ^ 2 * E) (VR := 512 * r ^ 2 * E)
    (M := 4 * r ^ 2) (m := r ^ 2)
    hcover hIntT hIntL hIntB hIntR hIntLRoot hIntBRoot hIntRRoot
    hfiniteL hfiniteB hfiniteR hTLmeas hLBmeas hTRmeas
    hTLfinite hLBfinite hTRfinite hm hTLvol hLBvol hTRvol
    hTvol hLvol hBvol hRvol hTPoincare hLPoincare hBPoincare hRPoincare
  have hconst :
      (2 + 20 * (4 * r ^ 2) / r ^ 2) *
          (512 * r ^ 2 * E + 512 * r ^ 2 * E +
            512 * r ^ 2 * E + 512 * r ^ 2 * E) =
        167936 * r ^ 2 * E := by
    field_simp [ne_of_gt hr]
    ring
  simpa only [S, cT] using hGlue.trans_eq hconst

end PDE
