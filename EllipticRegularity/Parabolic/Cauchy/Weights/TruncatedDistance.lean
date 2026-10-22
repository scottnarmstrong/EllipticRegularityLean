module

public import PDEFoundation.Sobolev.Ch4.Lipschitz
public import PDEFoundation.Sobolev.Inequalities.SobolevWholeSpaceMollify
public import PDEFoundation.Sobolev.W1p.ConvexApprox.Kernel
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith

/-!
# Smooth approximations of truncated Euclidean set distance

The Nash--Aronson weight is built from distance to the initial support.  The
distance is taken in the explicit Euclidean norm on `Vec d`, then truncated;
the standard positive mollifier gives smooth profiles with the same Euclidean
Lipschitz constant and a uniform approximation error.
-/

@[expose] public section

open scoped Convolution
open MeasureTheory Set Filter Topology

namespace PDE.Parabolic.Cauchy.Weights

variable {d : ℕ}

/-- Euclidean distance from a point to a nonempty set. -/
noncomputable def euclideanSetDistance (K : Set (Vec d)) (x : Vec d) : ℝ :=
  sInf (Set.range fun y : K => vecEuclideanNorm (x - (y : Vec d)))

private theorem euclideanSetDistance_range_nonempty {K : Set (Vec d)}
    (hK : K.Nonempty) (x : Vec d) :
    (Set.range fun y : K => vecEuclideanNorm (x - (y : Vec d))).Nonempty := by
  rcases hK with ⟨y, hy⟩
  exact ⟨vecEuclideanNorm (x - y), ⟨⟨y, hy⟩, rfl⟩⟩

private theorem euclideanSetDistance_bddBelow (K : Set (Vec d)) (x : Vec d) :
    BddBelow (Set.range fun y : K => vecEuclideanNorm (x - (y : Vec d))) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨y, rfl⟩
  exact vecEuclideanNorm_nonneg _

theorem euclideanSetDistance_nonneg {K : Set (Vec d)} (hK : K.Nonempty)
    (x : Vec d) : 0 ≤ euclideanSetDistance K x := by
  apply le_csInf (euclideanSetDistance_range_nonempty hK x)
  rintro _ ⟨y, rfl⟩
  exact vecEuclideanNorm_nonneg _

private theorem euclideanSetDistance_le {K : Set (Vec d)}
    (x : Vec d) (y : K) :
    euclideanSetDistance K x ≤ vecEuclideanNorm (x - (y : Vec d)) := by
  exact csInf_le (euclideanSetDistance_bddBelow K x) ⟨y, rfl⟩

private theorem le_euclideanSetDistance {K : Set (Vec d)}
    (hK : K.Nonempty) (x : Vec d) (b : ℝ)
    (hb : ∀ y : K, b ≤ vecEuclideanNorm (x - (y : Vec d))) :
    b ≤ euclideanSetDistance K x := by
  apply le_csInf (euclideanSetDistance_range_nonempty hK x)
  rintro _ ⟨y, rfl⟩
  exact hb y

private theorem euclideanSetDistance_triangle {K : Set (Vec d)}
    (hK : K.Nonempty) (x y : Vec d) :
    euclideanSetDistance K x ≤ vecEuclideanNorm (x - y) +
      euclideanSetDistance K y := by
  have hsub : euclideanSetDistance K x - vecEuclideanNorm (x - y) ≤
      euclideanSetDistance K y := by
    apply le_euclideanSetDistance hK y
    intro z
    have hDx := euclideanSetDistance_le x z
    have htriangle' : vecEuclideanNorm (x - (z : Vec d)) ≤
        vecEuclideanNorm (x - y) + vecEuclideanNorm (y - (z : Vec d)) := by
      rw [show x - (z : Vec d) = (x - y) + (y - (z : Vec d)) by abel]
      exact vecEuclideanNorm_add_le _ _
    linarith only [hDx, htriangle']
  linarith

/-- Distance to a set is Euclidean `1`-Lipschitz. -/
theorem euclideanSetDistance_eucLip {K : Set (Vec d)} (hK : K.Nonempty) :
    PDE.Ch4Infra.EucLip 1 (euclideanSetDistance K) := by
  intro x y
  rw [abs_le]
  constructor
  · have hyx := euclideanSetDistance_triangle hK y x
    rw [vecEuclideanNorm_sub_comm] at hyx
    have hnorm := vecEuclideanNorm_nonneg (x - y)
    have hlow : -(vecEuclideanNorm (x - y)) ≤
        euclideanSetDistance K x - euclideanSetDistance K y := by linarith
    simpa only [one_mul] using hlow
  · have hxy := euclideanSetDistance_triangle hK x y
    have hnorm := vecEuclideanNorm_nonneg (x - y)
    have hhigh : euclideanSetDistance K x - euclideanSetDistance K y ≤
        vecEuclideanNorm (x - y) := by linarith
    simpa only [one_mul] using hhigh

/-- Distance to a nonempty set, capped at radius `R`. -/
noncomputable def truncatedEuclideanSetDistance (K : Set (Vec d))
    (R : ℝ) (x : Vec d) : ℝ := min R (euclideanSetDistance K x)

theorem truncatedEuclideanSetDistance_nonneg {K : Set (Vec d)}
    (hK : K.Nonempty) {R : ℝ} (hR : 0 ≤ R) (x : Vec d) :
    0 ≤ truncatedEuclideanSetDistance K R x := by
  exact le_min hR (euclideanSetDistance_nonneg hK x)

theorem truncatedEuclideanSetDistance_le {K : Set (Vec d)}
    {R : ℝ} (x : Vec d) :
    truncatedEuclideanSetDistance K R x ≤ R := min_le_left _ _

theorem truncatedEuclideanSetDistance_eucLip {K : Set (Vec d)}
    (hK : K.Nonempty) {R : ℝ} :
    PDE.Ch4Infra.EucLip 1 (truncatedEuclideanSetDistance K R) := by
  change PDE.Ch4Infra.EucLip 1 (fun x => min R (euclideanSetDistance K x))
  simpa only [max_eq_left (by norm_num : (0 : ℝ) ≤ 1), min_comm] using
    PDE.Ch4Infra.EucLip.min (euclideanSetDistance_eucLip hK)
      (PDE.Ch4Infra.EucLip.const R)

private theorem scaledUnitKernel_eq_zero_of_lt_norm {a : ℝ} (ha : 0 < a)
    {y : Vec d} (hy : a < ‖y‖) :
    scaledConvexApproxKernel (unitConvexApproxKernel (d := d)) a y = 0 := by
  have hρ := isConvexApproxKernel_unitConvexApproxKernel (d := d)
  have hnorm : 1 < ‖a⁻¹ • y‖ := by
    rw [norm_smul, norm_inv, Real.norm_of_nonneg ha.le]
    rw [← div_eq_inv_mul, lt_div_iff₀ ha]
    simpa using hy
  have hnot : a⁻¹ • y ∉ tsupport (unitConvexApproxKernel (d := d)) := fun hmem =>
    absurd (by simpa using hρ.support_subset_closedBall hmem) (not_le.mpr hnorm)
  simp [scaledConvexApproxKernel, image_eq_zero_of_notMem_tsupport hnot]

private theorem convolutionExists_scaledUnitKernel {a : ℝ} (ha : 0 < a)
    {f : Vec d → ℝ} (hf : LocallyIntegrable f volume) :
    ConvolutionExists
      (scaledConvexApproxKernel (unitConvexApproxKernel (d := d)) a) f
      (ContinuousLinearMap.lsmul ℝ ℝ) volume :=
  (hasCompactSupport_scaledConvexApproxKernel
    (isConvexApproxKernel_unitConvexApproxKernel (d := d)).compactSupport ha).convolutionExists_left
    _ (continuous_scaledConvexApproxKernel
      (isConvexApproxKernel_unitConvexApproxKernel (d := d)).continuous a) hf

private theorem wholeSpaceMollify_eq_kernel_integral {a : ℝ}
    {h : Vec d → ℝ} (x : Vec d) :
    PDE.wholeSpaceMollify a h x =
      ∫ t, scaledConvexApproxKernel (unitConvexApproxKernel (d := d)) a t * h (x - t) := by
  simp [PDE.wholeSpaceMollify, convolution_def, ContinuousLinearMap.lsmul_apply,
    smul_eq_mul]

/-- Nonnegative bounded profiles stay in the same pointwise bounds after
convolution by the standard probability mollifier. -/
theorem wholeSpaceMollify_bounds {a B : ℝ} (ha : 0 < a) {h : Vec d → ℝ}
    (hhLip : PDE.Ch4Infra.EucLip 1 h)
    (hbound : ∀ x, 0 ≤ h x ∧ h x ≤ B) (x : Vec d) :
    0 ≤ PDE.wholeSpaceMollify a h x ∧ PDE.wholeSpaceMollify a h x ≤ B := by
  let K : Vec d → ℝ := scaledConvexApproxKernel
    (unitConvexApproxKernel (d := d)) a
  have hρ := isConvexApproxKernel_unitConvexApproxKernel (d := d)
  have hKnn : ∀ t, 0 ≤ K t := scaledConvexApproxKernel_nonneg hρ ha
  have hKint : Integrable K := integrable_scaledConvexApproxKernel hρ ha
  have hKone : ∫ t, K t = 1 := integral_scaledConvexApproxKernel hρ ha
  have hcont : Continuous h := hhLip.continuous (by norm_num)
  have hloc : LocallyIntegrable h volume := hcont.locallyIntegrable
  have hmeas : AEStronglyMeasurable (fun t : Vec d => h (x - t)) volume :=
    (hcont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hint : Integrable (fun t : Vec d => K t * h (x - t)) volume := by
    have hbound' : ∀ᵐ t : Vec d, ‖h (x - t)‖ ≤ B := by
      filter_upwards [] with t
      rw [Real.norm_eq_abs, abs_of_nonneg (hbound (x - t)).1]
      exact (hbound (x - t)).2
    have hint' := hKint.bdd_mul hmeas (c := B) hbound'
    simpa only [mul_comm] using hint'
  have hnonneg : 0 ≤ ∫ t, K t * h (x - t) := by
    apply integral_nonneg_of_ae
    filter_upwards [] with t
    exact mul_nonneg (hKnn t) (hbound (x - t)).1
  have hupper : ∫ t, K t * h (x - t) ≤ B := by
    calc
      ∫ t, K t * h (x - t) ≤ ∫ t, K t * B := by
        apply integral_mono_ae hint (hKint.mul_const B)
        filter_upwards [] with t
        exact mul_le_mul_of_nonneg_left (hbound (x - t)).2 (hKnn t)
      _ = B := by rw [integral_mul_const, hKone, one_mul]
  rw [wholeSpaceMollify_eq_kernel_integral x]
  exact ⟨hnonneg, hupper⟩

/-- Convolution with the nonnegative normalized kernel preserves a Euclidean
Lipschitz constant. -/
theorem wholeSpaceMollify_eucLip {a L B : ℝ} (ha : 0 < a) {h : Vec d → ℝ}
    (hhLip : PDE.Ch4Infra.EucLip L h) (hL : 0 ≤ L)
    (hbound : ∀ x, |h x| ≤ B) :
    PDE.Ch4Infra.EucLip L (PDE.wholeSpaceMollify a h) := by
  intro x y
  let K : Vec d → ℝ := scaledConvexApproxKernel
    (unitConvexApproxKernel (d := d)) a
  have hρ := isConvexApproxKernel_unitConvexApproxKernel (d := d)
  have hKnn : ∀ t, 0 ≤ K t := scaledConvexApproxKernel_nonneg hρ ha
  have hKint : Integrable K := integrable_scaledConvexApproxKernel hρ ha
  have hKone : ∫ t, K t = 1 := integral_scaledConvexApproxKernel hρ ha
  have hcont : Continuous h := hhLip.continuous hL
  have hloc : LocallyIntegrable h volume := hcont.locallyIntegrable
  have hmeas : ∀ v : Vec d, AEStronglyMeasurable (fun t : Vec d => h (v - t)) volume := by
    intro v
    exact (hcont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hint : ∀ v : Vec d,
      Integrable (fun t : Vec d => K t * h (v - t)) volume := by
    intro v
    have hbound' : ∀ᵐ t : Vec d, ‖h (v - t)‖ ≤ B := by
      filter_upwards [] with t
      rw [Real.norm_eq_abs]
      exact hbound (v - t)
    have hint' := hKint.bdd_mul (hmeas v) (c := B) hbound'
    simpa only [mul_comm] using hint'
  have hdiff :
      PDE.wholeSpaceMollify a h x - PDE.wholeSpaceMollify a h y =
        ∫ t, K t * (h (x - t) - h (y - t)) := by
    rw [wholeSpaceMollify_eq_kernel_integral x,
      wholeSpaceMollify_eq_kernel_integral y]
    rw [← integral_sub (hint x) (hint y)]
    congr 1
    funext t
    ring
  have hFint : Integrable
      (fun t : Vec d => K t * (h (x - t) - h (y - t))) volume := by
    convert (hint x).sub (hint y) using 1
    ext t
    change K t * (h (x - t) - h (y - t)) =
      K t * h (x - t) - K t * h (y - t)
    ring
  have hboundInt : Integrable
      (fun t : Vec d => K t * (L * vecEuclideanNorm (x - y))) volume :=
    hKint.mul_const _
  have hpoint : ∀ t,
      |K t * (h (x - t) - h (y - t))| ≤
        K t * (L * vecEuclideanNorm (x - y)) := by
    intro t
    have hLip := hhLip (x - t) (y - t)
    have hdist : vecEuclideanNorm ((x - t) - (y - t)) =
        vecEuclideanNorm (x - y) := by
      congr 1
      abel
    rw [hdist] at hLip
    rw [abs_mul, abs_of_nonneg (hKnn t)]
    exact mul_le_mul_of_nonneg_left hLip (hKnn t)
  have habs :
      |∫ t, K t * (h (x - t) - h (y - t))| ≤
        ∫ t, |K t * (h (x - t) - h (y - t))| :=
    abs_integral_le_integral_abs
  have hmono :
      ∫ t, |K t * (h (x - t) - h (y - t))| ≤
        ∫ t, K t * (L * vecEuclideanNorm (x - y)) := by
    apply integral_mono_ae (hFint.norm) hboundInt
    filter_upwards [] with t
    exact hpoint t
  have hfinal :
      |∫ t, K t * (h (x - t) - h (y - t))| ≤ L * vecEuclideanNorm (x - y) := by
    calc
      _ ≤ ∫ t, K t * (L * vecEuclideanNorm (x - y)) := habs.trans hmono
      _ = L * vecEuclideanNorm (x - y) := by
        rw [show (fun t : Vec d => K t * (L * vecEuclideanNorm (x - y))) =
          fun t => (L * vecEuclideanNorm (x - y)) * K t by
            funext t
            ring]
        rw [integral_const_mul, hKone, mul_one]
  calc
    |PDE.wholeSpaceMollify a h x - PDE.wholeSpaceMollify a h y| =
        |∫ t, K t * (h (x - t) - h (y - t))| := by rw [hdiff]
    _ ≤ L * vecEuclideanNorm (x - y) := hfinal

/-- Uniform error bound for mollifying an `L`-Lipschitz function.  The factor
`sqrt d` converts the kernel support bound from the inherited norm to the
explicit Euclidean norm on `Vec d`. -/
theorem wholeSpaceMollify_uniform_error {a L B : ℝ} (ha : 0 < a)
    {h : Vec d → ℝ} (hhLip : PDE.Ch4Infra.EucLip L h) (hL : 0 ≤ L)
    (hbound : ∀ x, |h x| ≤ B) (x : Vec d) :
    |PDE.wholeSpaceMollify a h x - h x| ≤ L * Real.sqrt d * a := by
  let K : Vec d → ℝ := scaledConvexApproxKernel
    (unitConvexApproxKernel (d := d)) a
  have hρ := isConvexApproxKernel_unitConvexApproxKernel (d := d)
  have hKnn : ∀ t, 0 ≤ K t := scaledConvexApproxKernel_nonneg hρ ha
  have hKint : Integrable K := integrable_scaledConvexApproxKernel hρ ha
  have hKone : ∫ t, K t = 1 := integral_scaledConvexApproxKernel hρ ha
  have hcont : Continuous h := hhLip.continuous hL
  have hloc : LocallyIntegrable h volume := hcont.locallyIntegrable
  have hmeasx : AEStronglyMeasurable (fun t : Vec d => h (x - t)) volume :=
    (hcont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  have hintx : Integrable (fun t : Vec d => K t * h (x - t)) volume := by
    have hbound' : ∀ᵐ t : Vec d, ‖h (x - t)‖ ≤ B := by
      filter_upwards [] with t
      rw [Real.norm_eq_abs]
      exact hbound (x - t)
    have hint' := hKint.bdd_mul hmeasx (c := B) hbound'
    simpa only [mul_comm] using hint'
  have hconstant : Integrable (fun t : Vec d => K t * h x) volume := hKint.mul_const _
  have hdiff : PDE.wholeSpaceMollify a h x - h x =
      ∫ t, K t * (h (x - t) - h x) := by
    have hconv := wholeSpaceMollify_eq_kernel_integral (a := a) (h := h) x
    have hconst : ∫ t, K t * h x = h x := by
      rw [integral_mul_const, hKone, one_mul]
    calc
      PDE.wholeSpaceMollify a h x - h x =
          (∫ t, K t * h (x - t)) - h x := by rw [hconv]
      _ =
          (∫ t, K t * h (x - t)) - ∫ t, K t * h x := by rw [hconst]
      _ =
          ∫ t, (K t * h (x - t) - K t * h x) :=
        (integral_sub hintx hconstant).symm
      _ = ∫ t, K t * (h (x - t) - h x) := by
        congr 1
        funext t
        ring
  have hFint : Integrable
      (fun t : Vec d => K t * (h (x - t) - h x)) volume := by
    convert hintx.sub hconstant using 1
    ext t
    change K t * (h (x - t) - h x) = K t * h (x - t) - K t * h x
    ring
  let C : ℝ := L * Real.sqrt d * a
  have hCint : Integrable (fun t : Vec d => K t * C) volume := hKint.mul_const C
  have hkernel : ∀ t, K t ≠ 0 → ‖t‖ ≤ a := by
    intro t hKt
    by_contra hnot
    have ht : a < ‖t‖ := lt_of_not_ge hnot
    have hz := scaledUnitKernel_eq_zero_of_lt_norm ha ht
    exact hKt (by simpa [K] using hz)
  have hpoint : ∀ t,
      |K t * (h (x - t) - h x)| ≤ K t * C := by
    intro t
    by_cases hKt : K t = 0
    · simp [hKt]
    · have hLip := hhLip (x - t) x
      have hdiffnorm : vecEuclideanNorm ((x - t) - x) = vecEuclideanNorm t := by
        rw [show (x - t) - x = -t by abel, vecEuclideanNorm_neg]
      rw [hdiffnorm] at hLip
      have hnorm : vecEuclideanNorm t ≤ Real.sqrt d * a := by
        calc
          vecEuclideanNorm t ≤ Real.sqrt d * ‖t‖ :=
            vecEuclideanNorm_le_sqrt_natCast_mul_norm t
          _ ≤ Real.sqrt d * a :=
            mul_le_mul_of_nonneg_left (hkernel t hKt) (Real.sqrt_nonneg _)
      have hLip' : |h (x - t) - h x| ≤ L * (Real.sqrt d * a) :=
        hLip.trans (mul_le_mul_of_nonneg_left hnorm hL)
      rw [abs_mul, abs_of_nonneg (hKnn t)]
      calc
        K t * |h (x - t) - h x| ≤ K t * (L * (Real.sqrt d * a)) :=
          mul_le_mul_of_nonneg_left hLip' (hKnn t)
        _ = K t * C := by dsimp [C]; ring
  have habs :
      |∫ t, K t * (h (x - t) - h x)| ≤
        ∫ t, |K t * (h (x - t) - h x)| :=
    abs_integral_le_integral_abs
  have hmono :
      ∫ t, |K t * (h (x - t) - h x)| ≤ ∫ t, K t * C := by
    apply integral_mono_ae (hFint.norm) hCint
    filter_upwards [] with t
    exact hpoint t
  have hfinal : |∫ t, K t * (h (x - t) - h x)| ≤ C := by
    calc
      _ ≤ ∫ t, |K t * (h (x - t) - h x)| := habs
      _ ≤ ∫ t, K t * C := hmono
      _ = C := by
        rw [show (fun t : Vec d => K t * C) = fun t => C * K t by
          funext t
          ring]
        rw [integral_const_mul, hKone, mul_one]
  calc
    |PDE.wholeSpaceMollify a h x - h x| =
        |∫ t, K t * (h (x - t) - h x)| := by rw [hdiff]
    _ ≤ C := hfinal
    _ = L * Real.sqrt d * a := rfl

/-- The standard-scale mollifications of truncated set distance. -/
noncomputable def truncatedDistanceMollify (K : Set (Vec d)) (R : ℝ)
    (n : ℕ) : Vec d → ℝ :=
  PDE.wholeSpaceMollify (unitConvexApproxScale n)
    (truncatedEuclideanSetDistance K R)

/-- The smooth truncated-distance approximants retain the Euclidean
one-Lipschitz bound. -/
theorem truncatedDistanceMollify_eucLip {K : Set (Vec d)}
    (hK : K.Nonempty) {R : ℝ} (hR : 0 ≤ R) (n : ℕ) :
    PDE.Ch4Infra.EucLip 1 (truncatedDistanceMollify K R n) := by
  have hρLip : PDE.Ch4Infra.EucLip 1 (truncatedEuclideanSetDistance K R) :=
    truncatedEuclideanSetDistance_eucLip hK
  have hρbound : ∀ x, |truncatedEuclideanSetDistance K R x| ≤ R := by
    intro x
    rw [abs_of_nonneg (truncatedEuclideanSetDistance_nonneg hK hR x)]
    exact truncatedEuclideanSetDistance_le x
  simpa [truncatedDistanceMollify] using
    (wholeSpaceMollify_eucLip (unitConvexApproxScale_pos n) hρLip
      (by norm_num) hρbound)

/-- A mollified truncated distance is smooth, remains in `[0,R]`, has Euclidean
gradient length at most one, and converges uniformly with the explicit kernel
support error. -/
theorem truncatedDistanceMollify_properties {K : Set (Vec d)}
    (hK : K.Nonempty) {R : ℝ} (hR : 0 ≤ R) (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (truncatedDistanceMollify K R n) ∧
      (∀ x, 0 ≤ truncatedDistanceMollify K R n x ∧
        truncatedDistanceMollify K R n x ≤ R) ∧
      (∀ x, vecEuclideanNorm
        (classicalGradient (truncatedDistanceMollify K R n) x) ≤ 1) ∧
      (∀ x, |truncatedDistanceMollify K R n x -
        truncatedEuclideanSetDistance K R x| ≤
          Real.sqrt d * unitConvexApproxScale n) := by
  let ρ : Vec d → ℝ := truncatedEuclideanSetDistance K R
  let ε : ℝ := unitConvexApproxScale n
  have hε : 0 < ε := unitConvexApproxScale_pos n
  have hρLip : PDE.Ch4Infra.EucLip 1 ρ := by
    simpa only [ρ] using truncatedEuclideanSetDistance_eucLip hK
  have hρbounds : ∀ x, 0 ≤ ρ x ∧ ρ x ≤ R := by
    intro x
    exact ⟨truncatedEuclideanSetDistance_nonneg hK hR x,
      truncatedEuclideanSetDistance_le x⟩
  have hρabs : ∀ x, |ρ x| ≤ R := by
    intro x
    rw [abs_of_nonneg (hρbounds x).1]
    exact (hρbounds x).2
  have hρcont : Continuous ρ := hρLip.continuous (by norm_num)
  have hρloc : LocallyIntegrable ρ volume := hρcont.locallyIntegrable
  have hkernel : IsConvexApproxKernel
      (unitConvexApproxKernel (d := d)) :=
    isConvexApproxKernel_unitConvexApproxKernel
  have hsmooth : ContDiff ℝ (⊤ : ℕ∞)
      (PDE.wholeSpaceMollify ε ρ) := by
    apply HasCompactSupport.contDiff_convolution_left
      (L := ContinuousLinearMap.lsmul ℝ ℝ) (μ := volume)
    · exact hasCompactSupport_scaledConvexApproxKernel
        hkernel.compactSupport hε
    · exact contDiff_scaledConvexApproxKernel hkernel ε
    · exact hρloc
  have hbounds : ∀ x, 0 ≤ PDE.wholeSpaceMollify ε ρ x ∧
      PDE.wholeSpaceMollify ε ρ x ≤ R := by
    intro x
    exact wholeSpaceMollify_bounds hε hρLip hρbounds x
  have hmLip : PDE.Ch4Infra.EucLip 1 (PDE.wholeSpaceMollify ε ρ) :=
    wholeSpaceMollify_eucLip hε hρLip (by norm_num) hρabs
  have hgrad : ∀ x, vecEuclideanNorm
      (classicalGradient (PDE.wholeSpaceMollify ε ρ) x) ≤ 1 := by
    intro x
    exact PDE.Ch4Infra.EucLip.vecEuclideanNorm_classicalGradient_le
      hmLip (by norm_num) (hsmooth.contDiffAt.differentiableAt (by simp))
  have herr : ∀ x, |PDE.wholeSpaceMollify ε ρ x - ρ x| ≤
      Real.sqrt d * ε := by
    intro x
    simpa only [one_mul] using
      (wholeSpaceMollify_uniform_error hε hρLip (by norm_num) hρabs x)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [truncatedDistanceMollify, ρ, ε] using hsmooth
  · intro x
    simpa [truncatedDistanceMollify, ρ, ε] using hbounds x
  · intro x
    simpa [truncatedDistanceMollify, ρ, ε] using hgrad x
  · intro x
    simpa [truncatedDistanceMollify, ρ, ε] using herr x

/-- A mollified truncated distance is small on the original support set. -/
theorem truncatedDistanceMollify_le_of_mem {K : Set (Vec d)}
    (hK : K.Nonempty) {R : ℝ} (hR : 0 ≤ R) (n : ℕ)
    {x : Vec d} (hx : x ∈ K) :
    truncatedDistanceMollify K R n x ≤ Real.sqrt d * unitConvexApproxScale n := by
  obtain ⟨_, hbounds, _, herr⟩ := truncatedDistanceMollify_properties hK hR n
  have hdist : truncatedEuclideanSetDistance K R x = 0 := by
    have hDnonneg := truncatedEuclideanSetDistance_nonneg hK hR x
    have hDle : truncatedEuclideanSetDistance K R x ≤ 0 := by
      apply min_le_of_right_le
      simpa [vecEuclideanNorm, vecNormSq, vecDot] using
        euclideanSetDistance_le x (⟨x, hx⟩ : K)
    exact le_antisymm hDle hDnonneg
  have hsmall := herr x
  rw [hdist, sub_zero, abs_of_nonneg (hbounds x).1] at hsmall
  exact hsmall

/-- The smooth truncated distances converge pointwise to the Lipschitz
truncated distance. -/
theorem truncatedDistanceMollify_tendsto {K : Set (Vec d)}
    (hK : K.Nonempty) {R : ℝ} (hR : 0 ≤ R) (x : Vec d) :
    Tendsto (fun n => truncatedDistanceMollify K R n x) atTop
      (𝓝 (truncatedEuclideanSetDistance K R x)) := by
  have herror : Tendsto (fun n =>
      |truncatedDistanceMollify K R n x - truncatedEuclideanSetDistance K R x|)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun n => abs_nonneg _)
      (fun n => truncatedDistanceMollify_properties hK hR n |>.2.2.2 x)
    simpa using (tendsto_const_nhds.mul PDE.tendsto_unitConvexApproxScale_zero)
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simpa only [Real.norm_eq_abs] using herror

/-- Dominated convergence for the Gaussian weight of the regularized
truncated distance. -/
theorem mollifiedTruncatedDistance_weight_integral_tendsto
    {K : Set (Vec d)} (hK : K.Nonempty) {R c : ℝ} (hR : 0 ≤ R)
    (hc : 0 ≤ c) {F : Vec d → ℝ} (hF : Integrable F volume)
    (hFnonneg : ∀ x, 0 ≤ F x) :
    Tendsto (fun n => ∫ x : Vec d,
      Real.exp (c * (truncatedDistanceMollify K R n x) ^ 2) * F x) atTop
      (𝓝 <| ∫ x : Vec d,
        Real.exp (c * (truncatedEuclideanSetDistance K R x) ^ 2) * F x) := by
  let G : ℝ → ℝ := fun r => Real.exp (c * r ^ 2)
  let C : ℝ := Real.exp (c * R ^ 2)
  have hGcont : Continuous G := by
    dsimp [G]
    fun_prop
  have hdom : Integrable (fun x : Vec d => C * F x) volume := hF.const_mul C
  have hpoint : ∀ x, Tendsto
      (fun n => G (truncatedDistanceMollify K R n x) * F x) atTop
      (𝓝 (G (truncatedEuclideanSetDistance K R x) * F x)) := by
    intro x
    exact (hGcont.continuousAt.tendsto.comp
      (truncatedDistanceMollify_tendsto hK hR x)).mul_const (F x)
  have hmeas : ∀ n, AEStronglyMeasurable
      (fun x : Vec d => G (truncatedDistanceMollify K R n x) * F x) volume := by
    intro n
    have hprof := (truncatedDistanceMollify_properties hK hR n).1
    have hweight : Continuous
        (fun x : Vec d => G (truncatedDistanceMollify K R n x)) :=
      hGcont.comp hprof.continuous
    exact hweight.aestronglyMeasurable.mul hF.aestronglyMeasurable
  have hbound : ∀ n, ∀ᵐ x ∂volume,
      ‖G (truncatedDistanceMollify K R n x) * F x‖ ≤ C * F x := by
    intro n
    filter_upwards [] with x
    have hp := (truncatedDistanceMollify_properties hK hR n).2.1 x
    have hweight : 0 ≤ G (truncatedDistanceMollify K R n x) ∧
        G (truncatedDistanceMollify K R n x) ≤ C := by
      constructor
      · exact Real.exp_nonneg _
      · apply Real.exp_le_exp.mpr
        have hsq : (truncatedDistanceMollify K R n x) ^ 2 ≤ R ^ 2 := by
          nlinarith [sq_nonneg (truncatedDistanceMollify K R n x - R)]
        exact mul_le_mul_of_nonneg_left hsq hc
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hweight.1,
      abs_of_nonneg (hFnonneg x)]
    exact mul_le_mul_of_nonneg_right hweight.2 (hFnonneg x)
  have hlim : ∀ᵐ x ∂volume, Tendsto
      (fun n => G (truncatedDistanceMollify K R n x) * F x) atTop
      (𝓝 (G (truncatedEuclideanSetDistance K R x) * F x)) :=
    ae_of_all _ hpoint
  simpa only [G] using tendsto_integral_of_dominated_convergence
    (fun x : Vec d => C * F x) hmeas hdom hbound hlim

/-- If the density is supported on the set from which distance is measured,
the limiting Gaussian weight is one, so mollified weighted integrals converge
to the unweighted integral. -/
theorem mollifiedTruncatedDistance_source_integral_tendsto
    {K : Set (Vec d)} (hK : K.Nonempty) {R c : ℝ} (hR : 0 ≤ R)
    (hc : 0 ≤ c) {F : Vec d → ℝ} (hF : Integrable F volume)
    (hFnonneg : ∀ x, 0 ≤ F x)
    (hFzero : ∀ᵐ x ∂volume, x ∉ K → F x = 0) :
    Tendsto (fun n => ∫ x : Vec d,
      Real.exp (c * (truncatedDistanceMollify K R n x) ^ 2) * F x) atTop
      (𝓝 <| ∫ x : Vec d, F x) := by
  have hlim := mollifiedTruncatedDistance_weight_integral_tendsto
    hK hR hc hF hFnonneg
  have htarget :
      (∫ x : Vec d,
        Real.exp (c * (truncatedEuclideanSetDistance K R x) ^ 2) * F x) =
        ∫ x : Vec d, F x := by
    apply integral_congr_ae
    filter_upwards [hFzero] with x hx
    by_cases hxK : x ∈ K
    · have hdist : truncatedEuclideanSetDistance K R x = 0 := by
        have hDnonneg := truncatedEuclideanSetDistance_nonneg hK hR x
        have hDle : truncatedEuclideanSetDistance K R x ≤ 0 := by
          apply min_le_of_right_le
          simpa [vecEuclideanNorm, vecNormSq, vecDot] using
            euclideanSetDistance_le x (⟨x, hxK⟩ : K)
        exact le_antisymm hDle hDnonneg
      simp [hdist]
    · simp [hx hxK]
  rw [htarget] at hlim
  exact hlim

end PDE.Parabolic.Cauchy.Weights
