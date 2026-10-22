module

public import PDEFoundation.Sobolev.Trace.Model.TraceCalculus
public import PDEFoundation.Ambient.Basis
public import PDEFoundation.Ambient.EuclideanNorm

/-!
# Step 3 of the trace theorem: the pointwise oscillation bound

For `x' ≠ y'` and `h = |y' - x'|`, comparing `v(x', 0)` and `v(y', 0)` through the values at
height `h` gives
`|w x' - w y'| ≤ ∫_0^h |∂ₜ v(x', ·)| + h ∫_0^1 |∇' v(x' + θ(y'-x'), h)| dθ + ∫_0^h |∂ₜ v(y', ·)|`
in `lintegral` form.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology
open scoped ENNReal

variable {n : ℕ}

/-- `∫_0^r |∂ₜ v(x', t)| dt`. -/
noncomputable def vertInt (v : Vec n × ℝ → ℝ) (x' : Vec n) (r : ℝ) : ℝ≥0∞ :=
  ∫⁻ t in Ioc 0 r, ENNReal.ofReal |normDeriv v (x', t)|

/-- Euclidean length of the tangential gradient. -/
noncomputable def tanGradNorm (v : Vec n × ℝ → ℝ) (z : Vec n × ℝ) : ℝ :=
  vecEuclideanNorm (tanGrad v z)

theorem fderiv_horizontal_eq_vecDot (v : Vec n × ℝ → ℝ) (z : Vec n × ℝ) (k : Vec n) :
    fderiv ℝ v z (k, 0) = vecDot k (tanGrad v z) := by
  have h : ((k, (0 : ℝ)) : Vec n × ℝ) = ∑ i : Fin n, k i • ((basisVec i : Vec n), (0 : ℝ)) := by
    ext j
    · simp only [Prod.fst_sum, Prod.smul_fst, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        basisVec_apply]
      simp
    · simp [Prod.snd_sum]
  rw [h, map_sum]
  simp only [map_smul, smul_eq_mul, vecDot, tanGrad]

theorem abs_fderiv_horizontal_le (v : Vec n × ℝ → ℝ) (z : Vec n × ℝ) (k : Vec n) :
    |fderiv ℝ v z (k, 0)| ≤ vecEuclideanNorm k * tanGradNorm v z := by
  rw [fderiv_horizontal_eq_vecDot]
  exact abs_vecDot_le_vecEuclideanNorm_mul k (tanGrad v z)

section Smooth

variable {v : Vec n × ℝ → ℝ} (hv : ContDiffOn ℝ 1 v (closedUpperHalf n))
include hv

/-- Vertical comparison: `|v(x',h) - v(x',0)| ≤ ∫_0^h |∂ₜ v(x',t)| dt`. -/
theorem ofReal_abs_slice_sub_le (x' : Vec n) {h : ℝ} (hh : 0 ≤ h) :
    ENNReal.ofReal |v (x', h) - v (x', 0)| ≤ vertInt v x' h := by
  have hsl := continuousOn_slice hv x'
  have hcu : ContinuousOn (fun s : ℝ => v (x', s)) (Icc 0 h) := hsl.mono Icc_subset_Ici_self
  have hd : ∀ t ∈ Ioo 0 h, HasDerivAt (fun s : ℝ => v (x', s))
      (fderivWithin ℝ v (closedUpperHalf n) (x', t) (0, 1)) t := by
    intro t ht
    rw [slice_deriv_eq (v := v) x' ht.1]
    exact hasDerivAt_slice hv x' ht.1
  have hi : IntervalIntegrable
      (fun s : ℝ => fderivWithin ℝ v (closedUpperHalf n) (x', s) (0, 1)) volume 0 h :=
    ((continuousOn_slice_deriv hv x').mono Icc_subset_Ici_self).intervalIntegrable_of_Icc hh
  refine (ofReal_abs_sub_le_lintegral hh hcu hd hi).trans (le_of_eq ?_)
  refine setLIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
  rw [slice_deriv_eq (v := v) x' ht.1]

/-- Horizontal comparison at height `h > 0` along the segment from `x'` to `x' + k`. -/
theorem ofReal_abs_segment_sub_le (x' k : Vec n) {h : ℝ} (hh : 0 < h) :
    ENNReal.ofReal |v (x' + k, h) - v (x', h)| ≤
      ENNReal.ofReal (vecEuclideanNorm k) *
        ∫⁻ θ in Ioc (0 : ℝ) 1, ENNReal.ofReal (tanGradNorm v (x' + θ • k, h)) := by
  have hmem : ∀ θ : ℝ, (x' + θ • k, h) ∈ upperHalf n := fun θ => mem_upperHalf_iff.2 hh
  have hcurve : Continuous (fun θ : ℝ => ((x' + θ • k, h) : Vec n × ℝ)) := by fun_prop
  have hcu : ContinuousOn (fun θ : ℝ => v (x' + θ • k, h)) (Icc 0 1) :=
    hv.continuousOn.comp hcurve.continuousOn
      (fun θ _ => upperHalf_subset_closed (hmem θ))
  have hd : ∀ θ ∈ Ioo (0 : ℝ) 1, HasDerivAt (fun s : ℝ => v (x' + s • k, h))
      (fderiv ℝ v (x' + θ • k, h) (k, 0)) θ := fun θ _ => hasDerivAt_segment hv x' k hh θ
  have hcd' : ContinuousOn (fun θ : ℝ => fderiv ℝ v (x' + θ • k, h) (k, 0)) (Icc 0 1) :=
    (ContinuousLinearMap.apply ℝ ℝ ((k : Vec n), (0 : ℝ))).continuous.comp_continuousOn
      ((continuousOn_fderiv_upper hv).comp hcurve.continuousOn (fun θ _ => hmem θ))
  have hF := ofReal_abs_sub_le_lintegral (zero_le_one' ℝ) hcu hd
    (hcd'.intervalIntegrable_of_Icc (zero_le_one' ℝ))
  simp only [one_smul, zero_smul, add_zero] at hF
  refine hF.trans ?_
  calc ∫⁻ θ in Ioc (0 : ℝ) 1, ENNReal.ofReal |fderiv ℝ v (x' + θ • k, h) (k, 0)|
      ≤ ∫⁻ θ in Ioc (0 : ℝ) 1, ENNReal.ofReal (vecEuclideanNorm k) *
          ENNReal.ofReal (tanGradNorm v (x' + θ • k, h)) := by
        refine lintegral_mono (fun θ => ?_)
        rw [← ENNReal.ofReal_mul (vecEuclideanNorm_nonneg k)]
        exact ENNReal.ofReal_le_ofReal (abs_fderiv_horizontal_le v _ k)
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- **Pointwise oscillation bound** (manuscript Step 3). -/
theorem ofReal_abs_boundary_sub_le (x' y' : Vec n) (hne : x' ≠ y') :
    ENNReal.ofReal |v (x', 0) - v (y', 0)| ≤
      vertInt v x' (vecEuclideanNorm (y' - x')) +
        ENNReal.ofReal (vecEuclideanNorm (y' - x')) *
          (∫⁻ θ in Ioc (0 : ℝ) 1,
            ENNReal.ofReal (tanGradNorm v (x' + θ • (y' - x'), vecEuclideanNorm (y' - x')))) +
        vertInt v y' (vecEuclideanNorm (y' - x')) := by
  set h := vecEuclideanNorm (y' - x') with hh
  have hpos : 0 < h := vecEuclideanNorm_pos_iff.2 (sub_ne_zero.2 hne.symm)
  have h1 := ofReal_abs_slice_sub_le hv x' hpos.le
  have h2 := ofReal_abs_segment_sub_le hv x' (y' - x') hpos
  have h3 := ofReal_abs_slice_sub_le hv y' hpos.le
  rw [add_sub_cancel] at h2
  have htri : |v (x', 0) - v (y', 0)| ≤ |v (x', h) - v (x', 0)| + |v (y', h) - v (x', h)| +
      |v (y', h) - v (y', 0)| := by
    have e : v (x', 0) - v (y', 0) = (v (x', 0) - v (x', h)) + (v (x', h) - v (y', h)) +
        (v (y', h) - v (y', 0)) := by ring
    rw [e]
    refine (abs_add_three _ _ _).trans (le_of_eq ?_)
    rw [abs_sub_comm (v (x', 0)) (v (x', h)), abs_sub_comm (v (x', h)) (v (y', h))]
  calc ENNReal.ofReal |v (x', 0) - v (y', 0)|
      ≤ ENNReal.ofReal (|v (x', h) - v (x', 0)| + |v (y', h) - v (x', h)| +
          |v (y', h) - v (y', 0)|) := ENNReal.ofReal_le_ofReal htri
    _ = ENNReal.ofReal |v (x', h) - v (x', 0)| + ENNReal.ofReal |v (y', h) - v (x', h)| +
          ENNReal.ofReal |v (y', h) - v (y', 0)| := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity),
          ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ _ := add_le_add (add_le_add h1 h2) h3

end Smooth

end PDE.TraceLane
