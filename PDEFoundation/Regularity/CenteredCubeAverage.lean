module

public import PDEFoundation.Measure.AxisBoxVolume
public import PDEFoundation.Sobolev.Mean
public import Mathlib.Tactic.Ring

/-!
# Averages and `L²` oscillations on centered axis cubes

This module supplies the square-specific mean comparison needed in the
proof of the Campanato characterisation. It deliberately uses `centeredAxisCube`, `integralAverage`,
and `normalizedVolumeOn`; it does not introduce a competing generic real
`L²`-norm facade.

The proof architecture is extracted from the native-vector Campanato
development in Superdiffusion, with the cube and average APIs moved into the
common foundation.
-/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

/-- The average of `u` over the open centered axis cube of half-side `r`. -/
def centeredCubeAverage {d : ℕ}
    (u : Vec d → ℝ) (x : Vec d) (r : ℝ) : ℝ :=
  integralAverage (centeredAxisCube x r) u

/-- The normalized `L²` oscillation of `u` about its own average on a centered
axis cube.

This purpose-specific total definition is used only together with explicit
integrability hypotheses in the Campanato theorems. -/
def centeredCubeL2Oscillation {d : ℕ}
    (u : Vec d → ℝ) (x : Vec d) (r : ℝ) : ℝ :=
  Real.sqrt
    (∫ y, (u y - centeredCubeAverage u x r) ^ 2 ∂
      normalizedVolumeOn (centeredAxisCube x r))

theorem centeredCubeAverage_eq_integral_normalizedVolumeOn {d : ℕ}
    (u : Vec d → ℝ) (x : Vec d) (r : ℝ) :
    centeredCubeAverage u x r =
      ∫ y, u y ∂normalizedVolumeOn (centeredAxisCube x r) := by
  exact
    (integral_normalizedVolumeOn_eq_integralAverage
      (centeredAxisCube x r) u).symm

theorem centeredCubeL2Oscillation_nonneg {d : ℕ}
    (u : Vec d → ℝ) (x : Vec d) (r : ℝ) :
    0 ≤ centeredCubeL2Oscillation u x r :=
  Real.sqrt_nonneg _

/-- The square of the normalized centered-cube `L²` oscillation is the raw
squared oscillation divided by the real cube volume. The identity is total;
positivity of the radius is needed only when dividing inequalities by this
volume later. -/
theorem centeredCubeL2Oscillation_sq_eq_setIntegral_div_volume
    {d : ℕ} (u : Vec d → ℝ) (x : Vec d) (r : ℝ) :
    centeredCubeL2Oscillation u x r ^ 2 =
      (∫ y in centeredAxisCube x r,
        (u y - integralAverage (centeredAxisCube x r) u) ^ 2) /
        (volume (centeredAxisCube x r)).toReal := by
  rw [centeredCubeL2Oscillation, Real.sq_sqrt]
  · rw [normalizedVolumeOn, integral_smul_measure,
      ENNReal.toReal_inv]
    change
      (volume (centeredAxisCube x r)).toReal⁻¹ *
          (∫ y in centeredAxisCube x r,
            (u y -
              integralAverage (centeredAxisCube x r) u) ^ 2) =
        _
    field_simp
  · exact integral_nonneg fun y => sq_nonneg _

private theorem integrableOn_sub_const_sq {d : ℕ}
    {W : Set (Vec d)} {u : Vec d → ℝ} (c : ℝ)
    (hWtop : volume W ≠ ⊤)
    (hu : IntegrableOn u W)
    (hu2 : IntegrableOn (fun y => u y ^ 2) W) :
    IntegrableOn (fun y => (u y - c) ^ 2) W := by
  have hpoly :
      IntegrableOn
        (fun y => u y ^ 2 - 2 * c * u y + c ^ 2) W :=
    (hu2.sub (hu.const_mul (2 * c))).add
      (integrableOn_const hWtop)
  convert hpoly using 1
  ext y
  ring

private theorem centeredCubeAverage_sub_const {d : ℕ}
    {u : Vec d → ℝ} {x : Vec d} {r : ℝ}
    (c : ℝ) (hr : 0 < r)
    (hu : IntegrableOn u (centeredAxisCube x r)) :
    centeredCubeAverage (fun y => u y - c) x r =
      centeredCubeAverage u x r - c := by
  unfold centeredCubeAverage integralAverage
  rw [integral_sub hu
      (integrableOn_const
        (volume_centeredAxisCube_ne_top x r)),
    setIntegral_const]
  simp only [measureReal_def, smul_eq_mul]
  have hvol :
      (volume (centeredAxisCube x r)).toReal ≠ 0 :=
    (volume_centeredAxisCube_toReal_pos x hr).ne'
  field_simp

private theorem
    abs_centeredCubeAverage_le_sqrt_integral_normalizedVolumeOn_sq
    {d : ℕ} {f : Vec d → ℝ} {x : Vec d} {r : ℝ}
    (hr : 0 < r)
    (hf : IntegrableOn f (centeredAxisCube x r))
    (hf2 : IntegrableOn (fun y => f y ^ 2)
      (centeredAxisCube x r)) :
    |centeredCubeAverage f x r| ≤
      Real.sqrt
        (∫ y, f y ^ 2 ∂
          normalizedVolumeOn (centeredAxisCube x r)) := by
  let Q := centeredAxisCube x r
  have hQpos : 0 < volume Q := by
    simpa only [Q] using
      volume_centeredAxisCube_pos x hr
  have hQtop : volume Q < ⊤ := by
    exact lt_top_iff_ne_top.mpr
      (by
        simpa only [Q] using
          volume_centeredAxisCube_ne_top x r)
  let : IsProbabilityMeasure (normalizedVolumeOn Q) :=
    isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top
      hQpos hQtop
  have hf' : Integrable f (normalizedVolumeOn Q) :=
    integrable_normalizedVolumeOn_of_integrableOn hf hQpos
  have hf2' :
      Integrable (fun y => |f y| ^ (2 : ℝ))
        (normalizedVolumeOn Q) := by
    have hsquare :
        (fun y => |f y| ^ (2 : ℝ)) =
          fun y => f y ^ 2 := by
      funext y
      rw [Real.rpow_two]
      exact sq_abs (f y)
    rw [hsquare]
    exact
      integrable_normalizedVolumeOn_of_integrableOn
        hf2 hQpos
  have hJensen :=
    abs_integral_rpow_le_integral_abs_rpow
      (p := (2 : ℝ)) (by norm_num) hf' hf2'
  rw [Real.rpow_two] at hJensen
  have hmean :
      (∫ y, f y ∂normalizedVolumeOn Q) =
        centeredCubeAverage f x r := by
    simpa only [Q] using
      (centeredCubeAverage_eq_integral_normalizedVolumeOn
        f x r).symm
  rw [hmean] at hJensen
  apply
    (sq_le_sq₀ (abs_nonneg _)
      (Real.sqrt_nonneg _)).mp
  have hnonneg :
      0 ≤ ∫ y, f y ^ 2 ∂normalizedVolumeOn Q :=
    integral_nonneg fun y => sq_nonneg (f y)
  rw [Real.sq_sqrt hnonneg]
  simpa only [Real.rpow_two, sq_abs] using hJensen

private theorem sqrt_integral_normalizedVolumeOn_sq_mono_subset
    {d : ℕ} {f : Vec d → ℝ}
    {x y : Vec d} {r R : ℝ}
    (hsub :
      centeredAxisCube y r ⊆ centeredAxisCube x R)
    (hr : 0 < r) (hR : 0 < R)
    (hf2 : IntegrableOn (fun z => f z ^ 2)
      (centeredAxisCube x R)) :
    Real.sqrt
        (∫ z, f z ^ 2 ∂
          normalizedVolumeOn (centeredAxisCube y r)) ≤
      Real.sqrt ((R / r) ^ d) *
        Real.sqrt
          (∫ z, f z ^ 2 ∂
            normalizedVolumeOn (centeredAxisCube x R)) := by
  let small := centeredAxisCube y r
  let large := centeredAxisCube x R
  have hsmallPos :
      0 < (volume small).toReal := by
    simpa only [small] using
      volume_centeredAxisCube_toReal_pos y hr
  have hlargePos :
      0 < (volume large).toReal := by
    simpa only [large] using
      volume_centeredAxisCube_toReal_pos x hR
  have hmonoint :
      ∫ z in small, f z ^ 2 ≤
        ∫ z in large, f z ^ 2 := by
    refine setIntegral_mono_set hf2 ?_ ?_
    · exact Filter.Eventually.of_forall
        fun z => sq_nonneg (f z)
    · exact Filter.Eventually.of_forall
        fun z hz => hsub hz
  have haverage :
      integralAverage small (fun z => f z ^ 2) ≤
        ((volume large).toReal /
            (volume small).toReal) *
          integralAverage large (fun z => f z ^ 2) := by
    unfold integralAverage
    have hrewrite :
        ((volume large).toReal /
            (volume small).toReal) *
            ((volume large).toReal⁻¹ *
              ∫ z in large, f z ^ 2) =
          (volume small).toReal⁻¹ *
            ∫ z in large, f z ^ 2 := by
      field_simp [hlargePos.ne']
    rw [hrewrite]
    exact mul_le_mul_of_nonneg_left hmonoint
      (by positivity)
  have hratio :
      0 ≤ (volume large).toReal /
        (volume small).toReal := by
    positivity
  calc
    Real.sqrt
        (∫ z, f z ^ 2 ∂normalizedVolumeOn small) =
        Real.sqrt
          (integralAverage small
            (fun z => f z ^ 2)) := by
      rw [integral_normalizedVolumeOn_eq_integralAverage]
    _ ≤ Real.sqrt
        (((volume large).toReal /
            (volume small).toReal) *
          integralAverage large
            (fun z => f z ^ 2)) :=
      Real.sqrt_le_sqrt haverage
    _ = Real.sqrt
          ((volume large).toReal /
            (volume small).toReal) *
        Real.sqrt
          (integralAverage large
            (fun z => f z ^ 2)) := by
      rw [Real.sqrt_mul hratio]
    _ = Real.sqrt ((R / r) ^ d) *
        Real.sqrt
          (∫ z, f z ^ 2 ∂
            normalizedVolumeOn large) := by
      rw [volume_centeredAxisCube_toReal_div_eq_div_pow
          x y hr hR,
        integral_normalizedVolumeOn_eq_integralAverage]

/-- Nested centered-cube averages differ by at most the larger cube's
normalized `L²` oscillation times the square root of the volume ratio. -/
theorem abs_centeredCubeAverage_sub_centeredCubeAverage_le
    {d : ℕ} {u : Vec d → ℝ}
    {x y : Vec d} {r R : ℝ}
    (hr : 0 < r) (hR : 0 < R)
    (hsub :
      centeredAxisCube y r ⊆ centeredAxisCube x R)
    (hu : IntegrableOn u (centeredAxisCube x R))
    (hu2 : IntegrableOn (fun z => u z ^ 2)
      (centeredAxisCube x R)) :
    |centeredCubeAverage u y r -
        centeredCubeAverage u x R| ≤
      Real.sqrt ((R / r) ^ d) *
        centeredCubeL2Oscillation u x R := by
  let c := centeredCubeAverage u x R
  let f : Vec d → ℝ := fun z => u z - c
  have husmall :
      IntegrableOn u (centeredAxisCube y r) :=
    hu.mono_set hsub
  have hu2small :
      IntegrableOn (fun z => u z ^ 2)
        (centeredAxisCube y r) :=
    hu2.mono_set hsub
  have hfsmall :
      IntegrableOn f (centeredAxisCube y r) := by
    exact husmall.sub
      (integrableOn_const
        (volume_centeredAxisCube_ne_top y r))
  have hf2small :
      IntegrableOn (fun z => f z ^ 2)
        (centeredAxisCube y r) := by
    exact
      integrableOn_sub_const_sq c
        (volume_centeredAxisCube_ne_top y r)
        husmall hu2small
  have hf2large :
      IntegrableOn (fun z => f z ^ 2)
        (centeredAxisCube x R) := by
    exact
      integrableOn_sub_const_sq c
        (volume_centeredAxisCube_ne_top x R)
        hu hu2
  have hmean :=
    centeredCubeAverage_sub_const
      (u := u) c hr husmall
  have hjensen :=
    abs_centeredCubeAverage_le_sqrt_integral_normalizedVolumeOn_sq
      hr hfsmall hf2small
  have hsubset :=
    sqrt_integral_normalizedVolumeOn_sq_mono_subset
      hsub hr hR hf2large
  calc
    |centeredCubeAverage u y r -
        centeredCubeAverage u x R| =
        |centeredCubeAverage f y r| := by
      rw [hmean]
    _ ≤ Real.sqrt
        (∫ z, f z ^ 2 ∂
          normalizedVolumeOn (centeredAxisCube y r)) :=
      hjensen
    _ ≤ Real.sqrt ((R / r) ^ d) *
        Real.sqrt
          (∫ z, f z ^ 2 ∂
            normalizedVolumeOn
              (centeredAxisCube x R)) :=
      hsubset
    _ = Real.sqrt ((R / r) ^ d) *
        centeredCubeL2Oscillation u x R := by
      rfl

end

end PDE
