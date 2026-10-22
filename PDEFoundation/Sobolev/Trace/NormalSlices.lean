module

public import PDEFoundation.Measure.AxisBoxSliceSummable
public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.Sobolev.Trace.NormalSliceCore

/-!
# Normal slices of a planar Sobolev function

For a function in `H¹` on an open planar axis box, Fubini supplies the value
and the appropriate coordinate of its weak gradient on almost every
coordinate slice.  For a common smooth approximation with dyadically
summable `H¹` graph errors, Fubini also gives vanishing value and
Euclidean-gradient errors on almost every slice.  The one-dimensional
smooth-limit theorem then constructs canonical continuous representatives
whose weak derivatives are the correct raw gradient coordinates.

Using one common planar approximation sequence is essential: it retains the
pointwise provenance later needed to identify normal-slice endpoint values
with square-side traces.
-/

@[expose] public section

namespace PDE

open Filter
open MeasureTheory Set
open scoped ENNReal Topology

noncomputable section

/-- On almost every vertical line through a planar axis box, an `L²` value
field and its second-coordinate candidate derivative both have genuine scalar
`L²` slices. -/
theorem ae_memLp_axisBox_vertical_value_and_normal_slices
    {f : Vec 2 → ℝ} {g : Vec 2 → Vec 2} {a b c d : ℝ}
    (hf : MemL2On (axisBox ![a, c] ![b, d]) f)
    (hg : MemL2On (axisBox ![a, c] ![b, d]) (fun x => g x 1)) :
    ∀ᵐ s ∂(volume.restrict (Ioo a b)),
      MemLp (fun t => f (squarePoint s t)) 2
          (volume.restrict (Ioo c d)) ∧
        MemLp (fun t => g (squarePoint s t) 1) 2
          (volume.restrict (Ioo c d)) := by
  filter_upwards [memLp_axisBox_slice_second_ae hf,
    memLp_axisBox_slice_second_ae hg] with s hsValue hsNormal
  exact ⟨hsValue, hsNormal⟩

/-- On almost every horizontal line through a planar axis box, an `L²` value
field and its first-coordinate candidate derivative both have genuine scalar
`L²` slices. -/
theorem ae_memLp_axisBox_horizontal_value_and_normal_slices
    {f : Vec 2 → ℝ} {g : Vec 2 → Vec 2} {a b c d : ℝ}
    (hf : MemL2On (axisBox ![a, c] ![b, d]) f)
    (hg : MemL2On (axisBox ![a, c] ![b, d]) (fun x => g x 0)) :
    ∀ᵐ t ∂(volume.restrict (Ioo c d)),
      MemLp (fun s => f (squarePoint s t)) 2
          (volume.restrict (Ioo a b)) ∧
        MemLp (fun s => g (squarePoint s t) 0) 2
          (volume.restrict (Ioo a b)) := by
  filter_upwards [memLp_axisBox_slice_first_ae hf,
    memLp_axisBox_slice_first_ae hg] with t htValue htNormal
  exact ⟨htValue, htNormal⟩

/-- The exact one-dimensional data obtained at one good vertical slice before
applying the smooth vector-error limit theorem. -/
structure VerticalSliceApproximationDataAt
    (F : ℕ → Vec 2 → ℝ) (u : Vec 2 → ℝ) (g : Vec 2 → Vec 2)
    (c d s : ℝ) : Prop where
  smooth : ∀ n, ContDiff ℝ 1 (F n)
  valueMemL2 : MemLp (verticalSlice u s) 2
    (volume.restrict (Icc c d))
  gradientMemL2 : MemLp (fun t => g (squarePoint s t) 1) 2
    (volume.restrict (Icc c d))
  valueErrorMemL2 : ∀ n, MemLp
    (fun t => verticalSlice (F n) s t - verticalSlice u s t)
    2 (volume.restrict (Icc c d))
  gradientErrorMemL2 : ∀ n, MemLp
    (fun t => vecEuclideanNorm
      (classicalGradient (F n) (squarePoint s t) -
        g (squarePoint s t)))
    2 (volume.restrict (Icc c d))
  valueErrorTendsto : Tendsto
    (fun n => ∫ t in Icc c d,
      |verticalSlice (F n) s t - verticalSlice u s t| ^ 2)
    atTop (𝓝 0)
  gradientErrorTendsto : Tendsto
    (fun n => ∫ t in Icc c d,
      vecEuclideanNorm
        (classicalGradient (F n) (squarePoint s t) -
          g (squarePoint s t)) ^ 2)
    atTop (𝓝 0)

/-- The exact one-dimensional data obtained at one good horizontal slice
before applying the smooth vector-error limit theorem. -/
structure HorizontalSliceApproximationDataAt
    (F : ℕ → Vec 2 → ℝ) (u : Vec 2 → ℝ) (g : Vec 2 → Vec 2)
    (a b t : ℝ) : Prop where
  smooth : ∀ n, ContDiff ℝ 1 (F n)
  valueMemL2 : MemLp (horizontalSlice u t) 2
    (volume.restrict (Icc a b))
  gradientMemL2 : MemLp (fun s => g (squarePoint s t) 0) 2
    (volume.restrict (Icc a b))
  valueErrorMemL2 : ∀ n, MemLp
    (fun s => horizontalSlice (F n) t s - horizontalSlice u t s)
    2 (volume.restrict (Icc a b))
  gradientErrorMemL2 : ∀ n, MemLp
    (fun s => vecEuclideanNorm
      (classicalGradient (F n) (squarePoint s t) -
        g (squarePoint s t)))
    2 (volume.restrict (Icc a b))
  valueErrorTendsto : Tendsto
    (fun n => ∫ s in Icc a b,
      |horizontalSlice (F n) t s - horizontalSlice u t s| ^ 2)
    atTop (𝓝 0)
  gradientErrorTendsto : Tendsto
    (fun n => ∫ s in Icc a b,
      vecEuclideanNorm
        (classicalGradient (F n) (squarePoint s t) -
          g (squarePoint s t)) ^ 2)
    atTop (𝓝 0)

/-- The four `L²` facts on one good vertical slice. -/
structure VerticalSliceL2DataAt
    (F : ℕ → Vec 2 → ℝ) (u : Vec 2 → ℝ) (g : Vec 2 → Vec 2)
    (c d s : ℝ) : Prop where
  valueMemL2 : MemLp (verticalSlice u s) 2
    (volume.restrict (Icc c d))
  gradientMemL2 : MemLp (fun t => g (squarePoint s t) 1) 2
    (volume.restrict (Icc c d))
  valueErrorMemL2 : ∀ n, MemLp
    (fun t => verticalSlice (F n) s t - verticalSlice u s t)
    2 (volume.restrict (Icc c d))
  gradientErrorMemL2 : ∀ n, MemLp
    (fun t => vecEuclideanNorm
      (classicalGradient (F n) (squarePoint s t) -
        g (squarePoint s t)))
    2 (volume.restrict (Icc c d))

/-- The two vanishing error-energy facts on one good vertical slice. -/
structure VerticalSliceTendstoDataAt
    (F : ℕ → Vec 2 → ℝ) (u : Vec 2 → ℝ) (g : Vec 2 → Vec 2)
    (c d s : ℝ) : Prop where
  valueErrorTendsto : Tendsto
    (fun n => ∫ t in Icc c d,
      |verticalSlice (F n) s t - verticalSlice u s t| ^ 2)
    atTop (𝓝 0)
  gradientErrorTendsto : Tendsto
    (fun n => ∫ t in Icc c d,
      vecEuclideanNorm
        (classicalGradient (F n) (squarePoint s t) -
          g (squarePoint s t)) ^ 2)
    atTop (𝓝 0)

/-- The four `L²` facts on one good horizontal slice. -/
structure HorizontalSliceL2DataAt
    (F : ℕ → Vec 2 → ℝ) (u : Vec 2 → ℝ) (g : Vec 2 → Vec 2)
    (a b t : ℝ) : Prop where
  valueMemL2 : MemLp (horizontalSlice u t) 2
    (volume.restrict (Icc a b))
  gradientMemL2 : MemLp (fun s => g (squarePoint s t) 0) 2
    (volume.restrict (Icc a b))
  valueErrorMemL2 : ∀ n, MemLp
    (fun s => horizontalSlice (F n) t s - horizontalSlice u t s)
    2 (volume.restrict (Icc a b))
  gradientErrorMemL2 : ∀ n, MemLp
    (fun s => vecEuclideanNorm
      (classicalGradient (F n) (squarePoint s t) -
        g (squarePoint s t)))
    2 (volume.restrict (Icc a b))

/-- The two vanishing error-energy facts on one good horizontal slice. -/
structure HorizontalSliceTendstoDataAt
    (F : ℕ → Vec 2 → ℝ) (u : Vec 2 → ℝ) (g : Vec 2 → Vec 2)
    (a b t : ℝ) : Prop where
  valueErrorTendsto : Tendsto
    (fun n => ∫ s in Icc a b,
      |horizontalSlice (F n) t s - horizontalSlice u t s| ^ 2)
    atTop (𝓝 0)
  gradientErrorTendsto : Tendsto
    (fun n => ∫ s in Icc a b,
      vecEuclideanNorm
        (classicalGradient (F n) (squarePoint s t) -
          g (squarePoint s t)) ^ 2)
    atTop (𝓝 0)

/-- Raw value and gradient `L²` data on one vertical slice. -/
structure VerticalSliceRawL2DataAt
    (u : Vec 2 → ℝ) (g : Vec 2 → Vec 2)
    (c d s : ℝ) : Prop where
  valueMemL2 : MemLp (verticalSlice u s) 2
    (volume.restrict (Icc c d))
  gradientMemL2 : MemLp (fun t => g (squarePoint s t) 1) 2
    (volume.restrict (Icc c d))

/-- Approximation-error `L²` data on one vertical slice. -/
structure VerticalSliceErrorL2DataAt
    (F : ℕ → Vec 2 → ℝ) (u : Vec 2 → ℝ) (g : Vec 2 → Vec 2)
    (c d s : ℝ) : Prop where
  valueErrorMemL2 : ∀ n, MemLp
    (fun t => verticalSlice (F n) s t - verticalSlice u s t)
    2 (volume.restrict (Icc c d))
  gradientErrorMemL2 : ∀ n, MemLp
    (fun t => vecEuclideanNorm
      (classicalGradient (F n) (squarePoint s t) -
        g (squarePoint s t)))
    2 (volume.restrict (Icc c d))

/-- Raw value and gradient `L²` data on one horizontal slice. -/
structure HorizontalSliceRawL2DataAt
    (u : Vec 2 → ℝ) (g : Vec 2 → Vec 2)
    (a b t : ℝ) : Prop where
  valueMemL2 : MemLp (horizontalSlice u t) 2
    (volume.restrict (Icc a b))
  gradientMemL2 : MemLp (fun s => g (squarePoint s t) 0) 2
    (volume.restrict (Icc a b))

/-- Approximation-error `L²` data on one horizontal slice. -/
structure HorizontalSliceErrorL2DataAt
    (F : ℕ → Vec 2 → ℝ) (u : Vec 2 → ℝ) (g : Vec 2 → Vec 2)
    (a b t : ℝ) : Prop where
  valueErrorMemL2 : ∀ n, MemLp
    (fun s => horizontalSlice (F n) t s - horizontalSlice u t s)
    2 (volume.restrict (Icc a b))
  gradientErrorMemL2 : ∀ n, MemLp
    (fun s => vecEuclideanNorm
      (classicalGradient (F n) (squarePoint s t) -
        g (squarePoint s t)))
    2 (volume.restrict (Icc a b))

/-- Apply the one-dimensional limit theorem to one good vertical slice. -/
theorem VerticalSliceApproximationDataAt.hasVerticalNormalSliceLimit
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {c d s : ℝ}
    (h : VerticalSliceApproximationDataAt F u g c d s)
    (hcd : c < d) :
    HasVerticalNormalSliceLimit F u g c d s :=
  hasVerticalNormalSliceLimit_of_tendsto_sq_vector_error
    hcd h.smooth h.valueMemL2 h.gradientMemL2
    h.valueErrorMemL2 h.gradientErrorMemL2
    h.valueErrorTendsto h.gradientErrorTendsto

/-- Apply the one-dimensional limit theorem to one good horizontal slice. -/
theorem HorizontalSliceApproximationDataAt.hasHorizontalNormalSliceLimit
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {a b t : ℝ}
    (h : HorizontalSliceApproximationDataAt F u g a b t)
    (hab : a < b) :
    HasHorizontalNormalSliceLimit F u g a b t :=
  hasHorizontalNormalSliceLimit_of_tendsto_sq_vector_error
    hab h.smooth h.valueMemL2 h.gradientMemL2
    h.valueErrorMemL2 h.gradientErrorMemL2
    h.valueErrorTendsto h.gradientErrorTendsto

/-- Concrete global data from which the two normal-slice limit theorems are
assembled.  Every field is an explicit smoothness, `L²`, or dyadic
summability statement; the later `H¹` facade constructs this structure from
graph convergence. -/
structure AxisBoxSmoothApproximationData
    (F : ℕ → Vec 2 → ℝ) (u : Vec 2 → ℝ) (g : Vec 2 → Vec 2)
    (a b c d : ℝ) : Prop where
  smooth : ∀ n, ContDiff ℝ 1 (F n)
  valueMemL2 : MemL2On (axisBox ![a, c] ![b, d]) u
  gradientMemL2 :
    ∀ i, MemL2On (axisBox ![a, c] ![b, d]) (fun x => g x i)
  valueErrorMemL2 : ∀ n,
    MemL2On (axisBox ![a, c] ![b, d])
      (fun x => F n x - u x)
  gradientErrorMemL2 : ∀ n,
    MemL2On (axisBox ![a, c] ![b, d])
      (fun x =>
        vecEuclideanNorm (classicalGradient (F n) x - g x))
  valueErrorSummable : Summable fun n => (2 : ℝ) ^ n *
    ∫ x in axisBox ![a, c] ![b, d], (F n x - u x) ^ 2
  gradientErrorSummable : Summable fun n => (2 : ℝ) ^ n *
    ∫ x in axisBox ![a, c] ![b, d],
      vecEuclideanNorm (classicalGradient (F n) x - g x) ^ 2

/-- Almost every vertical slice carries raw value and gradient `L²` data. -/
theorem ae_verticalSliceRawL2DataAt
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {a b c d : ℝ}
    (hData : AxisBoxSmoothApproximationData F u g a b c d) :
    ∀ᵐ s ∂(volume.restrict (Ioo a b)),
      VerticalSliceRawL2DataAt u g c d s := by
  refine
    (ae_memLp_axisBox_vertical_value_and_normal_slices
      hData.valueMemL2 (hData.gradientMemL2 1)).mono ?_
  rintro s ⟨hsValue, hsGradient⟩
  exact {
    valueMemL2 := by
      simpa only [verticalSlice, restrict_Ioo_eq_restrict_Icc] using!
        hsValue
    gradientMemL2 := by
      simpa only [restrict_Ioo_eq_restrict_Icc] using hsGradient }

/-- Almost every vertical slice carries every scalar value-error `L²`
restriction. -/
theorem ae_verticalSlice_valueError_memL2
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {a b c d : ℝ}
    (hData : AxisBoxSmoothApproximationData F u g a b c d) :
    ∀ᵐ s ∂(volume.restrict (Ioo a b)), ∀ n,
      MemLp
        (fun t => verticalSlice (F n) s t - verticalSlice u s t)
        2 (volume.restrict (Icc c d)) := by
  refine (ae_all_iff.2 fun n =>
    memLp_axisBox_slice_second_ae (hData.valueErrorMemL2 n)).mono ?_
  intro s hs n
  simpa only [verticalSlice, restrict_Ioo_eq_restrict_Icc] using hs n

/-- Almost every vertical slice carries every Euclidean-gradient error `L²`
restriction. -/
theorem ae_verticalSlice_gradientError_memL2
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {a b c d : ℝ}
    (hData : AxisBoxSmoothApproximationData F u g a b c d) :
    ∀ᵐ s ∂(volume.restrict (Ioo a b)), ∀ n,
      MemLp
        (fun t => vecEuclideanNorm
          (classicalGradient (F n) (squarePoint s t) -
            g (squarePoint s t)))
        2 (volume.restrict (Icc c d)) := by
  refine (ae_all_iff.2 fun n =>
    memLp_axisBox_slice_second_ae
      (hData.gradientErrorMemL2 n)).mono ?_
  intro s hs n
  simpa only [restrict_Ioo_eq_restrict_Icc] using hs n

/-- Almost every vertical slice carries all approximation-error `L²` data. -/
theorem ae_verticalSliceErrorL2DataAt
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {a b c d : ℝ}
    (hData : AxisBoxSmoothApproximationData F u g a b c d) :
    ∀ᵐ s ∂(volume.restrict (Ioo a b)),
      VerticalSliceErrorL2DataAt F u g c d s := by
  have hValue := ae_verticalSlice_valueError_memL2 hData
  have hGradient := ae_verticalSlice_gradientError_memL2 hData
  refine (hValue.and hGradient).mono ?_
  rintro s ⟨hsValue, hsGradient⟩
  exact {
    valueErrorMemL2 := hsValue
    gradientErrorMemL2 := hsGradient }

/-- Almost every horizontal slice carries raw value and gradient `L²` data. -/
theorem ae_horizontalSliceRawL2DataAt
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {a b c d : ℝ}
    (hData : AxisBoxSmoothApproximationData F u g a b c d) :
    ∀ᵐ t ∂(volume.restrict (Ioo c d)),
      HorizontalSliceRawL2DataAt u g a b t := by
  refine
    (ae_memLp_axisBox_horizontal_value_and_normal_slices
      hData.valueMemL2 (hData.gradientMemL2 0)).mono ?_
  rintro t ⟨htValue, htGradient⟩
  exact {
    valueMemL2 := by
      simpa only [horizontalSlice, restrict_Ioo_eq_restrict_Icc] using!
        htValue
    gradientMemL2 := by
      simpa only [restrict_Ioo_eq_restrict_Icc] using htGradient }

/-- Almost every horizontal slice carries every scalar value-error `L²`
restriction. -/
theorem ae_horizontalSlice_valueError_memL2
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {a b c d : ℝ}
    (hData : AxisBoxSmoothApproximationData F u g a b c d) :
    ∀ᵐ t ∂(volume.restrict (Ioo c d)), ∀ n,
      MemLp
        (fun s => horizontalSlice (F n) t s -
          horizontalSlice u t s)
        2 (volume.restrict (Icc a b)) := by
  refine (ae_all_iff.2 fun n =>
    memLp_axisBox_slice_first_ae (hData.valueErrorMemL2 n)).mono ?_
  intro t ht n
  simpa only [horizontalSlice, restrict_Ioo_eq_restrict_Icc] using ht n

/-- Almost every horizontal slice carries every Euclidean-gradient error
`L²` restriction. -/
theorem ae_horizontalSlice_gradientError_memL2
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {a b c d : ℝ}
    (hData : AxisBoxSmoothApproximationData F u g a b c d) :
    ∀ᵐ t ∂(volume.restrict (Ioo c d)), ∀ n,
      MemLp
        (fun s => vecEuclideanNorm
          (classicalGradient (F n) (squarePoint s t) -
            g (squarePoint s t)))
        2 (volume.restrict (Icc a b)) := by
  refine (ae_all_iff.2 fun n =>
    memLp_axisBox_slice_first_ae
      (hData.gradientErrorMemL2 n)).mono ?_
  intro t ht n
  simpa only [restrict_Ioo_eq_restrict_Icc] using ht n

/-- Almost every horizontal slice carries all approximation-error `L²`
data. -/
theorem ae_horizontalSliceErrorL2DataAt
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {a b c d : ℝ}
    (hData : AxisBoxSmoothApproximationData F u g a b c d) :
    ∀ᵐ t ∂(volume.restrict (Ioo c d)),
      HorizontalSliceErrorL2DataAt F u g a b t := by
  have hValue := ae_horizontalSlice_valueError_memL2 hData
  have hGradient := ae_horizontalSlice_gradientError_memL2 hData
  refine (hValue.and hGradient).mono ?_
  rintro t ⟨htValue, htGradient⟩
  exact {
    valueErrorMemL2 := htValue
    gradientErrorMemL2 := htGradient }

/-- Almost every vertical slice carries the four required `L²` facts. -/
theorem ae_verticalSliceL2DataAt
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {a b c d : ℝ}
    (hData : AxisBoxSmoothApproximationData F u g a b c d) :
    ∀ᵐ s ∂(volume.restrict (Ioo a b)),
      VerticalSliceL2DataAt F u g c d s := by
  have hRaw := ae_verticalSliceRawL2DataAt hData
  have hError := ae_verticalSliceErrorL2DataAt hData
  refine (hRaw.and hError).mono ?_
  rintro s ⟨hsRaw, hsError⟩
  exact {
    valueMemL2 := hsRaw.valueMemL2
    gradientMemL2 := hsRaw.gradientMemL2
    valueErrorMemL2 := hsError.valueErrorMemL2
    gradientErrorMemL2 := hsError.gradientErrorMemL2 }

/-- Almost every vertical slice has vanishing value and Euclidean-gradient
error energies. -/
theorem ae_verticalSliceTendstoDataAt
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {a b c d : ℝ}
    (hData : AxisBoxSmoothApproximationData F u g a b c d) :
    ∀ᵐ s ∂(volume.restrict (Ioo a b)),
      VerticalSliceTendstoDataAt F u g c d s := by
  have hValue :=
    ae_tendsto_axisBox_slice_second_sq_of_summable_dyadic
      hData.valueErrorMemL2 hData.valueErrorSummable
  have hGradient :=
    ae_tendsto_axisBox_slice_second_sq_of_summable_dyadic
      hData.gradientErrorMemL2 hData.gradientErrorSummable
  refine (hValue.and hGradient).mono ?_
  rintro s ⟨hsValue, hsGradient⟩
  exact {
    valueErrorTendsto := by
      simpa only [verticalSlice, sq_abs] using hsValue
    gradientErrorTendsto := hsGradient }

/-- Almost every horizontal slice carries the four required `L²` facts. -/
theorem ae_horizontalSliceL2DataAt
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {a b c d : ℝ}
    (hData : AxisBoxSmoothApproximationData F u g a b c d) :
    ∀ᵐ t ∂(volume.restrict (Ioo c d)),
      HorizontalSliceL2DataAt F u g a b t := by
  have hRaw := ae_horizontalSliceRawL2DataAt hData
  have hError := ae_horizontalSliceErrorL2DataAt hData
  refine (hRaw.and hError).mono ?_
  rintro t ⟨htRaw, htError⟩
  exact {
    valueMemL2 := htRaw.valueMemL2
    gradientMemL2 := htRaw.gradientMemL2
    valueErrorMemL2 := htError.valueErrorMemL2
    gradientErrorMemL2 := htError.gradientErrorMemL2 }

/-- Almost every horizontal slice has vanishing value and Euclidean-gradient
error energies. -/
theorem ae_horizontalSliceTendstoDataAt
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {a b c d : ℝ}
    (hData : AxisBoxSmoothApproximationData F u g a b c d) :
    ∀ᵐ t ∂(volume.restrict (Ioo c d)),
      HorizontalSliceTendstoDataAt F u g a b t := by
  have hValue :=
    ae_tendsto_axisBox_slice_first_sq_of_summable_dyadic
      hData.valueErrorMemL2 hData.valueErrorSummable
  have hGradient :=
    ae_tendsto_axisBox_slice_first_sq_of_summable_dyadic
      hData.gradientErrorMemL2 hData.gradientErrorSummable
  refine (hValue.and hGradient).mono ?_
  rintro t ⟨htValue, htGradient⟩
  exact {
    valueErrorTendsto := by
      simpa only [horizontalSlice, sq_abs] using htValue
    gradientErrorTendsto := htGradient }

/-- A common smooth planar approximation with dyadically summable value and
Euclidean-gradient errors supplies all one-dimensional limit data on almost
every vertical slice. -/
theorem ae_verticalSliceApproximationDataAt_of_summable_dyadic_error
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {a b c d : ℝ}
    (hData : AxisBoxSmoothApproximationData F u g a b c d) :
    ∀ᵐ s ∂(volume.restrict (Ioo a b)),
      VerticalSliceApproximationDataAt F u g c d s := by
  have hL2 := ae_verticalSliceL2DataAt hData
  have hTendsto := ae_verticalSliceTendstoDataAt hData
  refine (hL2.and hTendsto).mono ?_
  rintro s ⟨hsL2, hsTendsto⟩
  exact {
    smooth := hData.smooth
    valueMemL2 := hsL2.valueMemL2
    gradientMemL2 := hsL2.gradientMemL2
    valueErrorMemL2 := hsL2.valueErrorMemL2
    gradientErrorMemL2 := hsL2.gradientErrorMemL2
    valueErrorTendsto := hsTendsto.valueErrorTendsto
    gradientErrorTendsto := hsTendsto.gradientErrorTendsto }

/-- A common smooth planar approximation with dyadically summable value and
Euclidean-gradient errors determines a canonical continuous weak
representative on almost every vertical slice. -/
theorem ae_hasVerticalNormalSliceLimit_of_summable_dyadic_error
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {a b c d : ℝ}
    (hcd : c < d)
    (hData : AxisBoxSmoothApproximationData F u g a b c d) :
    ∀ᵐ s ∂(volume.restrict (Ioo a b)),
      HasVerticalNormalSliceLimit F u g c d s :=
  (ae_verticalSliceApproximationDataAt_of_summable_dyadic_error hData).mono
    fun _ hs => hs.hasVerticalNormalSliceLimit hcd

/-- A common smooth planar approximation with dyadically summable value and
Euclidean-gradient errors determines a canonical continuous weak
representative on almost every horizontal slice. -/
theorem ae_horizontalSliceApproximationDataAt_of_summable_dyadic_error
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {a b c d : ℝ}
    (hData : AxisBoxSmoothApproximationData F u g a b c d) :
    ∀ᵐ t ∂(volume.restrict (Ioo c d)),
      HorizontalSliceApproximationDataAt F u g a b t := by
  have hL2 := ae_horizontalSliceL2DataAt hData
  have hTendsto := ae_horizontalSliceTendstoDataAt hData
  refine (hL2.and hTendsto).mono ?_
  rintro t ⟨htL2, htTendsto⟩
  exact {
    smooth := hData.smooth
    valueMemL2 := htL2.valueMemL2
    gradientMemL2 := htL2.gradientMemL2
    valueErrorMemL2 := htL2.valueErrorMemL2
    gradientErrorMemL2 := htL2.gradientErrorMemL2
    valueErrorTendsto := htTendsto.valueErrorTendsto
    gradientErrorTendsto := htTendsto.gradientErrorTendsto }

/-- A common smooth planar approximation with dyadically summable value and
Euclidean-gradient errors determines a canonical continuous weak
representative on almost every horizontal slice. -/
theorem ae_hasHorizontalNormalSliceLimit_of_summable_dyadic_error
    {F : ℕ → Vec 2 → ℝ} {u : Vec 2 → ℝ} {g : Vec 2 → Vec 2}
    {a b c d : ℝ}
    (hab : a < b)
    (hData : AxisBoxSmoothApproximationData F u g a b c d) :
    ∀ᵐ t ∂(volume.restrict (Ioo c d)),
      HasHorizontalNormalSliceLimit F u g a b t :=
  (ae_horizontalSliceApproximationDataAt_of_summable_dyadic_error hData).mono
    fun _ ht => ht.hasHorizontalNormalSliceLimit hab

namespace H1Function

/-- A representative-level `H¹` function on a planar axis box has genuine
`L²` value slices and genuine `L²` second-coordinate gradient slices on
almost every vertical line.  Coordinate `1` is the slice-direction derivative
candidate for the scalar parameter `t` on that line. -/
theorem ae_memLp_vertical_value_and_normal_slices
    {a b c d : ℝ} (u : H1Function (axisBox ![a, c] ![b, d])) :
    ∀ᵐ s ∂(volume.restrict (Ioo a b)),
      MemLp (fun t => u.toFun (squarePoint s t)) 2
          (volume.restrict (Ioo c d)) ∧
        MemLp (fun t => u.grad (squarePoint s t) 1) 2
          (volume.restrict (Ioo c d)) :=
  ae_memLp_axisBox_vertical_value_and_normal_slices u.memL2
    (u.grad_memL2 1)

/-- A representative-level `H¹` function on a planar axis box has genuine
`L²` value slices and genuine `L²` first-coordinate gradient slices on
almost every horizontal line.  Coordinate `0` is the slice-direction
derivative candidate for the scalar parameter `s` on that line. -/
theorem ae_memLp_horizontal_value_and_normal_slices
    {a b c d : ℝ} (u : H1Function (axisBox ![a, c] ![b, d])) :
    ∀ᵐ t ∂(volume.restrict (Ioo c d)),
      MemLp (fun s => u.toFun (squarePoint s t)) 2
          (volume.restrict (Ioo a b)) ∧
        MemLp (fun s => u.grad (squarePoint s t) 0) 2
          (volume.restrict (Ioo a b)) :=
  ae_memLp_axisBox_horizontal_value_and_normal_slices u.memL2
    (u.grad_memL2 0)

end H1Function

end

end PDE
