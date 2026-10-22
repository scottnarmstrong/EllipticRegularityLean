module

public import PDEFoundation.Sobolev.Trace.Chart.Defs
public import PDEFoundation.Geometry.EuclideanBall

/-!
# Elementary facts about graph chart maps

The chart map `Ψ(x', t) = insertNth i (γ x' + sgn t) x'` is a `C¹` diffeomorphism with explicit
inverse, preserves Lebesgue measure (a shear followed by a coordinate insertion), and its
coordinates `succAbove i` are those of `x'`; this gives the two distance comparisons used for the
surface measure.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set

variable {n : ℕ} {i : Fin (n + 1)} {γ : Vec n → ℝ} {sgn L : ℝ}

theorem graphMapInv_graphMap (hs : sgn ^ 2 = 1) (z : Vec n × ℝ) :
    graphMapInv i γ sgn (graphMap i γ sgn z) = z := by
  obtain ⟨x, t⟩ := z
  simp only [graphMapInv, graphMap, Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  refine Prod.ext rfl ?_
  simp only
  have : sgn * (γ x + sgn * t - γ x) = sgn ^ 2 * t := by ring
  rw [this, hs, one_mul]

theorem graphMap_graphMapInv (hs : sgn ^ 2 = 1) (x : Vec (n + 1)) :
    graphMap i γ sgn (graphMapInv i γ sgn x) = x := by
  have h : γ (fun j => x (i.succAbove j)) + sgn * (sgn * (x i - γ fun j => x (i.succAbove j))) =
      x i := by
    have : sgn * (sgn * (x i - γ fun j => x (i.succAbove j))) =
        sgn ^ 2 * (x i - γ fun j => x (i.succAbove j)) := by ring
    rw [this, hs]; ring
  simp only [graphMap, graphMapInv, h]
  exact Fin.insertNth_self_removeNth i x

theorem contDiff_graphMap (hγ : ContDiff ℝ 1 γ) : ContDiff ℝ 1 (graphMap i γ sgn) := by
  refine contDiff_pi.2 fun j => ?_
  refine Fin.succAboveCases i ?_ ?_ j
  · simp only [graphMap, Fin.insertNth_apply_same]
    exact (hγ.comp contDiff_fst).add (contDiff_const.mul contDiff_snd)
  · intro k
    simp only [graphMap, Fin.insertNth_apply_succAbove]
    exact (contDiff_apply ℝ ℝ k).comp contDiff_fst

theorem contDiff_graphMapInv (hγ : ContDiff ℝ 1 γ) : ContDiff ℝ 1 (graphMapInv i γ sgn) := by
  have h1 : ContDiff ℝ 1 fun x : Vec (n + 1) => fun j => x (i.succAbove j) :=
    contDiff_pi.2 fun j => contDiff_apply ℝ ℝ _
  refine h1.prodMk (contDiff_const.mul ((contDiff_apply ℝ ℝ i).sub (hγ.comp h1)))

theorem measurePreserving_graphMap (hs : sgn ^ 2 = 1) (hγ : Measurable γ) :
    MeasurePreserving (graphMap i γ sgn) (volume.prod volume) volume := by
  have hsg : sgn ≠ 0 := by rintro rfl; norm_num at hs
  have habs : |sgn⁻¹| = 1 := by
    have : |sgn| = 1 := by
      have := sq_abs sgn; rw [hs] at this
      nlinarith [abs_nonneg sgn]
    rw [abs_inv, this]; simp
  have shear : MeasurePreserving (fun p : Vec n × ℝ => (p.1, γ p.1 + sgn * p.2))
      (volume.prod volume) (volume.prod volume) := by
    refine MeasurePreserving.skew_product (g := fun x t => γ x + sgn * t)
      (MeasurePreserving.id _) ?_ (Filter.Eventually.of_forall fun x => ?_)
    · exact (hγ.comp measurable_fst).add (measurable_const.mul measurable_snd)
    · have h1 : Measure.map (fun t : ℝ => sgn * t) volume = volume := by
        rw [Real.map_volume_mul_left hsg, habs]; simp
      have : (fun t : ℝ => γ x + sgn * t) = (fun u => γ x + u) ∘ (fun t => sgn * t) := rfl
      rw [this, ← Measure.map_map (measurable_const_add _) (measurable_const_mul _), h1]
      exact (measurePreserving_add_left volume (γ x)).map_eq
  have swap : MeasurePreserving (Prod.swap : Vec n × ℝ → ℝ × Vec n)
      (volume.prod volume) (volume.prod volume) := Measure.measurePreserving_swap
  have ins : MeasurePreserving (fun p : ℝ × Vec n => Fin.insertNth (α := fun _ => ℝ) i p.1 p.2)
      (volume.prod volume) volume := by
    have := (measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => (volume : Measure ℝ)) i).symm
    rw [← volume_pi] at this
    exact this
  have := ins.comp (swap.comp shear)
  have hfun : graphMap i γ sgn =
      (fun p : ℝ × Vec n => Fin.insertNth (α := fun _ => ℝ) i p.1 p.2) ∘ Prod.swap ∘
        fun p : Vec n × ℝ => (p.1, γ p.1 + sgn * p.2) := rfl
  rw [hfun]
  exact this

theorem vecEuclideanNorm_sub_le_graphMap (z w : Vec n × ℝ) :
    vecEuclideanNorm (z.1 - w.1) ≤
      vecEuclideanNorm (graphMap i γ sgn z - graphMap i γ sgn w) := by
  unfold vecEuclideanNorm
  apply Real.sqrt_le_sqrt
  simp only [vecNormSq_eq_sum_sq]
  rw [Fin.sum_univ_succAbove _ i]
  simp only [Pi.sub_apply, graphMap, Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same]
  exact le_add_of_nonneg_left (sq_nonneg _)

theorem vecEuclideanNorm_graphMap_zero_sub_le
    (hγ : ∀ x' y', |γ x' - γ y'| ≤ L * vecEuclideanNorm (x' - y')) (x' y' : Vec n) :
    vecEuclideanNorm (graphMap i γ sgn (x', 0) - graphMap i γ sgn (y', 0)) ≤
      Real.sqrt (1 + L ^ 2) * vecEuclideanNorm (x' - y') := by
  have hL := hγ x' y'
  have hn := vecEuclideanNorm_nonneg (x' - y')
  rw [← Real.sqrt_sq hn, ← Real.sqrt_mul (by positivity)]
  conv_lhs => unfold vecEuclideanNorm
  apply Real.sqrt_le_sqrt
  simp only [vecNormSq_eq_sum_sq]
  rw [Fin.sum_univ_succAbove _ i]
  simp only [Pi.sub_apply, graphMap, Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same,
    mul_zero, add_zero]
  have hsq : (∑ j, (x' j - y' j) ^ 2) = vecEuclideanNorm (x' - y') ^ 2 := by
    rw [vecEuclideanNorm_sq, vecNormSq_eq_sum_sq]; rfl
  rw [hsq]
  have : (γ x' - γ y') ^ 2 ≤ (L * vecEuclideanNorm (x' - y')) ^ 2 := sq_le_sq' (by
    linarith [abs_le.1 hL]) (abs_le.1 hL).2
  nlinarith

end PDE.TraceLane
