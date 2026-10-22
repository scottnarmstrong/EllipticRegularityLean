module

public import PDEFoundation.Analysis.Newtonian.WeakType.DecompositionStopping
public import PDEFoundation.Measure.FiniteVectorMean

/-! # The good and bad parts of the Calderón–Zygmund decomposition

Given stopping cubes `Q_k` (`CZStopping`), the good part `g` equals `F` off `⋃ Q_k` and the
vector average `⨍_{Q_k} F` on `Q_k`; the bad parts are `b_k = (F - ⨍_{Q_k} F) 1_{Q_k}`.
This file proves the pointwise identity `F = g + ∑ b_k`, the `L^∞` bound for `g`, and the
mean-zero, integrability and support properties of `b_k`.
-/

@[expose] public section

open BoxIntegral MeasureTheory Set Filter
open scoped ENNReal Topology Function

namespace PDE.NewtonWeakType

noncomputable section

variable {d : ℕ} {I : Box (Fin d)} {F : Vec d → Vec d} {lam : ℝ}

/-- The vector average of `F` over the `k`-th stopping cube. -/
def czAvg (S : CZStopping I F lam) (k : S.ι) : Vec d :=
  coordinateVectorAverage (S.cube k : Set (Vec d)) F

open Classical in
/-- The good part of the decomposition. -/
def czGood (S : CZStopping I F lam) (x : Vec d) : Vec d :=
  if h : ∃ k, x ∈ (S.cube k : Set (Vec d)) then czAvg S h.choose else F x

/-- The `k`-th bad part of the decomposition. -/
def czBad (S : CZStopping I F lam) (k : S.ι) (x : Vec d) : Vec d :=
  (S.cube k : Set (Vec d)).indicator (fun x => F x - czAvg S k) x

variable (S : CZStopping I F lam)

theorem czCube_subset_root (k : S.ι) : (S.cube k : Set (Vec d)) ⊆ (I : Set (Vec d)) :=
  fun _ hx => S.le_root k hx

theorem czCube_volume_toReal_pos (k : S.ι) : 0 < (volume (S.cube k : Set (Vec d))).toReal :=
  volume_box_toReal_pos _

theorem czCube_volume_lt_top (k : S.ι) : volume (S.cube k : Set (Vec d)) < ⊤ :=
  (S.cube k).measure_coe_lt_top volume

theorem czGood_of_mem {k : S.ι} {x : Vec d} (hx : x ∈ (S.cube k : Set (Vec d))) :
    czGood S x = czAvg S k := by
  have h : ∃ k, x ∈ (S.cube k : Set (Vec d)) := ⟨k, hx⟩
  unfold czGood
  simp only [h, ↓reduceDIte]
  have hk := h.choose_spec
  have : h.choose = k := by
    by_contra hne
    exact Set.disjoint_left.mp (S.pairwise_disjoint hne) hk hx
  rw [this]

theorem czGood_of_notMem {x : Vec d} (h : ∀ k, x ∉ (S.cube k : Set (Vec d))) :
    czGood S x = F x := by
  unfold czGood
  simp only [not_exists.mpr h, ↓reduceDIte]

theorem czBad_of_mem {k : S.ι} {x : Vec d} (hx : x ∈ (S.cube k : Set (Vec d))) :
    czBad S k x = F x - czAvg S k := by
  simp only [czBad, Set.indicator_of_mem hx]

theorem czBad_of_notMem {k : S.ι} {x : Vec d} (hx : x ∉ (S.cube k : Set (Vec d))) :
    czBad S k x = 0 := by
  simp only [czBad, Set.indicator_of_notMem hx]

/-- Support of a bad part. -/
theorem czBad_support_subset (k : S.ι) :
    Function.support (czBad S k) ⊆ closure (S.cube k : Set (Vec d)) := by
  intro x hx
  by_contra hxc
  exact hx (czBad_of_notMem S (fun h => hxc (subset_closure h)))

/-- Pointwise summation of the bad parts. -/
theorem hasSum_czBad (x : Vec d) : HasSum (fun k => czBad S k x) (F x - czGood S x) := by
  by_cases h : ∃ k, x ∈ (S.cube k : Set (Vec d))
  · obtain ⟨k, hk⟩ := h
    have hz : ∀ k', k' ≠ k → czBad S k' x = 0 := fun k' hk' =>
      czBad_of_notMem S (fun hx' => Set.disjoint_left.mp (S.pairwise_disjoint hk') hx' hk)
    have := hasSum_single k hz
    rw [czBad_of_mem S hk] at this
    rwa [czGood_of_mem S hk]
  · have hn : ∀ k, x ∉ (S.cube k : Set (Vec d)) := not_exists.mp h
    rw [czGood_of_notMem S hn, sub_self]
    have : (fun k => czBad S k x) = fun _ => 0 := funext fun k => czBad_of_notMem S (hn k)
    rw [this]
    exact hasSum_zero

/-- **The decomposition `F = g + ∑ b_k`**, valid at every point. -/
theorem eq_czGood_add_tsum_czBad (x : Vec d) :
    F x = czGood S x + ∑' k, czBad S k x := by
  rw [(hasSum_czBad S x).tsum_eq]
  abel

variable {S}

theorem czAvg_apply (k : S.ι) (i : Fin d) :
    czAvg S k i = (volume (S.cube k : Set (Vec d))).toReal⁻¹ *
      ∫ x in (S.cube k : Set (Vec d)), F x i := rfl

/-- The Euclidean norm of the vector average is at most the average of the Euclidean norm. -/
theorem vecEuclideanNorm_czAvg_le (hF : ∀ i, IntegrableOn (fun x => F x i) (I : Set (Vec d)))
    (k : S.ι) :
    vecEuclideanNorm (czAvg S k) ≤
      integralAverage (S.cube k : Set (Vec d)) (fun x => vecEuclideanNorm (F x)) := by
  set Q : Set (Vec d) := (S.cube k : Set (Vec d)) with hQ
  have hc : 0 ≤ (volume Q).toReal⁻¹ := inv_nonneg.mpr (czCube_volume_toReal_pos S k).le
  have hsmul : czAvg S k = (volume Q).toReal⁻¹ • (fun i => ∫ x in Q, F x i) := by
    ext i
    simp [czAvg_apply, hQ]
  rw [hsmul, vecEuclideanNorm_smul, abs_of_nonneg hc]
  unfold integralAverage
  refine mul_le_mul_of_nonneg_left ?_ hc
  exact vecEuclideanNorm_integral_le_integral_vecEuclideanNorm (μ := volume.restrict Q) F
    (fun i => (hF i).mono_set (czCube_subset_root S k))

/-- The good part is bounded by `2^d λ` almost everywhere on the root box. -/
theorem ae_vecEuclideanNorm_czGood_le
    (hF : ∀ i, IntegrableOn (fun x => F x i) (I : Set (Vec d))) :
    ∀ᵐ x ∂(volume : Measure (Vec d)),
      x ∈ (I : Set (Vec d)) → vecEuclideanNorm (czGood S x) ≤ 2 ^ d * lam := by
  filter_upwards [S.ae_le] with x hx hxI
  by_cases h : ∃ k, x ∈ (S.cube k : Set (Vec d))
  · obtain ⟨k, hk⟩ := h
    rw [czGood_of_mem S hk]
    exact (vecEuclideanNorm_czAvg_le hF k).trans (S.avg_le k)
  · have hn : ∀ k, x ∉ (S.cube k : Set (Vec d)) := not_exists.mp h
    rw [czGood_of_notMem S hn]
    exact (hx hxI hn).trans
      (le_mul_of_one_le_left S.lam_pos.le (one_le_pow₀ (by norm_num)))

theorem czBad_coord_eq_indicator (k : S.ι) (i : Fin d) :
    (fun x => czBad S k x i) =
      (S.cube k : Set (Vec d)).indicator (fun x => F x i - czAvg S k i) := by
  funext x
  by_cases hx : x ∈ (S.cube k : Set (Vec d))
  · simp [czBad, Set.indicator_of_mem hx]
  · simp [czBad, Set.indicator_of_notMem hx]

/-- Each coordinate of a bad part is integrable. -/
theorem integrable_czBad_coord (hF : ∀ i, IntegrableOn (fun x => F x i) (I : Set (Vec d)))
    (k : S.ι) (i : Fin d) : Integrable (fun x => czBad S k x i) := by
  rw [czBad_coord_eq_indicator]
  exact (((hF i).mono_set (czCube_subset_root S k)).sub
    (integrableOn_const (czCube_volume_lt_top S k).ne)).integrable_indicator
    (S.cube k).measurableSet_coe

/-- Each bad part has mean zero. -/
theorem integral_czBad_coord (hF : ∀ i, IntegrableOn (fun x => F x i) (I : Set (Vec d)))
    (k : S.ι) (i : Fin d) : ∫ x, czBad S k x i = 0 := by
  rw [czBad_coord_eq_indicator, integral_indicator (S.cube k).measurableSet_coe,
    integral_sub ((hF i).mono_set (czCube_subset_root S k))
      (integrableOn_const (czCube_volume_lt_top S k).ne), setIntegral_const, czAvg_apply]
  have hpos := czCube_volume_toReal_pos S k
  simp only [Measure.real, smul_eq_mul]
  field_simp
  ring

end

end PDE.NewtonWeakType
