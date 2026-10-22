module

public import PDEFoundation.FunctionalInequalities.Campanato.Averages
public import PDEFoundation.Regularity.Holder
public import PDEFoundation.Geometry.EuclideanBall

/-!
# Campanato quantity of a Hölder function

Part (2) of the Campanato characterisation: a function with a Hölder representative on the unit
ball has mean oscillation `⨍_{B_r(x)} |u - (u)_{B_r(x)}| ≤ 2^α K r ^ α`.
-/

@[expose] public section

namespace PDE.CampanatoProof

open MeasureTheory

variable {d : ℕ}

/-- An average of a function bounded by a constant is bounded by that constant. -/
theorem integralAverage_le_const {A : Set (Vec d)} (hA : MeasurableSet A) {g : Vec d → ℝ}
    {c : ℝ} (hg : IntegrableOn g A) (hpos : 0 < volume A) (hfin : volume A ≠ ⊤)
    (hbd : ∀ z ∈ A, g z ≤ c) : integralAverage A g ≤ c := by
  have hv : 0 < (volume A).toReal := ENNReal.toReal_pos hpos.ne' hfin
  have h1 : ∫ z in A, g z ∂volume ≤ ∫ z in A, c ∂volume :=
    setIntegral_mono_on hg (integrableOn_const hfin) hA hbd
  rw [setIntegral_const] at h1
  unfold integralAverage
  calc (volume A).toReal⁻¹ * ∫ z in A, g z ∂volume
      ≤ (volume A).toReal⁻¹ * ((volume A).toReal • c) :=
        mul_le_mul_of_nonneg_left h1 (inv_pos.mpr hv).le
    _ = c := by rw [smul_eq_mul]; field_simp

theorem euclideanBall_subset_unit {x : Vec d} {r : ℝ} (hx : x ∈ euclideanBall (0 : Vec d) (1 / 2))
    (hr : r < 1 / 4) (hr0 : 0 < r) : euclideanBall x r ⊆ euclideanBall (0 : Vec d) 1 := by
  intro y hy
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hr0] at hy
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)] at hx ⊢
  have : y - 0 = (y - x) + (x - 0) := by abel
  rw [this]
  exact lt_of_le_of_lt (vecEuclideanNorm_add_le _ _) (by linarith)

theorem vecEuclideanNorm_sub_lt_two_mul {x y z : Vec d} {r : ℝ} (hr : 0 < r)
    (hy : y ∈ euclideanBall x r) (hz : z ∈ euclideanBall x r) :
    vecEuclideanNorm (y - z) < 2 * r := by
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt hr] at hy hz
  have : y - z = (y - x) + (x - z) := by abel
  rw [this]
  have := vecEuclideanNorm_sub_comm z x
  have h2 := vecEuclideanNorm_add_le (y - x) (x - z)
  rw [vecEuclideanNorm_sub_comm x z] at h2
  linarith

/-- Mean oscillation of a function with a Hölder bound on a round ball. -/
theorem integralAverage_abs_sub_le_of_holder {x : Vec d} {r α K : ℝ} (hr : 0 < r) (hα : 0 < α)
    {v : Vec d → ℝ} (hv : IntegrableOn v (euclideanBall x r))
    (hH : ∀ y ∈ euclideanBall x r, ∀ z ∈ euclideanBall x r,
      |v y - v z| ≤ K * vecEuclideanNorm (y - z) ^ α) (hK : 0 ≤ K) :
    integralAverage (euclideanBall x r)
        (fun y => |v y - integralAverage (euclideanBall x r) v|) ≤ K * (2 * r) ^ α := by
  have hpos := volume_euclideanBall_pos x hr
  have hfin := volume_euclideanBall_ne_top x hr.le
  have hm := measurableSet_euclideanBall x r
  have hpt : ∀ y ∈ euclideanBall x r, ∀ z ∈ euclideanBall x r,
      |v z - v y| ≤ K * (2 * r) ^ α := by
    intro y hy z hz
    refine (hH z hz y hy).trans (mul_le_mul_of_nonneg_left ?_ hK)
    exact Real.rpow_le_rpow (vecEuclideanNorm_nonneg _)
      (vecEuclideanNorm_sub_lt_two_mul hr hz hy).le hα.le
  refine integralAverage_le_const hm ((hv.sub (integrableOn_const hfin)).abs) hpos hfin ?_
  intro y hy
  have h1 := abs_integralAverage_sub_le (A := euclideanBall x r) (g := v) (v y) hv hpos hfin
  have h2 : integralAverage (euclideanBall x r) (fun z => |v z - v y|) ≤ K * (2 * r) ^ α :=
    integralAverage_le_const hm ((hv.sub (integrableOn_const hfin)).abs) hpos hfin
      (fun z hz => hpt y hy z hz)
  rw [abs_sub_comm]
  exact h1.trans h2

/-- Part (2) of the Campanato characterisation. -/
theorem campanato_quantity_le_of_holder {α K : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (hK : 0 ≤ K)
    {u : Vec d → ℝ} (hu : IntegrableOn u (euclideanBall (0 : Vec d) 1))
    (h : HasEuclideanHolderRepresentativeOn (euclideanBall (0 : Vec d) 1) u α K)
    {x : Vec d} (hx : x ∈ euclideanBall (0 : Vec d) (1 / 2)) {r : ℝ} (hr : 0 < r)
    (hr4 : r < 1 / 4) :
    r ^ (-α) * integralAverage (euclideanBall x r)
      (fun y => |u y - integralAverage (euclideanBall x r) u|) ≤ 2 * K := by
  obtain ⟨v, hae, hH⟩ := h
  have hsub := euclideanBall_subset_unit hx hr4 hr
  have haeB : v =ᵐ[volumeOn (euclideanBall x r)] u :=
    ae_restrict_of_ae_restrict_of_subset hsub hae
  have hvint : IntegrableOn v (euclideanBall x r) :=
    ((hu.mono_set hsub).congr_fun_ae haeB.symm)
  have havg : integralAverage (euclideanBall x r) u = integralAverage (euclideanBall x r) v :=
    (integralAverage_congr_ae haeB).symm
  have hosc : integralAverage (euclideanBall x r)
      (fun y => |u y - integralAverage (euclideanBall x r) u|) =
      integralAverage (euclideanBall x r)
      (fun y => |v y - integralAverage (euclideanBall x r) v|) := by
    rw [havg]
    refine integralAverage_congr_ae ?_
    filter_upwards [haeB] with y hy
    rw [hy]
  rw [hosc]
  have hbound := integralAverage_abs_sub_le_of_holder hr hα hvint
    (fun y hy z hz => hH y (hsub hy) z (hsub hz)) hK
  have hrα : 0 < r ^ α := Real.rpow_pos_of_pos hr α
  calc r ^ (-α) * _ ≤ r ^ (-α) * (K * (2 * r) ^ α) :=
        mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hr.le _)
    _ = K * (2 : ℝ) ^ α := by
        rw [Real.mul_rpow (by norm_num) hr.le, Real.rpow_neg hr.le]
        field_simp
    _ ≤ K * 2 := by
        refine mul_le_mul_of_nonneg_left ?_ hK
        calc (2 : ℝ) ^ α ≤ 2 ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hα1
          _ = 2 := Real.rpow_one 2
    _ = 2 * K := by ring

end PDE.CampanatoProof
