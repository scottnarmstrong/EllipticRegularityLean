module

public import PDEFoundation.FunctionalInequalities.Campanato.Left

/-!
# The Hölder representative of a Campanato function

Assembly of part (1) of the Campanato characterisation.
-/

@[expose] public section

namespace PDE.CampanatoProof

open MeasureTheory Filter Topology

variable {d : ℕ}

theorem vecEuclideanNorm_sub_lt_one_of_mem_half {y z : Vec d}
    (hy : y ∈ euclideanBall (0 : Vec d) (1 / 2)) (hz : z ∈ euclideanBall (0 : Vec d) (1 / 2)) :
    vecEuclideanNorm (y - z) < 1 := by
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)] at hy hz
  have h1 : y - z = (y - 0) + (0 - z) := by abel
  have h2 := vecEuclideanNorm_add_le (y - 0) (0 - z)
  have h3 := vecEuclideanNorm_sub_comm 0 z
  rw [← h1] at h2
  linarith

/-- Part (1) of the Campanato characterisation, with the explicit constant `96 * 2 ^ d`. -/
theorem exists_holder_representative_of_campanato {α K : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hK : 0 ≤ K) {u : Vec d → ℝ} (hu : IntegrableOn u (euclideanBall (0 : Vec d) 1))
    (hA : ∀ x ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ r : ℝ, 0 < r → r < 1 / 4 →
      r ^ (-α) * integralAverage (euclideanBall x r)
        (fun y => |u y - integralAverage (euclideanBall x r) u|) ≤ K) :
    HasEuclideanHolderRepresentativeOn (euclideanBall (0 : Vec d) (1 / 2)) u α
      (96 * 2 ^ d * α⁻¹ * K) := by
  have key : ∀ x ∈ euclideanBall (0 : Vec d) (1 / 2), ∃ L : ℝ,
      Tendsto (fun n => integralAverage (euclideanBall x (dyadicScale n)) u) atTop (𝓝 L) ∧
      ∀ ρ : ℝ, 0 < ρ → ρ < 1 / 4 →
        |L - integralAverage (euclideanBall x ρ) u| ≤
          2 ^ d * K * ρ ^ α / (1 - (2 : ℝ) ^ (-α)) :=
    fun x hx => exists_pointLimit hα hK hu hA hx
  choose! v hvT hvB using key
  refine ⟨v, ?_, ?_⟩
  · -- almost-everywhere agreement via Lebesgue differentiation
    have hu0 : Integrable ((euclideanBall (0 : Vec d) 1).indicator u) volume :=
      hu.integrable_indicator (measurableSet_euclideanBall _ _)
    refine (ae_restrict_iff' (measurableSet_euclideanBall _ _)).2 ?_
    filter_upwards [ae_tendsto_integralAverage_euclideanBall hu0.locallyIntegrable] with x hx hxB
    have hxB1 : x ∈ euclideanBall (0 : Vec d) 1 :=
      euclideanBall_mono (by norm_num) (by norm_num) hxB
    have hev : (fun ρ : ℝ => integralAverage (euclideanBall x ρ)
        ((euclideanBall (0 : Vec d) 1).indicator u)) =ᶠ[𝓝[>] 0]
        fun ρ => integralAverage (euclideanBall x ρ) u := by
      filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 / 4 by norm_num)] with ρ hρ
      unfold integralAverage
      congr 1
      refine setIntegral_congr_fun (measurableSet_euclideanBall _ _) fun w hw => ?_
      exact Set.indicator_of_mem (euclideanBall_subset_unit hxB hρ.2 hρ.1 hw) u
    rw [Set.indicator_of_mem hxB1] at hx
    have hlim := (hx.congr' hev).comp tendsto_dyadicScale
    exact tendsto_nhds_unique (hvT x hxB) hlim
  · intro y hy z hz
    have hconv := convex_euclideanBall (0 : Vec d) (1 / 2)
    have hH0 : 0 ≤ 12 * 2 ^ d * K / α := by positivity
    have P0 : ∀ y ∈ euclideanBall (0 : Vec d) (1 / 2), ∀ z ∈ euclideanBall (0 : Vec d) (1 / 2),
        vecEuclideanNorm (y - z) < 1 / 8 →
        |v y - v z| ≤ (12 * 2 ^ d * K / α) * vecEuclideanNorm (y - z) ^ α := fun y hy z hz hδ =>
      local_holder hα hα1 hK hu hA (fun x hx ρ hρ hρ4 => hvB x hx ρ hρ hρ4) hy hz hδ
    have P1 := holder_double hconv hα hH0 P0
    have P2 := holder_double hconv hα (by positivity) P1
    have P3 := holder_double hconv hα (by positivity) P2
    have h := P3 y hy z hz (by
      have := vecEuclideanNorm_sub_lt_one_of_mem_half hy hz
      linarith)
    refine h.trans (le_of_eq ?_)
    congr 1
    field_simp
    ring

end PDE.CampanatoProof
