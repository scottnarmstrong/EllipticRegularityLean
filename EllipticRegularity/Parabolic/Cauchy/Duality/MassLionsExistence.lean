module

public import EllipticRegularity.Parabolic.Cauchy.Lions.ExistenceAssembly
public import EllipticRegularity.Parabolic.Cauchy.LionsRep.RepresentativeSolution
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

set_option autoImplicit false

namespace PDE.Parabolic.Duality

open MeasureTheory Set Filter Topology

noncomputable def cauchyMassDataCutoff {d : ℕ} (f : Vec d → ℝ) (n : ℕ) : Vec d → ℝ :=
  (euclideanClosedBall (0 : Vec d) ((n : ℝ) + 1)).indicator f

/-- Ball truncations of an `L¹ ∩ L²` datum retain both norms and converge in `L¹`. -/
theorem cauchyMassDataCutoff_properties {d : ℕ} (f : Vec d → ℝ)
    (hf1 : Integrable f volume) (hf2 : MemLp f 2 volume) :
    (∀ n, Integrable (cauchyMassDataCutoff f n) volume) ∧
    (∀ n, MemLp (cauchyMassDataCutoff f n) 2 volume) ∧
    (∀ n, ∃ S : ℝ, 0 ≤ S ∧
      ∀ x ∉ euclideanClosedBall (0 : Vec d) S, cauchyMassDataCutoff f n x = 0) ∧
    Tendsto (fun n => eLpNorm (cauchyMassDataCutoff f n - f) 1 volume)
      atTop (𝓝 0) := by
  have hK (n : ℕ) : MeasurableSet (euclideanClosedBall (0 : Vec d) ((n : ℝ) + 1)) :=
    measurableSet_euclideanClosedBall 0 ((n : ℝ) + 1)
  have hInt (n : ℕ) : Integrable (cauchyMassDataCutoff f n) volume := by
    rw [cauchyMassDataCutoff, integrable_indicator_iff (hK n)]
    exact hf1.restrict
  have hMem (n : ℕ) : MemLp (cauchyMassDataCutoff f n) 2 volume := by
    rw [cauchyMassDataCutoff, memLp_indicator_iff_restrict (hK n)]
    exact hf2.restrict (euclideanClosedBall (0 : Vec d) ((n : ℝ) + 1))
  have hSupport (n : ℕ) : ∃ S : ℝ, 0 ≤ S ∧
      ∀ x ∉ euclideanClosedBall (0 : Vec d) S, cauchyMassDataCutoff f n x = 0 := by
    refine ⟨(n : ℝ) + 1, by positivity, ?_⟩
    intro x hx
    simp [cauchyMassDataCutoff, hx]
  have hPoint (x : Vec d) : ∀ᶠ n : ℕ in atTop,
      cauchyMassDataCutoff f n x = f x := by
    obtain ⟨N, hN⟩ := exists_nat_gt (vecEuclideanNorm x)
    filter_upwards [eventually_ge_atTop N] with n hn
    have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
    have hx : x ∈ euclideanClosedBall (0 : Vec d) ((n : ℝ) + 1) := by
      rw [mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)]
      rw [sub_zero]
      linarith
    simp [cauchyMassDataCutoff, hx]
  have hBound (n : ℕ) : ∀ᵐ x : Vec d ∂volume,
      ‖cauchyMassDataCutoff f n x - f x‖ ≤ ‖f x‖ := by
    filter_upwards [] with x
    by_cases hx : x ∈ euclideanClosedBall (0 : Vec d) ((n : ℝ) + 1)
    · simp [cauchyMassDataCutoff, hx]
    · simp [cauchyMassDataCutoff, hx]
  have hBound' (n : ℕ) : ∀ᵐ x : Vec d ∂volume,
      ‖‖cauchyMassDataCutoff f n x - f x‖‖ ≤ ‖f x‖ := by
    filter_upwards [hBound n] with x hx
    simpa using hx
  have hNormTendsto : Tendsto (fun n =>
      ∫ x : Vec d, ‖cauchyMassDataCutoff f n x - f x‖) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence
      (fun x : Vec d => ‖f x‖)
      (fun n => (hInt n).sub hf1 |>.norm.aestronglyMeasurable)
      hf1.norm hBound'
      (Filter.Eventually.of_forall fun x => by
        have heq : (fun n : ℕ => ‖cauchyMassDataCutoff f n x - f x‖) =ᶠ[atTop]
            fun _ => (0 : ℝ) := by
          filter_upwards [hPoint x] with n hn
          simp [hn]
        exact tendsto_const_nhds.congr' heq.symm)
    simpa using h
  have hLpTendsto : Tendsto
      (fun n => ENNReal.ofReal (∫ x : Vec d,
        ‖cauchyMassDataCutoff f n x - f x‖)) atTop (𝓝 0) := by
    simpa using ENNReal.tendsto_ofReal hNormTendsto
  have hApprox : Tendsto
      (fun n => eLpNorm (cauchyMassDataCutoff f n - f) 1 volume)
      atTop (𝓝 0) := by
    have hEq (n : ℕ) : eLpNorm (cauchyMassDataCutoff f n - f) 1 volume =
        ENNReal.ofReal (∫ x : Vec d,
          ‖cauchyMassDataCutoff f n x - f x‖) := by
      rw [MemLp.eLpNorm_eq_integral_rpow_norm one_ne_zero ENNReal.one_ne_top
        (memLp_one_iff_integrable.mpr ((hInt n).sub hf1))]
      simp
    simpa only [hEq] using hLpTendsto
  exact ⟨hInt, hMem, hSupport, hApprox⟩

/-- The Lions construction, its global slice bound, and the all-time representative assemble a
weak Cauchy solution for every spatial `L²` datum. -/
theorem exists_cauchy_solution_from_lions {d : ℕ} {lam Lam s T : ℝ}
    {a : ParCoeffField d} (hsT : s < T)
    (ha : IsParabolicCoeff lam Lam a univ (Icc s T))
    (f : Vec d → ℝ) (hf : MemLp f 2 volume) :
    ∃ u : ParH1Function (univ : Set (Vec d)) (Icc s T),
      IsCauchySolution a s T f u := by
  obtain ⟨v, v₀, hclose, hrep, _, _, _, _⟩ :=
    PDE.Parabolic.Lions.exists_cauchy_lions_energyFields hsT ha f hf
  have hglobal := PDE.Parabolic.Lions.cauchyEnergyValue_ae_slice_norm_bound
    hsT ha f hf v hclose hrep
  exact PDE.Parabolic.LionsRep.exists_cauchy_energy_solution_of_globalSliceBound
    hsT ha f hf v hclose hrep hglobal

end PDE.Parabolic.Duality
