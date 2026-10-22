module

public import PDEFoundation.Monotonicity.ACF.AssemblySingle
public import PDEFoundation.Monotonicity.ACF.AssemblyMono

/-!
# ACF-A: the Alt--Caffarelli--Friedman formula from Friedland--Hayman

`PDE.alt_caffarelli_friedman_of_friedlandHayman` is the statement
`PDE.alt_caffarelli_friedman` with one extra hypothesis `hFH`, the statement
`PDE.friedland_hayman_of_disjoint` (for this `d`).  Route: for a.e. `r`, AM--GM turns the weighted
bound and the slice Rayleigh bound into `2 α_± J_± ≤ r J_±'`; Friedland--Hayman gives
`α₊ + α₋ ≥ 2`; hence `(r⁻⁴ J₊ J₋)' ≥ 0` a.e., and absolute continuity of `J_±` gives monotonicity.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE

namespace ACFAssembly

noncomputable section

variable {d : ℕ}

theorem two_le_of_ofReal_add {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : (2 : ℝ≥0∞) ≤ ENNReal.ofReal a + ENNReal.ofReal b) : 2 ≤ a + b := by
  have h2 : ENNReal.ofReal 2 ≤ ENNReal.ofReal (a + b) := by
    rw [ENNReal.ofReal_add ha hb]; simpa using h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2

end

end ACFAssembly

open ACFAssembly in
/-- **Alt--Caffarelli--Friedman monotonicity formula, conditional on Friedland--Hayman.**  The
statement of `PDE.alt_caffarelli_friedman` with the extra hypothesis `hFH`, the statement of
`PDE.friedland_hayman_of_disjoint` for this `d`. -/
theorem alt_caffarelli_friedman_of_friedlandHayman (d : ℕ) (hd : 3 ≤ d) (R : ℝ) (hR : 0 < R)
    (up um : H1Function (euclideanBall (0 : Vec d) R))
    (hup_cont : ContinuousOn up.toFun (euclideanBall (0 : Vec d) R))
    (hum_cont : ContinuousOn um.toFun (euclideanBall (0 : Vec d) R))
    (hup_nonneg : ∀ x ∈ euclideanBall (0 : Vec d) R, 0 ≤ up.toFun x)
    (hum_nonneg : ∀ x ∈ euclideanBall (0 : Vec d) R, 0 ≤ um.toFun x)
    (hup_sub : IsWeakDivergenceFormSubharmonicOn (fun _ => (1 : Mat d))
      (euclideanBall (0 : Vec d) R) up)
    (hum_sub : IsWeakDivergenceFormSubharmonicOn (fun _ => (1 : Mat d))
      (euclideanBall (0 : Vec d) R) um)
    (hup0 : up.toFun 0 = 0) (hum0 : um.toFun 0 = 0)
    (hdisj : ∀ x ∈ euclideanBall (0 : Vec d) R, up.toFun x * um.toFun x = 0)
    (hFH : 2 ≤ d → ∀ (Ωp Ωm : Set (Vec d)),
      (∃ U : Set (Vec d), IsOpen U ∧ Ωp = U ∩ euclideanSphere (0 : Vec d) 1) →
      (∃ U : Set (Vec d), IsOpen U ∧ Ωm = U ∩ euclideanSphere (0 : Vec d) 1) →
      Disjoint Ωp Ωm →
      2 ≤ eigenvalueDegree d (sphereDirichletEigenvalue d Ωp) +
        eigenvalueDegree d (sphereDirichletEigenvalue d Ωm)) :
    MonotoneOn (acfFunctional up.grad um.grad) (Set.Ioo 0 R) ∧
      ∀ r ∈ Set.Ioo 0 R, acfFunctional up.grad um.grad r ≠ ⊤ := by
  have _ := hup0
  have _ := hum0
  have hd2 : 2 ≤ d := by omega
  set Jp : ℝ → ℝ := fun r => ∫ ρ in (0 : ℝ)..r, dens up.grad ρ with hJp
  set Jm : ℝ → ℝ := fun r => ∫ ρ in (0 : ℝ)..r, dens um.grad ρ with hJm
  have hEp : ∀ r ∈ Ioo (0 : ℝ) R, acfWeightedEnergy up.grad r = ENNReal.ofReal (Jp r) :=
    fun r hr => (single_energy hd up hup_cont hup_nonneg hup_sub hr).1
  have hEm : ∀ r ∈ Ioo (0 : ℝ) R, acfWeightedEnergy um.grad r = ENNReal.ofReal (Jm r) :=
    fun r hr => (single_energy hd um hum_cont hum_nonneg hum_sub hr).1
  have hJp0 : ∀ r ∈ Ioo (0 : ℝ) R, 0 ≤ Jp r := fun r hr =>
    intervalIntegral.integral_nonneg hr.1.le fun ρ hρ => dens_nonneg _ hρ.1
  have hJm0 : ∀ r ∈ Ioo (0 : ℝ) R, 0 ≤ Jm r := fun r hr =>
    intervalIntegral.integral_nonneg hr.1.le fun ρ hρ => dens_nonneg _ hρ.1
  have hF : ∀ r ∈ Ioo (0 : ℝ) R, acfFunctional up.grad um.grad r =
      ENNReal.ofReal ((r ^ 4)⁻¹ * (Jp r * Jm r)) := by
    intro r hr
    rw [acfFunctional_eq_mul, hEp r hr, hEm r hr, ← ENNReal.ofReal_mul (hJp0 r hr),
      ← ENNReal.ofReal_mul (by positivity), inv_pow]
  have hmono : MonotoneOn (fun r : ℝ => (r ^ 4)⁻¹ * (Jp r * Jm r)) (Ioo 0 R) := by
    refine monotoneOn_inv_pow_four_mul (jp := dens up.grad) (jm := dens um.grad)
      (fun t ht0 htR => (single_energy hd up hup_cont hup_nonneg hup_sub ⟨ht0, htR⟩).2)
      (fun t ht0 htR => (single_energy hd um hum_cont hum_nonneg hum_sub ⟨ht0, htR⟩).2) ?_
    rw [← ae_restrict_iff' measurableSet_Ioo]
    filter_upwards [single_ae hd hR up hup_cont hup_nonneg hup_sub,
      single_ae hd hR um hum_cont hum_nonneg hum_sub,
      ae_restrict_mem measurableSet_Ioo] with r hp hm hr
    have hjp : 0 ≤ dens up.grad r := dens_nonneg _ hr.1.le
    have hjm : 0 ≤ dens um.grad r := dens_nonneg _ hr.1.le
    have h1 := hJp0 r hr
    have h2 := hJm0 r hr
    show 4 * (Jp r * Jm r) ≤ r * (dens up.grad r * Jm r + Jp r * dens um.grad r)
    rcases h1.eq_or_lt with h1' | h1'
    · rw [← h1']
      have := mul_nonneg hr.1.le (mul_nonneg hjp h2)
      nlinarith only [this]
    rcases h2.eq_or_lt with h2' | h2'
    · rw [← h2']
      have := mul_nonneg hr.1.le (mul_nonneg h1 hjm)
      nlinarith only [this]
    obtain ⟨tp, htp, hdp, hap⟩ := hp h1'
    obtain ⟨tm, htm, hdm, ham⟩ := hm h2'
    have hsum : 2 ≤ tp + tm := by
      refine two_le_of_ofReal_add htp htm ?_
      rw [← hdp, ← hdm]
      obtain ⟨Up, hUp, hUpeq⟩ := single_openSlice up hup_cont hr
      obtain ⟨Um, hUm, hUmeq⟩ := single_openSlice um hum_cont hr
      have hdj : Disjoint ({y | 0 < up.toFun (r • y)} ∩ euclideanSphere (0 : Vec d) 1)
          ({y | 0 < um.toFun (r • y)} ∩ euclideanSphere (0 : Vec d) 1) := by
        refine Set.disjoint_left.2 fun y hy1 hy2 => ?_
        have hb := smul_mem_ball_of_mem_sphere hr.1.le hr.2 hy1.2
        have := hdisj _ hb
        have h3 : 0 < up.toFun (r • y) * um.toFun (r • y) := mul_pos hy1.1 hy2.1
        linarith
      have key := hFH hd2 _ _ ⟨Up, hUp, hUpeq⟩ ⟨Um, hUm, hUmeq⟩ hdj
      rw [← sphereDirichletEigenvalue_congr_inter (Ω := {y | 0 < up.toFun (r • y)})
          (Ω' := {y | 0 < up.toFun (r • y)} ∩ euclideanSphere (0 : Vec d) 1)
          (by rw [inter_assoc, inter_self]),
        ← sphereDirichletEigenvalue_congr_inter (Ω := {y | 0 < um.toFun (r • y)})
          (Ω' := {y | 0 < um.toFun (r • y)} ∩ euclideanSphere (0 : Vec d) 1)
          (by rw [inter_assoc, inter_self])] at key
      exact key
    have e1 := mul_le_mul_of_nonneg_right hap h2
    have e2 := mul_le_mul_of_nonneg_left ham h1
    have e3 := mul_nonneg (sub_nonneg.2 hsum) (mul_nonneg h1 h2)
    nlinarith only [e1, e2, e3]
  refine ⟨?_, ?_⟩
  · intro s hs t ht hst
    rw [hF s hs, hF t ht]
    exact ENNReal.ofReal_le_ofReal (hmono hs ht hst)
  · intro r hr
    rw [hF r hr]
    exact ENNReal.ofReal_ne_top

end PDE
