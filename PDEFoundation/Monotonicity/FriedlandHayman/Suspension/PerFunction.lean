module

public import PDEFoundation.Monotonicity.FriedlandHayman.Suspension.Limit
public import PDEFoundation.Monotonicity.FriedlandHayman.Suspension.Measure

/-!
# Friedland--Hayman: the eigenvalue bound from a single test function

If `f` is a test function of `Ω ⊆ S^{n-1}` with Rayleigh quotient `a (a + n - 2)`, then the first
Dirichlet eigenvalue of the suspension of `Ω` in dimension `n + N` is at most `a (a + n + N - 2)`.
-/

@[expose] public section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace PDE.FHLane

noncomputable section

namespace Susp

theorem rayleigh_limit_algebra {N : ℕ} {n : ℕ} (hn : 2 ≤ n) {a I P Q A : ℝ} (hA : 0 < A)
    (hI : 0 < I) (hQ : 0 < Q) (hrel : ((n : ℝ) + 2 * a - 3 + N + 1) * Q =
      ((n : ℝ) + 2 * a - 3 + 1) * P) :
    A * (a ^ 2 * I * (P - Q) + a * (a + ((n : ℝ) - 2)) * I * P) / (A * I * Q) =
      a * (a + (((n + N - 2 : ℕ)) : ℝ)) := by
  have hcast : (((n + N - 2 : ℕ)) : ℝ) = (n : ℝ) + N - 2 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hcast, div_eq_iff (by positivity)]
  linear_combination (-(A * I * a)) * hrel

theorem eigenvalue_suspension_le_of_test {n N : ℕ} [NeZero n] [NeZero N] (hn : 2 ≤ n)
    {Ω : Set (Vec n)} {f : Vec n → ℝ} (hf : ContDiff ℝ 1 f)
    (hfΩ : closure {x | x ∈ euclideanSphere (0 : Vec n) 1 ∧ f x ≠ 0} ⊆ Ω)
    (hI : 0 < sphereIntegral (0 : Vec n) 1 (fun x => f x ^ 2)) {a : ℝ} (ha : 0 ≤ a)
    (hJ : sphereIntegral (0 : Vec n) 1 (tangentialGradientNormSq f) =
      a * (a + ((n : ℝ) - 2)) * sphereIntegral (0 : Vec n) 1 (fun x => f x ^ 2))
    (hpos : 0 < (n : ℝ) + 2 * a - 2) :
    sphereDirichletEigenvalue (n + N) (suspension n N Ω) ≤
      ENNReal.ofReal (a * (a + (((n + N - 2 : ℕ)) : ℝ))) := by
  set I := sphereIntegral (0 : Vec n) 1 (fun x => f x ^ 2) with hI_def
  set J := sphereIntegral (0 : Vec n) 1 (tangentialGradientNormSq f) with hJ_def
  have hn1 : 1 ≤ n := by omega
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hJ0 : 0 ≤ J := by rw [hJ]; have : 0 ≤ a + ((n : ℝ) - 2) := by linarith
                         positivity
  have hp : -1 < (n : ℝ) + 2 * a - 3 := by linarith
  have hp2 : -1 < (n : ℝ) + 2 * a - 3 + 2 := by linarith
  set P := sinCos N ((n : ℝ) + 2 * a - 3) with hP
  set Q := sinCos N ((n : ℝ) + 2 * a - 3 + 2) with hQ
  have hPpos : 0 < P := sinCos_pos N hp
  have hQpos : 0 < Q := sinCos_pos N hp2
  have hrel := sinCos_add_two (N := N) (NeZero.pos N) hp
  have hareaN : 0 < sphereArea N := sphereArea_pos
  -- limits of numerator and denominator
  have hnum := (tendsto_integral_numInt (N := N) (a := a) (I := I) (J := J) hn1 ha hp hI.le hJ0).const_mul
    (sphereArea N)
  have hden := (tendsto_integral_denInt (N := N) (a := a) (I := I) (J := J) hn1 hp hI.le hJ0).const_mul
    (sphereArea N)
  rw [integral_numLim hn1 hp] at hnum
  rw [integral_denLim hn1] at hden
  have hDlim : 0 < sphereArea N * (I * Q) := by positivity
  have hquot := hnum.div hden hDlim.ne'
  have hlim : sphereArea N * (a ^ 2 * I * (P - Q) + J * P) / (sphereArea N * (I * Q)) =
      a * (a + (((n + N - 2 : ℕ)) : ℝ)) := by
    rw [hJ, ← rayleigh_limit_algebra (N := N) hn hareaN hI hQpos hrel]
    ring
  rw [hlim] at hquot
  have hDpos : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      sphereArea N * (I * Q) / 2 < sphereArea N * ∫ θ in (0 : ℝ)..(Real.pi / 2), denInt n N a I ε θ :=
    hden.eventually (lt_mem_nhds (by linarith))
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), sphereDirichletEigenvalue (n + N) (suspension n N Ω) ≤
      ENNReal.ofReal (sphereArea N * (∫ θ in (0 : ℝ)..(Real.pi / 2), numInt n N a I J ε θ) /
        (sphereArea N * ∫ θ in (0 : ℝ)..(Real.pi / 2), denInt n N a I ε θ)) := by
    filter_upwards [self_mem_nhdsWithin, hDpos] with ε hε hD
    have hε' : (0 : ℝ) < ε := hε
    have hDen := denominator_cutLift (N := N) (a := a) hε' hf
    have hNum := numerator_cutLift (N := N) (a := a) hε' hf
    have hposD : 0 < sphereIntegral (0 : Vec (n + N)) 1 (fun x => cutLift (N := N) ε a f x ^ 2) := by
      rw [hDen]; exact lt_trans (by positivity) hD
    unfold sphereDirichletEigenvalue
    refine iInf₂_le_of_le (cutLift (N := N) ε a f)
      ⟨contDiff_cutLift hε' hf,
        closure_support_subset_suspension hε' (fun t ht => radProf_eq_zero hε' ht) hfΩ, hposD⟩ ?_
    rw [hNum, hDen]
  exact ge_of_tendsto (ENNReal.tendsto_ofReal hquot) hev

end Susp

end

end PDE.FHLane
