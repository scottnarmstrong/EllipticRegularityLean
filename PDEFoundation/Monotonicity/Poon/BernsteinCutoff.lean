module

public import PDEFoundation.Monotonicity.Poon.BernsteinIdentity
public import PDEFoundation.Ambient.EuclideanNorm

/-!
# The polynomial cutoff for the Bernstein argument

`Z(t, x) = 1 - c |x - x₀|²` and the weight `a = Z² (t - t₀)`, with their joint derivatives.
-/

@[expose] public section

open Set Filter
open scoped Topology

namespace PDE

noncomputable section

variable {d : ℕ}

/-- Squared distance to `x₀` on the joint space. -/
def jDistSq (x₀ : Vec d) : ℝ × Vec d → ℝ := fun q => ∑ i : Fin d, (q.2 i - x₀ i) * (q.2 i - x₀ i)

/-- The cutoff `1 - c |x - x₀|²`. -/
def jCutZ (x₀ : Vec d) (c : ℝ) : ℝ × Vec d → ℝ := fun q => 1 - c * jDistSq x₀ q

/-- The weight `Z² (t - t₀)`. -/
def jCutA (x₀ : Vec d) (t₀ c : ℝ) : ℝ × Vec d → ℝ :=
  fun q => (jCutZ x₀ c q * jCutZ x₀ c q) * (q.1 - t₀)

theorem jsm_coord (x₀ : Vec d) (i : Fin d) :
    JSm (Set.univ : Set (ℝ × Vec d)) (fun q => q.2 i - x₀ i) :=
  (ContDiff.sub (by fun_prop) contDiff_const).contDiffOn

theorem jsm_time (t₀ : ℝ) :
    JSm (Set.univ : Set (ℝ × Vec d)) (fun q => q.1 - t₀) :=
  (ContDiff.sub contDiff_fst contDiff_const).contDiffOn

theorem jsm_distSq (x₀ : Vec d) : JSm (Set.univ : Set (ℝ × Vec d)) (jDistSq x₀) :=
  ContDiffOn.sum fun i _ => (jsm_coord x₀ i).mul (jsm_coord x₀ i)

theorem jsm_cutZ (x₀ : Vec d) (c : ℝ) : JSm (Set.univ : Set (ℝ × Vec d)) (jCutZ x₀ c) :=
  contDiffOn_const.sub (contDiffOn_const.mul (jsm_distSq x₀))

theorem jsm_cutA (x₀ : Vec d) (t₀ c : ℝ) : JSm (Set.univ : Set (ℝ × Vec d)) (jCutA x₀ t₀ c) :=
  ((jsm_cutZ x₀ c).mul (jsm_cutZ x₀ c)).mul (jsm_time t₀)

theorem jd_coord (x₀ : Vec d) (u : ℝ × Vec d) (i : Fin d) (q : ℝ × Vec d) :
    jd u (fun q => q.2 i - x₀ i) q = u.2 i := by
  have h1 : HasFDerivAt (fun q : ℝ × Vec d => q.2 i)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin d => ℝ) i).comp
        (ContinuousLinearMap.snd ℝ ℝ (Vec d))) q :=
    HasFDerivAt.comp (g := fun y : Vec d => y i) (f := fun q : ℝ × Vec d => q.2) q
      (hasFDerivAt_apply i q.2) hasFDerivAt_snd
  have h := h1.sub_const (x₀ i)
  simp [jd, h.fderiv]

theorem jd_time (t₀ : ℝ) (u : ℝ × Vec d) (q : ℝ × Vec d) :
    jd u (fun q => q.1 - t₀) q = u.1 := by
  have h : HasFDerivAt (fun q : ℝ × Vec d => q.1 - t₀) (ContinuousLinearMap.fst ℝ ℝ (Vec d)) q :=
    (hasFDerivAt_fst).sub_const _
  simp [jd, h.fderiv]

section Values

variable (x₀ : Vec d) (t₀ c : ℝ)

theorem jd_distSq (u : ℝ × Vec d) (q : ℝ × Vec d) :
    jd u (jDistSq x₀) q = ∑ i : Fin d, 2 * (q.2 i - x₀ i) * u.2 i := by
  unfold jDistSq
  rw [jd_sum Finset.univ isOpen_univ u (fun i _ => (jsm_coord x₀ i).mul (jsm_coord x₀ i))
    (Set.mem_univ q)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [jd_mul isOpen_univ u (jsm_coord x₀ i) (jsm_coord x₀ i) (Set.mem_univ q), jd_coord]
  ring

theorem jd_cutZ (u : ℝ × Vec d) (q : ℝ × Vec d) :
    jd u (jCutZ x₀ c) q = -(c * ∑ i : Fin d, 2 * (q.2 i - x₀ i) * u.2 i) := by
  have h1 := jd_sub isOpen_univ u (f := fun _ => (1 : ℝ)) (g := fun q => c * jDistSq x₀ q)
    contDiffOn_const (contDiffOn_const.mul (jsm_distSq x₀)) (Set.mem_univ q)
  have h2 := jd_const_mul isOpen_univ u c (jsm_distSq x₀) (Set.mem_univ q)
  change jd u (fun q => (fun _ => (1 : ℝ)) q - (fun q => c * jDistSq x₀ q) q) q = _
  rw [h1, h2, jd_const, jd_distSq]
  ring

theorem jEt_cutZ (q : ℝ × Vec d) : jEt (jCutZ x₀ c) q = 0 := by
  unfold jEt
  rw [jd_cutZ]
  simp

theorem jEx_cutZ (k : Fin d) (q : ℝ × Vec d) :
    jEx k (jCutZ x₀ c) q = -2 * c * (q.2 k - x₀ k) := by
  unfold jEx
  rw [jd_cutZ]
  simp [basisVec_apply]
  ring

theorem jLap_cutZ (q : ℝ × Vec d) : jLap (jCutZ x₀ c) q = -2 * c * d := by
  unfold jLap
  have h : ∀ k : Fin d, jEx k (jEx k (jCutZ x₀ c)) q = -2 * c := by
    intro k
    have e : jEx k (jCutZ x₀ c) = fun q => (-2 * c) * (q.2 k - x₀ k) := by
      funext q; rw [jEx_cutZ]
    rw [e]
    unfold jEx
    rw [jd_const_mul isOpen_univ _ _ (jsm_coord x₀ k) (Set.mem_univ q), jd_coord]
    simp [basisVec_apply]
  simp [h]
  ring

theorem jsm_cutZsq : JSm (Set.univ : Set (ℝ × Vec d)) (fun q => jCutZ x₀ c q * jCutZ x₀ c q) :=
  (jsm_cutZ x₀ c).mul (jsm_cutZ x₀ c)

theorem jd_cutZsq (u : ℝ × Vec d) (q : ℝ × Vec d) :
    jd u (fun q => jCutZ x₀ c q * jCutZ x₀ c q) q = 2 * (jCutZ x₀ c q * jd u (jCutZ x₀ c) q) := by
  rw [jd_mul isOpen_univ u (jsm_cutZ x₀ c) (jsm_cutZ x₀ c) (Set.mem_univ q)]
  ring

theorem jEt_cutA (q : ℝ × Vec d) : jEt (jCutA x₀ t₀ c) q = jCutZ x₀ c q * jCutZ x₀ c q := by
  have h := jd_mul isOpen_univ ((1 : ℝ), (0 : Vec d)) (jsm_cutZsq x₀ c) (jsm_time t₀)
    (Set.mem_univ q)
  unfold jEt jCutA
  rw [h, jd_time, jd_cutZsq]
  have := jEt_cutZ x₀ c q
  unfold jEt at this
  rw [this]
  ring

theorem jEx_cutA (k : Fin d) (q : ℝ × Vec d) :
    jEx k (jCutA x₀ t₀ c) q =
      (q.1 - t₀) * (2 * jCutZ x₀ c q * (-2 * c * (q.2 k - x₀ k))) := by
  have h := jd_mul isOpen_univ (0, basisVec k) (jsm_cutZsq x₀ c) (jsm_time t₀) (Set.mem_univ q)
  unfold jEx jCutA
  rw [h, jd_time, jd_cutZsq]
  have := jEx_cutZ x₀ c k q
  unfold jEx at this
  rw [this]
  dsimp only
  ring

theorem jLap_cutA (q : ℝ × Vec d) :
    jLap (jCutA x₀ t₀ c) q = (q.1 - t₀) * (2 * jCutZ x₀ c q * (-2 * c * d) +
      2 * ∑ k : Fin d, (-2 * c * (q.2 k - x₀ k)) * (-2 * c * (q.2 k - x₀ k))) := by
  have h := jLap_mul isOpen_univ (jsm_cutZsq x₀ c) (jsm_time t₀) (Set.mem_univ q)
  have h2 := jLap_mul isOpen_univ (jsm_cutZ x₀ c) (jsm_cutZ x₀ c) (Set.mem_univ q)
  have hτ : jLap (fun q : ℝ × Vec d => q.1 - t₀) q = 0 := by
    unfold jLap jEx
    have e : ∀ k : Fin d, jd (0, basisVec k) (fun q : ℝ × Vec d => q.1 - t₀) = fun _ => 0 := by
      intro k; funext q; rw [jd_time]
    simp [e, jd]
  have hτk : ∀ k : Fin d, jEx k (fun q : ℝ × Vec d => q.1 - t₀) q = 0 := by
    intro k; unfold jEx; rw [jd_time]
  have hZ : ∀ k : Fin d, jEx k (jCutZ x₀ c) q = -2 * c * (q.2 k - x₀ k) :=
    fun k => jEx_cutZ x₀ c k q
  unfold jCutA
  rw [h, hτ]
  simp only [hτk, mul_zero, Finset.sum_const_zero, add_zero, zero_add]
  rw [h2, jLap_cutZ]
  simp only [hZ]
  ring

end Values

end

end PDE
