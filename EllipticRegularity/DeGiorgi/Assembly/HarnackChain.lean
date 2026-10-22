module

public import EllipticRegularity.DeGiorgi.Assembly.EssContinuous
public import PDEFoundation.Geometry.EuclideanBall.Interior

/-!
# The chaining step of the Harnack inequality

A local Harnack inequality on the balls `B_{1/16}(x)`, `x ∈ B_{1/2}`, propagates along the
segment `y, x₁, …, x₁₇ = z` in `B_{1/2}` at the price of the factor `K^17`.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.DGNMAssembly

open MeasureTheory

variable {d : ℕ}

theorem vecEuclideanNorm_sub_le (x y : Vec d) :
    vecEuclideanNorm (x - y) ≤ vecEuclideanNorm x + vecEuclideanNorm y := by
  have := vecEuclideanNorm_add_le x (-y)
  rwa [vecEuclideanNorm_neg, ← sub_eq_add_neg] at this

theorem chain_bound {v : Vec d → ℝ} {K : ℝ} (hK : 0 < K)
    (hloc : ∀ x₀ ∈ euclideanBall (0 : Vec d) (1 / 2),
      ∀ y ∈ euclideanBall x₀ (1 / 16) ∩ euclideanBall (0 : Vec d) (1 / 2),
      ∀ z ∈ euclideanBall x₀ (1 / 16) ∩ euclideanBall (0 : Vec d) (1 / 2), v y ≤ K * v z)
    {y z : Vec d} (hy : y ∈ euclideanBall (0 : Vec d) (1 / 2))
    (hz : z ∈ euclideanBall (0 : Vec d) (1 / 2)) :
    v y ≤ K ^ 17 * v z := by
  set x : ℕ → Vec d := fun i => y + ((i : ℝ) / 17) • (z - y) with hx
  have hxmem : ∀ i : ℕ, i ≤ 17 → x i ∈ euclideanBall (0 : Vec d) (1 / 2) := by
    intro i hi
    have ht : ((i : ℝ) / 17) ∈ Set.Icc (0 : ℝ) 1 := by
      refine ⟨by positivity, ?_⟩
      rw [div_le_one (by norm_num)]
      exact_mod_cast hi
    exact (convex_euclideanBall (0 : Vec d) (1 / 2)).add_smul_sub_mem hy hz ht
  have hdist : vecEuclideanNorm (z - y) < 1 := by
    have h1 := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp hy
    have h2 := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp hz
    simp only [sub_zero] at h1 h2
    linarith [vecEuclideanNorm_sub_le z y]
  have hstep : ∀ i : ℕ, i < 17 → x (i + 1) ∈ euclideanBall (x i) (1 / 16) := by
    intro i _
    rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)]
    have : x (i + 1) - x i = (1 / 17 : ℝ) • (z - y) := by
      simp only [hx]
      ext j
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    rw [this, vecEuclideanNorm_smul, abs_of_pos (by norm_num)]
    nlinarith [vecEuclideanNorm_nonneg (z - y)]
  have hind : ∀ i : ℕ, i ≤ 17 → v y ≤ K ^ i * v (x i) := by
    intro i
    induction i with
    | zero =>
      intro _
      simp [hx]
    | succ n ih =>
      intro hn
      have hn' : n ≤ 17 := by omega
      have hlt : n < 17 := by omega
      have h1 := ih hn'
      have h2 : v (x n) ≤ K * v (x (n + 1)) :=
        hloc (x n) (hxmem n hn') (x n)
          ⟨center_mem_euclideanBall _ (by norm_num), hxmem n hn'⟩ (x (n + 1))
          ⟨hstep n hlt, hxmem (n + 1) hn⟩
      calc v y ≤ K ^ n * v (x n) := h1
        _ ≤ K ^ n * (K * v (x (n + 1))) := by gcongr
        _ = K ^ (n + 1) * v (x (n + 1)) := by ring
  have h17 := hind 17 le_rfl
  have hx17 : x 17 = z := by
    simp only [hx]
    ext j
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  rwa [hx17] at h17

end PDE.DGNMAssembly
