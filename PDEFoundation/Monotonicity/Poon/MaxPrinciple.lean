module

public import PDEFoundation.Geometry.EuclideanBall.Topology
public import PDEFoundation.Sobolev.ClassicalLaplacian
import PDEFoundation.Monotonicity.Poon.MaxPrincipleLine

/-!
# Weak maximum principle for the heat operator on compact cylinders

For `w : ℝ → Vec d → ℝ` (time first) of class `C²` jointly near the cylinder
`Q = [t₀, t₁] × B̄_ρ(x₀)` with `∂_t w - Δ w ≤ 0` on `Q`, the supremum of `w` over `Q` is attained on the
parabolic boundary: the bottom `t = t₀` or the lateral boundary `|x - x₀| = ρ`.
-/

@[expose] public section

open Filter Set
open scoped Topology

namespace PDE

noncomputable section

variable {d : ℕ}

/-- **Weak maximum principle** for the heat operator on a compact cylinder. -/
theorem parabolic_weak_max_principle (w : ℝ → Vec d → ℝ) {U : Set (ℝ × Vec d)}
    (hU : IsOpen U) (hw : ContDiffOn ℝ 2 (fun p : ℝ × Vec d => w p.1 p.2) U)
    {x₀ : Vec d} {ρ t₀ t₁ : ℝ} (ht : t₀ ≤ t₁)
    (hcyl : Icc t₀ t₁ ×ˢ euclideanClosedBall x₀ ρ ⊆ U)
    (hsub : ∀ t ∈ Icc t₀ t₁, ∀ x ∈ euclideanClosedBall x₀ ρ,
      deriv (fun τ : ℝ => w τ x) t - euclideanCoordLaplacian (w t) x ≤ 0) :
    ∃ t ∈ Icc t₀ t₁, ∃ x ∈ euclideanClosedBall x₀ ρ,
      (t = t₀ ∨ x ∈ euclideanSphere x₀ ρ) ∧
      ∀ s ∈ Icc t₀ t₁, ∀ y ∈ euclideanClosedBall x₀ ρ, w s y ≤ w t x := by
  classical
  set F : ℝ × Vec d → ℝ := fun p => w p.1 p.2 with hF
  set K : Set (ℝ × Vec d) := Icc t₀ t₁ ×ˢ euclideanClosedBall x₀ ρ with hK
  have hball : euclideanClosedBall x₀ ρ = euclideanClosedBall x₀ |ρ| := by
    ext x; simp [euclideanClosedBall, sq_abs]
  have hKc : IsCompact K :=
    isCompact_Icc.prod (hball ▸ isCompact_euclideanClosedBall x₀ (abs_nonneg ρ))
  have hFc : ContinuousOn F K := hw.continuousOn.mono hcyl
  set B : Set (ℝ × Vec d) := K ∩ ({p | p.1 = t₀} ∪ {p | p.2 ∈ euclideanSphere x₀ ρ}) with hB
  have hBc : IsCompact B := by
    refine hKc.inter_right ?_
    exact (isClosed_eq continuous_fst continuous_const).union
      ((isClosed_euclideanSphere x₀ ρ).preimage continuous_snd)
  have hB0 : (t₀, x₀) ∈ B := by
    refine ⟨⟨⟨le_rfl, ht⟩, ?_⟩, Or.inl rfl⟩
    simp [euclideanClosedBall]
    positivity
  obtain ⟨pB, hpB, hpBmax⟩ := hBc.exists_isMaxOn ⟨_, hB0⟩ (hFc.mono inter_subset_left)
  have key : ∀ ε : ℝ, 0 < ε → ∀ q ∈ K, F q ≤ F pB + ε * (t₁ - t₀) := by
    intro ε hε q hq
    set φ : ℝ × Vec d → ℝ := fun p => F p - ε * (p.1 - t₀) with hφ
    have hφc : ContinuousOn φ K :=
      hFc.sub ((continuousOn_const.mul (continuous_fst.continuousOn.sub continuousOn_const)))
    obtain ⟨m, hmK, hmmax⟩ := hKc.exists_isMaxOn ⟨q, hq⟩ hφc
    have hmB : m ∈ B := by
      by_contra hmB
      obtain ⟨t', x'⟩ := m
      obtain ⟨⟨ht'K, hx'K⟩, hnot⟩ : (t' ∈ Icc t₀ t₁ ∧ x' ∈ euclideanClosedBall x₀ ρ) ∧
          ¬ (t' = t₀ ∨ x' ∈ euclideanSphere x₀ ρ) :=
        ⟨hmK, fun h => hmB ⟨hmK, h⟩⟩
      replace hnot := not_or.1 hnot
      have ht'0 : t₀ < t' := lt_of_le_of_ne ht'K.1 (Ne.symm hnot.1)
      have hx'lt : x' ∈ euclideanBall x₀ ρ := by
        have h1 : euclideanSqDist x' x₀ ≤ ρ ^ 2 := hx'K
        have h2 : euclideanSqDist x' x₀ ≠ ρ ^ 2 := hnot.2
        exact lt_of_le_of_ne h1 h2
      have hmem : (t', x') ∈ U := hcyl hmK
      have hmax' : ∀ p ∈ K, φ p ≤ φ (t', x') := fun p hp => hmmax hp
      -- spatial local maximum
      have hloc : IsLocalMax (w t') x' := by
        filter_upwards [(isOpen_euclideanBall x₀ ρ).mem_nhds hx'lt] with y hy
        have hyK : (t', y) ∈ K := ⟨ht'K, euclideanBall_subset_euclideanClosedBall x₀ ρ hy⟩
        have := hmax' _ hyK
        simp only [hφ, hF] at this
        linarith
      have hcd : ContDiffAt ℝ 2 (w t') x' := by
        have h1 : ContDiffAt ℝ 2 F (t', x') := hw.contDiffAt (hU.mem_nhds hmem)
        have h2 : ContDiffAt ℝ 2 (fun y : Vec d => (t', y)) x' :=
          contDiffAt_const.prodMk contDiffAt_id
        exact h1.comp x' h2
      have hlap : euclideanCoordLaplacian (w t') x' ≤ 0 :=
        Finset.sum_nonpos fun i _ =>
          euclideanCoordSecondDeriv_diag_nonpos_of_isLocalMax hcd hloc i
      -- time derivative
      have hcdt : ContDiffAt ℝ 2 (fun τ : ℝ => w τ x') t' := by
        have h1 : ContDiffAt ℝ 2 F (t', x') := hw.contDiffAt (hU.mem_nhds hmem)
        have h2 : ContDiffAt ℝ 2 (fun τ : ℝ => (τ, x')) t' :=
          contDiffAt_id.prodMk contDiffAt_const
        exact h1.comp t' h2
      have hder : HasDerivAt (fun τ : ℝ => w τ x') (deriv (fun τ : ℝ => w τ x') t') t' :=
        (hcdt.differentiableAt (by norm_num)).hasDerivAt
      have hder2 : HasDerivAt (fun τ : ℝ => w τ x' - ε * (τ - t₀))
          (deriv (fun τ : ℝ => w τ x') t' - ε) t' := by
        have := (hasDerivAt_id t').sub_const t₀ |>.const_mul ε
        have h := hder.sub this
        rw [mul_one] at h
        exact h
      have hnn := deriv_nonneg_of_isMaxOn_Icc hder2 ht'0 ht'K.2 (fun τ hτ => by
        have := hmax' (τ, x') ⟨hτ, hx'K⟩
        simpa [hφ, hF] using this)
      have hs := hsub t' ht'K x' hx'K
      linarith
    have h1 : φ q ≤ φ m := hmmax hq
    have h2 : F m ≤ F pB := hpBmax hmB
    have h3 : 0 ≤ ε * (m.1 - t₀) := mul_nonneg hε.le (sub_nonneg.2 hmK.1.1)
    have h4 : ε * (q.1 - t₀) ≤ ε * (t₁ - t₀) :=
      mul_le_mul_of_nonneg_left (by linarith [hq.1.2]) hε.le
    simp only [hφ] at h1
    linarith
  refine ⟨pB.1, hpB.1.1, pB.2, hpB.1.2, ?_, ?_⟩
  · exact hpB.2
  · intro s hs y hy
    have hq : (s, y) ∈ K := ⟨hs, hy⟩
    have hle : ∀ ε : ℝ, 0 < ε → F (s, y) ≤ F pB + ε := by
      intro ε hε
      have := key (ε / (t₁ - t₀ + 1)) (div_pos hε (by linarith)) _ hq
      have e : ε / (t₁ - t₀ + 1) * (t₁ - t₀) ≤ ε := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        nlinarith
      linarith
    exact le_of_forall_pos_le_add hle

end

end PDE
