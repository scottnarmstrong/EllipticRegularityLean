module

public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-! # A compactly supported time test with prescribed endpoint values -/

@[expose] public section

set_option autoImplicit false

open Set

namespace PDE.Parabolic.Lions

/-- A globally smooth compactly supported scalar test which is one at the initial endpoint and
zero at the terminal endpoint. -/
theorem exists_cauchy_endpoint_test {s T : ℝ} (hsT : s < T) :
    ∃ θ : ℝ → ℝ, ContDiff ℝ 1 θ ∧ HasCompactSupport θ ∧ θ s = 1 ∧ θ T = 0 := by
  let δ : ℝ := (T - s) / 3
  let O : Set ℝ := Ioo (s - δ) (s + δ)
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hsO : s ∈ O := by
    change s - δ < s ∧ s < s + δ
    constructor <;> linarith [hδ]
  have hOopen : IsOpen O := by exact isOpen_Ioo
  have hTO : T ∉ O := by
    intro hT
    have hT' := hT.2
    dsimp [O, δ] at hT'
    linarith
  obtain ⟨θ, hθ, hrange, hzero, hone⟩ :=
    exists_contDiff_zero_iff_one_iff_of_isClosed (n := 1)
      hOopen.isClosed_compl isClosed_singleton
      (Set.disjoint_left.mpr fun x hx hx' => by
        have : x = s := by simpa using hx'
        subst x
        exact hx hsO)
  have hθs : θ s = 1 := (hone s).mp (by simp)
  have hθT : θ T = 0 := by
    have : T ∈ Oᶜ := by simpa using hTO
    exact (hzero T).mp this
  have hθcompact : HasCompactSupport θ := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := Icc (s - δ) (s + δ)) isCompact_Icc ?_
    intro t ht
    by_contra hn
    have htO : t ∉ O := by
      intro htO
      exact hn ⟨htO.1.le, htO.2.le⟩
    exact ht ((hzero t).mp htO)
  refine ⟨θ, hθ.of_le (by simp), hθcompact, hθs, hθT⟩

end PDE.Parabolic.Lions
