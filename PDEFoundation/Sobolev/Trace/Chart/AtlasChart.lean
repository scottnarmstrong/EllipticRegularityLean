module

public import PDEFoundation.Sobolev.Trace.Chart.AtlasLocal
public import PDEFoundation.Sobolev.Cutoff.Ball
public import PDEFoundation.Geometry.C1Boundary
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-!
# Existence of graph charts at boundary points

For `Ω` open with `C¹` boundary and `x₀ ∈ ∂Ω`, the local graph `γ₀` of `AtlasLocal` is
globalised by a smooth ball cutoff to a globally `C¹`, compactly perturbed, Lipschitz function, and
yields a `GraphChart Ω` whose cylinder contains `x₀`.  The chart cylinders are open.
-/

@[expose] public section

namespace PDE.TraceLane

open Set Filter Topology

/-- Right inverse property of `graphMapInv` (for `sgn ^ 2 = 1`). -/
theorem atlas_graphMap_graphMapInv {n : ℕ} (i : Fin (n + 1)) (γ : Vec n → ℝ) {sgn : ℝ}
    (hs : sgn ^ 2 = 1) (x : Vec (n + 1)) :
    graphMap i γ sgn (graphMapInv i γ sgn x) = x := by
  unfold graphMap graphMapInv
  have : γ (fun j => x (i.succAbove j)) + sgn * (sgn * (x i - γ (fun j => x (i.succAbove j)))) =
      x i := by
    have : sgn * (sgn * (x i - γ (fun j => x (i.succAbove j)))) =
        x i - γ (fun j => x (i.succAbove j)) := by
      rw [← mul_assoc, ← sq, hs, one_mul]
    rw [this]; ring
  rw [this]
  exact atlasInsertCLM_base i x

/-- Left inverse property of `graphMapInv` (for `sgn ^ 2 = 1`). -/
theorem atlas_graphMapInv_graphMap {n : ℕ} (i : Fin (n + 1)) (γ : Vec n → ℝ) {sgn : ℝ}
    (hs : sgn ^ 2 = 1) (z : Vec n × ℝ) :
    graphMapInv i γ sgn (graphMap i γ sgn z) = z := by
  unfold graphMap graphMapInv
  have h1 : (fun j => (Fin.insertNth i (γ z.1 + sgn * z.2) z.1 : Vec (n + 1)) (i.succAbove j)) =
      z.1 := by
    ext j; simp
  rw [h1]
  refine Prod.ext rfl ?_
  simp only [Fin.insertNth_apply_same]
  have : sgn * (γ z.1 + sgn * z.2 - γ z.1) = sgn ^ 2 * z.2 := by ring
  rw [this, hs, one_mul]

theorem GraphChart.atlas_isOpen_dom {n : ℕ} {Ω : Set (Vec (n + 1))} (φ : GraphChart Ω) :
    IsOpen φ.dom := by
  have hc : Continuous φ.inv := by
    unfold GraphChart.inv graphMapInv
    have hγ := φ.γ_contDiff.continuous
    refine Continuous.prodMk ?_ ?_
    · exact continuous_pi fun j => continuous_apply _
    · exact continuous_const.mul ((continuous_apply _).sub
        (hγ.comp (continuous_pi fun j => continuous_apply _)))
  have hopen : IsOpen (euclideanBall φ.c φ.r ×ˢ Ioo (-φ.a) φ.a) :=
    (isOpen_euclideanBall _ _).prod isOpen_Ioo
  have : φ.dom = φ.inv ⁻¹' (euclideanBall φ.c φ.r ×ˢ Ioo (-φ.a) φ.a) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      show graphMapInv φ.i φ.γ φ.sgn (graphMap φ.i φ.γ φ.sgn z) ∈
        euclideanBall φ.c φ.r ×ˢ Ioo (-φ.a) φ.a
      rwa [atlas_graphMapInv_graphMap _ _ φ.sgn_sq]
    · intro hy
      refine ⟨φ.inv y, hy, ?_⟩
      exact atlas_graphMap_graphMapInv _ _ φ.sgn_sq y
  rw [this]
  exact hopen.preimage hc

private theorem phi_zero_of_mem_frontier {d : ℕ} {Ω W : Set (Vec d)} (hΩo : IsOpen Ω)
    (hW : IsOpen W) {φ : Vec d → ℝ} (hφ : Continuous φ)
    (hE : Ω ∩ W = {y | y ∈ W ∧ φ y < 0}) {x₀ : Vec d} (hx₀ : x₀ ∈ frontier Ω) (hx₀W : x₀ ∈ W) :
    φ x₀ = 0 := by
  rw [hΩo.frontier_eq] at hx₀
  obtain ⟨hcl, hnot⟩ := hx₀
  apply le_antisymm
  · by_contra hpos
    push Not at hpos
    have hopen : IsOpen (W ∩ {y | 0 < φ y}) := hW.inter (isOpen_lt continuous_const hφ)
    obtain ⟨y, hy, hyΩ⟩ := mem_closure_iff.1 hcl _ hopen ⟨hx₀W, hpos⟩
    have : y ∈ Ω ∩ W := ⟨hyΩ, hy.1⟩
    rw [hE] at this
    exact absurd this.2 (not_lt.2 hy.2.le)
  · by_contra hneg
    push Not at hneg
    exact hnot (by
      have : x₀ ∈ {y | y ∈ W ∧ φ y < 0} := ⟨hx₀W, hneg⟩
      rw [← hE] at this
      exact this.1)

/-- Every frontier point has a graph chart whose cylinder contains it. -/
theorem exists_graphChart {n : ℕ} {Ω : Set (Vec (n + 1))} (hΩo : IsOpen Ω) (hΩ : HasC1Boundary Ω)
    {x₀ : Vec (n + 1)} (hx₀ : x₀ ∈ frontier Ω) : ∃ φ : GraphChart Ω, x₀ ∈ φ.dom := by
  obtain ⟨W, hW, hx₀W, φ, hφ, hφd, hE⟩ := hΩ x₀ hx₀
  have hφ0 : φ x₀ = 0 := phi_zero_of_mem_frontier hΩo hW hφ.continuous hE hx₀ hx₀W
  obtain ⟨i, sgn, γ₀, ρ, a, hsgn, hρ, ha, hγ₀x, hγ₀C, hloc⟩ :=
    exists_localGraph hW hφ hx₀W hφ0 (hφd x₀ hx₀W)
  set x₀' : Vec n := fun j => x₀ (i.succAbove j) with hx₀'
  have hr₀ : 0 ≤ ρ / 2 := by positivity
  have hr₀ρ : ρ / 2 < ρ := by linarith
  set χ : Vec n → ℝ := canonicalBallCutoff x₀' (ρ / 2) ρ with hχ
  have hχsm : ContDiff ℝ 1 χ :=
    (canonicalBallCutoff_smooth x₀' hr₀ hr₀ρ).of_le (by exact_mod_cast le_top)
  have hχ1 : ∀ x' ∈ euclideanBall x₀' (ρ / 2), χ x' = 1 := fun x' hx' =>
    canonicalBallCutoff_eq_one_on_inner hr₀ hr₀ρ hx'
  have hχts : tsupport χ ⊆ euclideanBall x₀' ρ := canonicalBallCutoff_tsupport_subset_outer hr₀ hr₀ρ
  have hχcs : HasCompactSupport χ := canonicalBallCutoff_hasCompactSupport hr₀ hr₀ρ
  have hballρ : ∀ r, 0 < r → r ≤ ρ → euclideanBall x₀' r ⊆ Metric.ball x₀' ρ := fun r h hr x' hx' =>
    Metric.ball_subset_ball hr (euclideanBall_subset_supBall h hx')
  set γ : Vec n → ℝ := fun x' => x₀ i + χ x' * (γ₀ x' - x₀ i) with hγ
  have hγC : ContDiff ℝ 1 γ := by
    rw [contDiff_iff_contDiffAt]
    intro y
    by_cases hy : y ∈ tsupport χ
    · have hyb : ContDiffAt ℝ 1 γ₀ y := hγ₀C y (hballρ ρ hρ le_rfl (hχts hy))
      exact contDiffAt_const.add (hχsm.contDiffAt.mul (hyb.sub contDiffAt_const))
    · have hev : (fun x' => x₀ i) =ᶠ[𝓝 y] γ := by
        have : (tsupport χ)ᶜ ∈ 𝓝 y := (isClosed_tsupport χ).isOpen_compl.mem_nhds hy
        filter_upwards [this] with z hz
        simp [hγ, image_eq_zero_of_notMem_tsupport hz]
      exact contDiffAt_const.congr_of_eventuallyEq hev.symm
  have hcs : HasCompactSupport (fun x' => γ x' - x₀ i) := by
    have : HasCompactSupport (fun x' => χ x' * (γ₀ x' - x₀ i)) := hχcs.mul_right
    simpa [hγ] using this
  obtain ⟨C, hC⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hcs
    (hγC.sub contDiff_const) one_ne_zero
  have hγx : ∀ x' ∈ euclideanBall x₀' (ρ / 2), γ x' = γ₀ x' := by
    intro x' hx'
    simp [hγ, hχ1 x' hx']
  have hkey : ∀ x' ∈ euclideanBall x₀' (ρ / 2), ∀ t ∈ Ioo (-a) a,
      graphMap i γ sgn (x', t) ∈ W ∧ (φ (graphMap i γ sgn (x', t)) < 0 ↔ 0 < t) := by
    intro x' hx' t ht
    have h := hloc x' (hballρ _ (by positivity) hr₀ρ.le hx') t ht
    have e : graphMap i γ sgn (x', t) = graphMap i γ₀ sgn (x', t) := by
      unfold graphMap; simp only [hγx x' hx']
    rw [e]; exact h
  have hcenter : x₀' ∈ euclideanBall x₀' (ρ / 2) := center_mem_euclideanBall x₀' (by positivity)
  refine ⟨{ i := i, sgn := sgn, sgn_sq := hsgn, γ := γ, γ_contDiff := hγC, L := C,
            L_nonneg := C.2, γ_lip := ?_, c := x₀', r := ρ / 2, a := a,
            r_pos := by positivity, a_pos := ha, inter_eq := ?_ }, ?_⟩
  · intro x' y'
    have h1 := hC.dist_le_mul x' y'
    simp only [dist_eq_norm] at h1
    have h2 : |γ x' - γ y'| = |(γ x' - x₀ i) - (γ y' - x₀ i)| := by ring_nf
    rw [h2]
    calc _ ≤ (C : ℝ) * ‖x' - y'‖ := h1
      _ ≤ (C : ℝ) * vecEuclideanNorm (x' - y') :=
        mul_le_mul_of_nonneg_left (norm_le_vecEuclideanNorm _) C.2
  · ext y
    constructor
    · rintro ⟨hyΩ, ⟨x', t⟩, ⟨hx', ht⟩, rfl⟩
      obtain ⟨hyW, hiff⟩ := hkey x' hx' t ht
      have : graphMap i γ sgn (x', t) ∈ Ω ∩ W := ⟨hyΩ, hyW⟩
      rw [hE] at this
      exact ⟨(x', t), ⟨hx', (hiff.1 this.2), ht.2⟩, rfl⟩
    · rintro ⟨⟨x', t⟩, ⟨hx', ht0, hta⟩, rfl⟩
      have ht : t ∈ Ioo (-a) a := ⟨by linarith [ht0], hta⟩
      obtain ⟨hyW, hiff⟩ := hkey x' hx' t ht
      have : graphMap i γ sgn (x', t) ∈ {y | y ∈ W ∧ φ y < 0} := ⟨hyW, hiff.2 ht0⟩
      rw [← hE] at this
      exact ⟨this.1, (x', t), ⟨hx', ht⟩, rfl⟩
  · refine ⟨(x₀', 0), ⟨hcenter, ⟨by linarith, ha⟩⟩, ?_⟩
    show graphMap i γ sgn (x₀', 0) = x₀
    have h1 : γ x₀' = x₀ i := by simp [hγ, hχ1 x₀' hcenter, hγ₀x]
    rw [graphMap_eq_add]
    simp only [zero_smul, add_zero, h1]
    exact atlasInsertCLM_base i x₀

end PDE.TraceLane
