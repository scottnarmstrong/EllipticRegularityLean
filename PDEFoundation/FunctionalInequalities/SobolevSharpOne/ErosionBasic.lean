module

public import PDEFoundation.Geometry.EuclideanBall.Topology
public import Mathlib.Analysis.Normed.Group.Bounded
public import Mathlib.Topology.Order.Compact
public import Mathlib.Topology.Algebra.Support
public import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Erosion of a function by a Euclidean ball: basic data

For a continuous compactly supported `f : Vec d → ℝ` and a radius `h ≥ 0`, the erosion
`erode f h x` is the infimum of `f (x + v)` over the Euclidean closed ball `|v| ≤ h`
(an infimum over the subtype, so no junk value enters), and
`erosionSet f h s = {x | ∀ v ∈ euclideanClosedBall 0 h, s ≤ f (x + v)}` is the eroded superlevel
set. We also record a modulus of continuity `modulus F h`.
-/

@[expose] public section

open Set Filter Topology
open scoped Pointwise

namespace PDE.SobolevSharp

variable {d : ℕ}

/-- Erosion of `f` by the closed Euclidean ball of radius `h`. -/
noncomputable def erode (f : Vec d → ℝ) (h : ℝ) (x : Vec d) : ℝ :=
  ⨅ v : euclideanClosedBall (0 : Vec d) h, f (x + (v : Vec d))

/-- The eroded superlevel set `A_s = {x | ∀ |v| ≤ h, s ≤ f (x + v)}`. -/
def erosionSet (f : Vec d → ℝ) (h s : ℝ) : Set (Vec d) :=
  {x | ∀ v ∈ euclideanClosedBall (0 : Vec d) h, s ≤ f (x + v)}

/-- Modulus of continuity of `F`: the supremum of `|F (x + v) - F x|` over `x` and `|v| ≤ h`. -/
noncomputable def modulus (F : Vec d → ℝ) (h : ℝ) : ℝ :=
  sSup {t | ∃ x : Vec d, ∃ v ∈ euclideanClosedBall (0 : Vec d) h, t = |F (x + v) - F x|}

theorem zero_mem_euclideanClosedBall_zero {h : ℝ} (hh : 0 ≤ h) :
    (0 : Vec d) ∈ euclideanClosedBall (0 : Vec d) h := by
  rw [mem_euclideanClosedBall_iff_vecEuclideanNorm_le hh, sub_zero]
  have : vecEuclideanNorm (0 : Vec d) = 0 := vecEuclideanNorm_eq_zero_iff.mpr rfl
  rw [this]; exact hh

theorem neg_mem_euclideanClosedBall_zero {h : ℝ} {v : Vec d}
    (hv : v ∈ euclideanClosedBall (0 : Vec d) h) (hh : 0 ≤ h) :
    -v ∈ euclideanClosedBall (0 : Vec d) h := by
  rw [mem_euclideanClosedBall_iff_vecEuclideanNorm_le hh, sub_zero, vecEuclideanNorm_neg]
  have := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hh).mp hv
  rwa [sub_zero] at this

theorem smul_mem_euclideanClosedBall_zero {h : ℝ} {v : Vec d}
    (hv : v ∈ euclideanClosedBall (0 : Vec d) h) (hh : 0 ≤ h) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : t • v ∈ euclideanClosedBall (0 : Vec d) h := by
  rw [mem_euclideanClosedBall_iff_vecEuclideanNorm_le hh, sub_zero, vecEuclideanNorm_smul,
    abs_of_nonneg ht0]
  have := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hh).mp hv
  rw [sub_zero] at this
  calc t * vecEuclideanNorm v ≤ 1 * vecEuclideanNorm v :=
        mul_le_mul_of_nonneg_right ht1 (vecEuclideanNorm_nonneg v)
    _ ≤ h := by rw [one_mul]; exact this

section Basic

variable {f : Vec d → ℝ} {h s : ℝ} {x : Vec d}

theorem bddBelow_range_of_hasCompactSupport (hf : Continuous f) (hfc : HasCompactSupport f) :
    BddBelow (range f) :=
  (hfc.isCompact_range hf).bddBelow

theorem bddBelow_range_comp (hf : Continuous f) (hfc : HasCompactSupport f) (x : Vec d)
    (h : ℝ) :
    BddBelow (range fun v : euclideanClosedBall (0 : Vec d) h => f (x + (v : Vec d))) := by
  obtain ⟨m, hm⟩ := bddBelow_range_of_hasCompactSupport hf hfc
  exact ⟨m, by rintro _ ⟨v, rfl⟩; exact hm ⟨_, rfl⟩⟩

theorem erode_le (hf : Continuous f) (hfc : HasCompactSupport f) {v : Vec d}
    (hv : v ∈ euclideanClosedBall (0 : Vec d) h) : erode f h x ≤ f (x + v) :=
  ciInf_le (bddBelow_range_comp hf hfc x h) (⟨v, hv⟩ : euclideanClosedBall (0 : Vec d) h)

theorem le_erode_iff (hf : Continuous f) (hfc : HasCompactSupport f) (hh : 0 ≤ h) :
    s ≤ erode f h x ↔ ∀ v ∈ euclideanClosedBall (0 : Vec d) h, s ≤ f (x + v) := by
  have : Nonempty (euclideanClosedBall (0 : Vec d) h) :=
    ⟨⟨0, zero_mem_euclideanClosedBall_zero hh⟩⟩
  unfold erode
  rw [le_ciInf_iff (bddBelow_range_comp hf hfc x h)]
  exact ⟨fun H v hv => H ⟨v, hv⟩, fun H v => H v v.2⟩

theorem mem_erosionSet_iff (hf : Continuous f) (hfc : HasCompactSupport f) (hh : 0 ≤ h) :
    x ∈ erosionSet f h s ↔ s ≤ erode f h x :=
  (le_erode_iff hf hfc hh).symm

theorem erosionSet_eq_preimage (hf : Continuous f) (hfc : HasCompactSupport f) (hh : 0 ≤ h) :
    erosionSet f h s = {x | s ≤ erode f h x} := by
  ext x; exact mem_erosionSet_iff hf hfc hh

theorem erode_le_self (hf : Continuous f) (hfc : HasCompactSupport f) (hh : 0 ≤ h) :
    erode f h x ≤ f x := by
  simpa using erode_le (x := x) hf hfc (zero_mem_euclideanClosedBall_zero hh)

/-- There is a minimizing translation. -/
theorem exists_eq_erode (hf : Continuous f) (hfc : HasCompactSupport f) (hh : 0 ≤ h) :
    ∃ v ∈ euclideanClosedBall (0 : Vec d) h, f (x + v) = erode f h x := by
  have hK := isCompact_euclideanClosedBall (0 : Vec d) hh
  obtain ⟨v, hv, hmin⟩ := hK.exists_isMinOn ⟨0, zero_mem_euclideanClosedBall_zero hh⟩
    (f := fun v => f (x + v)) (by fun_prop)
  refine ⟨v, hv, le_antisymm ?_ (erode_le hf hfc hv)⟩
  rw [le_erode_iff hf hfc hh]
  exact fun w hw => hmin hw

theorem erode_eq_sInf_image (h : ℝ) (x : Vec d) :
    erode f h x = sInf ((fun v => f (x + v)) '' euclideanClosedBall (0 : Vec d) h) := by
  rw [sInf_image']; rfl

theorem continuous_erode (hf : Continuous f) (hh : 0 ≤ h) :
    Continuous (erode f h) := by
  have hK := isCompact_euclideanClosedBall (0 : Vec d) hh
  have : erode f h = fun x => sInf ((fun v => f (x + v)) '' euclideanClosedBall (0 : Vec d) h) := by
    ext x; exact erode_eq_sInf_image h x
  rw [this]
  exact hK.continuous_sInf (f := fun x v => f (x + v)) (by fun_prop)

theorem measurable_erode (hf : Continuous f) (hh : 0 ≤ h) :
    Measurable (erode f h) :=
  (continuous_erode hf hh).measurable

theorem isClosed_erosionSet (hf : Continuous f) (hfc : HasCompactSupport f) (hh : 0 ≤ h) :
    IsClosed (erosionSet f h s) := by
  rw [erosionSet_eq_preimage hf hfc hh]
  exact isClosed_le continuous_const (continuous_erode hf hh)

theorem erosionSet_subset_superlevel (hh : 0 ≤ h) :
    erosionSet f h s ⊆ {x | s ≤ f x} := fun x hx => by
  simpa using hx 0 (zero_mem_euclideanClosedBall_zero hh)

theorem isCompact_erosionSet (hf : Continuous f) (hfc : HasCompactSupport f) (hh : 0 ≤ h)
    (hs : 0 < s) : IsCompact (erosionSet f h s) := by
  refine hfc.of_isClosed_subset (isClosed_erosionSet hf hfc hh) ?_
  intro x hx
  have h1 := erosionSet_subset_superlevel hh hx
  exact subset_tsupport _ (by simp only [Function.mem_support]; exact (lt_of_lt_of_le hs h1).ne')

theorem erosionSet_add_subset (_hh : 0 ≤ h) :
    erosionSet f h s + euclideanClosedBall (0 : Vec d) h ⊆ {x | s ≤ f x} := by
  rintro _ ⟨x, hx, v, hv, rfl⟩
  exact hx v hv

end Basic

section Modulus

variable {F : Vec d → ℝ}

theorem bddAbove_modulus_set (hF : Continuous F) (hFc : HasCompactSupport F) (h : ℝ) :
    BddAbove {t | ∃ x : Vec d, ∃ v ∈ euclideanClosedBall (0 : Vec d) h,
      t = |F (x + v) - F x|} := by
  obtain ⟨M, hM⟩ := (hFc.isCompact_range hF).isBounded.exists_norm_le
  refine ⟨2 * M, ?_⟩
  rintro _ ⟨x, v, -, rfl⟩
  have h1 := hM (F (x + v)) ⟨_, rfl⟩
  have h2 := hM (F x) ⟨_, rfl⟩
  rw [Real.norm_eq_abs] at h1 h2
  calc |F (x + v) - F x| ≤ |F (x + v)| + |F x| := abs_sub _ _
    _ ≤ 2 * M := by linarith

theorem abs_sub_le_modulus (hF : Continuous F) (hFc : HasCompactSupport F) {h : ℝ} {v : Vec d}
    (hv : v ∈ euclideanClosedBall (0 : Vec d) h) (x : Vec d) :
    |F (x + v) - F x| ≤ modulus F h :=
  le_csSup (bddAbove_modulus_set hF hFc h) ⟨x, v, hv, rfl⟩

theorem modulus_nonneg (hF : Continuous F) (hFc : HasCompactSupport F) {h : ℝ} (hh : 0 ≤ h) :
    0 ≤ modulus F h :=
  (abs_nonneg (F (0 + 0) - F 0)).trans
    (abs_sub_le_modulus hF hFc (zero_mem_euclideanClosedBall_zero hh) 0)

theorem modulus_mono (hF : Continuous F) (hFc : HasCompactSupport F) {h h' : ℝ}
    (hh : 0 ≤ h) (hhh : h ≤ h') : modulus F h ≤ modulus F h' := by
  refine csSup_le_csSup (bddAbove_modulus_set hF hFc h') ⟨_, 0, 0,
    zero_mem_euclideanClosedBall_zero hh, rfl⟩ ?_
  rintro _ ⟨x, v, hv, rfl⟩
  exact ⟨x, v, euclideanClosedBall_mono hh hhh hv, rfl⟩

/-- Uniform continuity gives `modulus F h → 0`. -/
theorem modulus_le_of_small (hF : Continuous F) (hFc : HasCompactSupport F) {ε : ℝ}
    (hε : 0 < ε) : ∃ δ > 0, ∀ h, 0 ≤ h → h < δ → modulus F h ≤ ε := by
  obtain ⟨δ, hδ, H⟩ := Metric.uniformContinuous_iff.mp
    (hFc.uniformContinuous_of_continuous hF) ε hε
  refine ⟨δ, hδ, fun h hh hhδ => ?_⟩
  refine csSup_le ⟨_, 0, 0, zero_mem_euclideanClosedBall_zero hh, rfl⟩ ?_
  rintro _ ⟨x, v, hv, rfl⟩
  have hv' := euclideanClosedBall_subset_supClosedBall hh hv
  have hd : dist (x + v) x < δ := by
    rw [dist_eq_norm, add_sub_cancel_left]
    have := Metric.mem_closedBall.mp hv'
    rw [dist_zero_right] at this
    exact lt_of_le_of_lt this hhδ
  have := H hd
  rw [Real.dist_eq] at this
  exact this.le

theorem tendsto_modulus (hF : Continuous F) (hFc : HasCompactSupport F) :
    Tendsto (modulus F) (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨δ, hδ, H⟩ := modulus_le_of_small hF hFc (half_pos hε)
  refine ⟨δ, hδ, fun {h} hh hd => ?_⟩
  have h0 : 0 < h := hh
  have hlt : h < δ := by simpa [Real.dist_eq, abs_of_pos h0] using hd
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (modulus_nonneg hF hFc h0.le)]
  linarith [H h h0.le hlt]

/-- Uniform continuity: `erode F h ≥ F - modulus F h`. -/
theorem sub_modulus_le_erode (hF : Continuous F) (hFc : HasCompactSupport F) {h : ℝ}
    (hh : 0 ≤ h) (x : Vec d) : F x - modulus F h ≤ erode F h x := by
  rw [le_erode_iff hF hFc hh]
  intro v hv
  have := (abs_le.mp (abs_sub_le_modulus hF hFc hv x)).1
  linarith

/-- `{F ≥ s + ω_F(h)} ⊆ A_s`, so `ν_h(s) ≥ μ(s + ω_F(h))`. -/
theorem superlevel_modulus_subset_erosionSet (hF : Continuous F) (hFc : HasCompactSupport F)
    {h : ℝ} (hh : 0 ≤ h) (s : ℝ) :
    {x | s + modulus F h ≤ F x} ⊆ erosionSet F h s := by
  intro x hx
  rw [mem_erosionSet_iff hF hFc hh]
  have := sub_modulus_le_erode hF hFc hh x
  have hx' : s + modulus F h ≤ F x := hx
  linarith

end Modulus

end PDE.SobolevSharp
