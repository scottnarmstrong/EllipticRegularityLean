module

public import EllipticRegularity.Parabolic.ParabolicDef
public import PDEFoundation.Ambient.Basis

/-!
# Cutoff facts for the parabolic Caccioppoli inequality

Time of first support, vanishing of derivatives, and global bounds for a cutoff
`φ ∈ C¹_c((-1,0] × U)` (`U` open).
-/

@[expose] public section

namespace PDE

namespace ParabCaccioppoli

open MeasureTheory Set Filter Topology

variable {d : ℕ}

/-- There is a time `m ∈ (-1,0]` before which the cutoff vanishes. -/
theorem exists_vanishing_time {U : Set (Vec d)} (φ : ParCutoff U (Ioc (-1 : ℝ) 0)) :
    ∃ m : ℝ, -1 < m ∧ m ≤ 0 ∧ ∀ z ∈ U ×ˢ Ioc (-1 : ℝ) 0, z.2 < m → φ.toFun z = 0 := by
  obtain ⟨Z, hZc, hZs, hZ0⟩ := φ.compact_support
  rcases Z.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, by norm_num, le_rfl, fun z hz _ => hZ0 z hz (by simp)⟩
  · obtain ⟨z0, hz0, hmin⟩ := hZc.exists_isMinOn hne continuous_snd.continuousOn
    have hz0I := (hZs hz0).2
    exact ⟨z0.2, hz0I.1, hz0I.2, fun z hz hlt => hZ0 z hz fun hzZ => not_le.2 hlt (hmin hzZ)⟩

/-- Away from the compact support (inside `U × (-1,0]`) the derivative of the cutoff vanishes. -/
theorem fderiv_eq_zero_of_not_mem {U : Set (Vec d)} (hU : IsOpen U)
    (φ : ParCutoff U (Ioc (-1 : ℝ) 0)) (Z : Set (Vec d × ℝ)) (hZc : IsCompact Z)
    (hZ0 : ∀ z ∈ U ×ˢ Ioc (-1 : ℝ) 0, z ∉ Z → φ.toFun z = 0)
    (z : Vec d × ℝ) (hz : z ∈ U ×ˢ Ioc (-1 : ℝ) 0) (hzZ : z ∉ Z) :
    fderiv ℝ φ.toFun z = 0 := by
  obtain ⟨x, t⟩ := z
  obtain ⟨hxU, ht1, ht2⟩ := hz
  set S : Set (Vec d × ℝ) := (U ×ˢ Ioo (-1 : ℝ) 0) ∩ Zᶜ with hS
  have hSo : IsOpen S := (hU.prod isOpen_Ioo).inter hZc.isClosed.isOpen_compl
  have hSz : ∀ y ∈ S, fderiv ℝ φ.toFun y = 0 := by
    intro y hy
    have h0 : φ.toFun =ᶠ[𝓝 y] fun _ => (0 : ℝ) := by
      filter_upwards [hSo.mem_nhds hy] with w hw
      exact hZ0 w ⟨hw.1.1, Ioo_subset_Ioc_self hw.1.2⟩ hw.2
    rw [h0.fderiv_eq]; simp
  have hcont : Continuous (fderiv ℝ φ.toFun) := φ.contDiff.continuous_fderiv one_ne_zero
  have htend : Tendsto (fun s : ℝ => ((x, t - s) : Vec d × ℝ)) (𝓝[>] 0) (𝓝 (x, t)) := by
    have : Tendsto (fun s : ℝ => ((x, t - s) : Vec d × ℝ)) (𝓝 0) (𝓝 (x, t - 0)) :=
      (continuous_const.prodMk (continuous_const.sub continuous_id)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ), ((x, t - s) : Vec d × ℝ) ∈ S := by
    have h1 : ∀ᶠ s in 𝓝[>] (0 : ℝ), ((x, t - s) : Vec d × ℝ) ∈ Zᶜ :=
      htend.eventually (hZc.isClosed.isOpen_compl.mem_nhds hzZ)
    have h2 : ∀ᶠ s in 𝓝[>] (0 : ℝ), s ∈ Ioo (0 : ℝ) (t + 1) :=
      Ioo_mem_nhdsGT (by linarith)
    filter_upwards [h1, h2] with s hs1 hs2
    exact ⟨⟨hxU, by simp only [mem_Ioo]; constructor <;> linarith [hs2.1, hs2.2]⟩, hs1⟩
  have hlim : Tendsto (fun s : ℝ => fderiv ℝ φ.toFun (x, t - s)) (𝓝[>] 0)
      (𝓝 (fderiv ℝ φ.toFun (x, t))) := (hcont.tendsto _).comp htend
  have hlim0 : Tendsto (fun s : ℝ => fderiv ℝ φ.toFun (x, t - s)) (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' (hev.mono fun s hs => (hSz _ hs).symm)
  exact tendsto_nhds_unique hlim hlim0

/-- Global bound for the cutoff and its derivative on `U × (-1,0]`. -/
theorem exists_bound {U : Set (Vec d)} (hU : IsOpen U)
    (φ : ParCutoff U (Ioc (-1 : ℝ) 0)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ U ×ˢ Ioc (-1 : ℝ) 0,
      |φ.toFun z| ≤ C ∧ ‖fderiv ℝ φ.toFun z‖ ≤ C := by
  obtain ⟨Z, hZc, hZs, hZ0⟩ := φ.compact_support
  have hc : Continuous φ.toFun := φ.contDiff.continuous
  have hcd : Continuous (fderiv ℝ φ.toFun) := φ.contDiff.continuous_fderiv one_ne_zero
  obtain ⟨C1, hC1⟩ := hZc.exists_bound_of_continuousOn hc.continuousOn
  obtain ⟨C2, hC2⟩ := hZc.exists_bound_of_continuousOn hcd.continuousOn
  refine ⟨max 0 (max C1 C2), le_max_left _ _, fun z hz => ?_⟩
  by_cases hzZ : z ∈ Z
  · refine ⟨?_, ?_⟩
    · have := hC1 z hzZ; rw [Real.norm_eq_abs] at this
      exact this.trans ((le_max_left _ _).trans (le_max_right _ _))
    · exact (hC2 z hzZ).trans ((le_max_right _ _).trans (le_max_right _ _))
  · rw [hZ0 z hz hzZ, fderiv_eq_zero_of_not_mem hU φ Z hZc hZ0 z hz hzZ]
    simp

/-- The vanishing region: `φ` and its derivative vanish on `U × (-1, m)`. -/
theorem fderiv_eq_zero_of_lt {U : Set (Vec d)} (hU : IsOpen U)
    (φ : ParCutoff U (Ioc (-1 : ℝ) 0)) (m : ℝ) (hm0 : m ≤ 0)
    (hm : ∀ z ∈ U ×ˢ Ioc (-1 : ℝ) 0, z.2 < m → φ.toFun z = 0)
    (z : Vec d × ℝ) (hz : z ∈ U ×ˢ Ioo (-1 : ℝ) m) :
    φ.toFun z = 0 ∧ fderiv ℝ φ.toFun z = 0 := by
  have hW : IsOpen (U ×ˢ Ioo (-1 : ℝ) m) := hU.prod isOpen_Ioo
  have h0 : φ.toFun =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
    filter_upwards [hW.mem_nhds hz] with w hw
    exact hm w ⟨hw.1, ⟨hw.2.1, hw.2.2.le.trans hm0⟩⟩ hw.2.2
  refine ⟨h0.eq_of_nhds, ?_⟩
  rw [h0.fderiv_eq]; simp

end ParabCaccioppoli

end PDE
