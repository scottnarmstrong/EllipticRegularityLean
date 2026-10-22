module

public import EllipticRegularity.Ch4.GreenFunction.Construction

/-!
# Approximation of an arbitrary Green function (4.155)

For every Green function `G` and every `g ∈ L²(B_R)` vanishing in `B_ε`, `∫ Gₙ g → ∫ G g`; and
`‖Gₙ‖_{L²(B_R \ B_ε)} ≤ K_ε` once `ρₙ ≤ ε/2`.
-/

@[expose] public section

open scoped Topology ENNReal

namespace PDE.Ch4Green

open MeasureTheory PDE Filter

variable {d : ℕ}

namespace ApproxSetting

variable {Λ R : ℝ} {a : CoeffField d}

theorem one_le_Lam (S : ApproxSetting d Λ R a) : 1 ≤ Λ :=
  one_le_of_elliptic ⟨0, center_mem_euclideanBall _ S.hR⟩ S.hell

/-- **Approximation property** of an arbitrary Green function. -/
theorem tendsto_integral_of_isGreen (S : ApproxSetting d Λ R a) (hd : 3 ≤ d) {G : Vec d → ℝ}
    (hG : IsGreenFunction a R G) {ε : ℝ} (hε : 0 < ε) (hεR : ε < R) {g : Vec d → ℝ}
    (hg2 : MemL2On (euclideanBall (0 : Vec d) R) g)
    (hg : ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) ε)), g x = 0) :
    Tendsto (fun n => ∫ x in euclideanBall (0 : Vec d) R, (S.G n).toH1Function.toFun x * g x)
      atTop (𝓝 (∫ x in euclideanBall (0 : Vec d) R, G x * g x)) := by
  obtain ⟨C, -, hconv⟩ := S.exists_tendsto hd
  obtain ⟨L, hL, -, hvL⟩ := hconv hε hεR.le hg2 hg
  obtain ⟨v, hv⟩ := S.existsAdj g hg2
  rwa [tendsto_nhds_unique (hvL v hv) (hG.2.2 ε hε hεR g hg2 hg v hv)] at hL

/-- The weak-limit property of an arbitrary Green function on the shells `B_R \ B_ε`. -/
theorem weakLimitOn_of_isGreen (S : ApproxSetting d Λ R a) (hd : 3 ≤ d) {G : Vec d → ℝ}
    (hG : IsGreenFunction a R G) {ε : ℝ} (hε : 0 < ε) (hεR : ε < R) :
    WeakLimitOn (fun n => (S.G n).toH1Function.toFun)
      (euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) ε) G := by
  intro f hf
  set T := euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) ε
  have hT : MeasurableSet T :=
    (measurableSet_euclideanBall _ _).diff (measurableSet_euclideanBall _ _)
  have hTB : T ⊆ euclideanBall (0 : Vec d) R := Set.sdiff_subset
  have hzero : ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) ε)), T.indicator f x = 0 := by
    refine (ae_restrict_iff' (measurableSet_euclideanBall _ _)).2 (Eventually.of_forall ?_)
    intro x hx
    exact Set.indicator_of_notMem (fun h => h.2 hx) _
  have := S.tendsto_integral_of_isGreen hd hG hε hεR (memL2On_indicator hT hTB hf) hzero
  simpa only [integral_mul_indicator hT hTB] using this

/-- **Uniform `L²` bound** away from the pole: `‖Gₙ‖_{L²(B_R \ B_ε)} ≤ K_ε` once `ρₙ ≤ ε/2`. -/
theorem eLpNorm_G_le (S : ApproxSetting d Λ R a) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ R → ∀ n, approxRadius R n ≤ ε / 2 →
      (eLpNorm (S.G n).toH1Function.toFun 2
        (volumeOn (euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) ε))).toReal ≤
        poleConst C Λ ε S.E d := by
  obtain ⟨C, hC, hpole⟩ := pole_average (d := d) hd
  refine ⟨C, hC, ?_⟩
  intro ε hε hεR n hn
  set T := euclideanBall (0 : Vec d) R \ euclideanBall (0 : Vec d) ε with hTdef
  have hT : MeasurableSet T :=
    (measurableSet_euclideanBall _ _).diff (measurableSet_euclideanBall _ _)
  have hTB : T ⊆ euclideanBall (0 : Vec d) R := Set.sdiff_subset
  set f := (S.G n).toH1Function.toFun
  have hf : MemL2On T f := (S.G n).toH1Function.memL2.mono_measure (Measure.restrict_mono hTB
      le_rfl)
  set g := T.indicator f
  have hg2 : MemL2On (euclideanBall (0 : Vec d) R) g := memL2On_indicator hT hTB hf
  have hzero : ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) ε)), g x = 0 := by
    refine (ae_restrict_iff' (measurableSet_euclideanBall _ _)).2 (Eventually.of_forall ?_)
    intro x hx
    exact Set.indicator_of_notMem (fun h => h.2 hx) _
  obtain ⟨v, hv⟩ := S.existsAdj g hg2
  obtain ⟨-, hbd⟩ := hpole hε hεR S.hmeas S.hell hg2 hzero v hv S.hE (S.energyAdj g v hg2 hv)
  have hdual := integral_mul_eq_integralAverage (approxRadius_pos S.hR n).le
    (approxRadius_lt S.hR n).le (S.solG n) hv
  have hb := hbd _ (approxRadius_pos S.hR n) hn
  rw [← hdual, integral_mul_indicator hT hTB, eLpNorm_indicator_eq hT hTB] at hb
  have hsq : ∫ x in T, f x * f x = (eLpNorm f 2 (volumeOn T)).toReal ^ 2 := by
    rw [toReal_eLpNorm_two_sq_eq_integral_sq hf]
    congr 1
    funext x
    ring
  rw [hsq, abs_of_nonneg (sq_nonneg _)] at hb
  have hN := (ENNReal.toReal_nonneg : 0 ≤ (eLpNorm f 2 (volumeOn T)).toReal)
  have hΛ : 1 ≤ Λ := S.one_le_Lam
  have hK := poleConst_nonneg (d := d) hC.le (by linarith : (0 : ℝ) ≤ Λ) hε.le S.hE
  by_contra hlt
  rw [not_le] at hlt
  have hNpos : 0 < (eLpNorm f 2 (volumeOn T)).toReal := hK.trans_lt hlt
  nlinarith

end ApproxSetting

end PDE.Ch4Green
