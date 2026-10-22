module

public import PDEFoundation.Sobolev.Trace.Extension.ExtBound
public import PDEFoundation.Sobolev.ClassicalOnOpenWeakGradient
import PDEFoundation.Sobolev.Trace.Assembly.Basic

/-!
# The extension as an element of `W^{1,p}(Ω)`

`ExtData.extW1p` packages `D.ext g` (for `g` in the Besov class; `0` otherwise) together with its
classical gradient on `Ω` as a representative-level `W^{1,p}(Ω)` function.
-/

@[expose] public section

namespace PDE.TraceLane

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

variable {n : ℕ} {Ω : Set (Vec (n + 1))}

open scoped Classical in
/-- The gradient representative of the extension: the classical gradient on `Ω`, `0` outside. -/
noncomputable def ExtData.extGrad (D : ExtData Ω) (g : Vec (n + 1) → ℝ) (x : Vec (n + 1)) :
    Vec (n + 1) :=
  if x ∈ Ω then classicalGradient (D.ext g) x else 0

theorem ExtData.extGrad_of_mem (D : ExtData Ω) (g : Vec (n + 1) → ℝ) {x : Vec (n + 1)}
    (hx : x ∈ Ω) : D.extGrad g x = classicalGradient (D.ext g) x := by
  simp [ExtData.extGrad, hx]

theorem ExtData.extGrad_of_notMem (D : ExtData Ω) (g : Vec (n + 1) → ℝ) {x : Vec (n + 1)}
    (hx : x ∉ Ω) : D.extGrad g x = 0 := by
  simp [ExtData.extGrad, hx]

theorem ExtData.extGrad_ae_eq (D : ExtData Ω) (hΩo : IsOpen Ω) (g : Vec (n + 1) → ℝ) :
    D.extGrad g =ᵐ[volumeOn Ω] classicalGradient (D.ext g) :=
  (ae_restrict_iff' hΩo.measurableSet).2
    (Eventually.of_forall fun _ hx => D.extGrad_of_mem g hx)

/-- The `W^{1,p}` pair norm of the extension, in terms of the classical gradient. -/
theorem ExtData.w1pPairNorm_extGrad (D : ExtData Ω) (hΩo : IsOpen Ω) {p : ℝ}
    (g : Vec (n + 1) → ℝ) :
    w1pPairNorm Ω p (D.ext g) (D.extGrad g) = w1pPairNorm Ω p (D.ext g)
      (classicalGradient (D.ext g)) :=
  w1pPairNorm_congr_ae (Filter.EventuallyEq.refl _ _) (D.extGrad_ae_eq hΩo g)

theorem ExtData.memLp_ext (D : ExtData Ω) (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) {p : ℝ}
    (hp : 1 < p) {g : Vec (n + 1) → ℝ} (hg : IsBesov Ω (1 - 1 / p) p g) :
    MemLpOn Ω (ENNReal.ofReal p) (D.ext g) := by
  obtain ⟨C, hC⟩ := D.ext_bound hΩo hΩb hp
  have h := hC g hg
  have hlt : w1pPairNorm Ω p (D.ext g) (classicalGradient (D.ext g)) < ⊤ :=
    h.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hg.2)
  show eLpNorm _ _ _ < ⊤
  exact lt_of_le_of_lt le_self_add hlt

theorem ExtData.gradMemLp_ext (D : ExtData Ω) (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {p : ℝ} (hp : 1 < p) {g : Vec (n + 1) → ℝ} (hg : IsBesov Ω (1 - 1 / p) p g) :
    GradMemLpOn Ω (ENNReal.ofReal p) (D.extGrad g) := by
  obtain ⟨C, hC⟩ := D.ext_bound hΩo hΩb hp
  have h := hC g hg
  have hlt : w1pPairNorm Ω p (D.ext g) (classicalGradient (D.ext g)) < ⊤ :=
    h.trans_lt (ENNReal.mul_lt_top ENNReal.coe_lt_top hg.2)
  have hcd : ContDiffOn ℝ 1 (D.ext g) Ω := D.ext_contDiffOn hp hg
  have hcont : ContinuousOn (fderiv ℝ (D.ext g)) Ω := hcd.continuousOn_fderiv_of_isOpen hΩo le_rfl
  intro i
  have hci : ContinuousOn (fun x => classicalGradient (D.ext g) x i) Ω :=
    (continuousOn_pi.1 (continuousOn_pi.2 fun i => hcont.clm_apply continuousOn_const)) i
  have haes : AEStronglyMeasurable (fun x => D.extGrad g x i) (volumeOn Ω) :=
    (hci.aestronglyMeasurable hΩo.measurableSet).congr (by
      filter_upwards [D.extGrad_ae_eq hΩo g] with x hx
      rw [hx])
  show eLpNorm _ _ _ < ⊤
  refine lt_of_le_of_lt ?_ (lt_of_le_of_lt le_add_self hlt)
  refine eLpNorm_mono_ae haes ?_
  filter_upwards [D.extGrad_ae_eq hΩo g] with x hx
  rw [hx]
  simpa [Real.norm_eq_abs, abs_of_nonneg (vecEuclideanNorm_nonneg _)] using
    abs_apply_le_vecEuclideanNorm (classicalGradient (D.ext g) x) i

theorem ExtData.hasWeakGradient_ext (D : ExtData Ω) (hΩo : IsOpen Ω) {p : ℝ} (hp : 1 < p)
    {g : Vec (n + 1) → ℝ} (hg : IsBesov Ω (1 - 1 / p) p g) :
    HasWeakGradientOn Ω (D.ext g) (D.extGrad g) := by
  have h := HasWeakGradientOn.of_contDiffOn hΩo (D.ext_contDiffOn hp hg)
  intro i φ hφ hφc hφΩ
  refine (h i φ hφ hφc hφΩ).trans ?_
  congr 1
  exact setIntegral_congr_fun hΩo.measurableSet fun x hx => by
    simp only [D.extGrad_of_mem g hx]

open scoped Classical in
/-- The extension as an element of `W^{1,p}(Ω)` (zero outside the Besov class); its gradient is the
classical gradient on `Ω` and `0` outside. -/
noncomputable def ExtData.extW1p (D : ExtData Ω) (hΩo : IsOpen Ω)
    (hΩb : Bornology.IsBounded Ω) {p : ℝ} (hp : 1 < p) (g : Vec (n + 1) → ℝ) :
    W1pFunction Ω (ENNReal.ofReal p) :=
  if hg : IsBesov Ω (1 - 1 / p) p g then
    { toFun := D.ext g
      grad := D.extGrad g
      memLp := D.memLp_ext hΩo hΩb hp hg
      gradMemLp := D.gradMemLp_ext hΩo hΩb hp hg
      hasWeakGradient := D.hasWeakGradient_ext hΩo hp hg }
  else 0

theorem ExtData.extW1p_toFun (D : ExtData Ω) (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {p : ℝ} (hp : 1 < p) {g : Vec (n + 1) → ℝ} (hg : IsBesov Ω (1 - 1 / p) p g) :
    (D.extW1p hΩo hΩb hp g).toFun = D.ext g := by
  simp only [ExtData.extW1p, hg, ↓reduceDIte]

theorem ExtData.extW1p_grad_eq (D : ExtData Ω) (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {p : ℝ} (hp : 1 < p) {g : Vec (n + 1) → ℝ} (hg : IsBesov Ω (1 - 1 / p) p g) :
    (D.extW1p hΩo hΩb hp g).grad = D.extGrad g := by
  simp only [ExtData.extW1p, hg, ↓reduceDIte]

theorem ExtData.extW1p_grad (D : ExtData Ω) (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {p : ℝ} (hp : 1 < p) {g : Vec (n + 1) → ℝ} (hg : IsBesov Ω (1 - 1 / p) p g) {x : Vec (n + 1)}
    (hx : x ∈ Ω) : (D.extW1p hΩo hΩb hp g).grad x = classicalGradient (D.ext g) x := by
  rw [D.extW1p_grad_eq hΩo hΩb hp hg, D.extGrad_of_mem g hx]

/-- The `W^{1,p}(Ω)` norm of the extension is bounded by the Besov norm of the data. -/
theorem ExtData.extW1p_bound (D : ExtData Ω) (hΩo : IsOpen Ω) (hΩb : Bornology.IsBounded Ω)
    {p : ℝ} (hp : 1 < p) :
    ∃ C : ℝ≥0, ∀ g : Vec (n + 1) → ℝ, IsBesov Ω (1 - 1 / p) p g →
      w1pNorm Ω p (D.extW1p hΩo hΩb hp g) ≤ C * besovNorm Ω (1 - 1 / p) p g := by
  obtain ⟨C, hC⟩ := D.ext_bound hΩo hΩb hp
  refine ⟨C, fun g hg => ?_⟩
  unfold w1pNorm
  rw [D.extW1p_toFun hΩo hΩb hp hg, D.extW1p_grad_eq hΩo hΩb hp hg,
    D.w1pPairNorm_extGrad hΩo g]
  exact hC g hg

end PDE.TraceLane
