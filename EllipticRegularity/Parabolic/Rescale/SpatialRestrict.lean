module

public import EllipticRegularity.Parabolic.ParabolicDef

/-!
# Spatial restriction of parabolic energy functions

A parabolic energy function on `U × I` restricts, with the same representatives, to every
spatial subset `V ⊆ U`.  The only nontrivial field is weak continuity: a test function in
`L²_c(V)` is also in `L²_c(U)`, and its pairings over `V` and `U` agree because it vanishes
outside a compact subset of `V`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace PDE.Parabolic.Rescale

/-- An `L²_c(V)` function is `L²_c(U)` for `V ⊆ U`. -/
theorem isL2c_mono_set {d : ℕ} {U V : Set (Vec d)} (hVU : V ⊆ U) {ψ : Vec d → ℝ}
    (hψ : IsL2c V ψ) : IsL2c U ψ := by
  obtain ⟨hL2, K, hK, hKV, hK0⟩ := hψ
  refine ⟨?_, K, hK, hKV.trans hVU, hK0⟩
  have hind : K.indicator ψ = ψ := by
    funext x
    by_cases hx : x ∈ K
    · simp [hx]
    · simp [hx, hK0 x hx]
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have hmem : MemLp ψ 2 (volume.restrict K) :=
    hL2.mono_measure (Measure.restrict_mono hKV le_rfl)
  have h2 : MemLp (K.indicator ψ) 2 (volume.restrict U) := by
    rw [memLp_indicator_iff_restrict hKm, Measure.restrict_restrict hKm,
      inter_eq_left.2 (hKV.trans hVU)]
    exact hmem
  rwa [hind] at h2

/-- Integrals over `V ⊆ U` of a function vanishing outside a compact `K ⊆ V` agree. -/
theorem setIntegral_eq_of_zero_off {d : ℕ} {U V K : Set (Vec d)} (hVU : V ⊆ U)
    (hK : IsCompact K) (hKV : K ⊆ V) {F : Vec d → ℝ} (hF : ∀ x, x ∉ K → F x = 0) :
    ∫ x in V, F x = ∫ x in U, F x := by
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  have key : ∀ W : Set (Vec d), K ⊆ W → ∫ x in W, F x = ∫ x in K, F x := by
    intro W hKW
    have hind : F = K.indicator F := by
      funext x
      by_cases hx : x ∈ K
      · simp [hx]
      · simp [hx, hF x hx]
    calc ∫ x in W, F x = ∫ x in W, K.indicator F x := by rw [← hind]
      _ = ∫ x in W ∩ K, F x := setIntegral_indicator hKm
      _ = ∫ x in K, F x := by rw [inter_eq_right.2 hKW]
  rw [key V hKV, key U (hKV.trans hVU)]

/-- For `ψ ∈ L²_c(V)` the pairings over `V` and over `U ⊇ V` agree. -/
theorem setIntegral_mul_eq_of_isL2c {d : ℕ} {U V : Set (Vec d)} (hVU : V ⊆ U)
    {ψ : Vec d → ℝ} (hψ : IsL2c V ψ) (f : Vec d → ℝ) :
    ∫ x in V, f x * ψ x = ∫ x in U, f x * ψ x := by
  obtain ⟨-, K, hK, hKV, hK0⟩ := hψ
  exact setIntegral_eq_of_zero_off hVU hK hKV fun x hx => by simp [hK0 x hx]

/-- A weak gradient on `U` restricts to every subset `V ⊆ U`. -/
theorem hasWeakGradientOn_mono_set {d : ℕ} {U V : Set (Vec d)} (hVU : V ⊆ U)
    {f : Vec d → ℝ} {Df : Vec d → Vec d} (h : HasWeakGradientOn U f Df) :
    HasWeakGradientOn V f Df := by
  intro i φ hφ hc hsub
  have hK : IsCompact (tsupport φ) := hc.isCompact
  have hz : ∀ x, x ∉ tsupport φ → fderiv ℝ φ x = 0 := fun x hx =>
    fderiv_of_notMem_tsupport (𝕜 := ℝ) hx
  have h1 := setIntegral_eq_of_zero_off (U := U) hVU hK hsub
    (F := fun x => f x * (fderiv ℝ φ x) (basisVec i))
    (fun x hx => by simp [hz x hx])
  have h2 := setIntegral_eq_of_zero_off (U := U) hVU hK hsub
    (F := fun x => Df x i * φ x)
    (fun x hx => by simp [image_eq_zero_of_notMem_tsupport hx])
  rw [h1, h2]
  exact h i φ hφ hc (hsub.trans hVU)

/-- Restrict a parabolic energy function to a spatial subset (same representatives). -/
def restrictParH1Space {d : ℕ} {U V : Set (Vec d)} {I : Set ℝ} (hVU : V ⊆ U)
    (u : ParH1Function U I) : ParH1Function V I where
  toFun := u.toFun
  grad := u.grad
  memL2 := u.memL2.mono_measure
    (Measure.restrict_mono (prod_mono hVU subset_rfl) le_rfl)
  gradMemL2 i := (u.gradMemL2 i).mono_measure
    (Measure.restrict_mono (prod_mono hVU subset_rfl) le_rfl)
  sliceWeakGradient := by
    filter_upwards [u.sliceWeakGradient] with t ht
    exact hasWeakGradientOn_mono_set hVU ht
  sliceL2loc t ht K hK hKV := u.sliceL2loc t ht K hK (hKV.trans hVU)
  weakCont ψ hψ := by
    have h := u.weakCont ψ (isL2c_mono_set hVU hψ)
    refine h.congr fun t _ => ?_
    exact (setIntegral_mul_eq_of_isL2c hVU hψ (fun x => u.toFun (x, t)))

end PDE.Parabolic.Rescale
