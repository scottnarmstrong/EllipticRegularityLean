module

public import EllipticRegularity.Euler.WeakGradientAE
public import PDEFoundation.Euler.SpaceTimeLimit
public import PDEFoundation.Euler.SliceLimits
public import PDEFoundation.Euler.CrossLimit

/-!
# A jointly measurable space-time weak gradient for `v₂`

The slice construction (`ae_exists_weak_gradient`) gives, for a.e. `t`, a slice weak gradient `G_t ∈ L^p(cube)` with `‖G_t‖_p ≤ K p M` and
`∇(v^{aₖ}(t)) → G_t` in `L²(cube)`; `G_t` is a priori not jointly measurable.  Here `∇v^{aₖ}` is shown to converge
in `L²(cube × [0,T])` to a jointly measurable `Gst` (using the uniform slice bound `‖∇v^a(t)‖₂ = ‖curl v^a(t)‖₂ ≤ M`
and `exists_spacetime_limit`), and `Gst(·,t) = G_t` a.e. for a.e. `t`.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PDE

theorem eLpNorm_gradMat_entry_le {z : Vec 2 → Vec 2} (hz : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x => z x i))
    (hzp : IsTorusPeriodic z) (hzd : ∀ x, torusDiv z x = 0) {M : ℝ} (hM : ∀ x, |torusCurl z x| ≤ M)
    (i j : Fin 2) :
    eLpNorm (fun x => gradMat z x i j) 2 (volume.restrict torusCube) ≤ ENNReal.ofReal M := by
  have h1 : eLpNorm (fun x => gradMat z x i j) 2 (volume.restrict torusCube) ≤
      eLpNorm (fun x => matFrobNorm (gradMat z x)) 2 (volume.restrict torusCube) :=
    eLpNorm_mono_ae (continuous_gradMat_apply hz i j).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by
        simpa [Real.norm_eq_abs, abs_of_nonneg (matFrobNorm_nonneg _)] using
          abs_apply_le_matFrobNorm (gradMat z x) i j)
  rw [eLpNorm_matFrobNorm_gradMat_eq_curl hz hzp hzd] at h1
  refine h1.trans ?_
  have := eLpNorm_le_of_ae_bound (p := 2) (μ := volume.restrict torusCube)
    (f := torusCurl z) (C := M) (continuous_torusCurl hz).aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => by simpa [Real.norm_eq_abs] using hM x)
  refine this.trans ?_
  simp [volume_torusCube]

theorem ae_slice_aesm {T : ℝ} {h : Vec 2 × ℝ → ℝ} (hm : AEStronglyMeasurable h (eulerMeasure T)) :
    ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)),
      AEStronglyMeasurable (fun x => h (x, t)) (volume.restrict torusCube) := by
  rw [eulerMeasure_eq_prod] at hm
  exact (hm.comp_quasiMeasurePreserving (Measure.measurePreserving_swap
    (μ := volume.restrict (Icc (0 : ℝ) T)) (ν := volume.restrict torusCube)).quasiMeasurePreserving).prodMk_left

theorem ae_slice_bdd {T : ℝ} {v : Vec 2 × ℝ → Vec 2} {B : ℝ}
    (hB : ∀ᵐ z ∂(eulerMeasure T), vecNormSq (v z) ≤ B) :
    ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), ∀ᵐ x ∂(volume.restrict torusCube),
      vecNormSq (v (x, t)) ≤ B := by
  rw [eulerMeasure_eq_prod] at hB
  have h1 := (Measure.measurePreserving_swap (μ := volume.restrict (Icc (0 : ℝ) T))
    (ν := volume.restrict torusCube)).quasiMeasurePreserving.ae hB
  exact Measure.ae_ae_of_ae_prod h1

/-- **Space-time weak gradient of `v₂`.** -/
theorem exists_spacetime_gradient :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (T : ℝ), 0 < T → ∀ (v : Vec 2 × ℝ → Vec 2) (ω : Vec 2 × ℝ → ℝ) (B M : ℝ),
      EulerBdd T B v →
      (∀ ψ : Vec 2 × ℝ → ℝ, IsPeriodicSmooth ψ → VanishesOutsideInterior T ψ →
        ∫ z, vecDot (v z) (fun j => fderiv ℝ ψ z (basisVec j, 0)) ∂(eulerMeasure T) = 0) →
      AEStronglyMeasurable ω (eulerMeasure T) → (∀ᵐ z ∂(eulerMeasure T), |ω z| ≤ M) →
      (∀ ψ : Vec 2 × ℝ → ℝ, IsPeriodicSmooth ψ → VanishesOutsideInterior T ψ →
        ∫ z, ω z * ψ z ∂(eulerMeasure T) =
          ∫ z, (v z 0 * fderiv ℝ ψ z (basisVec 1, 0) - v z 1 * fderiv ℝ ψ z (basisVec 0, 0))
            ∂(eulerMeasure T)) →
      ∃ Gst : Vec 2 × ℝ → Fin 2 → Fin 2 → ℝ, SpaceTimeGrad T B v Gst ∧
        ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)),
          IsTorusWeakGradient (fun x => v (x, t)) (fun x => Gst (x, t)) ∧
          ∀ p : ℝ, 2 ≤ p →
            MemLp (fun x => matFrobNorm (Gst (x, t))) (ENNReal.ofReal p) (volume.restrict torusCube) ∧
            eLpNorm (fun x => matFrobNorm (Gst (x, t))) (ENNReal.ofReal p) (volume.restrict torusCube) ≤
              ENNReal.ofReal (K * p * M) := by
  obtain ⟨K, hK, hmain⟩ := ae_exists_weak_gradient
  refine ⟨K, hK, ?_⟩
  intro T hT v ω B M hbv hdiv hωm hωM hcurl
  have H := hmain T hT v ω B M tDelta hbv.meas hbv.per hbv.bdd hdiv hωm hωM hcurl tDelta_pos
    tDelta_le_one tendsto_tDelta
  have Hdiv := ae_mollify_slice_div hT hbv.meas hbv.per hbv.bdd hdiv
  have Hcurl := ae_mollify_slice_curl hT hbv.meas hbv.per hbv.bdd hωm hωM hcurl
  have Hmeas : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), ∀ i,
      AEStronglyMeasurable (fun x => v (x, t) i) (volume.restrict torusCube) :=
    ae_all_iff.2 fun i => ae_slice_aesm (hbv.coord_aesm i)
  have Hbdd := ae_slice_bdd hbv.bdd
  -- slice bound `‖∂ⱼ vᵃᵢ‖₂ ≤ M`
  have hbd : ∀ i j, ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), ∀ k,
      eLpNorm (fun x => gradMollST (tDelta k) v (x, t) i j) 2 (volume.restrict torusCube) ≤
        ENNReal.ofReal M := by
    intro i j
    filter_upwards [Hdiv, Hcurl] with t hd hc k
    obtain ⟨hs, hp, hdv, _⟩ := hd (tDelta k) (tDelta_pos k)
    obtain ⟨hcu, hb⟩ := hc (tDelta k) (tDelta_pos k)
    exact eLpNorm_gradMat_entry_le (z := mollifyVec (tDelta k) (fun y => v (y, t))) hs hp hdv
      (fun x => by rw [hcu x]; exact hb x) i j
  have hsl : ∀ i j, ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), ∃ g : Vec 2 → ℝ,
      MemLp g 2 (volume.restrict torusCube) ∧
      Tendsto (fun k => eLpNorm (fun x => gradMollST (tDelta k) v (x, t) i j - g x) 2
        (volume.restrict torusCube)) atTop (𝓝 0) := by
    intro i j
    filter_upwards [H, Hdiv] with t ht hd
    obtain ⟨G, hGl2, hGc, -, -⟩ := ht
    refine ⟨fun x => G x i j, hGl2 i j, ?_⟩
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hGc (fun _ => bot_le)
      (fun k => ?_)
    obtain ⟨hs, -, -, -⟩ := hd (tDelta k) (tDelta_pos k)
    refine eLpNorm_mono_ae ((continuous_gradMat_apply hs i j).aestronglyMeasurable.sub
      (hGl2 i j).aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
    have h1 := norm_le_pi_norm (fun j' => (gradMat (mollifyVec (tDelta k) (fun y => v (y, t))) x - G x) i j') j
    have h2 := norm_le_pi_norm (gradMat (mollifyVec (tDelta k) (fun y => v (y, t))) x - G x) i
    exact h1.trans h2
  have hF : ∀ i j, ∃ F : Vec 2 × ℝ → ℝ, Measurable F ∧ MemLp F 2 (eulerMeasure T) ∧
      Tendsto (fun k => eLpNorm ((fun z => gradMollST (tDelta k) v z i j) - F) 2 (eulerMeasure T))
        atTop (𝓝 0) ∧
      ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)),
        Tendsto (fun k => eLpNorm (fun x => gradMollST (tDelta k) v (x, t) i j - F (x, t)) 2
          (volume.restrict torusCube)) atTop (𝓝 0) := fun i j =>
    exists_spacetime_limit (fun k => hbv.grad_aesm (tDelta_pos k) i j) (hbd i j) (hsl i j)
  choose F hFm hFmem hFconv hFslice using hF
  have hFs : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)), ∀ i j,
      Tendsto (fun k => eLpNorm (fun x => gradMollST (tDelta k) v (x, t) i j - F i j (x, t)) 2
        (volume.restrict torusCube)) atTop (𝓝 0) :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun j => hFslice i j
  have Hall : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) T)),
      GradSlice tDelta (fun x => v (x, t)) (fun x i j => F i j (x, t)) B ∧
      IsTorusWeakGradient (fun x => v (x, t)) (fun x i j => F i j (x, t)) ∧
      ∀ p : ℝ, 2 ≤ p →
        MemLp (fun x => matFrobNorm (fun i j => F i j (x, t))) (ENNReal.ofReal p) (volume.restrict torusCube) ∧
        eLpNorm (fun x => matFrobNorm (fun i j => F i j (x, t))) (ENNReal.ofReal p)
          (volume.restrict torusCube) ≤ ENNReal.ofReal (K * p * M) := by
   filter_upwards [H, Hdiv, Hmeas, Hbdd, hFs] with t ht hd hm hb hFt
   obtain ⟨G, hGl2, hGc, hGw, hGp⟩ := ht
   -- identification `F(·,t) = G_t` a.e.
   have hid : ∀ i j, (fun x => F i j (x, t)) =ᵐ[volume.restrict torusCube] (fun x => G x i j) := by
     intro i j
     have hGc' : Tendsto (fun k => eLpNorm (fun x => gradMollST (tDelta k) v (x, t) i j - G x i j) 2
         (volume.restrict torusCube)) atTop (𝓝 0) := by
       refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hGc (fun _ => bot_le)
         (fun k => ?_)
       obtain ⟨hs, -, -, -⟩ := hd (tDelta k) (tDelta_pos k)
       refine eLpNorm_mono_ae ((continuous_gradMat_apply hs i j).aestronglyMeasurable.sub
         (hGl2 i j).aestronglyMeasurable) (Filter.Eventually.of_forall fun x => ?_)
       have h1 := norm_le_pi_norm (fun j' => (gradMat (mollifyVec (tDelta k) (fun y => v (y, t))) x - G x) i j') j
       have h2 := norm_le_pi_norm (gradMat (mollifyVec (tDelta k) (fun y => v (y, t))) x - G x) i
       exact h1.trans h2
     have hup : Tendsto (fun k => eLpNorm (fun x => gradMollST (tDelta k) v (x, t) i j - F i j (x, t)) 2
         (volume.restrict torusCube) + eLpNorm (fun x => gradMollST (tDelta k) v (x, t) i j - G x i j) 2
         (volume.restrict torusCube)) atTop (𝓝 0) := by
       have := (hFt i j).add hGc'
       simpa using this
     have hle : ∀ k, eLpNorm (fun x => F i j (x, t) - G x i j) 2 (volume.restrict torusCube) ≤
         eLpNorm (fun x => gradMollST (tDelta k) v (x, t) i j - F i j (x, t)) 2 (volume.restrict torusCube) +
         eLpNorm (fun x => gradMollST (tDelta k) v (x, t) i j - G x i j) 2 (volume.restrict torusCube) := by
       intro k
       calc eLpNorm (fun x => F i j (x, t) - G x i j) 2 (volume.restrict torusCube)
           = eLpNorm ((fun x => gradMollST (tDelta k) v (x, t) i j - G x i j) -
               (fun x => gradMollST (tDelta k) v (x, t) i j - F i j (x, t))) 2 (volume.restrict torusCube) := by
             congr 1; funext x; simp
         _ ≤ eLpNorm (fun x => gradMollST (tDelta k) v (x, t) i j - G x i j) 2 (volume.restrict torusCube) +
             eLpNorm (fun x => gradMollST (tDelta k) v (x, t) i j - F i j (x, t)) 2
               (volume.restrict torusCube) := eLpNorm_sub_le (by norm_num)
         _ = _ := add_comm _ _
     have hzero : eLpNorm (fun x => F i j (x, t) - G x i j) 2 (volume.restrict torusCube) = 0 :=
       le_antisymm (ge_of_tendsto' hup hle) bot_le
     have := (eLpNorm_eq_zero_iff (by norm_num)).1 hzero
     filter_upwards [this] with x hx
     simpa [sub_eq_zero] using hx
   have hidall : ∀ᵐ x ∂(volume.restrict torusCube), ∀ i j, F i j (x, t) = G x i j := by
     rw [ae_all_iff]; intro i
     rw [ae_all_iff]; intro j
     exact hid i j
   have hGeq : ∀ x, (∀ i j, F i j (x, t) = G x i j) → (fun i j => F i j (x, t)) = G x := fun x hx =>
     funext fun i => funext fun j => hx i j
   refine ⟨?_, ?_, ?_⟩
   · exact
       { pos := tDelta_pos
         le_one := tDelta_le_one
         tends := tendsto_tDelta
         per := hbv.per t
         meas := hm
         bdd := hb
         smooth := fun k i => (hd (tDelta k) (tDelta_pos k)).1 i
         mper := fun k => (hd (tDelta k) (tDelta_pos k)).2.1
         mdiv := fun k => (hd (tDelta k) (tDelta_pos k)).2.2.1
         Gl2 := fun i j => (hGl2 i j).ae_eq (hid i j).symm
         grad_conv := fun i j => hFt i j }
   · intro i j ψ hψ hψp
     have := hGw i j ψ hψ hψp
     show ∫ x in torusCube, v (x, t) i * pd j ψ x = -∫ x in torusCube, F i j (x, t) * ψ x
     rw [this]
     congr 1
     refine integral_congr_ae ?_
     filter_upwards [hid i j] with x hx
     rw [hx]
   · intro p hp
     have hae : (fun x => matFrobNorm (fun i j => F i j (x, t))) =ᵐ[volume.restrict torusCube]
         (fun x => matFrobNorm (G x)) := by
       filter_upwards [hidall] with x hx
       rw [hGeq x hx]
     obtain ⟨hmem, hle⟩ := hGp p hp
     refine ⟨hmem.ae_eq hae.symm, ?_⟩
     rw [eLpNorm_congr_ae hae]
     exact hle
  exact ⟨fun z i j => F i j z, ⟨fun i j => (hFm i j).aestronglyMeasurable, hFmem, hFconv,
    Hall.mono fun t h => h.1⟩, Hall.mono fun t h => h.2⟩

end PDE
