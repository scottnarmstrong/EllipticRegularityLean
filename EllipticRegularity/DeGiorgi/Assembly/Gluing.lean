module

public import EllipticRegularity.DeGiorgi.Assembly.EssContinuous

/-!
# Gluing local continuous representatives
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE.DGNMAssembly

open MeasureTheory Filter Set

variable {d : ℕ}

/-- If every point of an open set `O` has an open neighbourhood on which `f` has a continuous
representative, then `f` has a continuous representative on `O`. -/
theorem glue_continuous_rep {O : Set (Vec d)} (hO : IsOpen O) {f : Vec d → ℝ}
    (h : ∀ x ∈ O, ∃ V : Set (Vec d), IsOpen V ∧ x ∈ V ∧
      ∃ w : Vec d → ℝ, ContinuousOn w V ∧ w =ᵐ[volumeOn V] f) :
    ∃ v : Vec d → ℝ, ContinuousOn v O ∧ v =ᵐ[volumeOn O] f := by
  choose! V hVo hxV w hwc hwf using h
  classical
  let v : Vec d → ℝ := fun y => if y ∈ O then w y y else 0
  have hv : ∀ y ∈ O, v y = w y y := fun y hy => by simp [v, hy]
  have key : ∀ x ∈ O, ∀ y ∈ V x ∩ O, v y = w x y := by
    intro x hx y hy
    rw [hv y hy.2]
    have hyO := hy.2
    have hS : IsOpen (V x ∩ V y) := (hVo x hx).inter (hVo y hyO)
    have hae : w y =ᵐ[volumeOn (V x ∩ V y)] w x := by
      have h1 : w y =ᵐ[volumeOn (V y)] f := hwf y hyO
      have h2 : w x =ᵐ[volumeOn (V x)] f := hwf x hx
      have h1' : w y =ᵐ[volumeOn (V x ∩ V y)] f :=
        ae_mono (Measure.restrict_mono inter_subset_right le_rfl) h1
      have h2' : w x =ᵐ[volumeOn (V x ∩ V y)] f :=
        ae_mono (Measure.restrict_mono inter_subset_left le_rfl) h2
      exact h1'.trans h2'.symm
    have heq := Measure.eqOn_of_ae_eq hae
      ((hwc y hyO).mono inter_subset_right) ((hwc x hx).mono inter_subset_left)
      (by rw [hS.interior_eq]; exact subset_closure)
    exact heq ⟨hy.1, hxV y hyO⟩
  refine ⟨v, ?_, ?_⟩
  · intro x hx
    have hcw : ContinuousWithinAt (w x) O x :=
      ((hwc x hx).continuousAt ((hVo x hx).mem_nhds (hxV x hx))).continuousWithinAt
    have hev : v =ᶠ[𝓝[O] x] w x := by
      have : V x ∩ O ∈ 𝓝[O] x :=
        inter_mem (mem_nhdsWithin_of_mem_nhds ((hVo x hx).mem_nhds (hxV x hx)))
          self_mem_nhdsWithin
      exact eventuallyEq_of_mem this fun y hy => key x hx y hy
    exact hcw.congr_of_eventuallyEq hev (key x hx x ⟨hxV x hx, hx⟩)
  · obtain ⟨t, htO, htc, hcover⟩ := TopologicalSpace.countable_cover_nhdsWithin
      (f := V) (s := O) (fun x hx =>
        mem_nhdsWithin_of_mem_nhds ((hVo x hx).mem_nhds (hxV x hx)))
    have hcover' : O ⊆ ⋃ x ∈ t, (V x ∩ O) := by
      intro y hy
      have := hcover hy
      simp only [mem_iUnion] at this ⊢
      obtain ⟨x, hxt, hyx⟩ := this
      exact ⟨x, hxt, hyx, hy⟩
    have hall : ∀ᵐ y ∂(volumeOn (⋃ x ∈ t, (V x ∩ O))), v y = f y := by
      rw [volumeOn, ae_restrict_biUnion_iff _ htc]
      intro x hxt
      have hxO := htO hxt
      have h1 : ∀ᵐ y ∂(volumeOn (V x ∩ O)), w x y = f y :=
        ae_mono (Measure.restrict_mono inter_subset_left le_rfl) (hwf x hxO)
      have h2 : ∀ᵐ y ∂(volumeOn (V x ∩ O)), y ∈ V x ∩ O :=
        ae_restrict_mem ((hVo x hxO).inter hO).measurableSet
      filter_upwards [h1, h2] with y hy1 hy2
      rw [key x hxO y hy2, hy1]
    exact ae_mono (Measure.restrict_mono hcover' le_rfl) hall

/-- Local continuity of a weak solution: on `B_{1/8}(x)`, for `x ∈ B_{3/4}`, a solution has a
continuous representative (from De Giorgi's Hölder estimate applied to a rescaling). -/
theorem local_cont_rep {d : ℕ} (hDG : DeGiorgiHolderConcl d) (hSol : SolAffineTransfer d)
    {Λ : ℝ} (hΛ : 1 ≤ Λ) {a : CoeffField d}
    (hmeas : ∀ i j : Fin d, AEMeasurable (fun x => a x i j)
      (volumeOn (euclideanBall (0 : Vec d) 1)))
    (hell : ∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x))
    {u : H1Function (euclideanBall (0 : Vec d) 1)}
    (hsol : IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u (0 : Vec d → ℝ) 0) :
    ∀ x ∈ euclideanBall (0 : Vec d) (3 / 4), ∃ V : Set (Vec d), IsOpen V ∧ x ∈ V ∧
      ∃ w : Vec d → ℝ, ContinuousOn w V ∧ w =ᵐ[volumeOn V] u.toFun := by
  intro x hx
  have hr : (0 : ℝ) < 1 / 4 := by norm_num
  have hsub : euclideanBall x (1 / 4) ⊆ euclideanBall (0 : Vec d) 1 := by
    apply euclideanBall_subset_of_center_norm_add_le (by norm_num) (by norm_num)
    have := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp hx
    rw [sub_zero] at this ⊢
    linarith
  obtain ⟨ut, hut, hsolt⟩ := hSol Λ a hmeas hell x (1 / 4) hr hsub u hsol 1 0
  obtain ⟨hmeast, hellt⟩ := coeff_comp_aff hmeas hell x hr hsub
  obtain ⟨CD, hCD, hDGq⟩ := hDG
  obtain ⟨α, hα0, hα1, hαexp, hDGa⟩ := hDGq Λ hΛ
  obtain ⟨v, M₀, M₁, hae, hM₀, hM₁, hvbd, hHold, hbound⟩ := hDGa _ hmeast hellt ut hsolt
  have hvc : ContinuousOn v (euclideanBall (0 : Vec d) (1 / 2)) :=
    continuousOn_of_euclideanHolder hα0 hHold
  have hutfun : ut.toFun = fun y => u.toFun (x + (1 / 4 : ℝ) • y) := by
    funext y; rw [hut y]; ring
  have hback : ∀ y : Vec d, x + (1 / 4 : ℝ) • ((4 : ℝ) • (y - x)) = y := by
    intro y; ext i; simp
  have hfwd : ∀ z : Vec d, (4 : ℝ) • ((x + (1 / 4 : ℝ) • z) - x) = z := by
    intro z; ext i; simp
  have hmapsto : ∀ y ∈ euclideanBall x (1 / 4 * (1 / 2)),
      (4 : ℝ) • (y - x) ∈ euclideanBall (0 : Vec d) (1 / 2) := by
    intro y hy
    rw [← aff_mem_ball_iff x _ hr (by norm_num : (0 : ℝ) < 1 / 2), hback]
    exact hy
  have hcont : Continuous fun y : Vec d => (4 : ℝ) • (y - x) :=
    by fun_prop
  refine ⟨euclideanBall x (1 / 4 * (1 / 2)), isOpen_euclideanBall _ _,
    center_mem_euclideanBall _ (by norm_num), fun y => v ((4 : ℝ) • (y - x)), ?_, ?_⟩
  · exact hvc.comp hcont.continuousOn hmapsto
  · change ∀ᵐ y ∂(volumeOn (euclideanBall x (1 / 4 * (1 / 2)))),
      v ((4 : ℝ) • (y - x)) = u.toFun y
    rw [← ae_ball_comp_aff_iff x hr (by norm_num : (0 : ℝ) < 1 / 2)]
    filter_upwards [hae] with z hz
    rw [hfwd z, hz, hutfun]

end PDE.DGNMAssembly
