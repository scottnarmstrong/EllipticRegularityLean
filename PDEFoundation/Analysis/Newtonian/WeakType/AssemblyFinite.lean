module

public import PDEFoundation.Analysis.Newtonian.WeakType.AssemblyBad
public import PDEFoundation.Analysis.Newtonian.WeakType.AssemblyLinear
public import PDEFoundation.Analysis.Newtonian.WeakType.TruncateGood
public import PDEFoundation.Analysis.Newtonian.WeakType.HormanderCZBad
public import PDEFoundation.Analysis.Newtonian.WeakType.EnergyFinal
public import PDEFoundation.Analysis.Newtonian.WeakType.DecompositionExceptional

/-!
# The weak-type estimate for the mollified field and a finite truncation

For `F` smooth with compact support, `S` stopping cubes, a finite set `s` of cubes and `a > 0`
small relative to the cubes of `s`, the field `F_a = mollVec a F` splits as
`F_a = g_a + ∑_{k ∈ s} b_{k,a}` into smooth compactly supported pieces.  The good piece is
controlled by the `L²` energy bound; the bad pieces by the Hörmander estimate off the exceptional
set `⋃_k B(c_k, 4 r_k)`.
-/

@[expose] public section

open BoxIntegral MeasureTheory Set Filter
open scoped ENNReal Topology

namespace PDE.NewtonWeakType

noncomputable section

variable {d : ℕ} {I : Box (Fin d)} {F : Vec d → Vec d} {lam : ℝ}

variable (S : CZStopping I F lam)

/-- The exceptional set `⋃_k B(c_k, 4 r_k)`. -/
def czBigDilate (k : S.ι) : Set (Vec d) :=
  euclideanBall (czCenter S k) (2 * (2 * czRadius S k))

/-- The exceptional set. -/
def czExceptional : Set (Vec d) := ⋃ k, czBigDilate S k

theorem mollVec_decomp {a : ℝ} (ha : 0 < a) (hF : VBdd F) (s : Finset S.ι) :
    mollVec a F = fun y => mollVec a (czTrunc S s) y + ∑ k ∈ s, mollVec a (czBad S k) y := by
  have hbad := fun k (_ : k ∈ s) => vbdd_czBad S hF k
  have hF' : F = fun y => czTrunc S s y + ∑ k ∈ s, czBad S k y := by
    funext y; simp [czTrunc]
  have h1 := mollVec_add ha (vbdd_czTrunc S hF s) (VBdd.finsetSum s hbad)
  have h2 := mollVec_finsetSum ha s hbad
  conv_lhs => rw [hF']
  rw [h1, h2]

variable {S}

theorem gradient_mollVec_decomp (hd : 0 < d) {a : ℝ} (ha : 0 < a) (hF : VBdd F)
    (s : Finset S.ι) (x : Vec d) :
    classicalGradient (newtonPotential (mollVec a F)) x =
      classicalGradient (newtonPotential (mollVec a (czTrunc S s))) x +
        ∑ k ∈ s, classicalGradient (newtonPotential (mollVec a (czBad S k))) x := by
  have hbad := fun k (_ : k ∈ s) => vbdd_czBad S hF k
  rw [mollVec_decomp S ha hF s]
  rw [classicalGradient_newtonPotential_add hd (contDiff_mollVec ha (vbdd_czTrunc S hF s))
    (hasCompactSupport_mollVec ha (vbdd_czTrunc S hF s))
    (ContDiff.sum fun k hk => contDiff_mollVec ha (hbad k hk))
    (hasCompactSupport_finsetSum s fun k hk => hasCompactSupport_mollVec ha (hbad k hk)) x,
    classicalGradient_newtonPotential_finsetSum hd s (fun k hk => contDiff_mollVec ha (hbad k hk))
      (fun k hk => hasCompactSupport_mollVec ha (hbad k hk)) x]

theorem volume_gradient_mollVec_trunc_gt_le (hd : 0 < d) {a : ℝ} (ha : 0 < a) (hF : VBdd F)
    (s : Finset S.ι) {l : ℝ} (hl : 0 < l) :
    volume {x | l < vecEuclideanNorm
        (classicalGradient (newtonPotential (mollVec a (czTrunc S s))) x)} ≤
      ENNReal.ofReal (l⁻¹ ^ 2 * ∫ x, vecNormSq (czTrunc S s x)) := by
  refine (volume_gradient_newtonPotential_gt_le' hd (contDiff_mollVec ha (vbdd_czTrunc S hF s))
    (hasCompactSupport_mollVec ha (vbdd_czTrunc S hF s)) hl).trans ?_
  refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ (by positivity))
  exact integral_vecNormSq_mollVec_le ha (vbdd_czTrunc S hF s)

theorem vecEuclideanNorm_finsetSum_le {ι : Type*} (s : Finset ι) (v : ι → Vec d) :
    vecEuclideanNorm (∑ k ∈ s, v k) ≤ ∑ k ∈ s, vecEuclideanNorm (v k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [vecEuclideanNorm, vecNormSq, vecDot]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (vecEuclideanNorm_add_le _ _).trans (add_le_add le_rfl ih)

theorem continuous_classicalGradient_newtonPotential (hd : 0 < d) {H : Vec d → Vec d}
    (hH : ContDiff ℝ (⊤ : ℕ∞) H) (hHc : HasCompactSupport H) :
    Continuous (classicalGradient (newtonPotential H)) := by
  have hu := contDiff_newtonPotential hd hH hHc
  have hdc : Continuous (fderiv ℝ (newtonPotential H)) := hu.continuous_fderiv (by simp)
  exact continuous_pi fun i => hdc.clm_apply continuous_const

theorem ofReal_integral_vecEuclideanNorm_czBad (hFI : ∀ i, IntegrableOn (fun x => F x i) (I : Set (Vec d)))
    (k : S.ι) :
    ENNReal.ofReal (∫ x, vecEuclideanNorm (czBad S k x)) =
      ∫⁻ x, ENNReal.ofReal (vecEuclideanNorm (czBad S k x)) :=
  ofReal_integral_eq_lintegral_ofReal
    (integrable_vecEuclideanNorm_of_coord _ fun i => integrable_czBad_coord hFI k i)
    (Filter.Eventually.of_forall fun _ => vecEuclideanNorm_nonneg _)

theorem lintegral_bad_exterior_le (hd : 0 < d) {A : ℝ} (hA : 0 ≤ A)
    (hK : KernelHolder d newtonKernelJacobian A) (hF : VBdd F)
    (hFI : ∀ i, IntegrableOn (fun x => F x i) (I : Set (Vec d)))
    (s : Finset S.ι) {a : ℝ} (ha : 0 < a) (hsa : ∀ k ∈ s, Real.sqrt d * a ≤ czRadius S k) :
    ∫⁻ x in (czExceptional S)ᶜ,
        ENNReal.ofReal (vecEuclideanNorm
          (∑ k ∈ s, classicalGradient (newtonPotential (mollVec a (czBad S k))) x)) ≤
      ENNReal.ofReal (hormanderConst d * A * d) *
        (2 * ∫⁻ x in (I : Set (Vec d)), ENNReal.ofReal (vecEuclideanNorm (F x))) := by
  have hbad := fun k (_ : k ∈ s) => vbdd_czBad S hF k
  have hcont : ∀ k ∈ s, Continuous
      (classicalGradient (newtonPotential (mollVec a (czBad S k)))) := fun k hk =>
    continuous_classicalGradient_newtonPotential hd (contDiff_mollVec ha (hbad k hk))
      (hasCompactSupport_mollVec ha (hbad k hk))
  have hper : ∀ k ∈ s, ∫⁻ x in (czExceptional S)ᶜ,
      ENNReal.ofReal (vecEuclideanNorm
        (classicalGradient (newtonPotential (mollVec a (czBad S k))) x)) ≤
      ENNReal.ofReal (hormanderConst d * A * d) *
        ∫⁻ x, ENNReal.ofReal (vecEuclideanNorm (czBad S k x)) := by
    intro k hk
    have hr := czRadius_pos S hd k
    have hsupp : ∀ y, 2 * czRadius S k < vecEuclideanNorm (y - czCenter S k) →
        mollVec a (czBad S k) y = 0 := by
      intro y hy
      refine mollVec_eq_zero_of_support ha (fun z hz => czBad_eq_zero_of_czRadius_lt hd k hz) ?_
      linarith [hsa k hk]
    have hmean : ∀ i, ∫ y, mollVec a (czBad S k) y i = 0 := fun i => by
      rw [integral_mollVec_coord ha (hbad k hk) i, integral_czBad_coord hFI k i]
    have h1 := lintegral_gradient_newtonPotential_exterior_le hd hA hK
      (contDiff_mollVec ha (hbad k hk)) (hasCompactSupport_mollVec ha (hbad k hk)) hr hsupp hmean
    have hsub : (czExceptional S)ᶜ ⊆ (euclideanBall (czCenter S k) (2 * (2 * czRadius S k)))ᶜ :=
      compl_subset_compl.mpr (Set.subset_iUnion (fun k => czBigDilate S k) k)
    refine (lintegral_mono_set hsub).trans (h1.trans ?_)
    have h2 := integral_vecEuclideanNorm_mollVec_le ha (hbad k hk)
    have hC : 0 ≤ hormanderConst d * A := mul_nonneg (hormanderConst_nonneg d) hA
    calc ENNReal.ofReal (hormanderConst d * A * ∫ y, vecEuclideanNorm (mollVec a (czBad S k) y))
        ≤ ENNReal.ofReal (hormanderConst d * A * (d * ∫ y, vecEuclideanNorm (czBad S k y))) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left h2 hC)
      _ = ENNReal.ofReal (hormanderConst d * A * d) *
            ENNReal.ofReal (∫ y, vecEuclideanNorm (czBad S k y)) := by
          rw [← ENNReal.ofReal_mul (mul_nonneg hC (Nat.cast_nonneg d))]
          congr 1; ring
      _ = _ := by rw [ofReal_integral_vecEuclideanNorm_czBad hFI k]
  calc ∫⁻ x in (czExceptional S)ᶜ, ENNReal.ofReal (vecEuclideanNorm
          (∑ k ∈ s, classicalGradient (newtonPotential (mollVec a (czBad S k))) x))
      ≤ ∫⁻ x in (czExceptional S)ᶜ, ∑ k ∈ s, ENNReal.ofReal (vecEuclideanNorm
          (classicalGradient (newtonPotential (mollVec a (czBad S k))) x)) := by
        refine lintegral_mono fun x => ?_
        rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => vecEuclideanNorm_nonneg _]
        exact ENNReal.ofReal_le_ofReal (vecEuclideanNorm_finsetSum_le _ _)
    _ = ∑ k ∈ s, ∫⁻ x in (czExceptional S)ᶜ, ENNReal.ofReal (vecEuclideanNorm
          (classicalGradient (newtonPotential (mollVec a (czBad S k))) x)) := by
        refine lintegral_finsetSum _ fun k hk => ?_
        exact (ENNReal.measurable_ofReal.comp (measurable_vecEuclideanNorm.comp
          (hcont k hk).measurable))
    _ ≤ ∑ k ∈ s, ENNReal.ofReal (hormanderConst d * A * d) *
          ∫⁻ x, ENNReal.ofReal (vecEuclideanNorm (czBad S k x)) := Finset.sum_le_sum hper
    _ = ENNReal.ofReal (hormanderConst d * A * d) *
          ∑ k ∈ s, ∫⁻ x, ENNReal.ofReal (vecEuclideanNorm (czBad S k x)) := by
        rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal (hormanderConst d * A * d) *
          ∑' k, ∫⁻ x, ENNReal.ofReal (vecEuclideanNorm (czBad S k x)) :=
        mul_le_mul_right (ENNReal.sum_le_tsum _) _
    _ ≤ _ := mul_le_mul_right (tsum_lintegral_vecEuclideanNorm_czBad_le hFI) _

theorem measurableSet_czExceptional : MeasurableSet (czExceptional S) :=
  MeasurableSet.iUnion fun _ => measurableSet_euclideanBall _ _

theorem volume_czBigDilate (hd : 0 < d) (k : S.ι) :
    volume (czBigDilate S k) = ENNReal.ofReal (2 ^ d) * volume (czDilate S k) := by
  have hr := czRadius_pos S hd k
  have h1 : 0 < 2 * czRadius S k := by linarith
  have h2 : 0 < 2 * (2 * czRadius S k) := by linarith
  unfold czBigDilate czDilate
  rw [volume_euclideanBall_eq_unit_mul_of_pos _ h2, volume_euclideanBall_eq_unit_mul_of_pos _ h1,
    mul_pow, ENNReal.ofReal_mul (by positivity), mul_assoc]

theorem volume_czExceptional_le (hd : 0 < d) :
    volume (czExceptional S) ≤
      ENNReal.ofReal (2 ^ d) * (czDilateConst d * ENNReal.ofReal lam⁻¹ *
        ∫⁻ x in (I : Set (Vec d)), ENNReal.ofReal (vecEuclideanNorm (F x))) := by
  calc volume (czExceptional S) ≤ ∑' k, volume (czBigDilate S k) := measure_iUnion_le _
    _ = ENNReal.ofReal (2 ^ d) * ∑' k, volume (czDilate S k) := by
        rw [← ENNReal.tsum_mul_left]
        exact tsum_congr fun k => volume_czBigDilate hd k
    _ ≤ _ := mul_le_mul_right (tsum_volume_czDilate_le S hd) _

/-- **The finite-piece estimate for the mollified field.** -/
theorem volume_gradient_mollVec_gt_le (hd : 0 < d) {A : ℝ} (hA : 0 ≤ A)
    (hK : KernelHolder d newtonKernelJacobian A) (hF : VBdd F)
    (hFI : ∀ i, IntegrableOn (fun x => F x i) (I : Set (Vec d)))
    (s : Finset S.ι) {a : ℝ} (ha : 0 < a) (hsa : ∀ k ∈ s, Real.sqrt d * a ≤ czRadius S k) :
    volume {x | lam < vecEuclideanNorm (classicalGradient (newtonPotential (mollVec a F)) x)} ≤
      ENNReal.ofReal ((lam / 2)⁻¹ ^ 2 * ∫ x, vecNormSq (czTrunc S s x)) +
        (volume (czExceptional S) +
          ENNReal.ofReal (lam / 2)⁻¹ * (ENNReal.ofReal (hormanderConst d * A * d) *
            (2 * ∫⁻ x in (I : Set (Vec d)), ENNReal.ofReal (vecEuclideanNorm (F x))))) := by
  have hl : 0 < lam / 2 := half_pos S.lam_pos
  set E := czExceptional S with hE
  set Sg : Vec d → Vec d := fun x =>
    ∑ k ∈ s, classicalGradient (newtonPotential (mollVec a (czBad S k))) x with hSg
  have hbad := fun k (_ : k ∈ s) => vbdd_czBad S hF k
  have hScont : Continuous Sg := continuous_finsetSum _ fun k hk =>
    continuous_classicalGradient_newtonPotential hd (contDiff_mollVec ha (hbad k hk))
      (hasCompactSupport_mollVec ha (hbad k hk))
  set G : Set (Vec d) := {x | lam / 2 < vecEuclideanNorm
    (classicalGradient (newtonPotential (mollVec a (czTrunc S s))) x)} with hG
  set Bd : Set (Vec d) := {x | ENNReal.ofReal (lam / 2) ≤ ENNReal.ofReal (vecEuclideanNorm (Sg x))}
    with hBd
  have hsub : {x | lam < vecEuclideanNorm (classicalGradient (newtonPotential (mollVec a F)) x)} ⊆
      G ∪ (E ∪ (Bd ∩ Eᶜ)) := by
    intro x hx
    by_cases hxE : x ∈ E
    · exact Or.inr (Or.inl hxE)
    · have hdec := gradient_mollVec_decomp hd ha hF s x
      have hx' : lam < vecEuclideanNorm (classicalGradient (newtonPotential (mollVec a (czTrunc S s))) x) +
          vecEuclideanNorm (Sg x) := by
        calc lam < _ := hx
          _ ≤ _ := by rw [hdec]; exact vecEuclideanNorm_add_le _ _
      by_cases hg : lam / 2 < vecEuclideanNorm
          (classicalGradient (newtonPotential (mollVec a (czTrunc S s))) x)
      · exact Or.inl hg
      · refine Or.inr (Or.inr ⟨?_, hxE⟩)
        exact ENNReal.ofReal_le_ofReal (by linarith [not_lt.mp hg])
  have hBdvol : volume (Bd ∩ Eᶜ) ≤
      ENNReal.ofReal (lam / 2)⁻¹ * (ENNReal.ofReal (hormanderConst d * A * d) *
        (2 * ∫⁻ x in (I : Set (Vec d)), ENNReal.ofReal (vecEuclideanNorm (F x)))) := by
    have hmeas : Measurable (fun x => ENNReal.ofReal (vecEuclideanNorm (Sg x))) :=
      ENNReal.measurable_ofReal.comp (measurable_vecEuclideanNorm.comp hScont.measurable)
    have h1 : volume (Bd ∩ Eᶜ) = (volume.restrict Eᶜ) Bd := by
      rw [Measure.restrict_apply' (measurableSet_czExceptional (S := S)).compl]
    rw [h1]
    have h2 := meas_ge_le_lintegral_div (μ := volume.restrict Eᶜ) hmeas.aemeasurable
      (ε := ENNReal.ofReal (lam / 2)) (by simpa using hl) ENNReal.ofReal_ne_top
    refine h2.trans ?_
    rw [ENNReal.div_eq_inv_mul, ← ENNReal.ofReal_inv_of_pos hl]
    exact mul_le_mul_right (lintegral_bad_exterior_le hd hA hK hF hFI s ha hsa) _
  calc volume {x | lam < vecEuclideanNorm (classicalGradient (newtonPotential (mollVec a F)) x)}
      ≤ volume (G ∪ (E ∪ (Bd ∩ Eᶜ))) := measure_mono hsub
    _ ≤ volume G + (volume E + volume (Bd ∩ Eᶜ)) :=
        (measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))
    _ ≤ _ := add_le_add (volume_gradient_mollVec_trunc_gt_le hd ha hF s hl) (add_le_add le_rfl hBdvol)

end

end PDE.NewtonWeakType
