module

public import EllipticRegularity.Schauder.ContinuousGlobal
public import EllipticRegularity.Schauder.EllipticLocalGradient
public import PDEFoundation.Measure.SchauderForcing
public import PDEFoundation.Regularity.ModulusCoefficient

/-! # Continuous-coefficient Schauder estimate in higher dimensions -/

@[expose] public section

namespace PDE

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

/-- The exact continuous-coefficient Schauder estimate specialized to
dimensions at least two. -/
theorem exists_continuousCoefficientCalpha_constant_higherDimensional
    {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ}
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (ω : ℝ → ℝ) (hω0 : ω 0 = 0)
    (_hωnonneg : ∀ t : ℝ, 0 ≤ t → 0 ≤ ω t)
    (hωlim : Tendsto ω (𝓝[>] (0 : ℝ)) (𝓝 0)) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : CoeffField d,
      ContinuousOn a (euclideanClosedBall (0 : Vec d) 1) →
      (∀ x ∈ euclideanClosedBall (0 : Vec d) 1,
        IsEllipticMatrix 1 Λ (a x)) →
      (∀ x ∈ euclideanClosedBall (0 : Vec d) 1,
        ∀ y ∈ euclideanClosedBall (0 : Vec d) 1,
        IsMatrixPerturbationLE (ω (vecEuclideanNorm (x - y))) (a x) (a y)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      ∀ F : Vec d → Vec d,
      (∀ i : Fin d, AEStronglyMeasurable (fun x => F x i)
        (volumeOn (euclideanBall (0 : Vec d) 1))) →
      ∀ hF : MemLp (fun x => vecEuclideanNorm (F x))
        (ENNReal.ofReal ((d : ℝ) / (1 - α)))
        (volumeOn (euclideanBall (0 : Vec d) 1)),
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u 0 F →
      HasEuclideanHolderRepresentativeOn (euclideanBall (0 : Vec d) (1 / 2))
        u.toFun α
        ((C / α) *
          (Real.sqrt (∫ x in euclideanBall (0 : Vec d) 1,
            vecNormSq (u.grad x)) +
          euclideanFieldLpNormOn (euclideanBall (0 : Vec d) 1)
            (ENNReal.ofReal ((d : ℝ) / (1 - α))) F hF / (1 - α))) := by
  let δ : ℝ := (2 : ℝ) ^ (-3 - (d : ℝ) / 2) * (1 - α)
  have hgap : 0 < 1 - α := sub_pos.mpr hα1
  have hδ : 0 < δ := mul_pos (Real.rpow_pos_of_pos (by norm_num) _) hgap
  obtain ⟨R, hR, hRquarter, hfreeze⟩ :=
    exists_uniform_matrix_oscillation_radius (d := d) hω0 hωlim hδ
  obtain ⟨Clocal, hClocal, hlocalGradient⟩ :=
    exists_elliptic_local_gradient_constant hd Λ
  let V : ℝ := Real.sqrt (volume (euclideanBall (0 : Vec d) 1)).toReal
  let P : ℝ := R ^ (1 - α) * R ^ (-(d : ℝ) / 2) / V
  let Price : ℝ := schauderForcingVolumePrice d
  let K₀ : ℝ := Clocal * (P + Price + 1)
  have hV : 0 < V := by
    dsimp only [V]
    exact Real.sqrt_pos.mpr
      (volume_euclideanBall_toReal_pos (0 : Vec d) (by norm_num))
  have hP : 0 ≤ P := by
    dsimp only [P]
    positivity
  have hPrice : 0 < Price := by
    exact schauderForcingVolumePrice_pos d
  have hK₀ : 0 < K₀ := by
    dsimp only [K₀]
    positivity
  obtain ⟨C, hC, hglobal⟩ :=
    exists_continuousCalpha_constant_of_local_gradient_bounds
      hd hα0 hα1 hR hRquarter hK₀.le
  refine ⟨C, hC, ?_⟩
  intro a ha hell hmod u F hFcoord hF hsol
  let N := euclideanFieldLpNormOn (euclideanBall (0 : Vec d) 1)
    (ENNReal.ofReal ((d : ℝ) / (1 - α))) F hF
  let Graw := Real.sqrt (∫ x in euclideanBall (0 : Vec d) 1,
    vecNormSq (u.grad x))
  have hN : 0 ≤ N := by
    dsimp only [N, euclideanFieldLpNormOn]
    rw [lpNormOn_eq_toReal]
    exact ENNReal.toReal_nonneg
  have hGraw : 0 ≤ Graw := Real.sqrt_nonneg _
  have hp : 2 ≤ schauderSourceExponent d α :=
    two_le_schauderSourceExponent hd hα0 hα1
  have hFL2 : MemVectorL2On (euclideanBall (0 : Vec d) 1) F := by
    apply memVectorL2On_euclideanBall_of_memLp_vecEuclideanNorm hp
      (0 : Vec d) (by norm_num) (Set.Subset.refl _)
    · simpa only [schauderSourceExponent] using hF
    · exact hFcoord
  apply hglobal u hN
  intro z hz r hr hrR
  have hRhalf : R ≤ 1 / 2 := hRquarter.trans (by norm_num)
  have hBRunit : euclideanBall z R ⊆ euclideanBall (0 : Vec d) 1 :=
    (euclideanBall_mono hR.le hRhalf).trans
      (euclideanBall_half_subset_unit_of_center_mem_half hz)
  have hBRclosed : euclideanBall z R ⊆
      euclideanClosedBall (0 : Vec d) 1 :=
    hBRunit.trans (euclideanBall_subset_euclideanClosedBall _ _)
  have haLocal : ContinuousOn a (euclideanBall z R) := ha.mono hBRclosed
  have hAz : IsEllipticMatrix 1 Λ (a z) := by
    exact hell z (hBRclosed (center_mem_euclideanBall z hR))
  have hclose : ∀ x ∈ euclideanBall z R,
      IsMatrixPerturbationLE δ (a x) (a z) := by
    have hpair := hfreeze (euclideanClosedBall (0 : Vec d) 1) a hmod z hBRclosed
    intro x hx
    exact hpair x hx z (center_mem_euclideanBall z hR)
  have hFLocal : MemVectorL2On (euclideanBall z R) F := fun i =>
    (hFL2 i).mono_measure (Measure.restrict_mono hBRunit le_rfl)
  let uR := u.restrict (isOpen_euclideanBall z R) hBRunit
  have hsolR : IsWeakDivergenceFormSolutionOn a (euclideanBall z R) uR 0 F := by
    exact hsol.restrict (isOpen_euclideanBall _ _) (isOpen_euclideanBall _ _) hBRunit
  have hM : 0 ≤ Price * N := mul_nonneg hPrice.le hN
  have hforce : ∀ q : ℝ, 0 < q → q ≤ R →
      q ^ (1 - α) * Real.sqrt (integralAverage (euclideanBall z q)
        (fun x => vecNormSq (F x))) ≤ Price * N := by
    intro q hq hqR
    have hBqunit : euclideanBall z q ⊆ euclideanBall (0 : Vec d) 1 :=
      (euclideanBall_mono hq.le (hqR.trans hRhalf)).trans
        (euclideanBall_half_subset_unit_of_center_mem_half hz)
    have hf := schauder_forcing_euclideanBall_le_unitLp hd hα0 hα1 z hq
      hBqunit (by simpa only [schauderSourceExponent] using hF)
    simpa only [Price, N, schauderSourceExponent] using hf
  have hraw := hlocalGradient hR hα0 hα1 hδ.le le_rfl hM haLocal hAz hclose
    hFLocal uR hsolR hforce r hr hrR
  have henergy := sqrt_integralAverage_vecNormSq_interiorBall_le
    hz hR hRhalf u.gradMemL2
  have hmeanUnit : Real.sqrt (integralAverage (euclideanBall (0 : Vec d) 1)
      (fun x => vecNormSq (u.grad x))) = Graw / V := by
    dsimp only [Graw, V]
    exact sqrt_integralAverage_vecNormSq_eq _ _
  have hM0 : R ^ (1 - α) *
      Real.sqrt (integralAverage (euclideanBall z R)
        (fun x => vecNormSq (u.grad x))) ≤ P * Graw := by
    calc
      _ ≤ R ^ (1 - α) * (R ^ (-(d : ℝ) / 2) *
          Real.sqrt (integralAverage (euclideanBall (0 : Vec d) 1)
            (fun x => vecNormSq (u.grad x)))) :=
        mul_le_mul_of_nonneg_left henergy (Real.rpow_nonneg hR.le _)
      _ = P * Graw := by rw [hmeanUnit]; dsimp only [P]; ring
  have hNgap : 0 ≤ N / (1 - α) := div_nonneg hN hgap.le
  have hinside : P * Graw + Price * (N / (1 - α)) ≤
      (P + Price + 1) * (Graw + N / (1 - α)) := by
    nlinarith only [mul_nonneg hP hNgap, mul_nonneg hPrice.le hGraw,
      hP, hPrice.le, hGraw, hNgap]
  calc
    _ ≤ Clocal * (R ^ (1 - α) *
          Real.sqrt (integralAverage (euclideanBall z R)
            (fun x => vecNormSq (u.grad x))) +
        (Price * N) / (1 - α)) := by
      simpa only [uR, H1Function.restrict_grad] using hraw
    _ ≤ Clocal * (P * Graw + Price * (N / (1 - α))) := by
      apply mul_le_mul_of_nonneg_left _ hClocal.le
      rw [mul_div_assoc]
      exact add_le_add hM0 le_rfl
    _ ≤ Clocal * ((P + Price + 1) * (Graw + N / (1 - α))) :=
      mul_le_mul_of_nonneg_left hinside hClocal.le
    _ = K₀ * (Graw + N / (1 - α)) := by dsimp only [K₀]; ring

end

end PDE
