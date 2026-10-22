module

public import EllipticRegularity.DeGiorgi.Assembly.LocalHarnack
public import EllipticRegularity.DeGiorgi.Assembly.HarnackChain

/-!
# The Harnack inequality (assembly)

Theorem 4.18, from the weak Harnack inequality, Moser's `L^∞` estimate and De Giorgi's
continuity, through the local Harnack inequality and the 17-step chain.
-/

@[expose] public section

open scoped ENNReal Pointwise

namespace PDE.DGNMAssembly

open MeasureTheory Filter

variable {d : ℕ}

/-- **Harnack inequality** (Theorem 4.18). -/
theorem exists_harnack_constant_full (d : ℕ) (hd : 3 ≤ d) (hWH : WeakHarnackConcl d)
    (hMax : MoserLocalMaxConcl d) (hDG : DeGiorgiHolderConcl d) (hSol : SolAffineTransfer d) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Λ : ℝ) (a : CoeffField d),
      (∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) 1))) →
      (∀ x ∈ euclideanBall (0 : Vec d) 1, IsEllipticMatrix 1 Λ (a x)) →
      ∀ u : H1Function (euclideanBall (0 : Vec d) 1),
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) 1)), 0 < u.toFun x) →
      IsWeakDivergenceFormSolutionOn a (euclideanBall (0 : Vec d) 1) u (0 : Vec d → ℝ) 0 →
        essSup (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) ≤
          ENNReal.ofReal (Real.exp (C * Real.sqrt Λ)) *
            essInf (fun x => ENNReal.ofReal (u.toFun x)) (volumeOn (euclideanBall (0 : Vec d) (1 / 2))) := by
  obtain ⟨Cl, hloc⟩ := local_harnack d hd hWH hMax hSol
  obtain ⟨CD, hCD, hDGq⟩ := hDG
  refine ⟨max 1 (17 * Cl), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  intro Λ a hmeas hell u hpos hsol
  have hΛ1 : 1 ≤ Λ := one_le_of_elliptic hell
  obtain ⟨α, hα0, hα1, hαexp, hDGa⟩ := hDGq Λ hΛ1
  obtain ⟨v, M₀, M₁, hv_ae, hM₀, hM₁, hvbd, hHold, hbound⟩ := hDGa a hmeas hell u hsol
  set B : Set (Vec d) := euclideanBall (0 : Vec d) (1 / 2) with hB
  have hBopen : IsOpen B := isOpen_euclideanBall _ _
  have hvcont : ContinuousOn v B := continuousOn_of_euclideanHolder hα0 hHold
  have hposB := ae_pos_ball (u := u) hpos (ρ := 1 / 2) (by norm_num) (by norm_num)
  have hvpos : ∀ᵐ x ∂(volumeOn B), 0 < v x := by
    filter_upwards [hv_ae, hposB] with x h1 h2
    rw [h1]; exact h2
  have hvnn : ∀ z ∈ B, 0 ≤ v z := fun z hz =>
    nonneg_of_continuousOn_ae_pos hBopen hvcont hvpos hz
  set K : ℝ := Real.exp (Cl * Real.sqrt Λ) with hK
  have hKpos : 0 < K := Real.exp_pos _
  have hvu : (fun x => ENNReal.ofReal (v x)) =ᵐ[volumeOn B] fun x => ENNReal.ofReal (u.toFun x) := by
    filter_upwards [hv_ae] with x hx
    rw [hx]
  have hlocv : ∀ x₀ ∈ B, ∀ y ∈ euclideanBall x₀ (1 / 16) ∩ B,
      ∀ z ∈ euclideanBall x₀ (1 / 16) ∩ B, v y ≤ K * v z := by
    intro x₀ hx₀ y hy z hz
    have hW : IsOpen (euclideanBall x₀ (1 / 16) ∩ B) :=
      (isOpen_euclideanBall _ _).inter hBopen
    have hWU : euclideanBall x₀ (1 / 16) ∩ B ⊆ euclideanBall x₀ (1 / 16) := Set.inter_subset_left
    have hvW : ContinuousOn v (euclideanBall x₀ (1 / 16) ∩ B) :=
      hvcont.mono Set.inter_subset_right
    have hvuW : (fun x => ENNReal.ofReal (v x)) =ᵐ[volumeOn (euclideanBall x₀ (1 / 16) ∩ B)]
        fun x => ENNReal.ofReal (u.toFun x) :=
      ae_mono (Measure.restrict_mono Set.inter_subset_right le_rfl) hvu
    have h1 := ofReal_le_essSup_of_cont hW hWU hvW hvuW hy
    have h2 := essInf_le_ofReal_of_cont hW hWU hvW hvuW hz
    have h3 := hloc Λ a hmeas hell u hpos hsol x₀ hx₀
    have h4 : ENNReal.ofReal (v y) ≤ ENNReal.ofReal K * ENNReal.ofReal (v z) :=
      h1.trans (h3.trans (by gcongr))
    rw [← ENNReal.ofReal_mul hKpos.le] at h4
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hKpos.le (hvnn z hz.2))).1 h4
  have hchain : ∀ y ∈ B, ∀ z ∈ B, v y ≤ K ^ 17 * v z := fun y hy z hz =>
    chain_bound hKpos hlocv hy hz
  have hK17 : K ^ 17 ≤ Real.exp (max 1 (17 * Cl) * Real.sqrt Λ) := by
    rw [hK, ← Real.exp_nat_mul]
    apply Real.exp_le_exp.2
    have hs : 0 ≤ Real.sqrt Λ := Real.sqrt_nonneg _
    push_cast
    nlinarith [le_max_right 1 (17 * Cl)]
  have hK17pos : 0 < K ^ 17 := pow_pos hKpos 17
  have hIv : ∀ y ∈ B, ENNReal.ofReal (v y) ≤ ENNReal.ofReal (K ^ 17) *
      essInf (fun x => ENNReal.ofReal (v x)) (volumeOn B) := by
    intro y hy
    have hle : ENNReal.ofReal ((K ^ 17)⁻¹ * v y) ≤
        essInf (fun x => ENNReal.ofReal (v x)) (volumeOn B) := by
      exact le_essInf_of_ae_le _ (ae_restrict_of_forall_mem hBopen.measurableSet fun z hz =>
        ENNReal.ofReal_le_ofReal (by rw [inv_mul_le_iff₀ hK17pos]; exact hchain y hy z hz))
    calc ENNReal.ofReal (v y) = ENNReal.ofReal (K ^ 17) * ENNReal.ofReal ((K ^ 17)⁻¹ * v y) := by
          rw [← ENNReal.ofReal_mul hK17pos.le, ← mul_assoc, mul_inv_cancel₀ hK17pos.ne', one_mul]
      _ ≤ _ := by gcongr
  have hsup : essSup (fun x => ENNReal.ofReal (v x)) (volumeOn B) ≤ ENNReal.ofReal (K ^ 17) *
      essInf (fun x => ENNReal.ofReal (v x)) (volumeOn B) := by
    exact essSup_le_of_ae_le _ (ae_restrict_of_forall_mem hBopen.measurableSet hIv)
  rw [← essSup_congr_ae hvu, ← essInf_congr_ae hvu]
  refine hsup.trans ?_
  gcongr

end PDE.DGNMAssembly
