module

public import PDEFoundation.PDE.HarmonicReplacement
public import PDEFoundation.PDE.HarmonicEnergy
public import PDEFoundation.PDE.PerturbationEnergy
public import PDEFoundation.Sobolev.H1.MeanEnergyTriangle

/-!
# One dyadic step for equations close to the Laplacian

The harmonic replacement, its exact mean-energy comparison, and the tested
perturbation identity give a bound on the half-radius gradient mean. All
analytic inputs are proved from the actual weak equation.
-/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

variable {d : ℕ}

/-- A genuine weak solution has this dyadic gradient mean-energy estimate.
The coefficient error retains its operator norm and the radius loss is exactly
`2^(d/2)`. -/
theorem sqrt_integralAverage_vecNormSq_grad_half_le
    (hd : 0 < d) {z : Vec d} {R delta : ℝ} (hR : 0 < R)
    (hdelta : 0 ≤ delta) {a : CoeffField d}
    (u : H1Function (euclideanBall z R)) {F : Vec d → Vec d}
    (ha : ∀ i j, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall z R)))
    (hclose : ∀ᵐ x ∂volumeOn (euclideanBall z R), IsMatrixPerturbationLE delta (a x) 1)
    (hF : MemVectorL2On (euclideanBall z R) F)
    (hsol : IsWeakDivergenceFormSolutionOn a (euclideanBall z R) u 0 F) :
    Real.sqrt (integralAverage (euclideanBall z (R / 2))
      (fun x => vecNormSq (u.grad x))) ≤
      (1 + delta * (2 : ℝ) ^ ((d : ℝ) / 2)) *
        Real.sqrt (integralAverage (euclideanBall z R) (fun x => vecNormSq (u.grad x))) +
      (2 : ℝ) ^ ((d : ℝ) / 2) *
        Real.sqrt (integralAverage (euclideanBall z R) (fun x => vecNormSq (F x))) := by
  let : NeZero d := ⟨hd.ne'⟩
  obtain ⟨h, w, _hvalue, hgrad, horth, henergy⟩ :=
    exists_harmonicReplacement_on_euclideanBall hd hR u
  have hharm : ∀ φ : WeakTestFunction (euclideanBall z R),
      ∫ x in euclideanBall z R, vecDot (h.grad x) (φ.grad x) = 0 := by
    intro φ
    exact horth (H10Function.ofContDiff (isOpen_euclideanBall z R)
      φ.contDiff φ.hasCompactSupport φ.tsupport_subset)
  have herr := sqrt_integralAverage_vecNormSq_replacement_error_le
    hdelta ha hclose hF hsol w (by simpa only [hgrad] using horth w)
  have hmean := sqrt_integralAverage_vecNormSq_weakHarmonic_grad_mono
    hR h hharm (by positivity : 0 < R / 2) (by linarith : R / 2 ≤ R) le_rfl
  have hmeanR : Real.sqrt (integralAverage (euclideanBall z R)
      (fun x => vecNormSq (h.grad x))) ≤
      Real.sqrt (integralAverage (euclideanBall z R)
        (fun x => vecNormSq (u.grad x))) := by
    simp only [sqrt_integralAverage_vecNormSq_eq]
    exact div_le_div_of_nonneg_right (Real.sqrt_le_sqrt henergy) (Real.sqrt_nonneg _)
  have hwrestrict := sqrt_integralAverage_vecNormSq_euclideanBall_half_le
    hR w.toH1Function.gradMemL2
  have hsub : euclideanBall z (R / 2) ⊆ euclideanBall z R :=
    euclideanBall_mono (by positivity) (by linarith)
  have htri := sqrt_integralAverage_vecNormSq_add_le
    (fun i => memLpOn_mono hsub (h.gradMemL2 i))
    (fun i => memLpOn_mono hsub (w.toH1Function.gradMemL2 i))
  have hsum (x : Vec d) : h.grad x + w.toH1Function.grad x = u.grad x := by
    rw [hgrad]
    exact sub_add_cancel _ _
  simp_rw [hsum] at htri
  have hpow : 0 ≤ (2 : ℝ) ^ ((d : ℝ) / 2) := Real.rpow_nonneg (by norm_num) _
  calc
    _ ≤ Real.sqrt (integralAverage (euclideanBall z (R / 2))
        (fun x => vecNormSq (h.grad x))) +
        Real.sqrt (integralAverage (euclideanBall z (R / 2))
          (fun x => vecNormSq (w.toH1Function.grad x))) := htri
    _ ≤ Real.sqrt (integralAverage (euclideanBall z R) (fun x => vecNormSq (u.grad x))) +
        (2 : ℝ) ^ ((d : ℝ) / 2) *
          (delta * Real.sqrt (integralAverage (euclideanBall z R)
            (fun x => vecNormSq (u.grad x))) +
            Real.sqrt (integralAverage (euclideanBall z R) (fun x => vecNormSq (F x)))) :=
      add_le_add (hmean.trans hmeanR)
        (hwrestrict.trans (mul_le_mul_of_nonneg_left herr hpow))
    _ = _ := by ring

end

end PDE
