module

public import PDEFoundation.Monotonicity.Core.HarmonicLiouvilleDeriv
public import PDEFoundation.Monotonicity.Core.HarmonicFacade
public import PDEFoundation.Monotonicity.Core.TaylorPoly

/-!
# Liouville theorem for harmonic functions of polynomial growth

A globally `C²` harmonic function on `Vec d` whose ball `L²` averages grow like `r ^ (2 N)`
is a polynomial of total degree at most `⌊N⌋₊`.
-/

@[expose] public section

namespace PDE

noncomputable section

variable {d : ℕ}

/-- A globally `C²` harmonic function is `C^∞`. -/
theorem contDiff_top_of_harmonic (hd : 0 < d) {u : Vec d → ℝ} (hu : ContDiff ℝ 2 u)
    (hharm : ∀ x, euclideanCoordLaplacian u x = 0) : ContDiff ℝ (⊤ : ℕ∞) u := by
  rw [contDiff_iff_contDiffAt]
  intro x
  have h := contDiffOn_top_of_harmonicOn hd (R := vecEuclideanNorm x + 1) hu.contDiffOn
    (fun z _ => hharm z)
  refine (h.contDiffAt ((isOpen_euclideanBall 0 _).mem_nhds ?_))
  rw [mem_euclideanBall_iff_vecEuclideanNorm_lt (by linarith [vecEuclideanNorm_nonneg x])]
  simp

/-- **Liouville theorem, ball-average form.** -/
theorem exists_mvPolynomial_of_harmonic_growth (hd : 0 < d) {u : Vec d → ℝ}
    (hu : ContDiff ℝ 2 u) (hharm : ∀ x, euclideanCoordLaplacian u x = 0) {N C : ℝ}
    (hgrow : ∀ r : ℝ, 1 ≤ r →
      integralAverage (euclideanBall (0 : Vec d) r) (fun x => u x ^ 2) ≤ C * r ^ (2 * N)) :
    ∃ p : MvPolynomial (Fin d) ℝ, p.totalDegree ≤ ⌊N⌋₊ ∧
      ∀ x, u x = MvPolynomial.eval x p := by
  have hsm := contDiff_top_of_harmonic hd hu hharm
  refine exists_mvPolynomial_of_iteratedFDeriv_eq_zero_univ hsm fun x => ?_
  refine iteratedFDeriv_eq_zero_of_iteratedCoordDeriv_eq_zero hsm _ x fun ι => ?_
  exact iteratedCoordDeriv_eq_zero_of_growth hd hsm hharm hgrow x _ (by omega)
    (by
      have := Nat.lt_floor_add_one N
      push_cast
      exact this) ι

end

end PDE
