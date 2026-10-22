module

public import EllipticRegularity.Guerra.Weak.Gradient
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Topology.Separation.CompletelyRegular

/-!
# Guerra sharpness: the weak equation on `B₁`

The smooth flux `J = guerraFlux` is classically divergence-free off the origin and lies in
`L²(B₁)` (it is half of `2B ∇u`, and `2B` is uniformly elliptic). The point-removal lemma
`integral_vecDot_grad_eq_zero_of_classical_divergence_punctured` gives `∫ J·∇φ = 0` for smooth
compactly supported tests; hence any measurable uniformly elliptic `a` with `a ∇u = c J` off the
origin makes every `H¹` function with weak gradient `∇u` (namely `u` and `1 + u`) an `L²`-data weak
solution, which extends to all `H¹₀` tests by `IsWeakDivergenceFormL2SolutionOn.toH10SolutionOn`.
-/

@[expose] public section

open scoped BigOperators
open MeasureTheory

namespace PDE.Guerra

noncomputable section

variable {d : ℕ}

/-- A coefficient field with measurable entries that is elliptic on a measurable set `U` is an
elliptic field on `U` in the sense of `IsEllipticFieldOn`. -/
theorem isEllipticFieldOn_of_measurable {lam Lam : ℝ} {U : Set (Vec d)} {a : CoeffField d}
    (hU : MeasurableSet U) (hmeas : ∀ i k : Fin d, Measurable fun x => a x i k)
    (hell : ∀ x ∈ U, IsEllipticMatrix lam Lam (a x)) : IsEllipticFieldOn lam Lam U a := by
  classical
  refine ⟨?_, hell⟩
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun k => ?_
  exact Measurable.ite hU (hmeas i k) measurable_const

theorem measurable_nonsymField_apply {γ : ℝ} {h : ℝ → ℝ} (hh : Measurable h) (j i k : Fin d) :
    Measurable (fun x : Vec d => nonsymField γ h j x i k) := by
  simp only [nonsymField, Matrix.smul_apply, smul_eq_mul]
  exact measurable_const.mul (measurable_fieldMatrix_apply hh j i k)

/-- The nonsymmetric field `2B` is a measurable elliptic field on `B₁` with `Λ = (40γ)²`. -/
theorem isEllipticFieldOn_nonsymField (hd : 3 ≤ d) {γ : ℝ} (hγ : 1 ≤ γ) (j : Fin d) :
    IsEllipticFieldOn 1 ((40 * γ) ^ 2) (ball1 d) (nonsymField γ (hcorr d γ) j) :=
  isEllipticFieldOn_of_measurable (measurableSet_euclideanBall 0 1)
    (measurable_nonsymField_apply (measurable_hcorr d γ) j)
    fun x _ => isEllipticMatrix_nonsymField hγ j x fun _ ht => abs_hcorr_le hd hγ ht

/-- The smooth flux `J` lies in `L²(B₁)`. -/
theorem memVectorL2On_guerraFlux (hd : 3 ≤ d) {γ : ℝ} (hγ : 1 ≤ γ) (j : Fin d) :
    MemVectorL2On (ball1 d) (guerraFlux d (alpha d γ) (phi γ) j) := by
  have hP := profileData_guerra hd hγ
  have hα1 := alpha_lt_one hd hγ
  have hN := memVectorL2On_matVecMul_of_isEllipticFieldOn (isEllipticFieldOn_nonsymField hd hγ j)
    (gradMemL2On_gradU hd hγ hP.alpha_pos hα1 j)
  intro i
  refine ((hN i).const_mul (1 / 2 : ℝ)).ae_eq ?_
  filter_upwards [ae_ne_zero_restrict (by omega) (ball1 d)] with x hx
  rw [matVecMul_nonsymField_gradU hP j hx]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- `∫ J·∇φ = 0` for every smooth compactly supported test on `B₁`. -/
theorem integral_guerraFlux_grad_eq_zero (hd : 3 ≤ d) {γ : ℝ} (hγ : 1 ≤ γ) (j : Fin d)
    (φ : WeakTestFunction (ball1 d)) :
    ∫ x in ball1 d, vecDot (guerraFlux d (alpha d γ) (phi γ) j x) (φ.grad x) = 0 := by
  have hP := profileData_guerra hd hγ
  exact integral_vecDot_grad_eq_zero_of_classical_divergence_punctured (by omega)
    (isOpen_euclideanBall 0 1) _ (memVectorL2On_guerraFlux hd hγ j)
    (contDiffOn_guerraFlux_punctured hP j (ball1 d))
    (sum_classicalGradient_guerraFlux_punctured hP j (ball1 d)) φ

theorem vecDot_zero_left' (v : Vec d) : vecDot (0 : Vec d) v = 0 := by
  simp [vecDot]

/-- The master weak-solution lemma: an elliptic measurable field `a` with `a ∇u = c J` off the
origin makes every `H¹(B₁)` function with weak gradient `∇u` an all-`H¹₀` weak solution of
`-div(a ∇w) = 0`. -/
theorem isWeakDivergenceFormH10SolutionOn_of_flux (hd : 3 ≤ d) {γ : ℝ} (hγ : 1 ≤ γ)
    (j : Fin d) {lam Lam c : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (ball1 d) a)
    (hflux : ∀ x : Vec d, x ≠ 0 →
      matVecMul (a x) (gradU (alpha d γ) (phi γ) j x) =
        c • guerraFlux d (alpha d γ) (phi γ) j x)
    (v : H1Function (ball1 d)) (hv : v.grad = gradU (alpha d γ) (phi γ) j) :
    IsWeakDivergenceFormH10SolutionOn a (ball1 d) v (0 : Vec d → ℝ) 0 := by
  have hdata : DivergenceFormL2DataOn a (ball1 d) v (0 : Vec d → ℝ) 0 :=
    DivergenceFormL2DataOn.of_isEllipticFieldOn hEll MemLp.zero fun _ => MemLp.zero
  refine IsWeakDivergenceFormL2SolutionOn.toH10SolutionOn ⟨hdata, fun φ => ?_⟩
  have hrhs : (∫ x in ball1 d, (0 : Vec d → ℝ) x * φ x) -
      ∫ x in ball1 d, vecDot ((0 : Vec d → Vec d) x) (φ.grad x) = 0 := by
    simp only [Pi.zero_apply, zero_mul, integral_zero, vecDot_zero_left', sub_zero]
  rw [hrhs]
  have hae : (fun x => vecDot (matVecMul (a x) (v.grad x)) (φ.grad x)) =ᵐ[volume.restrict (ball1 d)]
      fun x => c * vecDot (guerraFlux d (alpha d γ) (phi γ) j x) (φ.grad x) := by
    filter_upwards [ae_ne_zero_restrict (by omega) (ball1 d)] with x hx
    rw [hv, hflux x hx, vecDot_smul_left]
  rw [integral_congr_ae hae, integral_const_mul, integral_guerraFlux_grad_eq_zero hd hγ j φ,
    mul_zero]

/-- Both `u` and `1 + u` are all-`H¹₀` weak solutions for any such field. -/
theorem weak_solutions_of_flux (hd : 3 ≤ d) {γ : ℝ} (hγ : 1 ≤ γ)
    (j : Fin d) {lam Lam c : ℝ} {a : CoeffField d}
    (hEll : IsEllipticFieldOn lam Lam (ball1 d) a)
    (hflux : ∀ x : Vec d, x ≠ 0 →
      matVecMul (a x) (gradU (alpha d γ) (phi γ) j x) =
        c • guerraFlux d (alpha d γ) (phi γ) j x) :
    (∃ v : H1Function (ball1 d), v.toFun = uProf j γ (alpha d γ) ∧
      IsWeakDivergenceFormH10SolutionOn a (ball1 d) v (0 : Vec d → ℝ) 0) ∧
    (∃ w : H1Function (ball1 d), w.toFun = (fun x => 1 + uProf j γ (alpha d γ) x) ∧
      IsWeakDivergenceFormH10SolutionOn a (ball1 d) w (0 : Vec d → ℝ) 0) := by
  have hα := alpha_pos hd hγ
  have hα1 := alpha_lt_one hd hγ
  obtain ⟨v, hv, hvg⟩ := exists_h1Function_const_add hd hγ hα hα1 j 0
  obtain ⟨w, hw, hwg⟩ := exists_h1Function_const_add hd hγ hα hα1 j 1
  refine ⟨⟨v, ?_, isWeakDivergenceFormH10SolutionOn_of_flux hd hγ j hEll hflux v hvg⟩,
    ⟨w, hw, isWeakDivergenceFormH10SolutionOn_of_flux hd hγ j hEll hflux w hwg⟩⟩
  rw [hv]
  funext x
  simp

/-! ### The symmetric field -/

theorem measurable_cMatrix {γ : ℝ} {h : ℝ → ℝ} (hh : Measurable h) (j : Fin d) :
    Measurable (fun x : Vec d => (cMatrix γ h j x : Fin d → Fin d → ℝ)) := by
  refine measurable_pi_iff.mpr fun i => measurable_pi_iff.mpr fun k => ?_
  simp only [cMatrix, Matrix.smul_apply, smul_eq_mul]
  exact measurable_const.mul (measurable_fieldMatrix_apply hh j i k)

/-- Entrywise measurability of the symmetric field, from the joint measurability of the
symmetrizer. -/
theorem measurable_symField_apply {γ : ℝ} {h : ℝ → ℝ} (hh : Measurable h) (j : Fin d)
    {S : Mat d → Vec d → Mat d}
    (hSmeas : ∀ i k : Fin d, Measurable
      (fun q : (Fin d → Fin d → ℝ) × Vec d => S (Matrix.of q.1) q.2 i k))
    {G : Vec d → Vec d} (hG : Measurable G) (i k : Fin d) :
    Measurable (fun x : Vec d => symField γ h j S G x i k) := by
  classical
  have hcomp : Measurable (fun x : Vec d => S (cMatrix γ h j x) (G x) i k) :=
    (hSmeas i k).comp ((measurable_cMatrix hh j).prodMk hG)
  have e : (fun x : Vec d => symField γ h j S G x i k) = fun x =>
      if x = 0 then ((2 : ℝ) • (1 : Mat d)) i k else (80 * γ) * S (cMatrix γ h j x) (G x) i k := by
    funext x
    by_cases hx : x = 0
    · simp [symField, hx]
    · simp [symField, hx]
  rw [e]
  exact Measurable.ite (measurableSet_singleton 0) measurable_const
    (measurable_const.mul hcomp)

end

end PDE.Guerra
