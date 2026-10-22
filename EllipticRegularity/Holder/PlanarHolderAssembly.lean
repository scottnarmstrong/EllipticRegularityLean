module

public import EllipticRegularity.Holder.PlanarHolderAssemblyBound

/-! # Assembly of planar Hölder regularity from oscillation decay -/

@[expose] public section

namespace PDE

open MeasureTheory

noncomputable section

/-- An explicit numerical constant that absorbs the exponent threshold, local
oscillation constant, globalization, and supremum bound. -/
def planarHolderAssemblyConstant : ℝ :=
  (4 * 687865857 : ℝ) ^ 2

/-- The planar Hölder conclusion with `IsEllipticFieldOn` and the homogeneous
weak equation. The displayed constant is independent of the field and
solution; its exponent has the sharp `Λ⁻¹ᐟ²` order and its norm prefactor has
the sharp `√Λ` order. -/
theorem planarHolder_of_isEllipticFieldOn
    {Lam : ℝ} {a : CoeffField 2}
    {u : H1Function (euclideanBall (0 : Vec 2) 1)}
    (hEll : IsEllipticFieldOn 1 Lam
      (euclideanBall (0 : Vec 2) 1) a)
    (hsol : IsWeakDivergenceFormSolutionOn a
      (euclideanBall (0 : Vec 2) 1) u
      (0 : Vec 2 → ℝ) (0 : Vec 2 → Vec 2)) :
    ∃ v : Vec 2 → ℝ,
      (∀ᵐ x ∂volumeOn (euclideanBall (0 : Vec 2) (1 / 2)),
        v x = u.toFun x) ∧
      ∃ M H : ℝ,
        (∀ x ∈ euclideanBall (0 : Vec 2) (1 / 2), |v x| ≤ M) ∧
        (∀ x ∈ euclideanBall (0 : Vec 2) (1 / 2),
          ∀ y ∈ euclideanBall (0 : Vec 2) (1 / 2),
            |v x - v y| ≤
              H * vecEuclideanNorm (x - y) ^
                ((planarHolderAssemblyConstant * Lam) ^ (-(1 / 2 : ℝ)))) ∧
        M + H ≤ planarHolderAssemblyConstant * Real.sqrt Lam *
          Real.sqrt (∫ x in euclideanBall (0 : Vec 2) 1,
            u.toFun x ^ 2) := by
  let C : ℝ := planarHolderAssemblyConstant
  let α : ℝ := (C * Lam) ^ (-(1 / 2 : ℝ))
  let L2 : ℝ := ∫ x in euclideanBall (0 : Vec 2) 1, u.toFun x ^ 2
  let K : ℝ := 131072 * Real.sqrt Lam * Real.sqrt L2
  let Kloc : ℝ := 2 ^ α * K
  let H : ℝ := 4096 * Kloc
  let M : ℝ := 4 * Real.sqrt L2 + H
  have hLam : 1 ≤ Lam := by
    have hA := hEll.elliptic
      (center_mem_euclideanBall (0 : Vec 2) (by norm_num : (0 : ℝ) < 1))
    exact hA.lam_le_Lam
  have hCpos : 0 < C := by norm_num [C, planarHolderAssemblyConstant]
  have hCthreshold : (4 * 687865857 : ℝ) ^ 2 ≤ C := le_rfl
  have hprod : 1 ≤ C * Lam := by nlinarith [hCthreshold, hLam]
  have hα : 0 < α := Real.rpow_pos_of_pos (by positivity) _
  have hαone : α ≤ 1 := by
    dsimp only [α]
    have h := Real.rpow_le_rpow_of_nonpos
      (by norm_num : (0 : ℝ) < 1) hprod
      (by norm_num : -(1 / 2 : ℝ) ≤ 0)
    simpa using h
  have hL2 : 0 ≤ L2 := integral_nonneg fun x => sq_nonneg (u.toFun x)
  have hK : 0 ≤ K := by positivity
  have hKloc : 0 ≤ Kloc := by positivity
  have hH : 0 ≤ H := by positivity
  have hδ : 0 < planarHolderPatchRadius := by
    norm_num [planarHolderPatchRadius, planarHolderRootRadius]
  have hlocal : ∀ z ∈ euclideanBall (0 : Vec 2) (1 / 2),
      ∃ f : Vec 2 → ℝ,
        (∀ᵐ y ∂volumeOn
          (closedCenteredAxisCube z planarHolderPatchRadius),
          f y = u.toFun y) ∧
        ∀ x ∈ closedCenteredAxisCube z planarHolderPatchRadius,
          ∀ y ∈ closedCenteredAxisCube z planarHolderPatchRadius,
            |f x - f y| ≤ Kloc * vecEuclideanNorm (x - y) ^ α := by
    intro z hz
    simpa only [Kloc, K, α, L2, C] using
      exists_planarHolder_local_representative
        hCthreshold hEll hsol z hz
  obtain ⟨v, hEq, hloc⟩ :=
    exists_glued_localHolder_representative
      (isOpen_euclideanBall (0 : Vec 2) (1 / 2))
      hδ hα hKloc hlocal
  have hGlobal := planarHolder_global_of_local hα hαone hKloc hloc
  have hSup := planarHolder_sup_bound_of_globalHolder
    hα hH hEq (by simpa only [H] using hGlobal)
  have hrootLam : 1 ≤ Real.sqrt Lam := by
    have hsq : Real.sqrt Lam ^ 2 = Lam := Real.sq_sqrt (by linarith)
    nlinarith [Real.sqrt_nonneg Lam]
  have hpow : (2 : ℝ) ^ α ≤ 2 := by
    calc
      (2 : ℝ) ^ α ≤ (2 : ℝ) ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hαone
      _ = 2 := by norm_num
  have hHbound : H ≤
      1073741824 * Real.sqrt Lam * Real.sqrt L2 := by
    dsimp only [H, Kloc, K]
    have hright : 0 ≤ 4096 * (131072 * Real.sqrt Lam * Real.sqrt L2) :=
      by positivity
    have hmul := mul_le_mul_of_nonneg_right hpow hright
    nlinarith [hL2, Real.sqrt_nonneg Lam, Real.sqrt_nonneg L2]
  have hMbound : M + H ≤ C * Real.sqrt Lam * Real.sqrt L2 := by
    have hmass : 4 * Real.sqrt L2 ≤
        4 * Real.sqrt Lam * Real.sqrt L2 := by
      have h := mul_le_mul_of_nonneg_right hrootLam (Real.sqrt_nonneg L2)
      nlinarith
    have hCbig : 2147483652 ≤ C := by
      norm_num [C, planarHolderAssemblyConstant]
    have hfactor : 0 ≤ Real.sqrt Lam * Real.sqrt L2 :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hbudget := mul_le_mul_of_nonneg_right hCbig hfactor
    dsimp only [M]
    nlinarith [hHbound, hmass, hbudget]
  refine ⟨v, hEq, M, H, ?_, ?_, ?_⟩
  · simpa only [M, L2] using hSup
  · simpa only [H, α, C] using hGlobal
  · simpa only [C, L2] using hMbound

end

end PDE
