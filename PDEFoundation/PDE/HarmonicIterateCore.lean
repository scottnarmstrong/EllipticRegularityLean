module

public import PDEFoundation.Analysis.IteratedCoordDeriv
public import PDEFoundation.Geometry.EuclideanBall.Interior
public import PDEFoundation.PDE.HarmonicMeanValueLocal

/-! # Conditional iteration of a first derivative estimate -/

@[expose] public section

namespace PDE

open Set
open scoped Topology

noncomputable section

private theorem iteratedCoordDerivList_contDiffOn_and_harmonic
    {d : ℕ} {U : Set (Vec d)} (hU : IsOpen U)
    {v : Vec d → ℝ} (hv : ContDiffOn ℝ (⊤ : ℕ∞) v U)
    (hharm : ∀ z ∈ U, euclideanCoordLaplacian v z = 0) :
    ∀ is : List (Fin d),
      ContDiffOn ℝ (⊤ : ℕ∞) (iteratedCoordDerivList is v) U ∧
        ∀ z ∈ U, euclideanCoordLaplacian (iteratedCoordDerivList is v) z = 0 := by
  intro is
  induction is with
  | nil =>
      exact ⟨by simpa [iteratedCoordDerivList] using hv,
        by simpa [iteratedCoordDerivList] using hharm⟩
  | cons i is ih =>
      exact contDiffOn_euclideanCoordDeriv_and_harmonic hU ih.1 ih.2 i

private theorem iteratedCoordDerivList_pointwise_bound
    {d : ℕ} {K ρ M : ℝ} (hK : 0 ≤ K) (hρ : 0 < ρ)
    {v : Vec d → ℝ} {x : Vec d} {R : ℝ}
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v (euclideanBall x R))
    (hharm : ∀ z ∈ euclideanBall x R,
      euclideanCoordLaplacian v z = 0)
    (hFirst : ∀ (w : Vec d → ℝ) (y : Vec d) (t s M : ℝ) (i : Fin d),
      ContDiffOn ℝ (⊤ : ℕ∞) w (euclideanBall y t) →
      (∀ z ∈ euclideanBall y t, euclideanCoordLaplacian w z = 0) →
      0 < s → s < t →
      (∀ z ∈ euclideanBall y s, |w z| ≤ M) →
      |euclideanCoordDeriv i w y| ≤ K / s * M)
    {m : ℕ} (hm : 1 ≤ m) (hρR : ρ < R)
    (hM : ∀ z ∈ euclideanClosedBall x ρ, |v z| ≤ M)
    (A : ℝ) (hA : A = K * (m : ℝ) / ρ)
    (hMnonneg : 0 ≤ M)
    (L : List (Fin d)) (hL : L.length ≤ m) :
    ∀ y ∈ euclideanClosedBall x
        (ρ * (1 - (L.length : ℝ) / (m : ℝ))),
      |iteratedCoordDerivList L v y| ≤ A ^ L.length * M ∧
        0 ≤ A ^ L.length * M := by
  have hA_nonneg : 0 ≤ A := by
    rw [hA]
    exact div_nonneg (mul_nonneg hK (Nat.cast_nonneg _)) hρ.le
  induction L with
  | nil =>
      intro y hy
      have hyρ : y ∈ euclideanClosedBall x ρ := by
        simpa using hy
      have hbound : |iteratedCoordDerivList [] v y| ≤ A ^ 0 * M := by
        simpa [iteratedCoordDerivList] using hM y hyρ
      exact ⟨hbound, by simpa using hMnonneg⟩
  | cons i L ih =>
      intro y hy
      have hLsucc : L.length + 1 ≤ m := by simpa using hL
      have hLlt : L.length < m := by omega
      have hmpos : 0 < (m : ℝ) := by
        exact_mod_cast (show 0 < m by omega)
      have hlenCast : (L.length : ℝ) < (m : ℝ) := by
        exact_mod_cast hLlt
      have hlenRatio : (L.length : ℝ) / (m : ℝ) < 1 :=
        (div_lt_one hmpos).2 hlenCast
      have hnextCast : ((L.length + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by
        exact_mod_cast hLsucc
      have hnextRatio : ((L.length + 1 : ℕ) : ℝ) / (m : ℝ) ≤ 1 :=
        (div_le_one hmpos).2 hnextCast
      let rPrev : ℝ := ρ * (1 - (L.length : ℝ) / (m : ℝ))
      let rNext : ℝ := ρ * (1 - ((L.length + 1 : ℕ) : ℝ) / (m : ℝ))
      let s : ℝ := ρ / (m : ℝ)
      have hrPrev : 0 < rPrev := by
        dsimp [rPrev]
        exact mul_pos hρ (sub_pos.mpr hlenRatio)
      have hrNext : 0 ≤ rNext := by
        dsimp [rNext]
        exact mul_nonneg hρ.le (sub_nonneg.mpr hnextRatio)
      have hs : 0 < s := by
        dsimp [s]
        exact div_pos hρ hmpos
      have hRadius : rNext + s = rPrev := by
        dsimp [rNext, s, rPrev]
        field_simp [hmpos.ne']
        simp only [Nat.cast_add, Nat.cast_one]
        ring
      have hyNorm : vecEuclideanNorm (y - x) ≤ rNext := by
        have hy' := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hrNext).mp hy
        exact hy'
      have hBallSmall : euclideanBall y s ⊆ euclideanClosedBall x rPrev := by
        have hbound : vecEuclideanNorm (y - x) + s ≤ rPrev := by
          calc
            vecEuclideanNorm (y - x) + s ≤ rNext + s := by
              simpa [add_comm] using add_le_add_right hyNorm s
            _ = rPrev := hRadius
        exact (euclideanBall_subset_of_center_norm_add_le hs hrPrev hbound).trans
          (euclideanBall_subset_euclideanClosedBall x rPrev)
      have hysRho : vecEuclideanNorm (y - x) + s ≤ ρ := by
        have hratioNonneg : 0 ≤ (L.length : ℝ) / (m : ℝ) :=
          div_nonneg (Nat.cast_nonneg _) hmpos.le
        have hprevLe : rPrev ≤ ρ := by
          dsimp [rPrev]
          nlinarith [hratioNonneg, hρ]
        calc
          vecEuclideanNorm (y - x) + s ≤ rNext + s := by
            simpa [add_comm] using add_le_add_right hyNorm s
          _ = rPrev := hRadius
          _ ≤ ρ := hprevLe
      have hysR : vecEuclideanNorm (y - x) + s < R :=
        lt_of_le_of_lt hysRho (by linarith)
      let t : ℝ := R - vecEuclideanNorm (y - x)
      have ht : 0 < t := by
        dsimp [t]
        linarith
      have hst : s < t := by
        dsimp [t]
        linarith
      have hOuter : euclideanBall y t ⊆ euclideanBall x R := by
        apply euclideanBall_subset_of_center_norm_add_le ht
          (lt_trans hρ hρR)
        dsimp [t]
        linarith
      have hlocal := iteratedCoordDerivList_contDiffOn_and_harmonic
        (isOpen_euclideanBall x R) hv hharm L
      have hw : ContDiffOn ℝ (⊤ : ℕ∞)
          (iteratedCoordDerivList L v) (euclideanBall y t) := hlocal.1.mono hOuter
      have hwharm : ∀ z ∈ euclideanBall y t,
          euclideanCoordLaplacian (iteratedCoordDerivList L v) z = 0 := by
        intro z hz
        exact hlocal.2 z (hOuter hz)
      have hsmall : ∀ z ∈ euclideanBall y s,
          |iteratedCoordDerivList L v z| ≤ A ^ L.length * M := by
        intro z hz
        exact (ih (by omega) z (hBallSmall hz)).1
      have hderiv := hFirst (iteratedCoordDerivList L v) y t s
        (A ^ L.length * M) i hw hwharm hs hst hsmall
      have hks : K / s = A := by
        rw [hA]
        dsimp [s]
        field_simp [hmpos.ne', hρ.ne']
      have hbound :
          |euclideanCoordDeriv i (iteratedCoordDerivList L v) y| ≤
            A ^ (L.length + 1) * M := by
        calc
          |euclideanCoordDeriv i (iteratedCoordDerivList L v) y|
              ≤ K / s * (A ^ L.length * M) := hderiv
          _ = A ^ (L.length + 1) * M := by
            rw [hks, pow_succ]
            ring
      exact ⟨by simpa [iteratedCoordDerivList] using hbound,
        by
          simpa only [List.length_cons] using
            (mul_nonneg (pow_nonneg hA_nonneg (L.length + 1)) hMnonneg)⟩

/-- Iterated coordinate derivatives are bounded by iterating a supplied
first-derivative estimate over nested interior balls.  `hFirst` is the explicit
external estimate to be instantiated by the first-derivative estimate. -/
theorem abs_iteratedCoordDeriv_le_of_firstDerivEstimate
    {d : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (hFirst : ∀ (w : Vec d → ℝ) (y : Vec d) (t s M : ℝ) (i : Fin d),
      ContDiffOn ℝ (⊤ : ℕ∞) w (euclideanBall y t) →
      (∀ z ∈ euclideanBall y t, euclideanCoordLaplacian w z = 0) →
      0 < s → s < t →
      (∀ z ∈ euclideanBall y s, |w z| ≤ M) →
      |euclideanCoordDeriv i w y| ≤ K / s * M)
    {v : Vec d → ℝ} {x : Vec d} {R ρ M : ℝ}
    (hv : ContDiffOn ℝ (⊤ : ℕ∞) v (euclideanBall x R))
    (hharm : ∀ z ∈ euclideanBall x R,
      euclideanCoordLaplacian v z = 0)
    (hρ : 0 < ρ) (hρR : ρ < R)
    (hM : ∀ z ∈ euclideanClosedBall x ρ, |v z| ≤ M)
    (m : ℕ) (hm : 1 ≤ m) (ι : Fin m → Fin d) :
    |iteratedCoordDeriv m ι v x| ≤ (K * m / ρ) ^ m * M := by
  let A : ℝ := K * (m : ℝ) / ρ
  have hA : A = K * (m : ℝ) / ρ := rfl
  have hxClosed : x ∈ euclideanClosedBall x ρ := by
    apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hρ.le).2
    rw [sub_self, vecEuclideanNorm]
    have hzero : vecNormSq (0 : Vec d) = 0 := by
      simp [vecNormSq, vecDot]
    rw [hzero, Real.sqrt_zero]
    exact hρ.le
  have hMnonneg : 0 ≤ M := (abs_nonneg (v x)).trans (hM x hxClosed)
  have hlist := iteratedCoordDerivList_pointwise_bound hK hρ hv hharm hFirst
    hm hρR hM A hA hMnonneg (List.ofFn ι)
    (by simp)
  have hlenOfFn : (List.ofFn ι).length = m := by simp
  have hxZero : x ∈ euclideanClosedBall x
      (ρ * (1 - ((List.ofFn ι).length : ℝ) / (m : ℝ))) := by
    have hradius : ρ * (1 - ((List.ofFn ι).length : ℝ) / (m : ℝ)) = 0 := by
      rw [hlenOfFn]
      have hmReal : (m : ℝ) ≠ 0 := by
        exact_mod_cast (show m ≠ 0 by omega)
      rw [div_self hmReal]
      simp
    rw [hradius]
    apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by norm_num)).2
    rw [sub_self, vecEuclideanNorm]
    have hzero : vecNormSq (0 : Vec d) = 0 := by
      simp [vecNormSq, vecDot]
    rw [hzero, Real.sqrt_zero]
  have hfinal := (hlist x hxZero).1
  rw [iteratedCoordDeriv_eq_list]
  simpa [A, hlenOfFn] using hfinal

end

end PDE
