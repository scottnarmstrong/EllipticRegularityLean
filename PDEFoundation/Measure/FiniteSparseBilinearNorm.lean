module

public import PDEFoundation.Measure.FiniteSparsePairing
public import PDEFoundation.Measure.ExtendedHolderNorm
public import PDEFoundation.Measure.DyadicBoxMaximalStrong

@[expose] public section

namespace PDE
open BoxIntegral MeasureTheory
open scoped ENNReal

/-- The literal finite sparse pairing has the sharp coefficient `4p/3`
after Hölder and the actual sharp dyadic maximal theorem. -/
theorem finite_sparse_pairing_le_eLpNorm_mul
    {d : ℕ} (I : Box (Fin d)) (S : Finset (List (Set (Fin d))))
    (b φ : Vec d → ℝ) (a : List (Set (Fin d)) → ℝ)
    (E : List (Set (Fin d)) → Set (Vec d))
    (hE : ∀ q ∈ S, MeasurableSet (E q))
    (hsub : ∀ q ∈ S, E q ⊆ (dyadicDescendant I q : Set (Vec d)))
    (hdisj : (S : Set (List (Set (Fin d)))).PairwiseDisjoint E)
    (hpacking : ∀ q ∈ S, ENNReal.ofReal (3 / 4 : ℝ) *
      volume (dyadicDescendant I q : Set (Vec d)) ≤ volume (E q))
    (hminor : ∀ q ∈ S, ∀ᵐ x ∂volume.restrict (dyadicDescendant I q : Set (Vec d)),
      a q ≤ |b x|) {p : ℝ} (hp : 1 < p)
    (hb : MemLp b (ENNReal.ofReal p) (volume.restrict (I : Set (Vec d))))
    (hφ : MemLp φ (ENNReal.ofReal (Real.conjExponent p))
      (volume.restrict (I : Set (Vec d)))) :
    (∑ q ∈ S, ENNReal.ofReal (a q) *
      ∫⁻ x in (dyadicDescendant I q : Set (Vec d)), ENNReal.ofReal |φ x|) ≤
      ENNReal.ofReal ((4 / 3 : ℝ) * p) *
        eLpNorm b (ENNReal.ofReal p) (volume.restrict (I : Set (Vec d))) *
        eLpNorm φ (ENNReal.ofReal (Real.conjExponent p))
          (volume.restrict (I : Set (Vec d))) := by
  have hpq := Real.HolderConjugate.conjExponent hp
  have hpair := finite_sparse_pairing_le I S b φ a E hE hsub hdisj hpacking hminor
  have hhold := lintegral_abs_mul_le_eLpNorm_mul_conjugate
    (volume.restrict (I : Set (Vec d))) b hb.aestronglyMeasurable (dyadicBoxMaximal I φ)
      ((measurable_dyadicBoxMaximal I φ).aemeasurable) hp
  have hmax := eLpNorm_dyadicBoxMaximal_le I φ hpq.symm.lt hφ
  have hqconst : Real.conjExponent p / (Real.conjExponent p - 1) = p := by
    exact hpq.symm.conjugate_eq.symm
  rw [hqconst] at hmax
  calc
    _ ≤ ENNReal.ofReal (4 / 3 : ℝ) *
        (eLpNorm b (ENNReal.ofReal p) (volume.restrict (I : Set (Vec d))) *
          eLpNorm (dyadicBoxMaximal I φ) (ENNReal.ofReal (Real.conjExponent p))
            (volume.restrict (I : Set (Vec d)))) :=
      hpair.trans (mul_le_mul_right hhold _)
    _ ≤ ENNReal.ofReal (4 / 3 : ℝ) *
        (eLpNorm b (ENNReal.ofReal p) (volume.restrict (I : Set (Vec d))) *
          (ENNReal.ofReal p * eLpNorm φ (ENNReal.ofReal (Real.conjExponent p))
            (volume.restrict (I : Set (Vec d))))) :=
      mul_le_mul_right (mul_le_mul_right hmax _) _
    _ = _ := by
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4 / 3)]
      ac_rfl

end PDE
