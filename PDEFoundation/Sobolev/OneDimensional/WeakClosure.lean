module

public import PDEFoundation.Sobolev.OneDimensional.OneDimensionalCoordinate
public import PDEFoundation.Sobolev.OneDimensional.WeakPrimitive
public import PDEFoundation.Sobolev.W1p.Closure

/-!
# Closure of one-dimensional weak derivatives

This module specializes the common closed weak-gradient theorem to scalar
functions on an interval.  It is the limit-passage used when smooth
restrictions to a square side converge in value and tangential derivative.
-/

@[expose] public section

open scoped ENNReal Topology

namespace PDE

open Filter MeasureTheory Set

noncomputable section

namespace HasWeakDerivOnIoo

/-- One-dimensional weak derivatives are closed under simultaneous `L²`
convergence of the values and derivatives.  The proof is an exact
specialization of the native closed weak-gradient graph. -/
theorem of_tendsto_eLpNorm
    {a b : ℝ} {u g : ℝ → ℝ}
    {uSeq gSeq : ℕ → ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (Ioo a b)))
    (hg : MemLp g 2 (volume.restrict (Ioo a b)))
    (huSeq : ∀ n, MemLp (uSeq n) 2 (volume.restrict (Ioo a b)))
    (hgSeq : ∀ n, MemLp (gSeq n) 2 (volume.restrict (Ioo a b)))
    (hweak : ∀ n, HasWeakDerivOnIoo a b (uSeq n) (gSeq n))
    (hValue :
      Tendsto
        (fun n =>
          eLpNorm (fun t => uSeq n t - u t) 2
            (volume.restrict (Ioo a b)))
        atTop (𝓝 0))
    (hDeriv :
      Tendsto
        (fun n =>
          eLpNorm (fun t => gSeq n t - g t) 2
            (volume.restrict (Ioo a b)))
        atTop (𝓝 0)) :
    HasWeakDerivOnIoo a b u g := by
  let U : Set (Vec 1) := oneDimensionalAxisBox a b
  let un : ℕ → Vec 1 → ℝ :=
    fun n => liftOneDimensional (uSeq n)
  let gn : ℕ → Vec 1 → Vec 1 :=
    fun n x _ => liftOneDimensional (gSeq n) x
  let uNative : Vec 1 → ℝ := liftOneDimensional u
  let gNative : Vec 1 → Vec 1 :=
    fun x _ => liftOneDimensional g x
  have huNative : MemLpOn U 2 uNative := by
    exact (memLp_two_liftOneDimensional_iff_memLp_two_Ioo a b).2 hu
  have hgNative : GradMemLpOn U 2 gNative := by
    intro i
    exact (memLp_two_liftOneDimensional_iff_memLp_two_Ioo a b).2 hg
  have hunNative : ∀ n, MemLpOn U 2 (un n) := by
    intro n
    exact
      (memLp_two_liftOneDimensional_iff_memLp_two_Ioo a b).2
        (huSeq n)
  have hgnNative : ∀ n, GradMemLpOn U 2 (gn n) := by
    intro n i
    exact
      (memLp_two_liftOneDimensional_iff_memLp_two_Ioo a b).2
        (hgSeq n)
  have hweakNative :
      ∀ n, HasWeakGradientOn U (un n) (gn n) := by
    intro n i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    exact hweak n
  have hValueNative :
      Tendsto
        (fun n => eLpNorm (un n - uNative) 2 (volumeOn U))
        atTop (𝓝 0) := by
    have heq :
        (fun n => eLpNorm (un n - uNative) 2 (volumeOn U)) =
          fun n =>
            eLpNorm (fun t => uSeq n t - u t) 2
              (volume.restrict (Ioo a b)) := by
      funext n
      rw [show un n - uNative =
          liftOneDimensional (fun t => uSeq n t - u t) by
        funext x
        rfl]
      exact eLpNorm_liftOneDimensional_eq_eLpNorm_Ioo a b
    rw [heq]
    exact hValue
  have hDerivNative :
      ∀ i : Fin 1,
        Tendsto
          (fun n =>
            eLpNorm
              (fun x => gn n x i - gNative x i)
              2 (volumeOn U))
          atTop (𝓝 0) := by
    intro i
    have heq :
        (fun n =>
          eLpNorm
            (fun x => gn n x i - gNative x i)
            2 (volumeOn U)) =
          fun n =>
            eLpNorm (fun t => gSeq n t - g t) 2
              (volume.restrict (Ioo a b)) := by
      funext n
      change
        eLpNorm
            (liftOneDimensional (fun t => gSeq n t - g t))
            2 (volumeOn U) =
          eLpNorm (fun t => gSeq n t - g t) 2
            (volume.restrict (Ioo a b))
      exact eLpNorm_liftOneDimensional_eq_eLpNorm_Ioo a b
    rw [heq]
    exact hDeriv
  have hNative :=
    HasWeakGradientOn.of_tendsto_eLpNorm
      huNative hgNative hunNative hgnNative hweakNative
      hValueNative hDerivNative
  exact hNative 0

end HasWeakDerivOnIoo

end

end PDE
