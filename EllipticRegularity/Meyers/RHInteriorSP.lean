module

public import EllipticRegularity.Meyers.CubeSP
public import PDEFoundation.Sobolev.H1.Basic
public import PDEFoundation.Measure.AxisBoxVolume

/-!
# Sobolev--Poincaré for an `H¹` function on a subcube

An `H¹(U)` function restricts to `W^{1,q}(V)` for a cube `V ⊆ U` (`q ≤ 2`), and the cube
Sobolev--Poincaré inequality applies to it.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.MeyersRH

open MeasureTheory

/-- Restrict an `H¹(U)` function to a subcube `V = centeredAxisCube z ρ` and regard it in
`W^{1,p}(V)` for `p ≤ 2`. -/
def restrictCubeW1p {d : ℕ} {U : Set (Vec d)} (u : H1Function U) (z : Vec d) {ρ : ℝ}
    (hVU : centeredAxisCube z ρ ⊆ U) (p : ℝ≥0∞) (hp : p ≤ 2) :
    W1pFunction (centeredAxisCube z ρ) p :=
  haveI : IsFiniteMeasure (volumeOn (centeredAxisCube z ρ)) :=
    (isOpenBoundedConvexDomain_centeredAxisCube z ρ).isFiniteMeasure_volumeOn
  { toFun := u.toFun
    grad := u.grad
    memLp := (memLpOn_mono hVU u.memL2).mono_exponent hp
    gradMemLp := fun i =>
      (memLpOn_mono hVU (u.gradMemL2 i)).mono_exponent hp
    hasWeakGradient :=
      (u.hasWeakGradient).restrict (isOpen_centeredAxisCube z ρ) hVU }

@[simp] theorem restrictCubeW1p_toFun {d : ℕ} {U : Set (Vec d)} (u : H1Function U) (z : Vec d)
    {ρ : ℝ} (hVU : centeredAxisCube z ρ ⊆ U) (p : ℝ≥0∞) (hp : p ≤ 2) :
    (restrictCubeW1p u z hVU p hp).toFun = u.toFun := rfl

@[simp] theorem restrictCubeW1p_grad {d : ℕ} {U : Set (Vec d)} (u : H1Function U) (z : Vec d)
    {ρ : ℝ} (hVU : centeredAxisCube z ρ ⊆ U) (p : ℝ≥0∞) (hp : p ≤ 2) :
    (restrictCubeW1p u z hVU p hp).grad = u.grad := rfl

theorem volume_centeredAxisCube_two_mul {d : ℕ} (z : Vec d) {r : ℝ} (hr : 0 ≤ r) :
    (volume (centeredAxisCube z (2 * r))).toReal =
      2 ^ d * (volume (centeredAxisCube z r)).toReal := by
  rw [volume_centeredAxisCube_toReal z (by linarith), volume_centeredAxisCube_toReal z hr,
    ← mul_pow]

end PDE.MeyersRH
