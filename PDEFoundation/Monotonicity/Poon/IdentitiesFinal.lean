module

public import PDEFoundation.Monotonicity.Poon.IdentitiesIBP

/-!
# Poon's integrated identities

For `v` with a `PoonSetup`, `w = x·∇v - 2 s Δv`, `κ = -d/(2s) + |x|²/(4s²)`, `Φ = Φ(s, ·)`:

* `∫ (2 v (-Δv) + v² κ) Φ = 2 ∫ |∇v|² Φ`,
* `∫ v w Φ = 2 s ∫ |∇v|² Φ`,
* `∫ (-2 ∇v·∇Δv + |∇v|² κ) Φ = (1/(2 s²)) ∫ w² Φ - (1/s) ∫ |∇v|² Φ`.
-/

@[expose] public section

namespace PDE

noncomputable section

variable {d : ℕ}

theorem eq_of_two_mul_eq {s X Y : ℝ} (hs : s ≠ 0) (h : X = 1 / (2 * s) * Y) : 2 * s * X = Y := by
  rw [h]; field_simp

namespace PoonSetup

variable {v : Vec d → ℝ} {s A' : ℝ} (hP : PoonSetup v s A')
include hP

/-- `∫ (2 v (-Δv) + v² κ) Φ = 2 ∫ |∇v|² Φ`. -/
theorem lam_H_identity :
    Lam d s (fun x => 2 * v x * (-(euclideanCoordLaplacian v x)) +
      v x ^ 2 * (-(d : ℝ) / (2 * s) + vecNormSq x / (4 * s ^ 2))) = 2 * Lam d s (pQ2 v) := by
  have hs := hP.pos
  have hw := hP.weight
  have hs0 : s ≠ 0 := hs.ne'
  have h1 := hP.lam_div1
  have h2 := hP.lam_div2
  rw [show (fun x => (d : ℝ) * (v x * v x) + 2 * v x * pP v x) =
      fun x => (d : ℝ) * (v x * v x) + 2 * (v x * pP v x) from funext fun x => by ring,
    Lam_add hs hw (hP.dom_vv.const_mul d) (hP.dom_vP.const_mul 2),
    Lam_const_mul, Lam_const_mul] at h1
  rw [Lam_add hs hw hP.dom_Q2 hP.dom_vL] at h2
  have h1' := eq_of_two_mul_eq hs0 h1
  have h2' := eq_of_two_mul_eq hs0 h2
  rw [show (fun x => 2 * v x * (-(euclideanCoordLaplacian v x)) +
      v x ^ 2 * (-(d : ℝ) / (2 * s) + vecNormSq x / (4 * s ^ 2))) =
      fun x => (-2) * (v x * euclideanCoordLaplacian v x) + (-(d : ℝ) / (2 * s)) * (v x * v x) +
        (1 / (4 * s ^ 2)) * (vecNormSq x * (v x * v x)) from funext fun x => by ring,
    Lam_add hs hw ((hP.dom_vL.const_mul _).add (hP.dom_vv.const_mul _)) (hP.dom_qvv.const_mul _),
    Lam_add hs hw (hP.dom_vL.const_mul _) (hP.dom_vv.const_mul _),
    Lam_const_mul, Lam_const_mul, Lam_const_mul]
  rw [← h1', ← h2']
  field_simp
  ring

/-- `∫ v w Φ = 2 s ∫ |∇v|² Φ`. -/
theorem lam_vw_identity :
    Lam d s (fun x => v x * (pP v x - 2 * s * euclideanCoordLaplacian v x)) =
      2 * s * Lam d s (pQ2 v) := by
  have hs := hP.pos
  have hw := hP.weight
  have hs0 : s ≠ 0 := hs.ne'
  have h2 := hP.lam_div2
  rw [Lam_add hs hw hP.dom_Q2 hP.dom_vL] at h2
  have h2' := eq_of_two_mul_eq hs0 h2
  rw [show (fun x => v x * (pP v x - 2 * s * euclideanCoordLaplacian v x)) =
      fun x => v x * pP v x + (-(2 * s)) * (v x * euclideanCoordLaplacian v x) from
      funext fun x => by ring,
    Lam_add hs hw hP.dom_vP (hP.dom_vL.const_mul _), Lam_const_mul]
  rw [← h2']
  ring

/-- `∫ (-2 ∇v·∇Δv + |∇v|² κ) Φ = (1/(2s²)) ∫ w² Φ - (1/s) ∫ |∇v|² Φ`. -/
theorem lam_D_identity :
    Lam d s (fun x => -2 * pV3 v x +
      pQ2 v x * (-(d : ℝ) / (2 * s) + vecNormSq x / (4 * s ^ 2))) =
      1 / (2 * s ^ 2) * Lam d s (fun x => (pP v x - 2 * s * euclideanCoordLaplacian v x) *
        (pP v x - 2 * s * euclideanCoordLaplacian v x)) - 1 / s * Lam d s (pQ2 v) := by
  have hs := hP.pos
  have hw := hP.weight
  have hs0 : s ≠ 0 := hs.ne'
  have h3 := hP.lam_div3
  have h4 := hP.lam_div4
  have h5 := hP.lam_div5
  rw [show (fun x => pP v x * euclideanCoordLaplacian v x) =
      fun x => euclideanCoordLaplacian v x * pP v x from funext fun x => mul_comm _ _] at h3
  rw [Lam_add hs hw hP.dom_LL hP.dom_V3] at h3
  rw [Lam_add hs hw (hP.dom_Q2.const_mul _) (hP.dom_R.const_mul _), Lam_const_mul,
    Lam_const_mul] at h4
  rw [Lam_add hs hw (hP.dom_LP.add hP.dom_Q2) hP.dom_R, Lam_add hs hw hP.dom_LP hP.dom_Q2] at h5
  have h3' := eq_of_two_mul_eq hs0 h3
  have h4' := eq_of_two_mul_eq hs0 h4
  have h5' := eq_of_two_mul_eq hs0 h5
  rw [show (fun x => -2 * pV3 v x +
      pQ2 v x * (-(d : ℝ) / (2 * s) + vecNormSq x / (4 * s ^ 2))) =
      fun x => (-2) * pV3 v x + (-(d : ℝ) / (2 * s)) * pQ2 v x +
        (1 / (4 * s ^ 2)) * (vecNormSq x * pQ2 v x) from funext fun x => by ring,
    Lam_add hs hw ((hP.dom_V3.const_mul _).add (hP.dom_Q2.const_mul _)) (hP.dom_qQ2.const_mul _),
    Lam_add hs hw (hP.dom_V3.const_mul _) (hP.dom_Q2.const_mul _),
    Lam_const_mul, Lam_const_mul, Lam_const_mul]
  rw [show (fun x => (pP v x - 2 * s * euclideanCoordLaplacian v x) *
        (pP v x - 2 * s * euclideanCoordLaplacian v x)) =
      fun x => pP v x * pP v x + (-(4 * s)) * (euclideanCoordLaplacian v x * pP v x) +
        (4 * s ^ 2) * (euclideanCoordLaplacian v x * euclideanCoordLaplacian v x) from
      funext fun x => by ring,
    Lam_add hs hw ((hP.dom_PP.add (hP.dom_LP.const_mul _))) (hP.dom_LL.const_mul _),
    Lam_add hs hw hP.dom_PP (hP.dom_LP.const_mul _),
    Lam_const_mul, Lam_const_mul]
  rw [← h4', ← h5', ← h3']
  field_simp
  ring

end PoonSetup

end

end PDE
