module

public import EllipticRegularity.Ch4.GreenHarnack.ChainPaths

/-!
# Any two points of the thick annulus are joined by a chain of `414` steps

The route is: radial segment to the sphere of radius `r`, an arc to a signed coordinate
vector (inner product `≥ 0`), at most two arcs to another signed coordinate vector (through a
third coordinate direction if necessary), an arc to the target's radial projection, and a radial
segment. Each arc and radial piece is a chain from `ChainPaths`; the total is
`13 + 97 + 2 * 97 + 97 + 13 = 414` steps of length `< r/16`.
-/

@[expose] public section

namespace PDE.Ch4GreenHarnack

open PDE

variable {d : ℕ}

/-- The signed coordinate vector `(σ r) e_i` with `σ = ±1`. -/
noncomputable def signedBasis (r σ : ℝ) (i : Fin d) : Vec d := (σ * r) • basisVec i

theorem vecEuclideanNorm_signedBasis {r σ : ℝ} (hr : 0 < r) (hσ : σ = 1 ∨ σ = -1) (i : Fin d) :
    vecEuclideanNorm (signedBasis r σ i) = r := by
  rw [signedBasis, vecEuclideanNorm_smul, vecEuclideanNorm_basisVec]
  rcases hσ with rfl | rfl <;> simp [abs_of_pos hr]

theorem vecDot_signedBasis_of_ne {r σ σ' : ℝ} {i j : Fin d} (hij : i ≠ j) :
    vecDot (signedBasis r σ i) (signedBasis r σ' j) = 0 := by
  rw [signedBasis, signedBasis, vecDot_smul_left', vecDot_smul_right', vecDot_basisVec_right]
  simp [basisVec_apply, hij.symm]

/-- Two signed coordinate vectors on the sphere of radius `r` are joined by `194` steps. -/
theorem signedBasis_chain (hd : 2 ≤ d) {r : ℝ} (hr : 0 < r) {σ σ' : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (hσ' : σ' = 1 ∨ σ' = -1) (i j : Fin d) :
    IsChain (annulusSet d r) (r / 16) 194 (signedBasis r σ i) (signedBasis r σ' j) := by
  have hs : 0 < r / 16 := by positivity
  by_cases hij : i = j
  · subst hij
    have : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd
    obtain ⟨k, hk⟩ := exists_ne i
    have h1 := arc_chain hr (vecEuclideanNorm_signedBasis hr hσ i)
      (vecEuclideanNorm_signedBasis hr (Or.inl rfl : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1) k)
      (vecDot_signedBasis_of_ne hk.symm).ge
    have h2 := arc_chain hr (vecEuclideanNorm_signedBasis hr (Or.inl rfl : (1 : ℝ) = 1 ∨ (1 : ℝ) = -1) k)
      (vecEuclideanNorm_signedBasis hr hσ' i)
      (vecDot_signedBasis_of_ne hk).ge
    simpa using h1.trans h2
  · exact (arc_chain hr (vecEuclideanNorm_signedBasis hr hσ i)
      (vecEuclideanNorm_signedBasis hr hσ' j) (vecDot_signedBasis_of_ne hij).ge).mono hs
        (by norm_num)

/-- Every vector of norm `r` has nonnegative inner product with some signed coordinate vector. -/
theorem exists_signedBasis {r : ℝ} (hr : 0 < r) (hd : 0 < d) (a : Vec d) :
    ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧ ∃ i : Fin d, 0 ≤ vecDot a (signedBasis r σ i) := by
  obtain ⟨i⟩ : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  by_cases ha : 0 ≤ a i
  · refine ⟨1, Or.inl rfl, i, ?_⟩
    rw [signedBasis, vecDot_smul_right', vecDot_basisVec_right]; positivity
  · refine ⟨-1, Or.inr rfl, i, ?_⟩
    rw [signedBasis, vecDot_smul_right', vecDot_basisVec_right]
    push Not at ha; nlinarith

/-- Any two points of `{r/4 ≤ |z| ≤ 3r/2}` are joined by a chain of `414` steps of length
`< r/16` inside this set. -/
theorem annulus_chain (hd : 2 ≤ d) {r : ℝ} (hr : 0 < r) {x y : Vec d} (hx : x ∈ annulusSet d r)
    (hy : y ∈ annulusSet d r) : IsChain (annulusSet d r) (r / 16) 414 x y := by
  have hs : 0 < r / 16 := by positivity
  have hxn : 0 < vecEuclideanNorm x := by have := hx.1; linarith
  have hyn : 0 < vecEuclideanNorm y := by have := hy.1; linarith
  set a := (r / vecEuclideanNorm x) • x with hadef
  set b := (r / vecEuclideanNorm y) • y with hbdef
  have han : vecEuclideanNorm a = r := by
    rw [hadef, vecEuclideanNorm_smul, abs_of_pos (by positivity)]; field_simp
  have hbn : vecEuclideanNorm b = r := by
    rw [hbdef, vecEuclideanNorm_smul, abs_of_pos (by positivity)]; field_simp
  obtain ⟨σ, hσ, i, hai⟩ := exists_signedBasis hr (by omega) a
  obtain ⟨σ', hσ', j, hbj⟩ := exists_signedBasis hr (by omega) b
  have c1 := radial_chain hr hx
  have c2 := arc_chain hr han (vecEuclideanNorm_signedBasis hr hσ i) hai
  have c3 := signedBasis_chain hd hr hσ hσ' i j
  have c4 := arc_chain hr hbn (vecEuclideanNorm_signedBasis hr hσ' j) hbj
  have c5 := radial_chain hr hy
  have := (((c1.trans c2).trans c3).trans c4.symm).trans c5.symm
  simpa using this

end PDE.Ch4GreenHarnack
