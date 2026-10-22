module

public import PDEFoundation.Monotonicity.FriedlandHayman.Transport.CapBound
public import PDEFoundation.Monotonicity.FriedlandHayman.Assembly.Frac
public import PDEFoundation.Monotonicity.FriedlandHayman.Local.PolyaSzego

/-!
# Friedland--Hayman: the Gaussian lower bound for the spherical eigenvalue

From the one-dimensional form of the spherical Pólya--Szegő inequality
(`polya_szego_one_dim_of_miss`) and the cap-to-Gaussian bound `cap_gauss_bound`: if
`|Ω| ≤ γ((t, ∞))` then `λ_D(Ω) ≥ (D - 2) β(t)`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDE.FHLane

noncomputable section

/-- Gaussian lower bound for the spherical Dirichlet eigenvalue in `S^{D-1}`, `D ≥ 3`. -/
theorem lambda_ge_gaussBeta {D : ℕ} (hD : 3 ≤ D)
    {Ω : Set (Vec D)} (hΩ : MeasurableSet Ω) {t : ℝ} (ht : sphFrac D Ω ≤ gaussTail t) :
    ENNReal.ofReal (((D : ℝ) - 2) * gaussBeta t) ≤ sphereDirichletEigenvalue D Ω := by
  have : NeZero D := ⟨by omega⟩
  unfold sphereDirichletEigenvalue
  refine le_iInf fun f => le_iInf fun hf => ?_
  obtain ⟨hfC, hsupp, hI⟩ := hf
  have hA : 0 < sphereArea D := sphereArea_pos
  have hsup := sphereIntegral_support_le hfC.continuous hΩ hsupp
  have hmiss : sphereIntegral (0 : Vec D) 1 ({x | f x ≠ 0}.indicator fun _ => (1 : ℝ)) <
      sphereArea D := by
    have h1 : sphFrac D Ω < 1 := ht.trans_lt (gaussTail_lt_one t)
    unfold sphFrac at h1
    rw [div_lt_one hA] at h1
    exact hsup.trans_lt h1
  obtain ⟨h, K, θ₀, hh, hθ, hz, hcap, hL2, hE⟩ := polya_szego_one_dim_of_miss hD hfC hI hmiss
  have hA1 : 0 < sphereArea (D - 1) := by
    have : NeZero (D - 1) := ⟨by omega⟩
    exact sphereArea_pos
  have hcf : capFrac D θ₀ ≤ sphFrac D Ω := by
    unfold sphFrac
    rw [le_div_iff₀ hA]
    exact hcap.trans hsup
  have hθlt : θ₀ < Real.pi := by
    rcases hθ.2.lt_or_eq with h' | h'
    · exact h'
    · exfalso
      have hlt := (hcf.trans ht).trans_lt (gaussTail_lt_one t)
      rw [h', capFrac_pi] at hlt
      exact lt_irrefl _ hlt
  have key := cap_gauss_bound hD hh ⟨hθ.1, hθlt⟩ hz (hcf.trans ht)
  have key2 : ((D : ℝ) - 2) * gaussBeta t * sphereIntegral (0 : Vec D) 1 (fun x => f x ^ 2) ≤
      sphereIntegral (0 : Vec D) 1 (tangentialGradientNormSq f) := by
    rw [← hL2]
    calc ((D : ℝ) - 2) * gaussBeta t *
          (sphereArea (D - 1) * ∫ φ in (0 : ℝ)..Real.pi, h φ ^ 2 * sinW D φ)
        = sphereArea (D - 1) *
            (((D : ℝ) - 2) * gaussBeta t * ∫ φ in (0 : ℝ)..Real.pi, h φ ^ 2 * sinW D φ) := by
          ring
      _ ≤ sphereArea (D - 1) * ∫ φ in (0 : ℝ)..Real.pi, deriv h φ ^ 2 * sinW D φ :=
          mul_le_mul_of_nonneg_left key hA1.le
      _ ≤ _ := hE
  apply ENNReal.ofReal_le_ofReal
  rw [le_div_iff₀ hI]
  exact key2

end

end PDE.FHLane
