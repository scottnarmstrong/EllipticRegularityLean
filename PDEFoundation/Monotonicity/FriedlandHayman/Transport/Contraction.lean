module

public import PDEFoundation.Monotonicity.FriedlandHayman.Transport.Map
public import PDEFoundation.Monotonicity.FriedlandHayman.Transport.Caffarelli

/-!
# Friedland--Hayman: the transport map is a contraction

For `D ≥ 3` the map `Θ = tmap D` together with `w = r * (zTot / gTot) * gaussW / sinW D (Θ s)`,
`r = √(D - 2)`, satisfies the differential system of the Caffarelli lemma, hence
`-Θ' = w / r ≤ 1 / r`.
-/

@[expose] public section

open Set Filter Topology

namespace PDE.FHLane

namespace Transp

noncomputable section

/-- `r = √(D - 2)`. -/
def rootD (D : ℕ) : ℝ := Real.sqrt ((D - 2 : ℕ) : ℝ)

/-- The weight `w = r * (-Θ')` of the transport map. -/
def wmap (D : ℕ) (s : ℝ) : ℝ := rootD D * (zTot D / gTot) * gaussW s / sinW D (tmap D s)

theorem rootD_pos {D : ℕ} (hD : 3 ≤ D) : 0 < rootD D := by
  unfold rootD
  apply Real.sqrt_pos.2
  have : 1 ≤ D - 2 := by omega
  exact_mod_cast this

theorem rootD_sq {D : ℕ} : rootD D ^ 2 = ((D - 2 : ℕ) : ℝ) := by
  unfold rootD
  exact Real.sq_sqrt (Nat.cast_nonneg _)

theorem wmap_pos (D : ℕ) (s : ℝ) (hD : 3 ≤ D) : 0 < wmap D s := by
  unfold wmap
  have := rootD_pos hD
  have := zTot_pos D
  have := gTot_pos
  have := gaussW_pos s
  have := sinW_pos (D := D) (tmap_mem D s)
  positivity

theorem algebra_wmap {A g sn cs r s : ℝ} (m : ℕ) (_hr : r ≠ 0) (hs : sn ≠ 0)
    (hk : r ^ 2 = (m : ℝ) + 1) :
    (A * (-s * g) * sn ^ (m + 1) -
        A * g * (((m + 1 : ℕ) : ℝ) * sn ^ m * (cs * (-(A * g / sn ^ (m + 1)) / r)))) /
        (sn ^ (m + 1)) ^ 2 =
      A * g / sn ^ (m + 1) * (r * (cs / sn) * (A * g / sn ^ (m + 1)) - s) := by
  have : ((m + 1 : ℕ) : ℝ) = r ^ 2 := by push_cast; linarith
  rw [this]
  field_simp
  ring

theorem caffData {D : ℕ} (hD : 3 ≤ D) : CaffData (rootD D) (tmap D) (wmap D) where
  r_pos := rootD_pos hD
  Θ_pos s := (tmap_mem D s).1
  Θ_lt s := (tmap_mem D s).2
  w_pos s := wmap_pos D s hD
  dΘ s := by
    refine (hasDerivAt_tmap D s).congr_deriv ?_
    have := (rootD_pos hD).ne'
    have := (sinW_pos (D := D) (tmap_mem D s)).ne'
    unfold wmap
    field_simp
  dw s := by
    obtain ⟨m, rfl⟩ : ∃ m, D = m + 3 := ⟨D - 3, by omega⟩
    have hr := (rootD_pos hD).ne'
    have hsn := (Real.sin_pos_of_pos_of_lt_pi (tmap_mem (m + 3) s).1 (tmap_mem (m + 3) s).2).ne'
    have hdΘ : HasDerivAt (tmap (m + 3)) (-(wmap (m + 3) s) / rootD (m + 3)) s := by
      refine (hasDerivAt_tmap (m + 3) s).congr_deriv ?_
      have := (sinW_pos (D := m + 3) (tmap_mem (m + 3) s)).ne'
      unfold wmap
      field_simp
    have hS := (hdΘ.sin).pow (m + 1)
    have hnum := (hasDerivAt_gaussW s).const_mul
      (rootD (m + 3) * (zTot (m + 3) / gTot))
    have hq := hnum.div hS (pow_ne_zero _ hsn)
    have e : wmap (m + 3) = fun s => rootD (m + 3) * (zTot (m + 3) / gTot) * gaussW s /
        Real.sin (tmap (m + 3) s) ^ (m + 1) := by
      funext s
      unfold wmap sinW
      rfl
    rw [e]
    refine hq.congr_deriv ?_
    have hk : rootD (m + 3) ^ 2 = (m : ℝ) + 1 := by
      rw [rootD_sq]
      have : m + 3 - 2 = m + 1 := by omega
      rw [this]
      push_cast
      ring
    have hw : ∀ x, wmap (m + 3) x = rootD (m + 3) * (zTot (m + 3) / gTot) * gaussW x /
        Real.sin (tmap (m + 3) x) ^ (m + 1) := fun x => congrFun e x
    simp only [barG, hw, Nat.add_sub_cancel]
    have := algebra_wmap (A := rootD (m + 3) * (zTot (m + 3) / gTot)) (g := gaussW s)
      (sn := Real.sin (tmap (m + 3) s)) (cs := Real.cos (tmap (m + 3) s))
      (r := rootD (m + 3)) (s := s) m hr hsn hk
    convert this using 2

theorem wmap_le_one {D : ℕ} (hD : 3 ≤ D) (s : ℝ) : wmap D s ≤ 1 :=
  (caffData hD).w_le_one s

/-- The derivative of the transport map, as a function. -/
def dtmap (D : ℕ) (s : ℝ) : ℝ := -(zTot D / gTot) * gaussW s / sinW D (tmap D s)

theorem dtmap_eq {D : ℕ} (hD : 3 ≤ D) (s : ℝ) : dtmap D s = -(wmap D s) / rootD D := by
  have := (rootD_pos hD).ne'
  have := (sinW_pos (D := D) (tmap_mem D s)).ne'
  unfold dtmap wmap
  field_simp

theorem dtmap_neg {D : ℕ} (hD : 3 ≤ D) (s : ℝ) : dtmap D s < 0 := by
  rw [dtmap_eq hD]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos (wmap_pos D s hD)) (rootD_pos hD)

theorem dtmap_sq_le {D : ℕ} (hD : 3 ≤ D) (s : ℝ) :
    dtmap D s ^ 2 * rootD D ^ 2 ≤ 1 := by
  rw [dtmap_eq hD, div_pow, neg_sq]
  have hr := (rootD_pos hD).ne'
  have h1 := wmap_pos D s hD
  have h2 := wmap_le_one hD s
  rw [div_mul_cancel₀ _ (pow_ne_zero 2 hr)]
  nlinarith

theorem tmap_lipschitz {D : ℕ} (hD : 3 ≤ D) :
    LipschitzWith (Real.toNNReal (rootD D)⁻¹) (tmap D) := by
  refine lipschitzWith_of_nnnorm_deriv_le (fun x => (hasDerivAt_tmap D x).differentiableAt) ?_
  intro x
  rw [(hasDerivAt_tmap D x).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _
    (inv_nonneg.2 (rootD_pos hD).le), Real.norm_eq_abs]
  have h := dtmap_eq hD x
  unfold dtmap at h
  rw [h, abs_div, abs_neg, abs_of_pos (wmap_pos D x hD), abs_of_pos (rootD_pos hD), inv_eq_one_div]
  exact div_le_div_of_nonneg_right (wmap_le_one hD x) (rootD_pos hD).le

end

end Transp

end PDE.FHLane
