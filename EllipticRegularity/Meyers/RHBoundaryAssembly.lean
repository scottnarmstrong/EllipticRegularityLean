module

public import EllipticRegularity.Meyers.RHBoundaryHolder
public import PDEFoundation.Measure.Jensen

/-!
# Assembly of the reverse Hölder step on a cube

Pure real-analysis lemmas on a set `P` of positive finite volume (later the cube `4Q`):
the Hölder step against the Sobolev–Poincaré bound, the integrability of the resulting
integrand, and Jensen's inequality for the exponent `θ < 1`.
-/

@[expose] public section

open MeasureTheory

namespace PDE

namespace MeyersRH

variable {d : ℕ} {P : Set (Vec d)}

theorem memLp_abs_sub_const {p' : ℝ} {u : Vec d → ℝ} {ub c : ℝ}
    (hPfin : volume P ≠ ⊤)
    (hv : MemLp (fun x => u x - ub) (ENNReal.ofReal p') (volume.restrict P)) :
    MemLp (fun x => |u x - c|) (ENNReal.ofReal p') (volume.restrict P) := by
  have : IsFiniteMeasure (volume.restrict P) := ⟨by simpa using hPfin.lt_top⟩
  have h1 : MemLp (fun x => u x - c) (ENNReal.ofReal p') (volume.restrict P) := by
    have := hv.add (memLp_const (ub - c))
    refine this.ae_eq (Filter.Eventually.of_forall fun x => ?_)
    simp only [Pi.add_apply]; ring
  simpa [Real.norm_eq_abs] using h1.norm

/-- Integrability of the integrand of the Hölder step. -/
theorem integrable_abs_sub_mul_add {p p' : ℝ} (hpp : p.HolderConjugate p')
    (hPfin : volume P ≠ ⊤) {u wE sE : Vec d → ℝ} {ub c L : ℝ}
    (hw0 : ∀ x, 0 ≤ wE x) (hs0 : ∀ x, 0 ≤ sE x)
    (hv : MemLp (fun x => u x - ub) (ENNReal.ofReal p') (volume.restrict P))
    (hw : MemLp wE (ENNReal.ofReal p) (volume.restrict P))
    (hs : MemLp sE (ENNReal.ofReal p) (volume.restrict P)) :
    Integrable (fun x => |u x - c| * (L * wE x + sE x)) (volume.restrict P) := by
  have hv' := memLp_abs_sub_const (c := c) hPfin hv
  have h1 := integrable_mul_of_memLp_conj hpp (fun x => abs_nonneg (u x - c)) hw0 hv' hw
  have h2 := integrable_mul_of_memLp_conj hpp (fun x => abs_nonneg (u x - c)) hs0 hv' hs
  refine ((h1.const_mul L).add h2).congr (Filter.Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply]; ring

/-- The normalized `L^p` norm over `P` of `f`: `((|P|⁻¹ ∫_P f^p))^{1/p}`. -/
noncomputable def lpAvg (P : Set (Vec d)) (p : ℝ) (f : Vec d → ℝ) : ℝ :=
  ((volume P).toReal⁻¹ * ∫ x in P, f x ^ p) ^ (1 / p)

theorem lpAvg_nonneg (P : Set (Vec d)) (p : ℝ) {f : Vec d → ℝ} (hf : ∀ x, 0 ≤ f x) :
    0 ≤ lpAvg P p f :=
  Real.rpow_nonneg (mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
    (integral_nonneg fun x => Real.rpow_nonneg (hf x) _)) _

/-- The Hölder step against the Sobolev–Poincaré bound. -/
theorem sp_holder_step {p p' : ℝ} (hpp : p.HolderConjugate p')
    (hP0 : 0 < (volume P).toReal) (hPfin : volume P ≠ ⊤)
    {u wE sE mE : Vec d → ℝ} {ub c κ Sl L : ℝ}
    (hκ : 0 ≤ κ) (hSl : 0 ≤ Sl) (hL : 0 ≤ L)
    (hw0 : ∀ x, 0 ≤ wE x) (hs0 : ∀ x, 0 ≤ sE x) (hm0 : ∀ x, 0 ≤ mE x)
    (hmw : ∀ x, mE x ≤ wE x)
    (hv : MemLp (fun x => u x - ub) (ENNReal.ofReal p') (volume.restrict P))
    (hw : MemLp wE (ENNReal.ofReal p) (volume.restrict P))
    (hs : MemLp sE (ENNReal.ofReal p) (volume.restrict P))
    (hm : MemLp mE (ENNReal.ofReal p) (volume.restrict P))
    (hSP : lpAvg P p' (fun x => |u x - ub|) ≤ Sl * lpAvg P p mE)
    (hc : |ub - c| ≤ κ * lpAvg P p' (fun x => |u x - ub|)) :
    ∫ x in P, |u x - c| * (L * wE x + sE x) ≤
      (volume P).toReal * (1 + κ) * Sl *
        (L * (lpAvg P p wE) ^ 2 + lpAvg P p wE * lpAvg P p sE) := by
  have : IsFiniteMeasure (volume.restrict P) := ⟨by simpa using hPfin.lt_top⟩
  have hp0 : 0 < p := hpp.pos
  have hp'0 : 0 < p' := hpp.symm.pos
  set V := (volume P).toReal with hV
  have hv' := memLp_abs_sub_const (c := c) hPfin hv
  have hint1 := integrable_mul_of_memLp_conj hpp (fun x => abs_nonneg (u x - c)) hw0 hv' hw
  have hint2 := integrable_mul_of_memLp_conj hpp (fun x => abs_nonneg (u x - c)) hs0 hv' hs
  have hH1 := integral_abs_sub_mul_le hpp hP0 hPfin hκ hw0 hv hw hc
  have hH2 := integral_abs_sub_mul_le hpp hP0 hPfin hκ hs0 hv hs hc
  have hsplit : ∫ x in P, |u x - c| * (L * wE x + sE x) =
      L * (∫ x in P, |u x - c| * wE x) + ∫ x in P, |u x - c| * sE x := by
    calc ∫ x in P, |u x - c| * (L * wE x + sE x)
        = ∫ x in P, (L * (|u x - c| * wE x) + |u x - c| * sE x) :=
          integral_congr_ae (Filter.Eventually.of_forall fun x => by ring)
      _ = (∫ x in P, L * (|u x - c| * wE x)) + ∫ x in P, |u x - c| * sE x :=
          integral_add (hint1.const_mul L) hint2
      _ = _ := by rw [integral_const_mul]
  -- `N ≤ Sl A`
  have hAmono : lpAvg P p mE ≤ lpAvg P p wE := by
    unfold lpAvg
    refine Real.rpow_le_rpow (mul_nonneg (inv_nonneg.mpr hP0.le)
      (integral_nonneg fun x => Real.rpow_nonneg (hm0 x) _)) ?_ (by positivity)
    refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hP0.le)
    have i1 : Integrable (fun x => mE x ^ p) (volume.restrict P) := by
      simpa [Real.norm_of_nonneg (hm0 _), ENNReal.toReal_ofReal hp0.le] using
        hm.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top
    have i2 : Integrable (fun x => wE x ^ p) (volume.restrict P) := by
      simpa [Real.norm_of_nonneg (hw0 _), ENNReal.toReal_ofReal hp0.le] using
        hw.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hp0).ne' ENNReal.ofReal_ne_top
    exact integral_mono i1 i2 fun x => Real.rpow_le_rpow (hm0 x) (hmw x) hp0.le
  have hN : lpAvg P p' (fun x => |u x - ub|) ≤ Sl * lpAvg P p wE :=
    hSP.trans (mul_le_mul_of_nonneg_left hAmono hSl)
  have hN0 : 0 ≤ lpAvg P p' (fun x => |u x - ub|) := lpAvg_nonneg P p' fun x => abs_nonneg _
  have hA0 : 0 ≤ lpAvg P p wE := lpAvg_nonneg P p hw0
  have hB0 : 0 ≤ lpAvg P p sE := lpAvg_nonneg P p hs0
  rw [hsplit]
  have e1 : ∫ x in P, |u x - c| * wE x ≤
      V * (1 + κ) * lpAvg P p' (fun x => |u x - ub|) * lpAvg P p wE := hH1
  have e2 : ∫ x in P, |u x - c| * sE x ≤
      V * (1 + κ) * lpAvg P p' (fun x => |u x - ub|) * lpAvg P p sE := hH2
  have hK : 0 ≤ V * (1 + κ) := mul_nonneg hP0.le (by linarith)
  calc L * (∫ x in P, |u x - c| * wE x) + ∫ x in P, |u x - c| * sE x
      ≤ L * (V * (1 + κ) * lpAvg P p' (fun x => |u x - ub|) * lpAvg P p wE) +
        V * (1 + κ) * lpAvg P p' (fun x => |u x - ub|) * lpAvg P p sE :=
        add_le_add (mul_le_mul_of_nonneg_left e1 hL) e2
    _ = V * (1 + κ) * lpAvg P p' (fun x => |u x - ub|) * (L * lpAvg P p wE + lpAvg P p sE) := by
        ring
    _ ≤ V * (1 + κ) * (Sl * lpAvg P p wE) * (L * lpAvg P p wE + lpAvg P p sE) := by
        gcongr
    _ = _ := by ring

/-- Jensen for the exponent `2θ < 2`: `(avg s^{2θ})^{1/θ} ≤ avg s²`. -/
theorem lpAvg_sq_le {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hP0 : 0 < (volume P).toReal) (hPfin : volume P ≠ ⊤)
    {s : Vec d → ℝ} (hs0 : ∀ x, 0 ≤ s x)
    (h1 : IntegrableOn (fun x => s x ^ (2 * θ)) P)
    (h2 : IntegrableOn (fun x => s x ^ (2 : ℕ)) P) :
    (lpAvg P (2 * θ) s) ^ 2 ≤ (volume P).toReal⁻¹ * ∫ x in P, s x ^ (2 : ℕ) := by
  have hPpos : 0 < volume P := ENNReal.toReal_pos_iff.mp hP0 |>.1
  have hprob := isProbabilityMeasure_normalizedVolumeOn_of_pos_of_lt_top hPpos hPfin.lt_top
  have hI1 := integrable_normalizedVolumeOn_of_integrableOn h1 hPpos
  have hG0 : ∀ x, 0 ≤ s x ^ (2 * θ) := fun x => Real.rpow_nonneg (hs0 x) _
  have hpow : ∀ x, |s x ^ (2 * θ)| ^ (1 / θ) = s x ^ (2 : ℕ) := by
    intro x
    rw [abs_of_nonneg (hG0 x), ← Real.rpow_mul (hs0 x)]
    have : 2 * θ * (1 / θ) = ((2 : ℕ) : ℝ) := by
      push_cast; field_simp
    rw [this, Real.rpow_natCast]
  have hI2 : Integrable (fun x => |s x ^ (2 * θ)| ^ (1 / θ)) (normalizedVolumeOn P) := by
    simp_rw [hpow]
    exact integrable_normalizedVolumeOn_of_integrableOn h2 hPpos
  have hJ := PDE.abs_integral_rpow_le_integral_abs_rpow (μ := normalizedVolumeOn P)
    (f := fun x => s x ^ (2 * θ)) (p := 1 / θ) (by rw [le_div_iff₀ hθ0]; linarith) hI1 hI2
  simp_rw [hpow] at hJ
  rw [integral_normalizedVolumeOn_eq_integralAverage, integral_normalizedVolumeOn_eq_integralAverage]
    at hJ
  have hX0 : 0 ≤ (volume P).toReal⁻¹ * ∫ x in P, s x ^ (2 * θ) :=
    mul_nonneg (inv_nonneg.mpr hP0.le) (integral_nonneg hG0)
  have hsq : (lpAvg P (2 * θ) s) ^ 2 =
      ((volume P).toReal⁻¹ * ∫ x in P, s x ^ (2 * θ)) ^ (1 / θ) := by
    unfold lpAvg
    rw [← Real.rpow_natCast, ← Real.rpow_mul hX0]
    congr 1
    push_cast; field_simp
  rw [hsq]
  have habs : |integralAverage P (fun x => s x ^ (2 * θ))| =
      (volume P).toReal⁻¹ * ∫ x in P, s x ^ (2 * θ) := by
    exact abs_of_nonneg hX0
  rw [habs] at hJ
  exact hJ

theorem lpAvg_sq_eq {θ : ℝ} (hθ0 : 0 < θ) {s : Vec d → ℝ} (hs0 : ∀ x, 0 ≤ s x) :
    (lpAvg P (2 * θ) s) ^ 2 = ((volume P).toReal⁻¹ * ∫ x in P, s x ^ (2 * θ)) ^ (1 / θ) := by
  have hX0 : 0 ≤ (volume P).toReal⁻¹ * ∫ x in P, s x ^ (2 * θ) :=
    mul_nonneg (inv_nonneg.mpr ENNReal.toReal_nonneg)
      (integral_nonneg fun x => Real.rpow_nonneg (hs0 x) _)
  unfold lpAvg
  rw [← Real.rpow_natCast, ← Real.rpow_mul hX0]
  congr 1
  push_cast; field_simp

/-- If `u` vanishes on a large subset `Z ⊆ P`, its mean is controlled by its oscillation:
`|ū| ≤ κ ‖u - ū‖_{L^{p'}(P)}` (normalized) whenever `|Z| ≥ κ^{-p'} |P|`. -/
theorem abs_le_mul_lpAvg_of_zero {p' : ℝ} (hp' : 0 < p') {Z : Set (Vec d)}
    (hZP : Z ⊆ P) (hZ : MeasurableSet Z)
    (hP0 : 0 < (volume P).toReal) {u : Vec d → ℝ} {ub κ : ℝ} (hκ : 0 < κ)
    (hint : IntegrableOn (fun x => |u x - ub| ^ p') P)
    (hu : ∀ x ∈ Z, u x = 0)
    (hvol : (κ ^ p')⁻¹ * (volume P).toReal ≤ (volume Z).toReal) :
    |ub| ≤ κ * lpAvg P p' (fun x => |u x - ub|) := by
  set V := (volume P).toReal with hV
  have hF0 : ∀ x, 0 ≤ |u x - ub| ^ p' := fun x => Real.rpow_nonneg (abs_nonneg _) _
  have hZint : ∫ x in Z, |u x - ub| ^ p' = |ub| ^ p' * (volume Z).toReal := by
    rw [setIntegral_congr_fun hZ (g := fun _ => |ub| ^ p') (fun x hx => by
      simp only [hu x hx, zero_sub, abs_neg])]
    rw [setIntegral_const]
    simp [Measure.real, mul_comm]
  have hmono : ∫ x in Z, |u x - ub| ^ p' ≤ ∫ x in P, |u x - ub| ^ p' :=
    setIntegral_mono_set hint (Filter.Eventually.of_forall hF0)
      (Filter.Eventually.of_forall hZP)
  have hpow : 0 ≤ |ub| ^ p' := Real.rpow_nonneg (abs_nonneg _) _
  have h2 : (|ub| / κ) ^ p' * V ≤ ∫ x in P, |u x - ub| ^ p' := by
    rw [Real.div_rpow (abs_nonneg _) hκ.le]
    calc |ub| ^ p' / κ ^ p' * V = |ub| ^ p' * ((κ ^ p')⁻¹ * V) := by ring
      _ ≤ |ub| ^ p' * (volume Z).toReal := mul_le_mul_of_nonneg_left hvol hpow
      _ = _ := hZint.symm
      _ ≤ _ := hmono
  have h3 : (|ub| / κ) ^ p' ≤ V⁻¹ * ∫ x in P, |u x - ub| ^ p' := by
    rw [le_inv_mul_iff₀ hP0]
    linarith
  have h4 : |ub| / κ ≤ lpAvg P p' (fun x => |u x - ub|) := by
    have := Real.rpow_le_rpow (by positivity) h3 (by positivity : (0 : ℝ) ≤ 1 / p')
    rwa [← Real.rpow_mul (by positivity), mul_one_div_cancel hp'.ne', Real.rpow_one] at this
  rwa [div_le_iff₀ hκ, mul_comm] at h4

end MeyersRH

end PDE
