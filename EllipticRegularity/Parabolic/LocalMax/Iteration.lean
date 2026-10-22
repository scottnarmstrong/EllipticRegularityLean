module

public import EllipticRegularity.DeGiorgi.MoserIter.Scalar
public import EllipticRegularity.DeGiorgi.MoserIter.EssSup
public import PDEFoundation.Measure.BallVolume

/-!
# Abstract Moser iteration on parabolic cylinders

If a reverse-Hölder step `L^p → L^{pχ}` (`χ = (d+2)/d`) holds between the cylinders
`B_r × (T, -1/2)` with constant `A (1/(ρ-r)² + 1/(T'-T))`, then iterating along the exponents
`p_k = ((d+1)/d) χ^k`, radii `r_k = 3/8 + 2^{-k}/8` and times `T_k = -11/16 - 2^{-k}/16` bounds
the essential supremum on `B_{3/8} × (-11/16, -1/2)` by the `L^{(d+1)/d}` norm on
`B_{1/2} × (-3/4, -1/2)`.  This is pure measure theory and scalar algebra.
-/

@[expose] public section

open MeasureTheory Set Filter Topology Finset
open scoped ENNReal

namespace PDE.Parabolic.LocalMax

/-- The cylinder `B_r × (T, -1/2)`. -/
def moserCyl (d : ℕ) (r T : ℝ) : Set (Vec d × ℝ) :=
  euclideanBall (0 : Vec d) r ×ˢ Ioo T (-1 / 2 : ℝ)

theorem moserCyl_mono (d : ℕ) {r r' T T' : ℝ} (hr : 0 ≤ r) (hrr : r ≤ r') (hT : T' ≤ T) :
    moserCyl d r T ⊆ moserCyl d r' T' :=
  prod_mono (euclideanBall_mono hr hrr) (Ioo_subset_Ioo_left hT)

theorem volume_moserCyl_ne_top (d : ℕ) {r : ℝ} (hr : 0 ≤ r) (T : ℝ) :
    volume (moserCyl d r T) ≠ ⊤ := by
  unfold moserCyl
  rw [Measure.volume_eq_prod, Measure.prod_prod]
  exact ENNReal.mul_ne_top (volume_euclideanBall_ne_top _ hr) (by simp)

/-- One step of the iteration in `ℝ≥0∞`. -/
theorem rpow_step {X J J' : ℝ≥0∞} {χ p : ℝ} (hχ : 0 < χ) (hp : 0 < p)
    (h : J' ≤ X ^ χ * J ^ χ) : J' ^ (p * χ)⁻¹ ≤ X ^ p⁻¹ * J ^ p⁻¹ := by
  have hq : 0 ≤ (p * χ)⁻¹ := by positivity
  calc J' ^ (p * χ)⁻¹ ≤ (X ^ χ * J ^ χ) ^ (p * χ)⁻¹ := ENNReal.rpow_le_rpow h hq
    _ = ((X * J) ^ χ) ^ (p * χ)⁻¹ := by rw [ENNReal.mul_rpow_of_nonneg _ _ hχ.le]
    _ = (X * J) ^ p⁻¹ := by
        rw [← ENNReal.rpow_mul]
        congr 1
        field_simp
    _ = X ^ p⁻¹ * J ^ p⁻¹ := ENNReal.mul_rpow_of_nonneg _ _ (by positivity)

/-- The iterated bound along a sequence of exponents growing by the factor `χ`. -/
theorem iterate_bound {J : ℕ → ℝ≥0∞} {p a : ℕ → ℝ} {χ : ℝ} (hχ : 0 < χ) (hp : ∀ k, 0 < p k)
    (hpχ : ∀ k, p (k + 1) = p k * χ) (ha : ∀ k, 0 ≤ a k)
    (h : ∀ k, J (k + 1) ≤ ENNReal.ofReal (a k) ^ χ * J k ^ χ) (k : ℕ) :
    J k ^ (p k)⁻¹ ≤ ENNReal.ofReal (∏ j ∈ range k, a j ^ (p j)⁻¹) * J 0 ^ (p 0)⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hs := rpow_step hχ (hp k) (h k)
    rw [← hpχ k, ENNReal.ofReal_rpow_of_nonneg (ha k) (inv_nonneg.2 (hp k).le)] at hs
    rw [prod_range_succ, ENNReal.ofReal_mul (prod_nonneg fun j _ =>
      Real.rpow_nonneg (ha j) _)]
    calc J (k + 1) ^ (p (k + 1))⁻¹ ≤ _ := hs
      _ ≤ ENNReal.ofReal (a k ^ (p k)⁻¹) *
            (ENNReal.ofReal (∏ j ∈ range k, a j ^ (p j)⁻¹) * J 0 ^ (p 0)⁻¹) := by gcongr
      _ = _ := by ring

/-- Scalar bound on the step constant. -/
theorem step_const_le {A u : ℝ} (hA : 1 ≤ A) (hu : 1 ≤ u) :
    A * (1 / ((3 / 8 + u⁻¹ / 8) - (3 / 8 + (2 * u)⁻¹ / 8)) ^ 2 +
      1 / ((-11 / 16 - (2 * u)⁻¹ / 16) - (-11 / 16 - u⁻¹ / 16))) ≤ 1280 * A * u ^ 2 := by
  have hu0 : 0 < u := by linarith
  have e1 : (3 / 8 + u⁻¹ / 8) - (3 / 8 + (2 * u)⁻¹ / 8) = 1 / (16 * u) := by
    field_simp; ring
  have e2 : (-11 / 16 - (2 * u)⁻¹ / 16) - (-11 / 16 - u⁻¹ / 16) = 1 / (32 * u) := by
    field_simp; ring
  rw [e1, e2]
  have e3 : 1 / (1 / (16 * u)) ^ 2 + 1 / (1 / (32 * u)) = 256 * u ^ 2 + 32 * u := by
    field_simp; ring
  rw [e3]
  have : 256 * u ^ 2 + 32 * u ≤ 1280 * u ^ 2 := by nlinarith
  have hA0 : 0 ≤ A := by linarith
  calc A * (256 * u ^ 2 + 32 * u) ≤ A * (1280 * u ^ 2) := by gcongr
    _ = _ := by ring

theorem moser_iteration_essSup (d : ℕ) (hd : 0 < d) (A : ℝ) (hA : 1 ≤ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Vec d × ℝ → ℝ,
      AEMeasurable f (volume.restrict (moserCyl d (1 / 2) (-3 / 4))) →
      (∀ p : ℝ, ((d : ℝ) + 1) / d ≤ p → ∀ r ρ T T' : ℝ, 3 / 8 ≤ r → r < ρ → ρ ≤ 1 / 2 →
        -3 / 4 ≤ T → T < T' → T' ≤ -11 / 16 →
        ∫⁻ z in moserCyl d r T', ENNReal.ofReal (f z) ^ (p * (((d : ℝ) + 2) / d)) ≤
          ENNReal.ofReal (A * (1 / (ρ - r) ^ 2 + 1 / (T' - T))) ^ (((d : ℝ) + 2) / d) *
            (∫⁻ z in moserCyl d ρ T, ENNReal.ofReal (f z) ^ p) ^ (((d : ℝ) + 2) / d)) →
      essSup (fun z => ENNReal.ofReal (f z)) (volume.restrict (moserCyl d (3 / 8) (-11 / 16))) ≤
        ENNReal.ofReal C *
          (∫⁻ z in moserCyl d (1 / 2) (-3 / 4), ENNReal.ofReal (f z) ^ (((d : ℝ) + 1) / d)) ^
            ((d : ℝ) / ((d : ℝ) + 1)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨χ, hχdef⟩ : ∃ χ : ℝ, χ = ((d : ℝ) + 2) / d := ⟨_, rfl⟩
  obtain ⟨p0, hp0def⟩ : ∃ p0 : ℝ, p0 = ((d : ℝ) + 1) / d := ⟨_, rfl⟩
  have hχ1 : 1 < χ := by
    rw [hχdef, lt_div_iff₀ hd0]; linarith
  have hp0 : 0 < p0 := by rw [hp0def]; positivity
  have hp01 : p0⁻¹ = (d : ℝ) / ((d : ℝ) + 1) := by rw [hp0def, inv_div]
  have hA' : 1 ≤ 1280 * A := by linarith
  set S₁ := χ / (χ - 1) / p0
  set S₂ := χ / (χ - 1) ^ 2 / p0
  refine ⟨(1280 * A) ^ S₁ * 4 ^ S₂, mul_pos (Real.rpow_pos_of_pos (by linarith) _)
    (Real.rpow_pos_of_pos (by norm_num) _), fun f hf hstep => ?_⟩
  rw [← hχdef, ← hp0def] at hstep
  rw [← hp0def, ← hp01]
  -- sequences
  set p : ℕ → ℝ := fun k => p0 * χ ^ k with hpdef
  set rr : ℕ → ℝ := fun k => 3 / 8 + ((2 : ℝ) ^ k)⁻¹ / 8 with hrr
  set TT : ℕ → ℝ := fun k => -11 / 16 - ((2 : ℝ) ^ k)⁻¹ / 16 with hTT
  set J : ℕ → ℝ≥0∞ := fun k => ∫⁻ z in moserCyl d (rr k) (TT k), ENNReal.ofReal (f z) ^ p k
    with hJ
  have hu1 : ∀ k : ℕ, (1 : ℝ) ≤ 2 ^ k := fun k => one_le_pow₀ (by norm_num)
  have hinv : ∀ k : ℕ, ((2 : ℝ) ^ k)⁻¹ ≤ 1 := fun k => inv_le_one_of_one_le₀ (hu1 k)
  have hinvpos : ∀ k : ℕ, 0 < ((2 : ℝ) ^ k)⁻¹ := fun k => inv_pos.2 (by positivity)
  have hpk : ∀ k, 0 < p k := fun k => mul_pos hp0 (pow_pos (by linarith) _)
  have hpχ : ∀ k, p (k + 1) = p k * χ := fun k => by simp only [hpdef]; ring
  have hstepJ : ∀ k, J (k + 1) ≤
      ENNReal.ofReal (1280 * A * 4 ^ k) ^ χ * J k ^ χ := by
    intro k
    have hu := hu1 k
    have hrk : (2 : ℝ) ^ (k + 1) = 2 * 2 ^ k := by ring
    have hge : p0 ≤ p k := by
      have : (1 : ℝ) ≤ χ ^ k := one_le_pow₀ hχ1.le
      simp only [hpdef]; nlinarith
    have hi := hinv k
    have hi' := hinvpos k
    have hi2 : ((2 : ℝ) ^ (k + 1))⁻¹ = (2 * 2 ^ k)⁻¹ := by rw [hrk]
    have hh : ((2 : ℝ) ^ (k + 1))⁻¹ = ((2 : ℝ) ^ k)⁻¹ / 2 := by
      rw [pow_succ]; field_simp
    have key := hstep (p k) hge (rr (k + 1)) (rr k) (TT k) (TT (k + 1))
      (by simp only [hrr]; linarith [hinvpos (k + 1)])
      (by simp only [hrr]; linarith [hinvpos (k + 1)])
      (by simp only [hrr]; linarith)
      (by simp only [hTT]; linarith)
      (by simp only [hTT]; linarith [hinvpos (k + 1)])
      (by simp only [hTT]; linarith [hinvpos (k + 1)])
    have hconst := step_const_le (u := 2 ^ k) hA hu
    have e4 : (4 : ℝ) ^ k = (2 ^ k) ^ 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, ← pow_mul, mul_comm, pow_mul]
    have hmono : ENNReal.ofReal (A * (1 / (rr k - rr (k + 1)) ^ 2 + 1 / (TT (k + 1) - TT k))) ≤
        ENNReal.ofReal (1280 * A * 4 ^ k) := by
      apply ENNReal.ofReal_le_ofReal
      rw [e4]
      simp only [hrr, hTT, hi2]
      simpa [hrk] using hconst
    calc J (k + 1) = ∫⁻ z in moserCyl d (rr (k + 1)) (TT (k + 1)),
          ENNReal.ofReal (f z) ^ (p k * χ) := by simp only [hJ, hpχ]
      _ ≤ _ := key.trans (by gcongr)
  have hmain := iterate_bound (J := J) (p := p) (a := fun k => 1280 * A * 4 ^ k) (by linarith)
    hpk hpχ (fun k => by positivity) hstepJ
  have hprod : ∀ k, ∏ j ∈ range k, (1280 * A * 4 ^ j) ^ (p j)⁻¹ ≤ (1280 * A) ^ S₁ * 4 ^ S₂ :=
    fun k => PDE.DGNMMoser.prod_geometric_le hχ1 hp0 hA' (by norm_num) k
  -- essSup
  set Q : Set (Vec d × ℝ) := moserCyl d (3 / 8) (-11 / 16) with hQ
  have hfin : IsFiniteMeasure (volume.restrict Q) :=
    ⟨by
      rw [Measure.restrict_apply_univ]
      exact (volume_moserCyl_ne_top d (by norm_num) _).lt_top⟩
  have hQsub : ∀ k, Q ⊆ moserCyl d (rr k) (TT k) := fun k =>
    moserCyl_mono d (by norm_num) (by simp only [hrr]; linarith [hinvpos k])
      (by simp only [hTT]; linarith [hinvpos k])
  have hQbig : Q ⊆ moserCyl d (1 / 2) (-3 / 4) :=
    moserCyl_mono d (by norm_num) (by norm_num) (by norm_num)
  have hfm : AEMeasurable f (volume.restrict Q) :=
    hf.mono_measure (Measure.restrict_mono hQbig le_rfl)
  set g : Vec d × ℝ → ℝ := fun z => max (f z) 0 with hg
  have hgm : AEMeasurable g (volume.restrict Q) := hfm.max aemeasurable_const
  have hgo : (fun z => ENNReal.ofReal (g z)) = fun z => ENNReal.ofReal (f z) := by
    funext z; simp only [hg]; rcases le_total (f z) 0 with h | h <;> simp [h]
  have hgen : ∀ z, ‖g z‖ₑ = ENNReal.ofReal (f z) := fun z => by
    rw [Real.enorm_eq_ofReal (le_max_right _ _), ← congrFun hgo z]
  have hptend : Tendsto p atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hχ1).const_mul_atTop hp0
  have h0 : J 0 = ∫⁻ z in moserCyl d (1 / 2) (-3 / 4), ENNReal.ofReal (f z) ^ p0 := by
    simp only [hJ, hrr, hTT, hpdef]; norm_num
  have hbound := PDE.DGNMMoser.essSup_ofReal_le_of_eLpNorm_le (μ := volume.restrict Q) (f := g) hgm hptend
    (B := ENNReal.ofReal ((1280 * A) ^ S₁ * 4 ^ S₂) * J 0 ^ (p 0)⁻¹) (fun k => by
      have hq0 : ENNReal.ofReal (p k) ≠ 0 := by simpa using hpk k
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hq0 ENNReal.ofReal_ne_top
        hgm.aestronglyMeasurable, ENNReal.toReal_ofReal (hpk k).le]
      simp only [hgen]
      calc (∫⁻ z in Q, ENNReal.ofReal (f z) ^ p k) ^ (1 / p k) ≤ J k ^ (p k)⁻¹ := by
            rw [one_div]
            refine ENNReal.rpow_le_rpow ?_ (inv_nonneg.2 (hpk k).le)
            exact lintegral_mono_set (hQsub k)
        _ ≤ ENNReal.ofReal (∏ j ∈ range k, (1280 * A * 4 ^ j) ^ (p j)⁻¹) * J 0 ^ (p 0)⁻¹ :=
            hmain k
        _ ≤ _ := by gcongr; exact hprod k)
  rw [hgo] at hbound
  have e0 : p 0 = p0 := by simp [hpdef]
  rw [e0, h0] at hbound
  exact hbound

end PDE.Parabolic.LocalMax
