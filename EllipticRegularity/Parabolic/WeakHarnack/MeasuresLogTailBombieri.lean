module

public import EllipticRegularity.Parabolic.WeakHarnack.MeasuresLogTail

/-!
# Log-tail bounds on the cylinders and the `hlog` hypothesis of Bombieri-Giusti

* `posNegCyl_log_tail(_at)`: the manuscript's (5.21) on `posCyl d 1` and `negCyl d 1`,
  from the hypotheses of `logTail_integrated` for `cutoffMeasure d` (`T₁ = -7/8`, `T₂ = 0`, level
  time `t₀ ∈ (-3/8,-11/32) \ N` given or chosen).
* `hlog_pos`, `hlog_neg`, `bombieri_hlog_of_log_tail`: the `hlog` hypothesis of
  `PDE.Bombieri.bombieri_giusti` for `f = e^{-k} v` on `posCyl d 1` and `f = e^k / v` on `negCyl d 1`
  with respect to `cylMeasure`.
-/

@[expose] public section

open MeasureTheory Set intervalIntegral
open scoped ENNReal

namespace PDE.Parabolic.WeakHarnack

variable {d : ℕ}

theorem posCyl_one_subset_slab {t₀ : ℝ} (ht₀ : -3 / 8 ≤ t₀) :
    posCyl d 1 ⊆ euclideanBall (0 : Vec d) (3 / 4) ×ˢ Ioc (-7 / 8 : ℝ) t₀ := by
  rw [posCyl_one]
  exact prod_mono le_rfl (Ioo_subset_Ioc_self.trans (Ioc_subset_Ioc le_rfl ht₀))

theorem negCyl_one_subset_slab {t₀ : ℝ} (ht₀ : t₀ ≤ -11 / 32) :
    negCyl d 1 ⊆ euclideanBall (0 : Vec d) (3 / 4) ×ˢ Ioc t₀ 0 := by
  rw [negCyl_one]
  exact prod_mono le_rfl (Ioc_subset_Ioc ht₀ le_rfl)

/-- A null set misses some point of every nonempty open interval. -/
theorem exists_mem_Ioo_notMem_of_volume_zero {N : Set ℝ} (hN : volume N = 0) {a b : ℝ}
    (hab : a < b) : ∃ t₀ ∈ Ioo a b, t₀ ∉ N := by
  by_contra h
  push Not at h
  have : volume (Ioo a b) ≤ 0 := hN ▸ measure_mono (fun t ht => h t ht)
  rw [Real.volume_Ioo] at this
  simp only [nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at this
  linarith

/-- The free level time: some `t₀ ∈ (-3/8, -11/32)` outside the null set `N`. -/
theorem exists_levelTime {N : Set ℝ} (hN : volume N = 0) :
    ∃ t₀ ∈ Ioo (-3 / 8 : ℝ) (-11 / 32), t₀ ∉ N :=
  exists_mem_Ioo_notMem_of_volume_zero hN (by norm_num)

/-- **Log tail on the cylinders** (manuscript (5.21)), at a free level time
`t₀ ∈ (-3/8, -11/32) \ N`.  Hypotheses are those of `logTail_integrated` for
`ν = cutoffMeasure d`, `w x t = g (x,t)`, `T₁ = -7/8`, `T₂ = 0`. -/
theorem posNegCyl_log_tail_at {g : Vec d × ℝ → ℝ} (hg : Measurable g) {c K : ℝ} (N : Set ℝ)
    (hc : 0 < c) (hK : 0 ≤ K) (hN : volume N = 0)
    (hL2 : ∀ t ∈ Icc (-7 / 8 : ℝ) 0, t ∉ N → MemLp (fun x => g (x, t)) 2 (cutoffMeasure d))
    (hV : IntervalIntegrable
      (fun t => ∫ x, (g (x, t) - ∫ y, g (y, t) ∂(cutoffMeasure d)) ^ 2 ∂(cutoffMeasure d))
      volume (-7 / 8) 0)
    (hdiff : ∀ t₁ ∈ Icc (-7 / 8 : ℝ) 0, ∀ t₂ ∈ Icc (-7 / 8 : ℝ) 0, t₁ ∉ N → t₂ ∉ N → t₁ < t₂ →
      ∫ τ in t₁..t₂, (c * ∫ x, (g (x, τ) - ∫ y, g (y, τ) ∂(cutoffMeasure d)) ^ 2
          ∂(cutoffMeasure d) - K) ≤
        (∫ x, g (x, t₂) ∂(cutoffMeasure d)) - ∫ x, g (x, t₁) ∂(cutoffMeasure d))
    {t₀ : ℝ} (ht₀I : t₀ ∈ Ioo (-3 / 8 : ℝ) (-11 / 32)) (ht₀ : t₀ ∉ N) :
    ∃ k : ℝ, ∀ ℓ : ℝ, 0 < ℓ →
      volume (posCyl d 1 ∩ {z | k + ℓ < g z}) + volume (negCyl d 1 ∩ {z | g z < k - ℓ}) ≤
        ENNReal.ofReal ((cutoffMass d).toReal * (4 / c + 4 * K * (0 - (-7 / 8 : ℝ)) ^ 2) / ℓ) := by
  refine ⟨∫ y, g (y, t₀) ∂(cutoffMeasure d), fun ℓ hℓ => ?_⟩
  have htail := logTail_integrated (cutoffMeasure d) (fun x t => g (x, t)) (T₁ := -7 / 8)
    (T₂ := 0) (t₀ := t₀) (c := c) (K := K) N (by linarith [ht₀I.1]) (by linarith [ht₀I.2])
    hc hK hN hL2 hV hdiff ht₀ hℓ
  set k := ∫ y, g (y, t₀) ∂(cutoffMeasure d) with hk
  have hν : ∀ A : Set (Vec d), MeasurableSet A →
      volume (A ∩ euclideanBall (0 : Vec d) (3 / 4)) ≤ cutoffMass d * cutoffMeasure d A :=
    fun A hA => volume_inter_le_cutoffMass_mul hA
  have hE1 : MeasurableSet {z : Vec d × ℝ | k + ℓ < g z} := measurableSet_lt measurable_const hg
  have hE2 : MeasurableSet {z : Vec d × ℝ | g z < k - ℓ} := measurableSet_lt hg measurable_const
  have h1 := volume_slab_inter_le (cutoffMass_ne_top d) (cutoffMeasure d) hν hE1
    (measurableSet_Ioc (a := (-7 / 8 : ℝ)) (b := t₀))
  have h2 := volume_slab_inter_le (cutoffMass_ne_top d) (cutoffMeasure d) hν hE2
    (measurableSet_Ioc (a := t₀) (b := 0))
  have hpos : volume (posCyl d 1 ∩ {z | k + ℓ < g z}) ≤
      cutoffMass d * ∫⁻ t in Ioc (-7 / 8 : ℝ) t₀,
        cutoffMeasure d {x | k + ℓ < g (x, t)} :=
    (measure_mono (inter_subset_inter_left _ (posCyl_one_subset_slab ht₀I.1.le))).trans h1
  have hneg : volume (negCyl d 1 ∩ {z | g z < k - ℓ}) ≤
      cutoffMass d * ∫⁻ t in Ioc t₀ 0, cutoffMeasure d {x | g (x, t) < k - ℓ} :=
    (measure_mono (inter_subset_inter_left _ (negCyl_one_subset_slab ht₀I.2.le))).trans h2
  calc _ ≤ cutoffMass d * (∫⁻ t in Ioc (-7 / 8 : ℝ) t₀, cutoffMeasure d {x | k + ℓ < g (x, t)}) +
        cutoffMass d * ∫⁻ t in Ioc t₀ 0, cutoffMeasure d {x | g (x, t) < k - ℓ} :=
        add_le_add hpos hneg
    _ = cutoffMass d * ((∫⁻ t in Ioc (-7 / 8 : ℝ) t₀,
          cutoffMeasure d {x | k + ℓ < g (x, t)}) +
        ∫⁻ t in Ioc t₀ 0, cutoffMeasure d {x | g (x, t) < k - ℓ}) := (mul_add _ _ _).symm
    _ ≤ cutoffMass d * ENNReal.ofReal ((4 / c + 4 * K * (0 - (-7 / 8 : ℝ)) ^ 2) / ℓ) := by
        gcongr
    _ = _ := by
        conv_lhs => rw [← ENNReal.ofReal_toReal (cutoffMass_ne_top d)]
        rw [← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
        congr 1; ring

/-- **Packaged log tail**: only the hypotheses of `logTail_integrated` with a null set `N`;
the level time `t₀ ∈ (-3/8,-11/32) \ N` is chosen internally (`exists_levelTime`). -/
theorem posNegCyl_log_tail {g : Vec d × ℝ → ℝ} (hg : Measurable g) {c K : ℝ} (N : Set ℝ)
    (hc : 0 < c) (hK : 0 ≤ K) (hN : volume N = 0)
    (hL2 : ∀ t ∈ Icc (-7 / 8 : ℝ) 0, t ∉ N → MemLp (fun x => g (x, t)) 2 (cutoffMeasure d))
    (hV : IntervalIntegrable
      (fun t => ∫ x, (g (x, t) - ∫ y, g (y, t) ∂(cutoffMeasure d)) ^ 2 ∂(cutoffMeasure d))
      volume (-7 / 8) 0)
    (hdiff : ∀ t₁ ∈ Icc (-7 / 8 : ℝ) 0, ∀ t₂ ∈ Icc (-7 / 8 : ℝ) 0, t₁ ∉ N → t₂ ∉ N → t₁ < t₂ →
      ∫ τ in t₁..t₂, (c * ∫ x, (g (x, τ) - ∫ y, g (y, τ) ∂(cutoffMeasure d)) ^ 2
          ∂(cutoffMeasure d) - K) ≤
        (∫ x, g (x, t₂) ∂(cutoffMeasure d)) - ∫ x, g (x, t₁) ∂(cutoffMeasure d)) :
    ∃ k : ℝ, ∀ ℓ : ℝ, 0 < ℓ →
      volume (posCyl d 1 ∩ {z | k + ℓ < g z}) + volume (negCyl d 1 ∩ {z | g z < k - ℓ}) ≤
        ENNReal.ofReal ((cutoffMass d).toReal * (4 / c + 4 * K * (0 - (-7 / 8 : ℝ)) ^ 2) / ℓ) := by
  obtain ⟨t₀, ht₀I, ht₀⟩ := exists_levelTime hN
  exact posNegCyl_log_tail_at hg N hc hK hN hL2 hV hdiff ht₀I ht₀

/-- Passing from a Lebesgue-measure tail bound to the normalized measure of `S`. -/
theorem cylMeasure_inter_le {α : Type*} [MeasureSpace α] {S E : Set α} (hS : MeasurableSet S)
    (h0 : volume S ≠ 0) (ht : volume S ≠ ⊤) {D lam c : ℝ} (hlam : 0 < lam)
    (hvol : volume (S ∩ E) ≤ ENNReal.ofReal (D / lam))
    (hc : D / (volume S).toReal ≤ c) :
    cylMeasure S (S ∩ E) ≤ ENNReal.ofReal (c / lam) := by
  have hVpos : 0 < (volume S).toReal := ENNReal.toReal_pos h0 ht
  rw [cylMeasure, Measure.smul_apply, Measure.restrict_apply' hS,
    inter_eq_left.2 inter_subset_left, smul_eq_mul]
  calc (volume S)⁻¹ * volume (S ∩ E) ≤ (volume S)⁻¹ * ENNReal.ofReal (D / lam) := by gcongr
    _ = ENNReal.ofReal ((volume S).toReal⁻¹) * ENNReal.ofReal (D / lam) := by
        rw [ENNReal.ofReal_inv_of_pos hVpos, ENNReal.ofReal_toReal ht]
    _ ≤ ENNReal.ofReal (c / lam) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        apply ENNReal.ofReal_le_ofReal
        calc (volume S).toReal⁻¹ * (D / lam) = (D / (volume S).toReal) / lam := by
              field_simp
          _ ≤ c / lam := by gcongr

/-- `hlog` for `f = e^{-k} v` on `posCyl d 1`, from the tail bound above `k`. -/
theorem hlog_pos {v : Vec d × ℝ → ℝ} (hvpos : ∀ z, 0 < v z) {k D c : ℝ}
    (htail : ∀ ℓ : ℝ, 0 < ℓ →
      volume (posCyl d 1 ∩ {z | k + ℓ < Real.log (v z)}) ≤ ENNReal.ofReal (D / ℓ))
    (hc : D / (volume (posCyl d 1)).toReal ≤ c) :
    ∀ lam : ℝ, 0 < lam →
      cylMeasure (posCyl d 1)
        (posCyl d 1 ∩ {z | lam < Real.log (Real.exp (-k) * v z)}) ≤ ENNReal.ofReal (c / lam) := by
  intro lam hlam
  have hset : posCyl d 1 ∩ {z | lam < Real.log (Real.exp (-k) * v z)} =
      posCyl d 1 ∩ {z | k + lam < Real.log (v z)} := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, and_congr_right_iff]
    intro _
    rw [Real.log_mul (Real.exp_pos _).ne' (hvpos z).ne', Real.log_exp]
    constructor <;> intro h <;> linarith
  rw [hset]
  exact cylMeasure_inter_le (measurableSet_posCyl _) (volume_posCyl_pos (by norm_num)).ne'
    (volume_posCyl_ne_top (by norm_num)) hlam (htail lam hlam) hc

/-- `hlog` for `f = e^{k} / v` on `negCyl d 1`, from the tail bound below `k`. -/
theorem hlog_neg {v : Vec d × ℝ → ℝ} (hvpos : ∀ z, 0 < v z) {k D c : ℝ}
    (htail : ∀ ℓ : ℝ, 0 < ℓ →
      volume (negCyl d 1 ∩ {z | Real.log (v z) < k - ℓ}) ≤ ENNReal.ofReal (D / ℓ))
    (hc : D / (volume (negCyl d 1)).toReal ≤ c) :
    ∀ lam : ℝ, 0 < lam →
      cylMeasure (negCyl d 1)
        (negCyl d 1 ∩ {z | lam < Real.log (Real.exp k / v z)}) ≤ ENNReal.ofReal (c / lam) := by
  intro lam hlam
  have hset : negCyl d 1 ∩ {z | lam < Real.log (Real.exp k / v z)} =
      negCyl d 1 ∩ {z | Real.log (v z) < k - lam} := by
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, and_congr_right_iff]
    intro _
    rw [Real.log_div (Real.exp_pos _).ne' (hvpos z).ne', Real.log_exp]
    constructor <;> intro h <;> linarith
  rw [hset]
  exact cylMeasure_inter_le (measurableSet_negCyl _) (volume_negCyl_pos (by norm_num)).ne'
    (volume_negCyl_ne_top (by norm_num)) hlam (htail lam hlam) hc

/-- Both `hlog` hypotheses at once from the combined log tail
(output of `posNegCyl_log_tail`, with `g = log ∘ v`). -/
theorem bombieri_hlog_of_log_tail {v : Vec d × ℝ → ℝ} (hvpos : ∀ z, 0 < v z) {k D : ℝ}
    (htail : ∀ ℓ : ℝ, 0 < ℓ →
      volume (posCyl d 1 ∩ {z | k + ℓ < Real.log (v z)}) +
        volume (negCyl d 1 ∩ {z | Real.log (v z) < k - ℓ}) ≤ ENNReal.ofReal (D / ℓ))
    {c₁ c₂ : ℝ} (hc₁ : D / (volume (posCyl d 1)).toReal ≤ c₁)
    (hc₂ : D / (volume (negCyl d 1)).toReal ≤ c₂) :
    (∀ lam : ℝ, 0 < lam →
      cylMeasure (posCyl d 1)
        (posCyl d 1 ∩ {z | lam < Real.log (Real.exp (-k) * v z)}) ≤ ENNReal.ofReal (c₁ / lam)) ∧
    (∀ lam : ℝ, 0 < lam →
      cylMeasure (negCyl d 1)
        (negCyl d 1 ∩ {z | lam < Real.log (Real.exp k / v z)}) ≤ ENNReal.ofReal (c₂ / lam)) :=
  ⟨hlog_pos hvpos (fun ℓ hℓ => le_trans le_self_add (htail ℓ hℓ)) hc₁,
    hlog_neg hvpos (fun ℓ hℓ => le_trans le_add_self (htail ℓ hℓ)) hc₂⟩

/-- The `hrh` hypothesis of `bombieri_giusti` is monotone in the constant `c`: if it holds with
`c₁ ≥ 1` (indeed `c₁ > 0` suffices) then it holds with any `c ≥ c₁`. -/
theorem hrh_mono_const {X : Type*} [MeasurableSpace X] (δ α₀ m : ℝ) (hα₀ : 0 < α₀)
    (ν : Measure X) (U : ℝ → Set X) (f : X → ℝ) {c₁ c : ℝ} (hc₁ : 0 < c₁) (hc : c₁ ≤ c)
    (hrh : ∀ σ' σ : ℝ, δ ≤ σ' → σ' < σ → σ ≤ 1 → ∀ α : ℝ, 0 < α → α ≤ min 1 (α₀ / 2) →
      eLpNorm f (ENNReal.ofReal α₀) (ν.restrict (U σ')) ≤
        ENNReal.ofReal ((c₁ * (σ - σ') ^ (-m)) ^ (1 / α - 1 / α₀)) *
          eLpNorm f (ENNReal.ofReal α) (ν.restrict (U σ))) :
    ∀ σ' σ : ℝ, δ ≤ σ' → σ' < σ → σ ≤ 1 → ∀ α : ℝ, 0 < α → α ≤ min 1 (α₀ / 2) →
      eLpNorm f (ENNReal.ofReal α₀) (ν.restrict (U σ')) ≤
        ENNReal.ofReal ((c * (σ - σ') ^ (-m)) ^ (1 / α - 1 / α₀)) *
          eLpNorm f (ENNReal.ofReal α) (ν.restrict (U σ)) := by
  intro σ' σ h1 h2 h3 α hα hαle
  refine (hrh σ' σ h1 h2 h3 α hα hαle).trans ?_
  have hd : 0 < σ - σ' := by linarith
  have hexp : 0 ≤ 1 / α - 1 / α₀ := by
    have : α ≤ α₀ := hαle.trans ((min_le_right _ _).trans (by linarith))
    rw [sub_nonneg]; exact one_div_le_one_div_of_le hα this
  gcongr

end PDE.Parabolic.WeakHarnack
