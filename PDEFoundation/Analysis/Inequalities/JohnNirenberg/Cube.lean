module

public import PDEFoundation.Analysis.Inequalities.JohnNirenberg.StoppingPacking
public import PDEFoundation.Analysis.Inequalities.JohnNirenberg.StoppingLocal

/-!
# The John–Nirenberg inequality on cubes

Lemma 1.16. The cube is a Mathlib box `I` (its half-open carrier differs from the closed
cube by a null set), and its dyadic subcubes are the literal dyadic descendants
`dyadicDescendant I p`. The proof is the manuscript's stopping-time argument: Step 2 iterates
the stopping generations and telescopes the means along the chain of ancestors, and Step 3 picks
the generation `m = ⌊(t / (e N) - 1) / 2 ^ d⌋`.
-/

@[expose] public section

namespace PDE.JohnNirenberg

open BoxIntegral MeasureTheory Set
open scoped ENNReal

/-- Step 2 (chain): for a point that is good for every root, exiting the stopping regions
`M` generations after the generation of `p` bounds `|v x - (v)_{I_p}|` by `lam + M 2 ^ d lam`. -/
theorem abs_sub_integralAverage_le_of_notMem_jnRegion {d : ℕ} (I : Box (Fin d))
    {v : Vec d → ℝ} (hv : IntegrableOn v (I : Set (Vec d))) {lam N : ℝ} (hlam : 0 ≤ lam)
    (hNlam : N ≤ lam)
    (hosc : ∀ p : List (Set (Fin d)),
      integralAverage (dyadicDescendant I p : Set (Vec d))
        (fun x => |v x - integralAverage (dyadicDescendant I p : Set (Vec d)) v|) ≤ N)
    {x : Vec d}
    (hgood : ∀ r : List (Set (Fin d)), x ∈ (dyadicDescendant I r : Set (Vec d)) →
      x ∉ jnStopUnion (dyadicDescendant I r) v lam →
        |v x - integralAverage (dyadicDescendant I r : Set (Vec d)) v| ≤ lam) :
    ∀ (M k : ℕ) (p : List (Set (Fin d))), p ∈ jnGeneration I v lam k →
      x ∈ (dyadicDescendant I p : Set (Vec d)) → x ∉ jnRegion I v lam (k + M) →
        |v x - integralAverage (dyadicDescendant I p : Set (Vec d)) v| ≤
          lam + M * ((2 : ℝ) ^ d * lam) := by
  intro M
  induction M with
  | zero =>
      intro k p hp hxp hxout
      exact (hxout (mem_jnRegion_of_mem hp hxp)).elim
  | succ M ih =>
      intro k p hp hxp hxout
      have h2 : 0 ≤ (2 : ℝ) ^ d * lam := by positivity
      by_cases hxstop : x ∈ jnStopUnion (dyadicDescendant I p) v lam
      · obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hxstop
        obtain ⟨hq, hxq⟩ := Set.mem_iUnion.mp hxq
        have hp' : p ++ q ∈ jnGeneration I v lam (k + 1) :=
          (mem_jnGeneration_succ I v lam k _).mpr ⟨p, hp, q, hq, rfl⟩
        have hxp' : x ∈ (dyadicDescendant I (p ++ q) : Set (Vec d)) := by
          rwa [dyadicDescendant_append]
        have hxout' : x ∉ jnRegion I v lam ((k + 1) + M) := by
          rwa [show k + 1 + M = k + (M + 1) by omega]
        have hrec := ih (k + 1) (p ++ q) hp' hxp' hxout'
        have hsub : (dyadicDescendant I p : Set (Vec d)) ⊆ (I : Set (Vec d)) :=
          dyadicDescendant_le I p
        have hjump := abs_integralAverage_sub_le_of_firstPrefixStop (dyadicDescendant I p)
          (hv.mono_set hsub) ((hosc p).trans hNlam) hq
        rw [← dyadicDescendant_append] at hjump
        calc
          |v x - integralAverage (dyadicDescendant I p : Set (Vec d)) v| ≤
              |v x - integralAverage (dyadicDescendant I (p ++ q) : Set (Vec d)) v| +
                |integralAverage (dyadicDescendant I (p ++ q) : Set (Vec d)) v -
                  integralAverage (dyadicDescendant I p : Set (Vec d)) v| :=
            abs_sub_le _ _ _
          _ ≤ (lam + M * ((2 : ℝ) ^ d * lam)) + (2 : ℝ) ^ d * lam := add_le_add hrec hjump
          _ = lam + ((M + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ d * lam) := by push_cast; ring
      · have hb := hgood p hxp hxstop
        have hM : 0 ≤ ((M + 1 : ℕ) : ℝ) * ((2 : ℝ) ^ d * lam) := by positivity
        linarith

/-- Step 2 (conclusion): the superlevel set at height `lam (1 + m 2 ^ d)` is contained in the
`m`-th stopping region up to a null set. -/
theorem volume_setOf_lt_abs_sub_le_volume_jnRegion {d : ℕ} (I : Box (Fin d)) (hd : 0 < d)
    {v : Vec d → ℝ} (hv : IntegrableOn v (I : Set (Vec d))) {lam N : ℝ} (hlam : 0 ≤ lam)
    (hNlam : N ≤ lam)
    (hosc : ∀ p : List (Set (Fin d)),
      integralAverage (dyadicDescendant I p : Set (Vec d))
        (fun x => |v x - integralAverage (dyadicDescendant I p : Set (Vec d)) v|) ≤ N)
    (m : ℕ) :
    volume {x ∈ (I : Set (Vec d)) |
        lam + m * ((2 : ℝ) ^ d * lam) < |v x - integralAverage (I : Set (Vec d)) v|} ≤
      volume (jnRegion I v lam m) := by
  apply measure_mono_ae
  filter_upwards [ae_forall_abs_sub_integralAverage_le I hd hv lam] with x hgood hxs
  obtain ⟨hxI, hxlt⟩ := hxs
  by_contra hxR
  have hb := abs_sub_integralAverage_le_of_notMem_jnRegion I hv hlam hNlam hosc hgood m 0 []
    (by simp) (by simpa using hxI) (by simpa using hxR)
  rw [dyadicDescendant_nil] at hb
  exact (not_lt_of_ge hb) hxlt

/-- **John–Nirenberg inequality on cubes** (Lemma 1.16). If `v ∈ L¹(I)` has mean
oscillation at most `N` on every dyadic subcube of `I` (including `I`), then for every `t > 0`,
`|{x ∈ I : |v(x) - (v)_I| > t}| ≤ e² |I| exp(-t / (2 ^ d e N))`. (For `t ≤ 0` the bound is
trivial, so no sign condition on `t` is imposed.) -/
theorem volume_lt_abs_sub_integralAverage_le {d : ℕ} (hd : 0 < d) (I : Box (Fin d))
    {v : Vec d → ℝ} (hv : IntegrableOn v (I : Set (Vec d))) {N : ℝ} (hN : 0 < N)
    (hosc : ∀ p : List (Set (Fin d)),
      integralAverage (dyadicDescendant I p : Set (Vec d))
        (fun x => |v x - integralAverage (dyadicDescendant I p : Set (Vec d)) v|) ≤ N)
    (t : ℝ) :
    (volume {x ∈ (I : Set (Vec d)) | t < |v x - integralAverage (I : Set (Vec d)) v|}).toReal ≤
      Real.exp 2 * Real.exp (-(t / ((2 : ℝ) ^ d * Real.exp 1 * N))) *
        (volume (I : Set (Vec d))).toReal := by
  set lam := Real.exp 1 * N with hlam_def
  have he1 : 1 < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := 1) one_ne_zero
    linarith
  have hlam : 0 < lam := mul_pos (Real.exp_pos 1) hN
  have hNlam : N ≤ lam := by
    rw [hlam_def]; nlinarith
  have h2d : (1 : ℝ) ≤ 2 ^ d := one_le_pow₀ (by norm_num)
  have hItop := I.measure_coe_lt_top volume
  have hVol := volume_box_toReal_pos I
  set S := {x ∈ (I : Set (Vec d)) | t < |v x - integralAverage (I : Set (Vec d)) v|}
  have hS : (volume S).toReal ≤ (volume (I : Set (Vec d))).toReal :=
    ENNReal.toReal_mono hItop.ne (measure_mono fun x hx => hx.1)
  have hden : (2 : ℝ) ^ d * Real.exp 1 * N = (2 : ℝ) ^ d * lam := by rw [hlam_def]; ring
  rw [hden]
  by_cases htlam : t < lam
  · -- Small `t`: the right side is at least `|I|`.
    refine hS.trans (le_mul_of_one_le_left hVol.le ?_)
    have hq : t / ((2 : ℝ) ^ d * lam) < 1 := by
      rw [div_lt_one (by positivity)]
      nlinarith
    have hexp : Real.exp (-1) ≤ Real.exp (-(t / ((2 : ℝ) ^ d * lam))) :=
      Real.exp_le_exp.mpr (by linarith)
    have h21 : Real.exp 2 * Real.exp (-1) = Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos 2, Real.exp_pos (-1)]
  · -- Large `t`: use the generation `m = ⌊(t / lam - 1) / 2 ^ d⌋`.
    push Not at htlam
    set a := (t / lam - 1) / (2 : ℝ) ^ d
    have ha : 0 ≤ a := by
      apply div_nonneg _ (by positivity)
      rw [sub_nonneg, le_div_iff₀ hlam]; linarith
    set m := ⌊a⌋₊
    have hm_le : (m : ℝ) ≤ a := Nat.floor_le ha
    have hm_gt : a < m + 1 := Nat.lt_floor_add_one a
    have hlevel : lam + m * ((2 : ℝ) ^ d * lam) ≤ t := by
      have : (m : ℝ) * (2 : ℝ) ^ d ≤ t / lam - 1 := by
        rw [← le_div_iff₀ (by positivity)]; exact hm_le
      have h' : (m : ℝ) * (2 : ℝ) ^ d * lam ≤ (t / lam - 1) * lam :=
        mul_le_mul_of_nonneg_right this hlam.le
      have h'' : (t / lam - 1) * lam = t - lam := by field_simp
      nlinarith
    have hsub : S ⊆ {x ∈ (I : Set (Vec d)) |
        lam + m * ((2 : ℝ) ^ d * lam) < |v x - integralAverage (I : Set (Vec d)) v|} :=
      fun x hx => ⟨hx.1, lt_of_le_of_lt hlevel hx.2⟩
    have hmeas := (measure_mono hsub).trans
      ((volume_setOf_lt_abs_sub_le_volume_jnRegion I hd hv hlam.le hNlam hosc m).trans
        (volume_jnRegion_le I hv hlam hN.le hosc m))
    have hratio : N / lam = Real.exp (-1) := by
      rw [hlam_def, Real.exp_neg]; field_simp
    have hpow : (N / lam) ^ m = Real.exp (-(m : ℝ)) := by
      rw [hratio, ← Real.exp_nat_mul]; ring_nf
    have hreal : (volume S).toReal ≤ Real.exp (-(m : ℝ)) * (volume (I : Set (Vec d))).toReal := by
      have h := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hItop.ne) hmeas
      rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), hpow] at h
    refine hreal.trans (mul_le_mul_of_nonneg_right ?_ hVol.le)
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hta : t / ((2 : ℝ) ^ d * lam) = a + 1 / (2 : ℝ) ^ d := by
      simp only [a]; field_simp; ring
    have hinv : 1 / (2 : ℝ) ^ d ≤ 1 := by
      rw [div_le_one (by positivity)]; exact h2d
    rw [hta]
    linarith

end PDE.JohnNirenberg
