module

public import EllipticRegularity.Ch4.GreenHarnack.ChainDef

/-!
# Radial segments and arcs of small angle

For `r > 0` let `annulusSet r = {z | r/4 ≤ |z| ≤ 3r/2}` (Euclidean norm). A radial segment
and the normalized chord between two points of the sphere of radius `r` with nonnegative
inner product are Lipschitz paths in this set; hence they give chains of step `< r/16`.
-/

@[expose] public section

namespace PDE.Ch4GreenHarnack

open PDE

variable {d : ℕ}

/-- The closed thick annulus `{r/4 ≤ |z| ≤ 3r/2}` (Euclidean norm). -/
def annulusSet (d : ℕ) (r : ℝ) : Set (Vec d) :=
  {z | r / 4 ≤ vecEuclideanNorm z ∧ vecEuclideanNorm z ≤ 3 * r / 2}

theorem vecEuclideanNorm_sub_le' (x y : Vec d) :
    vecEuclideanNorm (x - y) ≤ vecEuclideanNorm x + vecEuclideanNorm y := by
  have := vecEuclideanNorm_add_le x (-y)
  rwa [vecEuclideanNorm_neg, ← sub_eq_add_neg] at this

theorem abs_sub_norm_le (x y : Vec d) :
    |vecEuclideanNorm x - vecEuclideanNorm y| ≤ vecEuclideanNorm (x - y) := by
  rw [abs_le]
  constructor
  · have h3 := vecEuclideanNorm_add_le x (y - x)
    rw [add_sub_cancel, vecEuclideanNorm_sub_comm y x] at h3
    linarith
  · have h2 := vecEuclideanNorm_add_le (x - y) y
    rw [sub_add_cancel] at h2
    linarith

theorem vecDot_smul_left' (c : ℝ) (x y : Vec d) : vecDot (c • x) y = c * vecDot x y := by
  simp [vecDot, Finset.mul_sum, mul_assoc]

theorem vecDot_smul_right' (c : ℝ) (x y : Vec d) : vecDot x (c • y) = c * vecDot x y := by
  simp [vecDot, Finset.mul_sum]; congr 1; ext; ring

theorem annulusSet_of_norm_eq {r : ℝ} (hr : 0 < r) {x : Vec d} (hx : vecEuclideanNorm x = r) :
    x ∈ annulusSet d r := ⟨by rw [hx]; linarith, by rw [hx]; linarith⟩

/-! ### Radial segments -/

theorem radial_chain {r : ℝ} (hr : 0 < r) {x : Vec d} (hx : x ∈ annulusSet d r) :
    IsChain (annulusSet d r) (r / 16) 13 x ((r / vecEuclideanNorm x) • x) := by
  obtain ⟨hx1, hx2⟩ := hx
  have hX : 0 < vecEuclideanNorm x := by linarith
  set X := vecEuclideanNorm x with hXdef
  set γ : ℝ → Vec d := fun t => ((1 - t) + t * (r / X)) • x with hγ
  have hn : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → vecEuclideanNorm (γ t) = (1 - t) * X + t * r := by
    intro t ht
    have : 0 ≤ (1 - t) + t * (r / X) := by
      have := ht.1; have := ht.2; have : 0 ≤ t * (r / X) := by positivity
      linarith
    simp only [hγ, vecEuclideanNorm_smul, abs_of_nonneg this]
    rw [← hXdef]; field_simp
  have h := IsChain.of_lipschitz (K := annulusSet d r) (s := r / 16) (L := 3 * r / 4) (γ := γ)
    (n := 13) ?_ ?_ (by norm_num) (by linarith)
  · simpa [hγ] using h
  · intro t ht
    rw [annulusSet, Set.mem_ofPred_eq, hn t ht]
    have := ht.1; have := ht.2
    constructor <;> nlinarith
  · intro t ht t' ht'
    have : γ t - γ t' = ((t - t') * (r / X - 1)) • x := by
      simp only [hγ, ← sub_smul]; congr 1; ring
    rw [this, vecEuclideanNorm_smul, ← hXdef, abs_mul]
    have h2 : |r / X - 1| * X ≤ 3 * r / 4 := by
      have : |r / X - 1| * X = |r - X| := by
        rw [show r / X - 1 = (r - X) / X by field_simp, abs_div, abs_of_pos hX]
        field_simp
      rw [this, abs_le]; constructor <;> linarith
    calc |t - t'| * |r / X - 1| * X = |t - t'| * (|r / X - 1| * X) := by ring
      _ ≤ |t - t'| * (3 * r / 4) := by gcongr
      _ = 3 * r / 4 * |t - t'| := by ring

/-! ### Arcs -/

theorem norm_smul_div_sub_le {x y : Vec d} {c : ℝ} (hc : 0 ≤ c) (hx : 0 < vecEuclideanNorm x)
    (hy : 0 < vecEuclideanNorm y) :
    vecEuclideanNorm ((c / vecEuclideanNorm x) • x - (c / vecEuclideanNorm y) • y) ≤
      2 * c * vecEuclideanNorm (x - y) / vecEuclideanNorm x := by
  set X := vecEuclideanNorm x
  set Y := vecEuclideanNorm y
  have e : (c / X) • x - (c / Y) • y = (c / X) • (x - y) + (c / X - c / Y) • y := by
    rw [smul_sub, sub_smul]; abel
  rw [e]
  refine (vecEuclideanNorm_add_le _ _).trans ?_
  rw [vecEuclideanNorm_smul, vecEuclideanNorm_smul, abs_of_nonneg (by positivity)]
  have h1 : |c / X - c / Y| * Y = c * |Y - X| / X := by
    rw [show c / X - c / Y = c * (Y - X) / (X * Y) by field_simp, abs_div, abs_mul,
      abs_of_nonneg hc, abs_of_pos (mul_pos hx hy)]
    field_simp
  have h2 : |Y - X| ≤ vecEuclideanNorm (x - y) := by
    rw [abs_sub_comm]; exact abs_sub_norm_le x y
  have h3 : c * |Y - X| / X ≤ c * vecEuclideanNorm (x - y) / X := by
    gcongr
  calc c / X * vecEuclideanNorm (x - y) + |c / X - c / Y| * Y
      ≤ c / X * vecEuclideanNorm (x - y) + c * vecEuclideanNorm (x - y) / X := by
        rw [h1]; linarith
    _ = 2 * c * vecEuclideanNorm (x - y) / X := by ring

/-- The normalized chord between two points of the sphere of radius `r` with nonnegative inner
product is a chain of `97` steps. -/
theorem arc_chain {r : ℝ} (hr : 0 < r) {a b : Vec d} (ha : vecEuclideanNorm a = r)
    (hb : vecEuclideanNorm b = r) (hab : 0 ≤ vecDot a b) :
    IsChain (annulusSet d r) (r / 16) 97 a b := by
  set g : ℝ → Vec d := fun t => (1 - t) • a + t • b with hg
  have hgsq : ∀ t : ℝ, vecNormSq (g t) =
      (1 - t) ^ 2 * r ^ 2 + 2 * ((1 - t) * t * vecDot a b) + t ^ 2 * r ^ 2 := by
    intro t
    simp only [hg, vecNormSq_add_expand, vecNormSq_smul, vecDot_smul_left', vecDot_smul_right']
    rw [← vecEuclideanNorm_sq a, ← vecEuclideanNorm_sq b, ha, hb]
    ring
  have hglow : ∀ t ∈ Set.Icc (0 : ℝ) 1, 7 * r / 10 ≤ vecEuclideanNorm (g t) := by
    intro t ht
    have h1 : (7 * r / 10) ^ 2 ≤ vecEuclideanNorm (g t) ^ 2 := by
      rw [vecEuclideanNorm_sq, hgsq]
      have : 0 ≤ (1 - t) * t * vecDot a b := mul_nonneg (mul_nonneg (by linarith [ht.2]) ht.1) hab
      nlinarith [sq_nonneg (t - 1 / 2), sq_nonneg r]
    exact abs_le_of_sq_le_sq' h1 (vecEuclideanNorm_nonneg _) |>.2
  have hgpos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < vecEuclideanNorm (g t) := fun t ht => by
    linarith [hglow t ht]
  set γ : ℝ → Vec d := fun t => (r / vecEuclideanNorm (g t)) • g t with hγ
  have h := IsChain.of_lipschitz (K := annulusSet d r) (s := r / 16) (L := 6 * r) (γ := γ)
    (n := 97) ?_ ?_ (by norm_num) (by linarith)
  · have g0 : g 0 = a := by simp [hg]
    have g1 : g 1 = b := by simp [hg]
    simpa only [hγ, g0, g1, ha, hb, div_self hr.ne', one_smul] using h
  · intro t ht
    apply annulusSet_of_norm_eq hr
    have := hgpos t ht
    simp only [hγ, vecEuclideanNorm_smul, abs_of_nonneg (by positivity : 0 ≤ r / vecEuclideanNorm (g t))]
    field_simp
  · intro t ht t' ht'
    have hd : g t - g t' = (t - t') • (b - a) := by
      simp only [hg, smul_sub, sub_smul, one_smul]; abel
    have h1 := norm_smul_div_sub_le hr.le (hgpos t ht) (hgpos t' ht')
    have h2 : vecEuclideanNorm (g t - g t') ≤ 2 * r * |t - t'| := by
      rw [hd, vecEuclideanNorm_smul]
      have := vecEuclideanNorm_sub_le' b a
      rw [ha, hb] at this
      calc |t - t'| * vecEuclideanNorm (b - a) ≤ |t - t'| * (r + r) := by gcongr
        _ = 2 * r * |t - t'| := by ring
    refine h1.trans ?_
    have hl := hglow t ht
    rw [div_le_iff₀ (hgpos t ht)]
    calc 2 * r * vecEuclideanNorm (g t - g t') ≤ 2 * r * (2 * r * |t - t'|) := by gcongr
      _ = (4 * r * |t - t'| * r) := by ring
      _ ≤ 6 * r * |t - t'| * vecEuclideanNorm (g t) := by
        have : 0 ≤ r * |t - t'| := by positivity
        nlinarith

end PDE.Ch4GreenHarnack
