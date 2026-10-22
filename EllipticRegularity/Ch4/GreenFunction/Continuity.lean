module

public import EllipticRegularity.Ch4.GreenFunction.Harmonic
public import EllipticRegularity.DeGiorgi.Assembly.Gluing

/-!
# Continuous representative of the Green function (Step 6 of Proposition 4.40, end)

Each `y ∈ B_R \ {0}` has a ball `B_r(y) ⊆ B_R \ B̄_{|y|/2}`, where `G` is `H¹` and `a`-harmonic;
De Giorgi's theorem gives a continuous representative on `B_{r/2}(y)`, and these glue to a
representative continuous in `B_R \ {0}`.
-/

@[expose] public section

open scoped Topology ENNReal

namespace PDE.Ch4Green

open MeasureTheory PDE Filter

variable {d : ℕ}

/-- A.e. statements on `B_R \ {0}` hold a.e. on `B_R` (`d ≥ 1`). -/
theorem ae_ball_of_ae_punctured (hd : 0 < d) {R : ℝ} {P : Vec d → Prop}
    (h : ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) R \ {0})), P x) :
    ∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) R)), P x := by
  have hnull : volume ({0} : Set (Vec d)) = 0 := by
    have : NeZero d := ⟨hd.ne'⟩
    exact measure_singleton _
  have hcov : euclideanBall (0 : Vec d) R ⊆ (euclideanBall (0 : Vec d) R \ {0}) ∪ {0} := by
    intro x hx
    by_cases h0 : x = 0
    · exact Or.inr h0
    · exact Or.inl ⟨hx, h0⟩
  refine ae_restrict_of_ae_restrict_of_subset hcov ?_
  rw [ae_restrict_union_iff]
  exact ⟨h, by rw [Measure.restrict_eq_zero.2 hnull]; simp⟩

namespace ApproxSetting

variable {Λ R : ℝ} {a : CoeffField d}

/-- **Part (iii), second half**: a representative of `G` continuous in `B_R \ {0}`. -/
theorem exists_continuous_rep (S : ApproxSetting d Λ R a) (hd : 3 ≤ d) {G : Vec d → ℝ}
    (hG : IsGreenFunction a R G) :
    ∃ Gc : Vec d → ℝ, ContinuousOn Gc (euclideanBall (0 : Vec d) R \ {0}) ∧
      Gc =ᵐ[volumeOn (euclideanBall (0 : Vec d) R)] G := by
  obtain ⟨CD, -, hDG⟩ := exists_continuousOn_rep_ball (d := d) hd
  set B := euclideanBall (0 : Vec d) R
  have hBo : IsOpen B := isOpen_euclideanBall _ _
  have hO : IsOpen (B \ {0}) := hBo.sdiff isClosed_singleton
  have hlocal : ∀ y ∈ B \ {0}, ∃ V : Set (Vec d), IsOpen V ∧ y ∈ V ∧
      ∃ w : Vec d → ℝ, ContinuousOn w V ∧ w =ᵐ[volumeOn V] G := by
    rintro y ⟨hyB, hy0⟩
    have hypos : 0 < vecEuclideanNorm y := vecEuclideanNorm_pos_iff.mpr hy0
    have hyR : vecEuclideanNorm y < R := by
      have := (mem_euclideanBall_iff_vecEuclideanNorm_lt S.hR).1 hyB
      rwa [sub_zero] at this
    set ε := vecEuclideanNorm y / 2 with hεdef
    have hε : 0 < ε := by positivity
    have hεR : ε < R := by linarith
    set U := B \ euclideanClosedBall (0 : Vec d) ε
    have hUo : IsOpen U := hBo.sdiff (isClosed_euclideanClosedBall _ _)
    have hUB : U ⊆ B := Set.sdiff_subset
    obtain ⟨H, hHG, hHsol, -⟩ := S.exists_harmonic hd hG hε hεR
    set r := min ε (R - vecEuclideanNorm y)
    have hr : 0 < r := lt_min hε (by linarith)
    have hball : euclideanBall y r ⊆ U := by
      intro z hz
      have hzy := (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hz
      have h1 : vecEuclideanNorm z ≤ vecEuclideanNorm (z - y) + vecEuclideanNorm y := by
        have := vecEuclideanNorm_add_le (z - y) y
        rwa [sub_add_cancel] at this
      have h2 : vecEuclideanNorm y ≤ vecEuclideanNorm (y - z) + vecEuclideanNorm z := by
        have := vecEuclideanNorm_add_le (y - z) z
        rwa [sub_add_cancel] at this
      have h3 : vecEuclideanNorm (y - z) = vecEuclideanNorm (z - y) := by
        rw [← vecEuclideanNorm_neg, neg_sub]
      have hr1 : r ≤ ε := min_le_left _ _
      have hr2 : r ≤ R - vecEuclideanNorm y := min_le_right _ _
      refine ⟨?_, ?_⟩
      · rw [mem_euclideanBall_iff_vecEuclideanNorm_lt S.hR, sub_zero]; linarith
      · rw [mem_euclideanClosedBall_iff_vecEuclideanNorm_le hε.le, sub_zero]
        intro hle
        linarith [hεdef]
    obtain ⟨w, hwc, hwae, -⟩ := hDG S.one_le_Lam hUo
      (fun i j => (S.hmeas i j).mono_measure (Measure.restrict_mono hUB le_rfl))
      (fun x hx => S.hell x (hUB hx)) hHsol y hr hball
    refine ⟨euclideanBall y (r / 2), isOpen_euclideanBall _ _,
      center_mem_euclideanBall _ (half_pos hr), w, hwc, ?_⟩
    rw [hHG] at hwae
    exact hwae
  obtain ⟨Gc, hGc, hGcae⟩ := DGNMAssembly.glue_continuous_rep hO hlocal
  exact ⟨Gc, hGc, ae_ball_of_ae_punctured (by omega) hGcae⟩

end ApproxSetting

end PDE.Ch4Green
