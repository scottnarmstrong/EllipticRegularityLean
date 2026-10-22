module

public import PDEFoundation.Measure.QuadraticBallMaximalStrong

@[expose] public section

namespace PDE
open MeasureTheory
open scoped ENNReal

/-- The literal quadratic maximal function is measurable. -/
theorem measurable_quadraticBallMaximal {d : ℕ} (F : Vec d → Vec d) :
    Measurable (quadraticBallMaximal F) :=
  (measurable_uncenteredBallMaximal (fun x => vecNormSq (F x))).pow_const (1 / 2 : ℝ)

/-- The quadratic maximal function is finite almost everywhere for actual Lp
forcing above exponent two. -/
theorem ae_quadraticBallMaximal_ne_top {d : ℕ} (F : Vec d → Vec d)
    {p : ℝ} (hp : 2 < p)
    (hF : MemLp (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p) volume) :
    ∀ᵐ x ∂volume, quadraticBallMaximal F x ≠ ∞ := by
  have hp0 : 0 < p := by linarith
  have hnorm : eLpNorm (quadraticBallMaximal F) (ENNReal.ofReal p) volume < ∞ :=
    (eLpNorm_quadraticBallMaximal_le F hp hF).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hF.eLpNorm_lt_top)
  have hmoment := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (by positivity : ENNReal.ofReal p ≠ 0) ENNReal.ofReal_ne_top hnorm
  simp only [enorm_eq_self, ENNReal.toReal_ofReal hp0.le] at hmoment
  have hfinite := ae_lt_top ((measurable_quadraticBallMaximal F).pow_const p) hmoment.ne
  filter_upwards [hfinite] with x hx
  exact ((ENNReal.rpow_lt_top_iff_of_pos hp0).mp hx).ne

/-- The real quadratic maximal representative has the same Lp norm as the
extended maximal function; the round trip is guarded almost everywhere. -/
theorem eLpNorm_quadraticBallMaximal_toReal {d : ℕ} (F : Vec d → Vec d)
    {p : ℝ} (hp : 2 < p)
    (hF : MemLp (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p) volume) :
    eLpNorm (fun x => (quadraticBallMaximal F x).toReal) (ENNReal.ofReal p) volume =
      eLpNorm (quadraticBallMaximal F) (ENNReal.ofReal p) volume := by
  have hround : (fun x => ENNReal.ofReal (quadraticBallMaximal F x).toReal)
      =ᵐ[volume] quadraticBallMaximal F := by
    filter_upwards [ae_quadraticBallMaximal_ne_top F hp hF] with x hx
    exact ENNReal.ofReal_toReal hx
  rw [← eLpNorm_congr_ae hround]
  exact (eLpNorm_ofReal _ (ae_of_all volume fun x => ENNReal.toReal_nonneg)).symm

/-- Actual higher-integrable forcing gives a genuine real Lp maximal source. -/
theorem memLp_quadraticBallMaximal_toReal {d : ℕ} (F : Vec d → Vec d)
    {p : ℝ} (hp : 2 < p)
    (hF : MemLp (fun x => vecEuclideanNorm (F x)) (ENNReal.ofReal p) volume) :
    MemLp (fun x => (quadraticBallMaximal F x).toReal) (ENNReal.ofReal p) volume := by
  show eLpNorm (fun x => (quadraticBallMaximal F x).toReal) (ENNReal.ofReal p) volume < ∞
  rw [eLpNorm_quadraticBallMaximal_toReal F hp hF]
  exact (eLpNorm_quadraticBallMaximal_le F hp hF).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hF.eLpNorm_lt_top)

end PDE
