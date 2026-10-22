module

public import EllipticRegularity.Parabolic.CauchyDef
public import EllipticRegularity.Parabolic.NashKernel.AssemblyKernel
public import EllipticRegularity.Parabolic.NashKernel.PointwiseBounds

/-!
# Proof of `PDE.nashAronsonKernel`

`PDE.Ch5NashNashKernelProof.result` assembles the Nash--Aronson kernel: the bounded dyadic
kernel `P` representing the Cauchy solution operator on `L¹ ∩ L²`
(`exists_cauchyOp_kernel`) satisfies the two-sided Gaussian bounds almost everywhere
(`kernel_gaussian_bounds_of_representation`).
-/

@[expose] public section

namespace PDE.Ch5NashNashKernelProof

open MeasureTheory Set PDE.Parabolic.NashKernel PDE.NashKernelExtend

theorem result (d : ℕ) (hd : 0 < d) :
    ∃ C : ℝ, 0 < C ∧ ∀ Lam : ℝ, 1 ≤ Lam → ∃ c β : ℝ, 0 < c ∧ 0 < β ∧
      ∀ (a : ParCoeffField d) (s t : ℝ), s < t → IsParabolicCoeff 1 Lam a univ (Icc s t) →
      ∃ P : Vec d → Vec d → ℝ, Measurable (Function.uncurry P) ∧
        (∀ f : Vec d → ℝ, Integrable f volume → MemLp f 2 volume →
          ∀ u : ParH1Function (univ : Set (Vec d)) (Icc s t), IsCauchySolution a s t f u →
            ∀ᵐ x : Vec d, Integrable (fun y => P x y * f y) volume ∧
              u.toFun (x, t) = ∫ y, P x y * f y) ∧
        ∀ᵐ p ∂((volume : Measure (Vec d)).prod volume),
          c * (t - s) ^ (-(d : ℝ) / 2) * Real.exp (-β * euclideanSqDist p.1 p.2 / (t - s)) ≤ P p.1 p.2 ∧
          P p.1 p.2 ≤ C * (t - s) ^ (-(d : ℝ) / 2) *
            Real.exp (-euclideanSqDist p.1 p.2 / (8 * Lam * (t - s))) := by
  obtain ⟨C₁, -, hker⟩ := exists_cauchyOp_kernel hd
  obtain ⟨C₂, hC₂, hgb⟩ := kernel_gaussian_bounds_of_representation d hd
  refine ⟨C₂ * Real.exp ((d : ℝ) + 2), by positivity, fun Lam hLam => ?_⟩
  obtain ⟨c, β, hc, hβ, hb⟩ := hgb Lam hLam
  refine ⟨c, β, hc, hβ, fun a s t hst ha => ?_⟩
  obtain ⟨P, hPm, hPb, hrep⟩ := hker Lam hLam a s t hst ha
  refine ⟨P, hPm, fun f hf1 hf2 u hu => ?_, ?_⟩
  · filter_upwards [cauchyOp_ae_eq hst ha hf2 u hu, hrep f ⟨hf1, hf2⟩] with x h1 h2
    exact ⟨integrable_kernel_mul hPm hPb x hf1, h1.trans h2⟩
  · refine hb a s t hst ha _ P hPm hPb fun B hB hBb => ?_
    have hfin : volume B < ⊤ := hBb.measure_lt_top
    filter_upwards [hrep (B.indicator 1) (dom_indicator_one hB hfin)] with x hx
    rw [hx]
    exact kerOp_indicator_one hB x

end PDE.Ch5NashNashKernelProof
