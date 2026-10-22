module

public import EllipticRegularity.Ch4.GreenFunction.Pole
public import EllipticRegularity.Ch4.GreenFunction.Duality

/-!
# The approximation setting

`ApproxSetting d Λ R a` collects, for a fixed elliptic coefficient field `a` on `B_R`, the data
produced by the Dirichlet problem (Lemma 4.33): solvability of the adjoint problem
with an energy bound, and a sequence `Gₙ ∈ H¹₀(B_R)` of approximate Green functions solving
`-div (a ∇ Gₙ) = |B_{ρₙ}|⁻¹ 1_{B_{ρₙ}}`, `ρₙ = R/(n+2)`.  It is obtained from the interface
statement `GreenDirichletConcl d` by `ApproxSetting.ofDirichlet`; it is an internal bookkeeping
device, never an assumption of a public theorem.

The main result of this file: for `g ∈ L²(B_R)` vanishing in `B_ε`, `∫ Gₙ g` converges to the
pole value `lim_{ρ → 0} ⨍_{B_ρ} v_g`, which is bounded by `K_ε ‖g‖₂`.
-/

@[expose] public section

open scoped Topology ENNReal

namespace PDE.Ch4Green

open MeasureTheory PDE Filter

variable {d : ℕ}

/-- The radii `ρₙ = R/(n+2)`. -/
noncomputable def approxRadius (R : ℝ) (n : ℕ) : ℝ := R / ((n : ℝ) + 2)

theorem approxRadius_pos {R : ℝ} (hR : 0 < R) (n : ℕ) : 0 < approxRadius R n := by
  unfold approxRadius; positivity

theorem approxRadius_le {R : ℝ} (hR : 0 < R) (n : ℕ) : approxRadius R n ≤ R / 2 := by
  unfold approxRadius
  gcongr
  linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]

theorem approxRadius_lt {R : ℝ} (hR : 0 < R) (n : ℕ) : approxRadius R n < R :=
  (approxRadius_le hR n).trans_lt (half_lt_self hR)

theorem tendsto_approxRadius {R : ℝ} (hR : 0 < R) :
    Tendsto (approxRadius R) atTop (𝓝[>] 0) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => approxRadius_pos hR n⟩
  exact tendsto_const_nhds.div_atTop
    (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)

theorem eventually_approxRadius_le {R : ℝ} (hR : 0 < R) {s : ℝ} (hs : 0 < s) :
    ∀ᶠ n in atTop, approxRadius R n ≤ s :=
  ((tendsto_approxRadius hR).mono_right nhdsWithin_le_nhds).eventually (ge_mem_nhds hs)

/-- The data of the Dirichlet problem used to construct and study the Green function. -/
structure ApproxSetting (d : ℕ) (Λ R : ℝ) (a : CoeffField d) where
  hR : 0 < R
  hmeas : ∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d) R))
  hell : ∀ x ∈ euclideanBall (0 : Vec d) R, IsEllipticMatrix 1 Λ (a x)
  /-- energy constant `C₁² R²` -/
  E : ℝ
  hE : 0 ≤ E
  existsAdj : ∀ g : Vec d → ℝ, MemL2On (euclideanBall (0 : Vec d) R) g →
    ∃ v : H10Function (euclideanBall (0 : Vec d) R),
      IsWeakDivergenceFormH10SolutionOn (adjointCoeffField a) (euclideanBall (0 : Vec d) R)
        v.toH1Function g 0
  energyAdj : ∀ (g : Vec d → ℝ) (v : H10Function (euclideanBall (0 : Vec d) R)),
    MemL2On (euclideanBall (0 : Vec d) R) g →
    IsWeakDivergenceFormH10SolutionOn (adjointCoeffField a) (euclideanBall (0 : Vec d) R)
      v.toH1Function g 0 →
    eLpNorm v.toH1Function.toFun 2 (volumeOn (euclideanBall (0 : Vec d) R)) ≤
      ENNReal.ofReal E * eLpNorm g 2 (volumeOn (euclideanBall (0 : Vec d) R))
  /-- the approximate Green functions -/
  G : ℕ → H10Function (euclideanBall (0 : Vec d) R)
  solG : ∀ n, IsWeakDivergenceFormH10SolutionOn a (euclideanBall (0 : Vec d) R) (G n).toH1Function
    (approxSource d (approxRadius R n)) 0

namespace ApproxSetting

variable {Λ R : ℝ} {a : CoeffField d}

/-- The Dirichlet interface produces an approximation setting. -/
theorem nonempty_ofDirichlet (hDir : GreenDirichletConcl d) (hR : 0 < R)
    (hmeas : ∀ i j : Fin d, AEMeasurable (fun x => a x i j) (volumeOn (euclideanBall (0 : Vec d)
        R)))
    (hell : ∀ x ∈ euclideanBall (0 : Vec d) R, IsEllipticMatrix 1 Λ (a x)) :
    Nonempty (ApproxSetting d Λ R a) := by
  obtain ⟨C₁, -, hD⟩ := hDir
  have hD' := hD Λ R hR a hmeas hell
  have hF : MemVectorL2On (euclideanBall (0 : Vec d) R) (0 : Vec d → Vec d) := by
    intro i
    simp
  have hG : ∀ n : ℕ, ∃ v : H10Function (euclideanBall (0 : Vec d) R),
      IsWeakDivergenceFormH10SolutionOn a (euclideanBall (0 : Vec d) R) v.toH1Function
        (approxSource d (approxRadius R n)) 0 := fun n =>
    (hD' a (Or.inl rfl) _ 0 (memL2On_approxSource hR.le _) hF).1
  choose G hGsol using hG
  exact ⟨{
    hR := hR
    hmeas := hmeas
    hell := hell
    E := C₁ ^ 2 * R ^ 2
    hE := by positivity
    existsAdj := fun g hg => (hD' _ (Or.inr rfl) g 0 hg hF).1
    energyAdj := fun g v hg hv => ((hD' _ (Or.inr rfl) g 0 hg hF).2.2 rfl v hv).2
    G := G
    solG := hGsol }⟩

/-- **Convergence to the pole value.**  For `g ∈ L²(B_R)` vanishing a.e. in `B_ε`, the integrals
`∫ Gₙ g` converge to a limit `L`, bounded by `K_ε ‖g‖₂`, and the averages over `B_ρ` of every
`H¹₀` solution of the adjoint problem with source `g` converge to the same `L`. -/
theorem exists_tendsto (S : ApproxSetting d Λ R a) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧ ∀ {ε : ℝ}, 0 < ε → ε ≤ R → ∀ {g : Vec d → ℝ},
      MemL2On (euclideanBall (0 : Vec d) R) g →
      (∀ᵐ x ∂(volumeOn (euclideanBall (0 : Vec d) ε)), g x = 0) →
      ∃ L : ℝ, Tendsto (fun n => ∫ x in euclideanBall (0 : Vec d) R, (S.G n).toH1Function.toFun x *
          g x)
          atTop (𝓝 L) ∧
        |L| ≤ poleConst C Λ ε S.E d * (eLpNorm g 2 (volumeOn (euclideanBall (0 : Vec d) R))).toReal
            ∧
        ∀ v : H10Function (euclideanBall (0 : Vec d) R),
          IsWeakDivergenceFormH10SolutionOn (adjointCoeffField a) (euclideanBall (0 : Vec d) R)
            v.toH1Function g 0 →
          Tendsto (fun ρ => integralAverage (euclideanBall (0 : Vec d) ρ) v.toH1Function.toFun)
            (𝓝[>] 0) (𝓝 L) := by
  obtain ⟨C, hC, hpole⟩ := pole_average (d := d) hd
  refine ⟨C, hC, ?_⟩
  intro ε hε hεR g hg2 hg
  have hdual : ∀ (v : H10Function (euclideanBall (0 : Vec d) R)),
      IsWeakDivergenceFormH10SolutionOn (adjointCoeffField a) (euclideanBall (0 : Vec d) R)
        v.toH1Function g 0 → ∀ n,
      ∫ x in euclideanBall (0 : Vec d) R, (S.G n).toH1Function.toFun x * g x =
        integralAverage (euclideanBall (0 : Vec d) (approxRadius R n)) v.toH1Function.toFun :=
    fun v hv n => integral_mul_eq_integralAverage (approxRadius_pos S.hR n).le
      (approxRadius_lt S.hR n).le (S.solG n) hv
  obtain ⟨v₀, hv₀⟩ := S.existsAdj g hg2
  obtain ⟨⟨L, hL⟩, hbd⟩ := hpole hε hεR S.hmeas S.hell hg2 hg v₀ hv₀ S.hE
    (S.energyAdj g v₀ hg2 hv₀)
  have hseq : Tendsto (fun n => ∫ x in euclideanBall (0 : Vec d) R,
      (S.G n).toH1Function.toFun x * g x) atTop (𝓝 L) := by
    simp_rw [hdual v₀ hv₀]
    exact hL.comp (tendsto_approxRadius S.hR)
  refine ⟨L, hseq, ?_, ?_⟩
  · refine le_of_tendsto hseq.abs ?_
    filter_upwards [eventually_approxRadius_le S.hR (half_pos hε)] with n hn
    rw [hdual v₀ hv₀ n]
    exact hbd _ (approxRadius_pos S.hR n) hn
  · intro v hv
    obtain ⟨⟨L', hL'⟩, -⟩ := hpole hε hεR S.hmeas S.hell hg2 hg v hv S.hE
      (S.energyAdj g v hg2 hv)
    have hseq' : Tendsto (fun n => ∫ x in euclideanBall (0 : Vec d) R,
        (S.G n).toH1Function.toFun x * g x) atTop (𝓝 L') := by
      simp_rw [hdual v hv]
      exact hL'.comp (tendsto_approxRadius S.hR)
    rwa [tendsto_nhds_unique hseq hseq']

end ApproxSetting

end PDE.Ch4Green
