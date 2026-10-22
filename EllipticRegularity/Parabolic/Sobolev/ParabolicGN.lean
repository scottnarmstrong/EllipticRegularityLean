/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi, Amélie Loher. All rights reserved.
-/
module

public import PDEFoundation.Measure.LpPower
public import PDEFoundation.Sobolev.H1.ZeroBoundary
public import PDEFoundation.Sobolev.Inequalities.SobolevWholeSpace
public import EllipticRegularity.Parabolic.ParabolicDef

/-!
# Parabolic Gagliardo--Nirenberg inequality

Space-time interpolation from the whole-space Sobolev inequality and the
parabolic energy-space slice interface.
-/

@[expose] public section

open scoped ENNReal

namespace PDE.Parabolic

open MeasureTheory Set

/-- In dimensions at least three, the spatial Gagliardo--Nirenberg exponent
lies strictly between `2` and the critical Sobolev exponent.  This is the
whole-space `L^q`-norm form; its constant depends only on the dimension. -/
theorem exists_spatial_gagliardo_nirenberg_constant_ge_three
    (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ u : H1Function (Set.univ : Set (Vec d)),
        eLpNorm u.toFun (ENNReal.ofReal (2 * ((d : ℝ) + 2) / d)) volume ≤
          ENNReal.rpow (eLpNorm u.toFun 2 volume)
              (2 / ((d : ℝ) + 2)) *
            ENNReal.rpow (ENNReal.ofReal C *
              eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2 volume)
                ((d : ℝ) / ((d : ℝ) + 2)) := by
  obtain ⟨C₀, hC₀, hsob⟩ :=
    PDE.sobolev_inequality_wholeSpace_and_zeroBoundary d (by omega)
  have hdtwo : (2 : ℝ) < d := by exact_mod_cast (by omega : 2 < d)
  let qstar : ℝ := sobolevConjugate d 2
  let q : ℝ := 2 * ((d : ℝ) + 2) / d
  let θ : ℝ := 2 / ((d : ℝ) + 2)
  let β : ℝ := (d : ℝ) / ((d : ℝ) + 2)
  let κ : ℝ := C₀ * (2 * ((d : ℝ) - 1) / ((d : ℝ) - 2))
  have hqstar : qstar = 2 * d / ((d : ℝ) - 2) := by
    dsimp [qstar, sobolevConjugate]
    ring
  have hqpos : 0 < q := by
    dsimp [q]
    positivity
  have hθpos : 0 < θ := by
    dsimp [θ]
    positivity
  have hβpos : 0 < β := by
    dsimp [β]
    positivity
  have hκpos : 0 < κ := by
    dsimp [κ]
    have hdminus : (0 : ℝ) < (d : ℝ) - 2 := by linarith
    have hdminus1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
    positivity
  refine ⟨κ, hκpos, fun u => ?_⟩
  let huW1p :
      W1pFunction (Set.univ : Set (Vec d)) (ENNReal.ofReal (2 : ℝ)) := {
    toFun := u.toFun
    grad := u.grad
    memLp := by
      simpa only [MemL2On, MemLpOn, volumeOn, ENNReal.ofReal_ofNat] using u.memL2
    gradMemLp := by
      intro i
      simpa only [GradMemL2On, GradMemLpOn, volumeOn,
        ENNReal.ofReal_ofNat] using u.gradMemL2 i
    hasWeakGradient := u.hasWeakGradient
  }
  have hSob₀ := (hsob 2 (by norm_num) (by exact_mod_cast hdtwo)).1 huW1p
  have hSob :
      eLpNorm u.toFun (ENNReal.ofReal (sobolevConjugate d 2)) volume ≤
        ENNReal.ofReal (C₀ * (2 * ((d : ℝ) - 1) / ((d : ℝ) - 2))) *
          eLpNorm (fun x => vecEuclideanNorm (u.grad x))
            (ENNReal.ofReal (2 : ℝ)) volume := by
    dsimp [huW1p] at hSob₀
    exact hSob₀
  have hSob' :
      eLpNorm u.toFun (ENNReal.ofReal qstar) volume ≤
        ENNReal.ofReal κ *
          eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2 volume := by
    simpa only [qstar, κ, ENNReal.ofReal_ofNat] using hSob
  have hqstarpos : 0 < qstar := by
    rw [hqstar]
    positivity
  have hrealTriple :
      Real.HolderTriple (2 / θ) (qstar / β) q := by
    refine ⟨?_, div_pos (by positivity) hθpos,
      div_pos hqstarpos hβpos⟩
    dsimp [q, θ, β]
    rw [hqstar]
    field_simp
    ring
  let f : Vec d → ℝ := fun x => |u.toFun x| ^ θ
  let g : Vec d → ℝ := fun x => |u.toFun x| ^ β
  have huMem : MemLp u.toFun 2 volume := by
    simpa only [MemL2On, MemLpOn, volumeOn, Measure.restrict_univ] using u.memL2
  have hf : AEStronglyMeasurable f volume := by
    dsimp [f]
    exact (Real.continuous_rpow_const hθpos.le).comp continuous_abs
      |>.comp_aestronglyMeasurable huMem.aestronglyMeasurable
  have hg : AEStronglyMeasurable g volume := by
    dsimp [g]
    exact (Real.continuous_rpow_const hβpos.le).comp continuous_abs
      |>.comp_aestronglyMeasurable huMem.aestronglyMeasurable
  have hmul :
      eLpNorm (fun x => f x * g x) (ENNReal.ofReal q) volume ≤
        eLpNorm f (ENNReal.ofReal (2 / θ)) volume *
          eLpNorm g (ENNReal.ofReal (qstar / β)) volume := by
    have hmul₀ := eLpNorm_le_eLpNorm_mul_eLpNorm_of_norm
      (· * ·) 1 continuous_mul hf hg
      (by filter_upwards with x; simp [Real.norm_eq_abs])
      (hpqr := hrealTriple.ennrealOfReal)
    simpa using hmul₀
  have hpowf :
    eLpNorm f (ENNReal.ofReal (2 / θ)) volume =
        ENNReal.rpow (eLpNorm u.toFun 2 volume) θ := by
    change eLpNorm (fun x => |u.toFun x| ^ θ) _ _ = _
    rw [show (fun x => |u.toFun x| ^ θ) =
      fun x => ‖u.toFun x‖ ^ θ by funext x; rw [Real.norm_eq_abs]]
    rw [eLpNorm_norm_rpow u.toFun huMem.aestronglyMeasurable hθpos]
    congr 2
    rw [← ENNReal.ofReal_mul (by positivity)]
    dsimp [θ]
    field_simp
    norm_num [ENNReal.ofReal_ofNat]
  have hpowg :
    eLpNorm g (ENNReal.ofReal (qstar / β)) volume =
        ENNReal.rpow (eLpNorm u.toFun (ENNReal.ofReal qstar) volume)
          β := by
    change eLpNorm (fun x => |u.toFun x| ^ β) _ _ = _
    rw [show (fun x => |u.toFun x| ^ β) =
      fun x => ‖u.toFun x‖ ^ β by funext x; rw [Real.norm_eq_abs]]
    rw [eLpNorm_norm_rpow u.toFun huMem.aestronglyMeasurable hβpos]
    congr 2
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    dsimp [β]
    field_simp
  have hmulFun :
      (fun x => f x * g x) = fun x => |u.toFun x| := by
    funext x
    dsimp [f, g]
    by_cases hx : u.toFun x = 0
    · simp [hx, hθpos.ne', hβpos.ne']
    · rw [← Real.rpow_add (abs_pos.mpr hx) θ β]
      rw [show θ + β = 1 by dsimp [θ, β]; field_simp; ring]
      exact Real.rpow_one _
  have hinterp :
      eLpNorm u.toFun (ENNReal.ofReal q) volume ≤
        ENNReal.rpow (eLpNorm u.toFun 2 volume) θ *
          ENNReal.rpow (eLpNorm u.toFun (ENNReal.ofReal qstar) volume)
            β := by
    rw [hmulFun] at hmul
    have habs : (fun x => |u.toFun x|) = fun x => ‖u.toFun x‖ := by
      funext x
      exact (Real.norm_eq_abs _).symm
    rw [habs] at hmul
    simpa only [eLpNorm_norm u.toFun huMem.aestronglyMeasurable,
      hpowf, hpowg] using hmul
  have hpowSob :
      ENNReal.rpow (eLpNorm u.toFun (ENNReal.ofReal qstar) volume)
          β ≤
        ENNReal.rpow (ENNReal.ofReal κ *
          eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2 volume)
            β := by
    exact ENNReal.rpow_le_rpow hSob' hβpos.le
  calc
    eLpNorm u.toFun (ENNReal.ofReal q) volume ≤
        ENNReal.rpow (eLpNorm u.toFun 2 volume) θ *
          ENNReal.rpow (eLpNorm u.toFun (ENNReal.ofReal qstar) volume)
            β := hinterp
    _ ≤ ENNReal.rpow (eLpNorm u.toFun 2 volume) θ *
          ENNReal.rpow (ENNReal.ofReal κ *
            eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2 volume)
              β := by
      exact mul_le_mul_of_nonneg_left hpowSob (by positivity)

/-- The integral-energy form of the spatial estimate in dimensions at least
three.  `C` depends only on `d`; after raising the norm inequality to the
parabolic exponent, its square is the coefficient of the gradient energy. -/
theorem exists_spatial_gagliardo_nirenberg_energy_constant_ge_three
    (d : ℕ) (hd : 3 ≤ d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ u : H1Function (Set.univ : Set (Vec d)),
        (eLpNorm u.toFun (ENNReal.ofReal (2 * ((d : ℝ) + 2) / d)) volume) ^
              (2 * ((d : ℝ) + 2) / d) ≤
          (ENNReal.ofReal C) ^ (2 : ℝ) *
            (eLpNorm u.toFun 2 volume) ^ (4 / (d : ℝ)) *
              (eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2 volume) ^ (2 : ℝ) := by
  obtain ⟨C, hC, hGN⟩ := exists_spatial_gagliardo_nirenberg_constant_ge_three d hd
  refine ⟨C, hC, fun u => ?_⟩
  let q : ℝ := 2 * ((d : ℝ) + 2) / d
  let θ : ℝ := 2 / ((d : ℝ) + 2)
  let β : ℝ := (d : ℝ) / ((d : ℝ) + 2)
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hθq : θ * q = 4 / (d : ℝ) := by
    dsimp [θ, q]
    field_simp
    norm_num
  have hβq : β * q = 2 := by
    dsimp [β, q]
    field_simp
  have h := hGN u
  dsimp [θ, β] at h
  have hpow := ENNReal.rpow_le_rpow h (le_of_lt hqpos)
  have hθq' : (2 / ((d : ℝ) + 2)) * q = 4 / (d : ℝ) := by
    simpa only [θ] using hθq
  have hβq' : ((d : ℝ) / ((d : ℝ) + 2)) * q = 2 := by
    simpa only [β] using hβq
  rw [ENNReal.mul_rpow_of_nonneg _ _ (le_of_lt hqpos),
    ← ENNReal.rpow_mul (eLpNorm u.toFun 2 volume)
      (2 / ((d : ℝ) + 2)) q,
    ← ENNReal.rpow_mul
      (ENNReal.ofReal C * eLpNorm (fun x => vecEuclideanNorm (u.grad x)) 2 volume)
      ((d : ℝ) / ((d : ℝ) + 2)) q,
    hθq', hβq',
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : 0 ≤ (2 : ℝ))] at hpow
  simpa only [q, ENNReal.ofReal_ofNat, ENNReal.rpow_natCast,
    mul_assoc, mul_left_comm, mul_comm] using hpow

/-- A measure-theoretic time integration lemma for slice-wise parabolic
Gagliardo--Nirenberg estimates.  If `A(t) ≤ C B(t)^(2/d) D(t)` almost
everywhere and the spatial `L²` energy `B` is essentially bounded by `S`,
then the integrated estimate follows with `S^(2/d)`.  Taking `A` and `D` to
be the respective powers of spatial `Lᵖ` norms gives the usual product-space
energy inequality by Tonelli. -/
theorem lintegral_le_of_ae_gagliardo_nirenberg
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (d : ℕ) (hd : 1 ≤ d)
    (C S : ℝ≥0∞) {A B D : α → ℝ≥0∞}
    (hD : Measurable D)
    (hB : ∀ᵐ t ∂μ, B t ≤ S)
    (hGN : ∀ᵐ t ∂μ,
      A t ≤ C * B t ^ (2 / (d : ℝ)) * D t) :
    ∫⁻ t, A t ∂μ ≤
      C * S ^ (2 / (d : ℝ)) * ∫⁻ t, D t ∂μ := by
  have hδ : 0 ≤ 2 / (d : ℝ) := by
    have hd' : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
    positivity
  have hpoint : ∀ᵐ t ∂μ,
      A t ≤ (C * S ^ (2 / (d : ℝ))) * D t := by
    filter_upwards [hB, hGN] with t hBt hGNt
    calc
      A t ≤ C * B t ^ (2 / (d : ℝ)) * D t := hGNt
      _ ≤ (C * S ^ (2 / (d : ℝ))) * D t := by
        gcongr
  calc
    ∫⁻ t, A t ∂μ ≤ ∫⁻ t, (C * S ^ (2 / (d : ℝ))) * D t ∂μ :=
      lintegral_mono_ae hpoint
    _ = C * S ^ (2 / (d : ℝ)) * ∫⁻ t, D t ∂μ :=
      lintegral_const_mul _ hD

/-- Time-integrated parabolic Gagliardo--Nirenberg inequality for measurable
families of whole-space `H¹` slices in dimensions at least three.  The bound
`S` is an essential upper bound for the spatial `L²` energy. -/
theorem exists_time_integrated_gagliardo_nirenberg_constant_ge_three
    (d : ℕ) (hd : 3 ≤ d) {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (u : α → H1Function (Set.univ : Set (Vec d)))
    (S : ℝ≥0∞)
    (hS : ∀ᵐ t ∂μ, (eLpNorm (u t).toFun 2 volume) ^ (2 : ℝ) ≤ S)
    (hD : Measurable fun t =>
      (eLpNorm (fun x => vecEuclideanNorm ((u t).grad x)) 2 volume) ^ (2 : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧
      ∫⁻ t,
          (eLpNorm (u t).toFun
              (ENNReal.ofReal (2 * ((d : ℝ) + 2) / d)) volume) ^
                (2 * ((d : ℝ) + 2) / d) ∂μ ≤
        C * S ^ (2 / (d : ℝ)) *
          ∫⁻ t,
            (eLpNorm (fun x => vecEuclideanNorm ((u t).grad x)) 2 volume) ^
                (2 : ℝ) ∂μ := by
  obtain ⟨C, hC, hspace⟩ :=
    exists_spatial_gagliardo_nirenberg_energy_constant_ge_three d hd
  let A : α → ℝ≥0∞ := fun t =>
    (eLpNorm (u t).toFun
      (ENNReal.ofReal (2 * ((d : ℝ) + 2) / d)) volume) ^
        (2 * ((d : ℝ) + 2) / d)
  let B : α → ℝ≥0∞ := fun t =>
    (eLpNorm (u t).toFun 2 volume) ^ (2 : ℝ)
  let D : α → ℝ≥0∞ := fun t =>
    (eLpNorm (fun x => vecEuclideanNorm ((u t).grad x)) 2 volume) ^ (2 : ℝ)
  have hGN : ∀ᵐ t ∂μ,
      A t ≤ (ENNReal.ofReal C) ^ (2 : ℝ) * B t ^ (2 / (d : ℝ)) * D t :=
    Filter.Eventually.of_forall fun t => by
      have hBpow (t : α) :
          (eLpNorm (u t).toFun 2 volume) ^ (4 / (d : ℝ)) =
            B t ^ (2 / (d : ℝ)) := by
        dsimp [B]
        rw [show (4 / (d : ℝ)) = (2 : ℝ) * (2 / (d : ℝ)) by
          have hdne : (d : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt (by omega : 0 < d))
          field_simp; ring]
        rw [ENNReal.rpow_mul]
      rw [← hBpow t]
      simpa only [A, B, D, ENNReal.rpow_natCast] using hspace (u t)
  have hCpow : (ENNReal.ofReal C) ^ (2 : ℝ) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  refine ⟨(ENNReal.ofReal C) ^ (2 : ℝ), hCpow, ?_⟩
  simpa only [A, B, D] using
    lintegral_le_of_ae_gagliardo_nirenberg μ d (by omega)
      ((ENNReal.ofReal C) ^ (2 : ℝ)) S hD hS hGN

end PDE.Parabolic
