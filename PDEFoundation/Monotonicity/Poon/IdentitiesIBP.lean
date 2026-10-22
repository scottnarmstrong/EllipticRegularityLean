module

public import PDEFoundation.Monotonicity.Poon.IdentitiesAlgebra

/-!
# Gaussian integration by parts identities

`Lam s f = ∫ f Φ(s, ·)`.  For a vector field `F` with tame components,
`Lam (Σᵢ ∂ᵢ Fᵢ) = (1 / (2 s)) Lam (Σᵢ xᵢ Fᵢ)`.  Five instances (fields `x_i v²`, `v v_i`, `v_i Δv`,
`x_i |∇v|²`, `v_i (x · ∇v)`) are the integrated identities behind Poon's computation.
-/

@[expose] public section

open MeasureTheory

namespace PDE

noncomputable section

variable {d : ℕ}

/-- Integral against the heat kernel. -/
def Lam (d : ℕ) (s : ℝ) (f : Vec d → ℝ) : ℝ := ∫ x : Vec d, f x * heatKernel d s x

/-- Sum of `x_i * (x_i * a)` is `|x|² a`. -/
theorem sum_coord_mul_coord_mul (x : Vec d) (a : ℝ) : ∑ i, x i * (x i * a) = vecNormSq x * a := by
  rw [vecNormSq_eq_sum_sq, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem sum_coord_mul_mul (x : Vec d) (a : Fin d → ℝ) (c : ℝ) :
    ∑ i, x i * (c * a i) = c * ∑ i, x i * a i := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem sum_coord_mul_mul' (x : Vec d) (a : Fin d → ℝ) (c : ℝ) :
    ∑ i, x i * (a i * c) = (∑ i, x i * a i) * c := by
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => by ring

section Linear

variable {s A' : ℝ} (hs : 0 < s) (hw : WeightInt d s A')
include hs hw

theorem Lam_add {f g : Vec d → ℝ} (hf : PDom (A' + A') f) (hg : PDom (A' + A') g) :
    Lam d s (fun x => f x + g x) = Lam d s f + Lam d s g := by
  unfold Lam
  simp only [add_mul]
  exact integral_add (hf.integrable_mul_heatKernel hs hw) (hg.integrable_mul_heatKernel hs hw)

omit hs hw in
theorem Lam_const_mul {f : Vec d → ℝ} (c : ℝ) :
    Lam d s (fun x => c * f x) = c * Lam d s f := by
  unfold Lam
  simp only [mul_assoc]
  exact integral_const_mul c _

theorem Lam_sub {f g : Vec d → ℝ} (hf : PDom (A' + A') f) (hg : PDom (A' + A') g) :
    Lam d s (fun x => f x - g x) = Lam d s f - Lam d s g := by
  unfold Lam
  simp only [sub_mul]
  exact integral_sub (hf.integrable_mul_heatKernel hs hw) (hg.integrable_mul_heatKernel hs hw)

theorem Lam_sum {f : Fin d → Vec d → ℝ} (hf : ∀ i, PDom (A' + A') (f i)) :
    Lam d s (fun x => ∑ i, f i x) = ∑ i, Lam d s (f i) := by
  unfold Lam
  simp only [Finset.sum_mul]
  exact integral_finsetSum _ fun i _ => (hf i).integrable_mul_heatKernel hs hw

/-- Gaussian integration by parts for a vector field. -/
theorem gauss_div {F : Fin d → Vec d → ℝ} (hF : ∀ i, Sm (F i))
    (h0 : ∀ i, PDom (A' + A') (F i))
    (h1 : ∀ i, PDom (A' + A') (euclideanCoordDeriv i (F i)))
    (h2 : ∀ i, PDom (A' + A') (fun x => x i * F i x)) :
    Lam d s (fun x => ∑ i, euclideanCoordDeriv i (F i) x) =
      (1 / (2 * s)) * Lam d s (fun x => ∑ i, x i * F i x) := by
  rw [Lam_sum hs hw h1, Lam_sum hs hw h2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact gauss_ibp hs hw (hF i) i (h0 i) (h1 i) (h2 i)

end Linear

/-- Data making all the integrals in Poon's computation converge. -/
structure PoonSetup (v : Vec d → ℝ) (s A' : ℝ) : Prop where
  pos : 0 < s
  smooth : Sm v
  weight : WeightInt d s A'
  dom_v : PDom A' v
  dom_dv : ∀ i, PDom A' (euclideanCoordDeriv i v)
  dom_S : ∀ i j, PDom A' (euclideanCoordSecondDeriv i j v)
  dom_L : PDom A' (euclideanCoordLaplacian v)
  dom_L1 : ∀ i, PDom A' (euclideanCoordDeriv i (euclideanCoordLaplacian v))

namespace PoonSetup

variable {v : Vec d → ℝ} {s A' : ℝ} (hP : PoonSetup v s A')
include hP

theorem dom_Q2 : PDom (A' + A') (pQ2 v) :=
  PDom.sum _ _ fun i _ => (hP.dom_dv i).mul (hP.dom_dv i)

theorem dom_P : PDom A' (pP v) :=
  PDom.sum _ _ fun i _ => (PDom.coord i).mul_poly' (hP.dom_dv i)

theorem dom_R : PDom (A' + A') (pR v) :=
  PDom.sum _ _ fun i _ => PDom.sum _ _ fun j _ =>
    (PDom.coord j).mul_poly' ((hP.dom_dv i).mul (hP.dom_S j i))

theorem dom_V3 : PDom (A' + A') (pV3 v) :=
  PDom.sum _ _ fun i _ => (hP.dom_dv i).mul (hP.dom_L1 i)

theorem dom_vv : PDom (A' + A') (fun x => v x * v x) := hP.dom_v.mul hP.dom_v

theorem dom_vP : PDom (A' + A') (fun x => v x * pP v x) := hP.dom_v.mul hP.dom_P

theorem dom_qvv : PDom (A' + A') (fun x => vecNormSq x * (v x * v x)) :=
  PDom.normSq.mul_poly' hP.dom_vv

theorem dom_vL : PDom (A' + A') (fun x => v x * euclideanCoordLaplacian v x) :=
  hP.dom_v.mul hP.dom_L

theorem dom_LL : PDom (A' + A') (fun x => euclideanCoordLaplacian v x * euclideanCoordLaplacian v x) :=
  hP.dom_L.mul hP.dom_L

theorem dom_PL : PDom (A' + A') (fun x => pP v x * euclideanCoordLaplacian v x) :=
  hP.dom_P.mul hP.dom_L

theorem dom_LP : PDom (A' + A') (fun x => euclideanCoordLaplacian v x * pP v x) :=
  hP.dom_L.mul hP.dom_P

theorem dom_PP : PDom (A' + A') (fun x => pP v x * pP v x) := hP.dom_P.mul hP.dom_P

theorem dom_qQ2 : PDom (A' + A') (fun x => vecNormSq x * pQ2 v x) :=
  PDom.normSq.mul_poly' hP.dom_Q2

/-- First identity: `∫ (d v² + 2 v (x·∇v)) Φ = (1/(2s)) ∫ |x|² v² Φ`. -/
theorem lam_div1 :
    Lam d s (fun x => (d : ℝ) * (v x * v x) + 2 * v x * pP v x) =
      (1 / (2 * s)) * Lam d s (fun x => vecNormSq x * (v x * v x)) := by
  have hs := hP.pos
  have hw := hP.weight
  have hv := hP.smooth
  have := gauss_div hs hw (F := fun i x => x i * (v x * v x)) (fun i => (sm_coord i).mul (hv.mul hv))
    (fun i => (PDom.coord i).mul_poly' hP.dom_vv)
    (fun i => by
      refine PDom.congr (fun x => (deriv1 hv i x).symm) ?_
      exact (hP.dom_vv).add (((hP.dom_v.const_mul 2).mul ((PDom.coord i).mul_poly' (hP.dom_dv i)))))
    (fun i => by
      refine PDom.congr (fun x => rfl) ?_
      exact ((PDom.coord i).mul_poly' ((PDom.coord i).mul_poly' hP.dom_vv)))
  simp only [div1 hv, sum_coord_mul_coord_mul] at this
  exact this

/-- Second identity: `∫ (|∇v|² + v Δv) Φ = (1/(2s)) ∫ v (x·∇v) Φ`. -/
theorem lam_div2 :
    Lam d s (fun x => pQ2 v x + v x * euclideanCoordLaplacian v x) =
      (1 / (2 * s)) * Lam d s (fun x => v x * pP v x) := by
  have hs := hP.pos
  have hw := hP.weight
  have hv := hP.smooth
  have := gauss_div hs hw (F := fun i x => v x * euclideanCoordDeriv i v x)
    (fun i => hv.mul (hv.coordDeriv i))
    (fun i => hP.dom_v.mul (hP.dom_dv i))
    (fun i => by
      refine PDom.congr (fun x => (deriv2 hv i x).symm) ?_
      exact ((hP.dom_dv i).mul (hP.dom_dv i)).add (hP.dom_v.mul (hP.dom_S i i)))
    (fun i => (PDom.coord i).mul_poly' (hP.dom_v.mul (hP.dom_dv i)))
  simp only [div2 hv, sum_coord_mul_mul] at this
  exact this

/-- Third identity: `∫ (Δv² + ∇v·∇Δv) Φ = (1/(2s)) ∫ (x·∇v) Δv Φ`. -/
theorem lam_div3 :
    Lam d s (fun x => euclideanCoordLaplacian v x * euclideanCoordLaplacian v x + pV3 v x) =
      (1 / (2 * s)) * Lam d s (fun x => pP v x * euclideanCoordLaplacian v x) := by
  have hs := hP.pos
  have hw := hP.weight
  have hv := hP.smooth
  have := gauss_div hs hw
    (F := fun i x => euclideanCoordDeriv i v x * euclideanCoordLaplacian v x)
    (fun i => (hv.coordDeriv i).mul (sm_L hv))
    (fun i => (hP.dom_dv i).mul hP.dom_L)
    (fun i => by
      refine PDom.congr (fun x => (deriv3 hv i x).symm) ?_
      exact ((hP.dom_S i i).mul hP.dom_L).add ((hP.dom_dv i).mul (hP.dom_L1 i)))
    (fun i => (PDom.coord i).mul_poly' ((hP.dom_dv i).mul hP.dom_L))
  simp only [div3 hv, sum_coord_mul_mul'] at this
  exact this

/-- Fourth identity: `∫ (d |∇v|² + 2 R) Φ = (1/(2s)) ∫ |x|² |∇v|² Φ`. -/
theorem lam_div4 :
    Lam d s (fun x => (d : ℝ) * pQ2 v x + 2 * pR v x) =
      (1 / (2 * s)) * Lam d s (fun x => vecNormSq x * pQ2 v x) := by
  have hs := hP.pos
  have hw := hP.weight
  have hv := hP.smooth
  have := gauss_div hs hw (F := fun i x => x i * pQ2 v x)
    (fun i => (sm_coord i).mul (sm_pQ2 hv))
    (fun i => (PDom.coord i).mul_poly' hP.dom_Q2)
    (fun i => by
      refine PDom.congr (fun x => (deriv4 hv i x).symm) ?_
      exact hP.dom_Q2.add ((PDom.sum _ _ fun j _ =>
        (PDom.coord i).mul_poly' ((hP.dom_dv j).mul (hP.dom_S j i))).const_mul 2))
    (fun i => (PDom.coord i).mul_poly' ((PDom.coord i).mul_poly' hP.dom_Q2))
  simp only [div4 hv, sum_coord_mul_coord_mul] at this
  exact this

/-- Fifth identity: `∫ (Δv (x·∇v) + |∇v|² + R) Φ = (1/(2s)) ∫ (x·∇v)² Φ`. -/
theorem lam_div5 :
    Lam d s (fun x => euclideanCoordLaplacian v x * pP v x + pQ2 v x + pR v x) =
      (1 / (2 * s)) * Lam d s (fun x => pP v x * pP v x) := by
  have hs := hP.pos
  have hw := hP.weight
  have hv := hP.smooth
  have := gauss_div hs hw (F := fun i x => euclideanCoordDeriv i v x * pP v x)
    (fun i => (hv.coordDeriv i).mul (sm_pP hv))
    (fun i => (hP.dom_dv i).mul hP.dom_P)
    (fun i => by
      refine PDom.congr (fun x => (deriv5 hv i x).symm) ?_
      exact (((hP.dom_S i i).mul hP.dom_P).add ((hP.dom_dv i).mul (hP.dom_dv i))).add
        (PDom.sum _ _ fun j _ => (PDom.coord j).mul_poly' ((hP.dom_dv i).mul (hP.dom_S j i))))
    (fun i => (PDom.coord i).mul_poly' ((hP.dom_dv i).mul hP.dom_P))
  simp only [div5 hv, sum_coord_mul_mul'] at this
  exact this

end PoonSetup

end

end PDE
