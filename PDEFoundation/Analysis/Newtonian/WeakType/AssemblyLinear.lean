module

public import PDEFoundation.Analysis.Newtonian.Potential.Smooth
public import PDEFoundation.Analysis.Newtonian.Potential.Decay
public import PDEFoundation.Sobolev.ClassicalGradient

/-!
# Linearity of `F ↦ ∇ u_F` on smooth compactly supported fields
-/

@[expose] public section

open MeasureTheory

namespace PDE.NewtonWeakType

noncomputable section

variable {d : ℕ}

theorem newtonPotential_add (hd : 0 < d) {H₁ H₂ : Vec d → Vec d} (h₁ : Continuous H₁)
    (c₁ : HasCompactSupport H₁) (h₂ : Continuous H₂) (c₂ : HasCompactSupport H₂) (x : Vec d) :
    newtonPotential (fun y => H₁ y + H₂ y) x = newtonPotential H₁ x + newtonPotential H₂ x := by
  unfold newtonPotential
  rw [← integral_add (integrable_vecDot_newtonKernel_sub hd h₁ c₁ x)
    (integrable_vecDot_newtonKernel_sub hd h₂ c₂ x)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp [vecDot, mul_add, Finset.sum_add_distrib]

theorem classicalGradient_newtonPotential_add (hd : 0 < d) {H₁ H₂ : Vec d → Vec d}
    (h₁ : ContDiff ℝ (⊤ : ℕ∞) H₁) (c₁ : HasCompactSupport H₁)
    (h₂ : ContDiff ℝ (⊤ : ℕ∞) H₂) (c₂ : HasCompactSupport H₂) (x : Vec d) :
    classicalGradient (newtonPotential (fun y => H₁ y + H₂ y)) x =
      classicalGradient (newtonPotential H₁) x + classicalGradient (newtonPotential H₂) x := by
  have e : newtonPotential (fun y => H₁ y + H₂ y) =
      fun x => newtonPotential H₁ x + newtonPotential H₂ x :=
    funext (newtonPotential_add hd h₁.continuous c₁ h₂.continuous c₂)
  have d₁ := (contDiff_newtonPotential hd h₁ c₁).differentiable (by simp) x
  have d₂ := (contDiff_newtonPotential hd h₂ c₂).differentiable (by simp) x
  funext i
  simp only [classicalGradient, e, Pi.add_apply]
  rw [fderiv_fun_add d₁ d₂]
  rfl

theorem hasCompactSupport_finsetSum {ι : Type*} (s : Finset ι) {H : ι → Vec d → Vec d}
    (hc : ∀ k ∈ s, HasCompactSupport (H k)) : HasCompactSupport (fun y => ∑ k ∈ s, H k y) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact HasCompactSupport.zero
  | insert b t hb ih =>
    simp only [Finset.sum_insert hb]
    exact (hc b (Finset.mem_insert_self _ _)).add
      (ih fun k hk => hc k (Finset.mem_insert_of_mem hk))

theorem classicalGradient_newtonPotential_finsetSum (hd : 0 < d) {ι : Type*} (s : Finset ι)
    {H : ι → Vec d → Vec d} (hs : ∀ k ∈ s, ContDiff ℝ (⊤ : ℕ∞) (H k))
    (hc : ∀ k ∈ s, HasCompactSupport (H k)) (x : Vec d) :
    classicalGradient (newtonPotential (fun y => ∑ k ∈ s, H k y)) x =
      ∑ k ∈ s, classicalGradient (newtonPotential (H k)) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have : newtonPotential (fun y => ∑ k ∈ (∅ : Finset ι), H k y) = fun _ => 0 := by
      funext z; simp [newtonPotential, vecDot]
    rw [this]
    funext i
    simp [classicalGradient]
  | insert a s ha ih =>
    have hs' : ∀ k ∈ s, ContDiff ℝ (⊤ : ℕ∞) (H k) := fun k hk => hs k (Finset.mem_insert_of_mem hk)
    have hc' : ∀ k ∈ s, HasCompactSupport (H k) := fun k hk => hc k (Finset.mem_insert_of_mem hk)
    have hsum : ContDiff ℝ (⊤ : ℕ∞) (fun y => ∑ k ∈ s, H k y) := by
      refine ContDiff.sum fun k hk => hs' k hk
    have hsumc : HasCompactSupport (fun y => ∑ k ∈ s, H k y) := hasCompactSupport_finsetSum s hc'
    simp only [Finset.sum_insert ha]
    rw [classicalGradient_newtonPotential_add hd (hs a (Finset.mem_insert_self _ _))
      (hc a (Finset.mem_insert_self _ _)) hsum hsumc x, ih hs' hc']

end

end PDE.NewtonWeakType
