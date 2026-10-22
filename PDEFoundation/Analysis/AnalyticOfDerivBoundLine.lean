module

public import PDEFoundation.Analysis.AnalyticOfDerivBound

/-!
# Iterated derivatives along affine lines
-/

@[expose] public section

namespace PDE

/-- Iterated ordinary derivatives along an affine line are diagonal evaluations
of iterated Fréchet derivatives. -/
theorem iteratedDeriv_affine_line {d m : ℕ}
    (g : Vec d → ℝ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (x₀ h : Vec d) (t : ℝ) :
    iteratedDeriv m (fun s : ℝ => g (x₀ + s • h)) t =
      iteratedFDeriv ℝ m g (x₀ + t • h) (fun _ : Fin m => h) := by
  let L := ContinuousLinearMap.toSpanSingleton ℝ h
  let G : Vec d → ℝ := fun z => g (x₀ + z)
  have hG : ContDiff ℝ (⊤ : ℕ∞) G := by
    exact hg.comp (contDiff_const.add contDiff_id)
  have hγ : (fun s : ℝ => g (x₀ + s • h)) = G ∘ L := by
    funext s
    simp [G, L, ContinuousLinearMap.toSpanSingleton_apply]
  rw [hγ, iteratedDeriv_eq_iteratedFDeriv]
  rw [L.iteratedFDeriv_comp_right hG t (by simp)]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [iteratedFDeriv_comp_add_left]
  simp only [L, ContinuousLinearMap.toSpanSingleton_apply, one_smul]

end PDE
