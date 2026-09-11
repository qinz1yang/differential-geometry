import DifferentialGeometry.Topology.LoopSpace.Basic
import Mathlib.Topology.Covering.AddCircle
import Mathlib.Topology.Homotopy.Lifting
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Algebra.Module.LocallyConvex







noncomputable section

open Function

namespace DifferentialGeometry.Topology



theorem exists_real_homeomorphism_lift (ψ : loopCircle ≃ₜ loopCircle) :
    ∃ F : ℝ ≃ₜ ℝ, ∀ t : ℝ, (F t : loopCircle) = ψ (t : loopCircle) := by
  let p : ℝ → loopCircle := fun t => (t : loopCircle)
  have hcov : IsCoveringMap p := AddCircle.isCoveringMap_coe (1 : ℝ)
  obtain ⟨a, ha⟩ := QuotientAddGroup.mk_surjective (ψ 0)
  let f : C(ℝ, loopCircle) := ⟨ψ ∘ p, ψ.continuous.comp hcov.continuous⟩
  obtain ⟨F, ⟨hF0, hFlift⟩, _⟩ := hcov.existsUnique_continuousMap_lifts f 0 a (by
    change (a : loopCircle) = ψ (0 : loopCircle)
    exact ha)
  let g : C(ℝ, loopCircle) := ⟨ψ.symm ∘ p, ψ.symm.continuous.comp hcov.continuous⟩
  obtain ⟨G, ⟨hGa, hGlift⟩, _⟩ := hcov.existsUnique_continuousMap_lifts g a 0 (by
    change (0 : loopCircle) = ψ.symm (a : loopCircle)
    rw [ha, ψ.symm_apply_apply])
  have hF (t : ℝ) : p (F t) = ψ (p t) := congrFun hFlift t
  have hG (t : ℝ) : p (G t) = ψ.symm (p t) := congrFun hGlift t
  have hGF : G ∘ F = (id : ℝ → ℝ) := hcov.eq_of_comp_eq
    (G.continuous.comp F.continuous) continuous_id (by
      funext t
      change p (G (F t)) = p t
      rw [hG, hF, ψ.symm_apply_apply]) 0 (by
      change G (F 0) = 0
      rw [hF0, hGa])
  have hFG : F ∘ G = (id : ℝ → ℝ) := hcov.eq_of_comp_eq
    (F.continuous.comp G.continuous) continuous_id (by
      funext t
      change p (F (G t)) = p t
      rw [hF, hG, ψ.apply_symm_apply]) a (by
      change F (G a) = a
      rw [hGa, hF0])
  let H : ℝ ≃ₜ ℝ := {
    toFun := F
    invFun := G
    left_inv := fun t => congrFun hGF t
    right_inv := fun t => congrFun hFG t
    continuous_toFun := F.continuous
    continuous_invFun := G.continuous }
  exact ⟨H, hF⟩

end DifferentialGeometry.Topology
