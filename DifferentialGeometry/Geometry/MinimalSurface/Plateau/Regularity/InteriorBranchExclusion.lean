import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk
import DifferentialGeometry.Topology.LoopSpace.WeaklyMonotone.FactorDegree

set_option autoImplicit false

noncomputable section

open DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry

theorem DiskWeakJordanTrace.integer_shift_eq_one_or_neg_one_of_factor
    {M : Type*} [TopologicalSpace M] {γ : freeLoop M} {u : C(closedDisk, M)}
    (hu : DiskWeakJordanTrace γ u) (hγ : Function.Injective γ)
    {τ ρ : C(loopCircle, loopCircle)} (hfactor : diskTrace u = (γ.comp τ).comp ρ)
    (F : C(ℝ, ℝ)) (n : ℤ)
    (hlift : ∀ t : ℝ, (F t : loopCircle) = ρ (t : loopCircle))
    (hshift : ∀ t : ℝ, F (t + 1) = F t + (n : ℝ)) : n = 1 ∨ n = -1 := by
  obtain ⟨σ, hσ, htrace⟩ := hu
  have hσeq : σ = τ.comp ρ := by
    ext θ
    apply hγ
    exact congrArg (fun f : C(loopCircle, M) => f θ) (htrace.symm.trans hfactor)
  rw [hσeq] at hσ
  exact hσ.integer_shift_eq_one_or_neg_one_of_comp F n hlift hshift

end DifferentialGeometry.Geometry
