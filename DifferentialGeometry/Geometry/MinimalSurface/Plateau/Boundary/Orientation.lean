import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk
import DifferentialGeometry.Geometry.Measure.Area.Reparametrization

noncomputable section

open DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry

variable {M : Type*} [TopologicalSpace M]

theorem DiskWeakJordanTrace.exists_positive_lift_trace
    {γ : freeLoop M} {u : C(closedDisk, M)} (hu : DiskWeakJordanTrace γ u) :
    ∃ (v : C(closedDisk, M)) (σ : C(loopCircle, loopCircle)) (f : CircleDeg1Lift),
      (v = u ∨ v = u.comp ⟨diskReflection, diskReflection.continuous⟩) ∧
      Continuous f ∧ (∀ t : ℝ, (f t : loopCircle) = σ (t : loopCircle)) ∧
      diskTrace v = γ.comp σ := by
  obtain ⟨σ, ⟨ψ, hψ, hlift, hsign⟩, htrace⟩ := hu
  rcases hsign with ⟨hm, hp⟩ | ⟨hm, hp⟩
  · let f : CircleDeg1Lift :=
      { toFun := ψ
        monotone' := hm
        map_add_one' := hp }
    exact ⟨u, σ, f, Or.inl rfl, hψ, hlift, htrace⟩
  · let τ := σ.comp ⟨fun θ => -θ, continuous_neg⟩
    let f : CircleDeg1Lift :=
      { toFun := fun t => ψ (-t)
        monotone' := hm.comp (fun _ _ h => neg_le_neg h)
        map_add_one' := fun t => by
          have h := hp (-(t + 1))
          rw [show -(t + 1) + 1 = -t by ring] at h
          linarith }
    refine ⟨u.comp ⟨diskReflection, diskReflection.continuous⟩, τ, f,
      Or.inr rfl, hψ.comp continuous_neg, ?_, ?_⟩
    · intro t
      exact (hlift (-t)).trans (congrArg σ (AddCircle.coe_neg (1 : ℝ) (x := t)))
    · ext θ
      change u (diskReflection (diskBoundary θ)) = γ (σ (-θ))
      rw [diskReflection_diskBoundary]
      exact congrArg (fun η : freeLoop M => η (-θ)) htrace

end DifferentialGeometry.Geometry

end
