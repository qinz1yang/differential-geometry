import DifferentialGeometry.Topology.Manifold.OneManifold.CircleConsequences

/-!
# Applications of the circle classification

* the circle itself (model `𝓡 1`);
* the circle clause of LC83 in its model shape: every fibre of the trivial circle bundle
  `Circle × ℝ → ℝ`, with the regular-fibre charted space, is diffeomorphic to the circle.
-/

set_option autoImplicit false

open Set Manifold
open scoped ContDiff

namespace DifferentialGeometry.Topology.Manifold.OneManifold

theorem nonempty_diffeomorph_circle_self : Nonempty (Circle ≃ₘ⟮𝓡 1, 𝓡 1⟯ Circle) :=
  nonempty_diffeomorph_circle

theorem surjective_mfderiv_snd_circle_prod (x : Circle × ℝ) :
    Function.Surjective (mfderiv ((𝓡 1).prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Prod.snd x) := by
  rw [mfderiv_snd]
  intro v
  exact ⟨(0, v), rfl⟩

theorem nonempty_circle_diffeomorph_fiber_snd (t : ℝ) :
    letI := regularFiberChartedSpace (Prod.snd : Circle × ℝ → ℝ) t contMDiff_snd
      (fun x _ => surjective_mfderiv_snd_circle_prod x)
    Nonempty (Circle ≃ₘ⟮𝓡 1, 𝓘(ℝ, Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 1) × ℝ) -
      Module.finrank ℝ ℝ) → ℝ)⟯ {x : Circle × ℝ // x.2 = t}) := by
  have hfib : {x : Circle × ℝ | x.2 = t} = range (fun z : Circle => (z, t)) := by
    ext x
    constructor
    · intro hx
      exact ⟨x.1, Prod.ext rfl hx.symm⟩
    · rintro ⟨z, rfl⟩
      rfl
  have hcont : Continuous (fun z : Circle => (z, t)) := continuous_id.prodMk continuous_const
  apply nonempty_circle_diffeomorph_regularFiber
  · simp
  · rw [hfib]
    exact isCompact_range hcont
  · rw [hfib]
    exact isConnected_range hcont

end DifferentialGeometry.Topology.Manifold.OneManifold
