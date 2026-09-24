import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ConformalDisk
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDiskExtension
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothTraceLift
import DifferentialGeometry.Geometry.Measure.Area.Reparametrization








noncomputable section

open Bundle Manifold DifferentialGeometry Set ContinuousMap Filter
open DifferentialGeometry.Topology
open scoped Bundle Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]




omit [T3Space M] in
theorem IsMorreyDisk.exists_conformal_minimizing_disk
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (hd : Module.finrank ℝ E = 3) {γ : freeLoop M}
    (hγ : IsSmoothEmbeddedLoop (E := E) γ) {u : C(closedDisk, M)}
    (hu : IsMorreyDisk g γ u) (hboundary : ∃ U : ℂ → M, SmoothDiskExtension (E := E) u U) :
    ∃ (v : C(closedDisk, M)) (σ : C(loopCircle, loopCircle)) (U : ℂ → M),
      (v = u ∨ v = u.comp ⟨diskReflection, diskReflection.continuous⟩) ∧
      riemannianDiskArea g v = riemannianDiskArea g u ∧
      IsConformalMinimizingDisk g γ v σ U := by
  let _ := hd
  obtain ⟨U₀, hU₀⟩ := hboundary
  have hb : ∃ U : ℂ → M, SmoothDiskExtension (E := E) u U := ⟨U₀, hU₀⟩
  obtain ⟨σ, ψ, hψ, hlift, htrace, hsign⟩ :=
    hu.trace.exists_smooth_signed_lift hγ hU₀.smoothUpToBoundary
  rcases hsign with ⟨hmono, hper⟩ | ⟨hanti, hper⟩
  · exact exists_conformal_minimizing_disk_of_smooth_positive_trace g hu hb σ
      ⟨ψ, hψ, hmono, hper, hlift⟩ (Or.inl htrace)
  · refine exists_conformal_minimizing_disk_of_smooth_positive_trace g hu hb
      (σ.comp ⟨fun θ => -θ, continuous_neg⟩) ?_ (Or.inr ?_)
    · refine ⟨fun t => ψ (-t), hψ.comp contDiff_neg, ?_, ?_, ?_⟩
      · exact hanti.comp (fun a b h => neg_le_neg h)
      · intro t
        simp only []
        have h := hper (-(t + 1))
        have h' : -(t + 1) + 1 = -t := by ring
        rw [h'] at h
        linarith
      · intro t
        exact (hlift (-t)).trans (congrArg σ (AddCircle.coe_neg (1 : ℝ) (x := t)))
    · ext θ
      simp only [diskTrace, ContinuousMap.comp_apply, ContinuousMap.coe_mk]
      rw [diskReflection_diskBoundary]
      exact congrArg (fun η : freeLoop M => η (-θ)) htrace

end DifferentialGeometry.Geometry
