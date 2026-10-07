import DifferentialGeometry.Geometry.Hyperbolic.RigidityProofHGI

/-!
# Consumer of the G5 intake (S-HG-INTAKE, suffix `_HGI`)

`mostow_prasad_HGI` (the proved twin of the skeleton `mostow_prasad`) gives, for two complete
finite-volume hyperbolic three-manifolds with a homotopy equivalence, an isometric diffeomorphism.
-/

set_option autoImplicit false

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Hyperbolic

variable {M N : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [IsManifold (𝓡 3) ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N]
  [IsManifold (𝓡 3) ∞ N] [T2Space N] [SigmaCompactSpace N] [ConnectedSpace N]

theorem exists_isometric_diffeomorph_of_homotopyEquiv_HGI
    (g : SmoothRiemannianMetric (𝓡 3) M) (h : SmoothRiemannianMetric (𝓡 3) N)
    (K : ℝ) (hK : K < 0)
    (hgcurvature : hasConstantSectionalCurvature g K)
    (hhcurvature : hasConstantSectionalCurvature h K)
    (hgcomplete : RiemannianMetricComplete g) (hhcomplete : RiemannianMetricComplete h)
    (hgvolume : Integral.Measure.riemannianVolumeMeasure (𝓡 3) M g Set.univ < ⊤)
    (hhvolume : Integral.Measure.riemannianVolumeMeasure (𝓡 3) N h Set.univ < ⊤)
    (u : ContinuousMap.HomotopyEquiv M N) :
    ∃ f : M ≃ₘ⟮𝓡 3, 𝓡 3⟯ N, ∀ (p : M) (v w : TangentSpace (𝓡 3) p),
      h.inner (f p) (mfderiv (𝓡 3) (𝓡 3) f p v) (mfderiv (𝓡 3) (𝓡 3) f p w) = g.inner p v w := by
  obtain ⟨f, hf, -⟩ := mostow_prasad_HGI g h K hK hgcurvature hhcurvature hgcomplete hhcomplete
    hgvolume hhvolume u
  exact ⟨f, hf.1⟩

end DifferentialGeometry.Geometry.Hyperbolic
