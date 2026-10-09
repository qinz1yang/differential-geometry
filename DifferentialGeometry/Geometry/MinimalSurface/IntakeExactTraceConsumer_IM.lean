import DifferentialGeometry.Geometry.MinimalSurface.ExteriorDiskPhase

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.MinimalSurface

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M]

/-- Consumer of the IMS03 exact-trace kernel: an area-attaining exterior spanning disk whose
trace is only a weakly monotone reparametrization `γ.comp σ` of the prescribed embedded loop
yields an exact-trace attainer for `γ` itself, with the same infimum. -/
theorem exists_exact_trace_attainer_of_weakly_monotone_IM
    (g : SmoothRiemannianMetric (𝓡 3) M)
    {W : Set M} {γ : freeLoop M} {u : C(closedDisk, M)}
    {σ : C(loopCircle, loopCircle)}
    (hu : isExteriorSpanningDisk W (γ.comp σ) u)
    (hγ : IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γ)
    (hσ : IsWeaklyMonotoneOnce σ)
    (harea : riemannianDiskArea g u = leastExteriorDiskArea g W γ) :
    ∃ v : C(closedDisk, M), isExteriorSpanningDisk W γ v ∧
      riemannianDiskArea g v = leastExteriorDiskArea g W γ := by
  obtain ⟨_, _, φ, _, _, _, _, hexact, _, hareav⟩ :=
    hu.exists_exact_trace_of_weakly_monotone_phase hγ hσ
  exact ⟨u.comp ⟨φ, φ.continuous⟩, hexact, (hareav g).trans harea⟩

end DifferentialGeometry.Geometry.MinimalSurface
