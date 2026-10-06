import DifferentialGeometry.Geometry.MinimalSurface.ExteriorDiskAttainment
import DifferentialGeometry.Geometry.MinimalSurface.FixedBoundary.SpanningDiskRegularity

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.MinimalSurface

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M]

/-- Consumer of the IMS03 attainment kernel: an exact-trace exterior spanning disk `q` whose
area equals the area of a confined Morrey disk is an attainer of `leastExteriorDiskArea`, the
infimum is positive, and the prescribed boundary loop is a smooth embedded loop. -/
theorem exists_attainer_data_of_morrey_exactTrace_IM
    (g : SmoothRiemannianMetric (𝓡 3) M) (U : TopologicalSpace.Opens M)
    (G : SmoothRiemannianMetric (𝓡 3) U) {W : Set M}
    (hWU : W ⊆ (U : Set M))
    (hmetric : ∀ x : U, (x : M) ∈ W → G.inner x = (g.restrictOpen U).inner x)
    {γ : freeLoop U} {u : C(closedDisk, U)} (hu : IsMorreyDisk G γ u)
    (hγ : IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γ)
    (huW : ∀ z : closedDisk, (u z : M) ∈ W)
    {q : C(closedDisk, M)}
    (hq : isExteriorSpanningDisk W
      ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)).comp γ) q)
    (harea : riemannianDiskArea g q = riemannianDiskArea g (Subtype.val ∘ u)) :
    IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3))
        ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)).comp γ) ∧
      riemannianDiskArea g q = leastExteriorDiskArea g W
        ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)).comp γ) ∧
      0 < leastExteriorDiskArea g W
        ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)).comp γ) := by
  obtain ⟨hattain, hpos⟩ :=
    isExteriorSpanningDisk.attains_positive_leastExteriorDiskArea_of_morrey_open
      g U G hWU hmetric hu hγ huW hq harea
  exact ⟨hq.isSmoothEmbeddedLoop, hattain, hpos⟩

end DifferentialGeometry.Geometry.MinimalSurface
