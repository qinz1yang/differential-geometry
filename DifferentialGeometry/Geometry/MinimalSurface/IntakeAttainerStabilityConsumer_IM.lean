import DifferentialGeometry.Geometry.MinimalSurface.FixedBoundary.AttainerStability
import DifferentialGeometry.Geometry.MinimalSurface.IntakeAttainmentConsumer_IM

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.MinimalSurface

variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] [IsManifold (𝓡 3) ∞ M]
  [T3Space M]

/-- Consumer chain of two IMS03 kernels: the exact-trace disk `q` of equal area to a confined
Morrey disk attains `leastExteriorDiskArea` (attainment kernel), hence it is a stable minimal
disk to which the every-attainer Jacobi theorem applies; here we extract its smooth closed-disk
extension with injective derivative (the immersion that the Jacobi form is stated on). -/
theorem exists_immersed_extension_of_morrey_exactTrace_attainer_IM
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
    ∃ V : ℂ → M, SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3)) q V ∧
      ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
        Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) V z) := by
  obtain ⟨_, hattain, _⟩ :=
    exists_attainer_data_of_morrey_exactTrace_IM g U G hWU hmetric hu hγ huW hq harea
  obtain ⟨V, hV, hrank, _⟩ := every_area_attaining_exterior_disk_jacobi_form g W
    ((⟨Subtype.val, continuous_subtype_val⟩ : C(U, M)).comp γ) q hq hattain
  exact ⟨V, hV, hrank⟩

end DifferentialGeometry.Geometry.MinimalSurface
