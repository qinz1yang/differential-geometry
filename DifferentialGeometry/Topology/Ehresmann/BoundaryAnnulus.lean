import DifferentialGeometry.Topology.Ehresmann.BoundaryFiberTransport
import DifferentialGeometry.Topology.Ehresmann.Interval
import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Analysis.Normed.Module.Connected

noncomputable section
open Set Topology Manifold
open scoped ContDiff

namespace Poincare.Topology.Ehresmann

open Poincare.Geometry.Boundary
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
  [CompactSpace M] [T2Space M] {I : ModelWithCorners ℝ E H}
  [hI : HasSmoothBoundary E H I] [IsManifold I ∞ M]

set_option backward.isDefEq.respectTransparency false in
theorem exists_boundary_sphere_annulus
    {u : M → ℝ} {a b : ℝ} (hab : a < b) (hu : ContMDiff I 𝓘(ℝ) ∞ u)
    (hreg : ∀ x, mfderiv I 𝓘(ℝ) u x ≠ 0)
    (hboundary : ∀ x, I.IsBoundaryPoint x → u x = a ∨ u x = b)
    (ha : a ∈ range u) (hb : b ∈ range u)
    (η : Diffeomorph (𝓡 2) hI.boundaryI
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (boundaryLevel u a b hab.ne hu.continuous hboundary) ∞) :
    ∃ Ψ : Diffeomorph ((𝓡 2).prod (𝓡∂ 1)) I
        (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc (0 : ℝ) 1) M ∞,
      (∀ p, u (Ψ p) = a + (b - a) * p.2.1) ∧
      (∀ z, Ψ (z, ⟨0, by norm_num⟩) = (η z).1.1) ∧
      ∃ C : ∀ s : Icc a b,
          ChartedSpace (Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ) {x : M // u x = s.1},
        let _ (s : Icc a b) := C s
        (∀ s : Icc a b, IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ)
          ∞ {x : M // u x = s.1}) ∧
        ∀ s : Icc a b,
          Nonempty (Diffeomorph (𝓡 2) 𝓘(ℝ, Fin (Module.finrank ℝ E - Module.finrank ℝ ℝ) → ℝ)
            (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) {x : M // u x = s.1} ∞) ∧
          ConnectedSpace {x : M // u x = s.1} := by
  let _ : Fact (a < b) := ⟨hab⟩
  obtain ⟨C, hm, _, Θ, hh, hl, S, _, _⟩ :=
    exists_boundary_interval_fiber_transport hab hu hreg hboundary ha hb
  let c (s : Icc a b) := C s
  let Ψ := unitCylinderDiffeomorphOfProduct a b η Θ
  have hΨ (p) : u (Ψ p) = a + (b - a) * p.2.1 := by
    rw [unitCylinderDiffeomorphOfProduct_apply, hh, affineIntervalDiffeomorph_apply]
    exact add_comm _ _
  have hlower (z) : Ψ (z, ⟨0, by norm_num⟩) = (η z).1.1 := by
    rw [unitCylinderDiffeomorphOfProduct_lower]
    exact hl (η z)
  have hdim : 1 < Module.rank ℝ (EuclideanSpace ℝ (Fin 3)) := by
    rw [← Module.finrank_eq_rank]
    norm_num
  have hsphere : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_sphere hdim _ zero_le_one)
  refine ⟨Ψ, hΨ, hlower, C, hm, ?_⟩
  intro s
  let e := η.trans (S s)
  exact ⟨⟨e⟩, e.toHomeomorph.connectedSpace_iff.mp hsphere⟩

end Poincare.Topology.Ehresmann
