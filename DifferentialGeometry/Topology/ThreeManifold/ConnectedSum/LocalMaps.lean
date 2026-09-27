import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.Defs
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SmoothConnectedSum

universe u v w uE uH

variable {M : ClosedOrientedManifold.{u} 3} {N : ClosedOrientedManifold.{v} 3}
  {c : OrientedBallChart M} {d : OrientedBallChart N} {a : BoundaryAttachment}
  (s : SmoothConnectedSum c d a)
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type uH} [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  {P : Type w} [TopologicalSpace P] [ChartedSpace H P]

theorem isLocalDiffeomorphOn_of_comp
    (F : s.toConnectedClosedOrientedManifold.Carrier → P)
    (U : Set s.toConnectedClosedOrientedManifold.Carrier)
    (hleft : ∀ x, ConnectedSumQuotient.interiorLeft c.toBallChart d.toBallChart a.1 x ∈ U →
      IsLocalDiffeomorphAt (𝓡 3) J ∞
        (F ∘ ConnectedSumQuotient.interiorLeft c.toBallChart d.toBallChart a.1) x)
    (hright : ∀ x, ConnectedSumQuotient.interiorRight c.toBallChart d.toBallChart a.1 x ∈ U →
      IsLocalDiffeomorphAt (𝓡 3) J ∞
        (F ∘ ConnectedSumQuotient.interiorRight c.toBallChart d.toBallChart a.1) x)
    (hcollar : ∀ x, ConnectedSumQuotient.collarMap c.toBallChart d.toBallChart a.1 x ∈ U →
      IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) J ∞
        (F ∘ ConnectedSumQuotient.collarMap c.toBallChart d.toBallChart a.1) x) :
    IsLocalDiffeomorphOn (𝓡 3) J ∞ F U := by
  let _ : ChartedSpace (EuclideanSpace ℝ (Fin 3)) s.toConnectedClosedOrientedManifold.Carrier :=
    s.charts
  intro x
  rcases ConnectedSumQuotient.interior_collar_cover c.toBallChart d.toBallChart a.1 x.val with
    ⟨y, hy⟩ | ⟨y, hy⟩ | ⟨y, hy⟩
  · have hmem : ConnectedSumQuotient.interiorLeft c.toBallChart d.toBallChart a.1 y ∈ U :=
      hy.symm ▸ x.property
    rw [← hy]
    exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp (hleft y hmem)
      (s.interiorLeft_localDiffeomorph y)
  · have hmem : ConnectedSumQuotient.interiorRight c.toBallChart d.toBallChart a.1 y ∈ U :=
      hy.symm ▸ x.property
    rw [← hy]
    exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp (hright y hmem)
      (s.interiorRight_localDiffeomorph y)
  · have hmem : ConnectedSumQuotient.collarMap c.toBallChart d.toBallChart a.1 y ∈ U :=
      hy.symm ▸ x.property
    rw [← hy]
    exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp (hcollar y hmem)
      (s.collar_localDiffeomorph y)

theorem isLocalDiffeomorph_restrict_of_comp
    (F : s.toConnectedClosedOrientedManifold.Carrier → P)
    (U : TopologicalSpace.Opens s.toConnectedClosedOrientedManifold.Carrier)
    (hleft : ∀ x, ConnectedSumQuotient.interiorLeft c.toBallChart d.toBallChart a.1 x ∈ U →
      IsLocalDiffeomorphAt (𝓡 3) J ∞
        (F ∘ ConnectedSumQuotient.interiorLeft c.toBallChart d.toBallChart a.1) x)
    (hright : ∀ x, ConnectedSumQuotient.interiorRight c.toBallChart d.toBallChart a.1 x ∈ U →
      IsLocalDiffeomorphAt (𝓡 3) J ∞
        (F ∘ ConnectedSumQuotient.interiorRight c.toBallChart d.toBallChart a.1) x)
    (hcollar : ∀ x, ConnectedSumQuotient.collarMap c.toBallChart d.toBallChart a.1 x ∈ U →
      IsLocalDiffeomorphAt ((𝓡 2).prod 𝓘(ℝ, ℝ)) J ∞
        (F ∘ ConnectedSumQuotient.collarMap c.toBallChart d.toBallChart a.1) x) :
    IsLocalDiffeomorph (𝓡 3) J ∞ (fun x : U => F x) :=
  DifferentialGeometry.isLocalDiffeomorph_restrict_open U
    (s.isLocalDiffeomorphOn_of_comp F U hleft hright hcollar)

end DifferentialGeometry.Topology.SmoothConnectedSum
