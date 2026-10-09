import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.BallComplement
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Boundary
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PositiveComponentModels
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ProjectiveCapCore
import DifferentialGeometry.Topology.ProjectiveSpace.AffineThreeBall
import DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotientDiffeomorph

section
open private capCore_of_puncturedProjectiveDiffeomorph from DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ProjectiveCapCore

set_option autoImplicit false

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {P M : Type*} [TopologicalSpace P] [ChartedSpace ThreeSpace P]
  [TopologicalSpace M] [ChartedSpace ThreeSpace M] [T2Space M]

theorem exists_projectivePresentation_of_diagonal_slab_and_exterior_ball
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮IC, I3⟯ P)
    (Phi : PartialDiffeomorph I3 I3 P M ∞) {L : ℝ} (hL : 0 < L)
    (hsource : d '' (Geometry.cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-L) L)) ⊆ Phi.source)
    (G : PartialDiffeomorph I3 I3 ThreeSpace M ∞)
    (hG : Metric.closedBall (0 : ThreeSpace) 1 ⊆ G.source)
    (hGo : G '' Metric.ball (0 : ThreeSpace) 1 =
      (Phi '' (d '' (Geometry.cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-L) L))))ᶜ)
:
    ∃ e : RealProjectiveThreeSpace ≃ₘ⟮I3, I3⟯ M,
      (∀ z : Cylinder, z ∈ univ ×ˢ Icc (-L) L →
        e (Geometry.cylinderDiagonalQuotientDiffeomorph (Geometry.cylinderDiagonalQuotientMap z)).val =
          Phi (d (Geometry.cylinderDiagonalQuotientMap z))) ∧
      ∃ pr : ProjectivePresentation M,
        (∀ a : Sphere 3, pr.quotient a = e (realProjectiveSpaceQuotientMap a)) ∧
        ∃ D : ThreeSpace ≃ₘ⟮I3, I3⟯ ThreeSpace,
          D '' Metric.closedBall (0 : ThreeSpace) 1 = Metric.closedBall (0 : ThreeSpace) 1 ∧
          (∀ z ∈ Metric.closedBall (0 : ThreeSpace) 1,
            e (realProjectiveThreeAffineBall L hL.ne' z) = G (D z)) := by
  let E := Geometry.cylinderDiagonalQuotientDiffeomorph
  let ep := E.symm.trans d
  let b := realProjectiveThreeAffineBall L hL.ne'
  have hb2 : Metric.closedBall (0 : ThreeSpace) 2 ⊆ b.source :=
    realProjectiveThreeAffineBall_contains_closedBall L hL.ne'
  have hb1 : Metric.closedBall (0 : ThreeSpace) 1 ⊆ b.source :=
    (Metric.closedBall_subset_closedBall (by norm_num)).trans hb2
  obtain ⟨T, hTsource, hT, _hcore⟩ := capCore_of_puncturedProjectiveDiffeomorph ep b hb2
    (by rw [realProjectiveThreeAffineBall_apply, realProjectiveThreeAffineBallMap_zero])
  let K := (b '' Metric.ball (0 : ThreeSpace) 1)ᶜ
  have hKT : K ⊆ T.source := by
    intro y hy
    rw [hTsource]
    intro heq
    exact hy ⟨0, by simp, (by rw [realProjectiveThreeAffineBall_apply,
      realProjectiveThreeAffineBallMap_zero]; exact heq.symm)⟩
  have hTimage : T '' K = d '' (Geometry.cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-L) L)) := by
    rw [show K = (realProjectiveThreeAffineBall L hL.ne' '' Metric.ball (0 : ThreeSpace) 1)ᶜ from rfl,
      realProjectiveThreeAffineBall_complement_eq_slab_image hL, image_image, image_image]
    apply image_congr
    intro z hz
    have hh := hT (E (Geometry.cylinderDiagonalQuotientMap z))
    have hproj : (E (Geometry.cylinderDiagonalQuotientMap z)).val =
        realProjectiveSpaceQuotientMap
          (twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture z).val := rfl
    rw [hproj] at hh
    change T _ = d (E.symm (E (Geometry.cylinderDiagonalQuotientMap z))) at hh
    simpa only [Diffeomorph.symm_apply_apply] using hh
  let Q := T.trans Phi
  let U := Phi '' (d '' (Geometry.cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-L) L)))
  have hKQ : K ⊆ Q.source := by
    intro y hy
    exact ⟨hKT hy, hsource (hTimage ▸ mem_image_of_mem T hy)⟩
  have hQU : Q '' K = U := by
    change (Phi ∘ T) '' K = U
    rw [image_comp, hTimage]
  obtain ⟨e, heQ, _heBall, D, hDball, heG, O, hOo, hKO, hOQ, heO⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_diffeomorph_of_ball_complement_and_ball b Q G
      hb1 hKQ hG hQU hGo
  refine ⟨e, ?_, realProjectiveThreePresentation.map e, fun _ => rfl, D, hDball, heG⟩
  intro z hz
  have hproj : (E (Geometry.cylinderDiagonalQuotientMap z)).val ∈ K := by
    rw [show K = (realProjectiveThreeAffineBall L hL.ne' '' Metric.ball (0 : ThreeSpace) 1)ᶜ from rfl,
      realProjectiveThreeAffineBall_complement_eq_slab_image hL]
    exact ⟨z, hz, rfl⟩
  rw [heQ hproj]
  change Phi (T (E (Geometry.cylinderDiagonalQuotientMap z)).val) = _
  rw [hT]
  change Phi (d (E.symm (E (Geometry.cylinderDiagonalQuotientMap z)))) = _
  rw [Diffeomorph.symm_apply_apply]

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
