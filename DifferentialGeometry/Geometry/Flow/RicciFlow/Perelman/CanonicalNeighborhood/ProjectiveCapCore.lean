import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.PositiveComponentModels
import DifferentialGeometry.Topology.Manifold.ULift
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Topology.ProjectiveSpace.PuncturedThreeManifold
import DifferentialGeometry.Topology.ProjectiveSpace.AffineThreeBall
import DifferentialGeometry.Geometry.Metric.RicciSoliton.CylinderQuotientDiffeomorph

section
noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem capCore_of_puncturedProjectiveDiffeomorph
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    (e : PuncturedRealProjectiveThreeSpace ≃ₘ⟮I3, I3⟯ M)
    (ball : PartialDiffeomorph I3 I3 ThreeSpace RealProjectiveThreeSpace ∞)
    (hball : Metric.closedBall (0 : ThreeSpace) 2 ⊆ ball.source)
    (hcenter : ball 0 = realProjectiveThreeSpacePuncture) :
    ∃ F : PartialDiffeomorph I3 I3 RealProjectiveThreeSpace M ∞,
      F.source = {q | q ≠ realProjectiveThreeSpacePuncture} ∧
      (∀ q : PuncturedRealProjectiveThreeSpace, F q.val = e q) ∧
      Nonempty (CapCore (F '' (ball '' Metric.ball (0 : ThreeSpace) 1)ᶜ)) := by
  let O : TopologicalSpace.Opens RealProjectiveThreeSpace :=
    ⟨{q | q ≠ realProjectiveThreeSpacePuncture}, isOpen_compl_singleton⟩
  let : Nonempty O := by
    let z : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
      ⟨EuclideanSpace.single 0 1, by simp [PiLp.norm_single]⟩
    let y := twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture (z,0)
    exact ⟨⟨realProjectiveSpaceQuotientMap y.val,y.property⟩⟩
  let G : PartialDiffeomorph I3 I3 M RealProjectiveThreeSpace ∞ :=
    PartialDiffeomorph.liftTargetOpen (U := O) e.symm.toPartialDiffeomorph rfl
  let F := G.symm
  have hFsource : F.source = {q | q ≠ realProjectiveThreeSpacePuncture} := rfl
  have hFe (q : PuncturedRealProjectiveThreeSpace) : F q.val = e q := by
    have heq : G (e q) = q := by
      change ((e.symm (e q) : PuncturedRealProjectiveThreeSpace) : RealProjectiveThreeSpace) = q.val
      simp
    change G.toPartialEquiv.invFun q.val = e q
    rw [← heq]
    exact G.left_inv' (show e q ∈ G.source from mem_univ _)
  let K := (ball '' Metric.ball (0 : ThreeSpace) 1)ᶜ
  have hK : K ⊆ F.source := by
    intro q hq
    change q ≠ realProjectiveThreeSpacePuncture
    intro heq
    exact hq ⟨0, by simp, hcenter.trans heq.symm⟩
  let Z := ULift.{u} RealProjectiveThreeSpace
  let : ChartedSpace ThreeSpace Z := Topology.uliftChartedSpace _ _
  let : IsManifold I3 ∞ Z := Topology.isManifold_ulift I3 _
  let lift : RealProjectiveThreeSpace ≃ₘ⟮I3,I3⟯ Z := Topology.uliftDiffeomorph I3 _
  let bp := ball.trans lift.toPartialDiffeomorph
  let fp := lift.symm.toPartialDiffeomorph.trans F
  let : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
  let pr : ProjectivePresentation Z :=
    { quotient := fun x => lift (realProjectiveThreePresentation.quotient x)
      smooth := lift.contMDiff.comp realProjectiveThreePresentation.smooth
      onto := lift.surjective.comp realProjectiveThreePresentation.onto
      fibers := fun a b => (lift.injective.eq_iff).trans (realProjectiveThreePresentation.fibers a b)
      local_diffeo := by
        intro x
        have hl := lift.isLocalDiffeomorph
        have hq := realProjectiveSpaceQuotientMap_isLocalDiffeomorph (E := EuclideanSpace ℝ (Fin 4)) (n := 3)
        exact ((isLocalDiffeomorph_comp hl hq).mfderivToContinuousLinearEquiv (by simp) x).bijective }
  have hb : Metric.closedBall (0 : ThreeSpace) 2 ⊆ bp.source := by
    intro x hx
    exact ⟨hball hx, mem_univ _⟩
  have hbimage : bp '' Metric.ball (0 : ThreeSpace) 1 =
      lift '' (ball '' Metric.ball (0 : ThreeSpace) 1) := by
    rw [Set.image_image]
    rfl
  have hc : (bp '' Metric.ball (0 : ThreeSpace) 1)ᶜ = lift '' K := by
    rw [hbimage]
    change (lift.toHomeomorph '' (ball '' Metric.ball (0 : ThreeSpace) 1))ᶜ =
      lift.toHomeomorph '' K
    rw [lift.toHomeomorph.image_compl]
  have hcontains : (bp '' Metric.ball (0 : ThreeSpace) 1)ᶜ ⊆ fp.source := by
    rw [hc]
    rintro _ ⟨q,hq,rfl⟩
    refine ⟨mem_univ _, ?_⟩
    change lift.symm (lift q) ∈ F.source
    rw [Diffeomorph.symm_apply_apply]
    exact hK hq
  have heq : fp '' (bp '' Metric.ball (0 : ThreeSpace) 1)ᶜ = F '' K := by
    rw [hc, Set.image_image]
    congr 1
  exact ⟨F,hFsource,hFe,⟨CapCore.projective Z pr bp hb fp hcontains heq⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end

section
noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private theorem capCore_diagonalSlab
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    (d : Geometry.CylinderDiagonalQuotient ≃ₘ⟮IC, I3⟯ M)
    {L : ℝ} (hL : 0 < L) :
    Nonempty (CapCore (d '' (Geometry.cylinderDiagonalQuotientMap ''
      (univ ×ˢ Icc (-L) L)))) := by
  let E := Geometry.cylinderDiagonalQuotientDiffeomorph
  let e := E.symm.trans d
  obtain ⟨F,hFsource,hFe,hcore⟩ := capCore_of_puncturedProjectiveDiffeomorph e
    (realProjectiveThreeAffineBall L hL.ne')
    (realProjectiveThreeAffineBall_contains_closedBall L hL.ne')
    (by rw [realProjectiveThreeAffineBall_apply, realProjectiveThreeAffineBallMap_zero])
  have heq : F '' (realProjectiveThreeAffineBall L hL.ne' ''
      Metric.ball (0 : ThreeSpace) 1)ᶜ =
      d '' (Geometry.cylinderDiagonalQuotientMap '' (univ ×ˢ Icc (-L) L)) := by
    rw [realProjectiveThreeAffineBall_complement_eq_slab_image hL, Set.image_image,
      Set.image_image]
    apply Set.image_congr
    intro p hp
    have hh := hFe (E (Geometry.cylinderDiagonalQuotientMap p))
    have hproj : (E (Geometry.cylinderDiagonalQuotientMap p)).val =
        realProjectiveSpaceQuotientMap
          (twoSphereProdRealHomeomorphThreeSphereAwayFromRealProjectivePuncture p).val := rfl
    rw [hproj] at hh
    change F _ = d (E.symm (E (Geometry.cylinderDiagonalQuotientMap p))) at hh
    simpa only [Diffeomorph.symm_apply_apply] using hh
  rw [heq] at hcore
  exact hcore

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end

end
