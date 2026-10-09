import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePlugCapBallCharts
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibrePlugCutComponents
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Piece

/-!
Actual positive cap ball charts in the same canonical capped plug components, with their
unchanged ambient cap images and spherical attachment maps.
-/

set_option autoImplicit false

noncomputable section

open Set Function Topology Manifold Metric
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Seifert
open GC.GraphManifold.MixedBoundaryCertificate
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.ElementaryPresentation

variable {W : CompactCarrier.{u}} (E : ElementaryPresentation W)
  {j : Fin E.toTorus.pairing.count} {b : Bool} (h : E.IsSplitSeam j b)
  (hlin : E.IsLinearSeam j)
  (d : PartialDiffeomorph sphereSignedCollarModel W.model
    (ClosureSphere.{u} × ℝ) W.Carrier ∞) (hs : d.source = sphereSignedCollarSource)
  (hI : d.target ⊆ W.interior)
  (heq : ∀ z s, d (z, s) = E.boundedSplitTubeMap h hlin (z.down, s))
  (hc : E.toTorus.components.count = 2) (hn : E.toTorus.pairing.count = 1)
  {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
  (havρ : ∀ r, Disjoint ((E.toTorus.external.shrink hρ hρ1).collar r).target d.target)

abbrev plugComponentCapCarrier (i : Fin 2) : CompactCarrier.{u} :=
  GC.Topology.componentCarrier (E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapCarrier
    (E.fibrePlugCapComponents h hlin hc hn d hs heq hρ hρ1 hI havρ) i

abbrev plugCapAmbientChart (i : Fin 2) :=
  boundedPlugCapBallChart d hs hI (E.toTorus.external.shrink hρ hρ1)
    (E.toTorus.external_exhausted.trans (E.toTorus.external.shrink_image hρ hρ1).symm)
    havρ E h hlin heq i

include heq hc hn in
theorem plugCapAmbientChart_target_owned (i : Fin 2) :
    (E.plugCapAmbientChart h hlin d hs hI heq hρ hρ1 havρ i).target ⊆
      (E.fibrePlugCapComponents h hlin hc hn d hs heq hρ hρ1 hI havρ).piece i := by
  let P := E.plugCapAmbientChart h hlin d hs hI heq hρ hρ1 havρ i
  let D := E.fibrePlugCapComponents h hlin hc hn d hs heq hρ hρ1 hI havρ
  have hsrc : P.source = Metric.ball 0 (5 / 2) :=
    boundedPlugCapBallChart_source _ _ _ _ _ _ _ _ _ _ _
  have hzero : (0 : EuclideanSpace ℝ (Fin 3)) ∈ P.source := by rw [hsrc]; simp
  have hcap : P 0 ∈ D.piece i := by
    have himg : P 0 ∈ P '' Metric.closedBall 0 1 := ⟨0, by simp, rfl⟩
    rw [boundedPlugCapBallChart_closedUnit_image] at himg
    obtain ⟨x, hx⟩ := himg
    rw [← hx]
    exact E.fibrePlugCapComponents_cap_owned h hlin hc hn d hs heq hρ hρ1 hI havρ i x
  rw [← P.toPartialEquiv.image_source_eq_target]
  have hconn : IsPreconnected (P '' P.source) := by
    apply IsPreconnected.image _ P P.contMDiffOn.continuousOn
    rw [hsrc]
    exact (convex_ball (0 : EuclideanSpace ℝ (Fin 3)) (5 / 2)).isPreconnected
  exact hconn.subset_isClopen ⟨D.closed i, (D.piece i).isOpen⟩
    ⟨P 0, ⟨0, hzero, rfl⟩, hcap⟩

def plugComponentCapChart (i : Fin 2) :
    PartialDiffeomorph (𝓡 3)
      (E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ i).model
      (EuclideanSpace ℝ (Fin 3))
      (E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ i).Carrier ∞ :=
  codRestrictOpens (E.plugCapAmbientChart h hlin d hs hI heq hρ hρ1 havρ i)
    ((E.fibrePlugCapComponents h hlin hc hn d hs heq hρ hρ1 hI havρ).piece i)
    (by
      let := (E.fibrePlugCapComponents h hlin hc hn d hs heq hρ hρ1 hI havρ).connected i
      exact inferInstance)

theorem plugComponentCapChart_source (i : Fin 2) :
    (E.plugComponentCapChart h hlin d hs hI heq hc hn hρ hρ1 havρ i).source =
      Metric.ball 0 (5 / 2) := by
  rw [plugComponentCapChart, codRestrictOpens_source]
  · exact boundedPlugCapBallChart_source _ _ _ _ _ _ _ _ _ _ _
  · exact E.plugCapAmbientChart_target_owned h hlin d hs hI heq hc hn hρ hρ1 havρ i

theorem plugComponentCapChart_apply (i : Fin 2) (x : EuclideanSpace ℝ (Fin 3))
    (hx : x ∈ Metric.ball 0 (5 / 2)) :
    (E.plugComponentCapChart h hlin d hs hI heq hc hn hρ hρ1 havρ i x).val =
      E.plugCapAmbientChart h hlin d hs hI heq hρ hρ1 havρ i x := by
  change (codRestrictOpens (E.plugCapAmbientChart h hlin d hs hI heq hρ hρ1 havρ i)
    ((E.fibrePlugCapComponents h hlin hc hn d hs heq hρ hρ1 hI havρ).piece i) _ x).val = _
  refine codRestrictOpens_apply (I := 𝓡 3)
    (J := (E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapCarrier.model) _ _ _ ?_
  apply E.plugCapAmbientChart_target_owned h hlin d hs hI heq hc hn hρ hρ1 havρ i
  apply (E.plugCapAmbientChart h hlin d hs hI heq hρ hρ1 havρ i).map_source
  exact (boundedPlugCapBallChart_source _ _ _ _ _ _ _ _ _ _ _).symm.subset hx

theorem plugComponentCapChart_image (i : Fin 2) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (hA : A ⊆ Metric.ball 0 (5 / 2)) :
    Subtype.val '' (E.plugComponentCapChart h hlin d hs hI heq hc hn hρ hρ1 havρ i '' A) =
      E.plugCapAmbientChart h hlin d hs hI heq hρ hρ1 havρ i '' A := by
  ext y
  constructor
  · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx,
      (E.plugComponentCapChart_apply h hlin d hs hI heq hc hn hρ hρ1 havρ i x (hA hx)).symm⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨_, ⟨x, hx, rfl⟩,
      E.plugComponentCapChart_apply h hlin d hs hI heq hc hn hρ hρ1 havρ i x (hA hx)⟩

theorem plugComponentCapChart_closedUnit_image (i : Fin 2) :
    Subtype.val '' (E.plugComponentCapChart h hlin d hs hI heq hc hn hρ hρ1 havρ i ''
      Metric.closedBall 0 1) =
      range ((E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapReparameterizedCap i) := by
  rw [E.plugComponentCapChart_image h hlin d hs hI heq hc hn hρ hρ1 havρ i]
  · exact boundedPlugCapBallChart_closedUnit_image _ _ _ _ _ _ _ _ _ _ _
  · intro x hx
    rw [mem_ball_zero_iff]
    have hnorm := mem_closedBall_zero_iff.mp hx
    linarith

theorem plugComponentCapChart_openUnit_image (i : Fin 2) :
    Subtype.val '' (E.plugComponentCapChart h hlin d hs hI heq hc hn hρ hρ1 havρ i ''
      Metric.ball 0 1) =
      (E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapReparameterizedCap i ''
        {x : ClosedCell 3 | ‖x.val‖ < 1} := by
  rw [E.plugComponentCapChart_image h hlin d hs hI heq hc hn hρ hρ1 havρ i]
  · exact boundedPlugCapBallChart_openUnit_image _ _ _ _ _ _ _ _ _ _ _
  · exact Metric.ball_subset_ball (by norm_num)

theorem plugComponentCapChart_boundary (i : Fin 2) (z : ClosureSphere.{u}) :
    (E.plugComponentCapChart h hlin d hs hI heq hc hn hρ hρ1 havρ i z.down.val).val =
      (E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapCore
        ((E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereMap i
          ((E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapOrientationData.attaching
            i z)) := by
  rw [E.plugComponentCapChart_apply h hlin d hs hI heq hc hn hρ hρ1 havρ i]
  · exact boundedPlugCapBallChart_boundary _ _ _ _ _ _ _ _ _ _ _ _
  · rw [mem_ball_zero_iff]
    have hz : ‖z.down.val‖ = 1 := by simp
    rw [hz]
    norm_num

theorem plugComponentCapChart_mfderiv (i : Fin 2) (x : EuclideanSpace ℝ (Fin 3))
    (hx : x ∈ Metric.ball 0 (5 / 2)) :
    mfderiv (𝓡 3)
      (E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ i).model
      (E.plugComponentCapChart h hlin d hs hI heq hc hn hρ hρ1 havρ i) x =
    mfderiv (𝓡 3) (E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapCarrier.model
      (E.plugCapAmbientChart h hlin d hs hI heq hρ hρ1 havρ i) x := by
  let B := E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ
  let U := (E.fibrePlugCapComponents h hlin hc hn d hs heq hρ hρ1 hI havρ).piece i
  let p : PartialDiffeomorph (𝓡 3) B.sphereCapCarrier.model
      (EuclideanSpace ℝ (Fin 3)) U ∞ :=
    E.plugComponentCapChart h hlin d hs hI heq hc hn hρ hρ1 havρ i
  change mfderiv (𝓡 3) B.sphereCapCarrier.model p x = _
  rw [← DifferentialGeometry.mfderiv_subtypeVal_comp (I := 𝓡 3)
    (J := B.sphereCapCarrier.model) p x]
  apply Filter.EventuallyEq.mfderiv_eq
  filter_upwards [Metric.isOpen_ball.mem_nhds hx] with y hy
  exact E.plugComponentCapChart_apply h hlin d hs hI heq hc hn hρ hρ1 havρ i y hy

theorem plugComponentCapChart_positive (i : Fin 2) (x : EuclideanSpace ℝ (Fin 3))
    (hx : x ∈ (E.plugComponentCapChart h hlin d hs hI heq hc hn hρ hρ1 havρ i).source) :
    Orientation.map (Fin 3)
      (carrierSurgeryPatchTangentEquiv
        (E.plugComponentCapChart h hlin d hs hI heq hc hn hρ hρ1 havρ i) hx)
      sphereCapEuclideanOrientation =
        (E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ i).orientation.orientation
          (E.plugComponentCapChart h hlin d hs hI heq hc hn hρ hρ1 havρ i x) := by
  have hball : x ∈ Metric.ball 0 (5 / 2) :=
    (E.plugComponentCapChart_source h hlin d hs hI heq hc hn hρ hρ1 havρ i).subset hx
  have hsrc : x ∈ (E.plugCapAmbientChart h hlin d hs hI heq hρ hρ1 havρ i).source :=
    (boundedPlugCapBallChart_source _ _ _ _ _ _ _ _ _ _ _).symm.subset hball
  have he : carrierSurgeryPatchTangentEquiv
      (E.plugComponentCapChart h hlin d hs hI heq hc hn hρ hρ1 havρ i) hx =
      carrierSurgeryPatchTangentEquiv
        (E.plugCapAmbientChart h hlin d hs hI heq hρ hρ1 havρ i) hsrc := by
    apply LinearEquiv.ext
    intro v
    exact congrArg (fun L => L v)
      (E.plugComponentCapChart_mfderiv h hlin d hs hI heq hc hn hρ hρ1 havρ i x hball)
  rw [he]
  change _ = (E.fibrePlugCutBoundary d hs hρ hρ1 hI havρ).sphereCapCarrier.orientation.orientation _
  rw [E.plugComponentCapChart_apply h hlin d hs hI heq hc hn hρ hρ1 havρ i x hball]
  exact boundedPlugCapBallChart_positive _ _ _ _ _ _ _ _ _ _ _ _ hsrc

def plugComponentCapBallChart (i : Fin 2) :
    BallChart 3 (E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ i).model
      (E.plugComponentCapCarrier h hlin d hs hI heq hc hn hρ hρ1 havρ i).Carrier where
  chart := E.plugComponentCapChart h hlin d hs hI heq hc hn hρ hρ1 havρ i
  closedBall_subset_source := by
    intro x hx
    apply (E.plugComponentCapChart_source h hlin d hs hI heq hc hn hρ hρ1 havρ i).symm.subset
    rw [mem_ball_zero_iff]
    have hnorm := mem_closedBall_zero_iff.mp hx
    linarith

end GC.Seifert.ElementaryPresentation
