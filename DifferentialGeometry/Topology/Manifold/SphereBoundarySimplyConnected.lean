import DifferentialGeometry.Topology.Manifold.SphereBoundaryDomain
import DifferentialGeometry.Topology.VanKampen.SmoothSphereSeparation
import DifferentialGeometry.Topology.SphereSeparation.BicollarBandExtension
import DifferentialGeometry.Topology.Manifold.PartialChartEmbedding
import DifferentialGeometry.Topology.Embedding.Sphere
import DifferentialGeometry.Topology.OpenPartialHomeomorph.Images

noncomputable section

open Set Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp [E3]⟩

variable {M : Type*} [TopologicalSpace M] [T2Space M]
  [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M] [SimplyConnectedSpace M]

theorem simplyConnectedSpace_of_sphere_frontier
    {K : Set M} (hK : closure (interior K) = K)
    (e : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → M)
    (he : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e)
    (hfront : frontier K = range e) : SimplyConnectedSpace K := by
  have hne : (interior K).Nonempty := by
    by_contra h
    have hi : interior K = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    have hKe : K = ∅ := by simpa only [hi, closure_empty] using hK.symm
    have hf := range_nonempty e
    rw [← hfront, hKe, frontier_empty] at hf
    exact Set.not_nonempty_empty hf
  have hKclosed : IsClosed K := hK ▸ isClosed_closure
  have hconn := (isConnected_interior_and_compl_of_sphere_boundary hKclosed hne e he hfront).1
  obtain ⟨x, hx⟩ := hne
  have hxavoid : x ∈ (range e)ᶜ := by
    rw [← hfront]
    exact fun h => h.2 hx
  have hfronti : frontier (interior K) = range e := by
    rw [frontier, hK, interior_interior, ← hKclosed.frontier_eq, hfront]
  have hcomponent : connectedComponentIn (range e)ᶜ x = interior K := by
    rw [← hfronti]
    exact DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.connectedComponentIn_compl_frontier_eq
      hconn isOpen_interior hx
  have himage : Subtype.val '' connectedComponent (⟨x, hxavoid⟩ : ((range e)ᶜ : Set M)) = interior K :=
    (connectedComponentIn_eq_image hxavoid).symm.trans hcomponent
  have hsc := DifferentialGeometry.Topology.ThreeManifold.simplyConnectedSpace_closure_component_of_smoothSphereEmbedding
    he (⟨x, hxavoid⟩ : ((range e)ᶜ : Set M))
  rwa [himage, hK] at hsc

variable {Z : Type*} [TopologicalSpace Z] [T2Space Z]
  [ChartedSpace E3 Z] [IsManifold (𝓡 3) ∞ Z]

theorem simplyConnectedSpace_ball_complement_of_closed_image
    (b : PartialDiffeomorph (𝓡 3) (𝓡 3) E3 Z ∞)
    (F : PartialDiffeomorph (𝓡 3) (𝓡 3) Z M ∞)
    (hb : closedBall (0 : E3) 1 ⊆ b.source)
    (hF : (b '' ball (0 : E3) 1)ᶜ ⊆ F.source)
    (hclosed : IsClosed (F '' (b '' ball (0 : E3) 1)ᶜ)) :
    SimplyConnectedSpace ((b '' ball (0 : E3) 1)ᶜ : Set Z) := by
  let K0 := (b '' ball (0 : E3) 1)ᶜ
  let K := F '' K0
  have hopen : IsOpen (b '' ball (0 : E3) 1) :=
    b.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_ball
      (ball_subset_closedBall.trans hb)
  have hbint : interior (b '' closedBall (0 : E3) 1) = b '' ball (0 : E3) 1 := by
    have h := b.toOpenPartialHomeomorph.image_interior_of_subset_source hb
    rw [interior_closedBall _ one_ne_zero] at h
    exact h.symm
  have hreg0 : closure (interior K0) = K0 := by
    rw [interior_compl, closure_image_ball_of_partialDiffeomorph b hb,
      closure_compl, hbint]
  have hreg : closure (interior K) = K :=
    F.toOpenPartialHomeomorph.closure_interior_image_of_subset_source hF hreg0 hclosed
  let e0 : sphere (0 : E3) 1 → Z := b ∘ Subtype.val
  have he0 : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e0 :=
    DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph b
      (isSmoothEmbedding_coe_sphere (E := E3) (n := 2))
      (by rw [Subtype.range_val]; exact sphere_subset_closedBall.trans hb)
  have he0sub : range e0 ⊆ F.source := by
    change range (b ∘ Subtype.val : sphere (0 : E3) 1 → Z) ⊆ F.source
    rw [range_comp, Subtype.range_val]
    apply subset_trans ?_ hF
    rw [← frontier_image_ball_of_partialDiffeomorph b hb]
    intro x hx
    exact fun hi => hx.2 (hopen.interior_eq.symm ▸ hi)
  let e := F ∘ e0
  have he : _root_.Manifold.IsSmoothEmbedding (𝓡 2) (𝓡 3) ∞ e :=
    DifferentialGeometry.Topology.isSmoothEmbedding_comp_partialDiffeomorph F he0 he0sub
  have hfront : frontier K = range e := by
    have hf := F.toOpenPartialHomeomorph.image_frontier_of_subset_source hF
      hopen.isClosed_compl hclosed
    change F '' frontier K0 = frontier K at hf
    rw [← hf]
    change F '' frontier (b '' ball (0 : E3) 1)ᶜ =
      range (F ∘ b ∘ (Subtype.val : sphere (0 : E3) 1 → E3))
    rw [frontier_compl, frontier_image_ball_of_partialDiffeomorph b hb,
      range_comp, range_comp, Subtype.range_val]
  have hsc : SimplyConnectedSpace K := simplyConnectedSpace_of_sphere_frontier hreg e he hfront
  let H : K0 ≃ₜ K := F.toOpenPartialHomeomorph.homeomorphOfImageSubsetSource hF rfl
  exact H.toHomotopyEquiv.simplyConnectedSpace (hY := hsc)

end DifferentialGeometry.Topology.Manifold
