import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SphericalCappingBridge
import DifferentialGeometry.Topology.Handle.Manifold
import DifferentialGeometry.Topology.Manifold.ClosedBall
import DifferentialGeometry.Topology.Manifold.SmoothEmbeddingDiffeomorph

set_option autoImplicit false
noncomputable section
open Set Function Manifold
open DifferentialGeometry.Topology.Handle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

private abbrev E3 := EuclideanSpace ℝ (Fin 3)

attribute [local instance] closedCellChartedSpaceSucc closedCellIsManifold

private def ballHomeo : ThreeBall ≃ₜ DifferentialGeometry.Topology.ClosedCell 3 :=
  (closedCellBallHomeo 3).symm

@[reducible] def threeBallChartedSpace : ChartedSpace (EuclideanHalfSpace 3) ThreeBall :=
  chartedSpaceOfHomeomorph ballHomeo

attribute [local instance] threeBallChartedSpace

theorem threeBall_isManifold : IsManifold (𝓡∂ 3) ∞ ThreeBall :=
  isManifoldOfHomeomorph (𝓡∂ 3) ballHomeo

attribute [local instance] threeBall_isManifold

def threeBallDiffeomorph :
    DifferentialGeometry.Topology.ClosedCell 3 ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯ ThreeBall where
  toEquiv := ballHomeo.symm.toEquiv
  contMDiff_toFun := contMDiff_homeomorph_symm_of_chartedSpaceOfHomeomorph ballHomeo (𝓡∂ 3) ∞
  contMDiff_invFun := contMDiff_homeomorph_of_chartedSpaceOfHomeomorph ballHomeo (𝓡∂ 3) ∞

theorem threeBallDiffeomorph_apply_val (x : DifferentialGeometry.Topology.ClosedCell 3) :
    (threeBallDiffeomorph x).1 = x.1 := rfl

theorem threeBallDiffeomorph_symm_apply_val (x : ThreeBall) :
    (threeBallDiffeomorph.symm x).1 = x.1 := rfl

theorem isSmoothEmbedding_threeBall_inclusion :
    IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ (Subtype.val : ThreeBall → ThreeSpace) := by
  have h := DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_precomp
    (I := 𝓡∂ 3) (J := ThreeModel)
    (M := DifferentialGeometry.Topology.ClosedCell 3) (N := ThreeSpace) (P := ThreeBall)
    (Subtype.val : DifferentialGeometry.Topology.ClosedCell 3 → ThreeSpace)
    (DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_closedCell_inclusion 2)
    threeBallDiffeomorph.symm
  convert h using 1
  funext x
  rfl

theorem range_sphereToThreeBall :
    Set.range sphereToThreeBall = {x : ThreeBall | ‖x.1‖ = 1} := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change ‖(y : E3)‖ = 1
    simpa only [Metric.mem_sphere, dist_eq_norm, sub_zero] using y.2
  · intro hx
    change ‖(x : E3)‖ = 1 at hx
    exact ⟨⟨x.1, by simpa only [Metric.mem_sphere, dist_eq_norm, sub_zero] using hx⟩,
      Subtype.ext rfl⟩

theorem threeBall_boundary_eq_sphere :
    (𝓡∂ 3).boundary ThreeBall = Set.range sphereToThreeBall := by
  rw [range_sphereToThreeBall, ← threeBallDiffeomorph.image_boundary (by simp),
    DifferentialGeometry.Topology.Manifold.closedCell_boundary_eq_sphere 2]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    change ‖(threeBallDiffeomorph y).1‖ = 1
    rw [threeBallDiffeomorph_apply_val]
    exact hy
  · intro hx
    change ‖(x : E3)‖ = 1 at hx
    exact ⟨⟨x.1, by rw [hx]⟩, hx, Subtype.ext rfl⟩

variable {M Q : DifferentialGeometry.Topology.ClosedOrientedManifold.{u} 3}

theorem sphericalCutCap_capmap_eq (E : DifferentialGeometry.Topology.SphericalCutCapTransition M Q)
    (b : E.tubes.Boundary) :
    ⇑((E.capping.toTopological).cap b) =
      ⇑(E.capping.cap b) ∘ ⇑(threeBallDiffeomorph.symm :
        ThreeBall ≃ₘ⟮𝓡∂ 3, 𝓡∂ 3⟯
          DifferentialGeometry.Topology.ClosedCell 3) := rfl

theorem sphericalCutCap_subtype_eq (x : ThreeBall) :
    (Subtype.val : ThreeBall → ThreeSpace) x =
      (Subtype.val : DifferentialGeometry.Topology.ClosedCell 3 → ThreeSpace)
        (threeBallDiffeomorph.symm x) :=
  threeBallDiffeomorph_symm_apply_val x

theorem sphericalCutCap_cap_smooth
    (E : DifferentialGeometry.Topology.SphericalCutCapTransition M Q)
    (b : E.tubes.Boundary) :
    IsSmoothEmbedding (𝓡∂ 3) ThreeModel ∞ (⇑((E.capping.toTopological).cap b)) := by
  have h := DifferentialGeometry.Topology.Manifold.isSmoothEmbedding_diffeomorph_precomp
    (I := 𝓡∂ 3) (J := ThreeModel)
    (M := DifferentialGeometry.Topology.ClosedCell 3) (N := E.capped.Carrier) (P := ThreeBall)
    (E.capping.cap b) (E.capping.cap_embedding b) threeBallDiffeomorph.symm
  rw [sphericalCutCap_capmap_eq E b]
  exact h

variable {P : OrientedThreeStage.{u}} {a s : ℝ}

theorem OrientedThreeStage.IncomingSlab.terminalRegularRegion_eq_univ
    (G : P.IncomingSlab a s) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ t ∈ Ico a s, ∀ y : P.Carrier, G.riemannNorm t y ≤ K) :
    G.terminalRegularRegion = univ := by
  refine eq_univ_of_forall fun x =>
    ⟨univ, isOpen_univ, mem_univ x, a, ⟨le_rfl, G.lt⟩, K, hK, ?_⟩
  intro y _ t ht
  exact hb t ht y

theorem SmoothCutCapTransition.retainedTerminal_of_terminalRegularRegion_eq_univ
    {Q D N : OrientedThreeStage.{u}} {X : SmoothCutCapTransition P Q D N}
    (G : P.IncomingSlab a s) (h : G.terminalRegularRegion = univ) :
    ∀ x : X.trace.tubes.core, x ∈ X.trace.retainedCore → x.1 ∈ G.terminalRegularRegion :=
  fun _ _ => by rw [h]; exact mem_univ _

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
