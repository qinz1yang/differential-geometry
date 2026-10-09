import DifferentialGeometry.Geometry.Fibration.ActualStageChainSlimLoopCircleZSP35
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SlimPieceExit74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SlimLoopExitsOfDiffeo74

/-!
# Draft 74, S1 on the chain: the slim loop exits over the loops of any `D₃`

Lane C14-REG-CHAIN (by S-REG-CHAIN4), G36. For a chain `C` on the final family (`K ≥ 5`), the
carrier identification `φ : X ≃ₘ W` (`M.ψ`, `W` without boundary) and ANY smooth compact
one-dimensional domain `D` of the slim base, every loop `j` of `D` gives a slim piece exit
(`SlimPieceExit74.sphereLoop` / `.torusLoop`) whose piece has range `φ(f₃⁻¹(range (loop j)))`:
S-ZSP04's circle branch (`slim_loop_circle_ZSP35`, G18) is moved to `W` by
`SphereLoopExit74.ofDiffeo74` / `TorusLoopExit74.ofDiffeo74` (G33), the connectedness of the
region coming from the connected standard fibre
(`isPreconnected_of_circleSubmersion74`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Analysis
open GC.GraphManifold GC.Endpoint
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Ehresmann
open GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

/-- `ClosureSphere` is connected. -/
local instance closureSphereConnected_RLE74 : ConnectedSpace ClosureSphere.{0} :=
  have hS : ConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
    isConnected_iff_connectedSpace.mp (isConnected_sphere (by
      rw [← Module.finrank_eq_rank]; simp) 0 zero_le_one)
  Homeomorph.ulift.symm.surjective.connectedSpace Homeomorph.ulift.symm.continuous

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}

namespace Gaf02ChainEJA

variable {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- **The slim loop exit over a loop of any `D`** (S1 in `W`-form): the slim piece exit of the
loop `j` of `D` has image `φ(f₃⁻¹(range (loop j)))`. -/
theorem slim_loop_exit74
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hK : 5 ≤ K) {W : CompactCarrier.{0}} (φ : X ≃ₘ⟮𝓘(ℝ, E3), W.model⟯ W.Carrier)
    (hW : W.model.boundary W.Carrier = ∅) {n : ℕ} {E : BoundaryTori W n} {Z : ZeroDomains W}
    {Cu : CuspCores W E} (D : SmoothCompactOneDomain_BCF C.slimBs_ZSP35) (j : Fin D.l) :
    ∃ x : SlimPieceExit74 Z Cu, range x.piece.map =
      φ '' (C.slimMap_ZSP35 ⁻¹' range (D.loop j)) := by
  obtain ⟨hOo, hOc, p, hp, hsub, -, hF⟩ := C.slim_loop_circle_ZSP35 hK D j
  rcases hF with ⟨F₀, hr⟩ | ⟨F₀, hr⟩
  · have hconn := isPreconnected_of_circleSubmersion74 hOo hOc hp hsub (by
      rw [← hr]
      exact isPreconnected_range F₀.isSmoothEmbedding.contMDiff.continuous)
    exact ⟨.sphereLoop (SphereLoopExit74.ofDiffeo74 φ hW hOo hOc hconn hp hsub
      F₀.isSmoothEmbedding hr), range_sphereLoopPiece74 _⟩
  · have hconn := isPreconnected_of_circleSubmersion74 hOo hOc hp hsub (by
      rw [← hr]
      exact isPreconnected_range F₀.isSmoothEmbedding.contMDiff.continuous)
    exact ⟨.torusLoop (TorusLoopExit74.ofDiffeo74 φ hW hOo hOc hconn hp hsub
      F₀.isSmoothEmbedding hr), range_torusLoopPiece74 _⟩

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
