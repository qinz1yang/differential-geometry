import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSlimLoopExits74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SlimPiecesOfExits74

/-!
# Consumer of `slim_loop_exit74`: the slim pieces over all the loops of a domain

The exits over all loops `j` of a domain `D` assemble to a `SlimPiecesV2` (no end data are needed:
a loop has no end) as soon as the images are disjoint, which holds because the loops of `D` are
pairwise disjoint and `φ` is injective.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology GC.GraphManifold GC.Endpoint GC.GraphManifold.Assembly
open GC.GraphManifold.Assembly.FC39P0
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] LocalChartPackets.instMetricN LocalChartPackets.instChartedN
  LocalChartPackets.instMetricC

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {Kj : ℕ} {Ξ Γ S eg c cw : Fin 3 → ℝ}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) X 3} {cadj : ℝ}
  {P : LocalChartPacketsC14Z X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e
    T V vs ζ Λz oM}

/-- **The slim pieces over the loops of a domain**: one exit per loop, pairwise disjoint images,
a `SlimPiecesV2`. -/
theorem Gaf02ChainEJA.exists_slimPiecesOfLoops74
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hK : 5 ≤ K) {W : CompactCarrier.{0}} (φ : X ≃ₘ⟮𝓘(ℝ, E3), W.model⟯ W.Carrier)
    (hW : W.model.boundary W.Carrier = ∅) {n : ℕ} {E : BoundaryTori W n} {Z : ZeroDomains W}
    {Cu : CuspCores W E} (D : SmoothCompactOneDomain_BCF C.slimBs_ZSP35) :
    ∃ (Xs : Fin D.l → SlimPieceExit74 Z Cu) (hd : Pairwise fun j j' =>
      Disjoint (range (Xs j).piece.map) (range (Xs j').piece.map)),
      (slimPiecesOfExits74 Xs hd).count = D.l ∧
      ∀ j, range (Xs j).piece.map = φ '' (C.slimMap_ZSP35 ⁻¹' range (D.loop j)) := by
  choose Xs hXs using fun j => C.slim_loop_exit74 hK φ hW (Z := Z) (Cu := Cu) D j
  refine ⟨Xs, fun j j' hne => ?_, rfl, hXs⟩
  change Disjoint (range (Xs j).piece.map) (range (Xs j').piece.map)
  rw [hXs j, hXs j']
  refine disjoint_left.2 ?_
  rintro y ⟨x, hx, rfl⟩ ⟨x', hx', hxx⟩
  have := φ.injective hxx
  subst this
  exact disjoint_left.1 (D.loop_disjoint hne) hx hx'

end DifferentialGeometry.Geometry.Collapse
