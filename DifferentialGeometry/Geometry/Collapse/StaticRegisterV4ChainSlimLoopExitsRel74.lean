import DifferentialGeometry.Geometry.Collapse.StaticRegisterV4ChainSlimLoopExits74

/-!
# Draft 74, S1 on the chain: the loop exit with its exact relation to `f₃` and the loop

Lane C14-REG-CHAIN (by S-REG-CHAIN5), G39 (review 78, D78-6). `slim_loop_exit74` (G36) gives a
slim piece exit over a loop of `D` with the right range. The ruling asks the binder to deliver
the exact relation of the exit's circle projection to the actual `f₃` and the chosen loop
parametrisation. `slim_loop_exit_rel74` returns the exit as `sphereLoop l` / `torusLoop l`
(`overCircle` model: the monodromy is kept, no product is asserted) with

* `l.region.O = φ(f₃⁻¹(range (loop j)))` (the whole component; connected, clopen: proved by the
  producer `isPreconnected_of_circleSubmersion74`, not assumed);
* `l.p y = exp(2π t) ↔ f₃(φ⁻¹ y) = loop j t` for every `y` of the region and every `t`
  (S-ZSP04's `p`, transported by `φ`), the smooth submersion and the standard fibre being the
  fields of `l`.
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
local instance closureSphereConnected_RLE74r : ConnectedSpace ClosureSphere.{0} :=
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

/-- **The slim loop exit over a loop of `D`, with its exact relation to `f₃` and the loop**. -/
theorem slim_loop_exit_rel74
    (C : Gaf02ChainEJA P.toLocalChartPacketsC14D.toLocalChartPacketsC14 Kj Ξ Γ S eg c cw cadj)
    (hK : 5 ≤ K) {W : CompactCarrier.{0}} (φ : X ≃ₘ⟮𝓘(ℝ, E3), W.model⟯ W.Carrier)
    (hW : W.model.boundary W.Carrier = ∅) {n : ℕ} {E : BoundaryTori W n} {Z : ZeroDomains W}
    {Cu : CuspCores W E} (D : SmoothCompactOneDomain_BCF C.slimBs_ZSP35) (j : Fin D.l) :
    ∃ x : SlimPieceExit74 Z Cu, range x.piece.map = φ '' (C.slimMap_ZSP35 ⁻¹' range (D.loop j)) ∧
      ((∃ l : SphereLoopExit74 W, x = .sphereLoop l ∧
          l.region.O = φ '' (C.slimMap_ZSP35 ⁻¹' range (D.loop j)) ∧
          ∀ y ∈ l.region.O, ∀ t : ℝ,
            l.p y = Circle.exp (2 * Real.pi * t) ↔ C.slimMap_ZSP35 (φ.symm y) = D.loop j t) ∨
        (∃ l : TorusLoopExit74 W, x = .torusLoop l ∧
          l.region.O = φ '' (C.slimMap_ZSP35 ⁻¹' range (D.loop j)) ∧
          ∀ y ∈ l.region.O, ∀ t : ℝ,
            l.p y = Circle.exp (2 * Real.pi * t) ↔ C.slimMap_ZSP35 (φ.symm y) = D.loop j t)) := by
  obtain ⟨hOo, hOc, p, hp, hsub, hrel, hF⟩ := C.slim_loop_circle_ZSP35 hK D j
  rcases hF with ⟨F₀, hr⟩ | ⟨F₀, hr⟩
  · have hconn := isPreconnected_of_circleSubmersion74 hOo hOc hp hsub (by
      rw [← hr]
      exact isPreconnected_range F₀.isSmoothEmbedding.contMDiff.continuous)
    refine ⟨.sphereLoop (SphereLoopExit74.ofDiffeo74 φ hW hOo hOc hconn hp hsub
      F₀.isSmoothEmbedding hr), range_sphereLoopPiece74 _, Or.inl ⟨_, rfl, rfl, ?_⟩⟩
    rintro y ⟨x, hx, rfl⟩ t
    change p (φ.symm (φ x)) = _ ↔ _
    rw [φ.symm_apply_apply]
    exact hrel x hx t
  · have hconn := isPreconnected_of_circleSubmersion74 hOo hOc hp hsub (by
      rw [← hr]
      exact isPreconnected_range F₀.isSmoothEmbedding.contMDiff.continuous)
    refine ⟨.torusLoop (TorusLoopExit74.ofDiffeo74 φ hW hOo hOc hconn hp hsub
      F₀.isSmoothEmbedding hr), range_torusLoopPiece74 _, Or.inr ⟨_, rfl, rfl, ?_⟩⟩
    rintro y ⟨x, hx, rfl⟩ t
    change p (φ.symm (φ x)) = _ ↔ _
    rw [φ.symm_apply_apply]
    exact hrel x hx t

end Gaf02ChainEJA

end DifferentialGeometry.Geometry.Collapse
