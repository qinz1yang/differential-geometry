import DifferentialGeometry.Geometry.Thurston.HyperbolicPrime
import DifferentialGeometry.Topology.Covering.DeckGroup
import Mathlib.Analysis.Convex.Contractible

/-!
# The exponential cover of a hyperbolic manifold without boundary

Tier T2 of lane BHD (`handoffs/20261004-design-bhd-relative-hyperbolic-pieces.md`, §1). K18's
closed wrappers are restated for an arbitrary connected, Hausdorff, σ-compact `3`-manifold `N`
without boundary, such as the interior of a compact piece with its interior atlas:

* `inner_riemannOp_le_zero_of_hyperbolic'`: a hyperbolic structure has `⟪R(v, Y) Y, v⟫ ≤ 0`;
* `exists_isCoveringMap_of_hyperbolic'`: the framed exponential map at a point is a surjective
  covering `ℝ³ → N` and a local diffeomorphism (Cartan–Hadamard,
  `framedExpMap_isCoveringMap_of_nonpos`); no closedness is used.

For such a cover `p` the deck group `coveringDeckGroup p` acts properly discontinuously, its
quotient map is `p` (`isQuotientCoveringMap_coveringDeckGroup`), and π₁ of `N` at any point is
anti-isomorphic to it by monodromy (`IsQuotientCoveringMap.fundamentalGroupEquiv`), hence
isomorphic to it (`fundamentalGroupEquivDeck'`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Bundle
open scoped Manifold ContDiff Topology

namespace GC.Geometry.HyperbolicPiece

open DifferentialGeometry

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {N : Type*} [TopologicalSpace N] [ChartedSpace E3 N] [IsManifold (𝓡 3) ∞ N]
  [T2Space N] [SigmaCompactSpace N]

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection in
theorem inner_riemannOp_le_zero_of_hyperbolic' (g : GeometricStructure (𝓡 3) N)
    (hg : g.model = .hyperbolic) (x : N) (v Y : TangentSpace (𝓡 3) x) :
    g.metric.inner x (riemannOp (LeviCivita (I := 𝓡 3) g.metric) x v Y Y) v ≤ 0 := by
  have hA : HasThurstonAtlas g.metric .hyperbolic := hg ▸ g.atlas
  have hsec := hasConstantSectionalCurvature_of_hasThurstonAtlas_hyperbolic hA
  rw [riemannOp_eq_smul_of_hasConstantSectionalCurvature hsec x v Y Y]
  simp only [map_smul, map_sub, smul_apply, sub_apply, smul_eq_mul]
  have hcs := SmoothRiemannianMetric.metric_inner_cauchy_schwarz_sq g.metric x v Y
  rw [g.metric.symm x Y v]
  nlinarith

open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_isCoveringMap_of_hyperbolic' [ConnectedSpace N] [Nonempty N]
    (g : GeometricStructure (𝓡 3) N) (hg : g.model = .hyperbolic) :
    ∃ p : E3 → N, IsCoveringMap p ∧ Function.Surjective p ∧
      IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ p := by
  let : IsManifold (𝓡 3) 1 N :=
    IsManifold.of_le (I := 𝓡 3) (M := N) (n := (∞ : WithTop ℕ∞)) (by decide)
  let : TopologicalSpace.MetrizableSpace N := Manifold.metrizableSpace (𝓡 3) N
  let : T3Space N := inferInstance
  let : RiemannianBundle (fun x : N => TangentSpace (𝓡 3) x) :=
    ⟨g.metric.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E3 (fun x : N => TangentSpace (𝓡 3) x) :=
    ⟨⟨g.metric.inner, g.metric.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace N := EMetricSpace.ofRiemannianMetric (𝓡 3) N
  let : CompleteSpace N := g.complete.complete
  have hEg : IsMetricNorm (I := 𝓡 3) (M := N) g.metric := fun z v =>
    tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := 𝓡 3) g.metric z v
  have hR := inner_riemannOp_le_zero_of_hyperbolic' g hg
  obtain ⟨x₀⟩ := (inferInstance : Nonempty N)
  exact ⟨_, framedExpMap_isCoveringMap_of_nonpos g.metric hEg x₀ hR,
    framedExpMap_surjective g.metric hEg x₀,
    framedExpMap_isLocalDiffeomorph_of_nonpos g.metric hEg x₀ hR⟩

end GC.Geometry.HyperbolicPiece

namespace GC.Geometry.HyperbolicPiece

open DifferentialGeometry

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {N : Type*} [TopologicalSpace N] {p : E3 → N}

theorem isQuotientCoveringMap_deck (hp : IsCoveringMap p) (hsurj : Function.Surjective p) :
    IsQuotientCoveringMap p (coveringDeckGroup p) :=
  isQuotientCoveringMap_coveringDeckGroup hp hsurj

theorem properlyDiscontinuousSMul_deck [T2Space N] (hp : IsCoveringMap p)
    (hsurj : Function.Surjective p) :
    ProperlyDiscontinuousSMul (coveringDeckGroup p) E3 :=
  coveringDeckGroup_properlyDiscontinuousSMul hp hsurj

def fundamentalGroupEquivDeck' (hp : IsCoveringMap p) (hsurj : Function.Surjective p) {x : N}
    (e : p ⁻¹' {x}) : FundamentalGroup N x ≃* coveringDeckGroup p :=
  ((isQuotientCoveringMap_deck hp hsurj).fundamentalGroupEquiv e).trans
    (MulEquiv.inv' (coveringDeckGroup p)).symm

theorem fundamentalGroupEquivDeck'_smul (hp : IsCoveringMap p) (hsurj : Function.Surjective p)
    {x : N} (e : p ⁻¹' {x}) (γ : FundamentalGroup N x) :
    (fundamentalGroupEquivDeck' hp hsurj e γ)⁻¹ • (e : E3) = hp.monodromy γ e := by
  have h := (isQuotientCoveringMap_deck hp hsurj).unop_fundamentalGroupToMulOpposite_smul
    (e := e) (γ := γ)
  simp only [fundamentalGroupEquivDeck', MulEquiv.trans_apply, MulEquiv.inv'_symm_apply]
  exact h

end GC.Geometry.HyperbolicPiece
