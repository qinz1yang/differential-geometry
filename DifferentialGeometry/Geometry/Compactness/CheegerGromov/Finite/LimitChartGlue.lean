import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.FiniteMetricCompactness
import DifferentialGeometry.Geometry.Metric.Approximation.MarkedPointEvaluation
import DifferentialGeometry.Geometry.Metric.Approximation.PerturbApproximation
import DifferentialGeometry.Topology.Manifold.SmoothCarrier.Basic

/-!
# Glue between aligned manifolds and D's pointed Riemannian manifolds (LFR14, lane L-BIND)

The finite-regularity compactness theorems ported from the team branch (`Limit/SmoothCarrier.lean`,
`Limit/FiniteMetricCompactness.lean`) take a sequence of `PointedRiemannianManifold`s and measure
distances with the Riemannian metric space `HopfRinow.riemMetricSpace`. Chapter 13 works with the
aligned block: a manifold `M` with its own `MetricSpace` whose distance is the `g`-length distance
(`hmetric`). This file supplies the glue.

* `metricComplete_aligned`: the aligned pointed manifold `{ M := M, basepoint := p, metric := g }`
  is `MetricComplete` when `M` is complete.
* `riemMetricSpace_aligned_eq`: on an aligned connected manifold the Riemannian metric space
  structure IS the given one.
* `pointedGHConverges_of_metricSpace_eq`, `exists_pointedBallApprox_of_metricSpace_eq`: pointed
  Gromov–Hausdorff convergence and pointed ball approximations do not change when the metric space
  instances of the sources are replaced by equal ones (the marked-point evaluation is unchanged).
* `smoothCarrierOfBaseIsometryEquiv`, `extendToWholeSpace_mapTargetIsometry`: post-composition of
  a pointed ball approximation with the basepoint-preserving surjective isometry
  `ofBase : X ≃ᵢ SmoothCarrier 𝒜` (`PointedBallApprox.mapTargetIsometry`), and its marked-point
  evaluation.

The metric alignment is done in two steps, on instances and never by rewriting distances under
mixed instances: first the Riemannian extended metric and its completeness
(`metricComplete_aligned`, through `PseudoEMetricSpace.ext` and `hmetric`), then the finite
distance structure (`riemMetricSpace_aligned_eq`, through `MetricSpace.ext`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.CheegerGromovCompactness

open GC.MetricGeometry

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u v

section Transfer

variable {Y : Type v} [MetricSpace Y]

/-- Pointed Gromov–Hausdorff convergence only depends on the metric space instances of the
sources up to equality. -/
theorem pointedGHConverges_of_metricSpace_eq {X : ℕ → Type u} {m m' : ∀ i, MetricSpace (X i)}
    (h : ∀ i, m i = m' i) {p : ∀ i, X i} {q : Y}
    (hpq : @PointedGHConverges X m Y _ p q) : @PointedGHConverges X m' Y _ p q := by
  obtain rfl : m = m' := funext h
  exact hpq

/-- Subsequences of a pointed Gromov–Hausdorff convergent sequence converge, also after the metric
space instances of the sources are replaced by equal ones (all instances are passed explicitly, so
no instance is synthesized). -/
theorem pointedGHConverges_comp_of_metricSpace_eq {X : ℕ → Type u}
    {m m' : ∀ i, MetricSpace (X i)} (h : ∀ i, m i = m' i) {p : ∀ i, X i} {q : Y} {θ : ℕ → ℕ}
    (hθ : StrictMono θ) (hpq : @PointedGHConverges X m Y _ p q) :
    @PointedGHConverges (fun i => X (θ i)) (fun i => m' (θ i)) Y _ (fun i => p (θ i)) q := by
  obtain rfl : m = m' := funext h
  exact hpq.subsequence hθ

/-- A pointed ball approximation for one metric space instance of the source is one for any equal
instance, with the same marked-point evaluation. -/
theorem exists_pointedBallApprox_of_metricSpace_eq {Z : Type u} {m m' : MetricSpace Z}
    (h : m = m') {p : Z} {q : Y} {R ε : ℝ} (F : @PointedBallApprox Z Y m _ p q R ε) :
    ∃ F' : @PointedBallApprox Z Y m' _ p q R ε,
      @PointedBallApprox.extendToWholeSpace Z Y m' _ p q R ε F' =
        @PointedBallApprox.extendToWholeSpace Z Y m _ p q R ε F := by
  subst h
  exact ⟨F, rfl⟩

/-- Distances agree for equal metric space instances. -/
theorem dist_eq_of_metricSpace_eq {Z : Type u} {m m' : MetricSpace Z} (h : m = m') (x y : Z) :
    @dist Z m.toDist x y = @dist Z m'.toDist x y := by
  subst h
  rfl

/-- Closed balls agree for equal metric space instances. -/
theorem closedBall_eq_of_metricSpace_eq {Z : Type u} {m m' : MetricSpace Z} (h : m = m') (x : Z)
    (r : ℝ) :
    @Metric.closedBall Z m.toPseudoMetricSpace x r =
      @Metric.closedBall Z m'.toPseudoMetricSpace x r := by
  subst h
  rfl

/-- The marked-point evaluation of a pointed ball approximation post-composed with an isometry
equivalence is the post-composition of its marked-point evaluation. -/
theorem extendToWholeSpace_mapTargetIsometry {Z : Type u} [MetricSpace Z] {W : Type*}
    [MetricSpace W] {p : Z} {q : Y} {R ε : ℝ} (F : PointedBallApprox p q R ε) (e : Y ≃ᵢ W)
    (x : Z) : (F.mapTargetIsometry e).extendToWholeSpace x = e (F.extendToWholeSpace x) := by
  by_cases hx : dist x p ≤ R
  · rw [PointedBallApprox.extendToWholeSpace_apply _ x hx,
      PointedBallApprox.extendToWholeSpace_apply _ x hx]
    rfl
  · simp [PointedBallApprox.extendToWholeSpace, hx]

/-- Uniform convergence of `x ↦ A i (Φ' i x)` transfers to `x ↦ B i (Φ' i x)` when `A i = B i`
for every `i` (used to replace a marked-point evaluation by an equal one). -/
theorem tendstoUniformly_comp_congr {α β : Type*} [UniformSpace β] {Z : ℕ → Type*}
    (A B : ∀ i, Z i → β) (hAB : ∀ i, A i = B i) (Φ' : ∀ i, α → Z i) {G : α → β}
    {l : Filter ℕ} (h : TendstoUniformly (fun i x => A i (Φ' i x)) G l) :
    TendstoUniformly (fun i x => B i (Φ' i x)) G l := by
  obtain rfl : A = B := funext hAB
  exact h

end Transfer

section Carrier

open DifferentialGeometry.Topology.Manifold

variable {E X ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MetricSpace X]

/-- `ofBase : X → SmoothCarrier 𝒜` as an isometry equivalence (surjective isometry). -/
def smoothCarrierOfBaseIsometryEquiv (𝒜 : SmoothCompatibleAtlas E X ι) : X ≃ᵢ SmoothCarrier 𝒜 where
  toEquiv := (SmoothCarrier.equivBase 𝒜).symm
  isometry_toFun := fun _ _ => rfl

theorem coe_smoothCarrierOfBaseIsometryEquiv (𝒜 : SmoothCompatibleAtlas E X ι) :
    ⇑(smoothCarrierOfBaseIsometryEquiv 𝒜) = SmoothCarrier.ofBase 𝒜 :=
  rfl

end Carrier

section Aligned

variable {n : ℕ} {M : Type u} [MetricSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M] [SigmaCompactSpace M]
  [T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M)]

/-- The aligned pointed manifold `(M, g, p)` of a complete aligned manifold is `MetricComplete`. -/
theorem metricComplete_aligned [CompleteSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M)
    (hmetric : ∀ a b : M, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) (p : M) :
    MetricComplete ({ M := M, basepoint := p, metric := g } :
      PointedRiemannianManifold.{u} 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) := by
  let P : PointedRiemannianManifold.{u} 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) :=
    { M := M, basepoint := p, metric := g }
  have hem : (P.emetricSpace (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))).toPseudoEMetricSpace =
      (inferInstance : PseudoEMetricSpace M) := by
    apply PseudoEMetricSpace.ext
    ext x y
    change riemannianEDistOf g x y = edist x y
    rw [hmetric, edist_dist]
  have hU := congrArg (fun m : PseudoEMetricSpace M => m.toUniformSpace) hem
  change @CompleteSpace M (P.emetricSpace (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))).toUniformSpace
  rw [show (P.emetricSpace (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))).toUniformSpace =
    (inferInstance : PseudoEMetricSpace M).toUniformSpace from hU]
  infer_instance

omit [SigmaCompactSpace M] [T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M)] in
/-- On an aligned connected manifold, the Riemannian metric space structure of `g` is the given
metric space structure. -/
theorem riemMetricSpace_aligned_eq [ConnectedSpace M]
    (g : SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M)
    (hmetric : ∀ a b : M, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)) :
    letI : RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
      ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
        (fun x : M => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
      ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
    Geometry.Riemannian.HopfRinow.riemMetricSpace (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
      (M := M) = ‹MetricSpace M› := by
  let _ : RiemannianBundle (fun x : M => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
    ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (fun x : M => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  apply MetricSpace.ext
  ext x y
  rw [Geometry.Riemannian.HopfRinow.riemMetric_dist_eq (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) x y]
  change (riemannianEDistOf g x y).toReal = dist x y
  rw [hmetric, ENNReal.toReal_ofReal dist_nonneg]

end Aligned

end DifferentialGeometry.CheegerGromovCompactness
