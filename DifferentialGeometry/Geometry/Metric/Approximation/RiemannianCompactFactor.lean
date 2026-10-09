import DifferentialGeometry.Geometry.Metric.Approximation.RiemannianSequence
import DifferentialGeometry.Geometry.Metric.Approximation.BoundedDiameterLimit

/-! Actual Riemannian pointed limits retain compact uniformly bounded rank-one factors. -/

set_option autoImplicit false

open Set Metric Filter
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

namespace DifferentialGeometry.CheegerGromovCompactness

universe u uE uH uZ

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem PointedRiemannianSeq.exists_compact_factor_limit_of_sectional_lower_bound
    (X : PointedRiemannianSeq.{u, uE, uH} I)
    (hcomplete : ∀ i, MetricComplete (X.obj i))
    (hconn : ∀ i, ConnectedSpace (X.obj i).M)
    {κ ρ δ : ℕ → ℝ} {D : ℝ}
    (hκ : ∀ i, 0 ≤ κ i) (hκzero : Tendsto κ atTop (𝓝 0)) (hρ : Tendsto ρ atTop atTop)
    (hsec : ∀ i, ∀ y ∈ riemannianBallOf (X.obj i).metric (X.obj i).basepoint (ρ i),
      SectionalBoundedBelowAt (X.obj i).metric y (-κ i))
    {Z : ℕ → Type uZ} [∀ i, MetricSpace (Z i)] (b : ∀ i, Z i)
    (f : let : ∀ i, MetricSpace (X.obj i).M := fun i =>
      (properMetricOn (X.obj i) (hcomplete i) (hconn i)).alignedMetricSpace (X.obj i)
      ∀ i, KleinerLottApprox (X.obj i).basepoint (WithLp.toLp 2 ((0 : ℝ), b i)) (δ i))
    (hδ : Tendsto δ atTop (𝓝 0)) (hD : ∀ i, ∀ x y : Z i, dist x y ≤ D) :
    let : ∀ i, MetricSpace (X.obj i).M := fun i =>
      (properMetricOn (X.obj i) (hcomplete i) (hconn i)).alignedMetricSpace (X.obj i)
    ∃ (Y W : Type) (mY : MetricSpace Y) (mW : MetricSpace W), letI := mY; letI := mW
      ∃ (q : Y) (w : W) (φ : ℕ → ℕ), StrictMono φ ∧ CompleteSpace Y ∧ ProperSpace Y ∧
        CompleteSpace W ∧ ProperSpace W ∧ CompactSpace W ∧ (∀ x y : W, dist x y ≤ D) ∧
        PointedGHConverges (fun i => (X.obj (φ i)).basepoint) q ∧
        PointedGHConverges (fun i => b (φ i)) w ∧
        dimH (univ : Set Y) ≤ Module.finrank ℝ E ∧ fourPointComparison 0 (univ : Set Y) ∧
        ∃ e : Y ≃ᵢ WithLp 2 (ℝ × W), e q = WithLp.toLp 2 ((0 : ℝ), w) := by
  let : ∀ i, MetricSpace (X.obj i).M := fun i =>
    (properMetricOn (X.obj i) (hcomplete i) (hconn i)).alignedMetricSpace (X.obj i)
  obtain ⟨Y, mY, q, φ, hφ, hcY, hpY, hX, hdim, hfour, -⟩ :=
    X.exists_pointed_limit_of_sectional_lower_bound hcomplete hconn hκ hκzero hρ hsec
  let := mY
  let := hpY
  obtain ⟨W, mW, w, ψ, hψ, hpW, hcW, hcompact, hbound, hZ, hX', e, he⟩ :=
    hX.exists_compact_factor_of_approximate_products (fun i => f (φ i))
      (hδ.comp hφ.tendsto_atTop) (fun i => hD (φ i))
  let := mW
  exact ⟨Y, W, mY, mW, q, w, φ ∘ ψ, hφ.comp hψ, hcY, hpY, hcW, hpW,
    hcompact, hbound, hX', hZ, hdim, hfour, e, he⟩

end DifferentialGeometry.CheegerGromovCompactness
