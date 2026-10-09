import DifferentialGeometry.Geometry.Collapse.Parameters
import DifferentialGeometry.Geometry.Collapse.CurvatureScale
import DifferentialGeometry.Geometry.Hyperbolic.Cusp
import DifferentialGeometry.Geometry.Metric.Pullback.Local

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Tensor.RSTensor
open GC.Endpoint Bundle
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.Geometry.Collapse
universe u

def cuspMetricError {W : CompactCarrier.{u}}
    (g : SmoothRiemannianMetric W.model W.Carrier) (H : HyperbolicCusp)
    (f : CuspHalfSpace → W.Carrier) (p : CuspHalfSpace) :
    Tensor0SSpace 2 halfCollarModel p :=
  ((continuousMultilinearCurryFin1 ℝ (TangentSpace halfCollarModel p) ℝ).symm.toContinuousLinearMap.comp
    (localPullInner g f p - H.metric.inner p)).uncurryLeft

def cuspMetricErrorBound {W : CompactCarrier.{u}}
    (g : SmoothRiemannianMetric W.model W.Carrier) (K : ℕ) (δ : ℝ)
    (H : HyperbolicCusp) (f : CuspHalfSpace → W.Carrier) : Prop :=
  ∀ k : ℕ, k ≤ K → ∀ p ∈ cuspDomain,
    tensor0SFiberNorm H.metric p (2 + k)
      (iteratedMetricCovariantDerivative H.metric 2 (cuspMetricError g H f) k p) ≤ δ

structure CuspEmbedding (W : CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier) (K : ℕ) (δ : ℝ)
    (X : Set W.Carrier) where
  cusp : HyperbolicCusp
  toFun : CuspHalfSpace → W.Carrier
  contMDiffOn : ContMDiffOn halfCollarModel W.model (K + 1) toFun cuspDomain
  isEmbedding : _root_.Topology.IsEmbedding (fun p : cuspDomain => toFun p)
  immersion : ∀ p ∈ cuspDomain,
    Function.Injective (mfderiv halfCollarModel W.model toFun p)
  boundary_image : Set.range (fun t : Torus => toFun (t, halfZero)) = X
  boundary_preimage : ∀ {p}, p ∈ cuspDomain →
    (toFun p ∈ W.model.boundary W.Carrier ↔ p.2.val 0 = 0)
  metric_error : cuspMetricErrorBound g K δ cusp toFun

structure NearlyCuspidalBoundary (W : CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier) (K : ℕ) (δ : ℝ) where
  count : ℕ
  count_pos : 0 < count
  component : Fin count → Set W.Carrier
  connected : ∀ i, IsConnected (component i)
  closed : ∀ i, IsClosed (component i)
  disjoint : Pairwise (fun i j => Disjoint (component i) (component j))
  covers : ⋃ i, component i = W.model.boundary W.Carrier
  diameter : ∀ i, ∀ x ∈ component i, ∀ y ∈ component i,
    riemannianEDistOf g x y ≤ ENNReal.ofReal δ
  collar : ∀ i, CuspEmbedding W g K δ (component i)

def distanceToBoundary (W : CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier) (p : W.Carrier) : ℝ≥0∞ :=
  ⨅ q : W.model.boundary W.Carrier, riemannianEDistOf g p q

def boundaryVolumeCollapsed (W : CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier) (w : ℝ) : Prop :=
  ∀ p, ENNReal.ofReal boundaryBufferDistance < distanceToBoundary W g p → volumeCollapsedAtCurvatureScale g w p

def CuspEmbedding.weaken {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ₁ δ₂ : ℝ}
    {X : Set W.Carrier} (e : CuspEmbedding W g K δ₁ X) (hδ : δ₁ ≤ δ₂) :
    CuspEmbedding W g K δ₂ X :=
  { e with metric_error := fun k hk p hp => (e.metric_error k hk p hp).trans hδ }

def NearlyCuspidalBoundary.weaken {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ₁ δ₂ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ₁) (hδ : δ₁ ≤ δ₂) :
    NearlyCuspidalBoundary W g K δ₂ :=
  { B with
    diameter := fun i x hx y hy => (B.diameter i x hx y hy).trans (ENNReal.ofReal_le_ofReal hδ)
    collar := fun i => (B.collar i).weaken hδ }

theorem distanceToBoundary_eq_top_of_boundary_empty (W : CompactCarrier.{u}) (g : SmoothRiemannianMetric W.model W.Carrier)
    (h : W.model.boundary W.Carrier = ∅) (p : W.Carrier) :
    distanceToBoundary W g p = ⊤ := by
  unfold distanceToBoundary
  have : IsEmpty (W.model.boundary W.Carrier) := by
    rw [h]
    exact Set.isEmpty_coe_sort.mpr rfl
  exact iInf_of_empty _


def CuspEmbedding.restrictOrder {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K K' : ℕ} {δ : ℝ}
    {X : Set W.Carrier} (e : CuspEmbedding W g K δ X) (hK : K' ≤ K) :
    CuspEmbedding W g K' δ X :=
  { e with
    contMDiffOn := e.contMDiffOn.of_le (by exact_mod_cast Nat.add_le_add_right hK 1)
    metric_error := fun k hk p hp => e.metric_error k (hk.trans hK) p hp }

def NearlyCuspidalBoundary.restrictOrder {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K K' : ℕ} {δ : ℝ}
    (B : NearlyCuspidalBoundary W g K δ) (hK : K' ≤ K) :
    NearlyCuspidalBoundary W g K' δ :=
  { B with collar := fun i => (B.collar i).restrictOrder hK }

end DifferentialGeometry.Geometry.Collapse
