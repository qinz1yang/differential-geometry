import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.ExteriorDiskFlow
import DifferentialGeometry.Geometry.Hyperbolic.FiniteVolumeModel
import DifferentialGeometry.Geometry.Collapse.CurvatureScale
import DifferentialGeometry.Geometry.Metric.Pullback.Local

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open Manifold
open scoped Manifold ContDiff ENNReal
namespace GC.LongTime
universe u


structure PersistentModelPatch {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (H : FiniteVolumeHyperbolicModel.{u}) (T : ℝ) (α : ℝ → ℝ)
    (domain : ℝ → TopologicalSpace.Opens H.Carrier)
    (f : (t : ℝ) → T ≤ t → H.Carrier → (postStage F.observation t).Carrier)
    (t₀ : ℝ) (x₀ : H.Carrier) where
  n : ℕ
  first : Fin ((F.tower.history n).eventCount + 1)
  last : Fin ((F.tower.history n).eventCount + 1)
  ordered : first ≤ last
  a : ℝ
  b : ℝ
  a_nonneg : 0 ≤ a
  before : a < t₀
  after : t₀ < b
  horizon : b ≤ (F.tower.history n).horizon
  neighborhood : TopologicalSpace.Opens H.Carrier
  mem_neighborhood : x₀ ∈ neighborhood
  in_domain : ∀ t ∈ Ioo a b, T ≤ t → (neighborhood : Set H.Carrier) ⊆ domain t
  stages : ∀ t : Icc (0 : ℝ) (F.tower.history n).horizon,
    (t : ℝ) ∈ Ioo a b → first ≤ (F.tower.history n).toHistory.activeStage t ∧
      (F.tower.history n).toHistory.activeStage t ≤ last
  map : ℝ × H.Carrier → (F.tower.history n).toHistory.backwardSurvivorDomain first last ordered
  smooth : ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) ∞ map
    (Ioo a b ×ˢ (neighborhood : Set H.Carrier))
  agrees : ∀ (t : Icc (0 : ℝ) (F.tower.history n).horizon)
    (ht : (t : ℝ) ∈ Ioo a b) (hT : T ≤ t) (x : H.Carrier), x ∈ neighborhood →
    HEq ((F.tower.history n).toHistory.backwardSurvivorMap first last ordered
      ((F.tower.history n).toHistory.activeStage t) (stages t ht).1 (stages t ht).2 (map (t, x)))
      (f t hT x)
  speed : ∀ (t : Icc (0 : ℝ) (F.tower.history n).horizon)
    (ht : (t : ℝ) ∈ Ioo a b), T ≤ t → ∀ x ∈ neighborhood,
    let history := (F.tower.history n).toHistory;
    let track := history.backwardSurvivorMap first last ordered (history.activeStage t)
      (stages t ht).1 (stages t ht).2 ∘ map;
    let v := mfderiv (𝓘(ℝ, ℝ).prod (𝓡 3)) (𝓡 3) track (t, x) (1, 0);
    (history.stageMetric (history.activeStage t) t).inner (track (t, x)) v v < α t ^ 2 / t

structure PersistentHyperbolicCores {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ) where
  count : ℕ
  model : Fin count → FiniteVolumeHyperbolicModel.{u}
  start : ℝ
  start_pos : 0 < start
  accuracy : ℝ → ℝ
  accuracy_pos : ∀ t, start ≤ t → 0 < accuracy t
  accuracy_antitone : AntitoneOn accuracy (Ici start)
  accuracy_decay : ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → accuracy t < ε
  domain : (i : Fin count) → ℝ → TopologicalSpace.Opens (model i).Carrier
  map : (i : Fin count) → (t : ℝ) → start ≤ t →
    (model i).Carrier → (postStage F.observation t).Carrier
  smooth : ∀ i t (ht : start ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (map i t ht) (domain i t)
  embedding : ∀ i t (ht : start ≤ t),
    IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : domain i t => map i t ht x)
  advertised_ball : ∀ i t, start ≤ t →
    riemannianBallOf (model i).metric (model i).basepoint (accuracy t)⁻¹ ⊆ domain i t
  exhausts : ∀ i (S : Set (model i).Carrier), IsCompact S →
    ∃ T : ℝ, ∀ t, T ≤ t → S ⊆ domain i t
  disjoint : ∀ t (ht : start ≤ t), Pairwise fun i j =>
    Disjoint (map i t ht '' (domain i t : Set (model i).Carrier))
      (map j t ht '' (domain j t : Set (model j).Carrier))
  metric_error : ∀ i t (ht : start ≤ t),
    let h := (model i).metric;
    let error := fun p : (model i).Carrier =>
      ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) p) ℝ).symm.toContinuousLinearMap.comp
        ((t⁻¹ : ℝ) • localPullInner (postMetric F.observation t) (map i t ht) p - h.inner p)).uncurryLeft;
    ∀ k : ℕ, k ≤ max K ⌈(accuracy t)⁻¹⌉₊ →
      ∀ p ∈ riemannianBallOf h (model i).basepoint (accuracy t)⁻¹,
        tensor0SFiberNorm h p (2 + k) (iteratedMetricCovariantDerivative h 2 error k p) < accuracy t
  thick_covered : ∀ t (ht : start ≤ t) (p : (postStage F.observation t).Carrier) (r : ℝ),
    0 < r → curvatureRadius (scaleMetric t⁻¹ (inv_pos.mpr (start_pos.trans_le ht))
      (postMetric F.observation t)) p = ENNReal.ofReal r →
    ENNReal.ofReal (accuracy t * r ^ 3) ≤ ballVolume
      (scaleMetric t⁻¹ (inv_pos.mpr (start_pos.trans_le ht)) (postMetric F.observation t)) p r →
    ∃ i, p ∈ map i t ht '' riemannianBallOf (model i).metric (model i).basepoint (accuracy t)⁻¹
  static_patches : ∀ i t, start ≤ t → ∀ x, x ∈ domain i t →
    Nonempty (PersistentModelPatch F (model i) start accuracy (domain i) (map i) t x)

def hasPersistentHyperbolicCores {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ) : Prop :=
  Nonempty (PersistentHyperbolicCores F K)

end GC.LongTime
