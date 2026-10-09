import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Parameters
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.AnalyticAdmissibility
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.EnhancedProfileFullC11F
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.PersistentHyperbolicCores
import DifferentialGeometry.Geometry.Hyperbolic.Truncation
import DifferentialGeometry.Geometry.Collapse.LatePieceGeometry
import DifferentialGeometry.Geometry.Collapse.UniformDerivativeBounds

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open GC.Endpoint GC.GraphManifold DifferentialGeometry.Geometry.Hyperbolic Set
open GC.Topology
open scoped Manifold ContDiff ENNReal
namespace GC.LongTime
universe u

def RegularSlice.componentMetric {P : OrientedThreeStage.{u}} {g : P.Metric}
    {T : ObservationTower P g} (s : RegularSlice T)
    (C : ConnectedComponents s.stage.Carrier) :
    SmoothRiemannianMetric (𝓡 3) (s.stage.toClosedOrientedManifold.component C).Carrier :=
  s.normalizedMetric.restrictOpen (s.stage.toClosedOrientedManifold.componentOpen C)

def hasThinVolumeGeometry (W : CompactCarrier.{u})
    (g : SmoothRiemannianMetric W.model W.Carrier) (K : ℕ) (w : ℝ) : Prop :=
  (W.model.boundary W.Carrier = ∅ ∧ ∀ p, volumeCollapsedAtCurvatureScale g w p) ∨
    (Nonempty (NearlyCuspidalBoundary W g (K + 4) w) ∧ boundaryVolumeCollapsed W g w)

inductive HyperbolicOrThin {M : ConnectedClosedOrientedManifold.{u} 3}
    (D : TorusDecomposition M)
    (metric : (i : Fin D.components.count) → SmoothRiemannianMetric (D.component i).model (D.component i).Carrier)
    (thin : Fin D.components.count → Prop) (K : ℕ) (w : ℝ) (i : Fin D.components.count)
  | hyperbolic (not_thin : ¬ thin i) (geometry : D.carrier.InteriorGeometry (D.components.piece i))
      (model_eq : isHyperbolicInteriorGeometry geometry)
  | thin (member : thin i) (geometry : hasThinVolumeGeometry (D.component i) (metric i) K w)
  | nonnegative (not_thin : ¬ thin i) (closed : (D.component i).model.boundary (D.component i).Carrier = ∅)
      (curvature : DifferentialGeometry.Geometry.Riemannian.SectionalBoundedBelow (metric i) 0)

structure LateCutFamily {P : OrientedThreeStage.{u}} {g : P.Metric}
    (F : GC.Interface.RawSurgery P g) (K : ℕ) (slices : ℕ → RegularSlice F.observation) where
  cores : PersistentHyperbolicCores F (K + 4)
  decomposition : ∀ j (C : ConnectedComponents (slices j).stage.Carrier),
    TorusDecomposition ((slices j).stage.toClosedOrientedManifold.component C)
  metric : ∀ j C (i : Fin (decomposition j C).components.count),
    SmoothRiemannianMetric ((decomposition j C).component i).model ((decomposition j C).component i).Carrier
  induced : ∀ j C i, isInducedCutMetric ((slices j).componentMetric C) (decomposition j C) i (metric j C i)
  thin : ∀ j C, Fin (decomposition j C).components.count → Prop
  first : ℕ
  time_late : ∀ j, first ≤ j → cores.start ≤ (slices j).time
  truncation : ∀ (_j : ℕ) (i : Fin cores.count), HyperbolicTruncation (cores.model i)
  port : ∀ j, first ≤ j →
    (Σ C : ConnectedComponents (slices j).stage.Carrier, Fin (decomposition j C).boundary.count) ≃
      Σ i : Fin cores.count, Fin (truncation j i).count
  core_in_ball : ∀ j, first ≤ j → ∀ i,
    range (truncation j i).inclusion ⊆ riemannianBallOf (cores.model i).metric
      (cores.model i).basepoint (cores.accuracy (slices j).time)⁻¹
  seam_image : ∀ j (hj : first ≤ j) C (s : Fin (decomposition j C).boundary.count),
    let p := port j hj ⟨C, s⟩;
    HEq (range (fun x : Torus => cores.map p.1 (slices j).time (time_late j hj)
      ((truncation j p.1).cuspMap p.2 (x, halfZero))))
      (range (fun x : Torus => ((decomposition j C).reconstructionAtlas.torusInPrime
        (decomposition j C).reconstruction s x).val))
  finite_scales : ∀ j C i, thin j C i → ∀ p, curvatureRadius (metric j C i) p ≠ ⊤
  alternatives : ∀ w : ℝ, 0 < w → w < euclideanThreeUnitBallVolume →
    ∃ N : ℕ, ∀ j, N ≤ j → ∀ C,
      Nonempty ((i : Fin (decomposition j C).components.count) →
        HyperbolicOrThin (decomposition j C) (metric j C) (thin j C) K w i)

namespace LateCutFamily
variable {P : OrientedThreeStage.{u}} {g : P.Metric}
  {F : GC.Interface.RawSurgery P g} {K : ℕ} {slices : ℕ → RegularSlice F.observation}

def thinIndex (L : LateCutFamily F K slices) (j : ℕ) :=
  Σ C : ConnectedComponents (slices j).stage.Carrier,
    {i : Fin (L.decomposition j C).components.count // L.thin j C i}

instance (L : LateCutFamily F K slices) (j : ℕ) : Finite (L.thinIndex j) := by
  have : LocallyConnectedSpace (slices j).stage.Carrier :=
    ChartedSpace.locallyConnectedSpace ThreeSpace (slices j).stage.Carrier
  unfold thinIndex
  infer_instance

def hasEventualDerivativeBounds (L : LateCutFamily F K slices) : Prop :=
  ∀ w : ℝ, 0 < w → w < euclideanThreeUnitBallVolume →
    ∃ N : ℕ, ∃ C : ℝ, 0 < C ∧
      ∀ j, N ≤ j → ∀ c i, L.thin j c i →
      ∀ (p : ((L.decomposition j c).component i).Carrier) (r : ℝ), 0 < r →
        ENNReal.ofReal r < curvatureRadius (L.metric j c i) p →
        ENNReal.ofReal (w * r ^ 3) ≤ ballVolume (L.metric j c i) p r →
        ∀ k : ℕ, k ≤ K → ∀ q ∈ riemannianBallOf (L.metric j c i) p r,
          curvatureDerivativeNorm (L.metric j c i) k q ≤ C * (r ^ (k + 2))⁻¹

theorem exists_common_control (L : LateCutFamily F K slices) (h : L.hasEventualDerivativeBounds) :
    ∃ A : ℝ → ℝ, (∀ w, 0 < w → 0 < A w) ∧
      ∀ j C i, L.thin j C i → ∀ w, 0 < w → curvatureDerivativesControlled (L.metric j C i) K A w := by
  obtain ⟨A, hA, hcontrol⟩ := exists_common_curvature_derivative_bound_of_eventual K L.thinIndex
    (fun j i => (L.decomposition j i.1).component i.2.val)
    (fun j i => L.metric j i.1 i.2.val) (by
      intro w hw hc
      obtain ⟨N, C, hC, hb⟩ := h w hw hc
      exact ⟨N, C, hC, fun j hj i => hb j hj i.1 i.2.val i.2.property⟩)
  exact ⟨A, hA, fun j C i hi => hcontrol j ⟨C, i, hi⟩⟩

end LateCutFamily


theorem hasThinVolumeGeometry.collapseHypotheses {W : CompactCarrier.{u}}
    {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {w : ℝ} {A : ℝ → ℝ}
    (h : hasThinVolumeGeometry W g K w) (hcontrol : curvatureDerivativesControlled g K A w) :
    staticCollapseHypotheses W g K A w := by
  rcases h with h | ⟨⟨B⟩, hv⟩
  · exact Or.inl ⟨h.1, h.2, hcontrol⟩
  · exact Or.inr ⟨⟨B.restrictOrder (by omega : K ≤ K + 4)⟩, hv, hcontrol⟩

def HyperbolicOrThin.toHyperbolicOrCollapsed {M : ConnectedClosedOrientedManifold.{u} 3}
    {D : TorusDecomposition M}
    {metric : (i : Fin D.components.count) → SmoothRiemannianMetric (D.component i).model (D.component i).Carrier}
    {thin : Fin D.components.count → Prop} {K : ℕ} {w : ℝ} {i : Fin D.components.count}
    (h : HyperbolicOrThin D metric thin K w i)
    (g : SmoothRiemannianMetric (𝓡 3) M.Carrier) (A : ℝ → ℝ)
    (hinduced : isInducedCutMetric g D i (metric i))
    (hcontrol : thin i → curvatureDerivativesControlled (metric i) K A w) :
    HyperbolicOrCollapsed g D K A w i := by
  cases h with
  | hyperbolic _ geometry model_eq => exact .hyperbolic geometry model_eq
  | thin member geometry => exact .collapsed (metric i) hinduced (geometry.collapseHypotheses (hcontrol member))
  | nonnegative _ closed curvature => exact .nonnegative (metric i) hinduced closed curvature

theorem LateCutFamily.exists_late_tests_of_derivative_bounds
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {K : ℕ} {slices : ℕ → RegularSlice F.observation}
    (L : LateCutFamily F K slices) (h : L.hasEventualDerivativeBounds) :
    ∃ A : ℝ → ℝ, (∀ w, 0 < w → w < euclideanThreeUnitBallVolume → 0 < A w) ∧
      ∀ w, 0 < w → w < euclideanThreeUnitBallVolume → ∃ N : ℕ, ∀ j, N ≤ j → ∀ C,
        Nonempty ((i : Fin (L.decomposition j C).components.count) →
          HyperbolicOrCollapsed ((slices j).componentMetric C) (L.decomposition j C) K A w i) := by
  obtain ⟨A, hA, hbound⟩ := L.exists_common_control h
  refine ⟨A, fun w hw _ => hA w hw, ?_⟩
  intro w hw hc
  obtain ⟨N, hn⟩ := L.alternatives w hw hc
  refine ⟨max N L.first, ?_⟩
  intro j hj C
  obtain ⟨pieces⟩ := hn j (le_trans (le_max_left _ _) hj) C
  exact ⟨fun i => (pieces i).toHyperbolicOrCollapsed ((slices j).componentMetric C) A
    (L.induced j C i) (fun hi => hbound j C i hi w hw)⟩



end GC.LongTime
