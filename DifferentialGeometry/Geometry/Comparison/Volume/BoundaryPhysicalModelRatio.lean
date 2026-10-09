import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPhysicalBirthRank
import DifferentialGeometry.Geometry.Comparison.Volume.Model
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryCommonPoleInitialFrame
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPhasePhysicalFrame
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryCommonBirthPhase
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryOriginalPoleContinuity
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPhaseRadialFrame
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPhaseBirthDensity
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryBirthGramDensity
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryBirthAngularContinuation
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPoleGramLimit
import DifferentialGeometry.Geometry.Comparison.Variation.Jacobi.Gram
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryBirthTangentMap
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorChartMetric
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPoleJacobiFrame
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryJointJacobiFrame
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Naturality.VariationPairing
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorMetric
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

/-!
Actual pole families have model-normalized physical birth density tending to one.
Real near-pole bounds and angular rank provide the initial input for Ricci comparison.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open DifferentialGeometry.Geometry.Boundary
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [modelBoundary : HasSmoothBoundary E H I]
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M] [manifoldT2 : T2Space M]


private theorem physicalModelRatio_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem exists_boundary_physical_model_ratio (g : SmoothRiemannianMetric I M) (p : M)
    (b : modelBoundary.boundaryE) (hb : extChartAt I p p = modelBoundaryParam I b) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      physicalModelRatio_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    ∃ G : SmoothRiemannianMetric 𝓘(ℝ, E) E, RiemannianMetricComplete G ∧
      ∃ O : Opens E, extChartAt I p p ∈ O ∧
        (∀ y ∈ (O : Set E) ∩ range I, ∀ z w : E,
          G.inner y z w = DifferentialGeometry.Geometry.Connection.metricFlatModelInChart
            g p y z w) ∧
        ∃ V : Opens (E × ℝ), ∃ ρ : E × ℝ → U,
          ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ ρ V ∧
          (∀ q ∈ V,
            ((⟨extChartAt I p p, q.1⟩ : TangentBundle 𝓘(ℝ, E) E), q.2) ∈
              G.geodesicFlowDomain ∧
            boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2 ∈
              (O : Set E) ∩ interior (extChartAt I p).target ∧
            (ρ q : M) = (extChartAt I p).symm
              (boundaryPoleFlowFamily G (extChartAt I p p) q.1 q.2) ∧
            HasGeodesicEquationAt k (fun t => ρ (q.1, t)) q.2) ∧
          ∀ v : E, (∃ w : modelBoundary.boundaryE, ∃ c : ℝ, 0 < c ∧
            v = fderiv ℝ (modelBoundaryParam I) b w + c • modelBoundary.inwardCoordE) →
            G.inner (extChartAt I p p) v v = 1 →
            ∃ δ : ℝ, 0 < δ ∧ ∃ a ∈ Ioo 0 δ,
              ∃ σ : E → TangentBundle 𝓘(ℝ, E) U, ∃ W : Opens E,
                v ∈ W ∧ ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞ σ W ∧
                (∀ t ∈ Ioo 0 δ, (v, t) ∈ V ∧ (σ v, t - a) ∈ k.geodesicFlowDomain) ∧
                Tendsto (fun t : ℝ => ((boundaryPhasePoint k σ v (t - a) : U) : M))
                  (𝓝[>] (0 : ℝ)) (𝓝 p) ∧
                (∀ e : Fin 2 → E,
                  (∀ i j, G.inner (extChartAt I p p) (e i) (e j) = if i = j then 1 else 0) →
                  ∀ κ : ℝ,
                    Tendsto (fun t : ℝ => curveDensity k
                      (fun r => boundaryPhasePoint k σ v (r - a))
                      (fun i r => boundaryPhaseJacobiLinear k σ v (r - a) (e i)) t /
                        modelRadius (-κ ^ 2) t ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) ∧
                    ∃ η ∈ Ioo 0 δ, ∀ t ∈ Ioo 0 η,
                      (σ v, t - a) ∈ k.geodesicFlowDomain ∧
                      LinearIndependent ℝ (fun i : Fin 2 =>
                        boundaryPhaseJacobiLinear k σ v (t - a) (e i)) ∧
                      (1 : ℝ) / 2 ≤ curveDensity k
                        (fun r => boundaryPhasePoint k σ v (r - a))
                        (fun i r => boundaryPhaseJacobiLinear k σ v (r - a) (e i)) t /
                          modelRadius (-κ ^ 2) t ^ 2) ∧
                ∀ t : ℝ, (σ v, t - a) ∈ k.geodesicFlowDomain →
                  ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞
                    (fun r => boundaryPhasePoint k σ v (r - a)) t ∧
                  HasGeodesicEquationAt k (fun r => boundaryPhasePoint k σ v (r - a)) t ∧
                  k.inner (boundaryPhasePoint k σ v (t - a))
                    (curveVelocity (I := 𝓘(ℝ, E))
                      (fun r => boundaryPhasePoint k σ v (r - a)) t)
                    (curveVelocity (I := 𝓘(ℝ, E))
                      (fun r => boundaryPhasePoint k σ v (r - a)) t) = 1 ∧
                  (∀ w : E, G.inner (extChartAt I p p) w v = 0 →
                    k.inner (boundaryPhasePoint k σ v (t - a))
                      (boundaryPhaseJacobiLinear k σ v (t - a) w)
                      (curveVelocity (I := 𝓘(ℝ, E))
                        (fun r => boundaryPhasePoint k σ v (r - a)) t) = 0 ∧
                    k.inner (boundaryPhasePoint k σ v (t - a))
                      (covDerivAlong k (fun r => boundaryPhasePoint k σ v (r - a))
                        (fun r => boundaryPhaseJacobiLinear k σ v (r - a) w) t)
                      (curveVelocity (I := 𝓘(ℝ, E))
                        (fun r => boundaryPhasePoint k σ v (r - a)) t) = 0) ∧
                  (∀ w z : E, jacobiWronskian k
                    (fun r => boundaryPhasePoint k σ v (r - a))
                    (fun r => boundaryPhaseJacobiLinear k σ v (r - a) w)
                    (fun r => boundaryPhaseJacobiLinear k σ v (r - a) z) t = 0) ∧
                  ∀ w : E, IsJacobiAt k (fun r => boundaryPhasePoint k σ v (r - a))
                      (fun r => boundaryPhaseJacobiLinear k σ v (r - a) w) t ∧
                    ContMDiffAt 𝓘(ℝ) (𝓘(ℝ, E)).tangent ∞
                      (fun r => (⟨boundaryPhasePoint k σ v (r - a),
                        boundaryPhaseJacobiLinear k σ v (r - a) w⟩ :
                        TangentBundle 𝓘(ℝ, E) U)) t := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    physicalModelRatio_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  obtain ⟨G, hcomplete, O, hpO, hG, V, ρ, hρ, hall, hlaunch⟩ :=
    exists_boundary_physical_birth_rank g p b hb
  refine ⟨G, hcomplete, O, hpO, hG, V, ρ, hρ, hall, ?_⟩
  intro v hin hunit
  obtain ⟨δ, hδ, a, ha, σ, W, hv, hσ, hbirth, hPole, hrank, hframe⟩ :=
    hlaunch v hin hunit
  refine ⟨δ, hδ, a, ha, σ, W, hv, hσ, hbirth, hPole, ?_, hframe⟩
  intro e he κ
  obtain ⟨hdensity, η₀, hη₀, hborn⟩ := hrank e he
  let D : ℝ → ℝ := fun t => curveDensity k
    (fun r => boundaryPhasePoint k σ v (r - a))
    (fun i r => boundaryPhaseJacobiLinear k σ v (r - a) (e i)) t
  have hmodel : Tendsto (fun t : ℝ => (modelRadius (-κ ^ 2) t / t) ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa only [one_pow] using (modelRadiusRatio_tendsto (-κ ^ 2)).pow 2
  have hD : Tendsto (fun t : ℝ => D t / t ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := hdensity
  have hraw := hD.div hmodel (by norm_num : (1 : ℝ) ≠ 0)
  have heq : (fun t : ℝ => D t / t ^ 2 / (modelRadius (-κ ^ 2) t / t) ^ 2) =ᶠ[
      𝓝[>] (0 : ℝ)] (fun t => D t / modelRadius (-κ ^ 2) t ^ 2) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [div_pow, div_div_div_cancel_right₀ (pow_ne_zero 2 (ne_of_gt ht))]
  have hratio : Tendsto (fun t : ℝ => D t / modelRadius (-κ ^ 2) t ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    have hraw' : Tendsto (fun t : ℝ => D t / t ^ 2 /
        (modelRadius (-κ ^ 2) t / t) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) := by
      have hpoint : Tendsto (fun t : ℝ => D t / t ^ 2 /
          (modelRadius (-κ ^ 2) t / t) ^ 2)
          (𝓝[>] (0 : ℝ)) (𝓝 ((1 : ℝ) / 1)) :=
        hraw.congr' (Eventually.of_forall (fun t : ℝ => rfl))
      simpa only [div_one] using hpoint
    exact hraw'.congr' heq
  have hnear : ∀ᶠ t in 𝓝[>] (0 : ℝ), (1 : ℝ) / 2 <
      D t / modelRadius (-κ ^ 2) t ^ 2 :=
    Filter.Tendsto.eventually_const_lt (by norm_num : (1 : ℝ) / 2 < 1) hratio
  obtain ⟨η₁, hη₁, hηsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hnear
  let η := min η₀ η₁ / 2
  have hmin : 0 < min η₀ η₁ := lt_min hη₀.1 hη₁
  have hη0 : 0 < η := by dsimp [η]; positivity
  have hηη₀ : η ≤ η₀ := (half_le_self hmin.le).trans (min_le_left η₀ η₁)
  have hηη₁ : η ≤ η₁ := (half_le_self hmin.le).trans (min_le_right η₀ η₁)
  refine ⟨hratio, η, ⟨hη0, hηη₀.trans_lt hη₀.2⟩, ?_⟩
  intro t ht
  have hdata := hborn t ⟨ht.1, ht.2.trans_le hηη₀⟩
  exact ⟨hdata.1, hdata.2.2, (hηsub ⟨ht.1, ht.2.trans_le hηη₁⟩).le⟩

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
