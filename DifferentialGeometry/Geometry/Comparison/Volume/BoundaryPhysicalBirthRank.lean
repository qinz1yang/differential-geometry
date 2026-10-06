import Mathlib.Algebra.Order.Star.Real
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryUnitPhysicalFrame
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
Actual original pole density limits give positive full angular rank on genuine birth intervals.
The same metric and pole family precede all unit inward directions and initial frames.
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


private theorem physicalBirthRank_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

omit ambientFinite modelBoundary manifoldT2 in
private theorem density_positive_linearIndependent (g : SmoothRiemannianMetric I M)
    (γ : ℝ → M) (J : Fin 2 → ∀ t, TangentSpace I (γ t)) (t : ℝ)
    (hpositive : 0 < curveDensity g γ J t) :
    LinearIndependent ℝ (fun i => J i t) := by
  classical
  have hPSD : (curveGram g γ J t).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg (curveGram_herm g γ J t) ?_
    intro c
    rw [curveGram_dotVec]
    by_cases hz : (∑ i, c i • J i t) = 0
    · simp only [hz, map_zero]
      exact le_rfl
    · exact (g.pos (γ t) _ hz).le
  change 0 < Real.sqrt (curveGram g γ J t).det at hpositive
  have hPD := hPSD.posDef_iff_det_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mp hpositive))
  refine Fintype.linearIndependent_iff.mpr ?_
  intro c hc i
  by_contra hi
  have hc0 : c ≠ 0 := by
    intro hz
    exact hi (congrFun hz i)
  have hgt := hPD.dotProduct_mulVec_pos hc0
  rw [curveGram_dotVec, hc] at hgt
  have hzero : (0 : ℝ) < 0 := by simpa only [map_zero] using hgt
  exact (lt_irrefl (0 : ℝ)) hzero

theorem exists_boundary_physical_birth_rank (g : SmoothRiemannianMetric I M) (p : M)
    (b : modelBoundary.boundaryE) (hb : extChartAt I p p = modelBoundaryParam I b) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      physicalBirthRank_infty_ne_zero (M := M)
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
                  Tendsto (fun t : ℝ => curveDensity k
                    (fun r => boundaryPhasePoint k σ v (r - a))
                    (fun i r => boundaryPhaseJacobiLinear k σ v (r - a) (e i)) t / t ^ 2)
                    (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ)) ∧
                  ∃ η ∈ Ioo 0 δ, ∀ t ∈ Ioo 0 η,
                    (σ v, t - a) ∈ k.geodesicFlowDomain ∧
                    0 < curveDensity k (fun r => boundaryPhasePoint k σ v (r - a))
                      (fun i r => boundaryPhaseJacobiLinear k σ v (r - a) (e i)) t ∧
                    LinearIndependent ℝ (fun i : Fin 2 =>
                      boundaryPhaseJacobiLinear k σ v (t - a) (e i))) ∧
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
    physicalBirthRank_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  obtain ⟨G, hcomplete, O, hpO, hG, V, ρ, hρ, hall, hlaunch⟩ :=
    exists_boundary_unit_physical_frame g p b hb
  refine ⟨G, hcomplete, O, hpO, hG, V, ρ, hρ, hall, ?_⟩
  intro v hin hunit
  obtain ⟨δ, hδ, a, ha, σ, W, hv, hσ, hbirth, hPole, hlimit, hframe⟩ :=
    hlaunch v hin hunit
  refine ⟨δ, hδ, a, ha, σ, W, hv, hσ, hbirth, hPole, ?_, hframe⟩
  intro e he
  have hlim := hlimit e he
  have hnear : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 <
      curveDensity k (fun r => boundaryPhasePoint k σ v (r - a))
        (fun i r => boundaryPhaseJacobiLinear k σ v (r - a) (e i)) t / t ^ 2 :=
    Filter.Tendsto.eventually_const_lt (by norm_num : (0 : ℝ) < 1) hlim
  obtain ⟨η, hη, hηsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hnear
  let β := min δ η / 2
  have hmin : 0 < min δ η := lt_min hδ hη
  have hβ0 : 0 < β := by dsimp [β]; positivity
  have hβδ : β < δ := by dsimp [β]; linarith [min_le_left δ η]
  have hβη : β ≤ η :=
    (half_le_self hmin.le).trans (min_le_right δ η)
  refine ⟨hlim, β, ⟨hβ0, hβδ⟩, ?_⟩
  intro t ht
  have htδ : t ∈ Ioo 0 δ := ⟨ht.1, ht.2.trans hβδ⟩
  have hratio : 0 < curveDensity k (fun r => boundaryPhasePoint k σ v (r - a))
      (fun i r => boundaryPhaseJacobiLinear k σ v (r - a) (e i)) t / t ^ 2 :=
    hηsub ⟨ht.1, ht.2.trans_le hβη⟩
  have hdensity : 0 < curveDensity k (fun r => boundaryPhasePoint k σ v (r - a))
      (fun i r => boundaryPhaseJacobiLinear k σ v (r - a) (e i)) t := by
    rcases div_pos_iff.mp hratio with hpos | hneg
    · exact hpos.1
    · exact False.elim ((not_lt_of_ge (sq_nonneg t)) hneg.2)
  exact ⟨(hbirth t htδ).2, hdensity, density_positive_linearIndependent k
    (fun r => boundaryPhasePoint k σ v (r - a))
    (fun i r => boundaryPhaseJacobiLinear k σ v (r - a) (e i)) t hdensity⟩

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
