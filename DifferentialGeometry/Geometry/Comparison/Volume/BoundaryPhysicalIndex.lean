import DifferentialGeometry.Topology.Manifold.SmoothInterval
import DifferentialGeometry.Geometry.Comparison.Variation.SecondVariation.Minimizer
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryUnitPhysicalFrame
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPhysicalDomain
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryAlivePrefixMinimum
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
Actual pole minima produce global smooth native curves near every positive truncated interval.
Real minimizing subsegments yield nonnegative index forms on actual native smooth fields.
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
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [modelBoundary : HasSmoothBoundary E H I]
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M] [manifoldT2 : T2Space M]


private theorem physicalIndex_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem exists_boundary_physical_index (g : SmoothRiemannianMetric I M) (p : M)
    (b : modelBoundary.boundaryE) (hb : extChartAt I p p = modelBoundaryParam I b) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      physicalIndex_infty_ne_zero (M := M)
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
                    (𝓝[>] (0 : ℝ)) (𝓝 (1 : ℝ))) ∧
                ∀ T : ℝ, (σ v, T - a) ∈ k.geodesicFlowDomain →
                  DifferentialGeometry.riemannianEDistOf g p
                    ((boundaryPhasePoint k σ v (T - a) : U) : M) = ENNReal.ofReal T →
                  ∀ ε ∈ Ioo 0 T, ∃ Γ : ℝ → U,
                    ContMDiff 𝓘(ℝ) 𝓘(ℝ, E) ∞ Γ ∧
                    (∀ t ∈ Icc 0 (T - ε), Γ =ᶠ[𝓝 t]
                      (fun r => boundaryPhasePoint k σ v (r + ε - a))) ∧
                    IsGeodesicOn k Γ (Icc 0 (T - ε)) ∧
                    (∀ t ∈ Icc 0 (T - ε), k.inner (Γ t)
                      (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) Γ t 1)
                      (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) Γ t 1) = 1) ∧
                    (∀ η : ℝ → U, ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) 1 η (Icc 0 (T - ε)) →
                      η 0 = Γ 0 → η (T - ε) = Γ (T - ε) →
                      arcLength k Γ 0 (T - ε) ≤ arcLength k η 0 (T - ε)) ∧
                    ∀ Z : ℝ → E,
                      ContMDiff 𝓘(ℝ) (𝓘(ℝ, E)).tangent (8 : ℕ)
                        (fun t => (⟨Γ t, Z t⟩ : TangentBundle 𝓘(ℝ, E) U)) →
                      (∀ t ∈ Icc 0 (T - ε), k.inner (Γ t) (Z t)
                        (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) Γ t 1) = 0) →
                      Z 0 = 0 → Z (T - ε) = 0 →
                      0 ≤ indexForm k Γ 0 (T - ε) Z Z := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    physicalIndex_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  have hp : I.IsBoundaryPoint p := by
    change extChartAt I p p ∈ frontier (range I)
    rw [hb, ← range_modelBoundaryParam I]
    exact mem_range_self b
  obtain ⟨G, hcomplete, O, hpO, hG, V, ρ, hρ, hall, hlaunch⟩ :=
    exists_boundary_unit_physical_frame g p b hb
  refine ⟨G, hcomplete, O, hpO, hG, V, ρ, hρ, hall, ?_⟩
  intro v hin hunit
  obtain ⟨δ, hδ, a, ha, σ, W, hv, hσ, hbirth, hPole, hlimit, hframe⟩ :=
    hlaunch v hin hunit
  refine ⟨δ, hδ, a, ha, σ, W, hv, hσ, hbirth, hPole, hlimit, ?_⟩
  intro T hT hterminal ε hε
  have hε0 : 0 < ε := hε.1
  have hεT : ε < T := hε.2
  let φ : ℝ → U := fun t => boundaryPhasePoint k σ v (t - a)
  have hdomain := boundaryPhase_positive_physical_domain g p hp
    σ W hσ v hv δ a hδ ha (fun t ht => (hbirth t ht).2) hPole
  have hpositive : 0 < T := hdomain.1 T hT
  have hwhole (t : ℝ) (ht : t ∈ Ioc 0 T) :
      (σ v, t - a) ∈ k.geodesicFlowDomain := hdomain.2 t T ht.1 ht.2 hT
  have hsmooth : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) 1 φ (Ioc 0 T) := by
    intro t ht
    exact ((hframe t (hwhole t ht)).1.of_le (by simp)).contMDiffWithinAt
  have hspeed (t : ℝ) (ht : t ∈ Ioo 0 T) :
      k.inner (φ t) (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) φ t 1)
        (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) φ t 1) = 1 :=
    (hframe t (hwhole t ⟨ht.1, ht.2.le⟩)).2.2.1
  have hminimum := boundaryInterior_alive_prefix_minimum g p φ T
    hpositive hsmooth hspeed hPole hterminal
  let K : Set ℝ := {t | (σ v, t + ε - a) ∈ k.geodesicFlowDomain}
  have hKopen : IsOpen K := (k.isOpen_geodesicFlowDomain (r := ⊤) le_top).preimage
    (continuous_const.prodMk ((continuous_id.add continuous_const).sub continuous_const))
  have hK (t : ℝ) (ht : t ∈ Icc 0 (T - ε)) : t ∈ K :=
    hwhole (t + ε) ⟨by linarith [ht.1, hε.1], by linarith [ht.2]⟩
  have hshiftSmooth : ContMDiffOn 𝓘(ℝ) 𝓘(ℝ, E) ∞ (fun r => φ (r + ε)) K := by
    intro t ht
    have hadd : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ) ∞ (fun r : ℝ => r + ε) t :=
      contMDiffAt_id.add contMDiffAt_const
    exact ((hframe (t + ε) ht).1.comp (f := fun r : ℝ => r + ε) t hadd).contMDiffWithinAt
  obtain ⟨Γ, hΓ, heq⟩ :=
    DifferentialGeometry.Topology.Manifold.exists_global_smooth_curve_eq_near_interval
      (sub_nonneg.mpr hε.2.le) hKopen hK hshiftSmooth
  have hpoint (t : ℝ) (ht : t ∈ Icc 0 (T - ε)) : Γ t = φ (t + ε) :=
    (heq t ht).self_of_nhds
  have hvelocity (t : ℝ) (ht : t ∈ Icc 0 (T - ε)) :
      (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) Γ t 1 : E) =
        mfderiv 𝓘(ℝ) 𝓘(ℝ, E) φ (t + ε) 1 := by
    have hgerm := congrArg (fun A : ℝ →L[ℝ] E => A (1 : ℝ))
      ((heq t ht).mfderiv_eq (I := 𝓘(ℝ)) (I' := 𝓘(ℝ, E)))
    exact hgerm.trans (DifferentialGeometry.Geometry.mfderiv_comp_add_apply_one t ε
      ((hframe (t + ε) (hK t ht)).1.mdifferentiableAt (by simp)))
  have hΓunit (t : ℝ) (ht : t ∈ Icc 0 (T - ε)) : k.inner (Γ t)
      (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) Γ t 1)
      (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) Γ t 1) = 1 := by
    have hvv := congrArg₂ (fun x z : E => k.inner (Γ t) x z)
      (hvelocity t ht) (hvelocity t ht)
    have hpp := congrArg (fun q : U => k.inner q
      (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) φ (t + ε) 1)
      (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) φ (t + ε) 1)) (hpoint t ht)
    exact hvv.trans (hpp.trans ((hframe (t + ε) (hK t ht)).2.2.1))
  have hΓgeo : IsGeodesicOn k Γ (Icc 0 (T - ε)) := by
    intro t ht
    have hshift : HasGeodesicEquationAt k (fun r => φ (r + ε)) t := by
      have haff := hasGeodesicEquationAt_comp_affine
        (c := 1) (d := ε) (t := t)
        (by simpa only [one_mul] using (hframe (t + ε) (hK t ht)).2.1)
      simpa only [one_mul] using haff
    exact HasGeodesicEquationAt.congr_of_eventuallyEq_at (hpoint t ht) (heq t ht) hshift
  have hΓ0 : Γ 0 = φ ε := by simpa only [zero_add] using hpoint 0 ⟨le_rfl, by linarith⟩
  have hΓend : Γ (T - ε) = φ T := by
    simpa only [sub_add_cancel] using hpoint (T - ε) ⟨by linarith, le_rfl⟩
  have hdist : DifferentialGeometry.riemannianEDistOf g (Γ 0 : M)
      (Γ (T - ε) : M) = ENNReal.ofReal (T - ε) :=
    (congrArg₂ (fun x y : U => DifferentialGeometry.riemannianEDistOf g (x : M) (y : M))
      hΓ0 hΓend).trans (hminimum.2.1 ε ⟨hε.1, hε.2.le⟩ T ⟨hpositive, le_rfl⟩ hε.2.le)
  have hΓmin := boundaryInterior_curve_minimizing g Γ 0 (T - ε)
    (by linarith) (fun t ht => hΓunit t ⟨ht.1.le, ht.2.le⟩) (by
      simpa only [sub_zero] using hdist)
  refine ⟨Γ, hΓ, heq, hΓgeo, hΓunit, hΓmin, ?_⟩
  intro Z hZ hperp hzero hend
  exact indexForm_nonneg_of_minimising_geodesic k Γ (T - ε) Z (by linarith)
    hZ hΓgeo hΓmin hΓunit hperp hzero hend

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
