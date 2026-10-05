import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryOriginalLinearJacobi
import DifferentialGeometry.Geometry.Comparison.Variation.Jacobi.Gram

/-!
Original angular metric density agrees with the constructed interior linear Jacobi density.
Both the family and its common interval are derived from actual original geodesic inputs.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M] [manifoldT2 : T2Space M]

private theorem phaseDensity_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem boundary_original_phase_density_jacobi (g : SmoothRiemannianMetric I M)
    (V : Opens (E × ℝ)) (R : E × ℝ → M)
    (hR : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ)) I ∞ R V)
    (henter : ∀ q ∈ V, I.IsInteriorPoint (R q))
    (hgeo : ∀ q ∈ V, HasGeodesicEquationAt g (fun t => R (q.1, t)) q.2)
    (v₀ : E) (a : ℝ) (hva : (v₀, a) ∈ V) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      phaseDensity_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    ∃ σ : E → TangentBundle 𝓘(ℝ, E) U, ∃ W : Opens E, ∃ ε : ℝ,
      v₀ ∈ W ∧ 0 < ε ∧ ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞ σ W ∧
      (∀ e : Fin 2 → E, ∀ t ∈ Metric.ball (0 : ℝ) ε,
        (σ v₀, t) ∈ k.geodesicFlowDomain ∧
        ((boundaryPhasePoint k σ v₀ t : U) : M) = R (v₀, t + a) ∧
        curveDensity g (fun r => R (v₀, r + a))
          (fun i r => mfderiv 𝓘(ℝ, E) I (fun v => R (v, r + a)) v₀ (e i)) t =
          curveDensity k (fun r => boundaryPhasePoint k σ v₀ r)
            (fun i r => boundaryPhaseJacobiLinear k σ v₀ r (e i)) t) ∧
      ∀ w : E, ∀ t : ℝ, (σ v₀, t) ∈ k.geodesicFlowDomain →
        IsJacobiAt k (fun r => boundaryPhasePoint k σ v₀ r)
          (fun r => boundaryPhaseJacobiLinear k σ v₀ r w) t ∧
        ContMDiffAt 𝓘(ℝ) (𝓘(ℝ, E)).tangent ∞
          (fun r => (⟨boundaryPhasePoint k σ v₀ r,
            boundaryPhaseJacobiLinear k σ v₀ r w⟩ : TangentBundle 𝓘(ℝ, E) U)) t := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    phaseDensity_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  obtain ⟨σ, W, ε, hW, hε, hσ, hmatch, hJac⟩ :=
    boundary_original_phase_linear_jacobi g V R hR henter hgeo v₀ a hva
  refine ⟨σ, W, ε, hW, hε, hσ, ?_, hJac⟩
  intro e t ht
  obtain ⟨hdom, hpoint, hder⟩ := hmatch t ht
  refine ⟨hdom, hpoint, ?_⟩
  unfold curveDensity
  apply congrArg (fun A : Matrix (Fin 2) (Fin 2) ℝ => Real.sqrt A.det)
  ext i j
  simp only [curveGram, Matrix.of_apply]
  have hmetric := boundaryInteriorAtlasMetric_inner g (boundaryPhasePoint k σ v₀ t)
    (boundaryPhaseJacobiLinear k σ v₀ t (e i)) (boundaryPhaseJacobiLinear k σ v₀ t (e j))
  rw [hder (e i), hder (e j)] at hmetric
  rw [hpoint] at hmetric
  exact hmetric.symm

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
