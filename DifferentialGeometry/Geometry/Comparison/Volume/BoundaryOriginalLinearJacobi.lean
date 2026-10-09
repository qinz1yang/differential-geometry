import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryOriginalPhaseMatching
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPhaseJacobiLinearFrame

/-!
The original velocity derivative is the image of the constructed native linear Jacobi family.
One actual seed family and matching interval serve every direction simultaneously.
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

private theorem phaseLinear_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem boundary_original_phase_linear_jacobi (g : SmoothRiemannianMetric I M)
    (V : Opens (E × ℝ)) (R : E × ℝ → M)
    (hR : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ)) I ∞ R V)
    (henter : ∀ q ∈ V, I.IsInteriorPoint (R q))
    (hgeo : ∀ q ∈ V, HasGeodesicEquationAt g (fun t => R (q.1, t)) q.2)
    (v₀ : E) (a : ℝ) (hva : (v₀, a) ∈ V) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      phaseLinear_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    ∃ σ : E → TangentBundle 𝓘(ℝ, E) U, ∃ W : Opens E, ∃ ε : ℝ,
      v₀ ∈ W ∧ 0 < ε ∧ ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞ σ W ∧
      (∀ t ∈ Metric.ball (0 : ℝ) ε,
        (σ v₀, t) ∈ k.geodesicFlowDomain ∧
        ((boundaryPhasePoint k σ v₀ t : U) : M) = R (v₀, t + a) ∧
        ∀ w : E,
          (mfderiv 𝓘(ℝ, E) I (Subtype.val : U → M) (boundaryPhasePoint k σ v₀ t)
            (boundaryPhaseJacobiLinear k σ v₀ t w) : E) =
            mfderiv 𝓘(ℝ, E) I (fun v => R (v, t + a)) v₀ w) ∧
      ∀ w : E, ∀ t : ℝ, (σ v₀, t) ∈ k.geodesicFlowDomain →
        IsJacobiAt k (fun s => boundaryPhasePoint k σ v₀ s)
          (fun s => boundaryPhaseJacobiLinear k σ v₀ s w) t ∧
        ContMDiffAt 𝓘(ℝ) (𝓘(ℝ, E)).tangent ∞
          (fun s => (⟨boundaryPhasePoint k σ v₀ s,
            boundaryPhaseJacobiLinear k σ v₀ s w⟩ : TangentBundle 𝓘(ℝ, E) U)) t := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    phaseLinear_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  obtain ⟨σ, W, ε, hW, hε, hσ, _hbase, hmatch⟩ :=
    boundary_original_phase_flow_matches g V R hR henter hgeo v₀ a hva
  refine ⟨σ, W, ε, hW, hε, hσ, ?_,
    boundaryPhaseJacobiLinear_jacobi k W σ hσ v₀ hW⟩
  intro t ht
  have hdom := (hmatch v₀ hW t ht).1
  have hpoint := (hmatch v₀ hW t ht).2
  refine ⟨hdom, hpoint, ?_⟩
  intro w
  have hnew := boundaryPhasePoint_smoothAt k W σ hσ v₀ t hW hdom
  have hval := DifferentialGeometry.Manifold.contMDiff_intrinsicInterior_val
    I ∞ phaseLinear_infty_ne_zero (M := M)
  have hvalAt := (hval.contMDiffAt (x := boundaryPhasePoint k σ v₀ t)).mdifferentiableAt
    (by simp)
  have hcomp := mfderiv_comp v₀ hvalAt (hnew.mdifferentiableAt (by simp))
  have happ := congrArg (fun A : E →L[ℝ] E => A w) hcomp
  have hgerm : (fun v => ((boundaryPhasePoint k σ v t : U) : M)) =ᶠ[𝓝 v₀]
      (fun v => R (v, t + a)) := by
    filter_upwards [W.isOpen.mem_nhds hW] with v hv
    exact (hmatch v hv t ht).2
  have hder : mfderiv 𝓘(ℝ, E) I
      (fun v => ((boundaryPhasePoint k σ v t : U) : M)) v₀ =
      mfderiv 𝓘(ℝ, E) I (fun v => R (v, t + a)) v₀ := hgerm.mfderiv_eq
  exact happ.symm.trans (congrArg (fun A : E →L[ℝ] E => A w) hder)

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
