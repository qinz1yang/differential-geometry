import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryOriginalPhaseMatching
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPhaseJacobiLinearFrame
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryJointJacobiFrame
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorEquation

/-!
Actual interior birth families have common native phase seeds and linear angular continuation.
One neighborhood and time interval precede all directions; Jacobi fields extend to existing times.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M] [manifoldT2 : T2Space M]

private theorem birthPhaseContinuation_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem boundaryBirth_phase_continuation (g : SmoothRiemannianMetric I M) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      birthPhaseContinuation_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    ∀ V : Opens (E × ℝ), ∀ ρ : E × ℝ → U,
      ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ)) 𝓘(ℝ, E) ∞ ρ V →
      (∀ q ∈ V, HasGeodesicEquationAt k (fun r => ρ (q.1, r)) q.2) →
      ∀ (v₀ : E) (a : ℝ), (v₀, a) ∈ V →
        ∃ σ : E → TangentBundle 𝓘(ℝ, E) U, ∃ W : Opens E, ∃ ε : ℝ,
          v₀ ∈ W ∧ 0 < ε ∧ ContMDiffOn 𝓘(ℝ, E) (𝓘(ℝ, E)).tangent ∞ σ W ∧
          (∀ v ∈ W, (v, a) ∈ V ∧ (σ v).proj = ρ (v, a)) ∧
          (∀ v ∈ W, ∀ s ∈ Metric.ball (0 : ℝ) ε,
            (σ v, s) ∈ k.geodesicFlowDomain ∧
            boundaryPhasePoint k σ v s = ρ (v, s + a) ∧
            ∀ w : E, (boundaryPhaseJacobiLinear k σ v s w : E) =
              boundaryJointJacobiLinear (I := 𝓘(ℝ, E)) ρ v (s + a) w) ∧
          ∀ v ∈ W, ∀ w : E, ∀ t : ℝ, (σ v, t) ∈ k.geodesicFlowDomain →
            IsJacobiAt k (fun r => boundaryPhasePoint k σ v r)
                (fun r => boundaryPhaseJacobiLinear k σ v r w) t ∧
              ContMDiffAt 𝓘(ℝ) (𝓘(ℝ, E)).tangent ∞
                (fun r => (⟨boundaryPhasePoint k σ v r,
                  boundaryPhaseJacobiLinear k σ v r w⟩ : TangentBundle 𝓘(ℝ, E) U)) t := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    birthPhaseContinuation_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  intro V ρ hρ hgeo v₀ a hva
  let R := fun q : E × ℝ => (ρ q : M)
  have hval := DifferentialGeometry.Manifold.contMDiff_intrinsicInterior_val I ∞
    birthPhaseContinuation_infty_ne_zero (M := M)
  have hR : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ)) I ∞ R V :=
    hval.comp_contMDiffOn hρ
  have henter : ∀ q ∈ V, I.IsInteriorPoint (R q) := fun q _hq => (ρ q).property
  have hRgeo : ∀ q ∈ V, HasGeodesicEquationAt g (fun r => R (q.1, r)) q.2 := by
    intro q hq
    have hslice : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞ (fun r => ρ (q.1, r)) q.2 :=
      (hρ.contMDiffAt (V.isOpen.mem_nhds hq)).comp q.2
        (contMDiffAt_const.prodMk contMDiffAt_id)
    exact (boundaryInteriorAtlas_geodesicEquation_iff g (fun r => ρ (q.1, r))
      q.2 hslice).mp (hgeo q hq)
  obtain ⟨σ, W₀, ε, hv₀, hε, hσ, hbase, hmatch⟩ :=
    boundary_original_phase_flow_matches g V R hR henter hRgeo v₀ a hva
  let W : Opens E := ⟨(W₀ : Set E) ∩ {v : E | (v, a) ∈ V},
    W₀.isOpen.inter (V.isOpen.preimage (continuous_id.prodMk continuous_const))⟩
  have hpoint (v : E) (hv : v ∈ W₀) (s : ℝ) (hs : s ∈ Metric.ball 0 ε) :
      boundaryPhasePoint k σ v s = ρ (v, s + a) :=
    Subtype.ext (hmatch v hv s hs).2
  refine ⟨σ, W, ε, ⟨hv₀, hva⟩, hε, hσ.mono inter_subset_left, ?_, ?_, ?_⟩
  · intro v hv
    exact ⟨hv.2, Subtype.ext (hbase v hv.1)⟩
  · intro v hv s hs
    refine ⟨(hmatch v hv.1 s hs).1, hpoint v hv.1 s hs, ?_⟩
    intro w
    have heq : (fun u => boundaryPhasePoint k σ u s) =ᶠ[𝓝 v]
        (fun u => ρ (u, s + a)) :=
      eventually_of_mem (W₀.isOpen.mem_nhds hv.1) (fun u hu => hpoint u hu s hs)
    have hd := heq.mfderiv_eq (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E))
    exact congrArg (fun A : E →L[ℝ] E => A w) hd
  · intro v hv w t ht
    exact boundaryPhaseJacobiLinear_jacobi k W₀ σ hσ v hv.1 w t ht

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
