import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryOriginalPhaseMatching
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryPhaseJacobiVariation

/-!
Actual native phase Jacobi fields map to the original family's angular derivative.
All angular directions share one actual ray seed and one original/native matching interval.
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

private theorem angularJacobi_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem boundary_original_phase_angular_jacobi (g : SmoothRiemannianMetric I M)
    (V : Opens (E × ℝ)) (R : E × ℝ → M)
    (hR : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ)) I ∞ R V)
    (henter : ∀ q ∈ V, I.IsInteriorPoint (R q))
    (hgeo : ∀ q ∈ V, HasGeodesicEquationAt g (fun t => R (q.1, t)) q.2)
    (v₀ : E) (a : ℝ) (hva : (v₀, a) ∈ V) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      angularJacobi_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    ∃ seed : TangentBundle 𝓘(ℝ, E) U, ∃ ε : ℝ, 0 < ε ∧
      ∀ w : E, ∃ ζ : ℝ → TangentBundle 𝓘(ℝ, E) U,
      ζ 0 = seed ∧ ContMDiff 𝓘(ℝ) (𝓘(ℝ, E)).tangent ∞ ζ ∧
      (∀ t ∈ Metric.ball (0 : ℝ) ε,
        (ζ 0, t) ∈ k.geodesicFlowDomain ∧
        ((boundaryFlowVariation k ζ 0 t : U) : M) = R (v₀, t + a) ∧
        (mfderiv 𝓘(ℝ, E) I (Subtype.val : U → M) (boundaryFlowVariation k ζ 0 t)
          (boundaryFlowJacobiField k ζ t) : E) =
          mfderiv 𝓘(ℝ) I (fun s : ℝ => R (v₀ + s • w, t + a)) 0 (1 : ℝ)) ∧
      ∀ t : ℝ, (ζ 0, t) ∈ k.geodesicFlowDomain →
        IsJacobiAt k (fun s => boundaryFlowVariation k ζ 0 s)
          (boundaryFlowJacobiField k ζ) t ∧
        ContMDiffAt 𝓘(ℝ) (𝓘(ℝ, E)).tangent ∞
          (fun s => (⟨boundaryFlowVariation k ζ 0 s,
            boundaryFlowJacobiField k ζ s⟩ : TangentBundle 𝓘(ℝ, E) U)) t := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    angularJacobi_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  dsimp only
  obtain ⟨σ, W, ε, hW, hε, hσ, _hbase, hmatch⟩ :=
    boundary_original_phase_flow_matches g V R hR henter hgeo v₀ a hva
  refine ⟨σ v₀, ε, hε, ?_⟩
  intro w
  obtain ⟨ζ, hζ, hζzero, hζgerm, hJac⟩ :=
    boundary_phase_local_variation_jacobi k W σ hσ v₀ w hW
  let D : Set ℝ := {s | v₀ + s • w ∈ W}
  have hDopen : IsOpen D := W.isOpen.preimage
    (continuous_const.add (continuous_id.smul continuous_const))
  have hDzero : (0 : ℝ) ∈ D := by
    change v₀ + (0 : ℝ) • w ∈ W
    simpa only [zero_smul, add_zero] using hW
  have hrange : ∀ᶠ s in 𝓝 (0 : ℝ), v₀ + s • w ∈ W := hDopen.mem_nhds hDzero
  have hpointGerm (t : ℝ) (ht : t ∈ Metric.ball 0 ε) :
      (fun s => ((boundaryFlowVariation k ζ s t : U) : M)) =ᶠ[𝓝 (0 : ℝ)]
        (fun s => R (v₀ + s • w, t + a)) := by
    filter_upwards [hζgerm, hrange] with s hs hsw
    change ((k.geodesicFlow (ζ s) t).proj : M) = R (v₀ + s • w, t + a)
    rw [hs]
    exact (hmatch (v₀ + s • w) hsw t ht).2
  have hval := DifferentialGeometry.Manifold.contMDiff_intrinsicInterior_val
    I ∞ angularJacobi_infty_ne_zero (M := M)
  have hproj : ContMDiff (𝓘(ℝ, E)).tangent 𝓘(ℝ, E) ∞
      (TotalSpace.proj : TangentBundle 𝓘(ℝ, E) U → U) :=
    contMDiff_proj (TangentSpace 𝓘(ℝ, E) : U → Type _)
  have hfoot := hproj.comp_contMDiffOn (k.contMDiffOn_geodesicFlow (r := ⊤) le_top)
  have kopen := k.isOpen_geodesicFlowDomain (r := ⊤) le_top
  refine ⟨ζ, hζzero, hζ, ?_, hJac⟩
  intro t ht
  have hdom : (ζ 0, t) ∈ k.geodesicFlowDomain := by
    rw [hζzero]
    exact (hmatch v₀ hW t ht).1
  have hpoint : ((boundaryFlowVariation k ζ 0 t : U) : M) = R (v₀, t + a) := by
    simpa only [zero_smul, add_zero] using (hpointGerm t ht).eq_of_nhds
  have hphase : ContMDiff 𝓘(ℝ) ((𝓘(ℝ, E)).tangent.prod 𝓘(ℝ)) ∞
      (fun s : ℝ => (ζ s, t)) := hζ.prodMk contMDiff_const
  have hnew : ContMDiffAt 𝓘(ℝ) 𝓘(ℝ, E) ∞ (fun s => boundaryFlowVariation k ζ s t) 0 :=
    (hfoot.contMDiffAt (kopen.mem_nhds hdom)).comp (f := fun s : ℝ => (ζ s, t)) 0
      hphase.contMDiffAt
  have hvalAt : MDifferentiableAt 𝓘(ℝ, E) I (Subtype.val : U → M)
      (boundaryFlowVariation k ζ 0 t) :=
    (hval.contMDiffAt (x := boundaryFlowVariation k ζ 0 t)).mdifferentiableAt (by simp)
  have hcomp := mfderiv_comp (0 : ℝ) hvalAt (hnew.mdifferentiableAt (by simp))
  have happ := congrArg (fun A : ℝ →L[ℝ] E => A (1 : ℝ)) hcomp
  have hchain : (mfderiv 𝓘(ℝ) I (fun s => ((boundaryFlowVariation k ζ s t : U) : M))
      0 (1 : ℝ) : E) =
      mfderiv 𝓘(ℝ, E) I (Subtype.val : U → M) (boundaryFlowVariation k ζ 0 t)
        (boundaryFlowJacobiField k ζ t) := happ
  have hder : mfderiv 𝓘(ℝ) I (fun s => ((boundaryFlowVariation k ζ s t : U) : M)) 0 =
      mfderiv 𝓘(ℝ) I (fun s : ℝ => R (v₀ + s • w, t + a)) 0 :=
    (hpointGerm t ht).mfderiv_eq
  have hderApplied := congrArg (fun A : ℝ →L[ℝ] E => A (1 : ℝ)) hder
  exact ⟨hdom, hpoint, hchain.symm.trans hderApplied⟩

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
