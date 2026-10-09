import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorChartMap
import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryInteriorMetric
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open

/-!
The actual original true-interior chart is a local isometry into the genuine pole chart metric.
The tensor extension identity, original chart inverse and interior metric transport prove it.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [manifoldTopology : TopologicalSpace M] [manifoldCharts : ChartedSpace H M]
  [manifoldSmooth : IsManifold I ∞ M] [manifoldT2 : T2Space M]

private theorem interiorChartMetric_infty_ne_zero : (∞ : WithTop ℕ∞) ≠ 0 := by simp

theorem boundaryInteriorChart_metric_isometry
    (g : SmoothRiemannianMetric I M) (p : M)
    (G : SmoothRiemannianMetric 𝓘(ℝ, E) E) (O : Opens E)
    (hG : ∀ y ∈ (O : Set E) ∩ range I, ∀ w z : E,
      G.inner y w z = DifferentialGeometry.Geometry.Connection.metricFlatModelInChart
        g p y w z) :
    let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
      interiorChartMetric_infty_ne_zero (M := M)
    let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
    let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
    let k := boundaryInteriorAtlasMetric g
    let F := fun x : U => extChartAt I p (x : M)
    let S := {x : U | (x : M) ∈ (DifferentialGeometry.Manifold.interiorChart I ∞ p).source ∧
      F x ∈ O}
    IsOpen S ∧ IsLocalDiffeomorphOn 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ F S ∧
      ∀ x ∈ S, ∀ w z : TangentSpace 𝓘(ℝ, E) x,
        k.inner x w z = G.inner (F x) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) F x w)
          (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) F x z) := by
  let U := DifferentialGeometry.Manifold.intrinsicInterior I ∞
    interiorChartMetric_infty_ne_zero (M := M)
  let _interiorCharts := DifferentialGeometry.Manifold.interiorChartedSpace I ∞ (M := U)
  let _interiorSmooth := DifferentialGeometry.Manifold.interiorIsManifold I ∞ (M := U)
  let k := boundaryInteriorAtlasMetric g
  let F := fun x : U => extChartAt I p (x : M)
  let S₀ := {x : U | (x : M) ∈ (DifferentialGeometry.Manifold.interiorChart I ∞ p).source}
  let S := S₀ ∩ F ⁻¹' (O : Set E)
  dsimp only
  obtain ⟨hS₀, hF⟩ := boundaryInteriorChart_localDiffeomorph (I := I) p
  have hS : IsOpen S := hF.contMDiffOn.continuousOn.isOpen_inter_preimage hS₀ O.isOpen
  refine ⟨hS, (fun x => hF ⟨x.1, x.2.1⟩), ?_⟩
  intro x hx w z
  have htarget : F x ∈ interior (extChartAt I p).target :=
    (DifferentialGeometry.Manifold.interiorChart I ∞ p).map_source hx.1
  have hleft : (extChartAt I p).symm (F x) = (x : M) :=
    (DifferentialGeometry.Manifold.interiorChart I ∞ p).left_inv hx.1
  have hpoint := (hF ⟨x, hx.1⟩).contMDiffAt
  have hinverse : ContMDiffAt 𝓘(ℝ, E) I ∞ (extChartAt I p).symm (F x) :=
    (contMDiffOn_extChartAt_symm p).contMDiffAt
      (mem_interior_iff_mem_nhds.mp htarget)
  have hcolumn (u : TangentSpace 𝓘(ℝ, E) x) :
      mfderiv 𝓘(ℝ, E) I (extChartAt I p).symm (F x)
        (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) F x u) =
        mfderiv 𝓘(ℝ, E) I (Subtype.val : U → M) x u := by
    have hcomp := mfderiv_comp x (hinverse.mdifferentiableAt (by simp))
      (hpoint.mdifferentiableAt (by simp))
    have hcompApplied := congrArg (fun A : E →L[ℝ] E => A u) hcomp
    have hnear : ∀ᶠ q in 𝓝 x, q ∈ S₀ := hS₀.mem_nhds hx.1
    have heq : (fun q : U => (extChartAt I p).symm (F q)) =ᶠ[𝓝 x]
        (Subtype.val : U → M) := by
      filter_upwards [hnear] with q hq
      exact (DifferentialGeometry.Manifold.interiorChart I ∞ p).left_inv hq
    have hder := heq.mfderiv_eq (I := 𝓘(ℝ, E)) (I' := I)
    have hderApplied := congrArg (fun A : E →L[ℝ] E => A u) hder
    exact hcompApplied.symm.trans hderApplied
  have hk := boundaryInteriorAtlasMetric_inner g x w z
  have hc := boundaryChart_metric_inner_of_interior g p htarget
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) F x w) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) F x z)
  rw [hcolumn w, hcolumn z, hleft] at hc
  have hm := hG (F x) ⟨hx.2, extChartAt_target_subset_range p (interior_subset htarget)⟩
    (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) F x w) (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) F x z)
  exact hk.trans (hc.symm.trans hm.symm)

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
