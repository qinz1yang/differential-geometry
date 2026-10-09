import DifferentialGeometry.Geometry.Geodesic.Naturality.OpenSubtype
import DifferentialGeometry.Topology.Manifold.InteriorChart

/-!
Geodesic equations restrict to genuine open subsets at interior points of manifolds
with boundary. The ordinary coefficient germ is justified by interior membership.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Riemannian.Geodesic

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [manifoldTopology : TopologicalSpace M]
  [manifoldCharts : ChartedSpace H M] [manifoldSmooth : IsManifold I ∞ M]

private theorem boundaryOpen_gram_germ (g : SmoothRiemannianMetric I M)
    (U : Opens M) [openSeparated : T2Space U] (a : U)
    (ha : I.IsInteriorPoint (a : M)) (i j : Fin (Module.finrank ℝ E)) :
    chartGramOnE (g.restrictOpen U) a i j =ᶠ[𝓝 (extChartAt I a a)]
      chartGramOnE g (a : M) i j := by
  let openNonempty : Nonempty U := ⟨a⟩
  have haU : I.IsInteriorPoint a := I.isInteriorPoint_iff_isInteriorPoint_val.mpr ha
  have htarget : (extChartAt I a).target ∈ 𝓝 (extChartAt I a a) :=
    mem_interior_iff_mem_nhds.mp (I.isInteriorPoint_iff.mp haU)
  filter_upwards [htarget] with y hy
  let x : U := (extChartAt I a).symm y
  have hx : (x : M) ∈ (chartAt H (a : M)).source := by
    have hs := (extChartAt I a).map_target hy
    rw [extChartAt_source, Opens.chartAt_eq,
      OpenPartialHomeomorph.subtypeRestr_source] at hs
    exact hs
  have hval : (x : M) = (extChartAt I (a : M)).symm y := by
    have hc : extChartAt I (a : M) (x : M) = y :=
      (extChartAt I a).right_inv hy
    rw [← hc, (extChartAt I (a : M)).left_inv
      (by simpa only [extChartAt_source] using hx)]
  change chartGramMatrix (g.restrictOpen U) a x i j =
    chartGramMatrix g (a : M) ((extChartAt I (a : M)).symm y) i j
  rw [← hval]
  exact chartGram_open g U a x hx i j

theorem boundaryOpen_christoffel (g : SmoothRiemannianMetric I M)
    (U : Opens M) [openSeparated : T2Space U] (a : U)
    (ha : I.IsInteriorPoint (a : M)) (i j k : Fin (Module.finrank ℝ E)) :
    chartChristoffel (g.restrictOpen U) a i j k (extChartAt I a a) =
      chartChristoffel g (a : M) i j k (extChartAt I (a : M) (a : M)) := by
  have hgram : chartGramMatrix (g.restrictOpen U) a a =
      chartGramMatrix g (a : M) (a : M) := by
    ext r s
    exact chartGram_open g U a a (mem_chart_source H (a : M)) r s
  have hinv : chartInvGramMatrix (g.restrictOpen U) a a =
      chartInvGramMatrix g (a : M) (a : M) := congrArg (fun A => A⁻¹) hgram
  have hpartial (r s q : Fin (Module.finrank ℝ E)) :
      partialDeriv r (chartGramOnE (g.restrictOpen U) a s q) (extChartAt I a a) =
        partialDeriv r (chartGramOnE g (a : M) s q) (extChartAt I a a) :=
    congrArg (fun D : E →L[ℝ] ℝ => D (chartModelBasis E r))
      (boundaryOpen_gram_germ g U a ha s q).fderiv_eq
  simp only [chartChristoffel_def, extChartAt_to_inv, hinv, hpartial]
  rfl

theorem boundaryOpen_geodesicEquation_iff {g : SmoothRiemannianMetric I M}
    {U : Opens M} [openSeparated : T2Space U] {γ : ℝ → U} {t : ℝ}
    (ht : I.IsInteriorPoint (γ t : M)) :
    HasGeodesicEquationAt (g.restrictOpen U) γ t ↔
      HasGeodesicEquationAt g (fun s => (γ s : M)) t := by
  have hcontr (v : E) :
      chartChristoffelContraction (g.restrictOpen U) (γ t) v v
          (extChartAt I (γ t) (γ t)) =
        chartChristoffelContraction g (γ t : M) v v
          (extChartAt I (γ t : M) (γ t : M)) := by
    simp only [chartChristoffelContraction_def, boundaryOpen_christoffel g U (γ t) ht]
  have hcurve : chartLocalCurve (I := I) γ t =
      chartLocalCurve (I := I) (fun s => (γ s : M)) t := by
    funext s
    change extChartAt I (γ t) (γ s) = extChartAt I (γ t : M) (γ s : M)
    rfl
  simp only [HasGeodesicEquationAt, hcurve, hcontr]

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
