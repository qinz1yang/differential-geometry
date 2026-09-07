import DifferentialGeometry.Geometry.Boundary.SurfaceMeasure
import DifferentialGeometry.Analysis.Integration.Measure.ChartIntegral
import DifferentialGeometry.Analysis.Integration.Measure.BoundaryDensity

noncomputable section

open Set Bundle Manifold MeasureTheory
open scoped Manifold ContDiff

namespace DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

open DifferentialGeometry.Integral.Measure

variable {n : Nat} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) ∞ M]
  [T2Space M] [SigmaCompactSpace M]

local notation "J" => modelWithCornersEuclideanHalfSpace (n + 1)
local notation "K" => HasSmoothBoundary.boundaryModel J
local notation "HB" => HasSmoothBoundary.boundaryModelH J

private local instance : Nonempty HB := ⟨(0 : EuclideanSpace Real (Fin n))⟩
private local instance euclideanMeasurableSpace (i : Type*) :
    MeasurableSpace (EuclideanSpace Real i) := borel _
private local instance euclideanBorelSpace (i : Type*) :
    BorelSpace (EuclideanSpace Real i) := ⟨rfl⟩
private local instance : MeasurableSpace (BoundaryManifold J M) := borel _
private local instance : BorelSpace (BoundaryManifold J M) := ⟨rfl⟩

theorem integral_surfaceMeasure_flux_eq_integral_chart_density
    (g : SmoothRiemannianMetric J M) (alpha : BoundaryManifold J M)
    (V : (x : BoundaryManifold J M) → TangentSpace J (x : M))
    {f : BoundaryManifold J M → Real} (hf : HasCompactSupport f)
    (hs : tsupport f ⊆ {x | (x : M) ∈ (chartAt (EuclideanHalfSpace (n + 1)) (alpha : M)).source})
    (hm : AEStronglyMeasurable
      (fun x => f x * g.inner (x : M) (outwardNormal (M := M) g x) (V x))
      (chartLocalMeasure (inducedMetric g) alpha)) :
    ∫ x, f x * g.inner (x : M) (outwardNormal (M := M) g x) (V x) ∂surfaceMeasure g =
      -∫ z in (extChartAt K alpha).target,
        ((MeasureTheory.Measure.addHaarScalarFactor
          (modelHaar (E := EuclideanSpace Real (Fin (n + 1)))) volume : Real) *
          chartDensity g (alpha : M) (((extChartAt K alpha).symm z : BoundaryManifold J M) : M)) *
          f ((extChartAt K alpha).symm z) *
          ((trivializationAt (EuclideanSpace Real (Fin (n + 1))) (TangentSpace J)
            (alpha : M)).continuousLinearMapAt Real
              (((extChartAt K alpha).symm z : BoundaryManifold J M) : M)
              (V ((extChartAt K alpha).symm z))) 0
              ∂(volume : MeasureTheory.Measure (EuclideanSpace Real (Fin n))) := by
  let : IsManifold K ∞ (BoundaryManifold J M) := BoundaryManifold.isManifold
  let F : BoundaryManifold J M → Real :=
    fun x => f x * g.inner (x : M) (outwardNormal (M := M) g x) (V x)
  have hFc : HasCompactSupport F := hf.mul_right
  have hFs : tsupport F ⊆ (chartAt HB alpha).source := by
    intro x hx
    have hxf := tsupport_mul_subset_left hx
    change x ∈ (BoundaryManifold.defaultBoundaryChart (I := J) alpha).source
    rw [BoundaryManifold.defaultBoundaryChart_eq_boundaryChart]
    exact hs hxf
  rw [surfaceMeasure_def]
  change (∫ x, F x ∂riemannianVolumeMeasure (I := K) (M := BoundaryManifold J M) (inducedMetric g)) = _
  rw [integral_riemannianVolumeMeasure_eq_chartDensity_of_tsupport_subset
    (inducedMetric g) alpha hFc hFs hm]
  rw [(modelHaar (E := EuclideanSpace Real (Fin n))).isAddLeftInvariant_eq_smul volume,
    MeasureTheory.Measure.restrict_smul, integral_smul_nnreal_measure]
  change (MeasureTheory.Measure.addHaarScalarFactor
    (modelHaar (E := EuclideanSpace Real (Fin n))) volume : Real) * _ = _
  rw [← integral_const_mul, ← integral_neg]
  apply setIntegral_congr_fun (measurableSet_extChartAt_target alpha)
  intro z hz
  let x : BoundaryManifold J M := (extChartAt K alpha).symm z
  have hxs : x ∈ (chartAt HB alpha).source := by
    simpa only [extChartAt_source] using (extChartAt K alpha).map_target hz
  have hx : (x : M) ∈ (chartAt (EuclideanHalfSpace (n + 1)) (alpha : M)).source := by
    change x ∈ (BoundaryManifold.defaultBoundaryChart (I := J) alpha).source at hxs
    rw [BoundaryManifold.defaultBoundaryChart_eq_boundaryChart] at hxs
    exact hxs
  have h := modelHaarScalarFactor_mul_inducedDensity_mul_outwardNormal_inner_chart_euclideanHalfSpace
    g alpha x hx (V x)
  change (MeasureTheory.Measure.addHaarScalarFactor
    (modelHaar (E := EuclideanSpace Real (Fin n))) volume : Real) *
    (chartDensity (inducedMetric g) alpha x *
      (f x * g.inner (x : M) (outwardNormal g x) (V x))) = _
  nlinarith [congrArg (fun t : Real => f x * t) h]

end DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
