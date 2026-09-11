import DifferentialGeometry.Geometry.Boundary.SurfaceMeasure
import DifferentialGeometry.Analysis.Integration.Measure.ChartIntegral
import DifferentialGeometry.Analysis.Integration.Measure.BoundaryDensity
import DifferentialGeometry.Geometry.Operator.DirectionalDerivative

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

local notation "V" => EuclideanSpace Real (Fin (n + 1))
local notation "W" => EuclideanSpace Real (Fin n)

private theorem volume_preserving_toLp_borel
    [m : MeasurableSpace W] [BorelSpace W] :
    MeasurePreserving (fun z : Fin n → Real => WithLp.toLp 2 z)
      volume (volume : MeasureTheory.Measure W) := by
  have hm : m = WithLp.measurableSpace 2 (Fin n → Real) :=
    BorelSpace.measurable_eq.trans
      (@BorelSpace.measurable_eq W _ (WithLp.measurableSpace 2 (Fin n → Real)) inferInstance).symm
  subst m
  exact PiLp.volume_preserving_toLp (Fin n)

theorem integral_surfaceMeasure_flux_eq_neg_integral_chartPullZero
    (g : SmoothRiemannianMetric J M) (alpha : BoundaryManifold J M)
    (X : Cₛ^∞⟮J; V, (TangentSpace J : M → Type _)⟯)
    {f : M → Real} (hf : Continuous f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ (chartAt (EuclideanHalfSpace (n + 1)) (alpha : M)).source) :
    ∫ x, f (x : M) * g.inner (x : M) (outwardNormal (M := M) g x) (X (x : M))
        ∂surfaceMeasure g =
      -((MeasureTheory.Measure.addHaarScalarFactor (modelHaar (E := V)) volume : Real) *
        ∫ z : Fin n → Real,
          chartPullZero (I := J) (alpha : M) f (WithLp.toLp 2 (Fin.cons 0 z)) *
          chartDensityOnE g (alpha : M) (WithLp.toLp 2 (Fin.cons 0 z)) *
          ((trivializationAt V (TangentSpace J) (alpha : M))
            ⟨(extChartAt J (alpha : M)).symm (WithLp.toLp 2 (Fin.cons 0 z)),
              X ((extChartAt J (alpha : M)).symm (WithLp.toLp 2 (Fin.cons 0 z)))⟩).2 0) := by
  have hbc : HasCompactSupport (fun x : BoundaryManifold J M => f (x : M)) :=
    hasCompactSupport_comp_boundaryInclusion hc
  have hbs : tsupport (fun x : BoundaryManifold J M => f (x : M)) ⊆
      {x | (x : M) ∈ (chartAt (EuclideanHalfSpace (n + 1)) (alpha : M)).source} := by
    intro x hx
    exact hs (tsupport_comp_subset_preimage f continuous_subtype_val hx)
  have hcont : Continuous (fun x : BoundaryManifold J M => f (x : M) *
      g.inner (x : M) (outwardNormal g x) (X (x : M))) :=
    (hf.comp (continuous_subtype_val :
      Continuous (fun x : BoundaryManifold J M => (x : M)))).mul
      (continuous_outwardNormal_inner_smoothSection g X)
  have hm : AEStronglyMeasurable
      (fun x : BoundaryManifold J M => f (x : M) *
        g.inner (x : M) (outwardNormal g x) (X (x : M)))
      (chartLocalMeasure (inducedMetric g) alpha) :=
    hcont.measurable.aestronglyMeasurable
  rw [integral_surfaceMeasure_flux_eq_integral_chart_density
    g alpha (fun x => X (x : M)) hbc hbs hm]
  congr 1
  let F : W → Real := fun z =>
    chartPullZero (I := J) (alpha : M) f (EuclideanHalfSpaceInstance.inclEuclideanCLM (n + 1) z) *
    chartDensityOnE g (alpha : M) (EuclideanHalfSpaceInstance.inclEuclideanCLM (n + 1) z) *
    ((trivializationAt V (TangentSpace J) (alpha : M))
      ⟨(extChartAt J (alpha : M)).symm (EuclideanHalfSpaceInstance.inclEuclideanCLM (n + 1) z),
        X ((extChartAt J (alpha : M)).symm
          (EuclideanHalfSpaceInstance.inclEuclideanCLM (n + 1) z))⟩).2 0
  have hFi : (∫ z : W, F z ∂(volume : MeasureTheory.Measure W)) =
      ∫ z : Fin n → Real,
        chartPullZero (I := J) (alpha : M) f (WithLp.toLp 2 (Fin.cons 0 z)) *
        chartDensityOnE g (alpha : M) (WithLp.toLp 2 (Fin.cons 0 z)) *
        ((trivializationAt V (TangentSpace J) (alpha : M))
          ⟨(extChartAt J (alpha : M)).symm (WithLp.toLp 2 (Fin.cons 0 z)),
            X ((extChartAt J (alpha : M)).symm (WithLp.toLp 2 (Fin.cons 0 z)))⟩).2 0 := by
    have hp : MeasurePreserving (fun z : Fin n → Real => WithLp.toLp 2 z)
        volume (volume : MeasureTheory.Measure W) := volume_preserving_toLp_borel
    have hemb : MeasurableEmbedding (fun z : Fin n → Real => WithLp.toLp 2 z) :=
      (EuclideanSpace.equiv (Fin n) Real).symm.toHomeomorph.measurableEmbedding
    have h := hp.integral_comp hemb F
    have hFincl (z : W) : F z =
        chartPullZero (I := J) (alpha : M) f (WithLp.toLp 2 (Fin.cons 0 z)) *
        chartDensityOnE g (alpha : M) (WithLp.toLp 2 (Fin.cons 0 z)) *
        ((trivializationAt V (TangentSpace J) (alpha : M))
          ⟨(extChartAt J (alpha : M)).symm (WithLp.toLp 2 (Fin.cons 0 z)),
            X ((extChartAt J (alpha : M)).symm (WithLp.toLp 2 (Fin.cons 0 z)))⟩).2 0 := by
      dsimp only [F]
      rw [EuclideanHalfSpaceInstance.inclEuclideanCLM_succ_apply]
    rw [← h]
    apply integral_congr_ae
    filter_upwards with z
    exact hFincl (WithLp.toLp 2 z)
  rw [← hFi, ← integral_const_mul]
  have hzero : ∀ z : W, z ∉ (extChartAt K alpha).target → F z = 0 := by
    intro z hz
    have hz' : EuclideanHalfSpaceInstance.inclEuclideanCLM (n + 1) z ∉
        (extChartAt J (alpha : M)).target :=
      fun h => hz ((inclEuclideanCLM_mem_extChartAt_target_iff alpha z).mp h)
    simp only [F, chartPullZero_nmem (alpha : M) f hz', zero_mul]
  have hrestrict := setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := (volume : MeasureTheory.Measure W))
    (f := fun z => (MeasureTheory.Measure.addHaarScalarFactor
      (modelHaar (E := V)) volume : Real) * F z)
    (fun z hz => by rw [hzero z hz, mul_zero])
  rw [← hrestrict]
  apply setIntegral_congr_fun (measurableSet_extChartAt_target alpha)
  intro z hz
  have hzt := (inclEuclideanCLM_mem_extChartAt_target_iff alpha z).mpr hz
  have hinv := extChartAt_symm_inclEuclideanCLM_eq_boundaryInclusion alpha hz
  have hxs : (((extChartAt K alpha).symm z : BoundaryManifold J M) : M) ∈
      (trivializationAt V (TangentSpace J) (alpha : M)).baseSet := by
    rw [trivializationAt_baseSet_eq_chartAt_source]
    have h := (extChartAt J (alpha : M)).map_target hzt
    rw [hinv, extChartAt_source] at h
    exact h
  dsimp only [F]
  rw [chartPullZero_mem (alpha : M) f hzt, scalarOnE_def]
  unfold chartDensityOnE
  rw [hinv, boundaryInclusion_apply,
    Trivialization.continuousLinearMapAt_apply_of_mem Real _ hxs]
  ring

end DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
