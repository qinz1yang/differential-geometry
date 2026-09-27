import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.LocalFormula
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.Global
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.EuclideanHalfSpace
import DifferentialGeometry.Analysis.Integration.Measure.Boundary
import DifferentialGeometry.Geometry.Boundary.Model.EuclideanHalfSpace
import DifferentialGeometry.Geometry.Operator.DirectionalDerivative
import DifferentialGeometry.Analysis.Integration.Measure.ChartIntegral
import DifferentialGeometry.Analysis.Integration.Measure.SurfaceFlux

open Bundle Manifold Set MeasureTheory
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

open DifferentialGeometry.Integral.Measure DifferentialGeometry.Analysis

variable {n : Nat} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) ∞ M]

local notation "J" => modelWithCornersEuclideanHalfSpace (n + 1)
local notation "V" => EuclideanSpace Real (Fin (n + 1))

private local instance : MeasurableSpace V := borel _
private local instance : BorelSpace V := ⟨rfl⟩

theorem integral_chartDensity_mul_localDivergenceWithin_add_tangentSectionAction_eq_face
    (g : SmoothRiemannianMetric J M) (alpha : M)
    (X : Cₛ^∞⟮J; V, (TangentSpace J : M → Type _)⟯)
    {f : M → Real} (hf : ContMDiff J 𝓘(Real) ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ (chartAt (EuclideanHalfSpace (n + 1)) alpha).source) :
    ∫ y in (extChartAt J alpha).target, chartDensityOnE g alpha y *
        (f ((extChartAt J alpha).symm y) *
          localDivergenceWithin g alpha X ((extChartAt J alpha).symm y) +
            tangentSectionAction X f ((extChartAt J alpha).symm y)) ∂modelHaar =
      -((MeasureTheory.Measure.addHaarScalarFactor (modelHaar (E := V)) volume : Real) *
        ∫ z : Fin n → Real,
          chartPullZero (I := J) alpha f (WithLp.toLp 2 (Fin.cons 0 z)) *
          chartDensityOnE g alpha (WithLp.toLp 2 (Fin.cons 0 z)) *
          ((trivializationAt V (TangentSpace J) alpha)
            ⟨(extChartAt J alpha).symm (WithLp.toLp 2 (Fin.cons 0 z)),
              X ((extChartAt J alpha).symm (WithLp.toLp 2 (Fin.cons 0 z)))⟩).2 0) := by
  let U : Set V := (modelWithCornersEuclideanHalfSpace (n + 1)).symm ⁻¹'
    (chartAt (EuclideanHalfSpace (n + 1)) alpha).target
  let rho : V → Real := chartDensityOnE g alpha
  let phi : V → Real := chartPullZero (I := J) alpha f
  let u : V → V := fun y => ((trivializationAt V (TangentSpace J) alpha)
    ⟨(extChartAt J alpha).symm y, X ((extChartAt J alpha).symm y)⟩).2
  have hU : IsOpen U :=
    (chartAt (EuclideanHalfSpace (n + 1)) alpha).open_target.preimage
      (modelWithCornersEuclideanHalfSpace (n + 1)).continuous_symm
  have htarget : (extChartAt J alpha).target = U ∩ {y : V | 0 ≤ y 0} := by
    rw [extChartAt_target, range_modelWithCornersEuclideanHalfSpace]
  have hopen : IsOpen (U ∩ {y : V | 0 < y 0}) :=
    hU.inter (isOpen_lt continuous_const (PiLp.continuous_apply 2 _ 0))
  have hsub : U ∩ {y : V | 0 < y 0} ⊆ (extChartAt J alpha).target := by
    rw [htarget]
    exact fun y hy => ⟨hy.1, show 0 ≤ y 0 from le_of_lt hy.2⟩
  have hphi : ContDiffOn Real 1 phi (U ∩ {y : V | 0 ≤ y 0}) := by
    rw [← htarget]
    exact (chartPullZero_contDiffOn alpha hf).of_le (by simp)
  have hu : ContDiffOn Real 1 (fun y => rho y • u y) (U ∩ {y : V | 0 ≤ y 0}) := by
    rw [← htarget]
    let b := DifferentialGeometry.Tensor.Coordinates.chartModelBasis V
    have heq : (fun y => rho y • u y) = fun y =>
        ∑ i, (chartCoeffOnE alpha X i y * chartDensityOnE g alpha y) • b i := by
      funext y
      rw [← b.sum_repr (rho y • u y)]
      apply Finset.sum_congr rfl
      intro i _
      congr 1
      simp only [rho, u, map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact mul_comm _ _
    rw [heq]
    exact (ContDiffOn.sum fun i _ =>
      (chartCoeffOnE_mul_chartDensityOnE_contDiffOn g alpha X i).smul contDiffOn_const).of_le (by simp)
  have hrho : AEMeasurable rho
      ((modelHaar (E := V)).restrict (U ∩ {y : V | 0 < y 0})) :=
    ((chartDensityOnE_contDiffOn g alpha).continuousOn.mono hsub).aemeasurable hopen.measurableSet
  have hpos : ∀ᵐ y ∂((modelHaar (E := V)).restrict (U ∩ {y : V | 0 < y 0})), 0 < rho y := by
    filter_upwards [ae_restrict_mem hopen.measurableSet] with y hy
    exact chartDensity_pos g alpha (by
      rw [trivializationAt_baseSet_eq_chartAt_source]
      simpa only [extChartAt_source] using (extChartAt J alpha).map_target (hsub hy))
  have hphic : HasCompactSupport phi := hasCompactSupport_chartPullZero alpha hc hs
  have hcs : HasCompactSupport (fun y => phi y • (rho y • u y)) := hphic.smul_right
  have hsupp : tsupport (fun y => phi y • (rho y • u y)) ∩ {y : V | 0 ≤ y 0} ⊆ U := by
    intro y hy
    have hyt := tsupport_chartPullZero_subset_target alpha hc hs
      (tsupport_smul_subset_left phi (fun z => rho z • u z) hy.1)
    rw [htarget] at hyt
    exact hyt.1
  have hflux :=
    integral_mul_trace_fderivWithin_add_fderivWithin_withDensity_euclidean_half_space_inter_of_hasCompactSupport
      hU hphi hrho hu hpos hcs hsupp
  rw [integral_withDensity_eq_integral_toReal_smul₀ hrho.ennreal_ofReal
    (by filter_upwards with y; exact ENNReal.ofReal_lt_top) _] at hflux
  have hzero : (modelHaar (E := V)) {y : V | y 0 = 0} = 0 := by
    simpa only [EuclideanHalfSpaceInstance.frontier_range_modelWithCornersEuclideanHalfSpace_eq]
      using (modelHaar_frontier_range_eq_zero (I := J))
  have hae : (extChartAt J alpha).target =ᵐ[modelHaar] (U ∩ {y : V | 0 < y 0} : Set V) := by
    rw [htarget]
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero] with y hy
    change y 0 ≠ 0 at hy
    change (y ∈ U ∧ 0 ≤ y 0) = (y ∈ U ∧ 0 < y 0)
    exact propext (and_congr_right fun _ => ⟨fun h => lt_of_le_of_ne h (Ne.symm hy), le_of_lt⟩)
  rw [setIntegral_congr_set hae]
  calc
    _ = ∫ y in U ∩ {y : V | 0 < y 0},
        (ENNReal.ofReal (rho y)).toReal •
          (phi y * (LinearMap.trace Real V
            (fderivWithin Real (fun z => rho z • u z) (U ∩ {z : V | 0 ≤ z 0}) y).toLinearMap /
              rho y) + fderivWithin Real phi (U ∩ {z : V | 0 ≤ z 0}) y (u y))
        ∂modelHaar := by
      apply setIntegral_congr_fun hopen.measurableSet
      intro y hy
      dsimp only
      have hyt := hsub hy
      have hys := (extChartAt J alpha).map_target hyt
      have hys' : (extChartAt J alpha).symm y ∈
          (chartAt (EuclideanHalfSpace (n + 1)) alpha).source := by
        simpa only [extChartAt_source] using hys
      have hybase : (extChartAt J alpha).symm y ∈
          (trivializationAt V (TangentSpace J) alpha).baseSet := by
        rw [trivializationAt_baseSet_eq_chartAt_source]
        exact hys'
      have hrp : 0 < rho y := chartDensity_pos g alpha hybase
      rw [ENNReal.toReal_ofReal hrp.le, smul_eq_mul, ← htarget]
      have hdiv := localDivergenceWithin_eq_trace_fderivWithin g alpha X hys'
      rw [(extChartAt J alpha).right_inv hyt] at hdiv
      rw [hdiv]
      have hact := tangentSectionAction_eq_fderivWithin_scalarOnE alpha X hys'
        (hf.mdifferentiableAt (by simp))
      rw [(extChartAt J alpha).right_inv hyt] at hact
      rw [hact, Trivialization.continuousLinearMapAt_apply_of_mem Real _ hybase]
      have hderiv : fderivWithin Real phi (extChartAt J alpha).target y =
          fderivWithin Real (scalarOnE (I := J) alpha f) (extChartAt J alpha).target y :=
        fderivWithin_congr' (fun z hz => chartPullZero_mem alpha f hz) hyt
      rw [hderiv, show phi y = f ((extChartAt J alpha).symm y) from chartPullZero_mem alpha f hyt]
      rfl
    _ = _ := hflux

variable [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace M := borel _
private local instance : BorelSpace M := ⟨rfl⟩

theorem integral_mul_localDivergenceWithin_add_tangentSectionAction_eq_surfaceMeasure_flux
    (g : SmoothRiemannianMetric J M) (alpha : BoundaryManifold J M)
    (X : Cₛ^∞⟮J; V, (TangentSpace J : M → Type _)⟯)
    {f : M → Real} (hf : ContMDiff J 𝓘(Real) ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ (chartAt (EuclideanHalfSpace (n + 1)) (alpha : M)).source) :
    ∫ x, f x * localDivergenceWithin g (alpha : M) X x + tangentSectionAction X f x
        ∂riemannianVolumeMeasure (I := J) (M := M) g =
      ∫ x, f (x : M) * g.inner (x : M) (outwardNormal (M := M) g x) (X (x : M))
        ∂surfaceMeasure g := by
  let F : M → Real := fun x =>
    f x * localDivergenceWithin g (alpha : M) X x + tangentSectionAction X f x
  have hactzero (x : M) (hx : x ∉ tsupport f) : tangentSectionAction X f x = 0 := by
    change mfderiv J 𝓘(Real) f x (X x) = 0
    rw [(notMem_tsupport_iff_eventuallyEq.mp hx).mfderiv_eq]
    change mfderiv J 𝓘(Real) (fun _ : M => (0 : Real)) x (X x) = 0
    rw [mfderiv_const]
    rfl
  have hzero (x : M) (hx : x ∉ tsupport f) : F x = 0 := by
    dsimp only [F]
    rw [image_eq_zero_of_notMem_tsupport hx, hactzero x hx, zero_mul, zero_add]
  have hFs : tsupport F ⊆ tsupport f := by
    apply closure_minimal _ (isClosed_tsupport f)
    intro x hx
    by_contra hxf
    exact hx (hzero x hxf)
  have hFc : HasCompactSupport F := hc.of_isClosed_subset (isClosed_tsupport F) hFs
  have hFsource : tsupport F ⊆ (chartAt (EuclideanHalfSpace (n + 1)) (alpha : M)).source :=
    hFs.trans hs
  have hFcont : Continuous F := by
    apply continuous_iff_continuousAt.mpr
    intro x
    by_cases hx : x ∈ (chartAt (EuclideanHalfSpace (n + 1)) (alpha : M)).source
    · exact (hf.continuous.continuousAt.mul
        ((localDivergenceWithin_continuousOn g (alpha : M) X).continuousAt
          ((chartAt (EuclideanHalfSpace (n + 1)) (alpha : M)).open_source.mem_nhds hx))).add
          (tangentSectionAction_contMDiff X hf).continuous.continuousAt
    · have hxF : x ∉ tsupport F := fun h => hx (hFsource h)
      exact continuousAt_const.congr_of_eventuallyEq
        (notMem_tsupport_iff_eventuallyEq.mp hxF)
  change (∫ x, F x ∂riemannianVolumeMeasure (I := J) (M := M) g) = _
  rw [integral_riemannianVolumeMeasure_eq_chartDensity_of_tsupport_subset
    g (alpha : M) hFc hFsource hFcont.measurable.aestronglyMeasurable]
  change (∫ y in (extChartAt J (alpha : M)).target, chartDensityOnE g (alpha : M) y *
    (f ((extChartAt J (alpha : M)).symm y) *
      localDivergenceWithin g (alpha : M) X ((extChartAt J (alpha : M)).symm y) +
        tangentSectionAction X f ((extChartAt J (alpha : M)).symm y)) ∂modelHaar) = _
  rw [integral_chartDensity_mul_localDivergenceWithin_add_tangentSectionAction_eq_face
    g (alpha : M) X hf hc hs]
  exact (integral_surfaceMeasure_flux_eq_neg_integral_chartPullZero
    g alpha X hf.continuous hc hs).symm

theorem integral_mul_divergence_g_with_boundary_add_tangentSectionAction_eq_surfaceMeasure_flux_of_tsupport_subset
    (g : SmoothRiemannianMetric J M) (alpha : BoundaryManifold J M)
    (X : Cₛ^∞⟮J; V, (TangentSpace J : M → Type _)⟯)
    {f : M → Real} (hf : ContMDiff J 𝓘(Real) ∞ f) (hc : HasCompactSupport f)
    (hs : tsupport f ⊆ (chartAt (EuclideanHalfSpace (n + 1)) (alpha : M)).source) :
    ∫ x, f x * divergenceGWithBoundary g X x + tangentSectionAction X f x
        ∂riemannianVolumeMeasure (I := J) (M := M) g =
      ∫ x, f (x : M) * g.inner (x : M) (outwardNormal (M := M) g x) (X (x : M))
        ∂surfaceMeasure g := by
  rw [← integral_mul_localDivergenceWithin_add_tangentSectionAction_eq_surfaceMeasure_flux
    g alpha X hf hc hs]
  apply integral_congr_ae
  filter_upwards with x
  by_cases hx : f x = 0
  · simp only [hx, zero_mul]
  · rw [voss_weyl_divergence_with_boundary_formula g (alpha : M) X
      (hs (subset_tsupport f hx))]


end DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
