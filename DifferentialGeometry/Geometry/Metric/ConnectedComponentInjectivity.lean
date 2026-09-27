import DifferentialGeometry.Geometry.Metric.ConnectedComponentDistance
import DifferentialGeometry.Geometry.Metric.IntrinsicInjectivityRadius
import DifferentialGeometry.Geometry.Geodesic.Naturality.OpenSubtype

set_option autoImplicit false
noncomputable section

open Set Function Filter Bundle Manifold TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Riemannian

section RawExponential

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem expMapIntrinsic_restrictOpen_subtypeVal
    (U : Opens M) [SigmaCompactSpace U]
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [metricM : PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [@CompleteSpace M metricM.toUniformSpace]
    [IsContinuousRiemannianBundle E (TangentSpace I : M → Type _)]
    [RiemannianBundle (TangentSpace I : U → Type _)]
    [metricU : PseudoEMetricSpace U] [IsRiemannianManifold I U]
    [@CompleteSpace U metricU.toUniformSpace]
    [IsContinuousRiemannianBundle E (TangentSpace I : U → Type _)]
    (g : SmoothRiemannianMetric I M)
    (hnormM : IsMetricNorm (I := I) g)
    (hnormU : IsMetricNorm (I := I) (g.restrictOpen U))
    (x : U) (v : TangentSpace I x) :
    (expMapIntrinsic (M := U) (g.restrictOpen U) hnormU x v : M) =
      expMapIntrinsic g hnormM (x : M)
        (mfderiv I I (Subtype.val : U → M) x v) := by
  let γU : ℝ → U := intrinsicGeodesic (I := I) (M := U) (g.restrictOpen U) hnormU x v
  let γM : ℝ → M := intrinsicGeodesic g hnormM (x : M)
    (mfderiv I I (Subtype.val : U → M) x v)
  have hgeoU : IsGeodesic (g.restrictOpen U) γU :=
    intrinsicGeodesic_isGeodesic (I := I) (M := U) (g.restrictOpen U) hnormU x v
  have hgeoProj : IsGeodesic g (fun t => (γU t : M)) :=
    (geodesic_open_iff g U γU).mp hgeoU
  have hcontU : Continuous γU :=
    intrinsicGeodesic_continuous (I := I) (M := U) (g.restrictOpen U) hnormU x v
  have hc1U : ContMDiff 𝓘(ℝ) I 1 γU := by
    rw [← contMDiffOn_univ]
    exact intrinsicGeodesic_contMDiffOn (I := I) (M := U) (g.restrictOpen U) hnormU x v
  have hcomp :
      mfderiv 𝓘(ℝ) I ((Subtype.val : U → M) ∘ γU) 0 =
        (mfderiv I I (Subtype.val : U → M) (γU 0)).comp
          (mfderiv 𝓘(ℝ) I γU 0) :=
    mfderiv_comp 0 (hasMFDerivAt_subtype_val U (γU 0)).mdifferentiableAt
      (hc1U.mdifferentiableAt one_ne_zero)
  have hvProj :
      (mfderiv 𝓘(ℝ) I (fun t => (γU t : M)) 0 (1 : ℝ) : E) =
        (mfderiv I I (Subtype.val : U → M) x v : E) := by
    change mfderiv 𝓘(ℝ) I ((Subtype.val : U → M) ∘ γU) 0 1 = _
    rw [hcomp, ContinuousLinearMap.comp_apply, mfderiv_subtype_val_apply,
      mfderiv_subtype_val_apply]
    exact intrinsicGeodesic_mfderiv_zero (I := I) (M := U) (g.restrictOpen U) hnormU x v
  have hvM :
      (mfderiv 𝓘(ℝ) I γM 0 (1 : ℝ) : E) =
        (mfderiv I I (Subtype.val : U → M) x v : E) :=
    intrinsicGeodesic_mfderiv_zero g hnormM (x : M)
      (mfderiv I I (Subtype.val : U → M) x v)
  have h0 : (γU 0 : M) = γM 0 := by
    dsimp only [γU, γM]
    rw [intrinsicGeodesic_zero, intrinsicGeodesic_zero]
  have heq : (fun t => (γU t : M)) = γM :=
    isGeodesic_eq_of_initial g hgeoProj
      (intrinsicGeodesic_isGeodesic g hnormM (x : M)
        (mfderiv I I (Subtype.val : U → M) x v))
      (continuous_subtype_val.comp hcontU)
      (intrinsicGeodesic_continuous g hnormM (x : M)
        (mfderiv I I (Subtype.val : U → M) x v))
      h0 (hvProj.trans hvM.symm)
  exact congrFun heq 1

end RawExponential

section ComponentRadius

variable {E H M : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [FiniteDimensional ℝ E]
  [IsManifold I ∞ M] [T2Space M] in
private local instance componentSigmaCompact (p : M) :
    SigmaCompactSpace (connectedComponentOpen (I := I) p) :=
  (isClosed_connectedComponent (x := p)).sigmaCompactSpace

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [SigmaCompactSpace M] in
private theorem component_normalFrame_isometry
    (g : SmoothRiemannianMetric I M) (U : Opens M) (x : U) :
    ∃ A : E ≃ₗᵢ[ℝ] E, ∀ z : E,
      normalFrame g (x : M) (A z) =
        mfderiv I I (Subtype.val : U → M) x
          (normalFrame (g.restrictOpen U) x z) := by
  let LC : E ≃ₗ[ℝ] E := (normalFrame (g.restrictOpen U) x).toLinearEquiv
  let LM : E ≃ₗ[ℝ] E := (normalFrame g (x : M)).toLinearEquiv
  let T : E ≃ₗ[ℝ] E := LC.trans LM.symm
  have hframe (z : E) : normalFrame g (x : M) (T z) =
      normalFrame (g.restrictOpen U) x z := by
    change normalFrame g (x : M)
      ((normalFrame g (x : M)).symm (normalFrame (g.restrictOpen U) x z)) = _
    exact (normalFrame g (x : M)).apply_symm_apply _
  have hnorm (z : E) : ‖T z‖ = ‖z‖ := by
    calc
      ‖T z‖ = Real.sqrt (g.inner (x : M)
          (normalFrame g (x : M) (T z))
          (normalFrame g (x : M) (T z))) :=
        (normalFrame_sqrt g (x : M) (T z)).symm
      _ = Real.sqrt ((g.restrictOpen U).inner x
          (normalFrame (g.restrictOpen U) x z)
          (normalFrame (g.restrictOpen U) x z)) := by
        rw [hframe, SmoothRiemannianMetric.restrictOpen_inner]
      _ = ‖z‖ := normalFrame_sqrt (g.restrictOpen U) x z
  refine ⟨{ toLinearEquiv := T, norm_map' := hnorm }, ?_⟩
  intro z
  rw [mfderiv_subtype_val_apply]
  exact hframe z

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem intrinsicInjectivityRadiusOf_le_restrictOpen_connCompOpen
    (g : SmoothRiemannianMetric I M) (hg : RiemannianMetricComplete g)
    (p : M) (x : connectedComponentOpen (I := I) p) :
    intrinsicInjectivityRadiusOf g hg (x : M) ≤
      intrinsicInjectivityRadiusOf (g.restrictOpen (connectedComponentOpen (I := I) p))
        (riemannianMetricComplete_restrictOpen_connCompOpen g p hg) x := by
  let C := connectedComponentOpen (I := I) p
  let gC : SmoothRiemannianMetric I C := g.restrictOpen C
  have hgC : RiemannianMetricComplete gC :=
    riemannianMetricComplete_restrictOpen_connCompOpen g p hg
  let : MetrizableSpace M := Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨g.inner, g.contMDiff.continuous, fun _ _ _ => rfl⟩
  let metricM : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : PseudoEMetricSpace M := metricM.toPseudoEMetricSpace
  let : @CompleteSpace M metricM.toUniformSpace := hg.complete
  have hnormM : ∀ (q : M) (v : TangentSpace I q),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner q v v)) :=
    fun q v => tensor0SBundle_enorm_eq_riemannianBundle_enorm g q v
  let : MetrizableSpace C := Manifold.metrizableSpace I C
  let : T3Space C := inferInstance
  let : RiemannianBundle (TangentSpace I : C → Type _) :=
    ⟨gC.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (TangentSpace I : C → Type _) :=
    ⟨gC.inner, gC.contMDiff.continuous, fun _ _ _ => rfl⟩
  let metricC : EMetricSpace C := EMetricSpace.ofRiemannianMetric I C
  let : PseudoEMetricSpace C := metricC.toPseudoEMetricSpace
  let : @CompleteSpace C metricC.toUniformSpace := hgC.complete
  have hnormC : ∀ (q : C) (v : TangentSpace I q),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gC.inner q v v)) :=
    fun q v => tensor0SBundle_enorm_eq_riemannianBundle_enorm gC q v
  change intrinsicInjRadius g hnormM (x : M) ≤ intrinsicInjRadius gC hnormC x
  obtain ⟨A, hA⟩ := component_normalFrame_isometry g C x
  have hmap (z : E) : (intrinsicFramedExp (M := C) gC hnormC x z : M) =
      intrinsicFramedExp g hnormM (x : M) (A z) := by
    rw [intrinsicFrame_apply, intrinsicFrame_apply, hA]
    exact expMapIntrinsic_restrictOpen_subtypeVal C g hnormM hnormC x
      (normalFrame gC x z)
  have hAedist (z : E) : edist (A z) (0 : E) = edist z 0 := by
    simpa only [A.map_zero] using A.isometry.edist_eq z (0 : E)
  change sSup (intrinsicInjRadiusSet g hnormM (x : M)) ≤
    sSup (intrinsicInjRadiusSet gC hnormC x)
  apply sSup_le_sSup
  intro r hr
  change InjOn (intrinsicFramedExp g hnormM (x : M)) (Metric.eball (0 : E) r) at hr
  change InjOn (intrinsicFramedExp gC hnormC x) (Metric.eball (0 : E) r)
  intro z hz w hw heq
  apply A.injective
  apply hr
  · simpa only [Metric.mem_eball, hAedist] using hz
  · simpa only [Metric.mem_eball, hAedist] using hw
  · exact (hmap z).symm.trans
      ((congrArg (Subtype.val : C → M) heq).trans (hmap w))

end ComponentRadius

end DifferentialGeometry.Geometry.Riemannian

end
