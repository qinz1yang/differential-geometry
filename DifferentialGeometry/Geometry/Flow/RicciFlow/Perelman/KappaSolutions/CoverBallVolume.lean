import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ModelWitness
import DifferentialGeometry.Geometry.Metric.UniversalCover.Completeness
import DifferentialGeometry.Geometry.Metric.UniversalCover.Metric
import DifferentialGeometry.Topology.Covering.Smooth.LocalDiffeomorph
import DifferentialGeometry.Topology.Covering.SmoothLift
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import Mathlib.Geometry.Manifold.Instances.Icc

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open MeasureTheory Set Bundle Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Topology
open DifferentialGeometry.Integral.Measure
open CanonicalNeighborhood
open scoped Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
  [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M] [Inhabited M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [ConnectedSpace M] in
theorem universalCover_image_ball_liftedMetric
    (g : SmoothRiemannianMetric I M) (x : UniversalCover M)
    (r : ℝ) (hr : 0 < r) :
    (UniversalCover.proj : UniversalCover M → M) ''
        riemannianBallOf (I := I) (UniversalCover.liftedMetric (I := I) g) x r =
      riemannianBallOf (I := I) g (UniversalCover.proj x) r := by
  have _hr : 0 < r := hr
  let gL := UniversalCover.liftedMetric (I := I) g
  let _ : RiemannianBundle (fun z : M => TangentSpace I z) := ⟨g.toRiemannianMetric⟩
  let _ : RiemannianBundle (fun z : UniversalCover M => TangentSpace I z) :=
    ⟨gL.toRiemannianMetric⟩
  let _ : ∀ z : M, InnerProductSpace ℝ (TangentSpace I z) :=
    fun z => Bundle.instInnerProductSpaceReal (E := fun z : M => TangentSpace I z) z
  let _ : ∀ z : UniversalCover M, InnerProductSpace ℝ (TangentSpace I z) :=
    fun z => Bundle.instInnerProductSpaceReal (E := fun z : UniversalCover M => TangentSpace I z) z
  let _ : ∀ z : M, NormedSpace ℝ (TangentSpace I z) := fun z => inferInstance
  let _ : ∀ z : UniversalCover M, NormedSpace ℝ (TangentSpace I z) := fun z => inferInstance
  have hcrb : IsContinuousRiemannianBundle E (fun z : M => TangentSpace I z) :=
    ⟨⟨fun z => g.inner z, g.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have hcrbL : IsContinuousRiemannianBundle E (fun z : UniversalCover M => TangentSpace I z) :=
    ⟨⟨fun z => gL.inner z, gL.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  have _hlcm : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional (M := M) I
  let _ : RegularSpace M := inferInstance
  let _ : RegularSpace (UniversalCover M) := UniversalCover.uc_regularSpace (M := M) I
  let _ : PseudoEMetricSpace M := PseudoEMetricSpace.ofRiemannianMetric I M
  let _ : PseudoEMetricSpace (UniversalCover M) :=
    UniversalCover.ucPseudoEMetricSpace (I := I) (M := M) gL
  have hnorm : ∀ (z : M) (v : TangentSpace I z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner z v v)) := by
    intro z v
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    congr 1
  have hnormL : ∀ (z : UniversalCover M) (v : TangentSpace I z),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (gL.inner z v v)) := by
    intro z v
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    congr 1
  ext y
  constructor
  · rintro ⟨x', hx', rfl⟩
    have hlip := UniversalCover.proj_lipschitzWith_one (I := I) (M := M) g hnorm hnormL
    have h := hlip x x'
    rw [ENNReal.coe_one, one_mul] at h
    rw [IsRiemannianManifold.out (I := I) (M := UniversalCover M) x x',
      IsRiemannianManifold.out (I := I) (M := M) (UniversalCover.proj x)
        (UniversalCover.proj x')] at h
    exact lt_of_le_of_lt h hx'
  · intro hy
    obtain ⟨γ, hγ0, hγ1, hγsmooth, hγlen⟩ :=
      Manifold.exists_lt_of_riemannianEDist_lt (I := I) (M := M) hy
    let γc : C(unitInterval, M) :=
      ⟨fun t => γ (t : ℝ),
        hγsmooth.continuousOn.comp_continuous continuous_subtype_val (fun t => t.2)⟩
    have hγc0 : γc 0 = UniversalCover.proj x := by
      change γ (0 : ℝ) = UniversalCover.proj x
      rw [hγ0]
    let Γ : C(unitInterval, UniversalCover M) :=
      (UniversalCover.proj_isCoveringMap).liftPath γc x hγc0
    have hΓ_lifts : UniversalCover.proj ∘ Γ = γc :=
      IsCoveringMap.liftPath_lifts (UniversalCover.proj_isCoveringMap) γc x hγc0
    have hΓ0 : Γ 0 = x :=
      IsCoveringMap.liftPath_zero (UniversalCover.proj_isCoveringMap) γc x hγc0
    have hΓproj : ∀ t, UniversalCover.proj (Γ t) = γc t := fun t => congr_fun hΓ_lifts t
    have hγcsmooth : ContMDiff (𝓡∂ 1) I 1 γc := by
      rw [← contMDiffOn_comp_projIcc_iff (x := (0 : ℝ)) (y := 1)]
      refine hγsmooth.congr (fun t ht => ?_)
      change γ ↑(Set.projIcc 0 1 zero_le_one t) = γ t
      rw [Set.projIcc_of_mem zero_le_one ht]
    have hΓsmooth : ContMDiff (𝓡∂ 1) I 1 Γ :=
      DifferentialGeometry.Topology.contMDiff_one_of_lift_through_localDiffeomorph
        (p := (UniversalCover.proj : UniversalCover M → M))
        UniversalCover.proj_localDiffeo hγcsmooth Γ hΓproj
    let Γℝ : ℝ → UniversalCover M := fun t => Γ (Set.projIcc 0 1 zero_le_one t)
    have hΓℝsmooth : ContMDiffOn 𝓘(ℝ, ℝ) I 1 Γℝ (Set.Icc (0 : ℝ) 1) :=
      contMDiffOn_comp_projIcc_iff.mpr hΓsmooth
    have hΓℝ0 : Γℝ 0 = x := by
      change Γ (Set.projIcc 0 1 zero_le_one 0) = x
      simpa using hΓ0
    have hproj_Γℝ : ∀ t ∈ Set.Icc (0 : ℝ) 1, UniversalCover.proj (Γℝ t) = γ t := by
      intro t ht
      change UniversalCover.proj (Γ (Set.projIcc 0 1 zero_le_one t)) = γ t
      rw [hΓproj, Set.projIcc_of_mem zero_le_one ht]
      rfl
    have hlen_eq : pathELength I (fun t => UniversalCover.proj (Γℝ t)) 0 1 =
        pathELength I γ 0 1 :=
      pathELength_congr (fun t ht => hproj_Γℝ t ht)
    have hlen_proj : pathELength I (fun t => UniversalCover.proj (Γℝ t)) 0 1 =
        pathELength I Γℝ 0 1 :=
      UniversalCover.proj_pathELength_eq (I := I) (M := M) g hnorm hnormL hΓℝsmooth
    have hed : riemannianEDistOf (I := I) gL x (Γℝ 1) ≤ pathELength I Γℝ 0 1 :=
      Manifold.riemannianEDist_le_pathELength (I := I) (M := UniversalCover M) hΓℝsmooth
        hΓℝ0 rfl zero_le_one
    refine ⟨Γℝ 1, ?_, ?_⟩
    · calc riemannianEDistOf (I := I) gL x (Γℝ 1) ≤ pathELength I Γℝ 0 1 := hed
        _ = pathELength I (fun t => UniversalCover.proj (Γℝ t)) 0 1 := hlen_proj.symm
        _ = pathELength I γ 0 1 := hlen_eq
        _ < ENNReal.ofReal r := hγlen
    · rw [hproj_Γℝ 1 (by norm_num)]
      exact hγ1

variable [SecondCountableTopology M]

private local instance upstreamCoverVolumeMeasurable : MeasurableSpace M := borel M
private local instance upstreamCoverVolumeBorel : BorelSpace M := ⟨rfl⟩
private local instance upstreamCoverVolumeLiftMeasurable :
    MeasurableSpace (UniversalCover M) := borel (UniversalCover M)
private local instance upstreamCoverVolumeLiftBorel :
    BorelSpace (UniversalCover M) := ⟨rfl⟩
private local instance upstreamCoverVolumeC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance upstreamCoverVolumeLiftC1 :
    IsManifold I 1 (UniversalCover M) := IsManifold.of_le (n := ∞) (by decide)

theorem universalCover_volume_image_le
    (g : SmoothRiemannianMetric I M) (U : Set (UniversalCover M)) (hU : IsOpen U) :
    riemannianVolumeMeasure (I := I) (M := M) g
        ((UniversalCover.proj : UniversalCover M → M) '' U) ≤
      riemannianVolumeMeasure (I := I) (M := UniversalCover M)
        (UniversalCover.liftedMetric (I := I) g) U := by
  sorry

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
