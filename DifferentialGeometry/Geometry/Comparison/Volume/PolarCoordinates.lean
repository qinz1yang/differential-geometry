import DifferentialGeometry.Geometry.Comparison.Volume.CutTime
import DifferentialGeometry.Geometry.Comparison.NormalCoordinates.ExponentialBallPartialDiffeomorph

set_option autoImplicit false

noncomputable section

open Set Function Bundle Manifold MeasureTheory
open scoped Topology Manifold ContDiff ENNReal

namespace Poincare.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M]
variable [RiemannianBundle (fun x : M => TangentSpace I x)]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem expMapIntrinsic_isLocalDiffeomorphOn_minimizingInterior
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M) :
    IsLocalDiffeomorphOn 𝓘(ℝ, E) I ∞
      (fun v : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from v))
      (SegmentInt (I := I) g hEnorm x) := by
  rintro ⟨v, hv⟩
  have hnot : ¬ IsConjVec (I := I) g hEnorm x
      (tangentSpaceModelContinuousLinearEquiv (I := I) x
        (show TangentSpace I x from v)) := by
    rw [tangentSpaceModelContinuousLinearEquiv_apply]
    exact segmentInt_no_conj (I := I) g hEnorm hv
  obtain ⟨B, hvB⟩ := branch_of_not_conj (I := I) g hEnorm hnot
  exact ⟨B.hom, hvB, B.hom_eq⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem exists_expMapIntrinsic_partialDiffeomorph_minimizingInterior
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞,
      Φ.source = SegmentInt (I := I) g hEnorm x ∧
      Φ.target =
        (fun v : E => expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v)) ''
            SegmentInt (I := I) g hEnorm x ∧
      Set.EqOn Φ
        (fun v : E => expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v))
        (SegmentInt (I := I) g hEnorm x) := by
  let _ : Nontrivial E := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  exact exists_partial_diffeomorph_of_is_local_diffeomorph_on_inj_on
      (expMapIntrinsic_isLocalDiffeomorphOn_minimizingInterior
        (I := I) g hEnorm x)
      (isOpen_segInt (I := I) g hEnorm x)
      (exp_inj_segmentInt (I := I) g hEnorm x)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def polarMinimizingDomain [PseudoEMetricSpace M] [IsRiemannianManifold I M]
    [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M) : Set E :=
  SegmentInt (I := I) g hEnorm x \ {(0 : E)}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem isOpen_polarMinimizingDomain [ConnectedSpace M]
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M) :
    IsOpen (polarMinimizingDomain (I := I) g hEnorm x) := by
  exact (isOpen_segInt (I := I) g hEnorm x).inter isOpen_compl_singleton

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem segmentCutLocusCandidate_eq_segmentEndpointImage
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M) :
    segmentCutLocusCandidate (I := I) g hEnorm x =
      segmentEndpointImage (I := I) g hEnorm x := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨w, hwexp, hwlen⟩ :=
      hopf_rinow_expMapIntrinsic_surjective_minimizing
        (I := I) g hEnorm x y
    have hwD : w ∈ SegmentDom (I := I) g hEnorm x :=
      (mem_segmentDom (I := I)).mpr (by rw [hwexp]; exact hwlen)
    refine ⟨w, ⟨hwD, ?_⟩, hwexp⟩
    intro hwI
    apply hy
    exact ⟨w, hwI, hwexp⟩
  · rintro ⟨w, ⟨hwD, hwI⟩, hwexp⟩ ⟨v, hvI, hvexp⟩
    have hvw : v = w :=
      expMapIntrinsic_eq_of_left_mem_segInt (I := I) g hEnorm x
        hvI hwD (hvexp.trans hwexp.symm)
    exact hwI (hvw ▸ hvI)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem segmentEndpointImage_volume_zero
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M) :
    riemannianVolumeMeasure (I := I) (M := M) g
        (segmentEndpointImage (I := I) g hEnorm x) = 0 := by
  rw [← segmentCutLocusCandidate_eq_segmentEndpointImage
    (I := I) g hEnorm x]
  exact segmentCutLocusCandidate_volume_zero (I := I) g hEnorm x

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem expMapIntrinsic_image_polarMinimizingDomain
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M) :
    (fun v : E => expMapIntrinsic (I := I) g hEnorm x
      (show TangentSpace I x from v)) ''
        polarMinimizingDomain (I := I) g hEnorm x =
      ({x} ∪ segmentEndpointImage (I := I) g hEnorm x)ᶜ := by
  classical
  let F : E → M := fun v => expMapIntrinsic (I := I) g hEnorm x
    (show TangentSpace I x from v)
  ext y
  constructor
  · rintro ⟨v, ⟨hvI, hv0⟩, rfl⟩
    have hbase : F v ≠ x := by
      intro heq
      have hvzero : (show TangentSpace I x from v) = 0 :=
        expMapIntrinsic_eq_of_left_mem_segInt (I := I) g hEnorm x
          hvI (segmentDom_zero (I := I) g hEnorm x) (by
            rw [expMapIntrinsic_zero (I := I) g hEnorm x]
            exact heq)
      have hvzeroE : v = 0 :=
        congrArg (fun z : TangentSpace I x => (z : E)) hvzero
      exact hv0 (by simpa only [Set.mem_singleton_iff] using hvzeroE)
    have hend : F v ∉ segmentEndpointImage (I := I) g hEnorm x := by
      rw [← segmentCutLocusCandidate_eq_segmentEndpointImage
        (I := I) g hEnorm x]
      exact fun hcut => hcut ⟨v, hvI, rfl⟩
    simpa only [Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff,
      not_or] using ⟨hbase, hend⟩
  · intro hy
    have hy' : y ≠ x ∧
        y ∉ segmentEndpointImage (I := I) g hEnorm x := by
      simpa only [Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff,
        not_or] using hy
    have hyInt : y ∈ F '' SegmentInt (I := I) g hEnorm x := by
      by_contra hnot
      have hcut : y ∈ segmentCutLocusCandidate (I := I) g hEnorm x := hnot
      rw [segmentCutLocusCandidate_eq_segmentEndpointImage
        (I := I) g hEnorm x] at hcut
      exact hy'.2 hcut
    obtain ⟨v, hvI, hvexp⟩ := hyInt
    refine ⟨v, ⟨hvI, ?_⟩, hvexp⟩
    intro hv0
    have hvzero : v = 0 := by simpa only [Set.mem_singleton_iff] using hv0
    apply hy'.1
    rw [← hvexp, hvzero]
    exact expMapIntrinsic_zero (I := I) g hEnorm x

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem exists_expMapIntrinsic_partialDiffeomorph_polarMinimizingDomain
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M) :
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞,
      Φ.source = polarMinimizingDomain (I := I) g hEnorm x ∧
      Φ.target = ({x} ∪ segmentEndpointImage (I := I) g hEnorm x)ᶜ ∧
      Set.EqOn Φ
        (fun v : E => expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v))
        (polarMinimizingDomain (I := I) g hEnorm x) := by
  let _ : Nontrivial E := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  obtain ⟨Φ, hsource, htarget, heq⟩ :=
    exists_partial_diffeomorph_of_is_local_diffeomorph_on_inj_on
      (s := polarMinimizingDomain (I := I) g hEnorm x)
      (f := fun v : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from v))
      (fun ⟨v, hv⟩ =>
        expMapIntrinsic_isLocalDiffeomorphOn_minimizingInterior
          (I := I) g hEnorm x ⟨v, hv.1⟩)
      (isOpen_polarMinimizingDomain (I := I) g hEnorm x)
      ((exp_inj_segmentInt (I := I) g hEnorm x).mono sdiff_subset)
  refine ⟨Φ, hsource, ?_, heq⟩
  exact htarget.trans
    (expMapIntrinsic_image_polarMinimizingDomain (I := I) g hEnorm x)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def minimizingExpJacobianMeasure [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M) : Measure E :=
  ((modelHaar (E := E)).restrict (SegmentInt (I := I) g hEnorm x)).withDensity
    (fun v : E => ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianVolumeMeasure_eq_map_exp_minimizingInterior
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M) :
    riemannianVolumeMeasure (I := I) (M := M) g =
      Measure.map (fun v : E => expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from v))
        (minimizingExpJacobianMeasure (I := I) g hEnorm x) := by
  classical
  let μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g
  let F : E → M := expMapIntrinsic (I := I) g hEnorm x
  let U : Set E := SegmentInt (I := I) g hEnorm x
  let Y : Set M := F '' U
  let D : E → ℝ≥0∞ := fun v => ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
  have hFmeas : Measurable F :=
    (intrinsicFiber_smooth (I := I) g hEnorm x).continuous.measurable
  have hUmeas : MeasurableSet U := measurableSet_segmentInt (I := I) g hEnorm x
  have hFinj : Set.InjOn F U := exp_inj_segmentInt (I := I) g hEnorm x
  have hYmeas : MeasurableSet Y :=
    hUmeas.image_of_continuousOn_injOn
      (intrinsicFiber_smooth (I := I) g hEnorm x).continuous.continuousOn hFinj
  have hYfull : ∀ᵐ y ∂μ, y ∈ Y := by
    have hnull : μ Yᶜ = 0 := by
      with_unfolding_all exact
        segmentCutLocusCandidate_volume_zero (I := I) g hEnorm x
    exact (measure_eq_zero_iff_ae_notMem.mp hnull).mono fun y hy => by
      simpa only [mem_compl_iff, not_not] using hy
  have hrestrict : μ.restrict Y = μ :=
    Measure.restrict_eq_self_of_ae_mem hYfull
  apply Measure.ext
  intro A hA
  have hpre : MeasurableSet (F ⁻¹' A) := hA.preimage hFmeas
  let K : Set E := U ∩ F ⁻¹' A
  have hKmeas : MeasurableSet K := hUmeas.inter hpre
  have hKinj : Set.InjOn F K := hFinj.mono inter_subset_left
  have himage : F '' K = A ∩ Y := by
    ext y
    constructor
    · rintro ⟨v, ⟨hvU, hvA⟩, rfl⟩
      exact ⟨hvA, v, hvU, rfl⟩
    · rintro ⟨hyA, v, hvU, rfl⟩
      exact ⟨v, ⟨hvU, hyA⟩, rfl⟩
  calc
    μ A = μ (A ∩ Y) := by
      rw [← Measure.restrict_apply hA, hrestrict]
    _ = μ (F '' K) := by rw [himage]
    _ = ∫⁻ v in K, D v ∂(modelHaar (E := E)) := by
      simpa only [μ, F, D] using
        riemVol_exp_image_eq (I := I) g hEnorm x hKmeas hKinj
    _ = ∫⁻ v in F ⁻¹' A, D v ∂((modelHaar (E := E)).restrict U) := by
      rw [Measure.restrict_restrict hpre, inter_comm]
    _ = minimizingExpJacobianMeasure (I := I) g hEnorm x (F ⁻¹' A) := by
      rw [minimizingExpJacobianMeasure, withDensity_apply _ hpre]
    _ = Measure.map F (minimizingExpJacobianMeasure (I := I) g hEnorm x) A := by
      rw [Measure.map_apply hFmeas hA]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lintegral_eq_lintegral_exp_minimizingInterior
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M)
    (f : M → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ y, f y ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫⁻ v in SegmentInt (I := I) g hEnorm x,
        f (expMapIntrinsic (I := I) g hEnorm x v) *
          ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
        ∂(modelHaar (E := E)) := by
  rw [riemannianVolumeMeasure_eq_map_exp_minimizingInterior
    (I := I) g hEnorm x, lintegral_map hf
      (intrinsicFiber_smooth (I := I) g hEnorm x).continuous.measurable,
    minimizingExpJacobianMeasure,
    lintegral_withDensity_eq_lintegral_mul]
  · apply setLIntegral_congr_fun
      (measurableSet_segmentInt (I := I) g hEnorm x)
    intro v _hv
    exact mul_comm _ _
  · exact ENNReal.measurable_ofReal.comp
      (expJacobianDensity_continuous (I := I) g hEnorm x).measurable
  · exact hf.comp
      (intrinsicFiber_smooth (I := I) g hEnorm x).continuous.measurable

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def normalExpJacobian [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M) (w : E) : ℝ :=
  curveDensity (I := I) g
    (intrinsicGeodesic (I := I) g hEnorm x
      (normalFrame (I := I) (E := E) g x w))
    (fun i t => intrinsicJacobi (I := I) g hEnorm x
      (normalFrame (I := I) (E := E) g x w)
      ((normalBasis (I := I) g x) i) t) 1

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem normalExpJacobian_eq_det_mul_expJacDensity
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M) (w : E) :
    normalExpJacobian (I := I) g hEnorm x w =
      |(chartModelBasis E).det (normalBasis (I := I) g x)| *
        expJacobianDensity (I := I) g hEnorm x
          (normalFrame (I := I) (E := E) g x w) := by
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := chartModelBasis E
  let b' : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    normalBasis (I := I) g x
  have h := jacobianDens_basis (I := I) g hEnorm x
    (normalFrame (I := I) (E := E) g x w) b b'
  with_unfolding_all
    exact h

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem normalExpJacobian_continuous
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M) :
    Continuous (normalExpJacobian (I := I) g hEnorm x) := by
  apply Continuous.congr
    (continuous_const.mul
      ((expJacobianDensity_continuous (I := I) g hEnorm x).comp
        (normalFrame (I := I) (E := E) g x).continuous))
  · intro w
    exact (normalExpJacobian_eq_det_mul_expJacDensity
      (I := I) g hEnorm x w).symm

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem normalExpJacobian_pos_of_mem_segInt
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M) (w : E)
    (hw : normalFrame (I := I) (E := E) g x w ∈
      SegmentInt (I := I) g hEnorm x) :
    0 < normalExpJacobian (I := I) g hEnorm x w := by
  have hnot : ¬ IsConjVec (I := I) g hEnorm x
      (tangentSpaceModelContinuousLinearEquiv (I := I) x
        (normalFrame (I := I) (E := E) g x w)) := by
    rw [tangentSpaceModelContinuousLinearEquiv_apply]
    exact segmentInt_no_conj (I := I) g hEnorm hw
  obtain ⟨B, hwB⟩ := branch_of_not_conj (I := I) g hEnorm hnot
  apply curveDensity_pos
  exact intrinsicJacobi_li (I := I) B hwB
    (normalBasis (I := I) g x) (normalBasis (I := I) g x).linearIndependent

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem setLIntegral_expJacobian_normalFrame
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M)
    (K : Set E) (f : M → ℝ≥0∞) :
    (∫⁻ v in K,
        f (expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v)) *
          ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
        ∂(modelHaar (E := E))) =
      ∫⁻ w in (normalFrame (I := I) (E := E) g x) ⁻¹' K,
        f (expMapIntrinsic (I := I) g hEnorm x
          (normalFrame (I := I) (E := E) g x w)) *
          ENNReal.ofReal (normalExpJacobian (I := I) g hEnorm x w)
        ∂(volume : Measure E) := by
  classical
  let b : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E := chartModelBasis E
  let b' : Module.Basis (Fin (Module.finrank ℝ E)) ℝ E :=
    normalBasis (I := I) g x
  let L : E ≃L[ℝ] E := normalFrame (I := I) (E := E) g x
  let Dt : E → ℝ := fun v =>
    curveDensity (I := I) g
      (intrinsicGeodesic (I := I) g hEnorm x
        (show TangentSpace I x from v))
      (fun i t => intrinsicJacobi (I := I) g hEnorm x
        (show TangentSpace I x from v) (b' i) t) 1
  let W : E → ℝ≥0∞ := fun v =>
    f (expMapIntrinsic (I := I) g hEnorm x
      (show TangentSpace I x from v))
  have hD (v : E) :
      ENNReal.ofReal |b.det b'| *
          ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v) =
        ENNReal.ofReal (Dt v) := by
    rw [← ENNReal.ofReal_mul (abs_nonneg (b.det b'))]
    congr 1
    change |b.det b'| * expJacobianDensity (I := I) g hEnorm x v =
      curveDensity (I := I) g
        (intrinsicGeodesic (I := I) g hEnorm x v)
        (fun i t => intrinsicJacobi (I := I) g hEnorm x v (b' i) t) 1
    exact (jacobianDens_basis (I := I) g hEnorm x v b b').symm
  have hbasis :
      (∫⁻ v in K,
          W v * ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
          ∂(modelHaar (E := E))) =
        ∫⁻ v in K, W v * ENNReal.ofReal (Dt v) ∂b'.addHaar := by
    calc
      _ = ∫⁻ v in K,
          W v * ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
          ∂b.addHaar := by rfl
      _ = ∫⁻ v in K,
          ENNReal.ofReal |b.det b'| *
            (W v * ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v))
          ∂b'.addHaar := by
        rw [← Module.Basis.det_smul_addHaar b b',
          setLIntegral_smul_measure]
        exact (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ = ∫⁻ v in K, W v * ENNReal.ofReal (Dt v) ∂b'.addHaar := by
        apply lintegral_congr
        intro v
        rw [← hD v]
        ac_rfl
  have hbmap :
      (stdOrthonormalBasis ℝ E).toBasis.map L.toLinearEquiv = b' := by
    ext i
    change normalFrame (I := I) (E := E) g x
        ((stdOrthonormalBasis ℝ E) i) = normalBasis (I := I) g x i
    exact normalFrame_basis (I := I) g x i
  have hmap : Measure.map L (volume : Measure E) = b'.addHaar := by
    calc
      _ = Measure.map L (stdOrthonormalBasis ℝ E).toBasis.addHaar := by
        rw [(stdOrthonormalBasis ℝ E).addHaar_eq_volume]
      _ = ((stdOrthonormalBasis ℝ E).toBasis.map
          L.toLinearEquiv).addHaar := Module.Basis.map_addHaar _ _
      _ = b'.addHaar := congrArg Module.Basis.addHaar hbmap
  have hmp : MeasurePreserving L (volume : Measure E) b'.addHaar :=
    ⟨L.continuous.measurable, hmap⟩
  rw [hbasis]
  have hchange := (hmp.setLIntegral_comp_preimage_emb
    L.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun v => W v * ENNReal.ofReal (Dt v)) K).symm
  with_unfolding_all
    convert hchange using 1
    all_goals rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lintegral_eq_lintegral_normal_minimizingInterior
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M)
    (f : M → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ y, f y ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫⁻ w in (normalFrame (I := I) (E := E) g x) ⁻¹'
          SegmentInt (I := I) g hEnorm x,
        f (expMapIntrinsic (I := I) g hEnorm x
          (normalFrame (I := I) (E := E) g x w)) *
          ENNReal.ofReal (normalExpJacobian (I := I) g hEnorm x w)
        ∂(volume : Measure E) := by
  calc
    _ = ∫⁻ v in SegmentInt (I := I) g hEnorm x,
        f (expMapIntrinsic (I := I) g hEnorm x v) *
          ENNReal.ofReal (expJacobianDensity (I := I) g hEnorm x v)
        ∂(modelHaar (E := E)) :=
      lintegral_eq_lintegral_exp_minimizingInterior
        (I := I) g hEnorm x f hf
    _ = _ := setLIntegral_expJacobian_normalFrame
      (I := I) g hEnorm x (SegmentInt (I := I) g hEnorm x) f

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def normalPolarJacobian [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M)
    (t : ℝ) (u : Metric.sphere (0 : E) 1) : ℝ :=
  t ^ (Module.finrank ℝ E - 1) *
    normalExpJacobian (I := I) g hEnorm x (t • (u : E))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem normalPolarJacobian_eq
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M)
    (t : ℝ) (u : Metric.sphere (0 : E) 1) :
    normalPolarJacobian (I := I) g hEnorm x t u =
      t ^ (Module.finrank ℝ E - 1) *
        normalExpJacobian (I := I) g hEnorm x (t • (u : E)) := rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem normalPolarJacobian_pos
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M)
    (t : ℝ) (u : Metric.sphere (0 : E) 1)
    (ht : 0 < t)
    (hseg : normalFrame (I := I) (E := E) g x (t • (u : E)) ∈
      SegmentInt (I := I) g hEnorm x) :
    0 < normalPolarJacobian (I := I) g hEnorm x t u := by
  exact mul_pos (pow_pos ht _) (normalExpJacobian_pos_of_mem_segInt
    (I := I) g hEnorm x (t • (u : E)) hseg)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lintegral_polar_minimizingInterior
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M)
    (f : M → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ y, f y ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫⁻ u : Metric.sphere (0 : E) 1,
        ∫⁻ r : Ioi (0 : ℝ),
          ((normalFrame (I := I) (E := E) g x) ⁻¹'
              SegmentInt (I := I) g hEnorm x).indicator
            (fun w =>
              f (expMapIntrinsic (I := I) g hEnorm x
                (normalFrame (I := I) (E := E) g x w)) *
                ENNReal.ofReal (normalExpJacobian (I := I) g hEnorm x w))
            (r.1 • u.1)
          ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1))
        ∂(volume : Measure E).toSphere := by
  let _ : Nontrivial E := Module.nontrivial_of_finrank_pos
    (Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E)))
  let L : E ≃L[ℝ] TangentSpace I x := normalFrame (I := I) (E := E) g x
  let U : Set E := L ⁻¹' SegmentInt (I := I) g hEnorm x
  let G : E → ℝ≥0∞ := U.indicator (fun w =>
    f (expMapIntrinsic (I := I) g hEnorm x (L w)) *
      ENNReal.ofReal (normalExpJacobian (I := I) g hEnorm x w))
  have hU : MeasurableSet U :=
    (measurableSet_segmentInt (I := I) g hEnorm x).preimage L.continuous.measurable
  have hbody : Measurable (fun w : E =>
      f (expMapIntrinsic (I := I) g hEnorm x (L w)) *
        ENNReal.ofReal (normalExpJacobian (I := I) g hEnorm x w)) :=
    (hf.comp ((intrinsicFiber_smooth (I := I) g hEnorm x).continuous.comp
      L.continuous).measurable).mul
      (ENNReal.measurable_ofReal.comp
        (normalExpJacobian_continuous (I := I) g hEnorm x).measurable)
  have hG : Measurable G := hbody.indicator hU
  calc
    _ = ∫⁻ w in U,
        f (expMapIntrinsic (I := I) g hEnorm x (L w)) *
          ENNReal.ofReal (normalExpJacobian (I := I) g hEnorm x w)
        ∂(volume : Measure E) := by
      simpa only [L, U] using
        lintegral_eq_lintegral_normal_minimizingInterior
          (I := I) g hEnorm x f hf
    _ = ∫⁻ w, G w ∂(volume : Measure E) := by
      rw [lintegral_indicator hU]
    _ = ∫⁻ u : Metric.sphere (0 : E) 1,
        ∫⁻ r : Ioi (0 : ℝ), G (r.1 • u.1)
          ∂(Measure.volumeIoiPow (Module.finrank ℝ E - 1))
        ∂(volume : Measure E).toSphere :=
      MeasureTheory.lintegral_polar (volume : Measure E) G hG.aemeasurable
    _ = _ := by rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def normalPolarRayDomain [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M)
    (u : Metric.sphere (0 : E) 1) : Set ℝ :=
  {t | 0 < t ∧ normalFrame (I := I) (E := E) g x (t • (u : E)) ∈
    SegmentInt (I := I) g hEnorm x}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def normalUnitTangent
    (g : SmoothRiemannianMetric I M) (x : M)
    (u : Metric.sphere (0 : E) 1) : gUnitTangentSphere (I := I) g x := by
  refine ⟨normalFrame (I := I) (E := E) g x (u : E), ?_⟩
  rw [normalFrame_inner, real_inner_self_eq_norm_sq]
  have hu : ‖(u : E)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using u.property
  rw [hu, one_pow]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem normalPolarRayDomain_eq_cutTime
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M)
    (u : Metric.sphere (0 : E) 1) :
    normalPolarRayDomain (I := I) g hEnorm x u =
      {t : ℝ | 0 < t ∧
        ENNReal.ofReal t <
          cutTime (I := I) g hEnorm x (normalUnitTangent (I := I) g x u)} := by
  ext t
  simp only [normalPolarRayDomain, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨ht, hseg⟩
    refine ⟨ht, (ofReal_lt_cutTime_iff_smul_mem_segInt
      (I := I) g hEnorm x (normalUnitTangent (I := I) g x u) ht).2 ?_⟩
    simpa only [normalUnitTangent, map_smul] using hseg
  · rintro ⟨ht, hcut⟩
    refine ⟨ht, ?_⟩
    have hseg := (ofReal_lt_cutTime_iff_smul_mem_segInt
      (I := I) g hEnorm x (normalUnitTangent (I := I) g x u) ht).1 hcut
    simpa only [normalUnitTangent, map_smul] using hseg

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def normalPolarDomain [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M) :
    Set (Metric.sphere (0 : E) 1 × ℝ) :=
  {z | z.2 ∈ normalPolarRayDomain (I := I) g hEnorm x z.1}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def normalPolarMap [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M)
    (z : Metric.sphere (0 : E) 1 × ℝ) : M :=
  expMapIntrinsic (I := I) g hEnorm x
    (normalFrame (I := I) (E := E) g x (z.2 • (z.1 : E)))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem measurableSet_normalPolarDomain
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M) :
    MeasurableSet (normalPolarDomain (I := I) g hEnorm x) := by
  change MeasurableSet
    ({z : Metric.sphere (0 : E) 1 × ℝ | 0 < z.2} ∩
      {z | normalFrame (I := I) (E := E) g x (z.2 • (z.1 : E)) ∈
        SegmentInt (I := I) g hEnorm x})
  refine (measurableSet_Ioi.preimage measurable_snd).inter
    ((measurableSet_segmentInt (I := I) g hEnorm x).preimage ?_)
  exact (normalFrame (I := I) (E := E) g x).continuous.measurable.comp
    (measurable_snd.smul (measurable_subtype_coe.comp measurable_fst))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem normalPolarMap_measurable
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M) :
    Measurable (normalPolarMap (I := I) g hEnorm x) := by
  exact (intrinsicFiber_smooth (I := I) g hEnorm x).continuous.measurable.comp
    ((normalFrame (I := I) (E := E) g x).continuous.measurable.comp
      (measurable_snd.smul (measurable_subtype_coe.comp measurable_fst)))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem normalPolarJacobian_measurable
    [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M) :
    Measurable (fun z : Metric.sphere (0 : E) 1 × ℝ =>
      ENNReal.ofReal (normalPolarJacobian (I := I) g hEnorm x z.2 z.1)) := by
  apply ENNReal.measurable_ofReal.comp
  exact (measurable_snd.pow_const (Module.finrank ℝ E - 1)).mul
    ((normalExpJacobian_continuous (I := I) g hEnorm x).measurable.comp
      (measurable_snd.smul (measurable_subtype_coe.comp measurable_fst)))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
def normalPolarJacobianMeasure [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M) :
    Measure (Metric.sphere (0 : E) 1 × ℝ) :=
  ((volume : Measure E).toSphere.prod (volume : Measure ℝ)).withDensity
    ((normalPolarDomain (I := I) g hEnorm x).indicator
      (fun z => ENNReal.ofReal
        (normalPolarJacobian (I := I) g hEnorm x z.2 z.1)))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem riemannianEDist_normalPolar_eq_of_mem_rayDomain
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M)
    (u : Metric.sphere (0 : E) 1) {t : ℝ}
    (ht : t ∈ normalPolarRayDomain (I := I) g hEnorm x u) :
    riemannianEDist I x
        (expMapIntrinsic (I := I) g hEnorm x
          (normalFrame (I := I) (E := E) g x (t • (u : E)))) =
      ENNReal.ofReal t := by
  have hvD : normalFrame (I := I) (E := E) g x (t • (u : E)) ∈
      SegmentDom (I := I) g hEnorm x :=
    segmentInt_subset (I := I) g hEnorm x ht.2
  have hfin : riemannianEDist I x
      (expMapIntrinsic (I := I) g hEnorm x
        (normalFrame (I := I) (E := E) g x (t • (u : E)))) ≠ ⊤ :=
    riemannianEDist_ne_top (I := I) _ _
  rw [← ENNReal.ofReal_toReal hfin, ← (mem_segmentDom (I := I)).mp hvD,
    normalFrame_sqrt, norm_smul, Real.norm_eq_abs, abs_of_pos ht.1]
  have hu : ‖(u : E)‖ = 1 := by
    simpa only [Metric.mem_sphere, dist_zero_right] using u.property
  rw [hu, mul_one]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [T2Space (TangentBundle I M)] in
theorem measurableSet_normalPolarRayDomain
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M)
    (u : Metric.sphere (0 : E) 1) :
    MeasurableSet (normalPolarRayDomain (I := I) g hEnorm x u) := by
  rw [normalPolarRayDomain]
  refine measurableSet_Ioi.inter
    ((measurableSet_segmentInt (I := I) g hEnorm x).preimage ?_)
  exact (normalFrame (I := I) (E := E) g x).continuous.measurable.comp
    (measurable_smul_const (u : E))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lintegral_polarJacobian_minimizingInterior
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M)
    (f : M → ℝ≥0∞) (hf : Measurable f) :
    ∫⁻ y, f y ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫⁻ u : Metric.sphere (0 : E) 1,
        ∫⁻ t in normalPolarRayDomain (I := I) g hEnorm x u,
          f (expMapIntrinsic (I := I) g hEnorm x
            (normalFrame (I := I) (E := E) g x (t • (u : E)))) *
            ENNReal.ofReal (normalPolarJacobian (I := I) g hEnorm x t u)
          ∂(volume : Measure ℝ)
        ∂(volume : Measure E).toSphere := by
  rw [lintegral_polar_minimizingInterior (I := I) g hEnorm x f hf]
  apply lintegral_congr
  intro u
  rw [Measure.volumeIoiPow,
    lintegral_withDensity_eq_lintegral_mul]
  · let Q : ℝ → ℝ≥0∞ := fun t =>
        ENNReal.ofReal (t ^ (Module.finrank ℝ E - 1)) *
          (((normalFrame (I := I) (E := E) g x) ⁻¹'
              SegmentInt (I := I) g hEnorm x).indicator
            (fun w =>
              f (expMapIntrinsic (I := I) g hEnorm x
                (normalFrame (I := I) (E := E) g x w)) *
                ENNReal.ofReal (normalExpJacobian (I := I) g hEnorm x w))
            (t • u.1))
    change (∫⁻ r : Ioi (0 : ℝ), Q r.1
          ∂((volume : Measure ℝ).comap Subtype.val)) = _
    rw [lintegral_subtype_comap measurableSet_Ioi]
    let R : Set ℝ := normalPolarRayDomain (I := I) g hEnorm x u
    let B : ℝ → ℝ≥0∞ := fun t =>
      f (expMapIntrinsic (I := I) g hEnorm x
        (normalFrame (I := I) (E := E) g x (t • (u : E)))) *
        ENNReal.ofReal (normalPolarJacobian (I := I) g hEnorm x t u)
    have hRmeas : MeasurableSet R :=
      measurableSet_normalPolarRayDomain (I := I) g hEnorm x u
    have hRsub : R ⊆ Ioi (0 : ℝ) := fun _ ht => ht.1
    calc
      (∫⁻ t in Ioi (0 : ℝ), Q t ∂(volume : Measure ℝ)) =
          ∫⁻ t in Ioi (0 : ℝ), R.indicator B t ∂(volume : Measure ℝ) := by
        apply setLIntegral_congr_fun measurableSet_Ioi
        intro t ht
        by_cases hseg : normalFrame (I := I) (E := E) g x (t • (u : E)) ∈
            SegmentInt (I := I) g hEnorm x
        · dsimp only [Q]
          rw [Set.indicator_of_mem (show t • (u : E) ∈
            (normalFrame (I := I) (E := E) g x) ⁻¹'
              SegmentInt (I := I) g hEnorm x from hseg)]
          rw [Set.indicator_of_mem (show t ∈ R from ⟨ht, hseg⟩)]
          dsimp only [B]
          rw [normalPolarJacobian, ENNReal.ofReal_mul (pow_nonneg ht.le _)]
          ac_rfl
        · dsimp only [Q]
          rw [Set.indicator_of_notMem (show t • (u : E) ∉
            (normalFrame (I := I) (E := E) g x) ⁻¹'
              SegmentInt (I := I) g hEnorm x from hseg)]
          simp only [mul_zero]
          rw [Set.indicator_of_notMem]
          exact fun h => hseg h.2
      _ = ∫⁻ t in R, B t ∂(volume : Measure ℝ) := by
        rw [setLIntegral_indicator hRmeas]
        rw [inter_eq_left.mpr hRsub]
  · exact ENNReal.measurable_ofReal.comp
      (measurable_subtype_coe.pow_const (Module.finrank ℝ E - 1))
  · have hU : MeasurableSet
        ((normalFrame (I := I) (E := E) g x) ⁻¹'
          SegmentInt (I := I) g hEnorm x) :=
      (measurableSet_segmentInt (I := I) g hEnorm x).preimage
        (normalFrame (I := I) (E := E) g x).continuous.measurable
    have hbody : Measurable (fun w : E =>
        f (expMapIntrinsic (I := I) g hEnorm x
          (normalFrame (I := I) (E := E) g x w)) *
          ENNReal.ofReal (normalExpJacobian (I := I) g hEnorm x w)) :=
      (hf.comp ((intrinsicFiber_smooth (I := I) g hEnorm x).continuous.comp
        (normalFrame (I := I) (E := E) g x).continuous).measurable).mul
        (ENNReal.measurable_ofReal.comp
          (normalExpJacobian_continuous (I := I) g hEnorm x).measurable)
    exact (hbody.indicator hU).comp
      (measurable_subtype_coe.smul measurable_const)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem riemannianVolumeMeasure_eq_map_normalPolarMap
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M) :
    riemannianVolumeMeasure (I := I) (M := M) g =
      Measure.map (normalPolarMap (I := I) g hEnorm x)
        (normalPolarJacobianMeasure (I := I) g hEnorm x) := by
  apply (Measure.ext_iff_lintegral _).mpr
  intro f hf
  rw [lintegral_map hf (normalPolarMap_measurable (I := I) g hEnorm x),
    normalPolarJacobianMeasure, lintegral_withDensity_eq_lintegral_mul]
  · rw [lintegral_polarJacobian_minimizingInterior
      (I := I) g hEnorm x f hf]
    let D : Set (Metric.sphere (0 : E) 1 × ℝ) :=
      normalPolarDomain (I := I) g hEnorm x
    let j : Metric.sphere (0 : E) 1 × ℝ → ℝ≥0∞ := fun z =>
      ENNReal.ofReal (normalPolarJacobian (I := I) g hEnorm x z.2 z.1)
    let G : Metric.sphere (0 : E) 1 × ℝ → ℝ≥0∞ := fun z =>
      D.indicator j z * f (normalPolarMap (I := I) g hEnorm x z)
    have hD : MeasurableSet D :=
      measurableSet_normalPolarDomain (I := I) g hEnorm x
    have hj : Measurable j :=
      normalPolarJacobian_measurable (I := I) g hEnorm x
    have hG : Measurable G :=
      (hj.indicator hD).mul
        (hf.comp (normalPolarMap_measurable (I := I) g hEnorm x))
    change (∫⁻ u : Metric.sphere (0 : E) 1,
        ∫⁻ t in normalPolarRayDomain (I := I) g hEnorm x u,
          f (normalPolarMap (I := I) g hEnorm x (u, t)) *
            j (u, t) ∂(volume : Measure ℝ)
        ∂(volume : Measure E).toSphere) =
      ∫⁻ z, G z
        ∂((volume : Measure E).toSphere.prod (volume : Measure ℝ))
    rw [lintegral_prod G hG.aemeasurable]
    apply lintegral_congr
    intro u
    rw [← lintegral_indicator
      (measurableSet_normalPolarRayDomain (I := I) g hEnorm x u)]
    apply lintegral_congr
    intro t
    by_cases ht : t ∈ normalPolarRayDomain (I := I) g hEnorm x u
    · rw [Set.indicator_of_mem ht]
      dsimp only [G]
      rw [Set.indicator_of_mem (show (u, t) ∈ D from ht)]
      exact mul_comm _ _
    · rw [Set.indicator_of_notMem ht]
      dsimp only [G]
      rw [Set.indicator_of_notMem]
      · simp only [zero_mul]
      · exact ht
  · exact (normalPolarJacobian_measurable (I := I) g hEnorm x).indicator
      (measurableSet_normalPolarDomain (I := I) g hEnorm x)
  · exact hf.comp (normalPolarMap_measurable (I := I) g hEnorm x)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem metricBall_volume_eq_lintegral_polarJacobian
    [ConnectedSpace M] [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g) (x : M)
    {R : ℝ} (hR : 0 < R) :
    riemannianVolumeMeasure (I := I) (M := M) g
        {y : M | riemannianEDist I x y < ENNReal.ofReal R} =
      ∫⁻ u : Metric.sphere (0 : E) 1,
        ∫⁻ t in normalPolarRayDomain (I := I) g hEnorm x u ∩ Iio R,
          ENNReal.ofReal (normalPolarJacobian (I := I) g hEnorm x t u)
          ∂(volume : Measure ℝ)
        ∂(volume : Measure E).toSphere := by
  let B : Set M :=
    {y : M | riemannianEDist I x y < ENNReal.ofReal R}
  have hdist : Continuous (fun y : M => riemannianEDist I x y) := by
    exact (continuous_riemannianEDist_to (I := I) x).congr
      (fun y => Manifold.riemannianEDist_comm)
  have hB : MeasurableSet B :=
    (isOpen_lt hdist continuous_const).measurableSet
  have hf : Measurable (B.indicator (fun _ : M => (1 : ℝ≥0∞))) :=
    measurable_const.indicator hB
  have hpolar := lintegral_polarJacobian_minimizingInterior
    (I := I) g hEnorm x (B.indicator (fun _ : M => (1 : ℝ≥0∞))) hf
  rw [lintegral_indicator hB, setLIntegral_one] at hpolar
  change riemannianVolumeMeasure (I := I) (M := M) g B = _
  rw [hpolar]
  apply lintegral_congr
  intro u
  rw [inter_comm, ← setLIntegral_indicator measurableSet_Iio]
  apply setLIntegral_congr_fun
    (measurableSet_normalPolarRayDomain (I := I) g hEnorm x u)
  intro t ht
  have hmem :
      expMapIntrinsic (I := I) g hEnorm x
          (normalFrame (I := I) (E := E) g x (t • (u : E))) ∈ B ↔
        t ∈ Iio R := by
    change riemannianEDist I x
        (expMapIntrinsic (I := I) g hEnorm x
          (normalFrame (I := I) (E := E) g x (t • (u : E)))) <
        ENNReal.ofReal R ↔ t < R
    rw [riemannianEDist_normalPolar_eq_of_mem_rayDomain
      (I := I) g hEnorm x u ht]
    exact ENNReal.ofReal_lt_ofReal_iff hR
  by_cases htR : t ∈ Iio R
  · change B.indicator (fun _ : M => (1 : ℝ≥0∞))
        (expMapIntrinsic (I := I) g hEnorm x
          (normalFrame (I := I) (E := E) g x (t • (u : E)))) * _ = _
    rw [Set.indicator_of_mem (hmem.mpr htR), Set.indicator_of_mem htR]
    simp only [one_mul]
  · change B.indicator (fun _ : M => (1 : ℝ≥0∞))
        (expMapIntrinsic (I := I) g hEnorm x
          (normalFrame (I := I) (E := E) g x (t • (u : E)))) * _ = _
    rw [Set.indicator_of_notMem (fun h => htR (hmem.mp h)),
      Set.indicator_of_notMem htR, zero_mul]

end Poincare.Geometry.Riemannian.VolumeComparison

end
