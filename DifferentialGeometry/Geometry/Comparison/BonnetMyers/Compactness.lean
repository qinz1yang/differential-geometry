import DifferentialGeometry.Geometry.Comparison.BonnetMyers.Diameter
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Set Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace BonnetMyers

open DifferentialGeometry.Integral.Measure

open DifferentialGeometry.Geometry.Riemannian.Exponential
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H]

omit [NeZero (Module.finrank ℝ E)] in
theorem tangent_closedBall_isCompact
    {M : Type*}
    (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M]
    (p : M) {R : ℝ} :
    IsCompact (Metric.closedBall (0 : TangentSpace I p) R) := by
  have : ProperSpace E := FiniteDimensional.proper_real E
  exact isCompact_closedBall (0 : TangentSpace I p) R
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem isCompact_image_closedBall_under_expMapIntrinsic
    {M : Type*}
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    [PseudoEMetricSpace M]
    (g : SmoothRiemannianMetric I M)
    [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {R : ℝ} :
    IsCompact ((fun v => expMapIntrinsic (I := I) g hEnorm p v) ''
      Metric.closedBall (0 : TangentSpace I p) R) := by
  have : FiniteDimensional ℝ (TangentSpace I p) := inferInstanceAs (FiniteDimensional ℝ E)
  have : ProperSpace (TangentSpace I p) := FiniteDimensional.proper_real (TangentSpace I p)
  have hcompact : IsCompact (Metric.closedBall (0 : TangentSpace I p) R) :=
    isCompact_closedBall (0 : TangentSpace I p) R
  exact hcompact.image (expMapIntrinsic_continuous (I := I) g hEnorm p)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem expMapIntrinsic_surjective_on_closedBall_of_ediam_le
    {M : Type*}
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M]
    [PseudoEMetricSpace M]
    (g : SmoothRiemannianMetric I M)
    [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) {R : ℝ} (hR : 0 ≤ R)
    (hdiam : Metric.ediam (Set.univ : Set M) ≤ ENNReal.ofReal R) :
    (Set.univ : Set M) ⊆ (fun v => expMapIntrinsic (I := I) g hEnorm p v) ''
      Metric.closedBall (0 : TangentSpace I p) R := by
  intro y _
  obtain ⟨v, hv_exp, hv_len⟩ :=
    hopf_rinow_expMapIntrinsic_surjective_minimizing (I := I) g hEnorm p y
  refine ⟨v, ?_, hv_exp⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hnorm : ‖v‖ = Real.sqrt (g.inner p v v) := by
    have hz := hEnorm p v
    rw [← ofReal_norm] at hz
    exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg v) (Real.sqrt_nonneg _)).mp hz
  have hedist : edist p y ≤ ENNReal.ofReal R :=
    le_trans (Metric.edist_le_ediam_of_mem (Set.mem_univ p) (Set.mem_univ y)) hdiam
  have hre : riemannianEDist I p y = edist p y := (IsRiemannianManifold.out (I := I) p y).symm
  rw [hnorm, hv_len, hre]
  calc (edist p y).toReal
      ≤ (ENNReal.ofReal R).toReal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hedist
    _ = R := ENNReal.toReal_ofReal hR

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem isCompact_univ
    {M : Type*}
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [T2Space (TangentBundle I M)]
    [SigmaCompactSpace M] [ConnectedSpace M]
    [PseudoEMetricSpace M]
    (g : SmoothRiemannianMetric I M)
    [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (hdim : 2 ≤ Module.finrank ℝ E)
    {K : ℝ} (hK : 0 < K)
    (hRic : RicciBoundedBelow (I := I) g (((Module.finrank ℝ E : ℝ) - 1) * K))
    (hEnorm : IsMetricNorm (I := I) (M := M) g) :
    IsCompact (Set.univ : Set M) := by
  let p : M := Classical.arbitrary M
  set R : ℝ := Real.pi / Real.sqrt K with hR_def
  have hR_nn : 0 ≤ R := by
    have hpi_nn : (0 : ℝ) ≤ Real.pi := Real.pi_nonneg
    have hsqrt_nn : (0 : ℝ) ≤ Real.sqrt K := Real.sqrt_nonneg K
    exact div_nonneg hpi_nn hsqrt_nn
  have hdiam : Metric.ediam (Set.univ : Set M) ≤ ENNReal.ofReal R :=
    bonnet_myers_diameter_of_ricci_bound (E := E) g hdim hK hRic hEnorm
  have hsurj :=
    expMapIntrinsic_surjective_on_closedBall_of_ediam_le (I := I) (E := E) g hEnorm p hR_nn hdiam
  have himg :=
    isCompact_image_closedBall_under_expMapIntrinsic (I := I) (E := E) g hEnorm p (R := R)
  exact himg.of_isClosed_subset isClosed_univ hsurj

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem bonnet_myers_compactSpace_of_ricci_bound
    {M : Type*}
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [T2Space (TangentBundle I M)]
    [SigmaCompactSpace M] [ConnectedSpace M]
    [PseudoEMetricSpace M]
    (g : SmoothRiemannianMetric I M)
    [Bundle.RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun (x : M) ↦ TangentSpace I x)]
    (hdim : 2 ≤ Module.finrank ℝ E)
    {K : ℝ} (hK : 0 < K)
    (hRic : RicciBoundedBelow (I := I) g (((Module.finrank ℝ E : ℝ) - 1) * K))
    (hEnorm : IsMetricNorm (I := I) (M := M) g) :
    CompactSpace M :=
  isCompact_univ_iff.mp (isCompact_univ (E := E) g hdim hK hRic hEnorm)
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem bonnet_myers_compactSpace_of_complete_metric
    {M : Type*}
    {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [T2Space (TangentBundle I M)]
    [SigmaCompactSpace M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hdim : 2 ≤ Module.finrank ℝ E)
    {K : ℝ} (hK : 0 < K)
    (hRic : RicciBoundedBelow (I := I) g (((Module.finrank ℝ E : ℝ) - 1) * K)) :
    CompactSpace M := by
  let : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  let : TopologicalSpace.MetrizableSpace M :=
    Manifold.metrizableSpace I M
  let : T3Space M := inferInstance
  let : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  let : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  let : PseudoEMetricSpace M := inferInstance
  let : CompleteSpace M := hcomplete.complete
  have hEnorm : IsMetricNorm (I := I) (M := M) g := by
    intro x v
    exact tensor0SBundle_enorm_eq_riemannianBundle_enorm (I := I) g x v
  exact bonnet_myers_compactSpace_of_ricci_bound (I := I) (M := M) g
    hdim hK hRic hEnorm
end BonnetMyers
end Riemannian
end Geometry
end DifferentialGeometry

end
