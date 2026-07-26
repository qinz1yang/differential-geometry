import Mathlib.Topology.Order.IntermediateValue
import DifferentialGeometry.Geometry.Comparison.TangentNormDiamond
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Geometry.Metric.Completeness

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Proper Riemannian Metric From Intrinsic Hopf--Rinow

This file packages the compactness and intermediate-distance consequences of the
intrinsic Hopf--Rinow endpoint in `Exponential/MinimizingGeodesic.lean`.
-/

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Topology Manifold ContDiff ENNReal

namespace DifferentialGeometry

namespace RiemannianMetricComplete

open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- A finite-radius closed ball for the extended distance of a complete
Riemannian metric is compact, without a connectedness assumption. -/
theorem closedEBall_isCompact
    {g : SmoothRiemannianMetric I M}
    (hg : RiemannianMetricComplete (I := I) g)
    (O : M) (R : ℝ) :
    IsCompact
      {x : M |
        riemannianEDistOf (I := I) g O x ≤ ENNReal.ofReal R} := by
  letI : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  letI : TopologicalSpace.MetrizableSpace M :=
    Manifold.metrizableSpace I M
  letI : T3Space M := inferInstance
  letI : RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E
      (fun x : M => TangentSpace I x) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x v w; rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : CompleteSpace M := hg.complete
  have hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)) :=
    fun x v =>
      tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) g x v
  let ρ : ℝ := (ENNReal.ofReal R).toReal
  haveI : FiniteDimensional ℝ (TangentSpace I O) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  haveI : ProperSpace (TangentSpace I O) :=
    FiniteDimensional.proper_real (TangentSpace I O)
  have himg :
      IsCompact
        ((fun v => expMapIntrinsic (I := I) g hEnorm O v) ''
          Metric.closedBall (0 : TangentSpace I O) ρ) :=
    (isCompact_closedBall (0 : TangentSpace I O) ρ).image
      (expMapIntrinsic_continuous (I := I) g hEnorm O)
  have hclosed :
      IsClosed
        {x : M |
          riemannianEDistOf (I := I) g O x ≤ ENNReal.ofReal R} := by
    have hset :
        {x : M |
          riemannianEDistOf (I := I) g O x ≤ ENNReal.ofReal R} =
          Metric.closedEBall O (ENNReal.ofReal R) := by
      ext x
      rw [Metric.mem_closedEBall',
        IsRiemannianManifold.out (I := I) O x]
      rfl
    rw [hset]
    exact Metric.isClosed_closedEBall
  refine himg.of_isClosed_subset hclosed ?_
  intro x hx
  have hfin :
      riemannianEDist I O x ≠ (⊤ : ℝ≥0∞) := by
    apply ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    simpa only [riemannianEDistOf] using hx
  obtain ⟨v, hv_exp, hv_len⟩ :=
    hopf_rinow_expMapIntrinsic_surjective_minimizing_of_ne_top
      (I := I) g hEnorm O x hfin
  refine ⟨v, ?_, hv_exp⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hnorm : ‖v‖ = Real.sqrt (g.inner O v v) := by
    have hv := hEnorm O v
    rw [← ofReal_norm_eq_enorm] at hv
    exact (ENNReal.ofReal_eq_ofReal_iff
      (norm_nonneg v) (Real.sqrt_nonneg _)).mp hv
  rw [hnorm, hv_len]
  exact (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).2
    (by simpa only [riemannianEDistOf] using hx)

end RiemannianMetricComplete

namespace Geometry
namespace Riemannian
namespace HopfRinow

open DifferentialGeometry.Geometry.Riemannian.Exponential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [InnerProductSpace ℝ E] [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] [T3Space M]
variable [RiemannianBundle (fun x : M => TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The finite metric-space structure associated to the Riemannian emetric. -/
@[reducible] noncomputable def riemMetricSpace
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] :
    MetricSpace M :=
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  EMetricSpace.toMetricSpace (fun x y : M => by
    rw [IsRiemannianManifold.out (I := I) x y]
    exact riemannianEDist_ne_top (I := I) x y)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- The metric `riemMetricSpace` realizes the ambient Riemannian emetric. -/
theorem riemMetric_realizes
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)] :
    ∀ x y : M,
      (letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
       edist x y) =
      ENNReal.ofReal (letI : MetricSpace M := riemMetricSpace (I := I) (M := M)
       dist x y) := by
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  letI : MetricSpace M := riemMetricSpace (I := I) (M := M)
  intro x y
  exact edist_dist x y

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Distance in `riemMetricSpace` is the real value of `riemannianEDist`. -/
theorem riemMetric_dist_eq
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (x y : M) :
    letI : MetricSpace M := riemMetricSpace (I := I) (M := M)
    dist x y = (riemannianEDist I x y).toReal := by
  letI : MetricSpace M := riemMetricSpace (I := I) (M := M)
  have hreal := riemMetric_realizes (I := I) (M := M) x y
  have hfin : riemannianEDist I x y ≠ (⊤ : ℝ≥0∞) :=
    riemannianEDist_ne_top (I := I) x y
  have hout :
      (letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
       edist x y) = riemannianEDist I x y := by
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    exact IsRiemannianManifold.out (I := I) x y
  have hriem : riemannianEDist I x y = ENNReal.ofReal (dist x y) := by
    rw [← hout]
    exact hreal
  rw [hriem, ENNReal.toReal_ofReal dist_nonneg]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Compactness of a tangent closed ball's image under the intrinsic exponential. -/
theorem expImgClosedBall_compact
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (hcomplete :
      letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
      CompleteSpace M)
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (R : ℝ) :
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    IsCompact ((fun v => expMapIntrinsic (I := I) g hEnorm p v) ''
      Metric.closedBall (0 : TangentSpace I p) R) := by
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  haveI : CompleteSpace M := hcomplete
  haveI : FiniteDimensional ℝ (TangentSpace I p) :=
    inferInstanceAs (FiniteDimensional ℝ E)
  haveI : ProperSpace (TangentSpace I p) :=
    FiniteDimensional.proper_real (TangentSpace I p)
  exact (isCompact_closedBall (0 : TangentSpace I p) R).image
    (expMapIntrinsic_continuous (I := I) g hEnorm p)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Points in a Riemannian closed ball are reached by bounded intrinsic
exponential vectors. -/
theorem closedBall_subset_expImg
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (hcomplete :
      letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
      CompleteSpace M)
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {R : ℝ} :
    letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
    (letI : MetricSpace M := riemMetricSpace (I := I) (M := M)
     Metric.closedBall p R) ⊆
      (fun v => expMapIntrinsic (I := I) g hEnorm p v) ''
        Metric.closedBall (0 : TangentSpace I p) R := by
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  haveI : CompleteSpace M := hcomplete
  letI : MetricSpace M := riemMetricSpace (I := I) (M := M)
  intro y hy
  obtain ⟨v, hv_exp, hv_len⟩ :=
    hopf_rinow_expMapIntrinsic_surjective_minimizing (I := I) g hEnorm p y
  refine ⟨v, ?_, hv_exp⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hnorm : ‖v‖ = Real.sqrt (g.inner p v v) := by
    have hz := hEnorm p v
    rw [← ofReal_norm_eq_enorm] at hz
    exact (ENNReal.ofReal_eq_ofReal_iff (norm_nonneg v) (Real.sqrt_nonneg _)).mp hz
  rw [hnorm, hv_len]
  have hy' : dist p y ≤ R := by
    simpa [Metric.mem_closedBall, dist_comm] using hy
  rw [riemMetric_dist_eq (I := I) (M := M) p y] at hy'
  exact hy'

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Hopf--Rinow properness for the finite Riemannian metric. -/
theorem properSpace_riemMetric
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (hcomplete :
      letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
      CompleteSpace M)
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v))) :
    letI : MetricSpace M := riemMetricSpace (I := I) (M := M)
    ProperSpace M := by
  letI : MetricSpace M := riemMetricSpace (I := I) (M := M)
  refine ProperSpace.of_isCompact_closedBall_of_le (α := M) 0 ?_
  intro p R hR
  have hsubset :=
    closedBall_subset_expImg (I := I) (M := M) hcomplete g hEnorm p (R := R)
  have himg :=
    expImgClosedBall_compact (I := I) (M := M) hcomplete g hEnorm p R
  have hclosed : IsClosed (Metric.closedBall p R) := by
    simpa [riemMetricSpace] using
      (Metric.isClosed_closedBall : IsClosed (Metric.closedBall p R))
  exact himg.of_isClosed_subset hclosed hsubset

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
/-- Every intermediate distance to a basepoint is realized in the finite
Riemannian metric. -/
theorem intermediateDist_riemMetric
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (hcomplete :
      letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
      CompleteSpace M)
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ x : M, ∀ v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (O : M) :
    letI : MetricSpace M := riemMetricSpace (I := I) (M := M)
    ∀ p : M, ∀ t : ℝ, 0 ≤ t → t ≤ dist p O →
      ∃ q : M, dist q O = t := by
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  haveI : CompleteSpace M := hcomplete
  letI : MetricSpace M := riemMetricSpace (I := I) (M := M)
  intro p t ht0 htp
  obtain ⟨v, hv_exp, _hv_len⟩ :=
    hopf_rinow_expMapIntrinsic_surjective_minimizing (I := I) g hEnorm O p
  let γ : ℝ → M := intrinsicGeodesic (I := I) g hEnorm O v
  let f : ℝ → ℝ := fun s => dist (γ s) O
  have hγ0 : γ 0 = O := intrinsicGeodesic_zero (I := I) g hEnorm O v
  have hγ1 : γ 1 = p := by
    simpa [γ, expMapIntrinsic_def] using hv_exp
  have hf_cont : ContinuousOn f (Set.Icc (0 : ℝ) 1) := by
    exact ((intrinsicGeodesic_continuous (I := I) g hEnorm O v).dist
      continuous_const).continuousOn
  have hmem : t ∈ Set.Icc (f 0) (f 1) := by
    rw [Set.mem_Icc]
    constructor
    · simpa [f, hγ0] using ht0
    · simpa [f, hγ1, dist_comm] using htp
  obtain ⟨s, hsIcc, hs⟩ :=
    intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hf_cont hmem
  exact ⟨γ s, by simpa [f] using hs⟩

end HopfRinow
end Riemannian
end Geometry
end DifferentialGeometry

end
