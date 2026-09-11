import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.Hamilton
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.Interfaces
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.Noncollapsing.Predicates
import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.Parabolic
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.ApproximateIsometry.MetricApproximation.Defs
import DifferentialGeometry.Geometry.Curvature.Bounds.ScalarNorm
import DifferentialGeometry.Geometry.Metric.Distance.Ball
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness

set_option autoImplicit false

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood

noncomputable section

universe u uE uH

open Bundle DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal

section Definitions

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M]
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}



def frozenBackwardCylinder (S : SolutionOn (I := I) (M := M) D)
    (x : M) (t A depth Q : Real) : Set (M × Real) :=
  riemannianClosedBallOf (I := I) (S.base.metric t) x (A / Real.sqrt Q) ×ˢ
    Set.Icc (t - depth / Q) t

def FrozenBackwardCylinderAdmissible
    (D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval) (t depth Q : Real) : Prop :=
  Set.Icc (t - depth / Q) t ⊆ D.carrier

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 1 M] [T2Space M]
  [SigmaCompactSpace M] in
theorem frozenBall_paraSolution
    (S : SolutionOn (I := I) (M := M) D) (x : M) (t Q A : Real)
    (hQ : 0 < Q) (ht : t ∈ D.carrier) :
    riemannianClosedBallOf (I := I)
        ((parabolicSolution (I := I) S t Q hQ ht).base.metric 0) x A =
      riemannianClosedBallOf (I := I) (S.base.metric t) x (A / Real.sqrt Q) := by
  have hmetric : (parabolicSolution (I := I) S t Q hQ ht).base.metric 0 =
      scaleMetric (I := I) Q hQ (S.base.metric t) := by
    change scaleMetric (I := I) Q hQ (S.base.metric (parabolicTime t Q 0)) =
      scaleMetric (I := I) Q hQ (S.base.metric t)
    rw [parabolicTime_zero]
  have hs : Real.sqrt Q ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hQ)
  have hA : Real.sqrt Q * (A / Real.sqrt Q) = A := by
    field_simp
  have hscale := riemannianClosedBallOf_scaleMetric (I := I) Q hQ (S.base.metric t) x
    (A / Real.sqrt Q)
  rw [hA] at hscale
  rw [hmetric]
  exact hscale

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 1 M] [T2Space M]
  [SigmaCompactSpace M] in
theorem frozenBackwardCylinder_paraSolution
    (S : SolutionOn (I := I) (M := M) D) (x : M) (t Q A depth : Real)
    (hQ : 0 < Q) (ht : t ∈ D.carrier) :
    frozenBackwardCylinder (I := I) (parabolicSolution (I := I) S t Q hQ ht) x 0 A depth 1 =
      (fun p : M × Real => (p.1, parabolicTime t Q p.2)) ⁻¹'
        frozenBackwardCylinder (I := I) S x t A depth Q := by
  have hball := frozenBall_paraSolution (I := I) S x t Q A hQ ht
  have hdiv : ∀ a b : Real, a / Q ≤ b / Q ↔ a ≤ b := fun a b =>
    div_le_div_iff_of_pos_right hQ
  ext p
  have h1 : p.1 ∈ riemannianClosedBallOf (I := I)
        ((parabolicSolution (I := I) S t Q hQ ht).base.metric 0) x (A / Real.sqrt 1) ↔
      p.1 ∈ riemannianClosedBallOf (I := I) (S.base.metric t) x (A / Real.sqrt Q) := by
    rw [Real.sqrt_one, div_one, hball]
  have h2 : p.2 ∈ Set.Icc ((0 : Real) - depth / 1) 0 ↔
      parabolicTime t Q p.2 ∈ Set.Icc (t - depth / Q) t := by
    constructor
    · rintro ⟨hs1, hs2⟩
      simp only [div_one, zero_sub] at hs1
      have hlow : (-depth) / Q ≤ p.2 / Q := (hdiv _ _).2 hs1
      rw [neg_div] at hlow
      have hhigh : p.2 / Q ≤ 0 / Q := (hdiv _ _).2 hs2
      rw [zero_div] at hhigh
      exact ⟨by simp only [parabolicTime]; linarith, by simp only [parabolicTime]; linarith⟩
    · rintro ⟨hs1, hs2⟩
      simp only [parabolicTime] at hs1 hs2
      refine ⟨?_, ?_⟩
      · simp only [div_one, zero_sub]
        have hlow : (-depth) / Q ≤ p.2 / Q := by
          rw [neg_div]
          linarith
        exact (hdiv _ _).1 hlow
      · have hhigh : p.2 / Q ≤ 0 / Q := by
          rw [zero_div]
          linarith
        exact (hdiv _ _).1 hhigh
  constructor
  · rintro ⟨ha, hb⟩
    exact ⟨h1.1 ha, h2.1 hb⟩
  · rintro ⟨ha, hb⟩
    exact ⟨h1.2 ha, h2.2 hb⟩



def ancientTimeInterval : DifferentialGeometry.Geometry.Curvature.RealTimeInterval :=
  DifferentialGeometry.Geometry.Curvature.RealTimeInterval.infiniteClosed 0 0 le_rfl

@[simp] theorem ancientTimeInterval_carrier :
    ancientTimeInterval.carrier = Set.Iic 0 := rfl

@[simp] theorem ancientTimeInterval_regular :
    ancientTimeInterval.regular = Set.Iio 0 := rfl

def PointedFlowNonnegativeCurvatureOperator
    (F : PointedFlowData.{u, uE, uH} (I := I) D) (t : Real) : Prop :=
  letI : TopologicalSpace F.M := F.topology
  letI : ChartedSpace H F.M := F.charted
  letI : IsManifold I ∞ F.M := F.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) F.M := by
    change IsManifold I ∞ F.M
    infer_instance
  letI : SigmaCompactSpace F.M := F.sigmaCompact
  letI : T2Space F.M := F.t2
  ∀ x : F.M, ∀ (n : Nat) (c : Fin n → Real) (v w : Fin n → TangentSpace I x),
    0 ≤ ∑ i, ∑ j, c i * c j *
      F.S.base.rm04 t x (vec4 (I := I) (v i) (w i) (w j) (v j))

def PointedFlowScalarBounded
    (F : PointedFlowData.{u, uE, uH} (I := I) D) (C : Real) : Prop :=
  letI : TopologicalSpace F.M := F.topology
  letI : ChartedSpace H F.M := F.charted
  letI : IsManifold I ∞ F.M := F.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) F.M := by
    change IsManifold I ∞ F.M
    infer_instance
  letI : SigmaCompactSpace F.M := F.sigmaCompact
  letI : T2Space F.M := F.t2
  ∀ t ∈ D.carrier, ∀ x : F.M, 0 ≤ F.S.scalar t x ∧ F.S.scalar t x ≤ C


def PointedFlowRmNormSqBounded
    (F : PointedFlowData.{u, uE, uH} (I := I) D) (C : Real) : Prop :=
  ∀ t ∈ D.carrier, ∀ x : F.M, F.rmNormSq (I := I) t x ≤ C

def PointedFlowScalarAtBase
    (F : PointedFlowData.{u, uE, uH} (I := I) D) (r : Real) : Prop :=
  letI : TopologicalSpace F.M := F.topology
  letI : ChartedSpace H F.M := F.charted
  letI : IsManifold I ∞ F.M := F.smooth
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) F.M := by
    change IsManifold I ∞ F.M
    infer_instance
  letI : SigmaCompactSpace F.M := F.sigmaCompact
  letI : T2Space F.M := F.t2
  F.S.scalar 0 F.basepoint = r


def PointedFlowNotFlat (F : PointedFlowData.{u, uE, uH} (I := I) D) : Prop :=
  ∃ t ∈ D.carrier, ∃ x : F.M, F.rmNormSq (I := I) t x ≠ 0

def PointedFlowNoncollapsedAllScales
    (F : PointedFlowData.{u, uE, uH} (I := I) D) (kappa : Real) : Prop :=
  letI : TopologicalSpace F.M := F.topology
  letI : ChartedSpace H F.M := F.charted
  letI : IsManifold I ∞ F.M := F.smooth
  letI : IsManifold I 1 F.M :=
    IsManifold.of_le (I := I) (M := F.M) (n := (∞ : WithTop ℕ∞))
      (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) F.M := by
    change IsManifold I ∞ F.M
    infer_instance
  letI : SigmaCompactSpace F.M := F.sigmaCompact
  letI : T2Space F.M := F.t2
  ∀ (time : DifferentialGeometry.Geometry.Curvature.RealTimeInterval.FlowTime D)
    (B : Perelman.FlowMetricBall (I := I) (M := F.M) F.S time),
    B.IsSpatiallyKappaNoncollapsed kappa

theorem pointedFlowNoncollapsedAllScales_iff
    (F : PointedFlowData.{u, uE, uH} (I := I) D) (kappa : Real) :
    PointedFlowNoncollapsedAllScales (I := I) F kappa ↔
      PointedFlowSpatiallyKappaNoncollapsed (I := I) F kappa Set.univ := by
  simp only [PointedFlowNoncollapsedAllScales, PointedFlowSpatiallyKappaNoncollapsed,
    Perelman.FlowMetricBall.IsSpatiallyKappaNoncollapsed,
    Perelman.FlowMetricBall.IsSpatiallyRmControlled, Set.mem_univ, forall_const]

structure IsAncientKappaSolution (kappa : Real)
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : Prop where
  kappa_pos : 0 < kappa
  carrier_eq : D.carrier = Set.Iic 0
  regular_eq : D.regular = Set.Iio 0
  connected :
    letI : TopologicalSpace F.M := F.topology
    ConnectedSpace F.M
  complete : ∀ t ∈ D.carrier, MetricComplete (I := I) (F.atTime (I := I) t)
  nonnegativeCurvatureOperator :
    ∀ t ∈ D.carrier, PointedFlowNonnegativeCurvatureOperator (I := I) F t
  globalScalarBound : ∃ C : Real, PointedFlowScalarBounded (I := I) F C
  noncollapsed : PointedFlowNoncollapsedAllScales (I := I) F kappa
  notFlat : PointedFlowNotFlat (I := I) F

theorem pointedFlowNotFlat_of_scalar_ne_zero
    (F : PointedFlowData.{u, uE, uH} (I := I) D) {t : Real} (ht : t ∈ D.carrier)
    (x : F.M)
    (hx :
      letI : TopologicalSpace F.M := F.topology
      letI : ChartedSpace H F.M := F.charted
      letI : IsManifold I ∞ F.M := F.smooth
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) F.M := by
        change IsManifold I ∞ F.M
        infer_instance
      letI : SigmaCompactSpace F.M := F.sigmaCompact
      letI : T2Space F.M := F.t2
      F.S.scalar t x ≠ 0) :
    PointedFlowNotFlat (I := I) F := by
  let : TopologicalSpace F.M := F.topology
  let : ChartedSpace H F.M := F.charted
  let : IsManifold I ∞ F.M := F.smooth
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) F.M := by
    change IsManifold I ∞ F.M
    infer_instance
  let : SigmaCompactSpace F.M := F.sigmaCompact
  let : T2Space F.M := F.t2
  refine ⟨t, ht, x, ?_⟩
  intro hzero
  apply hx
  have hbound := DifferentialGeometry.Geometry.Curvature.scalar_abs_le_rm (I := I) (M := F.M)
    (F.S.base.metric t) x
  have hrw : Real.sqrt (Tensor0SBundle.normSq0S (I := I) (F.S.base.metric t) x 4
      (DifferentialGeometry.Geometry.Curvature.metricRm04At (I := I) (M := F.M)
        (F.S.base.metric t) x)) = 0 := by
    have hz : Tensor0SBundle.normSq0S (I := I) (F.S.base.metric t) x 4
        (DifferentialGeometry.Geometry.Curvature.metricRm04At (I := I) (M := F.M)
          (F.S.base.metric t) x) = 0 := hzero
    rw [hz, Real.sqrt_zero]
  rw [hrw, mul_zero] at hbound
  have habs : |DifferentialGeometry.Geometry.Curvature.metricScalarAt (I := I) (M := F.M)
      (F.S.base.metric t) x| = 0 := le_antisymm hbound (abs_nonneg _)
  exact abs_eq_zero.1 habs




def modelRadius (eps : Real) : Real := (Real.sqrt eps)⁻¹


def modelDepth (eps : Real) : Real := eps⁻¹


def modelOrder (eps : Real) : Nat := ⌈eps⁻¹⌉₊ + 1

theorem modelRadius_anti {delta eps : Real} (hd : 0 < delta) (hde : delta ≤ eps) :
    modelRadius eps ≤ modelRadius delta := by
  have hsd : 0 < Real.sqrt delta := Real.sqrt_pos.2 hd
  have hs : Real.sqrt delta ≤ Real.sqrt eps := Real.sqrt_le_sqrt hde
  unfold modelRadius
  rw [inv_eq_one_div, inv_eq_one_div]
  exact div_le_div_of_nonneg_left zero_le_one hsd hs

theorem modelDepth_anti {delta eps : Real} (hd : 0 < delta) (hde : delta ≤ eps) :
    modelDepth eps ≤ modelDepth delta := by
  unfold modelDepth
  rw [inv_eq_one_div, inv_eq_one_div]
  exact div_le_div_of_nonneg_left zero_le_one hd hde

theorem modelOrder_anti {delta eps : Real} (hd : 0 < delta) (hde : delta ≤ eps) :
    modelOrder eps ≤ modelOrder delta := by
  have hinv : eps⁻¹ ≤ delta⁻¹ := by
    rw [inv_eq_one_div, inv_eq_one_div]
    exact div_le_div_of_nonneg_left zero_le_one hd hde
  exact Nat.add_le_add_right (Nat.ceil_le_ceil hinv) 1

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 1 M] [T2Space M]
  [SigmaCompactSpace M] in
theorem inner_self_nonneg (g : SmoothRiemannianMetric I M) (y : M) (v : TangentSpace I y) :
    0 ≤ g.inner y v v := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · exact (g.pos y v hv).le

def rescaledMetric (S : SolutionOn (I := I) (M := M) D) (t Q : Real) (hQ : 0 < Q) :
    Real → SmoothRiemannianMetric I M :=
  fun s => scaleMetric (I := I) Q hQ (S.base.metric (parabolicTime t Q s))

omit [FiniteDimensional Real E] [CompleteSpace E] [IsManifold I 1 M] [T2Space M]
  [SigmaCompactSpace M] in
theorem rescaledMetric_eq_paraSolution
    (S : SolutionOn (I := I) (M := M) D) (t Q : Real) (hQ : 0 < Q) (ht : t ∈ D.carrier) :
    rescaledMetric (I := I) S t Q hQ = (parabolicSolution (I := I) S t Q hQ ht).base.metric := rfl

section ModelComparison

variable {N : Type u} [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
variable [IsManifold I 1 N] [T2Space N] [SigmaCompactSpace N]

structure ModelComparison (eps : Real)
    (h : Real → SmoothRiemannianMetric I N)
    (ghat : Real → SmoothRiemannianMetric I M)
    (p : N) (x : M)
    (F : PartialDiffeomorph I I N M (∞ : WithTop ℕ∞)) where
  buffered_ball_subset :
    riemannianClosedBallOf (I := I) (h 0) p (modelRadius eps + 1) ⊆ F.source
  base_map : F p = x
  pullback : Real → Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
    (I := I) (M := N) (n := (∞ : WithTop ℕ∞)) 2




  pullback_apply : ∀ (s : Real) (y : N), y ∈ F.source → ∀ (v : Fin 2 → TangentSpace I y),
    pullback s y v =
      (ghat s).inner (F y)
        (mfderiv I I (F : N → M) y (v 0)) (mfderiv I I (F : N → M) y (v 1))
  jet : Nat → Real → Tensor0SBundle.Tensor0SField (𝕜 := Real) (E := E) (H := H)
    (I := I) (M := N) (n := (∞ : WithTop ℕ∞)) 2
  jet_zero : ∀ (s : Real) (y : N) (v : Fin 2 → TangentSpace I y),
    jet 0 s y v = pullback s y v - (h s).inner y (v 0) (v 1)
  jet_succ : ∀ (b : Nat) (s : Real) (y : N) (v : Fin 2 → TangentSpace I y),
    jet (b + 1) s y v = derivWithin (fun sigma : Real => jet b sigma y v) (Set.Iic 0) s
  metric_equivalence : ∀ s ∈ Set.Icc (-(modelDepth eps)) (0 : Real),
    ∀ y ∈ riemannianClosedBallOf (I := I) (h 0) p (modelRadius eps),
      ∀ v : TangentSpace I y,
        (1 - eps) * (h s).inner y v v ≤ pullback s y (fun _ => v) ∧
          pullback s y (fun _ => v) ≤ (1 + eps) * (h s).inner y v v
  cm_close : ∀ a b : Nat, a + 2 * b ≤ modelOrder eps →
    ∀ s ∈ Set.Icc (-(modelDepth eps)) (0 : Real),
      ∀ y ∈ riemannianClosedBallOf (I := I) (h 0) p (modelRadius eps),
        tensor02CovDerivNormWith (I := I) a (jet b s) (h s) (h s) y ≤ eps
  source_capture :
    riemannianBallOf (I := I) (ghat 0) x (modelRadius eps - 1) ⊆ (F : N → M) '' F.source

def ModelComparison.mono {delta eps : Real} (hd : 0 < delta) (hde : delta ≤ eps)
    {h : Real → SmoothRiemannianMetric I N} {ghat : Real → SmoothRiemannianMetric I M}
    {p : N} {x : M} {F : PartialDiffeomorph I I N M (∞ : WithTop ℕ∞)}
    (C : ModelComparison (I := I) delta h ghat p x F) :
    ModelComparison (I := I) eps h ghat p x F where
  buffered_ball_subset :=
    Set.Subset.trans
      (riemannianClosedBallOf_mono (I := I) (h 0) p
        (by have := modelRadius_anti hd hde; linarith))
      C.buffered_ball_subset
  base_map := C.base_map
  pullback := C.pullback
  pullback_apply := C.pullback_apply
  jet := C.jet
  jet_zero := C.jet_zero
  jet_succ := C.jet_succ
  metric_equivalence := by
    intro s hs y hy v
    have hwin : s ∈ Set.Icc (-(modelDepth delta)) (0 : Real) := by
      refine ⟨?_, hs.2⟩
      have hdep := modelDepth_anti hd hde
      have := hs.1
      linarith
    have hball : y ∈ riemannianClosedBallOf (I := I) (h 0) p (modelRadius delta) :=
      riemannianClosedBallOf_mono (I := I) (h 0) p (modelRadius_anti hd hde) hy
    obtain ⟨hlow, hhigh⟩ := C.metric_equivalence s hwin y hball v
    have hnn : 0 ≤ (h s).inner y v v := inner_self_nonneg (I := I) (h s) y v
    have hgap : 0 ≤ (eps - delta) * (h s).inner y v v :=
      mul_nonneg (sub_nonneg.2 hde) hnn
    constructor
    · nlinarith
    · nlinarith
  cm_close := by
    intro a b hab s hs y hy
    have horder : a + 2 * b ≤ modelOrder delta :=
      le_trans hab (modelOrder_anti hd hde)
    have hwin : s ∈ Set.Icc (-(modelDepth delta)) (0 : Real) := by
      refine ⟨?_, hs.2⟩
      have hdep := modelDepth_anti hd hde
      have := hs.1
      linarith
    have hball : y ∈ riemannianClosedBallOf (I := I) (h 0) p (modelRadius delta) :=
      riemannianClosedBallOf_mono (I := I) (h 0) p (modelRadius_anti hd hde) hy
    exact le_trans (C.cm_close a b horder s hwin y hball) hde
  source_capture :=
    Set.Subset.trans
      (riemannianBallOf_mono (I := I) (ghat 0) x
        (by have := modelRadius_anti hd hde; linarith))
      C.source_capture

end ModelComparison

structure KappaModelWitness (eps kappa : Real)
    (S : SolutionOn (I := I) (M := M) D) (x : M) (t : Real) where
  eps_pos : 0 < eps
  eps_lt_one : eps < 1
  time_mem : t ∈ D.carrier
  scalar_pos : 0 < S.scalar t x
  window_mem : Set.Icc (t - (eps * S.scalar t x)⁻¹) t ⊆ D.carrier
  model : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval
  model_ancient : IsAncientKappaSolution (I := I) kappa model
  model_scalar_base : PointedFlowScalarAtBase (I := I) model 1
  embedding :
    letI : TopologicalSpace model.M := model.topology
    letI : ChartedSpace H model.M := model.charted
    PartialDiffeomorph I I model.M M (∞ : WithTop ℕ∞)
  comparison :
    letI : TopologicalSpace model.M := model.topology
    letI : ChartedSpace H model.M := model.charted
    letI : IsManifold I ∞ model.M := model.smooth
    letI : IsManifold I 1 model.M :=
      IsManifold.of_le (I := I) (M := model.M) (n := (∞ : WithTop ℕ∞))
        (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) model.M := by
      change IsManifold I ∞ model.M
      infer_instance
    letI : SigmaCompactSpace model.M := model.sigmaCompact
    letI : T2Space model.M := model.t2
    ModelComparison (I := I) (M := M) (N := model.M) eps
      (fun s => model.S.base.metric s)
      (rescaledMetric (I := I) S t (S.scalar t x) scalar_pos)
      model.basepoint x embedding

def KappaModelWitness.IsOrientationPreserving {eps kappa : Real}
    {S : SolutionOn (I := I) (M := M) D} {x : M} {t : Real}
    (orient : ∀ P : PointedFlowData.{u, uE, uH} (I := I) ancientTimeInterval,
      (letI : TopologicalSpace P.M := P.topology
       letI : ChartedSpace H P.M := P.charted
       PartialDiffeomorph I I P.M M (∞ : WithTop ℕ∞)) → Prop)
    (W : KappaModelWitness (I := I) eps kappa S x t) : Prop :=
  orient W.model W.embedding


def IsGoodPoint (eps kappa : Real) (S : SolutionOn (I := I) (M := M) D)
    (x : M) (t : Real) : Prop :=
  Nonempty (KappaModelWitness.{u, uE, uH} (I := I) eps kappa S x t)


def IsBadPoint (eps kappa : Real) (S : SolutionOn (I := I) (M := M) D)
    (x : M) (t : Real) : Prop :=
  ¬ IsGoodPoint.{u, uE, uH} (I := I) eps kappa S x t

def KappaModelWitness.mono {delta eps kappa : Real}
    {S : SolutionOn (I := I) (M := M) D} {x : M} {t : Real}
    (hde : delta ≤ eps) (heps : eps < 1)
    (W : KappaModelWitness (I := I) delta kappa S x t) :
    KappaModelWitness (I := I) eps kappa S x t where
  eps_pos := lt_of_lt_of_le W.eps_pos hde
  eps_lt_one := heps
  time_mem := W.time_mem
  scalar_pos := W.scalar_pos
  window_mem := by
    have hdq : 0 < delta * S.scalar t x := mul_pos W.eps_pos W.scalar_pos
    have hle : delta * S.scalar t x ≤ eps * S.scalar t x :=
      mul_le_mul_of_nonneg_right hde W.scalar_pos.le
    have hinv : (eps * S.scalar t x)⁻¹ ≤ (delta * S.scalar t x)⁻¹ := by
      rw [inv_eq_one_div, inv_eq_one_div]
      exact div_le_div_of_nonneg_left zero_le_one hdq hle
    exact Set.Subset.trans (Set.Icc_subset_Icc (by linarith) le_rfl) W.window_mem
  model := W.model
  model_ancient := W.model_ancient
  model_scalar_base := W.model_scalar_base
  embedding := W.embedding
  comparison := by
    letI : TopologicalSpace W.model.M := W.model.topology
    letI : ChartedSpace H W.model.M := W.model.charted
    letI : IsManifold I ∞ W.model.M := W.model.smooth
    letI : IsManifold I 1 W.model.M :=
      IsManifold.of_le (I := I) (M := W.model.M) (n := (∞ : WithTop ℕ∞))
        (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) W.model.M := by
      change IsManifold I ∞ W.model.M
      infer_instance
    letI : SigmaCompactSpace W.model.M := W.model.sigmaCompact
    letI : T2Space W.model.M := W.model.t2
    exact W.comparison.mono W.eps_pos hde

omit [T2Space M] [SigmaCompactSpace M] in
theorem isGoodPoint_mono {delta eps kappa : Real}
    {S : SolutionOn (I := I) (M := M) D} {x : M} {t : Real}
    (hde : delta ≤ eps) (heps : eps < 1)
    (hgood : IsGoodPoint.{u, uE, uH} (I := I) delta kappa S x t) :
    IsGoodPoint.{u, uE, uH} (I := I) eps kappa S x t :=
  hgood.elim fun W => ⟨W.mono hde heps⟩

def GoodSetOpen (eps kappa : Real) (S : SolutionOn (I := I) (M := M) D) : Prop :=
  ∀ U : Set (M × Real), IsOpen U →
    (∀ q ∈ U, Set.Icc (q.2 - (eps * S.scalar q.2 q.1)⁻¹) q.2 ⊆ D.carrier) →
      IsOpen (U ∩ {q : M × Real | IsGoodPoint.{u, uE, uH} (I := I) eps kappa S q.1 q.2})

end Definitions

section CurvatureScaleDerivatives

theorem inverse_root_gradient_bound_iff {R G C : Real} (hR : 0 < R) :
    1 / 2 * G / (R * Real.sqrt R) ≤ C ↔ G ≤ 2 * C * (R * Real.sqrt R) := by
  have hpos : 0 < R * Real.sqrt R := mul_pos hR (Real.sqrt_pos.2 hR)
  rw [div_le_iff₀ hpos]
  constructor <;> intro h <;> linarith

theorem inverse_time_derivative_bound_iff {R T C : Real} (hR : 0 < R) :
    T / R ^ 2 ≤ C ↔ T ≤ C * R ^ 2 := by
  have hpos : (0 : Real) < R ^ 2 := by positivity
  exact div_le_iff₀ hpos

end CurvatureScaleDerivatives

section GoodPointDerivatives

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M]
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

def scalarDifferential (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M)
    (v : TangentSpace I x) : Real :=
  mfderiv I (modelWithCornersSelf Real Real) (fun y : M => S.scalar t y) x v

def GoodPointDerivativeBounds (I : ModelWithCorners Real E H) (kappa : Real) : Prop :=
  ∃ epsStar CStar : Real, 0 < epsStar ∧ 0 ≤ CStar ∧
    ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
      [IsManifold I 1 M] [T2Space M] [SigmaCompactSpace M]
      {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
      (S : SolutionOn (I := I) (M := M) D) (x : M) (t eps : Real),
      0 < eps → eps ≤ epsStar →
      IsGoodPoint.{u, uE, uH} (I := I) eps kappa S x t →
        (∀ v : TangentSpace I x,
            |scalarDifferential (I := I) S t x v| ≤
              2 * CStar * (S.scalar t x * Real.sqrt (S.scalar t x)) *
                Real.sqrt ((S.base.metric t).inner x v v)) ∧
          |deriv (fun tau : Real => S.scalar tau x) t| ≤ CStar * S.scalar t x ^ 2

omit [T2Space M] [SigmaCompactSpace M] in
theorem inverse_curvature_derivative_bounds
    {S : SolutionOn (I := I) (M := M) D} {x : M} {t CStar : Real}
    (hR : 0 < S.scalar t x)
    (hgrad : ∀ v : TangentSpace I x, |scalarDifferential (I := I) S t x v| ≤
      2 * CStar * (S.scalar t x * Real.sqrt (S.scalar t x)) *
        Real.sqrt ((S.base.metric t).inner x v v))
    (htime : |deriv (fun tau : Real => S.scalar tau x) t| ≤ CStar * S.scalar t x ^ 2) :
    (∀ v : TangentSpace I x,
        1 / 2 * |scalarDifferential (I := I) S t x v| /
            (S.scalar t x * Real.sqrt (S.scalar t x)) ≤
          CStar * Real.sqrt ((S.base.metric t).inner x v v)) ∧
      |deriv (fun tau : Real => S.scalar tau x) t| / S.scalar t x ^ 2 ≤ CStar := by
  refine ⟨fun v => ?_, (inverse_time_derivative_bound_iff hR).2 htime⟩
  rw [inverse_root_gradient_bound_iff hR]
  calc |scalarDifferential (I := I) S t x v|
      ≤ 2 * CStar * (S.scalar t x * Real.sqrt (S.scalar t x)) *
          Real.sqrt ((S.base.metric t).inner x v v) := hgrad v
    _ = 2 * (CStar * Real.sqrt ((S.base.metric t).inner x v v)) *
          (S.scalar t x * Real.sqrt (S.scalar t x)) := by ring

end GoodPointDerivatives

section Compactness

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

abbrev PointedFlowSqrtRmNormLeScalar
    (F : PointedFlowData.{u, uE, uH} (I := I) D) (Cn : Real) : Prop :=
  PointedFlowRmNormLeScalar (I := I) F Cn

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] in
theorem pointedFlow_rmNormSq_nonneg
    (F : PointedFlowData.{u, uE, uH} (I := I) D) (t : Real) (y : F.M) :
    0 ≤ F.rmNormSq (I := I) t y := by
  let : TopologicalSpace F.M := F.topology
  let : ChartedSpace H F.M := F.charted
  let : IsManifold I ∞ F.M := F.smooth
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) F.M := by
    change IsManifold I ∞ F.M
    infer_instance
  let : SigmaCompactSpace F.M := F.sigmaCompact
  let : T2Space F.M := F.t2
  exact Tensor0SBundle.normSq0S_nonneg (I := I) (F.S.family.metric t) y 4
    (F.S.base.rm04 t y)

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] in
theorem pointedFlowRmNormSqBounded_of_scalarBounded
    (F : PointedFlowData.{u, uE, uH} (I := I) D) {C Cn : Real}
    (hCn : 0 ≤ Cn)
    (hC : PointedFlowScalarBounded (I := I) F C)
    (hrm : PointedFlowRmNormLeScalar (I := I) F Cn) :
    PointedFlowRmNormSqBounded (I := I) F ((Cn * C) ^ 2) := by
  let : TopologicalSpace F.M := F.topology
  let : ChartedSpace H F.M := F.charted
  let : IsManifold I ∞ F.M := F.smooth
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) F.M := by
    change IsManifold I ∞ F.M
    infer_instance
  let : SigmaCompactSpace F.M := F.sigmaCompact
  let : T2Space F.M := F.t2
  intro t ht y
  have h1 : Real.sqrt (F.rmNormSq (I := I) t y) ≤ Cn * F.S.scalar t y := hrm t ht y
  have h2 : F.S.scalar t y ≤ C := (hC t ht y).2
  have h3 : Real.sqrt (F.rmNormSq (I := I) t y) ≤ Cn * C :=
    le_trans h1 (mul_le_mul_of_nonneg_left h2 hCn)
  have h4 : 0 ≤ F.rmNormSq (I := I) t y := pointedFlow_rmNormSq_nonneg (I := I) F t y
  have h5 : Real.sqrt (F.rmNormSq (I := I) t y) ^ 2 = F.rmNormSq (I := I) t y :=
    Real.sq_sqrt h4
  nlinarith [Real.sqrt_nonneg (F.rmNormSq (I := I) t y)]

theorem movingShi_of_ancient_kappa_solution
    (F : PointedFlowData.{u, uE, uH} (I := I) D) {kappa C Cn : Real}
    (hF : IsAncientKappaSolution (I := I) kappa F)
    (hC : PointedFlowScalarBounded (I := I) F C)
    (hCn : 0 ≤ Cn)
    (hrm : PointedFlowRmNormLeScalar (I := I) F Cn)
    {alpha beta psi : Real}
    (hab : alpha < beta) (hbp : beta ≤ psi) (hpsi : psi < 0) (N : Nat) :
    ∃ KShi : Real, 0 ≤ KShi ∧
      letI : TopologicalSpace F.M := F.topology
      letI : ChartedSpace H F.M := F.charted
      letI : IsManifold I ∞ F.M := F.smooth
      letI : IsManifold I 1 F.M :=
        IsManifold.of_le (I := I) (M := F.M) (n := (∞ : WithTop ℕ∞))
          (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
      letI : IsManifold I 2 F.M :=
        IsManifold.of_le (I := I) (M := F.M) (n := (∞ : WithTop ℕ∞))
          (by decide : (2 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) F.M := by
        change IsManifold I ∞ F.M
        infer_instance
      letI : SigmaCompactSpace F.M := F.sigmaCompact
      letI : T2Space F.M := F.t2
      MovingShiBoundOn (I := I) Set.univ beta psi
        (fun _ t => F.S.family.metric t) N KShi := by
  have hslab : Set.Icc alpha psi ⊆ D.carrier := by
    rw [hF.carrier_eq]
    intro s hs
    exact Set.mem_Iic.2 (le_trans hs.2 hpsi.le)
  have hreg : Set.Ioc alpha psi ⊆ D.regular := by
    rw [hF.regular_eq]
    intro s hs
    exact Set.mem_Iio.2 (lt_of_le_of_lt hs.2 hpsi)
  have halpha : alpha ∈ D.carrier := by
    rw [hF.carrier_eq]
    exact Set.mem_Iic.2 (by linarith)
  have hbound := pointedFlowRmNormSqBounded_of_scalarBounded (I := I) F hCn hC hrm
  have hcurv : ∀ t ∈ Set.Icc alpha psi, ∀ y : F.M,
      F.rmNormSq (I := I) t y ≤ (Cn * C) ^ 2 := fun t ht y => hbound t (hslab ht) y
  exact movingShi_complete (I := I) F hab hbp hslab hreg (hF.complete alpha halpha)
    (by positivity) hcurv N

theorem tendsto_neg_mul_atBot_of_theta
    {Q tSeq : Nat → Real} {theta : Real} (htheta : 0 < theta)
    (hQ : Filter.Tendsto Q Filter.atTop Filter.atTop)
    (ht : ∀ i : Nat, theta ≤ tSeq i) :
    Filter.Tendsto (fun i : Nat => -(Q i * tSeq i)) Filter.atTop Filter.atBot := by
  rw [Filter.tendsto_neg_atBot_iff]
  refine Filter.tendsto_atTop_mono' Filter.atTop ?_ (hQ.atTop_mul_const htheta)
  filter_upwards [hQ.eventually_ge_atTop 0] with i hi
  exact mul_le_mul_of_nonneg_left (ht i) hi

theorem exists_pointed_limit_of_scalar_normalized
    {alpha b : Real} (h0 : (0 : Real) ∈ Set.Ioo alpha b)
    (X : PointedFlowSeq.{u, uE, uH} (I := I))
    (hD : X.D =
      DifferentialGeometry.Geometry.Curvature.RealTimeInterval.openInterval alpha b 0 h0)
    (hcomplete : FlowMetricComplete (I := I) X)
    (hcurv : FlowCurvatureBoundedOnCompactWindows (I := I) X)
    (hinj : FlowScaleInjectivityBound (I := I) X)
    (hconn : ∀ k : Nat,
      letI : TopologicalSpace (X.term k).M := (X.term k).topology
      ConnectedSpace (X.term k).M)
    (hnorm : ∀ k : Nat, PointedFlowScalarAtBase (I := I) (X.term k) 1) :
    ∃ L : PointedFlowData.{u, uE, uH} (I := I) X.D, ∃ subseq : Nat → Nat,
      StrictMono subseq ∧ Nonempty (SmoothCGHConverges (I := I) X L subseq) ∧
        (∀ t ∈ X.D.carrier, MetricComplete (I := I) (L.atTime (I := I) t)) ∧
          PointedFlowScalarAtBase (I := I) L 1 := by
  obtain ⟨L, subseq, hmono, hconvNe, hcompleteL⟩ :=
    compactnessSolution (I := I) h0 X hD hcomplete hcurv hinj hconn
  obtain ⟨conv⟩ := hconvNe
  refine ⟨L, subseq, hmono, ⟨conv⟩, hcompleteL, ?_⟩
  have hzero : (0 : Real) ∈ X.D.carrier := by
    rw [hD]
    exact h0
  have hlim := conv.scalar_converges 0 hzero L.basepoint
  have hbase : ∀ k : Nat,
      conv.spatial.maps.map (I := I) k L.basepoint = (X.term (subseq k)).basepoint :=
    fun k => conv.spatial.maps.basepoint_map k
  have hconst : Filter.Tendsto (fun _ : Nat => (1 : Real)) Filter.atTop
      (nhds (letI : TopologicalSpace L.M := L.topology
             letI : ChartedSpace H L.M := L.charted
             letI : IsManifold I ∞ L.M := L.smooth
             letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.M := by
               change IsManifold I ∞ L.M
               infer_instance
             letI : SigmaCompactSpace L.M := L.sigmaCompact
             letI : T2Space L.M := L.t2
             L.S.scalar 0 L.basepoint)) := by
    refine hlim.congr ?_
    intro k
    rw [hbase k]
    exact hnorm (subseq k)
  exact tendsto_nhds_unique hconst tendsto_const_nhds

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] in
theorem isAncientKappaSolution_of_limit
    (L : PointedFlowData.{u, uE, uH} (I := I) D) {kappa C : Real}
    (hkappa : 0 < kappa)
    (hcarrier : D.carrier = Set.Iic 0) (hregular : D.regular = Set.Iio 0)
    (hconn :
      letI : TopologicalSpace L.M := L.topology
      ConnectedSpace L.M)
    (hcomplete : ∀ t ∈ D.carrier, MetricComplete (I := I) (L.atTime (I := I) t))
    (hnonneg : ∀ t ∈ D.carrier, PointedFlowNonnegativeCurvatureOperator (I := I) L t)
    (hscalar : PointedFlowScalarBounded (I := I) L C)
    (hnc : PointedFlowNoncollapsedAllScales (I := I) L kappa)
    (hbase : PointedFlowScalarAtBase (I := I) L 1) :
    IsAncientKappaSolution (I := I) kappa L := by
  have hzero : (0 : Real) ∈ D.carrier := by
    rw [hcarrier]
    exact Set.mem_Iic.2 le_rfl
  refine
    { kappa_pos := hkappa
      carrier_eq := hcarrier
      regular_eq := hregular
      connected := hconn
      complete := hcomplete
      nonnegativeCurvatureOperator := hnonneg
      globalScalarBound := ⟨C, hscalar⟩
      noncollapsed := hnc
      notFlat := ?_ }
  refine pointedFlowNotFlat_of_scalar_ne_zero (I := I) L hzero L.basepoint ?_
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : IsManifold I ∞ L.M := L.smooth
  let : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.M := by
    change IsManifold I ∞ L.M
    infer_instance
  let : SigmaCompactSpace L.M := L.sigmaCompact
  let : T2Space L.M := L.t2
  have hb : L.S.scalar 0 L.basepoint = 1 := hbase
  rw [hb]
  exact one_ne_zero

end Compactness

end

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
