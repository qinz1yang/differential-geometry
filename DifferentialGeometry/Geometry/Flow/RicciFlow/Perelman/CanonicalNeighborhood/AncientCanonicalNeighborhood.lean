import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.HighCurvatureModelBounds

set_option autoImplicit false
noncomputable section
open scoped _root_.Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
theorem tensor02CovDerivNormWith_zero_le {eps : ℝ} (heps : 0 ≤ eps)
    (g : SmoothRiemannianMetric I3 M) (a : ℕ) (x : M) :
    tensor02CovDerivNormWith (I := I3) a
      (0 : Tensor0SField (I := I3) (M := M) (n := ∞) 2) g g x ≤ eps := by
  have hnz : ∀ (s : ℕ) (y : M),
      Real.sqrt (Tensor0SBundle.normSq0S (I := I3) g y s
        (0 : Tensor0SSpace (𝕜 := ℝ) (E := ThreeSpace) (H := ThreeSpace)
          (I := I3) (M := M) s y)) = 0 := by
    intro s y
    have hz : Tensor0SBundle.inner0S (I := I3) g y s
        (0 : Tensor0SSpace (𝕜 := ℝ) (E := ThreeSpace) (H := ThreeSpace)
          (I := I3) (M := M) s y) 0 = 0 := by
      change (Tensor0SBundle.tensor0SMetricData (I := I3) g y s).flat 0 0 = 0
      rw [(Tensor0SBundle.tensor0SMetricData (I := I3) g y s).flat.map_zero]
      exact LinearMap.zero_apply _
    rw [Tensor0SBundle.normSq0S_eq_inner, hz, Real.sqrt_zero]
  have hfield : tensor02CovDeriv (I := I3)
      (0 : Tensor0SField (I := I3) (M := M) (n := ∞) 2) g a = 0 := by
    rw [tensor02_cov_deriv_eq_cov_deriv_of_field, covDerivOfField_zero_tensor]
  have hzd : tensor02CovDeriv (I := I3)
      (0 : Tensor0SField (I := I3) (M := M) (n := ∞) 2) g a x = 0 := by
    rw [hfield]
    simp
  change Real.sqrt (Tensor0SBundle.normSq0S (I := I3) g x (a + 2)
    (tensor02CovDeriv (I := I3)
      (0 : Tensor0SField (I := I3) (M := M) (n := ∞) 2) g a x)) ≤ eps
  rw [hzd, hnz]
  exact heps

def metricComparisonOnSelf (g : ℝ → SmoothRiemannianMetric I3 M)
    (U : Set M) (times : Set ℝ) (order : ℕ) {eps : ℝ} (heps : 0 < eps) :
    MetricComparisonOn g g (id : M → M) U times order eps where
  pullback s := metricTensorField (I := I3) (g s)
  pullback_eq := by
    intro s y hy v
    rw [metricTensorField_apply, mfderiv_id]
    rfl
  jet _ _ := 0
  jet_zero := by
    intro s y v
    simp [metricTensorField_apply, sub_self]
  jet_succ := by
    intro b s hs y hy v
    simp
  equivalence := by
    intro s hs y hy v
    have hnn := inner_self_nonneg (g s) y v
    simp only [metricTensorField_apply]
    constructor <;> nlinarith
  close := by
    intro a b hab s hs y hy
    exact tensor02CovDerivNormWith_zero_le heps.le (g s) a y

def metricComparisonOnRefl (g : ℝ → SmoothRiemannianMetric I3 M)
    (U : Set M) (times : Set ℝ) (order : ℕ) {eps : ℝ} (heps : 0 < eps) :
    MetricComparisonOn g g (PartialDiffeomorph.refl (I := I3) M : M → M) U times order eps := by
  have hid : (↑(PartialDiffeomorph.refl (I := I3) M) : M → M) = id := by
    funext x
    rfl
  rw [hid]
  exact metricComparisonOnSelf g U times order heps

omit [T2Space M] [SigmaCompactSpace M] in
theorem preservesTangentOrientationAt_refl (o : TangentOrientationSection M) (y : M)
    (hf : Function.Bijective (mfderiv I3 I3
      (PartialDiffeomorph.refl (I := I3) M : M → M) y)) :
    PreservesTangentOrientationAt o o (PartialDiffeomorph.refl (I := I3) M : M → M) y hf := by
  unfold PreservesTangentOrientationAt
  have hd : mfderiv I3 I3 (PartialDiffeomorph.refl (I := I3) M : M → M) y =
      ContinuousLinearMap.id ℝ (TangentSpace I3 y) := mfderiv_id
  have he : LinearEquiv.ofBijective
      (mfderiv I3 I3 (PartialDiffeomorph.refl (I := I3) M : M → M) y).toLinearMap hf =
      LinearEquiv.refl ℝ (TangentSpace I3 y) := by
    ext v
    change mfderiv I3 I3 (PartialDiffeomorph.refl (I := I3) M : M → M) y v = v
    rw [hd]
    rfl
  have hm := congrArg (fun e : TangentSpace I3 y ≃ₗ[ℝ] TangentSpace I3 y =>
    Orientation.map (Fin 3) e (o.orientation y)) he
  have hr := congrArg (fun e : Orientation ℝ (TangentSpace I3 y) (Fin 3) ≃
    Orientation ℝ (TangentSpace I3 y) (Fin 3) => e (o.orientation y))
    (Orientation.map_refl (R := ℝ) (M := TangentSpace I3 y) (Fin 3))
  exact hm.trans hr

theorem scalar_zero_base_eq_one (P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    (hbase : PointedFlowScalarAtBase P 1) :
    P.S.scalar 0 P.basepoint = 1 := by
  simpa only [PointedFlowScalarAtBase, SolutionOn.scalar, SolutionFamily.scalar] using hbase

theorem rescaledMetric_zero_of_scalar_one (P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    (hbase : P.S.scalar 0 P.basepoint = 1) {hQ : 0 < P.S.scalar 0 P.basepoint} :
    rescaledMetric (I := I3) (M := P.M) P.S 0 (P.S.scalar 0 P.basepoint) hQ =
      P.S.base.metric := by
  funext s
  apply SmoothRiemannianMetric.ext_inner
  intro y v w
  rw [rescaledMetric, scaleMetric_inner, parabolicTime, hbase, div_one, zero_add, one_mul]

theorem orientedWitness_self (P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval)
    {kappa delta : ℝ} (hanc : IsAncientKappaSolution kappa P)
    (hbase : PointedFlowScalarAtBase P 1) (o : TangentOrientationSection P.M)
    (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    OrientedWitness P.S o delta kappa P.basepoint 0 := by
  have hbase' : P.S.scalar 0 P.basepoint = 1 := scalar_zero_base_eq_one P hbase
  have hQpos : 0 < P.S.scalar 0 P.basepoint := by rw [hbase']; norm_num
  let K : Set P.M :=
    riemannianClosedBallOf (I := I3) (P.S.base.metric 0) P.basepoint (modelRadius delta)
  refine ⟨{ eps_pos := hdelta
            eps_lt_one := hdelta1
            time_mem := by simp only [ancientTimeInterval_carrier, Set.mem_Iic]; exact le_rfl
            scalar_pos := hQpos
            window_mem := by
              intro s hs
              simpa only [ancientTimeInterval_carrier, Set.mem_Iic] using hs.2
            model := P
            model_ancient := hanc
            model_scalar_base := hbase
            embedding := PartialDiffeomorph.refl (I := I3) P.M
            buffered_ball := fun y _ => Set.mem_univ y
            base_map := rfl
            comparison := by
              rw [rescaledMetric_zero_of_scalar_one P hbase' (hQ := hQpos)]
              exact metricComparisonOnRefl P.S.base.metric K
                (Set.Icc (-(modelDepth delta)) 0) (modelOrder delta) hdelta
            source_capture := fun y _ => ⟨y, Set.mem_univ y, rfl⟩ }, ?_⟩
  refine ⟨o, fun y _ => ?_⟩
  have hd : mfderiv I3 I3 (PartialDiffeomorph.refl (I := I3) P.M : P.M → P.M) y =
      ContinuousLinearMap.id ℝ (TangentSpace I3 y) := mfderiv_id
  have hbij : Function.Bijective
      (mfderiv I3 I3 (PartialDiffeomorph.refl (I := I3) P.M : P.M → P.M) y) := by
    rw [hd]
    exact Function.bijective_id
  exact ⟨hbij, preservesTangentOrientationAt_refl o y hbij⟩

theorem kappa_canonical_neighborhood_of_buffered_canonical_pullback :
    ∃ epsCan : ℝ, 0 < epsCan ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsCan →
      ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧ ∀ kappa : ℝ, 0 < kappa →
        ∀ P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval,
          IsAncientKappaSolution kappa P → PointedFlowScalarAtBase P 1 →
          TangentOrientationSection P.M →
            Nonempty (CanonicalWitness P.S eps C1 C2 P.basepoint 0) := by
  obtain ⟨epsCan, hepsCan, hpb⟩ := buffered_canonical_pullback.{u}
  refine ⟨epsCan, hepsCan, fun eps heps hle => ?_⟩
  obtain ⟨C1, C2, hC1, hC2, htransfer⟩ := hpb eps heps hle
  refine ⟨C1, C2, hC1, hC2, fun kappa hkappa P hanc hbase o => ?_⟩
  obtain ⟨delta, hd, hd1, hdelta⟩ := htransfer kappa hkappa
  exact hdelta (M := P.M) (D := ancientTimeInterval) (S := P.S) (o := o) (x := P.basepoint)
    (t := 0) (orientedWitness_self P hanc hbase o hd hd1)

theorem kappa_canonical_neighborhood :
    ∃ epsCan : ℝ, 0 < epsCan ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsCan →
      ∃ C1 C2 : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧ ∀ kappa : ℝ, 0 < kappa →
        ∀ P : PointedFlowData.{u, 0, 0} I3 ancientTimeInterval,
          IsAncientKappaSolution kappa P → PointedFlowScalarAtBase P 1 →
          TangentOrientationSection P.M →
            Nonempty (CanonicalWitness P.S eps C1 C2 P.basepoint 0) :=
  kappa_canonical_neighborhood_of_buffered_canonical_pullback

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
