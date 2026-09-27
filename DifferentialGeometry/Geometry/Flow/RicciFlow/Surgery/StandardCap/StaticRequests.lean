import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Distance
import DifferentialGeometry.Geometry.Metric.OpenEmbeddingPullback
import DifferentialGeometry.Geometry.Metric.DerivativeENorm

set_option autoImplicit false
noncomputable section
open Set Function TopologicalSpace Manifold DifferentialGeometry
open DifferentialGeometry.Geometry.Metric
open scoped Manifold ContDiff Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
private abbrev RequestE3 := EuclideanSpace ℝ (Fin 3)

def closedModelBall (D : ℝ) : Set RequestE3 :=
  {x | (riemannianEDistOf metric 0 x).toReal ≤ D}

theorem closedModelBall_eq (D : ℝ) :
    closedModelBall D = Metric.closedBall (0 : RequestE3) D := by
  ext x
  simp only [closedModelBall, mem_ofPred_eq, distance_zero, Metric.mem_closedBall, dist_zero_right]

theorem isCompact_closedModelBall (D : ℝ) : IsCompact (closedModelBall D) := by
  rw [closedModelBall_eq]
  exact isCompact_closedBall _ _

structure StaticRequest where
  radius : ℝ
  order : ℕ
  error : ℝ
  radius_pos : 0 < radius
  error_pos : 0 < error

namespace StaticRequest

def DominatedBy (P P' : StaticRequest) : Prop :=
  P.radius ≤ P'.radius ∧ P.order ≤ P'.order ∧ P'.error ≤ P.error

theorem dominatedBy_refl (P : StaticRequest) : P.DominatedBy P := ⟨le_rfl, le_rfl, le_rfl⟩

theorem DominatedBy.trans {P P' P'' : StaticRequest}
    (h : P.DominatedBy P') (h' : P'.DominatedBy P'') : P.DominatedBy P'' :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h'.2.2.trans h.2.2⟩

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  (g : SmoothRiemannianMetric I M) (Q : ℝ) (hQ : 0 < Q)
  (U : Opens RequestE3) (J : U → M) (hJ : IsLocalDiffeomorph (𝓡 3) I ∞ J)
  (hinj : Injective J) (p : M)

def IsSatisfied (P : StaticRequest) : Prop :=
  closedModelBall P.radius ⊆ U ∧
  (∀ h0 : (0 : RequestE3) ∈ U, J ⟨0, h0⟩ = p) ∧
  metricDerivENormSupOn {x : U | x.val ∈ closedModelBall P.radius} P.order
    (pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric Q hQ g) J hJ hinj)
    (metric.restrictOpen U) (metric.restrictOpen U) < ENNReal.ofReal P.error

theorem IsSatisfied.contains_tip {P : StaticRequest}
    (h : P.IsSatisfied g Q hQ U J hJ hinj p) : (0 : RequestE3) ∈ U := by
  apply h.1
  change (riemannianEDistOf metric 0 0).toReal ≤ P.radius
  rw [distance_zero, norm_zero]
  exact P.radius_pos.le

theorem IsSatisfied.mono {P P' : StaticRequest} (hPP' : P.DominatedBy P')
    (h : P'.IsSatisfied g Q hQ U J hJ hinj p) :
    P.IsSatisfied g Q hQ U J hJ hinj p := by
  have hball : closedModelBall P.radius ⊆ closedModelBall P'.radius :=
    fun _ hx => hx.trans hPP'.1
  refine ⟨hball.trans h.1, h.2.1, ?_⟩
  have hm := metricDerivENormSupOn_mono
    (K := {x : U | x.val ∈ closedModelBall P.radius})
    (L := {x : U | x.val ∈ closedModelBall P'.radius})
    (fun _ hx => hball hx) hPP'.2.1
    (pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric Q hQ g) J hJ hinj)
    (metric.restrictOpen U) (metric.restrictOpen U)
  exact (hm.trans_lt h.2.2).trans_le (ENNReal.ofReal_le_ofReal hPP'.2.2)
end StaticRequest
end DifferentialGeometry.PDE.RicciFlow.StandardCap
