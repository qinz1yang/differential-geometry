import DifferentialGeometry.Geometry.Metric.TensorInner.TangentNormDiamond
import DifferentialGeometry.Geometry.Exponential.DiagInvBranch
import DifferentialGeometry.Geometry.Exponential.NormalBallHome

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
open NormalCoordinates
namespace Exponential
namespace DiagInvBranch

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
variable [PseudoEMetricSpace M] [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

noncomputable def diagReadout
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p)
    (y : M × M) : E :=
  (trivializationAt E (TangentSpace I) p (B.inv y)).2

def readDom
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p) : Set (M × M) :=
  B.dom ∩ Prod.fst ⁻¹' (trivializationAt E (TangentSpace I) p).baseSet

omit [ConnectedSpace M] in
theorem readoutDomInf
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : DiagInvBranch (I := I) g hEnorm p) :
    IsOpen B.readDom ∧
      (p, p) ∈ B.readDom ∧
      ContMDiffOn (I.prod I) 𝓘(ℝ, E) ∞ (diagReadout B) B.readDom ∧
      ∀ y ∈ B.readDom,
        diagExp (I := I) g hEnorm (B.inv y) = y ∧
        (B.inv y).proj = y.1 ∧
        expMapIntrinsic (I := I) g hEnorm y.1 (B.inv y).snd = y.2 := by
  let e := trivializationAt E (TangentSpace I) p
  have hopen : IsOpen B.readDom :=
    B.hom.open_target.inter (e.open_baseSet.preimage continuous_fst)
  have hp : (p, p) ∈ B.readDom :=
    ⟨B.center_mem, mem_baseSet_trivializationAt E (TangentSpace I) p⟩
  have hsmooth : ContMDiffOn (I.prod I) 𝓘(ℝ, E) ∞
      (diagReadout B) B.readDom := by
    intro y hy
    have hbranchAt : ContMDiffAt (I.prod I) I.tangent ∞ B.inv y :=
      (B.inv_inf y hy.1).contMDiffAt (B.hom.open_target.mem_nhds hy.1)
    have hbase : (B.inv y).proj ∈ e.baseSet := by
      rw [B.proj_eq hy.1]
      exact hy.2
    have hreadAt : ContMDiffAt (I.prod I) 𝓘(ℝ, E) ∞
        (diagReadout B) y := by
      have hreadAt' := ((e.contMDiffAt_iff (e.mem_source.2 hbase)).mp hbranchAt).2
      refine hreadAt'.congr_of_eventuallyEq ?_
      exact Filter.Eventually.of_forall fun _ => rfl
    exact hreadAt.contMDiffWithinAt
  refine ⟨hopen, hp, hsmooth, ?_⟩
  intro y hy
  exact ⟨B.right_inv hy.1, B.proj_eq hy.1, B.exp_eq hy.1⟩

section ChartReadout

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] [NeZero (Module.finrank ℝ E')]
variable {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  [IsManifold I' ∞ M'] [T2Space M'] [SigmaCompactSpace M'] [ConnectedSpace M']
variable [RiemannianBundle (fun x : M' ↦ TangentSpace I' x)]
variable [PseudoEMetricSpace M'] [IsRiemannianManifold I' M'] [CompleteSpace M']
  [IsContinuousRiemannianBundle E' (fun x : M' ↦ TangentSpace I' x)]

noncomputable def chartReadout
    {g : SmoothRiemannianMetric I' M'}
    {hEnorm : ∀ (x : M') (w : TangentSpace I' x),
      ‖w‖₊ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M'} (B : DiagInvBranch (I := I') g hEnorm p)
    (c : NormalBallChart (I := I') p) (y : M' × M') : E' :=
  (c.tangentHome.symm (B.inv y)).2

def chartReadDom
    {g : SmoothRiemannianMetric I' M'}
    {hEnorm : ∀ (x : M') (w : TangentSpace I' x),
      ‖w‖₊ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M'} (B : DiagInvBranch (I := I') g hEnorm p)
    (c : NormalBallChart (I := I') p) : Set (M' × M') :=
  B.dom ∩ Prod.fst ⁻¹' c.restrictBall.target

omit [ConnectedSpace M'] in
theorem chartReadoutInf
    {g : SmoothRiemannianMetric I' M'}
    {hEnorm : ∀ (x : M') (w : TangentSpace I' x),
      ‖w‖₊ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M'} (B : DiagInvBranch (I := I') g hEnorm p)
    (c : NormalBallChart (I := I') p) :
    IsOpen (B.chartReadDom c) ∧
      (p, p) ∈ B.chartReadDom c ∧
      ContMDiffOn (I'.prod I') 𝓘(ℝ, E') ∞
        (B.chartReadout c) (B.chartReadDom c) ∧
      ∀ y ∈ B.chartReadDom c,
        diagExp (I := I') g hEnorm (B.inv y) = y ∧
        (B.inv y).proj = y.1 ∧
        expMapIntrinsic (I := I') g hEnorm y.1 (B.inv y).snd = y.2 := by
  have hopen : IsOpen (B.chartReadDom c) :=
    B.hom.open_target.inter (c.restrictBall.open_target.preimage continuous_fst)
  have hpTarget : p ∈ c.restrictBall.target := by
    refine ⟨0, ?_, ?_⟩
    · change (0 : E') ∈ Metric.ball 0 c.radius
      simpa only [Metric.mem_ball, dist_self] using c.radius_pos
    · simpa only [NormalBallChart.restrictBall_apply] using c.map_zero
  have hp : (p, p) ∈ B.chartReadDom c :=
    ⟨B.center_mem, hpTarget⟩
  have hsmooth : ContMDiffOn (I'.prod I') 𝓘(ℝ, E') ∞
      (B.chartReadout c) (B.chartReadDom c) := by
    intro y hy
    have hbranchAt : ContMDiffAt (I'.prod I') I'.tangent ∞ B.inv y :=
      (B.inv_inf y hy.1).contMDiffAt (B.hom.open_target.mem_nhds hy.1)
    have hinTarget : B.inv y ∈ c.tangentHome.target := by
      rw [c.tangentHome_target]
      change (B.inv y).proj ∈ c.restrictBall.target
      rw [B.proj_eq hy.1]
      exact hy.2
    have hcoordsAt : ContMDiffAt (I'.prod I') 𝓘(ℝ, E' × E') ∞
        (fun z => c.tangentHome.symm (B.inv z)) y :=
      (c.tangentHome_inv_inf (B.inv y) hinTarget).contMDiffAt
        (c.tangentHome.open_target.mem_nhds hinTarget) |>.comp y hbranchAt
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at hcoordsAt
    have hreadAt : ContMDiffAt (I'.prod I') 𝓘(ℝ, E') ∞
        (B.chartReadout c) y := by
      have hreadAt' := contMDiffAt_snd.comp y hcoordsAt
      refine hreadAt'.congr_of_eventuallyEq ?_
      exact Filter.Eventually.of_forall fun _ => rfl
    exact hreadAt.contMDiffWithinAt
  refine ⟨hopen, hp, hsmooth, ?_⟩
  intro y hy
  exact ⟨B.right_inv hy.1, B.proj_eq hy.1, B.exp_eq hy.1⟩

end ChartReadout

end DiagInvBranch
end Exponential
end Riemannian
end Geometry
end DifferentialGeometry
