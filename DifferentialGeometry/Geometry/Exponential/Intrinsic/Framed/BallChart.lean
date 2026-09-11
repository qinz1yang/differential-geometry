import DifferentialGeometry.Geometry.Comparison.NormalCoordinates.ExponentialBallPartialDiffeomorph
import DifferentialGeometry.Geometry.Exponential.Intrinsic.Framed.Jacobi
import DifferentialGeometry.Geometry.Exponential.NormalBall.Chart

set_option autoImplicit false

noncomputable section

open Bundle Set
open scoped Bundle Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open NormalCoordinates

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [CompleteSpace E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [PseudoEMetricSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

namespace Exponential
namespace ExponentialInverseBranch

noncomputable def framed
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : ExponentialInverseBranch (I := I) g hEnorm p) :
    PartialDiffeomorph (modelWithCornersSelf Real E) I E M ∞ := by
  let L := intrinsicFrameCLE (I := I) g p
  exact
    { toPartialEquiv :=
        { toFun := fun z => B.hom (L z)
          invFun := fun q => L.symm (B.hom.symm q)
          source := L ⁻¹' B.hom.source
          target := B.hom.target
          map_source' := fun _ hz => B.hom.map_source hz
          map_target' := by
            intro q hq
            change L (L.symm (B.hom.symm q)) ∈ B.hom.source
            rw [L.apply_symm_apply]
            exact B.hom.map_target hq
          left_inv' := by
            intro z hz
            calc
              L.symm (B.hom.symm (B.hom (L z))) =
                  L.symm (L z) := congrArg L.symm (B.hom.left_inv hz)
              _ = z := L.symm_apply_apply z
          right_inv' := by
            intro q hq
            rw [L.apply_symm_apply]
            exact B.hom.right_inv hq }
      open_source := B.hom.open_source.preimage L.continuous
      open_target := B.hom.open_target
      contMDiffOn_toFun :=
        B.hom.contMDiffOn_toFun.comp
          L.toContinuousLinearMap.contMDiff.contMDiffOn (fun _ hz => hz)
      contMDiffOn_invFun :=
        L.symm.toContinuousLinearMap.contMDiff.comp_contMDiffOn
          B.hom.contMDiffOn_invFun }

omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
@[simp] theorem framed_source
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : ExponentialInverseBranch (I := I) g hEnorm p) :
    B.framed.source =
      intrinsicFrameCLE (I := I) g p ⁻¹' B.hom.source :=
  rfl

omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
@[simp] theorem framed_apply
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : ExponentialInverseBranch (I := I) g hEnorm p) (z : E) :
    B.framed z = B.hom (intrinsicFrameCLE (I := I) g p z) :=
  rfl

omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
theorem framed_eq_intr
    {g : SmoothRiemannianMetric I M}
    {hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w))}
    {p : M} (B : ExponentialInverseBranch (I := I) g hEnorm p) :
    EqOn (intrinsicFramedExp (I := I) g hEnorm p) B.framed
      B.framed.source := by
  intro z hz
  change intrinsicFrameCLE (I := I) g p z ∈ B.hom.source at hz
  have hframe :
      (tangentSpaceModelContinuousLinearEquiv (I := I) p).symm
          (intrinsicFrameCLE (I := I) g p z) =
        normalFrame (I := I) g p z := by
    exact (tangentSpaceModelContinuousLinearEquiv_symm_apply
      (I := I) p (intrinsicFrameCLE (I := I) g p z)).trans rfl
  rw [intrinsicFrame_apply, framed_apply]
  exact (congrArg (expMapIntrinsic (I := I) g hEnorm p) hframe.symm).trans
    (B.hom_eq hz)

end ExponentialInverseBranch
end Exponential

namespace NormalCoordinates

open Exponential

omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
theorem intrinsicFrame_localAt
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (B : ExponentialInverseBranch (I := I) g hEnorm p) {z : E}
    (hz : (normalFrame (I := I) g p z : E) ∈ B.hom.source) :
    IsLocalDiffeomorphAt (modelWithCornersSelf Real E) I ∞
      (intrinsicFramedExp (I := I) g hEnorm p) z := by
  refine ⟨B.framed, ?_, B.framed_eq_intr⟩
  change intrinsicFrameCLE (I := I) g p z ∈ B.hom.source
  convert hz using 1
  rfl

omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
theorem intrinsicFrame_localOn
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (U : Set E)
    (hbranch : ∀ z ∈ U, ∃ B : ExponentialInverseBranch (I := I) g hEnorm p,
      (normalFrame (I := I) g p z : E) ∈ B.hom.source) :
    IsLocalDiffeomorphOn (modelWithCornersSelf Real E) I ∞
      (intrinsicFramedExp (I := I) g hEnorm p) U := by
  intro z
  obtain ⟨B, hz⟩ := hbranch z z.2
  exact intrinsicFrame_localAt (I := I) g hEnorm p B hz

structure IntrinsicBallChart
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) (r : Real) where
  hom : PartialDiffeomorph (modelWithCornersSelf Real E) I E M ∞
  source_eq : hom.source = Metric.ball (0 : E) r
  target_eq :
    hom.target =
      intrinsicFramedExp (I := I) g hEnorm p '' Metric.ball (0 : E) r
  hom_eq :
    EqOn hom (intrinsicFramedExp (I := I) g hEnorm p)
      (Metric.ball (0 : E) r)

def IntrinsicBallChart.toNormalBallChart
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {r : Real} (c : IntrinsicBallChart (I := I) g hEnorm p r)
    (hr : 0 < r) :
    NormalBallChart (I := I) p := by
  have hsub : Metric.ball (0 : E) r ⊆ c.hom.source := by
    rw [c.source_eq]
  have hzero : c.hom 0 = p := by
    rw [c.hom_eq (Metric.mem_ball.mpr (by simpa using hr))]
    exact intrinsicFrame_zero (I := I) g hEnorm p
  exact NormalBallChart.ofHigher (I := I) hr c.hom hsub hzero

omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
theorem exists_intrinsic_ball_chart
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (x : M) (w : TangentSpace I x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    (p : M) {r : Real}
    (hloc : IsLocalDiffeomorphOn (modelWithCornersSelf Real E) I ∞
      (intrinsicFramedExp (I := I) g hEnorm p) (Metric.ball (0 : E) r))
    (hinj : InjOn (intrinsicFramedExp (I := I) g hEnorm p)
      (Metric.ball (0 : E) r)) :
    Nonempty (IntrinsicBallChart (I := I) g hEnorm p r) := by
  obtain ⟨Φ, hsource, htarget, hEq⟩ :=
    Geometry.Riemannian.exists_partial_diffeomorph_of_is_local_diffeomorph_on_inj_on
      hloc Metric.isOpen_ball hinj
  exact ⟨⟨Φ, hsource, htarget, hEq⟩⟩

end NormalCoordinates
end Riemannian
end Geometry
end DifferentialGeometry

end
