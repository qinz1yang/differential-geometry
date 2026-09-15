import DifferentialGeometry.Geometry.Exponential.Intrinsic.Framed.Coordinates
import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic

section

set_option autoImplicit false
noncomputable section
open Bundle Set Manifold
open DifferentialGeometry.Geometry.Riemannian.Exponential
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [CompleteSpace E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M]
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup Tensor0SBundle.tangentSpaceNormedSpace
variable [PseudoEMetricSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M] [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
variable (g : SmoothRiemannianMetric I M)
variable (hEnorm : forall x : M, forall v : TangentSpace I x, ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))

omit [CompleteSpace E] [ConnectedSpace M] in
theorem intrinsicFramedExp_image_closedBall (p : M) {R : Real} (hR : 0 ≤ R) :
    intrinsicFramedExp (I := I) g hEnorm p '' Metric.closedBall (0 : E) R =
      {q : M | riemannianEDist I p q ≤ ENNReal.ofReal R} := by
  ext q
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hdist := intrinsicGeodesic_riemannianEDist_le (I := I) g hEnorm p
      (normalFrame (I := I) g p z) (s := (0 : Real)) (t := (1 : Real)) zero_le_one
    have hzR : ‖z‖ ≤ R := by simpa only [Metric.mem_closedBall, dist_zero_right] using hz
    rw [intrinsicGeodesic_zero (I := I) g hEnorm p (normalFrame (I := I) g p z),
      ← expMapIntrinsic_def (I := I) g hEnorm p (normalFrame (I := I) g p z)] at hdist
    have hrad : riemannianEDist I p (intrinsicFramedExp (I := I) g hEnorm p z) ≤
        ENNReal.ofReal ‖z‖ := by
      simpa only [intrinsicGeodesic_zero, ← expMapIntrinsic_def,
        intrinsicFrame_apply, normalFrame_sqrt, sub_zero, mul_one] using hdist
    exact hrad.trans (ENNReal.ofReal_le_ofReal hzR)
  · intro hq
    have hfin : riemannianEDist I p q ≠ ⊤ :=
      ne_of_lt (lt_of_le_of_lt hq ENNReal.ofReal_lt_top)
    obtain ⟨v, hvexp, hvnorm⟩ :=
      hopf_rinow_expMapIntrinsic_surjective_minimizing_of_ne_top (I := I) g hEnorm p q hfin
    refine ⟨(normalFrame (I := I) g p).symm v, ?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_zero_right,
        ← normalFrame_sqrt (I := I) g p ((normalFrame (I := I) g p).symm v),
        ContinuousLinearEquiv.apply_symm_apply, hvnorm]
      exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hq).trans_eq (ENNReal.toReal_ofReal hR)
    · rw [intrinsicFrame_apply, ContinuousLinearEquiv.apply_symm_apply]
      exact hvexp
end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

end

end
