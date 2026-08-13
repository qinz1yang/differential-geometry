import DifferentialGeometry.Geometry.Exponential.FramedNormalCoordinates
import DifferentialGeometry.Geometry.Exponential.IntrinsicVelocity
import DifferentialGeometry.Geometry.Exponential.Smoothness.IntrinsicMfderivZero
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection

noncomputable section

open Bundle Set
open scoped Bundle Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace NormalCoordinates

open DifferentialGeometry.Geometry.Riemannian.Exponential

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [CompleteSpace E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] [ConnectedSpace M]

noncomputable def intrFrameCLM
    (g : SmoothRiemannianMetric I M) (p : M) : E →L[Real] E :=
  LinearMap.toContinuousLinearMap
    (normalFrame (I := I) g p).toLinearEquiv.toLinearMap

omit [CompleteSpace E] [NeZero (Module.finrank Real E)] [I.Boundaryless]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
  [ConnectedSpace M] in
@[simp] theorem intrFrameCLM_apply
    (g : SmoothRiemannianMetric I M) (p : M) (z : E) :
    intrFrameCLM (I := I) g p z = normalFrame (I := I) g p z := by
  rfl

section

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace

noncomputable def intrinsicFramedExp
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) : E → M :=
  fun z => expMapIntrinsic (I := I) g hEnorm p
    (show TangentSpace I p from intrFrameCLM (I := I) g p z)

omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
omit [ConnectedSpace M] in
@[simp] theorem intrFrame_apply
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (z : E) :
    intrinsicFramedExp (I := I) g hEnorm p z =
      expMapIntrinsic (I := I) g hEnorm p
        (normalFrame (I := I) g p z) := by
  rw [intrinsicFramedExp, intrFrameCLM_apply]

omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
omit [ConnectedSpace M] in
theorem intrFrame_smooth
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) :
    ContMDiff (modelWithCornersSelf Real E) I ∞
      (intrinsicFramedExp (I := I) g hEnorm p) := by
  exact (intrinsicFiber_smooth (I := I) g hEnorm p).comp
    (intrFrameCLM (I := I) g p).contMDiff

omit [CompleteSpace E]
  [ConnectedSpace M] in
@[simp] theorem intrFrame_zero
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) :
    intrinsicFramedExp (I := I) g hEnorm p 0 = p := by
  obtain ⟨r, hr, hagree⟩ :=
    exists_expMapIntrinsic_eq_expMap_radius (I := I) g hEnorm p
  have hzero : Real.sqrt
      (g.inner p (0 : TangentSpace I p) (0 : TangentSpace I p)) < r := by
    simpa using hr
  rw [intrFrame_apply, map_zero, hagree hzero]
  exact expMap_zero (I := I) g p

omit [ConnectedSpace M] in
theorem intrFrame_deriv_zero
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) :
    mfderiv (modelWithCornersSelf Real E) I
        (intrinsicFramedExp (I := I) g hEnorm p) 0 =
      intrFrameCLM (I := I) g p := by
  let F : E → M := fun v =>
    expMapIntrinsic (I := I) g hEnorm p (show TangentSpace I p from v)
  let L : E →L[Real] E :=
    intrFrameCLM (I := I) g p
  have hF : MDifferentiableAt (modelWithCornersSelf Real E) I F (L 0) := by
    rw [map_zero]
    exact (intrinsicFiber_smooth (I := I) g hEnorm p).contMDiffAt.mdifferentiableAt
      (by decide)
  have hL : MDifferentiableAt (modelWithCornersSelf Real E)
      (modelWithCornersSelf Real E) (fun z : E => L z) 0 := by
    have hL_smooth : ContMDiff (modelWithCornersSelf Real E)
        (modelWithCornersSelf Real E) ∞ (fun z : E => L z) := L.contMDiff
    exact hL_smooth.contMDiffAt.mdifferentiableAt (by simp)
  have hchain := mfderiv_comp
    (I := modelWithCornersSelf Real E)
    (I' := modelWithCornersSelf Real E) (I'' := I) 0 hF hL
  have hLderiv : mfderiv (modelWithCornersSelf Real E)
      (modelWithCornersSelf Real E) (fun z : E => L z) 0 = L := by
    rw [mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
  rw [hLderiv] at hchain
  have hFderiv : mfderiv (modelWithCornersSelf Real E) I F (L 0) =
      ContinuousLinearMap.id Real E := by
    rw [map_zero]
    exact mfderiv_expMapIntrinsic_at_zero (I := I) g hEnorm p
  rw [hFderiv] at hchain
  have hchain' : mfderiv (modelWithCornersSelf Real E) I
      (F ∘ fun z : E => L z) 0 = L :=
    hchain.trans (ContinuousLinearMap.id_comp L)
  simpa only [intrinsicFramedExp, F, L, Function.comp_apply] using hchain'

omit [CompleteSpace E]
  [ConnectedSpace M] in
theorem exists_intrFrame_eq
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) :
    ∃ r : Real, 0 < r ∧ ∀ z : E,
      z ∈ Metric.ball (0 : E) r →
        intrinsicFramedExp (I := I) g hEnorm p z =
          framedExpMap (I := I) g p z := by
  obtain ⟨r, hr, hagree⟩ :=
    exists_expMapIntrinsic_eq_expMap_radius (I := I) g hEnorm p
  refine ⟨r, hr, ?_⟩
  intro z hz
  have hnorm : norm z < r := by
    simpa only [Metric.mem_ball, dist_zero_right] using hz
  rw [intrFrame_apply, framedExpMap_apply]
  exact hagree (by simpa only [normalFrame_sqrt] using hnorm)

noncomputable def intrFrameRadius
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) : Real :=
  Classical.choose (exists_intrFrame_eq (I := I) g hEnorm p)

omit [CompleteSpace E]
  [ConnectedSpace M] in
theorem intrFrameRadius_pos
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) :
    0 < intrFrameRadius (I := I) g hEnorm p :=
  (Classical.choose_spec (exists_intrFrame_eq (I := I) g hEnorm p)).1

omit [CompleteSpace E]
  [ConnectedSpace M] in
theorem intrFrame_eq_of_mem
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {z : E}
    (hz : z ∈ Metric.ball (0 : E) (intrFrameRadius (I := I) g hEnorm p)) :
    intrinsicFramedExp (I := I) g hEnorm p z =
      framedExpMap (I := I) g p z :=
  (Classical.choose_spec (exists_intrFrame_eq (I := I) g hEnorm p)).2 z hz

noncomputable def intrFrameDiffeo
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) : PartialDiffeomorph (modelWithCornersSelf Real E) I E M 1 := by
  let Φ := framedExpDiffeo (I := I) g p
  let U : Set E := Φ.source ∩
    Metric.ball (0 : E) (intrFrameRadius (I := I) g hEnorm p)
  let f : E → M := intrinsicFramedExp (I := I) g hEnorm p
  have hEq : Set.EqOn f Φ U := by
    intro z hz
    exact (intrFrame_eq_of_mem (I := I) g hEnorm p hz.2).trans
      (framedExp_eq_expMap (I := I) g p hz.1).symm
  exact
    { toPartialEquiv :=
        { toFun := f
          invFun := Φ.symm
          source := U
          target := Φ '' U
          map_source' := by
            intro z hz
            exact ⟨z, hz, (hEq hz).symm⟩
          map_target' := by
            rintro q ⟨z, hz, rfl⟩
            have hleft : (Φ.symm : M → E) (Φ z) = z :=
              Φ.toPartialEquiv.left_inv hz.1
            rw [hleft]
            exact hz
          left_inv' := by
            intro z hz
            rw [hEq hz]
            exact Φ.toPartialEquiv.left_inv hz.1
          right_inv' := by
            rintro q ⟨z, hz, rfl⟩
            have hleft : (Φ.symm : M → E) (Φ z) = z :=
              Φ.toPartialEquiv.left_inv hz.1
            rw [hleft]
            exact hEq hz }
      open_source := Φ.open_source.inter Metric.isOpen_ball
      open_target := by
        exact Φ.toOpenPartialHomeomorph.isOpen_image_source_inter Metric.isOpen_ball
      contMDiffOn_toFun := by
        exact (intrFrame_smooth (I := I) g hEnorm p).contMDiffOn.of_le
          (by exact_mod_cast le_top)
      contMDiffOn_invFun := by
        apply Φ.contMDiffOn_invFun.mono
        rintro q ⟨z, hz, rfl⟩
        exact Φ.map_source' hz.1 }

omit [ConnectedSpace M] in
@[simp] theorem intrFrameDiffeo_source
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) :
    (intrFrameDiffeo (I := I) g hEnorm p).source =
      (framedExpDiffeo (I := I) g p).source ∩
        Metric.ball (0 : E) (intrFrameRadius (I := I) g hEnorm p) := by
  rfl

omit [ConnectedSpace M] in
theorem zero_mem_intrFrame_source
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) :
    (0 : E) ∈ (intrFrameDiffeo (I := I) g hEnorm p).source := by
  rw [intrFrameDiffeo_source]
  exact ⟨zero_mem_framedExp_source (I := I) g p,
    by simpa using intrFrameRadius_pos (I := I) g hEnorm p⟩

omit [ConnectedSpace M] in
@[simp] theorem intrFrameDiffeo_apply
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (z : E) :
    intrFrameDiffeo (I := I) g hEnorm p z =
      intrinsicFramedExp (I := I) g hEnorm p z := by
  rfl

omit [ConnectedSpace M] in
@[simp] theorem intrFrame_symm_eq
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (q : M) :
    (intrFrameDiffeo (I := I) g hEnorm p).symm q =
      framedChartAt (I := I) g p q := by
  rfl

omit [ConnectedSpace M] in
theorem intrFrame_eq_old
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {z : E}
    (hz : z ∈ (intrFrameDiffeo (I := I) g hEnorm p).source) :
    intrinsicFramedExp (I := I) g hEnorm p z =
      framedExpDiffeo (I := I) g p z := by
  rw [intrFrameDiffeo_source] at hz
  exact (intrFrame_eq_of_mem (I := I) g hEnorm p hz.2).trans
    (framedExp_eq_expMap (I := I) g p hz.1).symm

noncomputable def intrFrameMetric
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) : E → E →L[Real] E →L[Real] Real :=
  fun z =>
    let F : E → M := intrinsicFramedExp (I := I) g hEnorm p
    let D : E →L[Real] TangentSpace I (F z) :=
      mfderiv (modelWithCornersSelf Real E) I F z
    (ContinuousLinearMap.precomp Real D).comp
      ((g.inner (F z)).comp D)

omit [CompleteSpace E] [T2Space (TangentBundle I M)] in
omit [ConnectedSpace M] in
theorem intrFrameMetric_apply
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (z v w : E) :
    intrFrameMetric (I := I) g hEnorm p z v w =
      g.inner (intrinsicFramedExp (I := I) g hEnorm p z)
        (mfderiv (modelWithCornersSelf Real E) I
          (intrinsicFramedExp (I := I) g hEnorm p) z v)
        (mfderiv (modelWithCornersSelf Real E) I
          (intrinsicFramedExp (I := I) g hEnorm p) z w) := by
  simp only [intrFrameMetric, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.precomp_apply]
  rfl

omit [ConnectedSpace M] in
@[simp] theorem intrFrameMetric_zero
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) :
    intrFrameMetric (I := I) g hEnorm p 0 =
      (innerSL Real : E →L[Real] E →L[Real] Real) := by
  ext v w
  rw [intrFrameMetric_apply, intrFrame_zero,
    intrFrame_deriv_zero]
  change g.inner p (normalFrame (I := I) g p v)
    (normalFrame (I := I) g p w) = Inner.inner Real v w
  exact normalFrame_inner (I := I) g p v w

omit [ConnectedSpace M] in
theorem intrFrameMetric_eq
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) {z : E}
    (hz : z ∈ (intrFrameDiffeo (I := I) g hEnorm p).source) :
    intrFrameMetric (I := I) g hEnorm p z = framedMetric (I := I) g p z := by
  have hev : Filter.EventuallyEq (nhds z)
      (intrinsicFramedExp (I := I) g hEnorm p)
      (fun q : E => framedExpDiffeo (I := I) g p q) :=
    Filter.eventuallyEq_of_mem
      ((intrFrameDiffeo (I := I) g hEnorm p).open_source.mem_nhds hz)
      (fun _ hq => intrFrame_eq_old (I := I) g hEnorm p hq)
  have hD : mfderiv (modelWithCornersSelf Real E) I
      (intrinsicFramedExp (I := I) g hEnorm p) z =
      mfderiv (modelWithCornersSelf Real E) I
        (fun q : E => framedExpDiffeo (I := I) g p q) z :=
    Filter.EventuallyEq.mfderiv_eq
      (I := modelWithCornersSelf Real E) (I' := I) hev
  ext v w
  rw [intrFrameMetric_apply, framedMetric_apply,
    intrFrame_eq_old (I := I) g hEnorm p hz, hD]

end

end NormalCoordinates
end Riemannian
end Geometry
end DifferentialGeometry
