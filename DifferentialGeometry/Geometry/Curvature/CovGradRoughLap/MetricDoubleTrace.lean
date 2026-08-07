import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.TensorSlotSwap
import DifferentialGeometry.Geometry.Connection.TensorNabla.HomTensorRSSectionCalculus
open DifferentialGeometry.Geometry.Connection.Realization
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Geometry.Connection


noncomputable section

set_option backward.isDefEq.respectTransparency false

open Bundle Manifold MeasureTheory Set Filter DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Geometry
namespace Curvature

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.TensorMultilinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

set_option backward.isDefEq.respectTransparency false in

noncomputable def metricDoubleTraceFib (g : SmoothRiemannianMetric I M) (r t : ℕ) (x : M) :
    TensorRSSpace r (t + 2) I x →L[ℝ] TensorRSSpace r t I x :=
  haveI : FiniteDimensional ℝ (TensorRSSpace r (t + 2) I x) :=
    tensorRSSpaceFiniteDimensional (I := I) (M := M)
  haveI : T2Space (TensorRSSpace r (t + 2) I x) := tensorRSSpaceT2 (I := I) (M := M)
  haveI : T2Space (TensorRSSpace r t I x) := tensorRSSpaceT2 (I := I) (M := M)
  LinearMap.toContinuousLinearMap
    { toFun := fun V =>
        ∑ i : Fin (Module.finrank ℝ E),
          curryLastTwoTensorSlots (I := I) (M := M) r t x V
            (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x i x)
      map_add' := fun V V' => by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [twoSlotPeel_add, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]
      map_smul' := fun c V => by
        rw [RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [twoSlotPeel_smul, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply] }

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
lemma metricDoubleTraceFib_apply (g : SmoothRiemannianMetric I M) (r t : ℕ) (x : M)
    (V : TensorRSSpace r (t + 2) I x) :
    metricDoubleTraceFib (I := I) (M := M) g r t x V =
      ∑ i : Fin (Module.finrank ℝ E),
        curryLastTwoTensorSlots (I := I) (M := M) r t x V
          (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x i x) := by
  haveI : FiniteDimensional ℝ (TensorRSSpace r (t + 2) I x) :=
    tensorRSSpaceFiniteDimensional (I := I) (M := M)
  haveI : T2Space (TensorRSSpace r (t + 2) I x) := tensorRSSpaceT2 (I := I) (M := M)
  haveI : T2Space (TensorRSSpace r t I x) := tensorRSSpaceT2 (I := I) (M := M)
  rw [metricDoubleTraceFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]

set_option backward.isDefEq.respectTransparency false in

private noncomputable def metricDoubleTraceFibFixedFrame (r t : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M) :
    TensorRSSpace r (t + 2) I x →L[ℝ] TensorRSSpace r t I x :=
  haveI : FiniteDimensional ℝ (TensorRSSpace r (t + 2) I x) :=
    tensorRSSpaceFiniteDimensional (I := I) (M := M)
  haveI : T2Space (TensorRSSpace r (t + 2) I x) := tensorRSSpaceT2 (I := I) (M := M)
  haveI : T2Space (TensorRSSpace r t I x) := tensorRSSpaceT2 (I := I) (M := M)
  LinearMap.toContinuousLinearMap
    { toFun := fun V =>
        ∑ i : Fin (Module.finrank ℝ E),
          curryLastTwoTensorSlots (I := I) (M := M) r t x V (B i x) (B i x)
      map_add' := fun V V' => by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [twoSlotPeel_add, ContinuousLinearMap.add_apply, ContinuousLinearMap.add_apply]
      map_smul' := fun c V => by
        rw [RingHom.id_apply, Finset.smul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [twoSlotPeel_smul, ContinuousLinearMap.smul_apply, ContinuousLinearMap.smul_apply] }

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
private lemma metricDoubleTraceFibFixedFrame_apply (r t : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b) (x : M)
    (V : TensorRSSpace r (t + 2) I x) :
    metricDoubleTraceFibFixedFrame (I := I) (M := M) r t B x V =
      ∑ i : Fin (Module.finrank ℝ E),
        curryLastTwoTensorSlots (I := I) (M := M) r t x V (B i x) (B i x) := by
  haveI : FiniteDimensional ℝ (TensorRSSpace r (t + 2) I x) :=
    tensorRSSpaceFiniteDimensional (I := I) (M := M)
  haveI : T2Space (TensorRSSpace r (t + 2) I x) := tensorRSSpaceT2 (I := I) (M := M)
  haveI : T2Space (TensorRSSpace r t I x) := tensorRSSpaceT2 (I := I) (M := M)
  rw [metricDoubleTraceFibFixedFrame, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk]

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
private lemma metricDoubleTraceFib_eq_fixedFrame_moving (g : SmoothRiemannianMetric I M) (r t : ℕ)
    (x : M) :
    metricDoubleTraceFib (I := I) (M := M) g r t x =
      metricDoubleTraceFibFixedFrame (I := I) (M := M) r t (smoothOrthoFrame (I := I) g x) x := rfl

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    in
private theorem metricDoubleTraceFibFixedFrame_contMDiff (r t : ℕ)
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (t + 2) ℝ E →L[ℝ] TensorRSModel r t ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r (t + 2) ℝ E →L[ℝ] TensorRSModel r t ℝ E)
        (E := fun z : M => TensorRSSpace r (t + 2) I z →L[ℝ] TensorRSSpace r t I z) x
        (metricDoubleTraceFibFixedFrame (I := I) (M := M) r t B x)) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (V₁ := fun z : M => TensorRSSpace r (t + 2) I z)
    (V₂ := fun z : M => TensorRSSpace r t I z)
    (φ := fun x => metricDoubleTraceFibFixedFrame (I := I) (M := M) r t B x)
  intro Z
  have hsum : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r t ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r t ℝ E)
        (E := fun z : M => TensorRSSpace r t I z) x
        (∑ i : Fin (Module.finrank ℝ E),
          curryLastTwoTensorSlots (I := I) (M := M) r t x (Z x) (B i x) (B i x))) := by
    refine ContMDiff.sum_section (s := Finset.univ) (fun i _ => ?_)
    have hA :=
      (covGradBundleEquiv_symm_contMDiff_totalSpace (I := I) (M := M) r (t + 1)).comp Z.contMDiff
    have h1 :=
      ContMDiff.clm_bundle_apply (b := id) hA (hB i)
    have h2 :=
      (covGradBundleEquiv_symm_contMDiff_totalSpace (I := I) (M := M) r t).comp h1
    have h3 :=
      ContMDiff.clm_bundle_apply (b := id) h2 (hB i)
    refine h3.congr ?_
    intro x
    rfl
  refine hsum.congr ?_
  intro x
  exact congrArg (TotalSpace.mk' (TensorRSModel r t ℝ E)
    (E := fun z : M => TensorRSSpace r t I z) x)
    (metricDoubleTraceFibFixedFrame_apply (I := I) (M := M) r t B x (Z x)).symm

set_option backward.isDefEq.respectTransparency false in

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
private theorem metricDoubleTraceFibFixedFrame_frame_independent (g : SmoothRiemannianMetric I M)
    (r t : ℕ)
    {B C : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b} (y : M)
    (hB_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner y (B i y) (B j y) = if i = j then (1 : ℝ) else 0)
    (hC_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner y (C i y) (C j y) = if i = j then (1 : ℝ) else 0) :
    metricDoubleTraceFibFixedFrame (I := I) (M := M) r t B y =
      metricDoubleTraceFibFixedFrame (I := I) (M := M) r t C y := by
  classical
  refine ContinuousLinearMap.ext (fun V => ?_)
  apply tensorRS_eq_of_toModel_eval_eq (I := I) (M := M)
  intro D m
  have hexpand : ∀ F : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b,
      Tensor0SSpace.toModel
          ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace t I y from
            metricDoubleTraceFibFixedFrame (I := I) (M := M) r t F y V) D) m =
        ∑ i : Fin (Module.finrank ℝ E),
          Tensor0SSpace.toModel
            ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace t I y from
              curryLastTwoTensorSlots (I := I) (M := M) r t y V (F i y) (F i y)) D) m := by
    intro F
    rw [show (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace t I y from
          metricDoubleTraceFibFixedFrame (I := I) (M := M) r t F y V) =
        ∑ i : Fin (Module.finrank ℝ E),
          (show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace t I y from
            curryLastTwoTensorSlots (I := I) (M := M) r t y V (F i y) (F i y)) from
      metricDoubleTraceFibFixedFrame_apply (I := I) (M := M) r t F y V]
    rw [ContinuousLinearMap.sum_apply, toModel_sum_eval]
  rw [hexpand B, hexpand C]
  haveI : T2Space (TangentSpace I y) := tangentSpaceT2 (I := I) (M := M)
  haveI : FiniteDimensional ℝ (TangentSpace I y) :=
    tangentSpaceFiniteDimensional (I := I) (M := M)
  set Hb : TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun u =>
          LinearMap.toContinuousLinearMap
            { toFun := fun w => Tensor0SSpace.toModel
                ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace t I y from
                  curryLastTwoTensorSlots (I := I) (M := M) r t y V u w) D) m
              map_add' := fun w w' => by
                rw [map_add (curryLastTwoTensorSlots (I := I) (M := M) r t y V u),
                  ContinuousLinearMap.add_apply,
                  Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]
              map_smul' := fun c w => by
                rw [map_smul (curryLastTwoTensorSlots (I := I) (M := M) r t y V u),
                  ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul,
                  ContinuousMultilinearMap.smul_apply]; rfl }
        map_add' := fun u u' => by
          refine ContinuousLinearMap.ext (fun w => ?_)
          change Tensor0SSpace.toModel
              ((curryLastTwoTensorSlots (I := I) (M := M) r t y V (u + u') w) D) m =
            Tensor0SSpace.toModel ((curryLastTwoTensorSlots (I := I) (M := M) r t y V u w) D) m +
              Tensor0SSpace.toModel ((curryLastTwoTensorSlots (I := I) (M := M) r t y V u' w) D) m
          rw [map_add (curryLastTwoTensorSlots (I := I) (M := M) r t y V),
            ContinuousLinearMap.add_apply,
            ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add,
            ContinuousMultilinearMap.add_apply]
        map_smul' := fun c u => by
          refine ContinuousLinearMap.ext (fun w => ?_)
          change Tensor0SSpace.toModel
              ((curryLastTwoTensorSlots (I := I) (M := M) r t y V (c • u) w) D) m =
            c • Tensor0SSpace.toModel ((curryLastTwoTensorSlots (I := I) (M := M) r t y V u w) D) m
          rw [map_smul (curryLastTwoTensorSlots (I := I) (M := M) r t y V),
            ContinuousLinearMap.smul_apply,
            ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul,
            ContinuousMultilinearMap.smul_apply] }
    with hHb_def
  have hHb_apply : ∀ u w : TangentSpace I y,
      Hb u w = Tensor0SSpace.toModel
        ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace t I y from
          curryLastTwoTensorSlots (I := I) (M := M) r t y V u w) D) m := by
    intro u w
    rw [hHb_def, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace t I y from
            curryLastTwoTensorSlots (I := I) (M := M) r t y V (B i y) (B i y)) D) m) =
      ∑ i : Fin (Module.finrank ℝ E), Hb (B i y) (B i y) from
    Finset.sum_congr rfl (fun i _ => (hHb_apply (B i y) (B i y)).symm)]
  rw [show (∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          ((show Tensor0SSpace r I y →L[ℝ] Tensor0SSpace t I y from
            curryLastTwoTensorSlots (I := I) (M := M) r t y V (C i y) (C i y)) D) m) =
      ∑ i : Fin (Module.finrank ℝ E), Hb (C i y) (C i y) from
    Finset.sum_congr rfl (fun i _ => (hHb_apply (C i y) (C i y)).symm)]
  rw [orthonormal_basis_bilin_trace (I := I) (M := M) g (x := y) Hb (fun i => B i y) hB_orth,
    orthonormal_basis_bilin_trace (I := I) (M := M) g (x := y) Hb (fun i => C i y) hC_orth]

set_option backward.isDefEq.respectTransparency false in

omit [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    in
private lemma metricDoubleTraceFib_eq_fixedFrame_smoothOrthoFrame_on_nbhd
    (g : SmoothRiemannianMetric I M) (r t : ℕ) (x₀ : M)
    {y : M} (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    metricDoubleTraceFib (I := I) (M := M) g r t y =
      metricDoubleTraceFibFixedFrame (I := I) (M := M) r t (smoothOrthoFrame (I := I) g x₀) y := by
  rw [metricDoubleTraceFib_eq_fixedFrame_moving]
  exact metricDoubleTraceFibFixedFrame_frame_independent (I := I) (M := M) g r t y
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g x₀ hy i j)

set_option backward.isDefEq.respectTransparency false in

omit [I.Boundaryless] [BoundarylessManifold I M] in
omit [T2Space M] in
private lemma metricDoubleTraceFib_eventuallyEq_fixedFrame
    (g : SmoothRiemannianMetric I M) (r t : ℕ) (x₀ : M) :
    (fun x : M => TotalSpace.mk'
        (TensorRSModel r (t + 2) ℝ E →L[ℝ] TensorRSModel r t ℝ E)
        (E := fun z : M => TensorRSSpace r (t + 2) I z →L[ℝ] TensorRSSpace r t I z) x
        (metricDoubleTraceFib (I := I) (M := M) g r t x)) =ᶠ[𝓝 x₀]
      (fun x : M => TotalSpace.mk'
        (TensorRSModel r (t + 2) ℝ E →L[ℝ] TensorRSModel r t ℝ E)
        (E := fun z : M => TensorRSSpace r (t + 2) I z →L[ℝ] TensorRSSpace r t I z) x
        (metricDoubleTraceFibFixedFrame (I := I) (M := M) r t
          (smoothOrthoFrame (I := I) g x₀) x)) := by
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel r (t + 2) ℝ E →L[ℝ] TensorRSModel r t ℝ E)
    (E := fun z : M => TensorRSSpace r (t + 2) I z →L[ℝ] TensorRSSpace r t I z) y)
    (metricDoubleTraceFib_eq_fixedFrame_smoothOrthoFrame_on_nbhd (I := I) (M := M) g r t x₀ hy)

set_option backward.isDefEq.respectTransparency false in

omit [I.Boundaryless] [BoundarylessManifold I M] in
  private theorem metricDoubleTraceFib_contMDiffAt
    (g : SmoothRiemannianMetric I M) (r t : ℕ) (x₀ : M) :
    ContMDiffAt I
      (I.prod 𝓘(ℝ, TensorRSModel r (t + 2) ℝ E →L[ℝ] TensorRSModel r t ℝ E)) ∞
      (fun x : M => TotalSpace.mk'
        (TensorRSModel r (t + 2) ℝ E →L[ℝ] TensorRSModel r t ℝ E)
        (E := fun z : M => TensorRSSpace r (t + 2) I z →L[ℝ] TensorRSSpace r t I z) x
      (metricDoubleTraceFib (I := I) (M := M) g r t x)) x₀ := by
  have h_fixed_at :=
    metricDoubleTraceFibFixedFrame_contMDiff (I := I) (M := M) r t
      (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) x₀
  exact h_fixed_at.congr_of_eventuallyEq
    (metricDoubleTraceFib_eventuallyEq_fixedFrame (I := I) (M := M) g r t x₀)

set_option backward.isDefEq.respectTransparency false in

omit [I.Boundaryless] [BoundarylessManifold I M] in
private theorem metricDoubleTraceFib_contMDiff (g : SmoothRiemannianMetric I M) (r t : ℕ) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel r (t + 2) ℝ E →L[ℝ] TensorRSModel r t ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel r (t + 2) ℝ E →L[ℝ] TensorRSModel r t ℝ E)
        (E := fun z : M => TensorRSSpace r (t + 2) I z →L[ℝ] TensorRSSpace r t I z) x
        (metricDoubleTraceFib (I := I) (M := M) g r t x)) :=
  fun x₀ => metricDoubleTraceFib_contMDiffAt (I := I) (M := M) g r t x₀

set_option backward.isDefEq.respectTransparency false in

noncomputable def metricDoubleTraceField (g : SmoothRiemannianMetric I M) (r : ℕ) :
    (t : ℕ) → HomTensorRSField (E := E) (M := M) r (t + 2) t I :=
  fun t =>
    { toFun := fun x : M => metricDoubleTraceFib (I := I) (M := M) g r t x
      contMDiff_toFun := metricDoubleTraceFib_contMDiff (I := I) (M := M) g r t }

set_option backward.isDefEq.respectTransparency false in

omit [I.Boundaryless] [BoundarylessManifold I M] in
lemma metricDoubleTraceField_apply (g : SmoothRiemannianMetric I M) (r t : ℕ) (x : M) :
    (show TensorRSSpace r (t + 2) I x →L[ℝ] TensorRSSpace r t I x from
        metricDoubleTraceField (I := I) (M := M) (E := E) g r t x) =
      metricDoubleTraceFib (I := I) (M := M) g r t x := rfl

set_option backward.isDefEq.respectTransparency false in

theorem roughLap_eq_metricDoubleTrace (g : SmoothRiemannianMetric I M) (r t : ℕ)
    (W : SmoothCcTensor g r t) :
    rawTensorConnLapSmooth (I := I) g r t W =
      homTensorRSFieldApply (I := I) (M := M) g r (t + 2) t
        (metricDoubleTraceField (I := I) (M := M) (E := E) g r t)
        (iteratedCovGrad g r t 2 W) := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  rw [rawTensorConnLapSmooth_toSection_apply, appFullSec_toSection, metricDoubleTraceField_apply,
    metricDoubleTraceFib_apply]
  rw [rawTensorConnLap_eq_frame_trace_secondCovDeriv (I := I) g r t (fun z : M => W.toSection z) x]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  apply tensorRS_eq_of_toModel_eval_eq (I := I) (M := M)
  intro D m
  rw [twoSlotPeel_eval (I := I) (M := M) r t x ((iteratedCovGrad g r t 2 W).toSection x)
    (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x i x) D m]
  rw [show (iteratedCovGrad g r t 2 W).toSection x =
      (covGrad (I := I) (M := M) g r (t + 1)
        (covGrad (I := I) (M := M) g r t W)).toSection x from rfl]
  exact (secondCovGrad_eval_eq_tensorSecondCovDeriv (I := I) g r t W
    (smoothOrthoFrame_smooth (I := I) g x i) (smoothOrthoFrame_smooth (I := I) g x i) x D m).symm



end Curvature
end Geometry
end DifferentialGeometry
