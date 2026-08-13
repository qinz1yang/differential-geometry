import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FrozenFramePureRCurvatureTower.FrameIndependentOperator
open DifferentialGeometry.Geometry.Connection.Realization
open DifferentialGeometry.Analysis.Spectral
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance tensorRSRiemannianNormedAddCommGroup
    (r s : ℕ) [h : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b)] (b : M) :
    NormedAddCommGroup (TensorRSSpace r s I b) :=
  (h.g.toCore b).toNormedAddCommGroupOfTopology
    (h.g.continuousAt b) (h.g.isVonNBounded b)

private noncomputable def pureRDirCLMTensor
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (x : M) (τ : TensorRSSpace 0 (m + 1) I x) :
    TangentSpace I x →L[ℝ] TensorRSSpace 0 m I x :=
  ∑ i : Fin (Module.finrank ℝ E),
    (haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
     haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
     LinearMap.toContinuousLinearMap
      { toFun := fun v => riemannOp (tensorCov (I := I) g 0 m) x (B i x) v
          ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm τ (B i x))
        map_add' := fun v v' => by
          rw [map_add (riemannOp (tensorCov (I := I) g 0 m) x (B i x)) v v']; rfl
        map_smul' := fun c v => by
          rw [map_smul (riemannOp (tensorCov (I := I) g 0 m) x (B i x)) c v]; rfl })


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma pureRDirCLMTensor_apply
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (x : M) (τ : TensorRSSpace 0 (m + 1) I x) (v : TangentSpace I x) :
    pureRDirCLMTensor (I := I) (M := M) g m B x τ v =
      ∑ i : Fin (Module.finrank ℝ E),
        riemannOp (tensorCov (I := I) g 0 m) x (B i x) v
          ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm τ (B i x)) := by
  classical
  rw [pureRDirCLMTensor, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]


omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma pureRFrozenDirCLM_eq_pureRDirCLMTensor
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (W : SmoothCcTensor g 0 (m + 1)) (x : M) :
    pureRFrozenDirCLM (I := I) (M := M) g m B (fun y : M => W.toSection y) x =
      pureRDirCLMTensor (I := I) (M := M) g m B x (W.toSection x) := by
  refine ContinuousLinearMap.ext (fun v => ?_)
  rw [pureRFrozenDirCLM_apply, pureRDirCLMTensor_apply]


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem riemannOp_tensorCov_homNatural
    (g : SmoothRiemannianMetric I M) (m : ℕ) (x : M) (v w : TangentSpace I x)
    (Ξ : TensorRSSpace 0 m I x) (d : Tensor0SSpace 0 I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from
        riemannOp (tensorCov (I := I) g 0 m) x v w Ξ) d =
      riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M m (LeviCivita (I := I) g)) x v w
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from Ξ) d) := by
  classical
  set X : Π y : M, TangentSpace I y := smoothExtensionTangent (I := I) x v with hX_def
  set Wfield : Π y : M, TangentSpace I y := smoothExtensionTangent (I := I) x w with hW_def
  have hX : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% X) :=
    smoothExtensionTangent_contMDiff (I := I) x v
  have hW : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% Wfield) :=
    smoothExtensionTangent_contMDiff (I := I) x w
  have hXx : X x = v := smoothExtensionTangent_eq (I := I) x v
  have hWx : Wfield x = w := smoothExtensionTangent_eq (I := I) x w
  obtain ⟨Ξsec, hΞx⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := TensorRSModel 0 m ℝ E) (V := fun y : M => TensorRSSpace 0 m I y) (n := (⊤ : ℕ∞)) x Ξ
  obtain ⟨dSec, hdSec⟩ := ContMDiffSection.exists_eq_at (I := I)
    (F := Tensor0SModel 0 ℝ E) (V := fun y : M => Tensor0SSpace 0 I y) (n := (⊤ : ℕ∞)) x d
  have hΞd_smooth : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel m ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (Tensor0SModel m ℝ E)
        (E := fun z : M => Tensor0SSpace m I z) y
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace m I y from Ξsec y) (dSec y))) :=
    ContMDiff.clm_bundle_apply (b := id) Ξsec.contMDiff dSec.contMDiff
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from
        riemannOp (tensorCov (I := I) g 0 m) x v w Ξ) d =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from
        riemannSec (tensorCov (I := I) g 0 m) (fun b => X b) (fun b => Wfield b)
          (fun b => Ξsec b) x) (dSec x) from by
    rw [← hXx, ← hWx, ← hΞx,
      riemannOp_apply_smooth (cov := tensorCov (I := I) g 0 m) hX hW Ξsec.contMDiff]
    rw [show d = dSec x from hdSec.symm]]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from
        riemannSec (tensorCov (I := I) g 0 m) (fun b => X b) (fun b => Wfield b)
          (fun b => Ξsec b) x) (dSec x) =
      riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M m (LeviCivita (I := I) g))
          (fun b => X b) (fun b => Wfield b)
          (HomConnectionGen.pairedSection (M := M) (U := fun z : M => Tensor0SSpace 0 I z)
            (V := fun z : M => Tensor0SSpace m I z)
            (fun b => Ξsec b) (fun b => dSec b)) x -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from Ξsec x)
          (riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
            (fun b => X b) (fun b => Wfield b) (fun b => dSec b) x) from
    HomConnectionGen.riemannSec_homBundleGen_apply_eq I M
      (Tensor0SModel 0 ℝ E) (fun z : M => Tensor0SSpace 0 I z)
      (Tensor0SModel m ℝ E) (fun z : M => Tensor0SSpace m I z)
      (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
      (Tensor0SNabla.tensor0SCovariantDerivative I M m (LeviCivita (I := I) g))
      ⟨fun b => X b, hX⟩ ⟨fun b => Wfield b, hW⟩ Ξsec dSec x]
  rw [show riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M 0 (LeviCivita (I := I) g))
        (fun b => X b) (fun b => Wfield b) (fun b => dSec b) x = 0 from
    riemannSec_tensor0SCov_zero_eq_zero (I := I) (M := M) g ⟨fun b => X b, hX⟩
      ⟨fun b => Wfield b, hW⟩ (fun b => dSec b) dSec.contMDiff x]
  rw [map_zero, sub_zero]
  rw [show riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M m (LeviCivita (I := I) g)) x v w
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from Ξ) d) =
      riemannSec (Tensor0SNabla.tensor0SCovariantDerivative I M m (LeviCivita (I := I) g))
          (fun b => X b) (fun b => Wfield b)
          (HomConnectionGen.pairedSection (M := M) (U := fun z : M => Tensor0SSpace 0 I z)
            (V := fun z : M => Tensor0SSpace m I z)
            (fun b => Ξsec b) (fun b => dSec b)) x from by
    rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from Ξ) d =
        HomConnectionGen.pairedSection (M := M) (U := fun z : M => Tensor0SSpace 0 I z)
          (V := fun z : M => Tensor0SSpace m I z)
          (fun b => Ξsec b) (fun b => dSec b) x from by
      rw [HomConnectionGen.pairedSection_apply, show d = dSec x from hdSec.symm, hΞx]]
    rw [← hXx, ← hWx]
    exact riemannOp_apply_smooth
      (cov := Tensor0SNabla.tensor0SCovariantDerivative I M m (LeviCivita (I := I) g)) hX hW
      hΞd_smooth]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
private lemma covGradBundleEquiv_symm_apply_eq_curry
    (m : ℕ) (x : M)
    (τ : TensorRSSpace 0 (m + 1) I x) (w : TangentSpace I x) (d : Tensor0SSpace 0 I x) :
    (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from
      ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm τ) w) d =
      tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from τ) d) w := by
  apply tensor0SSpace_ext (𝕜 := ℝ) m x
  intro v'
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from
        ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm τ) w) d v' =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from
          ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm τ) w) d) v' from rfl]
  rw [covGradBundleEquiv_symm_apply_eval (I := I) (M := M) 0 m x τ w d v']
  rw [show tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from τ) d) w v' =
      Tensor0SSpace.toModel
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from τ) d) w) v' from rfl]
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from τ) d) w v']


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma pureRDirCLMTensor_covGradEquiv_eval
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (x : M) (τ : TensorRSSpace 0 (m + 1) I x) (d : Tensor0SSpace 0 I x)
    (v : Fin (m + 1) → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
          covGradBundleEquiv (I := I) (M := M) 0 m x
            (pureRDirCLMTensor (I := I) (M := M) g m B x τ)) d) v =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M m (LeviCivita (I := I) g)) x
            (B i x) (v 0)
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from τ) d) (B i x)))
          (Matrix.vecTail v) := by
  classical
  rw [covGradBundleEquiv_apply_eval (I := I) (M := M) 0 m x
    (pureRDirCLMTensor (I := I) (M := M) g m B x τ) d v]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace m I x from
        pureRDirCLMTensor (I := I) (M := M) g m B x τ (v 0)) d =
      (∑ i : Fin (Module.finrank ℝ E),
        riemannOp (tensorCov (I := I) g 0 m) x (B i x) (v 0)
          ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm τ (B i x))) d from by
    rw [pureRDirCLMTensor_apply (I := I) (M := M) g m B x τ (v 0)]]
  rw [ContinuousLinearMap.sum_apply, ← Tensor0SSpace.toModelL_apply, map_sum,
    ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Tensor0SSpace.toModelL_apply]
  rw [riemannOp_tensorCov_homNatural (I := I) (M := M) g m x (B i x) (v 0)
    ((covGradBundleEquiv (I := I) (M := M) 0 m x).symm τ (B i x)) d]
  rw [covGradBundleEquiv_symm_apply_eq_curry (I := I) (M := M) m x τ (B i x) d]


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma pureREndoOpFibVal_eval
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (x : M) (S : Tensor0SSpace (m + 1) I x) (v : Fin (m + 1) → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
          covGradBundleEquiv (I := I) (M := M) 0 m x
            (pureRDirCLMTensor (I := I) (M := M) g m B x
              (unitScalarRSLift (I := I) (M := M) x S)))
          (unitZeroSec (I := I) (M := M) x)) v =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M m (LeviCivita (I := I) g)) x
            (B i x) (v 0)
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x S (B i x)))
          (Matrix.vecTail v) := by
  rw [pureRDirCLMTensor_covGradEquiv_eval (I := I) (M := M) g m B x
    (unitScalarRSLift (I := I) (M := M) x S) (unitZeroSec (I := I) (M := M) x) v]
  rw [unitScalarRSLift_apply_unit (I := I) (M := M) x S]


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private noncomputable def pureREndoOpFibFun
    (g : SmoothRiemannianMetric I M) (m : ℕ) (x : M)
    (S : Tensor0SSpace (m + 1) I x) : Tensor0SSpace (m + 1) I x :=
  (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
    covGradBundleEquiv (I := I) (M := M) 0 m x
      (pureRDirCLMTensor (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
        (unitScalarRSLift (I := I) (M := M) x S)))
    (unitZeroSec (I := I) (M := M) x)

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem pureREndoOpFibFun_add
    (g : SmoothRiemannianMetric I M) (m : ℕ) (x : M)
    (S S' : Tensor0SSpace (m + 1) I x) :
    pureREndoOpFibFun (I := I) (M := M) g m x (S + S') =
      pureREndoOpFibFun (I := I) (M := M) g m x S +
        pureREndoOpFibFun (I := I) (M := M) g m x S' := by
  apply tensor0SSpace_ext (𝕜 := ℝ) (m + 1) x
  intro v
  rw [show pureREndoOpFibFun (I := I) (M := M) g m x (S + S') v =
        Tensor0SSpace.toModel (pureREndoOpFibFun (I := I) (M := M) g m x (S + S')) v from rfl,
    show (pureREndoOpFibFun (I := I) (M := M) g m x S +
        pureREndoOpFibFun (I := I) (M := M) g m x S') v =
      Tensor0SSpace.toModel (pureREndoOpFibFun (I := I) (M := M) g m x S) v +
        Tensor0SSpace.toModel (pureREndoOpFibFun (I := I) (M := M) g m x S') v from rfl]
  rw [pureREndoOpFibFun, pureREndoOpFibVal_eval (I := I) (M := M) g m
      (smoothOrthoFrame (I := I) g x) x (S + S') v,
    pureREndoOpFibFun, pureREndoOpFibVal_eval (I := I) (M := M) g m
      (smoothOrthoFrame (I := I) g x) x S v,
    pureREndoOpFibFun, pureREndoOpFibVal_eval (I := I) (M := M) g m
      (smoothOrthoFrame (I := I) g x) x S' v, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x (S + S')
          (smoothOrthoFrame (I := I) g x i x) =
        tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x S
            (smoothOrthoFrame (I := I) g x i x) +
          tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x S'
            (smoothOrthoFrame (I := I) g x i x) from by
    rw [map_add (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x),
      ContinuousLinearMap.add_apply]]
  rw [map_add (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M m
    (LeviCivita (I := I) g)) x (smoothOrthoFrame (I := I) g x i x) (v 0)),
    Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private theorem pureREndoOpFibFun_smul
    (g : SmoothRiemannianMetric I M) (m : ℕ) (x : M) (c : ℝ)
    (S : Tensor0SSpace (m + 1) I x) :
    pureREndoOpFibFun (I := I) (M := M) g m x (c • S) =
      c • pureREndoOpFibFun (I := I) (M := M) g m x S := by
  apply tensor0SSpace_ext (𝕜 := ℝ) (m + 1) x
  intro v
  rw [show pureREndoOpFibFun (I := I) (M := M) g m x (c • S) v =
        Tensor0SSpace.toModel (pureREndoOpFibFun (I := I) (M := M) g m x (c • S)) v from rfl,
    show (c • pureREndoOpFibFun (I := I) (M := M) g m x S) v =
      c • Tensor0SSpace.toModel (pureREndoOpFibFun (I := I) (M := M) g m x S) v from rfl]
  rw [pureREndoOpFibFun, pureREndoOpFibVal_eval (I := I) (M := M) g m
      (smoothOrthoFrame (I := I) g x) x (c • S) v,
    pureREndoOpFibFun, pureREndoOpFibVal_eval (I := I) (M := M) g m
      (smoothOrthoFrame (I := I) g x) x S v, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [show tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x (c • S)
          (smoothOrthoFrame (I := I) g x i x) =
        c • tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x S
          (smoothOrthoFrame (I := I) g x i x) from by
    rw [map_smul (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x),
      ContinuousLinearMap.smul_apply]]
  rw [map_smul (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M m
    (LeviCivita (I := I) g)) x (smoothOrthoFrame (I := I) g x i x) (v 0)),
    Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply]

omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private noncomputable def pureREndoOpFib
    (g : SmoothRiemannianMetric I M) (m : ℕ) (x : M) :
    Tensor0SSpace (m + 1) I x →L[ℝ] Tensor0SSpace (m + 1) I x :=
  haveI : FiniteDimensional ℝ (Tensor0SSpace (m + 1) I x) := inferInstance
  LinearMap.toContinuousLinearMap
    { toFun := pureREndoOpFibFun (I := I) (M := M) g m x
      map_add' := pureREndoOpFibFun_add (I := I) (M := M) g m x
      map_smul' := pureREndoOpFibFun_smul (I := I) (M := M) g m x }


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma pureREndoOpFib_apply
    (g : SmoothRiemannianMetric I M) (m : ℕ) (x : M) (S : Tensor0SSpace (m + 1) I x) :
    pureREndoOpFib (I := I) (M := M) g m x S =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
        covGradBundleEquiv (I := I) (M := M) 0 m x
          (pureRDirCLMTensor (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
            (unitScalarRSLift (I := I) (M := M) x S)))
        (unitZeroSec (I := I) (M := M) x) := by
  rw [pureREndoOpFib, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    pureREndoOpFibFun]


omit [CompactSpace M] in
omit [NeZero (Module.finrank ℝ E)] in
private lemma pureRGenuineEndoFib_eq_comp
    (g : SmoothRiemannianMetric I M) (m : ℕ) (W : SmoothCcTensor g 0 (m + 1)) (x : M) :
    pureRGenuineEndoFib (I := I) (M := M) g m W x =
      TensorRSSpace.ofCLM
        ((pureREndoOpFib (I := I) (M := M) g m x).comp
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from W.toSection x)) := by
  apply tensorRSSpace_ext (𝕜 := ℝ) 0 (m + 1) x
  intro d
  apply tensor0SSpace_ext (𝕜 := ℝ) (m + 1) x
  intro v
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
        pureRGenuineEndoFib (I := I) (M := M) g m W x) d v =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
          covGradBundleEquiv (I := I) (M := M) 0 m x
            (pureRDirCLMTensor (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
              (W.toSection x))) d) v from by
    rw [pureRGenuineEndoFib, pureRFrozenEndoFib,
      pureRFrozenDirCLM_eq_pureRDirCLMTensor (I := I) (M := M) g m
        (smoothOrthoFrame (I := I) g x) W x]
    rfl]
  rw [pureRDirCLMTensor_covGradEquiv_eval (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
    (W.toSection x) d v]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
        TensorRSSpace.ofCLM
          ((pureREndoOpFib (I := I) (M := M) g m x).comp
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from W.toSection x))) d v =
      Tensor0SSpace.toModel
        (pureREndoOpFib (I := I) (M := M) g m x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from W.toSection x) d)) v from
            rfl]
  rw [pureREndoOpFib_apply (I := I) (M := M) g m x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from W.toSection x) d)]
  rw [pureRDirCLMTensor_covGradEquiv_eval (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
    (unitScalarRSLift (I := I) (M := M) x
      ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from W.toSection x) d))
    (unitZeroSec (I := I) (M := M) x) v]
  rw [unitScalarRSLift_apply_unit (I := I) (M := M) x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from W.toSection x) d)]


theorem pureRGenuineDiffOp_zero_succ_toSection_unit_eval
    (g : SmoothRiemannianMetric I M) (m : ℕ) (W : SmoothCcTensor g 0 (m + 1)) (x : M)
    (v : Fin (m + 1) → TangentSpace I x) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
          (pureRGenuineDiffOp (I := I) (M := M) g 0 (m + 1) W).toSection x)
          (unitZeroSec (I := I) (M := M) x)) v =
      ∑ i : Fin (Module.finrank ℝ E),
        Tensor0SSpace.toModel
          (riemannOp (Tensor0SNabla.tensor0SCovariantDerivative I M m (LeviCivita (I := I) g)) x
            (smoothOrthoFrame (I := I) g x i x) (v 0)
            (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) m x
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from W.toSection x)
                (unitZeroSec (I := I) (M := M) x))
              (smoothOrthoFrame (I := I) g x i x)))
          (Matrix.vecTail v) := by
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
        (pureRGenuineDiffOp (I := I) (M := M) g 0 (m + 1) W).toSection x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
        covGradBundleEquiv (I := I) (M := M) 0 m x
          (pureRDirCLMTensor (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
            (W.toSection x))) from by
    change (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
        pureRGenuineEndoFib (I := I) (M := M) g m W x) = _
    rw [pureRGenuineEndoFib, pureRFrozenEndoFib,
      pureRFrozenDirCLM_eq_pureRDirCLMTensor (I := I) (M := M) g m
        (smoothOrthoFrame (I := I) g x) W x]]
  rw [pureRDirCLMTensor_covGradEquiv_eval (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) x
    (W.toSection x) (unitZeroSec (I := I) (M := M) x) v]


private theorem pureREndoOp_contMDiff (g : SmoothRiemannianMetric I M) (m : ℕ) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel (m + 1) (m + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel (m + 1) (m + 1) ℝ E)
        (E := fun z : M => TensorRSSpace (m + 1) (m + 1) I z)
        x (TensorRSSpace.ofCLM (pureREndoOpFib (I := I) (M := M) g m x))) := by
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := Tensor0SModel (m + 1) ℝ E) (V₁ := fun x : M => Tensor0SSpace (m + 1) I x)
    (F₂ := Tensor0SModel (m + 1) ℝ E) (V₂ := fun x : M => Tensor0SSpace (m + 1) I x)
    (φ := fun x => (show Tensor0SSpace (m + 1) I x →L[ℝ] Tensor0SSpace (m + 1) I x from
      pureREndoOpFib (I := I) (M := M) g m x))
  intro Z
  set Wσ : SmoothCcTensor g 0 (m + 1) :=
    ⟨unitScalarRSLiftCₛ (I := I) (M := M) Z, HasCompactSupport.of_compactSpace _⟩ with hWσ_def
  have hpt : ∀ x : M, pureREndoOpFib (I := I) (M := M) g m x (Z x) =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
        pureRGenuineEndoFib (I := I) (M := M) g m Wσ x) (unitZeroSec (I := I) (M := M) x) := by
    intro x
    rw [pureREndoOpFib_apply (I := I) (M := M) g m x (Z x)]
    rw [pureRGenuineEndoFib, pureRFrozenEndoFib,
      pureRFrozenDirCLM_eq_pureRDirCLMTensor (I := I) (M := M) g m
        (smoothOrthoFrame (I := I) g x) Wσ x]
    rfl
  have hWσ : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (m + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 (m + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (m + 1) I z) x
        (pureRGenuineEndoFib (I := I) (M := M) g m Wσ x)) :=
    pureRGenuineEndoFib_contMDiff (I := I) (M := M) g m Wσ
  have heval : ContMDiff I (I.prod 𝓘(ℝ, Tensor0SModel (m + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (Tensor0SModel (m + 1) ℝ E)
        (E := fun z : M => Tensor0SSpace (m + 1) I z) x
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (m + 1) I x from
          pureRGenuineEndoFib (I := I) (M := M) g m Wσ x)
          (unitZeroSec (I := I) (M := M) x))) :=
    ContMDiff.clm_bundle_apply (b := id) hWσ (unitZeroSec (I := I) (M := M)).contMDiff
  refine heval.congr ?_
  intro x
  exact (congrArg (TotalSpace.mk' (Tensor0SModel (m + 1) ℝ E)
    (E := fun z : M => Tensor0SSpace (m + 1) I z) x) (hpt x)).symm ▸ rfl

theorem exists_baseOperatorField_apply_eq_pureRGenuineDiffOp (g : SmoothRiemannianMetric I M) :
    ∃ Φ₀ : ∀ r : ℕ, SmoothCcTensor g (r + 0) (r + 0),
      ∀ (r : ℕ) (W : SmoothCcTensor g 0 r),
        pureRGenuineDiffOp (I := I) (M := M) g 0 r W =
          operatorFieldApply (I := I) (M := M) g (r + 0) (r + 0) (Φ₀ r) W := by
  classical
  refine ⟨fun r => match r with
    | 0 => 0
    | (m + 1) =>
        { toSection :=
            { toFun := fun x : M => TensorRSSpace.ofCLM (pureREndoOpFib (I := I) (M := M) g m x)
              contMDiff_toFun := pureREndoOp_contMDiff (I := I) (M := M) g m }
          hasCompactSupport := HasCompactSupport.of_compactSpace _ }, ?_⟩
  intro r W
  cases r with
  | zero =>
      apply SmoothCcTensor.ext
      apply ContMDiffSection.ext
      intro x
      rw [show (pureRGenuineDiffOp (I := I) (M := M) g 0 0 W).toSection x =
            (pureRGenuineEndo0 (I := I) (M := M) g 0 W).toSection x from rfl,
        show pureRGenuineEndo0 (I := I) (M := M) g 0 W = 0 from rfl,
        SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero]
      rw [appCc_toSection (I := I) (M := M) g 0 0 0 W]
      rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace 0 I x from
            (0 : SmoothCcTensor g 0 0).toSection x) = 0 from by
        rw [SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero]; rfl]
      rw [ContinuousLinearMap.zero_comp]
      rfl
  | succ m =>
      apply SmoothCcTensor.ext
      apply ContMDiffSection.ext
      intro x
      rw [show (pureRGenuineDiffOp (I := I) (M := M) g 0 (m + 1) W).toSection x =
            pureRGenuineEndoFib (I := I) (M := M) g m W x from rfl]
      rw [appCc_toSection (I := I) (M := M) g (m + 1) (m + 1) _ W]
      rw [pureRGenuineEndoFib_eq_comp (I := I) (M := M) g m W x]
      rfl

theorem exists_proportional_pureRGenuineDiffOp_highOrder (g : SmoothRiemannianMetric I M) :
    ∃ kappaHigh : ℕ → ℕ → ℝ, (∀ p r, 0 ≤ kappaHigh p r) ∧
      ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + (p + 1)) x
            ((pureRGenuineDiffOp (I := I) (M := M) g (p + 1) r W).toSection x) ≤
          kappaHigh p r * ∑ q ∈ Finset.range (p + 2),
            riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
              ((iteratedCovGrad g 0 r q W).toSection x) := by
  classical
  obtain ⟨Φ₀, hΦ₀⟩ := exists_baseOperatorField_apply_eq_pureRGenuineDiffOp (I := I) (M := M) g
  have hNF : ∀ (p r : ℕ),
      IsIteratedCovGradNormalForm (I := I) (M := M) g (pureRGenuineDiffOp (I := I) (M := M) g) p
        r :=
    fun p => normalForm_of_base (I := I) (M := M) g
      (pureRGenuineDiffOp (I := I) (M := M) g)
      (covGrad_pureRGenuineDiffOp_eq (I := I) (M := M) g) Φ₀ hΦ₀ p
  choose kap hkap_nn hkap using fun p r =>
    exists_jet_bound_of_normalForm (I := I) (M := M) g
      (pureRGenuineDiffOp (I := I) (M := M) g) p r (hNF p r)
  refine ⟨fun p r => kap (p + 1) r, fun p r => hkap_nn (p + 1) r, fun p r W x => ?_⟩
  have h := hkap (p + 1) r W x
  rw [show (p + 1) + 1 = p + 2 from rfl] at h
  exact h

theorem exists_proportional_pureRGenuineDiffOp (g : SmoothRiemannianMetric I M) :
    ∃ kappa : ℕ → ℕ → ℝ, (∀ p r, 0 ≤ kappa p r) ∧
      ∀ (p r : ℕ) (W : SmoothCcTensor g 0 r) (x : M),
        riemannianFiberNormSq (I := I) (M := M) g 0 (r + p) x
            ((pureRGenuineDiffOp (I := I) (M := M) g p r W).toSection x) ≤
          kappa p r * ∑ q ∈ Finset.range (p + 1),
            riemannianFiberNormSq (I := I) (M := M) g 0 (r + q) x
              ((iteratedCovGrad g 0 r q W).toSection x) := by
  classical
  obtain ⟨kappa0, hkappa0_nn, hkappa0⟩ :=
    exists_proportional_pureRFrozenFrameDiffOp_orderZero (I := I) (M := M) g
  obtain ⟨kappaHigh, hkappaHigh_nn, hkappaHigh⟩ :=
    exists_proportional_pureRGenuineDiffOp_highOrder (I := I) (M := M) g
  refine ⟨fun p r => match p with | 0 => kappa0 r | (p' + 1) => kappaHigh p' r,
    fun p r => ?_, fun p r W x => ?_⟩
  · cases p with
    | zero => exact hkappa0_nn r
    | succ p' => exact hkappaHigh_nn p' r
  · cases p with
    | zero =>
        have h := hkappa0 r W x
        rw [show (fun p r => match p with
            | 0 => kappa0 r | (p' + 1) => kappaHigh p' r) 0 r = kappa0 r from rfl]
        have hsec : (pureRGenuineDiffOp (I := I) (M := M) g 0 r W).toSection x =
            (pureRFrozenDiffOp (I := I) (M := M) g (smoothOrthoFrame (I := I) g x)
              (fun i => smoothOrthoFrame_smooth (I := I) g x i) 0 r W).toSection x := by
          cases r with
          | zero => rfl
          | succ m => rfl
        rw [hsec, Finset.sum_range_one]
        exact h
    | succ p' =>
        have h := hkappaHigh p' r W x
        rw [show (fun p r => match p with
            | 0 => kappa0 r | (p'' + 1) => kappaHigh p'' r) (p' + 1) r = kappaHigh p' r from rfl]
        rw [show (p' + 1) + 1 = p' + 2 from rfl]
        exact h

end Curvature
end Geometry
end DifferentialGeometry

end
