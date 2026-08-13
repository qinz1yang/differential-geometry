import DifferentialGeometry.Geometry.Curvature.Bochner.PointwiseTensorCurvFirstOrderBound
import DifferentialGeometry.Geometry.Connection.TensorNabla.HomTensorRSValueLocal
import DifferentialGeometry.Geometry.Curvature.FiberNormParseval.Slot0CurryReconstruction
import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.RicciTraceCarrier
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnection
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

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M] [T2Space M]
    in
lemma smoothOrthoFrame_parsevalExpand
    (g : SmoothRiemannianMetric I M) (x : M) (u : TangentSpace I x) :
    u = ∑ a : Fin (Module.finrank ℝ E),
      g.inner x (smoothOrthoFrame (I := I) g x a x) u • (smoothOrthoFrame (I := I) g x a x) := by
  classical
  haveI : Nonempty (Fin (Module.finrank ℝ E)) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank ℝ E))⟩⟩
  set e : Fin (Module.finrank ℝ E) → TangentSpace I x :=
    fun a => smoothOrthoFrame (I := I) g x a x with he_def
  have horth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0 := fun i j =>
    smoothOrthoFrame_orthonormal_at_center (I := I) g x i j
  have he_li : LinearIndependent ℝ e := by
    rw [linearIndependent_iff']
    intro fs c hsum k hk_mem
    have h_zero : g.inner x (e k) (∑ j ∈ fs, c j • e j) = 0 := by rw [hsum]; simp
    rw [map_sum] at h_zero
    have h_pull : ∀ j ∈ fs, g.inner x (e k) (c j • e j) = c j * (if k = j then (1 : ℝ) else 0) := by
      intro j _
      rw [(g.inner x (e k)).map_smul (c j) (e j), smul_eq_mul, horth k j]
    rw [Finset.sum_congr rfl h_pull, Finset.sum_eq_single_of_mem k hk_mem] at h_zero
    · rwa [if_pos rfl, mul_one] at h_zero
    · intro j _ hjk; rw [if_neg (fun h => hjk h.symm), mul_zero]
  have hcard : Fintype.card (Fin (Module.finrank ℝ E)) = Module.finrank ℝ (TangentSpace I x) := by
    rw [Fintype.card_fin]; rfl
  set bse : Module.Basis (Fin (Module.finrank ℝ E)) ℝ (TangentSpace I x) :=
    basisOfLinearIndependentOfCardEqFinrank he_li hcard with hbse_def
  have hbse_eq : ∀ i, bse i = e i := by
    intro i; rw [hbse_def]; exact congrFun (coe_basisOfLinearIndependentOfCardEqFinrank he_li hcard)
      i
  conv_lhs => rw [← bse.sum_repr u]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [hbse_eq a]
  apply congrArg (fun c : ℝ => c • e a)
  have hrepr : g.inner x (e a) u =
      ∑ b : Fin (Module.finrank ℝ E), bse.repr u b * g.inner x (e a) (e b) := by
    conv_lhs => rw [show u = ∑ b : Fin (Module.finrank ℝ E),
      bse.repr u b • bse b from (bse.sum_repr u).symm]
    rw [map_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [(g.inner x (e a)).map_smul (bse.repr u b) (bse b), smul_eq_mul, hbse_eq b]
  rw [hrepr, Finset.sum_eq_single a]
  · rw [horth a a, if_pos rfl, mul_one]
  · intro b _ hba; rw [horth a b, if_neg (fun h => hba h.symm), mul_zero]
  · intro h; exact absurd (Finset.mem_univ a) h

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
private lemma tensor0SAsRS_add_loc {t : ℕ} (x : M) (C D : Tensor0SSpace t I x) :
    tensor0SToTensorRS (I := I) (M := M) x (C + D) =
      tensor0SToTensorRS (I := I) (M := M) x C + tensor0SToTensorRS (I := I) (M := M) x D := by
  apply tensorRSSpace_ext (𝕜 := ℝ) 0 t x
  intro τ
  rw [tensor0SAsRS_apply (I := I) (M := M) x (C + D) τ]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensor0SToTensorRS (I := I) (M := M) x C + tensor0SToTensorRS (I := I) (M := M) x D) τ =
      (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensor0SToTensorRS (I := I) (M := M) x C) τ +
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
          tensor0SToTensorRS (I := I) (M := M) x D) τ from by
    rw [ContinuousLinearMap.add_apply]]
  rw [tensor0SAsRS_apply (I := I) (M := M) x C τ, tensor0SAsRS_apply (I := I) (M := M) x D τ,
    smul_add]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
private lemma tensor0SAsRS_smul_loc {t : ℕ} (x : M) (c : ℝ) (C : Tensor0SSpace t I x) :
    tensor0SToTensorRS (I := I) (M := M) x (c • C) =
      c • tensor0SToTensorRS (I := I) (M := M) x C := by
  apply tensorRSSpace_ext (𝕜 := ℝ) 0 t x
  intro τ
  rw [tensor0SAsRS_apply (I := I) (M := M) x (c • C) τ]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        c • tensor0SToTensorRS (I := I) (M := M) x C) τ =
      c • (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace t I x from
        tensor0SToTensorRS (I := I) (M := M) x C) τ from by
    rw [ContinuousLinearMap.smul_apply]]
  rw [tensor0SAsRS_apply (I := I) (M := M) x C τ, smul_comm]

noncomputable def tensorSlotZeroEvalFib (x : M) (s : ℕ)
    (v : TangentSpace I x) :
    TensorRSSpace 0 (s + 1) I x →L[ℝ] TensorRSSpace 0 s I x :=
  haveI : FiniteDimensional ℝ (TensorRSSpace 0 (s + 1) I x) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x))
  haveI : T2Space (TensorRSSpace 0 (s + 1) I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x))
  LinearMap.toContinuousLinearMap
    { toFun := fun Wx =>
        tensor0SToTensorRS (I := I) (M := M) x
          (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from Wx)
              (unitZeroSec (I := I) (M := M) x)) v)
      map_add' := fun W₁ W₂ => by
        have hval : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from W₁ + W₂)
            (unitZeroSec (I := I) (M := M) x) =
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from W₁)
              (unitZeroSec (I := I) (M := M) x) +
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from W₂)
              (unitZeroSec (I := I) (M := M) x) := by
          rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from W₁ + W₂) =
              (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from W₁) +
                (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from W₂) from rfl,
            ContinuousLinearMap.add_apply]
        rw [hval, map_add (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x),
          ContinuousLinearMap.add_apply,
          tensor0SAsRS_add_loc (I := I) (M := M) x]
      map_smul' := fun c W => by
        have hval : (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from c • W)
            (unitZeroSec (I := I) (M := M) x) =
            c • (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from W)
              (unitZeroSec (I := I) (M := M) x) := by
          rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from c • W) =
              c • (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from W) from rfl,
            ContinuousLinearMap.smul_apply]
        rw [hval, map_smul (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x),
          ContinuousLinearMap.smul_apply, tensor0SAsRS_smul_loc (I := I) (M := M) x]
        rfl }


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
lemma slot0SliceFib_apply (x : M) (s : ℕ) (v : TangentSpace I x)
    (Wx : TensorRSSpace 0 (s + 1) I x) :
    tensorSlotZeroEvalFib (I := I) (M := M) x s v Wx =
      tensor0SToTensorRS (I := I) (M := M) x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from Wx)
            (unitZeroSec (I := I) (M := M) x)) v) := by
  haveI : FiniteDimensional ℝ (TensorRSSpace 0 (s + 1) I x) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x))
  haveI : T2Space (TensorRSSpace 0 (s + 1) I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x))
  rw [tensorSlotZeroEvalFib, LinearMap.coe_toContinuousLinearMap']
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] in
lemma slot0SliceFib_eq_covGradBundleEquiv_symm (x : M) (s : ℕ) (v : TangentSpace I x)
    (T : TensorRSSpace 0 (s + 1) I x) :
    tensorSlotZeroEvalFib (I := I) (M := M) x s v T =
      (show TangentSpace I x →L[ℝ] TensorRSSpace 0 s I x from
        (covGradBundleEquiv (I := I) (M := M) 0 s x).symm T) v := by
  classical
  apply tensorRSSpace_ext (𝕜 := ℝ) 0 s x
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  rw [slot0SliceFib_apply]
  rw [tensor0SAsRS_apply (I := I) (M := M) x _ D]
  simp only [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply]
  rw [TensorMultilinear.tensor0S_curry_apply_eval (I := I) (M := M)
      (T := (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from T)
        (unitZeroSec (I := I) (M := M) x)) (v0 := v) (vs := m)]
  rw [covGradBundleEquiv_symm_apply_eval (I := I) (M := M) 0 s x T v D m]
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from T) D =
      tensor00Scalar (I := I) (M := M) x D •
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from T)
          (unitZeroSec (I := I) (M := M) x) from by
    conv_lhs => rw [tensor0S_zero_span' (I := I) (M := M) x D]
    rw [ContinuousLinearMap.map_smul]]
  simp only [Tensor0SSpace.toModel_smul, ContinuousMultilinearMap.smul_apply]

omit [NeZero (Module.finrank ℝ E)] in
lemma slot0SliceFib_covGrad_eq (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s)
    (x : M) (v : TangentSpace I x) :
    tensorSlotZeroEvalFib (I := I) (M := M) x s v ((covGrad (I := I) (M := M) g 0 s S).toSection x)
      =
      (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x v := by
  rw [slot0SliceFib_apply]
  rw [curry_covGrad_unit_eval_general (I := I) (M := M) g s S x v]
  exact tensor0SAsRS_unit_recover (I := I) (M := M) s x
    ((tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x v)


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
lemma slot0SliceFib_dir_add (x : M) (s : ℕ) (v v' : TangentSpace I x)
    (Wx : TensorRSSpace 0 (s + 1) I x) :
    tensorSlotZeroEvalFib (I := I) (M := M) x s (v + v') Wx =
      tensorSlotZeroEvalFib (I := I) (M := M) x s v Wx + tensorSlotZeroEvalFib (I := I) (M := M) x s
        v' Wx := by
  rw [slot0SliceFib_apply, slot0SliceFib_apply, slot0SliceFib_apply]
  rw [map_add (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from Wx)
      (unitZeroSec (I := I) (M := M) x)))]
  rw [tensor0SAsRS_add_loc (I := I) (M := M) x]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
    [T2Space M] in
lemma slot0SliceFib_dir_smul (x : M) (s : ℕ) (c : ℝ) (v : TangentSpace I x)
    (Wx : TensorRSSpace 0 (s + 1) I x) :
    tensorSlotZeroEvalFib (I := I) (M := M) x s (c • v) Wx =
      c • tensorSlotZeroEvalFib (I := I) (M := M) x s v Wx := by
  rw [slot0SliceFib_apply, slot0SliceFib_apply]
  rw [map_smul (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
    ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from Wx)
      (unitZeroSec (I := I) (M := M) x)))]
  rw [tensor0SAsRS_smul_loc (I := I) (M := M) x]

noncomputable def curvatureGradContractionDirLM
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (x : M) (Wx : TensorRSSpace 0 (s + 1) I x) :
    TangentSpace I x →ₗ[ℝ] TensorRSSpace 0 s I x where
  toFun w := ∑ i : Fin (Module.finrank ℝ E),
    ((2 : ℝ) • riemannOp (tensorCov (I := I) g 0 s) x (B i x) w
        (tensorSlotZeroEvalFib (I := I) (M := M) x s (B i x) Wx) -
      tensorSlotZeroEvalFib (I := I) (M := M) x s
        (riemannOp (LeviCivita (I := I) g) x (B i x) w (B i x)) Wx)
  map_add' w w' := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_add (riemannOp (tensorCov (I := I) g 0 s) x (B i x)) w w',
      ContinuousLinearMap.add_apply, smul_add]
    rw [map_add (riemannOp (LeviCivita (I := I) g) x (B i x)) w w',
      ContinuousLinearMap.add_apply, slot0SliceFib_dir_add (I := I) (M := M) x s]
    abel
  map_smul' c w := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [map_smul (riemannOp (tensorCov (I := I) g 0 s) x (B i x)) c w,
      ContinuousLinearMap.smul_apply, smul_comm (2 : ℝ) c]
    rw [map_smul (riemannOp (LeviCivita (I := I) g) x (B i x)) c w,
      ContinuousLinearMap.smul_apply, slot0SliceFib_dir_smul (I := I) (M := M) x s]
    rw [smul_sub]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
@[simp] lemma gradArmDirLM_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (x : M) (Wx : TensorRSSpace 0 (s + 1) I x) (w : TangentSpace I x) :
    curvatureGradContractionDirLM (I := I) (M := M) g s B x Wx w =
      ∑ i : Fin (Module.finrank ℝ E),
        ((2 : ℝ) • riemannOp (tensorCov (I := I) g 0 s) x (B i x) w
            (tensorSlotZeroEvalFib (I := I) (M := M) x s (B i x) Wx) -
          tensorSlotZeroEvalFib (I := I) (M := M) x s
            (riemannOp (LeviCivita (I := I) g) x (B i x) w (B i x)) Wx) := rfl

noncomputable def curvatureGradContractionDirCLM
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (x : M) (Wx : TensorRSSpace 0 (s + 1) I x) :
    TangentSpace I x →L[ℝ] TensorRSSpace 0 s I x :=
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  LinearMap.toContinuousLinearMap (curvatureGradContractionDirLM (I := I) (M := M) g s B x Wx)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
@[simp] lemma gradArmDirCLM_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (x : M) (Wx : TensorRSSpace 0 (s + 1) I x) (w : TangentSpace I x) :
    curvatureGradContractionDirCLM (I := I) (M := M) g s B x Wx w =
      ∑ i : Fin (Module.finrank ℝ E),
        ((2 : ℝ) • riemannOp (tensorCov (I := I) g 0 s) x (B i x) w
            (tensorSlotZeroEvalFib (I := I) (M := M) x s (B i x) Wx) -
          tensorSlotZeroEvalFib (I := I) (M := M) x s
            (riemannOp (LeviCivita (I := I) g) x (B i x) w (B i x)) Wx) := by
  rw [curvatureGradContractionDirCLM, LinearMap.coe_toContinuousLinearMap']
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma gradArmDirCLM_value_add
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (x : M) (W₁ W₂ : TensorRSSpace 0 (s + 1) I x) :
    curvatureGradContractionDirCLM (I := I) (M := M) g s B x (W₁ + W₂) =
      curvatureGradContractionDirCLM (I := I) (M := M) g s B x W₁ + curvatureGradContractionDirCLM
        (I := I) (M := M) g s B x W₂ := by
  apply ContinuousLinearMap.ext
  intro w
  rw [ContinuousLinearMap.add_apply, gradArmDirCLM_apply, gradArmDirCLM_apply, gradArmDirCLM_apply,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_add (tensorSlotZeroEvalFib (I := I) (M := M) x s (B i x)) W₁ W₂,
    map_add (riemannOp (tensorCov (I := I) g 0 s) x (B i x) w), smul_add,
    map_add (tensorSlotZeroEvalFib (I := I) (M := M) x s
      (riemannOp (LeviCivita (I := I) g) x (B i x) w (B i x))) W₁ W₂]
  abel

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma gradArmDirCLM_value_smul
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (x : M) (c : ℝ) (W : TensorRSSpace 0 (s + 1) I x) :
    curvatureGradContractionDirCLM (I := I) (M := M) g s B x (c • W) =
      c • curvatureGradContractionDirCLM (I := I) (M := M) g s B x W := by
  apply ContinuousLinearMap.ext
  intro w
  rw [ContinuousLinearMap.smul_apply, gradArmDirCLM_apply, gradArmDirCLM_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul (tensorSlotZeroEvalFib (I := I) (M := M) x s (B i x)) c W,
    map_smul (riemannOp (tensorCov (I := I) g 0 s) x (B i x) w),
    map_smul (tensorSlotZeroEvalFib (I := I) (M := M) x s
      (riemannOp (LeviCivita (I := I) g) x (B i x) w (B i x))) c W]
  rw [smul_sub, smul_comm (2 : ℝ) c]

noncomputable def curvatureGradContractionFib
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (x : M) :
    TensorRSSpace 0 (s + 1) I x →L[ℝ] TensorRSSpace 0 (s + 1) I x :=
  haveI : FiniteDimensional ℝ (TensorRSSpace 0 (s + 1) I x) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x))
  haveI : T2Space (TensorRSSpace 0 (s + 1) I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x))
  LinearMap.toContinuousLinearMap
    { toFun := fun Wx =>
        covGradBundleEquiv (I := I) (M := M) 0 s x
          (curvatureGradContractionDirCLM (I := I) (M := M) g s B x Wx)
      map_add' := fun W₁ W₂ => by
        rw [gradArmDirCLM_value_add (I := I) (M := M) g s B x W₁ W₂, map_add]
      map_smul' := fun c W => by
        rw [gradArmDirCLM_value_smul (I := I) (M := M) g s B x c W, map_smul]
        rfl }


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma gradArmFib_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (x : M) (Wx : TensorRSSpace 0 (s + 1) I x) :
    curvatureGradContractionFib (I := I) (M := M) g s B x Wx =
      covGradBundleEquiv (I := I) (M := M) 0 s x
        (curvatureGradContractionDirCLM (I := I) (M := M) g s B x Wx) := by
  haveI : FiniteDimensional ℝ (TensorRSSpace 0 (s + 1) I x) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x))
  haveI : T2Space (TensorRSSpace 0 (s + 1) I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x))
  rw [curvatureGradContractionFib, LinearMap.coe_toContinuousLinearMap']
  rfl

lemma gradArmFib_covGrad_slice_eq
    (g : SmoothRiemannianMetric I M) (s : ℕ) (S : SmoothCcTensor g 0 s) (x : M)
    (a : Fin (Module.finrank ℝ E)) :
    tensor0SToTensorRS (I := I) (M := M) x
        (tensor0S_curry (I := I) (M := M) (𝕜 := ℝ) s x
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace (s + 1) I x from
            curvatureGradContractionFib (I := I) (M := M) g s (smoothOrthoFrame (I := I) g x) x
              ((covGrad (I := I) (M := M) g 0 s S).toSection x))
            (unitZeroSec (I := I) (M := M) x))
          (smoothOrthoFrame (I := I) g x a x)) =
      (2 : ℝ) • ∑ i : Fin (Module.finrank ℝ E),
          riemannSec (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
            (smoothOrthoFrame (I := I) g x a)
            (covApply (tensorCov (I := I) g 0 s) (smoothOrthoFrame (I := I) g x i)
              (fun y : M => S.toSection y)) x -
        ∑ i : Fin (Module.finrank ℝ E),
          (tensorCov (I := I) g 0 s).toFun (fun y : M => S.toSection y) x
            (riemannOp (LeviCivita (I := I) g) x (smoothOrthoFrame (I := I) g x i x)
              (smoothOrthoFrame (I := I) g x a x) (smoothOrthoFrame (I := I) g x i x)) := by
  classical
  set B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b :=
    fun i => smoothOrthoFrame (I := I) g x i with hB
  set Wx : TensorRSSpace 0 (s + 1) I x := (covGrad (I := I) (M := M) g 0 s S).toSection x with hWx
  rw [gradArmFib_apply (I := I) (M := M) g s B x Wx]
  rw [tensor0S_curry_covGradBundleEquiv_unit_genVal (I := I) (M := M) s x
    (curvatureGradContractionDirCLM (I := I) (M := M) g s B x Wx) (B a x)]
  rw [tensor0SAsRS_unit_recover (I := I) (M := M) s x
    (curvatureGradContractionDirCLM (I := I) (M := M) g s B x Wx (B a x))]
  rw [gradArmDirCLM_apply (I := I) (M := M) g s B x Wx (B a x)]
  rw [Finset.sum_sub_distrib, Finset.smul_sum]
  apply congrArg₂ (fun T U => T - U)
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hWx, slot0SliceFib_covGrad_eq (I := I) (M := M) g s S x (B i x)]
    rw [riemannSec_eq_riemannOp_tensorCov (I := I) g 0 s
      (smoothOrthoFrame_smooth (I := I) g x i) (smoothOrthoFrame_smooth (I := I) g x a)
      (covApplyRS_contMDiff (I := I) g 0 s S.toSection.contMDiff
        (smoothOrthoFrame_smooth (I := I) g x i))]
    rfl
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hWx, slot0SliceFib_covGrad_eq (I := I) (M := M) g s S x
      (riemannOp (LeviCivita (I := I) g) x (B i x) (B a x) (B i x))]


omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] in
lemma slot0SliceFib_section_contMDiff
    (_g : SmoothRiemannianMetric I M) (s : ℕ)
    {Y : Π b : M, TensorRSSpace 0 (s + 1) I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (s + 1) I z) b (Y b)))
    {V : Π b : M, TangentSpace I b}
    (hV : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% V)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) b
        (tensorSlotZeroEvalFib (I := I) (M := M) b s (V b) (Y b))) := by
  have heq : (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
      (E := fun z : M => TensorRSSpace 0 s I z) b
      (tensorSlotZeroEvalFib (I := I) (M := M) b s (V b) (Y b))) =
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) b
        ((show TangentSpace I b →L[ℝ] TensorRSSpace 0 s I b from
          (covGradBundleEquiv (I := I) (M := M) 0 s b).symm (Y b)) (V b))) := by
    funext b
    rw [slot0SliceFib_eq_covGradBundleEquiv_symm (I := I) (M := M) b s (V b) (Y b)]
  rw [heq]
  have hHom : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel 0 s ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel 0 s ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TensorRSSpace 0 s I z) b
        ((covGradBundleEquiv (I := I) (M := M) 0 s b).symm (Y b))) :=
    (covGradBundleEquiv_symm_contMDiff_totalSpace (I := I) (M := M) 0 s).comp hY
  exact ContMDiff.clm_bundle_apply (b := fun b : M => b)
    (ϕ := fun b => (covGradBundleEquiv (I := I) (M := M) 0 s b).symm (Y b))
    (v := fun b => V b) hHom hV

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma gradArmDirCLM_homSection_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    {Y : Π b : M, TensorRSSpace 0 (s + 1) I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (s + 1) I z) b (Y b))) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] TensorRSModel 0 s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (E →L[ℝ] TensorRSModel 0 s ℝ E)
        (E := fun z : M => TangentSpace I z →L[ℝ] TensorRSSpace 0 s I z) x
        (curvatureGradContractionDirCLM (I := I) (M := M) g s B x (Y x))) := by
  classical
  apply contMDiff_clm_section_of_pointwise (I := I) (M := M)
    (F₁ := E) (V₁ := fun z : M => TangentSpace I z)
    (F₂ := TensorRSModel 0 s ℝ E) (V₂ := fun z : M => TensorRSSpace 0 s I z)
    (φ := fun x => curvatureGradContractionDirCLM (I := I) (M := M) g s B x (Y x))
  intro Z
  have hval : (fun x : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
      (E := fun z : M => TensorRSSpace 0 s I z) x
      (curvatureGradContractionDirCLM (I := I) (M := M) g s B x (Y x) (Z x))) =
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) x
        (∑ i : Fin (Module.finrank ℝ E),
          ((2 : ℝ) • riemannOp (tensorCov (I := I) g 0 s) x (B i x) (Z x)
              (tensorSlotZeroEvalFib (I := I) (M := M) x s (B i x) (Y x)) -
            tensorSlotZeroEvalFib (I := I) (M := M) x s
              (riemannOp (LeviCivita (I := I) g) x (B i x) (Z x) (B i x)) (Y x)))) := by
    funext x
    rw [gradArmDirCLM_apply]
  rw [hval]
  refine ContMDiff.sum_section (s := Finset.univ) (fun i _ => ?_)
  have hRarm : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) x
        ((2 : ℝ) • riemannOp (tensorCov (I := I) g 0 s) x (B i x) (Z x)
          (tensorSlotZeroEvalFib (I := I) (M := M) x s (B i x) (Y x)))) := by
    have hslice := slot0SliceFib_section_contMDiff (I := I) (M := M) g s hY (hB i)
    have hRsec : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
        (fun x : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
          (E := fun z : M => TensorRSSpace 0 s I z) x
          (riemannSec (tensorCov (I := I) g 0 s) (B i) Z
            (fun y : M => tensorSlotZeroEvalFib (I := I) (M := M) y s (B i y) (Y y)) x)) :=
      riemannSec_contMDiff (cov := tensorCov (I := I) g 0 s) (hB i) Z.contMDiff hslice
    have hpt : (fun x : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) x
        ((2 : ℝ) • riemannOp (tensorCov (I := I) g 0 s) x (B i x) (Z x)
          (tensorSlotZeroEvalFib (I := I) (M := M) x s (B i x) (Y x)))) =
        (fun x : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
          (E := fun z : M => TensorRSSpace 0 s I z) x
          ((2 : ℝ) • riemannSec (tensorCov (I := I) g 0 s) (B i) Z
            (fun y : M => tensorSlotZeroEvalFib (I := I) (M := M) y s (B i y) (Y y)) x)) := by
      funext x
      rw [riemannOp_apply_smooth (cov := tensorCov (I := I) g 0 s) (hB i) Z.contMDiff hslice]
    rw [hpt]
    exact ContMDiff.smul_section (𝕜 := ℝ) (contMDiff_const (c := (2 : ℝ))) hRsec
  have hC5arm : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 s ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 s ℝ E)
        (E := fun z : M => TensorRSSpace 0 s I z) x
        (tensorSlotZeroEvalFib (I := I) (M := M) x s
          (riemannOp (LeviCivita (I := I) g) x (B i x) (Z x) (B i x)) (Y x))) := by
    have hdir : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
        (T% (fun x : M => riemannOp (LeviCivita (I := I) g) x (B i x) (Z x) (B i x))) := by
      have hsec : ContMDiff I (I.prod 𝓘(ℝ, E)) ∞
          (T% (fun y : M => riemannSec (LeviCivita (I := I) g) (B i) Z (B i) y)) :=
        riemannSec_contMDiff (cov := LeviCivita (I := I) g) (hB i) Z.contMDiff (hB i)
      refine hsec.congr ?_
      intro x
      exact congrArg (TotalSpace.mk' E (E := fun z : M => TangentSpace I z) x)
        (riemannOp_apply_smooth (cov := LeviCivita (I := I) g) (hB i) Z.contMDiff (hB i))
    exact slot0SliceFib_section_contMDiff (I := I) (M := M) g s hY hdir
  exact hRarm.sub_section hC5arm

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
lemma gradArmFib_frozen_section_contMDiff
    (g : SmoothRiemannianMetric I M) (s : ℕ)
    {B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b}
    (hB : ∀ i, ContMDiff I (I.prod 𝓘(ℝ, E)) ∞ (T% (B i)))
    {Y : Π b : M, TensorRSSpace 0 (s + 1) I b}
    (hY : ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E)) ∞
      (fun b : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (s + 1) I z) b (Y b))) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (s + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (s + 1) I z) x
        (curvatureGradContractionFib (I := I) (M := M) g s B x (Y x))) := by
  have heq : (fun x : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
      (E := fun z : M => TensorRSSpace 0 (s + 1) I z) x
      (curvatureGradContractionFib (I := I) (M := M) g s B x (Y x))) =
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 (s + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (s + 1) I z) x
        (covGradBundleEquiv (I := I) (M := M) 0 s x
          (curvatureGradContractionDirCLM (I := I) (M := M) g s B x (Y x)))) := by
    funext x
    rw [gradArmFib_apply (I := I) (M := M) g s B x (Y x)]
  rw [heq]
  exact (covGradBundleEquiv_contMDiff_totalSpace (I := I) (M := M) 0 s).comp
    (gradArmDirCLM_homSection_contMDiff (I := I) (M := M) g s hB hY)

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma frameSum_riemannOp_LeviCivita_eq_neg_ricEndoRaised
    (g : SmoothRiemannianMetric I M) (x : M)
    (e : Fin (Module.finrank ℝ E) → TangentSpace I x)
    (horth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (e i) (e j) = if i = j then (1 : ℝ) else 0)
    (v : TangentSpace I x) :
    ∑ i : Fin (Module.finrank ℝ E), riemannOp (LeviCivita (I := I) g) x (e i) v (e i) =
      - ricEndoRaisedFib (I := I) g x v := by
  classical
  apply SmoothRiemannianMetric.eq_of_inner_eq (I := I) g
  intro ζ
  rw [map_sum, ContinuousLinearMap.sum_apply, map_neg]
  have hflip : ∀ i : Fin (Module.finrank ℝ E),
      g.inner x (riemannOp (LeviCivita (I := I) g) x (e i) v (e i)) ζ =
        - g.inner x (riemannOp (LeviCivita (I := I) g) x (e i) v ζ) (e i) := by
    intro i
    have hskew := riemannOp_metric_skew (I := I) g x (e i) v (e i) ζ
    have hsymm : g.inner x (e i) (riemannOp (LeviCivita (I := I) g) x (e i) v ζ) =
        g.inner x (riemannOp (LeviCivita (I := I) g) x (e i) v ζ) (e i) :=
      g.symm x _ _
    rw [hsymm] at hskew
    linarith [hskew]
  rw [Finset.sum_congr rfl (fun i _ => hflip i), Finset.sum_neg_distrib]
  rw [ContinuousLinearMap.neg_apply, inner_ricEndoRaisedFib (I := I) (M := M) g x v ζ,
    ricciTensor_eq_orthonormal_trace (I := I) g x v ζ e horth]

private noncomputable def curvatureGradContractionBilin
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) (w : TangentSpace I x)
    (Wx : TensorRSSpace 0 (s + 1) I x) (m : Fin s → E) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I x) := inferInstanceAs (FiniteDimensional ℝ E)
  letI : TopologicalSpace (TensorRSSpace 0 s I x) :=
    tensorRSSpace_topologicalSpace 0 s x
  letI : AddCommGroup (TensorRSSpace 0 s I x) := tensorRSSpace_addCommGroup 0 s x
  letI : Module ℝ (TensorRSSpace 0 s I x) := tensorRSSpace_module 0 s x
  letI : ContinuousAdd (TensorRSSpace 0 s I x) := tensorRSSpace_continuousAdd 0 s x
  letI : ContinuousSMul ℝ (TensorRSSpace 0 s I x) := tensorRSSpace_continuousSMul 0 s x
  haveI iFD : FiniteDimensional ℝ (TensorRSSpace 0 s I x) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x))
  haveI iT2 : T2Space (TensorRSSpace 0 s I x) :=
    inferInstanceAs (T2Space (Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x))
  let evalCLM : TensorRSSpace 0 s I x →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun T => Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T)
            (unitZeroSec (I := I) (M := M) x)) m
        map_add' := fun T T' => by
          simp only [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T + T') =
              (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T) +
                (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T') from rfl,
            ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add,
            ContinuousMultilinearMap.add_apply]
        map_smul' := fun c T => by
          simp only [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from c • T) =
              c • (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T) from rfl,
            ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul,
            ContinuousMultilinearMap.smul_apply, RingHom.id_apply] }
  let sliceDirCLM : TangentSpace I x →L[ℝ] TensorRSSpace 0 s I x :=
    LinearMap.toContinuousLinearMap
      { toFun := fun b => tensorSlotZeroEvalFib (I := I) (M := M) x s b Wx
        map_add' := fun b b' => slot0SliceFib_dir_add (I := I) (M := M) x s b b' Wx
        map_smul' := fun c b => slot0SliceFib_dir_smul (I := I) (M := M) x s c b Wx }
  letI : AddCommMonoid (TensorRSSpace 0 s I x →L[ℝ] TensorRSSpace 0 s I x) :=
    ContinuousLinearMap.addCommMonoid
  letI : ContinuousAdd (TensorRSSpace 0 s I x →L[ℝ] TensorRSSpace 0 s I x) :=
    inferInstance
  letI : AddCommMonoid
      (TangentSpace I x →L[ℝ] TensorRSSpace 0 s I x →L[ℝ] TensorRSSpace 0 s I x) :=
    ContinuousLinearMap.addCommMonoid
  LinearMap.toContinuousLinearMap
    { toFun := fun a => evalCLM.comp
        ((riemannOp (tensorCov (I := I) g 0 s) x a w).comp sliceDirCLM)
      map_add' := fun a a' => by
        apply ContinuousLinearMap.ext; intro b
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
          (riemannOp (tensorCov (I := I) g 0 s) x).map_add a a']
        exact evalCLM.map_add _ _
      map_smul' := fun c a => by
        apply ContinuousLinearMap.ext; intro b
        simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
          RingHom.id_apply, (riemannOp (tensorCov (I := I) g 0 s) x).map_smul c a]
        exact evalCLM.map_smul c _ }

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
@[simp] private lemma rArmBilin_apply
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M) (w : TangentSpace I x)
    (Wx : TensorRSSpace 0 (s + 1) I x) (m : Fin s → E) (a b : TangentSpace I x) :
    curvatureGradContractionBilin (I := I) (M := M) g s x w Wx m a b =
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          riemannOp (tensorCov (I := I) g 0 s) x a w
            (tensorSlotZeroEvalFib (I := I) (M := M) x s b Wx))
          (unitZeroSec (I := I) (M := M) x)) m := by
  rw [curvatureGradContractionBilin]
  simp only [LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    ContinuousLinearMap.comp_apply]

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
private lemma gradArmDirCLM_summand_toModel
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (w : TangentSpace I x) (Wx : TensorRSSpace 0 (s + 1) I x) (m : Fin s → E)
    (i : Fin (Module.finrank ℝ E)) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          (2 : ℝ) • riemannOp (tensorCov (I := I) g 0 s) x (B i x) w
              (tensorSlotZeroEvalFib (I := I) (M := M) x s (B i x) Wx) -
            tensorSlotZeroEvalFib (I := I) (M := M) x s
              (riemannOp (LeviCivita (I := I) g) x (B i x) w (B i x)) Wx)
          (unitZeroSec (I := I) (M := M) x)) m =
      (2 : ℝ) * curvatureGradContractionBilin (I := I) (M := M) g s x w Wx m (B i x) (B i x) -
        Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            tensorSlotZeroEvalFib (I := I) (M := M) x s
              (riemannOp (LeviCivita (I := I) g) x (B i x) w (B i x)) Wx)
            (unitZeroSec (I := I) (M := M) x)) m := by
  rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
        (2 : ℝ) • riemannOp (tensorCov (I := I) g 0 s) x (B i x) w
            (tensorSlotZeroEvalFib (I := I) (M := M) x s (B i x) Wx) -
          tensorSlotZeroEvalFib (I := I) (M := M) x s
            (riemannOp (LeviCivita (I := I) g) x (B i x) w (B i x)) Wx) =
      (2 : ℝ) • (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          riemannOp (tensorCov (I := I) g 0 s) x (B i x) w
            (tensorSlotZeroEvalFib (I := I) (M := M) x s (B i x) Wx)) -
        (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
          tensorSlotZeroEvalFib (I := I) (M := M) x s
            (riemannOp (LeviCivita (I := I) g) x (B i x) w (B i x)) Wx) from rfl]
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    Tensor0SSpace.toModel_sub, Tensor0SSpace.toModel_smul,
    ContinuousMultilinearMap.sub_apply, ContinuousMultilinearMap.smul_apply]
  rw [rArmBilin_apply (I := I) (M := M) g s x w Wx m (B i x) (B i x)]
  rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless] in
omit [BoundarylessManifold I M] [T2Space M] in
lemma toModel_unit_finsum {ι : Type*} (s : ℕ) (x : M) (fs : Finset ι)
    (T : ι → TensorRSSpace 0 s I x) (m : Fin s → E) :
    Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from ∑ i ∈ fs, T i)
          (unitZeroSec (I := I) (M := M) x)) m =
      ∑ i ∈ fs, Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T i)
          (unitZeroSec (I := I) (M := M) x)) m := by
  classical
  induction fs using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty]
      rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            (0 : TensorRSSpace 0 s I x)) (unitZeroSec (I := I) (M := M) x) =
          (0 : Tensor0SSpace s I x) from ContinuousLinearMap.zero_apply _]
      rw [Tensor0SSpace.toModel_zero, ContinuousMultilinearMap.zero_apply]
  | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T a + ∑ i ∈ t, T i)
            (unitZeroSec (I := I) (M := M) x) =
          (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T a)
              (unitZeroSec (I := I) (M := M) x) +
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from ∑ i ∈ t, T i)
              (unitZeroSec (I := I) (M := M) x) from by
        rw [show (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T a + ∑ i ∈ t, T i) =
            (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T a) +
              (show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from ∑ i ∈ t, T i) from rfl,
          ContinuousLinearMap.add_apply]]
      rw [Tensor0SSpace.toModel_add, ContinuousMultilinearMap.add_apply, ih]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
lemma gradArmDirCLM_frame_independent
    (g : SmoothRiemannianMetric I M) (s : ℕ) (x : M)
    (B C : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (hBorth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (B i x) (B j x) = if i = j then (1 : ℝ) else 0)
    (hCorth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner x (C i x) (C j x) = if i = j then (1 : ℝ) else 0)
    (Wx : TensorRSSpace 0 (s + 1) I x) :
    curvatureGradContractionDirCLM (I := I) (M := M) g s B x Wx =
      curvatureGradContractionDirCLM (I := I) (M := M) g s C x Wx := by
  classical
  apply ContinuousLinearMap.ext
  intro w
  rw [gradArmDirCLM_apply, gradArmDirCLM_apply]
  apply tensorRSSpace_ext (𝕜 := ℝ) 0 s x
  intro D
  apply Tensor0SSpace.toModel_injective
  refine ContinuousMultilinearMap.ext (fun m => ?_)
  have hredD : ∀ F : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b,
      Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            ∑ i : Fin (Module.finrank ℝ E),
              ((2 : ℝ) • riemannOp (tensorCov (I := I) g 0 s) x (F i x) w
                  (tensorSlotZeroEvalFib (I := I) (M := M) x s (F i x) Wx) -
                tensorSlotZeroEvalFib (I := I) (M := M) x s
                  (riemannOp (LeviCivita (I := I) g) x (F i x) w (F i x)) Wx)) D) m =
        tensor00Scalar (I := I) (M := M) x D *
          ∑ i : Fin (Module.finrank ℝ E),
            Tensor0SSpace.toModel
              ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
                (2 : ℝ) • riemannOp (tensorCov (I := I) g 0 s) x (F i x) w
                    (tensorSlotZeroEvalFib (I := I) (M := M) x s (F i x) Wx) -
                  tensorSlotZeroEvalFib (I := I) (M := M) x s
                    (riemannOp (LeviCivita (I := I) g) x (F i x) w (F i x)) Wx)
                (unitZeroSec (I := I) (M := M) x)) m := by
    intro F
    set T : TensorRSSpace 0 s I x :=
      ∑ i : Fin (Module.finrank ℝ E),
        ((2 : ℝ) • riemannOp (tensorCov (I := I) g 0 s) x (F i x) w
            (tensorSlotZeroEvalFib (I := I) (M := M) x s (F i x) Wx) -
          tensorSlotZeroEvalFib (I := I) (M := M) x s
            (riemannOp (LeviCivita (I := I) g) x (F i x) w (F i x)) Wx) with hT
    have hstep : Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T) D) m =
        tensor00Scalar (I := I) (M := M) x D *
          Tensor0SSpace.toModel
            ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from T)
              (unitZeroSec (I := I) (M := M) x)) m := by
      conv_lhs => rw [tensor0S_zero_span' (I := I) (M := M) x D]
      rw [ContinuousLinearMap.map_smul]
      simp only [Tensor0SSpace.toModel_smul,
        ContinuousMultilinearMap.smul_apply, smul_eq_mul]
    rw [hstep, hT]
    apply congrArg (fun z : ℝ => tensor00Scalar (I := I) (M := M) x D * z)
    exact toModel_unit_finsum (I := I) (M := M) s x Finset.univ
      (fun i => (2 : ℝ) • riemannOp (tensorCov (I := I) g 0 s) x (F i x) w
            (tensorSlotZeroEvalFib (I := I) (M := M) x s (F i x) Wx) -
          tensorSlotZeroEvalFib (I := I) (M := M) x s
            (riemannOp (LeviCivita (I := I) g) x (F i x) w (F i x)) Wx) m
  rw [hredD B, hredD C]
  apply congrArg (fun z : ℝ => tensor00Scalar (I := I) (M := M) x D * z)
  rw [Finset.sum_congr rfl (fun i _ =>
    gradArmDirCLM_summand_toModel (I := I) (M := M) g s x B w Wx m i),
    Finset.sum_congr rfl (fun i _ =>
    gradArmDirCLM_summand_toModel (I := I) (M := M) g s x C w Wx m i)]
  rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  apply congrArg₂ (fun a b : ℝ => a - b)
  · rw [← Finset.mul_sum, ← Finset.mul_sum]
    apply congrArg (fun z : ℝ => 2 * z)
    rw [orthonormal_basis_bilin_trace (I := I) g x
      (curvatureGradContractionBilin (I := I) (M := M) g s x w Wx m)
        (fun i => B i x) hBorth,
      orthonormal_basis_bilin_trace (I := I) g x
        (curvatureGradContractionBilin (I := I) (M := M) g s x w Wx m)
        (fun i => C i x) hCorth]
  · have hsliceSum : ∀ F : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b,
        (∑ i : Fin (Module.finrank ℝ E),
            Tensor0SSpace.toModel ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
              tensorSlotZeroEvalFib (I := I) (M := M) x s
                (riemannOp (LeviCivita (I := I) g) x (F i x) w (F i x)) Wx)
              (unitZeroSec (I := I) (M := M) x)) m) =
          Tensor0SSpace.toModel ((show Tensor0SSpace 0 I x →L[ℝ] Tensor0SSpace s I x from
            tensorSlotZeroEvalFib (I := I) (M := M) x s
              (∑ i : Fin (Module.finrank ℝ E),
                riemannOp (LeviCivita (I := I) g) x (F i x) w (F i x)) Wx)
            (unitZeroSec (I := I) (M := M) x)) m := by
      intro F
      let sliceLM : TangentSpace I x →ₗ[ℝ] TensorRSSpace 0 s I x :=
        { toFun := fun v => tensorSlotZeroEvalFib (I := I) (M := M) x s v Wx
          map_add' := fun v v' => slot0SliceFib_dir_add (I := I) (M := M) x s v v' Wx
          map_smul' := fun c v => slot0SliceFib_dir_smul (I := I) (M := M) x s c v Wx }
      have hdir : tensorSlotZeroEvalFib (I := I) (M := M) x s
            (∑ i : Fin (Module.finrank ℝ E),
              riemannOp (LeviCivita (I := I) g) x (F i x) w (F i x)) Wx =
          ∑ i : Fin (Module.finrank ℝ E),
            tensorSlotZeroEvalFib (I := I) (M := M) x s
              (riemannOp (LeviCivita (I := I) g) x (F i x) w (F i x)) Wx :=
        map_sum sliceLM (fun i => riemannOp (LeviCivita (I := I) g) x (F i x) w (F i x))
          Finset.univ
      rw [hdir]
      exact (toModel_unit_finsum (I := I) (M := M) s x Finset.univ
        (fun i => tensorSlotZeroEvalFib (I := I) (M := M) x s
          (riemannOp (LeviCivita (I := I) g) x (F i x) w (F i x)) Wx) m).symm
    rw [hsliceSum B, hsliceSum C]
    rw [frameSum_riemannOp_LeviCivita_eq_neg_ricEndoRaised (I := I) (M := M) g x
        (fun i => B i x) hBorth w,
      frameSum_riemannOp_LeviCivita_eq_neg_ricEndoRaised (I := I) (M := M) g x
        (fun i => C i x) hCorth w]

end Curvature
end Geometry
end DifferentialGeometry

end
