import DifferentialGeometry.Geometry.Curvature.CovGradRoughLap.FrozenFramePureRCurvatureTower.FrozenOperator
open DifferentialGeometry.Analysis.Spectral
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
  [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

private local instance tensorRSRiemannianNormedAddCommGroup
    (r s : ℕ) [h : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b)] (b : M) :
    NormedAddCommGroup (TensorRSSpace r s I b) :=
  (h.g.toCore b).toNormedAddCommGroupOfTopology
    (h.g.continuousAt b) (h.g.isVonNBounded b)

private noncomputable def pureRSlot0BilinAt
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (W : Π b : M, TensorRSSpace 0 (m + 1) I b) (y : M) (v : TangentSpace I y) :
    TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] TensorRSSpace 0 m I y :=
  haveI : T2Space (TangentSpace I y) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I y) := inferInstanceAs (FiniteDimensional ℝ E)
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace 0 m I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g 0 m
  letI : NormedAddCommGroup (TensorRSSpace 0 m I y) :=
    tensorRSRiemannianNormedAddCommGroup 0 m y
  LinearMap.toContinuousLinearMap
    { toFun := fun X => (riemannOp (tensorCov (I := I) g 0 m) y X v).comp
        ((covGradBundleEquiv (I := I) (M := M) 0 m y).symm (W y))
      map_add' := fun X X' => by
        ext Y
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
          (riemannOp (tensorCov (I := I) g 0 m) y).map_add X X']
      map_smul' := fun c X => by
        ext Y
        simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
          RingHom.id_apply, (riemannOp (tensorCov (I := I) g 0 m) y).map_smul c X] }

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma pureRSlot0BilinAt_apply
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (W : Π b : M, TensorRSSpace 0 (m + 1) I b) (y : M) (v X Y : TangentSpace I y) :
    pureRSlot0BilinAt (I := I) (M := M) g m W y v X Y =
      riemannOp (tensorCov (I := I) g 0 m) y X v
        ((covGradBundleEquiv (I := I) (M := M) 0 m y).symm (W y) Y) := rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] in
omit [SigmaCompactSpace M] in
private lemma pureRSlot0BilinAt_frame_summand
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (W : SmoothCcTensor g 0 (m + 1))
    (B : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b)
    (i : Fin (Module.finrank ℝ E)) (y : M) (v : TangentSpace I y) :
    riemannOp (tensorCov (I := I) g 0 m) y (B i y) v
        ((covGradBundleEquiv (I := I) (M := M) 0 m y).symm (W.toSection y) (B i y)) =
      pureRSlot0BilinAt (I := I) (M := M) g m (fun b : M => W.toSection b) y v (B i y) (B i y) :=
        rfl

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private theorem pureRFrozenDirCLM_frame_independent
    (g : SmoothRiemannianMetric I M) (m : ℕ) (W : SmoothCcTensor g 0 (m + 1))
    {B C : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b} (y : M)
    (hB_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner y (B i y) (B j y) = if i = j then (1 : ℝ) else 0)
    (hC_orth : ∀ i j : Fin (Module.finrank ℝ E),
      g.inner y (C i y) (C j y) = if i = j then (1 : ℝ) else 0) :
    pureRFrozenDirCLM (I := I) (M := M) g m B (fun b : M => W.toSection b) y =
      pureRFrozenDirCLM (I := I) (M := M) g m C (fun b : M => W.toSection b) y := by
  classical
  haveI : T2Space (TangentSpace I y) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional ℝ (TangentSpace I y) := inferInstanceAs (FiniteDimensional ℝ E)
  refine ContinuousLinearMap.ext (fun v => ?_)
  refine ContinuousLinearMap.ext (fun D => ?_)
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro mtail
  haveI : T2Space (TensorRSSpace 0 m I y) :=
    inferInstanceAs (T2Space (Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace m I y))
  haveI : FiniteDimensional ℝ (TensorRSSpace 0 m I y) :=
    inferInstanceAs (FiniteDimensional ℝ (Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace m I y))
  set scalarize : TensorRSSpace 0 m I y →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun T => Tensor0SSpace.toModel
          ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace m I y from T) D) mtail
        map_add' := fun T T' => by
          change Tensor0SSpace.toModel ((T + T') D) mtail =
            Tensor0SSpace.toModel (T D) mtail + Tensor0SSpace.toModel (T' D) mtail
          rw [ContinuousLinearMap.add_apply, Tensor0SSpace.toModel_add,
            ContinuousMultilinearMap.add_apply]
        map_smul' := fun c T => by
          change Tensor0SSpace.toModel ((c • T) D) mtail = c • Tensor0SSpace.toModel (T D) mtail
          rw [ContinuousLinearMap.smul_apply, Tensor0SSpace.toModel_smul,
            ContinuousMultilinearMap.smul_apply] }
    with hscalarize_def
  have hscalarize_apply : ∀ T : TensorRSSpace 0 m I y,
      scalarize T = Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace m I y from T) D) mtail := by
    intro T
    rw [hscalarize_def, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk]
  set Hb : TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ :=
    LinearMap.toContinuousLinearMap
      { toFun := fun X => scalarize.comp
          (pureRSlot0BilinAt (I := I) (M := M) g m (fun b : M => W.toSection b) y v X)
        map_add' := fun X X' => by
          ext Y
          change scalarize (pureRSlot0BilinAt (I := I) (M := M) g m
              (fun b : M => W.toSection b) y v (X + X') Y) =
            scalarize (pureRSlot0BilinAt (I := I) (M := M) g m
                (fun b : M => W.toSection b) y v X Y) +
              scalarize (pureRSlot0BilinAt (I := I) (M := M) g m
                (fun b : M => W.toSection b) y v X' Y)
          rw [map_add (pureRSlot0BilinAt (I := I) (M := M) g m
            (fun b : M => W.toSection b) y v) X X',
            ContinuousLinearMap.add_apply, map_add scalarize]
        map_smul' := fun c X => by
          ext Y
          change scalarize (pureRSlot0BilinAt (I := I) (M := M) g m
              (fun b : M => W.toSection b) y v (c • X) Y) =
            c • scalarize (pureRSlot0BilinAt (I := I) (M := M) g m
              (fun b : M => W.toSection b) y v X Y)
          rw [map_smul (pureRSlot0BilinAt (I := I) (M := M) g m
            (fun b : M => W.toSection b) y v) c X,
            ContinuousLinearMap.smul_apply, map_smul scalarize] }
    with hHb_def
  have hHb_apply : ∀ X Y : TangentSpace I y,
      Hb X Y = Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace m I y from
          pureRSlot0BilinAt (I := I) (M := M) g m (fun b : M => W.toSection b) y v X Y) D)
            mtail := by
    intro X Y
    rw [hHb_def, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
      ContinuousLinearMap.comp_apply, hscalarize_apply]
  have hframe : ∀ (F : Fin (Module.finrank ℝ E) → Π b : M, TangentSpace I b),
      Tensor0SSpace.toModel
        ((show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace m I y from
          pureRFrozenDirCLM (I := I) (M := M) g m F (fun b : M => W.toSection b) y v) D) mtail =
      ∑ i : Fin (Module.finrank ℝ E), Hb (F i y) (F i y) := by
    intro F
    have hsum_apply :
        (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace m I y from
          pureRFrozenDirCLM (I := I) (M := M) g m F (fun b : M => W.toSection b) y v) D =
        ∑ i : Fin (Module.finrank ℝ E),
          (show Tensor0SSpace 0 I y →L[ℝ] Tensor0SSpace m I y from
            riemannOp (tensorCov (I := I) g 0 m) y (F i y) v
              ((covGradBundleEquiv (I := I) (M := M) 0 m y).symm (W.toSection y) (F i y))) D := by
      rw [pureRFrozenDirCLM_apply, ContinuousLinearMap.sum_apply]
    rw [hsum_apply, ← Tensor0SSpace.toModelL_apply, map_sum, ContinuousMultilinearMap.sum_apply]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Tensor0SSpace.toModelL_apply, hHb_apply (F i y) (F i y),
      pureRSlot0BilinAt_frame_summand (I := I) (M := M) g m W F i y v]
  rw [hframe B, hframe C]
  rw [orthonormal_basis_bilin_trace (I := I) (M := M) g (x := y) Hb (fun i => B i y) hB_orth,
    orthonormal_basis_bilin_trace (I := I) (M := M) g (x := y) Hb (fun i => C i y) hC_orth]

noncomputable def pureRGenuineEndoFib
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (W : SmoothCcTensor g 0 (m + 1)) (x : M) :
    TensorRSSpace 0 (m + 1) I x :=
  pureRFrozenEndoFib (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x) W x

omit [CompactSpace M] [I.Boundaryless] [SigmaCompactSpace M] in
private lemma pureRGenuineEndoFib_eq_frozen_on_nbhd
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (W : SmoothCcTensor g 0 (m + 1)) (x₀ : M) {y : M}
    (hy : y ∈ smoothOrthoFrameNbhd (I := I) (M := M) x₀) :
    pureRGenuineEndoFib (I := I) (M := M) g m W y =
      pureRFrozenEndoFib (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x₀) W y := by
  rw [pureRGenuineEndoFib, pureRFrozenEndoFib, pureRFrozenEndoFib]
  refine congrArg (covGradBundleEquiv (I := I) (M := M) 0 m y) ?_
  exact pureRFrozenDirCLM_frame_independent (I := I) (M := M) g m W y
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g y i j)
    (fun i j => smoothOrthoFrame_orthonormal (I := I) g x₀ hy i j)

omit [CompactSpace M] [I.Boundaryless] in
theorem pureRGenuineEndoFib_contMDiff
    (g : SmoothRiemannianMetric I M) (m : ℕ) (W : SmoothCcTensor g 0 (m + 1)) :
    ContMDiff I (I.prod 𝓘(ℝ, TensorRSModel 0 (m + 1) ℝ E)) ∞
      (fun x : M => TotalSpace.mk' (TensorRSModel 0 (m + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (m + 1) I z) x
        (pureRGenuineEndoFib (I := I) (M := M) g m W x)) := by
  classical
  intro x₀
  have h_fixed_at : ContMDiffAt I (I.prod 𝓘(ℝ, TensorRSModel 0 (m + 1) ℝ E)) ∞
      (fun y : M => TotalSpace.mk' (TensorRSModel 0 (m + 1) ℝ E)
        (E := fun z : M => TensorRSSpace 0 (m + 1) I z) y
        (pureRFrozenEndoFib (I := I) (M := M) g m (smoothOrthoFrame (I := I) g x₀) W y)) x₀ :=
    pureRFrozenEndoFib_contMDiff (I := I) (M := M) g m
      (fun i => smoothOrthoFrame_smooth (I := I) g x₀ i) W x₀
  refine h_fixed_at.congr_of_eventuallyEq ?_
  filter_upwards [smoothOrthoFrameNbhd_mem_nhds (I := I) (M := M) x₀] with y hy
  exact congrArg (TotalSpace.mk' (TensorRSModel 0 (m + 1) ℝ E)
    (E := fun z : M => TensorRSSpace 0 (m + 1) I z) y)
    (pureRGenuineEndoFib_eq_frozen_on_nbhd (I := I) (M := M) g m W x₀ hy)

private noncomputable def pureRGenuineEndoSucc
    (g : SmoothRiemannianMetric I M) (m : ℕ) (W : SmoothCcTensor g 0 (m + 1)) :
    SmoothCcTensor g 0 (m + 1) where
  toSection :=
    { toFun := fun x : M => pureRGenuineEndoFib (I := I) (M := M) g m W x
      contMDiff_toFun := pureRGenuineEndoFib_contMDiff (I := I) (M := M) g m W }
  hasCompactSupport := HasCompactSupport.of_compactSpace _

omit [I.Boundaryless] in
@[simp] private lemma pureRGenuineEndoSucc_toSection
    (g : SmoothRiemannianMetric I M) (m : ℕ) (W : SmoothCcTensor g 0 (m + 1)) (x : M) :
    (pureRGenuineEndoSucc (I := I) (M := M) g m W).toSection x =
      pureRGenuineEndoFib (I := I) (M := M) g m W x := rfl

noncomputable def pureRGenuineEndo0
    (g : SmoothRiemannianMetric I M) :
    ∀ (r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 r
  | 0 => fun _ => 0
  | (m + 1) => fun W => pureRGenuineEndoSucc (I := I) (M := M) g m W

noncomputable def pureRGenuineDiffOp
    (g : SmoothRiemannianMetric I M) :
    ∀ (p r : ℕ), SmoothCcTensor g 0 r → SmoothCcTensor g 0 (r + p)
  | 0, r => fun W => pureRGenuineEndo0 (I := I) (M := M) g r W
  | (p + 1), r => fun W =>
      covGrad (I := I) (M := M) g 0 (r + p)
          (pureRGenuineDiffOp g p r W) -
        castCcTensorRank g 0 (by omega : (r + 1) + p = r + (p + 1))
          (pureRGenuineDiffOp g p (r + 1) (covGrad (I := I) (M := M) g 0 r W))

theorem covGrad_pureRGenuineDiffOp_eq
    (g : SmoothRiemannianMetric I M) (p r : ℕ) (W : SmoothCcTensor g 0 r) :
    covGrad (I := I) (M := M) g 0 (r + p) (pureRGenuineDiffOp (I := I) (M := M) g p r W) =
      pureRGenuineDiffOp (I := I) (M := M) g (p + 1) r W +
        castCcTensorRank g 0 (by omega : (r + 1) + p = r + (p + 1))
          (pureRGenuineDiffOp (I := I) (M := M) g p (r + 1)
            (covGrad (I := I) (M := M) g 0 r W)) := by
  change _ = (covGrad (I := I) (M := M) g 0 (r + p)
      (pureRGenuineDiffOp (I := I) (M := M) g p r W) -
      castCcTensorRank g 0 (by omega : (r + 1) + p = r + (p + 1))
        (pureRGenuineDiffOp (I := I) (M := M) g p (r + 1)
          (covGrad (I := I) (M := M) g 0 r W))) + _
  rw [sub_add_cancel]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma pureRGenuineEndoFib_linear
    (g : SmoothRiemannianMetric I M) (m : ℕ) (c₁ c₂ : ℝ)
    (W₁ W₂ : SmoothCcTensor g 0 (m + 1)) (x : M) :
    pureRGenuineEndoFib (I := I) (M := M) g m
        (c₁ • W₁ + c₂ • W₂) x =
      c₁ • pureRGenuineEndoFib (I := I) (M := M) g m W₁ x +
        c₂ • pureRGenuineEndoFib (I := I) (M := M) g m W₂ x := by
  classical
  rw [pureRGenuineEndoFib, pureRGenuineEndoFib, pureRGenuineEndoFib]
  rw [pureRFrozenEndoFib, pureRFrozenEndoFib, pureRFrozenEndoFib]
  rw [← map_smul (covGradBundleEquiv (I := I) (M := M) 0 m x) c₁,
    ← map_smul (covGradBundleEquiv (I := I) (M := M) 0 m x) c₂,
    ← map_add (covGradBundleEquiv (I := I) (M := M) 0 m x)]
  refine congrArg (covGradBundleEquiv (I := I) (M := M) 0 m x) ?_
  refine ContinuousLinearMap.ext (fun v => ?_)
  rw [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply,
    pureRFrozenDirCLM_apply, pureRFrozenDirCLM_apply, pureRFrozenDirCLM_apply,
    Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have hval : (c₁ • W₁ + c₂ • W₂).toSection x =
      c₁ • W₁.toSection x + c₂ • W₂.toSection x := by
    rw [SmoothCcTensor.toSection_add, ContMDiffSection.coe_add, Pi.add_apply,
      SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply,
      SmoothCcTensor.toSection_smul, ContMDiffSection.coe_smul, Pi.smul_apply]
  rw [hval, map_add, map_smul, map_smul,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply, map_add, map_smul, map_smul]

omit [CompactSpace M] [I.Boundaryless] in
omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
private lemma pureRGenuineEndoFib_local
    (g : SmoothRiemannianMetric I M) (m : ℕ)
    (W₁ W₂ : SmoothCcTensor g 0 (m + 1)) (x : M)
    (hx : W₁.toSection x = W₂.toSection x) :
    pureRGenuineEndoFib (I := I) (M := M) g m W₁ x =
      pureRGenuineEndoFib (I := I) (M := M) g m W₂ x := by
  classical
  rw [pureRGenuineEndoFib, pureRGenuineEndoFib, pureRFrozenEndoFib, pureRFrozenEndoFib]
  refine congrArg (covGradBundleEquiv (I := I) (M := M) 0 m x) ?_
  refine ContinuousLinearMap.ext (fun v => ?_)
  rw [pureRFrozenDirCLM_apply, pureRFrozenDirCLM_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hx]

private theorem pureRGenuineDiffOp_isOrderZeroCurvFactor (g : SmoothRiemannianMetric I M) :
    IsPointwiseLinearLocalOperator (I := I) (M := M) g
      (pureRGenuineDiffOp (I := I) (M := M) g) where
  linear := by
    intro r c₁ c₂ W₁ W₂ x
    cases r with
    | zero =>
        have h0 : ∀ W : SmoothCcTensor g 0 0,
            (pureRGenuineDiffOp (I := I) (M := M) g 0 0 W).toSection x =
              (0 : TensorRSSpace 0 (0 + 0) I x) := by
          intro W
          change (pureRGenuineEndo0 (I := I) (M := M) g 0 W).toSection x =
            (0 : TensorRSSpace 0 (0 + 0) I x)
          rw [show pureRGenuineEndo0 (I := I) (M := M) g 0 W = 0 from rfl,
            SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero]
          rfl
        rw [h0, h0, h0]
        simp
    | succ m =>
        rw [show (pureRGenuineDiffOp (I := I) (M := M) g 0 (m + 1) (c₁ • W₁ + c₂ • W₂)).toSection x
          =
              pureRGenuineEndoFib (I := I) (M := M) g m (c₁ • W₁ + c₂ • W₂) x from rfl,
          show (pureRGenuineDiffOp (I := I) (M := M) g 0 (m + 1) W₁).toSection x =
              pureRGenuineEndoFib (I := I) (M := M) g m W₁ x from rfl,
          show (pureRGenuineDiffOp (I := I) (M := M) g 0 (m + 1) W₂).toSection x =
              pureRGenuineEndoFib (I := I) (M := M) g m W₂ x from rfl,
          pureRGenuineEndoFib_linear (I := I) (M := M) g m c₁ c₂ W₁ W₂ x]
  local' := by
    intro r W₁ W₂ x hx
    cases r with
    | zero =>
        have h0 : ∀ W : SmoothCcTensor g 0 0,
            (pureRGenuineDiffOp (I := I) (M := M) g 0 0 W).toSection x =
              (0 : TensorRSSpace 0 (0 + 0) I x) := by
          intro W
          change (pureRGenuineEndo0 (I := I) (M := M) g 0 W).toSection x =
            (0 : TensorRSSpace 0 (0 + 0) I x)
          rw [show pureRGenuineEndo0 (I := I) (M := M) g 0 W = 0 from rfl,
            SmoothCcTensor.toSection_zero, ContMDiffSection.coe_zero]
          rfl
        rw [h0, h0]
    | succ m =>
        rw [show (pureRGenuineDiffOp (I := I) (M := M) g 0 (m + 1) W₁).toSection x =
              pureRGenuineEndoFib (I := I) (M := M) g m W₁ x from rfl,
          show (pureRGenuineDiffOp (I := I) (M := M) g 0 (m + 1) W₂).toSection x =
          pureRGenuineEndoFib (I := I) (M := M) g m W₂ x from rfl,
          pureRGenuineEndoFib_local (I := I) (M := M) g m W₁ W₂ x hx]

end Curvature
end Geometry
end DifferentialGeometry

end
