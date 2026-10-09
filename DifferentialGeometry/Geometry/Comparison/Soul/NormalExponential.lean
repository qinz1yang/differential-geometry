import DifferentialGeometry.Geometry.Comparison.Soul.NormalBundle
import DifferentialGeometry.Geometry.Comparison.Soul.NormalSplitting
import DifferentialGeometry.Geometry.Comparison.Soul.NormalExpDerivative
import DifferentialGeometry.Geometry.Comparison.Soul.SmoothLocalInverse

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold BigOperators
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [ConnectedSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
  [T2Space (TangentBundle I M)]

variable (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
  {S : Set M}

local notation "FB" => (Fin (maxSliceDim I S) → ℝ)
local notation "FN" => (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
local notation "IB" => 𝓘(ℝ, FB)
local notation "IN" => ModelWithCorners.prod
  (modelWithCornersSelf ℝ (Fin (maxSliceDim I S) → ℝ))
  (modelWithCornersSelf ℝ (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ))

def normalExp (S : Set M) :
    TotalSpace (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ)
      (normalBundleFiber (I := I) g S) → M :=
  fun z => expMapIntrinsic (I := I) g hEnorm z.proj.1 z.snd.1

omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
@[simp] theorem normalExp_zero (p : S) :
    normalExp (I := I) g hEnorm S ⟨p, 0⟩ = p.1 :=
  expMapIntrinsic_zero (I := I) g hEnorm p.1

theorem normalExp_contMDiff (hconv : IsTotallyConvex (I := I) g S)
    (hB : relBoundary I S = ∅) :
    let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
    let _ := embeddedSliceChartedSpace hS
    let a := normalBundlePrebundle g hEnorm hconv hB
    let _ := a.totalSpaceTopology
    let _ := a.toFiberBundle
    let _ := a.toVectorBundle
    ContMDiff IN I ∞ (normalExp (I := I) g hEnorm S) := by
  let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
  let _ := embeddedSliceChartedSpace hS
  let a := normalBundlePrebundle g hEnorm hconv hB
  let _ := a.totalSpaceTopology
  let _ := a.toFiberBundle
  let _ := a.toVectorBundle
  exact (intrinsicExp_smooth (I := I) g hEnorm).comp
    (normalBundleInclusion_contMDiff g hEnorm hconv hB)

omit [ConnectedSpace M] [T2Space (TangentBundle I M)] in
private theorem tangentChartExp_fixed_base (p : M) (v : E) :
    tangentChartExp (I := I) g hEnorm p (extChartAt I p p, v) =
      extChartAt I p (expMapIntrinsic (I := I) g hEnorm p v) := by
  let z : TangentBundle I M := ⟨p, (0 : E)⟩
  let w : TangentBundle I M := ⟨p, v⟩
  have hw : w ∈ (extChartAt I.tangent z).source := by
    rw [extChartAt_source]
    exact (mem_chartAt_modelProd_zero_source_iff (I := I) p w).mpr (mem_chart_source H p)
  have hc : extChartAt I.tangent z w = (extChartAt I p p, v) := by
    rw [TangentBundle.extChartAt_tangent_zero_apply_chartFiber (I := I) p
      (p := w) (mem_chart_source H p)]
    exact Prod.ext rfl (chartFiberCoord_mk_self (I := I) p v)
  have hi : (extChartAt I.tangent z).symm (extChartAt I p p, v) = w := by
    rw [← hc]
    exact (extChartAt I.tangent z).left_inv hw
  rw [tangentChartExp_apply]
  change extChartAt I p
    (expMapIntrinsic (I := I) g hEnorm
      ((extChartAt I.tangent z).symm (extChartAt I p p, v)).proj
      ((extChartAt I.tangent z).symm (extChartAt I p p, v)).snd) = _
  rw [hi]

theorem normalExp_isLocalDiffeomorphAt_zero
    (hconv : IsTotallyConvex (I := I) g S) (hB : relBoundary I S = ∅) (p : S) :
    let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
    let _ := embeddedSliceChartedSpace hS
    let a := normalBundlePrebundle g hEnorm hconv hB
    let _ := a.totalSpaceTopology
    let _ := a.toFiberBundle
    let _ := a.toVectorBundle
    IsLocalDiffeomorphAt IN I ∞ (normalExp (I := I) g hEnorm S) ⟨p, 0⟩ := by
  classical
  let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  let a := normalBundlePrebundle g hEnorm hconv hB
  let _ := a.totalSpaceTopology
  let _ := a.toFiberBundle
  let _ := a.toVectorBundle
  let _ := normalBundle_isContMDiff g hEnorm hconv hB
  let z₀ : TotalSpace FN (normalBundleFiber (I := I) g S) := ⟨p, 0⟩
  let f := normalExp (I := I) g hEnorm S
  let cB := extChartAt IB p
  let cN := extChartAt IN z₀
  let e := trivializationAt FN (normalBundleFiber (I := I) g S) p
  let u₀ : FB := cB p
  let G : FB × FN → E := fun z => extChartAt I p.1 (f (cN.symm z))
  have hp : p ∈ e.baseSet := mem_baseSet_trivializationAt FN (normalBundleFiber g S) p
  have hzero : f z₀ = p.1 := normalExp_zero g hEnorm p
  have hq₀ : cB.symm u₀ = p := cB.left_inv (mem_extChartAt_source p)
  have hc₀ : cN z₀ = (u₀, 0) := by
    change extChartAt IN z₀ z₀ = _
    rw [FiberBundle.extChartAt]
    change (cB (e z₀).1, (e z₀).2) = _
    have he : e z₀ = (p, 0) := e.zeroSection ℝ hp
    rw [he]
  have hG : writtenInExtChartAt IN I z₀ f = G := by
    simp only [writtenInExtChartAt, hzero]
    rfl
  have hf : ContMDiff IN I ∞ f := normalExp_contMDiff g hEnorm hconv hB
  let D : (FB × FN) →L[ℝ] E := mfderiv IN I f z₀
  have hD : HasFDerivAt G D (u₀, 0) := by
    have hd := (hf.mdifferentiable (by simp) z₀).hasMFDerivAt.2
    change HasFDerivWithinAt (writtenInExtChartAt IN I z₀ f) D
      (range IN) (cN z₀) at hd
    rwa [ModelWithCorners.Boundaryless.range_eq_univ, hasFDerivWithinAt_univ, hG, hc₀] at hd
  let L : FB →L[ℝ] E := mfderiv IB I (Subtype.val : S → M) p
  let σ : FB → E := writtenInExtChartAt IB I p (Subtype.val : S → M)
  have hL : HasFDerivAt σ L u₀ := by
    have hd := ((embeddedSlice_inclusion_contMDiff hS p).mdifferentiableAt
      (by simp)).hasMFDerivAt.2
    change HasFDerivWithinAt σ L (range IB) u₀ at hd
    rwa [ModelWithCorners.Boundaryless.range_eq_univ, hasFDerivWithinAt_univ] at hd
  let n : FN ≃L[ℝ] normalBundleFiber (I := I) g S p :=
    (e.continuousLinearEquivAt ℝ p hp).symm
  let N : FN →L[ℝ] E := (normalSpace (I := I) g S p.1).subtypeL.comp n.toContinuousLinearMap
  obtain ⟨F, W, hF, hpW, heW, hframe⟩ :=
    exists_normalBundle_trivializationAt_frame g hEnorm hconv hB p
  have hformula {u : FB} (hu : (cB.symm u).1 ∈ W) (v : FN) :
      G (u, v) = extChartAt I p.1
        (expMapIntrinsic (I := I) g hEnorm (cB.symm u).1
          (∑ j, v j • gradFun (I := I) g (F j) (cB.symm u).1)) := by
    have hq : cB.symm u ∈ e.baseSet := by
      change cB.symm u ∈ (trivializationAt FN (normalBundleFiber g S) p).baseSet
      rwa [heW]
    have hsymm : cN.symm (u, v) = ⟨cB.symm u, e.symm (cB.symm u) v⟩ := by
      change (extChartAt IN z₀).symm (u, v) = _
      rw [FiberBundle.extChartAt]
      exact (e.mk_symm hq v).symm
    change extChartAt I p.1 (f (cN.symm (u, v))) = _
    rw [hsymm]
    change extChartAt I p.1 (expMapIntrinsic (I := I) g hEnorm (cB.symm u).1
      (e.symm (cB.symm u) v).1) = _
    rw [hframe (cB.symm u) hu v]
  have hW : ∀ᶠ u in 𝓝 u₀, (cB.symm u).1 ∈ W := by
    have hψ : ContinuousAt (fun u : FB => (cB.symm u).1) u₀ :=
      continuous_subtype_val.continuousAt.comp (continuousAt_extChartAt_symm p)
    exact hψ (by simpa only [hq₀] using hF.isOpen.mem_nhds hpW)
  have hbase : (fun u : FB => G (u, 0)) =ᶠ[𝓝 u₀] σ := by
    filter_upwards [hW] with u hu
    rw [hformula hu]
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero, expMapIntrinsic_zero]
    rfl
  have hfiber : (fun v : FN => G (u₀, v)) =ᶠ[𝓝 (0 : FN)]
      (fun v : FN => tangentChartExp (I := I) g hEnorm p.1 (extChartAt I p.1 p.1, N v)) := by
    filter_upwards with v
    have hu : (cB.symm u₀).1 ∈ W := by rwa [hq₀]
    rw [hformula hu v, hq₀]
    rw [← hframe p hpW v]
    exact (tangentChartExp_fixed_base g hEnorm p.1 (N v)).symm
  have hleft : D.comp ((ContinuousLinearMap.id ℝ FB).prod (0 : FB →L[ℝ] FN)) = L := by
    have hι : HasFDerivAt (fun u : FB => (u, (0 : FN)))
        ((ContinuousLinearMap.id ℝ FB).prod (0 : FB →L[ℝ] FN)) u₀ :=
      (hasFDerivAt_id u₀).prodMk (hasFDerivAt_const (0 : FN) u₀)
    exact ((hD.comp u₀ hι).congr_of_eventuallyEq hbase.symm).unique hL
  have hright : D.comp ((0 : FN →L[ℝ] FB).prod (ContinuousLinearMap.id ℝ FN)) = N := by
    have hι : HasFDerivAt (fun v : FN => (u₀, v))
        ((0 : FN →L[ℝ] FB).prod (ContinuousLinearMap.id ℝ FN)) (0 : FN) :=
      (hasFDerivAt_const u₀ (0 : FN)).prodMk (hasFDerivAt_id (0 : FN))
    have hlaunch : HasFDerivAt (fun v : FN => (extChartAt I p.1 p.1, N v))
        ((0 : FN →L[ℝ] E).prod N) (0 : FN) :=
      (hasFDerivAt_const (extChartAt I p.1 p.1) (0 : FN)).prodMk N.hasFDerivAt
    have he : HasFDerivAt (tangentChartExp (I := I) g hEnorm p.1)
        (ContinuousLinearMap.fst ℝ E E + ContinuousLinearMap.snd ℝ E E)
        (extChartAt I p.1 p.1, N 0) := by
      simpa only [map_zero] using tangentChartExp_hasFDerivAt_zero (I := I) g hEnorm p.1
    have hN : HasFDerivAt
        (fun v : FN => tangentChartExp (I := I) g hEnorm p.1 (extChartAt I p.1 p.1, N v))
        N (0 : FN) := by
      apply (he.comp (0 : FN) hlaunch).congr_fderiv
      apply ContinuousLinearMap.ext
      intro v
      change (0 : E) + N v = N v
      exact zero_add _
    exact ((hD.comp (0 : FN) hι).congr_of_eventuallyEq hfiber.symm).unique hN
  let A : (FB × FN) ≃L[ℝ] E :=
    ((ContinuousLinearEquiv.refl ℝ FB).prodCongr n).trans (normalSplitting g hS p)
  have hA (v : FB) (w : FN) : A (v, w) = L v + N w := by
    change normalSplitting g hS p (v, n w) = _
    exact normalSplitting_apply g hS p v (n w)
  have hDA : D = A.toContinuousLinearMap := by
    apply ContinuousLinearMap.ext
    rintro ⟨v, w⟩
    have hl : D (v, 0) = L v := congrArg (fun Q : FB →L[ℝ] E => Q v) hleft
    have hr : D (0, w) = N w := congrArg (fun Q : FN →L[ℝ] E => Q w) hright
    calc
      D (v, w) = D ((v, 0) + (0, w)) := by simp only [Prod.mk_add_mk, add_zero, zero_add]
      _ = D (v, 0) + D (0, w) := D.map_add _ _
      _ = L v + N w := by rw [hl, hr]
      _ = A (v, w) := (hA v w).symm
  change IsLocalDiffeomorphAt IN I ∞ f z₀
  apply isLocalDiffeomorphAt_of_contMDiffOn_of_isInvertible
    isOpen_univ (mem_univ z₀) hf.contMDiffOn
  rw [hG, hc₀]
  exact ⟨A, (hD.fderiv.trans hDA).symm⟩

end DifferentialGeometry.Geometry.Topology

end
