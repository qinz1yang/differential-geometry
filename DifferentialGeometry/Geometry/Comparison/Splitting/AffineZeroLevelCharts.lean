import DifferentialGeometry.Geometry.Comparison.Splitting.AffineFunctionNormalForm
import DifferentialGeometry.Geometry.Comparison.Soul.EmbeddedSlice
import Mathlib.Topology.Algebra.Module.FiniteDimension

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Topology

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}

section Local

variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

abbrev affineFunctionKernel (b : M → ℝ) (p : M) : Submodule ℝ E :=
  (mvfderiv (I := I) b p : E →L[ℝ] ℝ).ker

variable [FiniteDimensional ℝ E]


def affineFunctionKernelProjection
    (g : SmoothRiemannianMetric I M) {b : M → ℝ}
    (hunit : ∀ p, g.inner p (gradientFun (I := I) g b p) (gradientFun (I := I) g b p) = 1)
    (p : M) : E →L[ℝ] affineFunctionKernel (I := I) b p := by
  let L : E →L[ℝ] ℝ := mvfderiv (I := I) b p
  let w : E := gradientFun (I := I) g b p
  have hL : L w = 1 :=
    (inner_gradientFun (I := I) g b p (gradientFun (I := I) g b p)).symm.trans (hunit p)
  refine ((ContinuousLinearMap.id ℝ E) - L.smulRight w).codRestrict
    (affineFunctionKernel (I := I) b p) ?_
  intro v
  change L (v - L v • w) = 0
  rw [map_sub, map_smul, hL]
  simp only [smul_eq_mul, mul_one, sub_self]


theorem affineFunctionKernelProjection_apply
    (g : SmoothRiemannianMetric I M) {b : M → ℝ}
    (hunit : ∀ p, g.inner p (gradientFun (I := I) g b p) (gradientFun (I := I) g b p) = 1)
    (p : M) (v : E) :
    (affineFunctionKernelProjection (I := I) g hunit p v : E) =
      v - @SMul.smul ℝ E _ (mvfderiv (I := I) b p v) (gradientFun (I := I) g b p) := rfl


theorem affineFunctionKernelProjection_coe_eq
    (g : SmoothRiemannianMetric I M) {b : M → ℝ}
    (hunit : ∀ p, g.inner p (gradientFun (I := I) g b p) (gradientFun (I := I) g b p) = 1)
    (p : M) {v : E} (hv : v ∈ affineFunctionKernel (I := I) b p) :
    (affineFunctionKernelProjection (I := I) g hunit p v : E) = v := by
  rw [affineFunctionKernelProjection_apply]
  let w : E := gradientFun (I := I) g b p
  change v - (mvfderiv (I := I) b p v) • w = v
  have hz : (mvfderiv (I := I) b p : E →L[ℝ] ℝ) v = 0 := hv
  erw [hz]
  rw [zero_smul, sub_zero]

private theorem kernelProjection_subtype
    (g : SmoothRiemannianMetric I M) {b : M → ℝ}
    (hunit : ∀ p, g.inner p (gradientFun (I := I) g b p) (gradientFun (I := I) g b p) = 1)
    (p : M) (v : affineFunctionKernel (I := I) b p) :
    affineFunctionKernelProjection (I := I) g hunit p v = v :=
  Subtype.ext (affineFunctionKernelProjection_coe_eq (I := I) g hunit p v.property)

def affineFunctionKernelEquiv
    (g : SmoothRiemannianMetric I M) {b : M → ℝ}
    (hunit : ∀ p, g.inner p (gradientFun (I := I) g b p) (gradientFun (I := I) g b p) = 1)
    (p q : M) : affineFunctionKernel (I := I) b p ≃L[ℝ] affineFunctionKernel (I := I) b q :=
  ContinuousLinearEquiv.ofFinrankEq (Nat.add_right_cancel
    ((affineFunction_kernel_finrank (I := I) g b hunit p).trans
      (affineFunction_kernel_finrank (I := I) g b hunit q).symm))

end Local

variable [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

variable (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) (M := M) g)
  {b : M → ℝ} (hb : ContMDiff I 𝓘(ℝ, ℝ) ∞ b)
  (hunit : ∀ p, g.inner p (gradientFun (I := I) g b p) (gradientFun (I := I) g b p) = 1)
  (hH : ∀ p, hessFun (I := I) g b p = 0)

private def zeroLevelForward (p₀ p : {q : M // b q = 0}) (x : M) :
    affineFunctionKernel (I := I) b p₀.1 :=
  affineFunctionKernelEquiv (I := I) g hunit p.1 p₀.1
    (affineFunctionKernelProjection (I := I) g hunit p.1
      ((standardDiagonalInverseBranch (I := I) g hEnorm p.1).fixedBasePartialDiffeomorph.symm x))

private def zeroLevelInverse (p₀ p : {q : M // b q = 0})
    (z : affineFunctionKernel (I := I) b p₀.1) : M :=
  (standardDiagonalInverseBranch (I := I) g hEnorm p.1).fixedBasePartialDiffeomorph
    ((affineFunctionKernelEquiv (I := I) g hunit p.1 p₀.1).symm z : E)

include hb hH in
private theorem zeroLevelInverse_mem (p₀ p : {q : M // b q = 0})
    (z : affineFunctionKernel (I := I) b p₀.1) :
    b (zeroLevelInverse (I := I) g hEnorm hunit p₀ p z) = 0 := by
  change b (expMapIntrinsic (I := I) g hEnorm p.1 _) = 0
  rw [affineFunction_expMapIntrinsic (I := I) g hEnorm hb hH, p.property, zero_add]
  exact ((affineFunctionKernelEquiv (I := I) g hunit p.1 p₀.1).symm z).property

def affineZeroLevelChart (p₀ p : {q : M // b q = 0}) :
    OpenPartialHomeomorph {q : M // b q = 0} (affineFunctionKernel (I := I) b p₀.1) := by
  let Φ := (standardDiagonalInverseBranch (I := I) g hEnorm p.1).fixedBasePartialDiffeomorph
  let e := affineFunctionKernelEquiv (I := I) g hunit p.1 p₀.1
  let P := affineFunctionKernelProjection (I := I) g hunit p.1
  have hproj (q : {q : M // b q = 0}) (hq : q.1 ∈ Φ.target) :
      (P (Φ.symm q.1) : E) = Φ.symm q.1 :=
    affineFunctionKernelProjection_coe_eq (I := I) g hunit p.1
      ((affineFunction_normalCoordinate_level_iff (I := I) g hEnorm hb hH p.1 q.1 hq).mp
        (q.property.trans p.property.symm))
  refine
    { toFun := fun q => zeroLevelForward (I := I) g hEnorm hunit p₀ p q.1
      invFun := fun z => ⟨zeroLevelInverse (I := I) g hEnorm hunit p₀ p z,
        zeroLevelInverse_mem (I := I) g hEnorm hb hunit hH p₀ p z⟩
      source := {q | q.1 ∈ Φ.target}
      target := {z | (e.symm z : E) ∈ Φ.source}
      map_source' := ?_
      map_target' := ?_
      left_inv' := ?_
      right_inv' := ?_
      open_source := Φ.open_target.preimage continuous_subtype_val
      open_target := Φ.open_source.preimage (continuous_subtype_val.comp e.symm.continuous)
      continuousOn_toFun := ?_
      continuousOn_invFun := ?_ }
  · intro q hq
    change (e.symm (e (P (Φ.symm q.1))) : E) ∈ Φ.source
    rw [e.symm_apply_apply, hproj q hq]
    exact Φ.map_target hq
  · intro z hz
    exact Φ.map_source hz
  · intro q hq
    apply Subtype.ext
    change Φ (e.symm (e (P (Φ.symm q.1))) : E) = q.1
    rw [e.symm_apply_apply, hproj q hq]
    exact Φ.right_inv hq
  · intro z hz
    change e (P (Φ.symm (Φ (e.symm z : E)))) = z
    exact (congrArg (fun v : E => e (P v)) (Φ.left_inv hz)).trans
      ((congrArg e (kernelProjection_subtype (I := I) g hunit p.1 (e.symm z))).trans
        (e.apply_symm_apply z))
  · exact (e.continuous.comp P.continuous).comp_continuousOn
      (Φ.contMDiffOn_invFun.continuousOn.comp continuous_subtype_val.continuousOn
        (fun q hq => hq))
  · apply _root_.Topology.IsInducing.subtypeVal.continuousOn_iff.mpr
    exact Φ.contMDiffOn_toFun.continuousOn.comp
      (continuous_subtype_val.comp e.symm.continuous).continuousOn (fun z hz => hz)


theorem mem_affineZeroLevelChart_source (p₀ p : {q : M // b q = 0}) :
    p ∈ (affineZeroLevelChart (I := I) g hEnorm hb hunit hH p₀ p).source :=
  (standardDiagonalInverseBranch (I := I) g hEnorm p.1).fixedBasePartialDiffeomorph_center_mem_target

private theorem zeroLevelForward_contMDiffOn (p₀ p : {q : M // b q = 0}) :
    ContMDiffOn I 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) ∞
      (zeroLevelForward (I := I) g hEnorm hunit p₀ p)
      (standardDiagonalInverseBranch (I := I) g hEnorm p.1).fixedBasePartialDiffeomorph.target :=
  ((affineFunctionKernelEquiv (I := I) g hunit p.1 p₀.1).toContinuousLinearMap.contMDiff.comp
    (affineFunctionKernelProjection (I := I) g hunit p.1).contMDiff).comp_contMDiffOn
    (standardDiagonalInverseBranch (I := I) g hEnorm p.1).fixedBasePartialDiffeomorph.contMDiffOn_invFun

private theorem zeroLevelInverse_contMDiffOn (p₀ p : {q : M // b q = 0}) :
    ContMDiffOn 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) I ∞
      (zeroLevelInverse (I := I) g hEnorm hunit p₀ p)
      (affineZeroLevelChart (I := I) g hEnorm hb hunit hH p₀ p).target :=
  (standardDiagonalInverseBranch (I := I) g hEnorm p.1).fixedBasePartialDiffeomorph.contMDiffOn_toFun.comp
    (((affineFunctionKernel (I := I) b p.1).subtypeL.contMDiff.comp
      (affineFunctionKernelEquiv (I := I) g hunit p.1 p₀.1).symm.toContinuousLinearMap.contMDiff).contMDiffOn)
    (fun _ hz => hz)

theorem affineZeroLevelChart_transition_contDiffOn (p₀ p q : {q : M // b q = 0}) :
    ContDiffOn ℝ ∞
      ((affineZeroLevelChart (I := I) g hEnorm hb hunit hH p₀ p).symm ≫ₕ
        affineZeroLevelChart (I := I) g hEnorm hb hunit hH p₀ q)
      ((affineZeroLevelChart (I := I) g hEnorm hb hunit hH p₀ p).symm ≫ₕ
        affineZeroLevelChart (I := I) g hEnorm hb hunit hH p₀ q).source := by
  let c := affineZeroLevelChart (I := I) g hEnorm hb hunit hH p₀ p
  let d := affineZeroLevelChart (I := I) g hEnorm hb hunit hH p₀ q
  intro z hz
  have hzt : z ∈ c.target := hz.1
  have hxs : (c.symm z).1 ∈ (standardDiagonalInverseBranch (I := I) g hEnorm q.1).fixedBasePartialDiffeomorph.target := hz.2
  have hinv := (zeroLevelInverse_contMDiffOn (I := I) g hEnorm hb hunit hH p₀ p)
    |>.contMDiffAt (c.open_target.mem_nhds hzt)
  have hforward := (zeroLevelForward_contMDiffOn (I := I) g hEnorm hunit p₀ q)
    |>.contMDiffAt ((standardDiagonalInverseBranch (I := I) g hEnorm q.1).fixedBasePartialDiffeomorph.open_target.mem_nhds hxs)
  have hcomp := hforward.comp z hinv
  exact (contMDiffAt_iff_contDiffAt.mp hcomp).contDiffWithinAt

@[reducible] def affineZeroLevelChartedSpace (p₀ : {q : M // b q = 0}) :
    ChartedSpace (affineFunctionKernel (I := I) b p₀.1) {q : M // b q = 0} where
  atlas := Set.range (affineZeroLevelChart (I := I) g hEnorm hb hunit hH p₀)
  chartAt := affineZeroLevelChart (I := I) g hEnorm hb hunit hH p₀
  mem_chart_source := mem_affineZeroLevelChart_source (I := I) g hEnorm hb hunit hH p₀
  chart_mem_atlas p := ⟨p, rfl⟩

theorem affineZeroLevel_isManifold (p₀ : {q : M // b q = 0}) :
    let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
    IsManifold 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) ∞ {q : M // b q = 0} := by
  let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
  refine { toHasGroupoid := ?_ }
  refine hasGroupoid_of_pregroupoid
    (contDiffPregroupoid ∞ 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1)) ?_
  intro e e' he he'
  rcases he with ⟨p, rfl⟩
  rcases he' with ⟨q, rfl⟩
  change ContDiffOn ℝ ∞
    (𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) ∘
      ((affineZeroLevelChart (I := I) g hEnorm hb hunit hH p₀ p).symm ≫ₕ
        affineZeroLevelChart (I := I) g hEnorm hb hunit hH p₀ q) ∘
      𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1).symm)
    (𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1).symm ⁻¹'
      ((affineZeroLevelChart (I := I) g hEnorm hb hunit hH p₀ p).symm ≫ₕ
        affineZeroLevelChart (I := I) g hEnorm hb hunit hH p₀ q).source ∩
      Set.range 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1))
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
    Function.comp_id, Function.id_comp, preimage_id_eq, range_id, inter_univ]
  exact affineZeroLevelChart_transition_contDiffOn (I := I) g hEnorm hb hunit hH p₀ p q

theorem affineZeroLevel_inclusion_contMDiff (p₀ : {q : M // b q = 0}) :
    let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
    ContMDiff 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) I ∞
      (Subtype.val : {q : M // b q = 0} → M) := by
  let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
  change ContMDiff 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) I ∞
    (Subtype.val : {q : M // b q = 0} → M)
  intro p
  let c := affineZeroLevelChart (I := I) g hEnorm hb hunit hH p₀ p
  have hp : p ∈ c.source := mem_affineZeroLevelChart_source (I := I) g hEnorm hb hunit hH p₀ p
  have hsm := (zeroLevelInverse_contMDiffOn (I := I) g hEnorm hb hunit hH p₀ p)
    |>.contMDiffAt (c.open_target.mem_nhds (c.map_source hp))
  rw [contMDiffAt_iff_source, modelWithCornersSelf_coe, range_id]
  exact hsm.contMDiffWithinAt

theorem affineZeroLevel_corestrict_contMDiff
    (p₀ : {q : M // b q = 0})
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
    {X : Type*} [TopologicalSpace X] [ChartedSpace G X]
    (f : X → M) (hf : ContMDiff J I ∞ f) (hfzero : ∀ x, b (f x) = 0) :
    let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
    ContMDiff J 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) ∞
      (fun x => (⟨f x, hfzero x⟩ : {q : M // b q = 0})) := by
  let _ := affineZeroLevelChartedSpace (I := I) g hEnorm hb hunit hH p₀
  change ContMDiff J 𝓘(ℝ, affineFunctionKernel (I := I) b p₀.1) ∞
    (fun x => (⟨f x, hfzero x⟩ : {q : M // b q = 0}))
  intro x
  let p : {q : M // b q = 0} := ⟨f x, hfzero x⟩
  have hsm := (zeroLevelForward_contMDiffOn (I := I) g hEnorm hunit p₀ p)
    |>.contMDiffAt ((standardDiagonalInverseBranch (I := I) g hEnorm p.1).fixedBasePartialDiffeomorph.open_target.mem_nhds
      (standardDiagonalInverseBranch (I := I) g hEnorm p.1).fixedBasePartialDiffeomorph_center_mem_target)
  rw [contMDiffAt_iff_target]
  refine ⟨(hf.continuous.subtype_mk hfzero).continuousAt, ?_⟩
  exact hsm.comp x (hf x)

include g hEnorm hb hunit hH in
theorem affineZeroLevel_isEmbeddedSlice :
    DifferentialGeometry.Geometry.IsEmbeddedSlice I (Module.finrank ℝ E - 1)
      {p : M | b p = 0} := by
  intro p hp
  let B := standardDiagonalInverseBranch (I := I) g hEnorm p
  let K := affineFunctionKernel (I := I) b p
  refine ⟨B.fixedBasePartialDiffeomorph.symm, K.toAffineSubspace, inferInstance, B.fixedBasePartialDiffeomorph_center_mem_target, ?_, ?_⟩
  · rw [Submodule.toAffineSubspace_direction]
    have h := affineFunction_kernel_finrank (I := I) g b hunit p
    change Module.finrank ℝ K + 1 = Module.finrank ℝ E at h
    omega
  · intro q hq
    change B.fixedBasePartialDiffeomorph.symm q ∈ K ↔ b q = 0
    have h := affineFunction_normalCoordinate_level_iff (I := I) g hEnorm hb hH p q hq
    have hp0 : b p = 0 := hp
    simpa only [hp0] using! h.symm

end DifferentialGeometry.Geometry.Topology

end
