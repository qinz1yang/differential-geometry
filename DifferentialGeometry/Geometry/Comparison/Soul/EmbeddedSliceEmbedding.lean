import DifferentialGeometry.Geometry.Comparison.Soul.NormalExponential
import Mathlib.Geometry.Manifold.SmoothEmbedding

set_option autoImplicit false
noncomputable section

open Bundle Filter Function Manifold Set
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Topology

section ModelCharts

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private def extendedChartDiffeomorph (p : M) :
    PartialDiffeomorph I 𝓘(ℝ, E) M E ∞ where
  toPartialEquiv := extChartAt I p
  open_source := isOpen_extChartAt_source p
  open_target := isOpen_extChartAt_target p
  contMDiffOn_toFun := by
    simpa only [extChartAt_source] using contMDiffOn_extChartAt (I := I) (x := p)
  contMDiffOn_invFun := contMDiffOn_extChartAt_symm p

private def boundarylessModelInverse : PartialDiffeomorph 𝓘(ℝ, E) I E H ∞ where
  toPartialEquiv := I.toHomeomorph.symm.toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := by
    change ContMDiffOn 𝓘(ℝ, E) I ∞ I.symm univ
    simpa only [I.range_eq_univ] using I.contMDiffOn_symm (n := ∞)
  contMDiffOn_invFun := I.contMDiff.contMDiffOn

end ModelCharts

section NormalBundle

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
local notation "IB" => 𝓘(ℝ, Fin (maxSliceDim I S) → ℝ)
local notation "IN" => ModelWithCorners.prod
  (modelWithCornersSelf ℝ (Fin (maxSliceDim I S) → ℝ))
  (modelWithCornersSelf ℝ (Fin (Module.finrank ℝ E - maxSliceDim I S) → ℝ))
local notation "NB" => TotalSpace FN (normalBundleFiber (I := I) g S)

theorem embeddedSlice_inclusion_isSmoothEmbedding
    (hconv : IsTotallyConvex (I := I) g S) (hB : relBoundary I S = ∅) :
    let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
    let _ := embeddedSliceChartedSpace hS
    IsSmoothEmbedding IB I ∞ (Subtype.val : S → M) := by
  classical
  let hS := isEmbeddedSlice_of_relBoundary_eq_empty hEnorm hconv hB
  let _ := embeddedSliceChartedSpace hS
  let _ := embeddedSlice_isManifold hS
  let a := normalBundlePrebundle g hEnorm hconv hB
  let _ := a.totalSpaceTopology
  let _ := a.toFiberBundle
  let _ := a.toVectorBundle
  let _ := normalBundle_isContMDiff g hEnorm hconv hB
  change IsSmoothEmbedding IB I ∞ (Subtype.val : S → M)
  have himm : IsImmersionOfComplement FN IB I ∞ (Subtype.val : S → M) := by
    intro p
    let Z : S → NB := fun q => ⟨q, 0⟩
    let z₀ : NB := Z p
    have hZsmooth : ContMDiff IB IN ∞ Z :=
      Bundle.contMDiff_zeroSection ℝ (F := FN) (normalBundleFiber g S)
    have hZ : Continuous Z := hZsmooth.continuous
    obtain ⟨Φ, hpΦ, hΦ⟩ := normalExp_isLocalDiffeomorphAt_zero g hEnorm hconv hB p
    let α₀ := chartAt FB p
    let β : PartialDiffeomorph IN 𝓘(ℝ, FB × FN) NB (FB × FN) ∞ :=
      extendedChartDiffeomorph (I := IN) z₀
    let e := trivializationAt FN (normalBundleFiber g S) p
    have hpβ : Z p ∈ β.source := mem_extChartAt_source z₀
    have hpe : p ∈ e.baseSet := mem_baseSet_trivializationAt FN (normalBundleFiber g S) p
    have hdim : Module.finrank ℝ (FB × FN) = Module.finrank ℝ E := by
      have hd := hS.dim_le (show S.Nonempty from ⟨p.1, p.2⟩)
      simp only [Module.finrank_prod, Module.finrank_pi, Fintype.card_fin]
      omega
    let L : (FB × FN) ≃L[ℝ] E := ContinuousLinearEquiv.ofFinrankEq hdim
    let χ := Φ.symm.trans β
    let κ := χ.trans L.toDiffeomorph.toPartialDiffeomorph
    let ψD := κ.trans (boundarylessModelInverse (I := I))
    let ψ : OpenPartialHomeomorph M H := ψD.toOpenPartialHomeomorph
    let V : Set S := ((Z ⁻¹' Φ.source) ∩ (Z ⁻¹' β.source)) ∩ e.baseSet
    have hV : IsOpen V :=
      ((Φ.open_source.preimage hZ).inter (β.open_source.preimage hZ)).inter e.open_baseSet
    have hpV : p ∈ V := ⟨⟨hpΦ, hpβ⟩, hpe⟩
    let α : OpenPartialHomeomorph S FB := α₀.restr V
    have hαsource : α.source = α₀.source ∩ V := α₀.restr_source' V hV
    have hpα : p ∈ α.source := by
      rw [hαsource]
      exact ⟨mem_chart_source FB p, hpV⟩
    have hαmax : α ∈ IsManifold.maximalAtlas IB ∞ S :=
      restr_mem_maximalAtlas (contDiffGroupoid ∞ IB)
        (IsManifold.chart_mem_maximalAtlas p) hV
    have hψmax : ψ ∈ IsManifold.maximalAtlas I ∞ M :=
      ψ.mem_maximalAtlas_of_contMDiffOn ψD.contMDiffOn_toFun ψD.contMDiffOn_invFun
    have hΦzero (q : S) (hq : Z q ∈ Φ.source) : Φ (Z q) = q.1 :=
      (hΦ hq).symm.trans (normalExp_zero g hEnorm q)
    have hΦinv (q : S) (hq : Z q ∈ Φ.source) : Φ.symm q.1 = Z q := by
      calc
        Φ.symm q.1 = Φ.symm (Φ (Z q)) := congrArg (fun y : M => Φ.symm y) (hΦzero q hq).symm
        _ = Z q := Φ.toPartialEquiv.left_inv hq
    have hβzero (q : S) (hq : q ∈ e.baseSet) : β (Z q) = (α₀ q, 0) := by
      change extChartAt IN z₀ (Z q) = (α₀ q, 0)
      rw [FiberBundle.extChartAt]
      change (extChartAt IB p (e (Z q)).1, (e (Z q)).2) = (α₀ q, 0)
      rw [show e (Z q) = (q, 0) from e.zeroSection ℝ hq]
      rfl
    have hψsource (q : S) (hq : q ∈ V) : q.1 ∈ ψ.source := by
      change ((q.1 ∈ Φ.target ∧ Φ.symm q.1 ∈ β.source) ∧ True) ∧ True
      refine ⟨⟨⟨?_, ?_⟩, trivial⟩, trivial⟩
      · rw [← hΦzero q hq.1.1]
        exact Φ.map_source hq.1.1
      · rw [hΦinv q hq.1.1]
        exact hq.1.2
    have hψzero (q : S) (hq : q ∈ V) : (ψ.extend I) q.1 = L (α₀ q, 0) := by
      change I (I.symm (L (β (Φ.symm q.1)))) = L (α₀ q, 0)
      rw [I.right_inv (by rw [I.range_eq_univ]; trivial), hΦinv q hq.1.1, hβzero q hq.2]
    refine IsImmersionAtOfComplement.mk_of_charts (f := (Subtype.val : S → M)) L α ψ
      hpα (hψsource p hpV) hαmax hψmax ?_ ?_
    · intro q hq
      apply hψsource q
      rw [hαsource] at hq
      exact hq.2
    · intro u hu
      have huα : u ∈ α.target := by
        simpa only [OpenPartialHomeomorph.extend_target, modelWithCornersSelf_coe_symm,
          preimage_id_eq, modelWithCornersSelf_coe, range_id, inter_univ, id_eq] using hu
      let q : S := α.symm u
      have hqa : q ∈ α.source := α.map_target huα
      have hqV : q ∈ V := by
        rw [hαsource] at hqa
        exact hqa.2
      have hαq : α₀ q = u := α.right_inv huα
      change (ψ.extend I) (((α.extend IB).symm u).1) = L (u, 0)
      have hsymm : (α.extend IB).symm u = q := rfl
      rw [hsymm, hψzero q hqV, hαq]
  exact ⟨himm.isImmersion, _root_.Topology.IsEmbedding.subtypeVal⟩

end NormalBundle

end DifferentialGeometry.Geometry.Topology
