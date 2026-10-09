import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.EdgeCircleBinderECM

/-!
# E4c: the fibre-preserving product `D² × S¹` of a circle component of the edge bundle

Draft 74, package E4c (`edge_circle_product74`, disposition D74-12). For `P : EdgeBundle W` and a
circle component `C` of its base with smooth parametrization `g` (`range g = C`),
`edge_circle_product_ECM` is the six clauses `circleTriv_smooth / mfderiv / injective / range /
proj / disk / rim` of `EdgeComponentModels` for ONE circle component: a smooth injective map
`T : D² × S¹ → W` with bijective differential whose image is the whole component, which projects to
`g z` on the slice over `z`, whose slices are the whole disks and whose slice rims are the whole
rims. Nothing beyond the fields of `EdgeBundle` is assumed: the disk bundle is oriented because `W`
is (`W.orientation` pulled back to the sublevel manifold), the flow, the return map and its
isotopy are the tree's D2S1 kernels (`EdgeCircleProductKernelECM.lean`), the sublevel manifold and
the boundary curves come from `EdgeCircleSublevelECM.lean` / `EdgeCircleBinderECM.lean`.

`EdgeComponentModels.ofCircleProducts_ECM` is the consumer: all other fields of the registry
(interval components, labels, endpoints) are arguments, and the circle fields `circleTriv_*` are
produced by `edge_circle_product_ECM` (a structure instance on an abstract `P`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

local instance diskChartsProduct_ECM : ChartedSpace (EuclideanHalfSpace 2) (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellChartedSpaceSucc 1

local instance diskSmoothProduct_ECM : IsManifold (𝓡∂ 2) ∞ (ClosedCell 2) :=
  DifferentialGeometry.Topology.Handle.closedCellIsManifold 1

/-- **E4c: the fibre-preserving product of an edge circle component.** -/
theorem edge_circle_product_ECM {W : CompactCarrier.{u}} (P : EdgeBundle W)
    (C : P.EdgeBaseComponent) (g : Circle → P.Base)
    (hg : IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ g) (hgC : range g = C.1) :
    ∃ T : ClosedCell 2 × Circle → W.Carrier,
      ContMDiff ((𝓡∂ 2).prod (𝓡 1)) W.model ∞ T ∧
      (∀ p, Bijective (mfderiv ((𝓡∂ 2).prod (𝓡 1)) W.model T p)) ∧
      Injective T ∧ range T = P.wholeComponent C ∧
      (∀ w z, ∃ hx : T (w, z) ∈ P.source, P.proj ⟨T (w, z), hx⟩ = g z) ∧
      (∀ z, range (fun w => T (w, z)) = P.disk (g z)) ∧
      (∀ z, (fun w => T (w, z)) '' diskRim = P.rim (g z)) := by
  classical
  have : ConnectedSpace (EdgeBundle.TotalC_ECM hg) := EdgeBundle.connectedSpace_totalC_ECM hg
  let oM : ManifoldOrientation (𝓡∂ 3) (EdgeBundle.TotalC_ECM hg) 3 :=
    DifferentialGeometry.Topology.Manifold.manifoldOrientationPullback (𝓡∂ 3) W.model
      finrank_euclideanSpace_fin (Subtype.val : EdgeBundle.TotalC_ECM hg → W.Carrier)
      P.contMDiff_total_val_ECM P.mfderiv_total_val_bijective_ECM W.orientation
  obtain ⟨φ₁, hφ₁e, hφ₁r⟩ := P.fibre_disk (g 1)
  obtain ⟨T, hT⟩ := edge_circle_product_kernel_ECM oM
    (Subtype.val : EdgeBundle.TotalC_ECM hg → W.Carrier) P.contMDiff_total_val_ECM
    (EdgeBundle.totalProj_ECM hg) (EdgeBundle.contMDiff_totalProj_ECM hg)
    (EdgeBundle.surjective_mfderiv_totalProj_ECM hg)
    (fun x hx => EdgeBundle.exists_boundaryCurve_ECM hg x hx)
    (EdgeBundle.liftDisk_ECM hg hφ₁r)
    (EdgeBundle.contMDiff_liftDisk_ECM hg hφ₁r hφ₁e.contMDiff) hφ₁e
    (EdgeBundle.range_liftDisk_ECM hg hφ₁r)
  refine ⟨fun q => (T q).1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact P.contMDiff_total_val_ECM.comp T.contMDiff
  · intro q
    have hd1 : MDifferentiableAt (𝓡∂ 3) W.model
        (Subtype.val : EdgeBundle.TotalC_ECM hg → W.Carrier) (T q) :=
      (P.contMDiff_total_val_ECM (T q)).mdifferentiableAt (by simp)
    have hd2 : MDifferentiableAt ((𝓡∂ 2).prod (𝓡 1)) (𝓡∂ 3) T q :=
      (T.contMDiff q).mdifferentiableAt (by simp)
    have hc := mfderiv_comp q hd1 hd2
    change Bijective (mfderiv ((𝓡∂ 2).prod (𝓡 1)) W.model
      ((Subtype.val : EdgeBundle.TotalC_ECM hg → W.Carrier) ∘ T) q)
    rw [hc, ContinuousLinearMap.coe_comp]
    exact (P.mfderiv_total_val_bijective_ECM (T q)).comp (mfderiv_diffeo_bijective_ECM T q)
  · exact Subtype.val_injective.comp T.injective
  · ext x
    constructor
    · rintro ⟨q, rfl⟩
      obtain ⟨hov, hle⟩ := EdgeBundle.sublevelFn_le_iff_ECM.mp (T q).2
      obtain ⟨hs, hb⟩ := EdgeBundle.mem_overOpen_ECM.mp hov
      refine ⟨⟨(T q).1, hs⟩, ⟨?_, ?_⟩, rfl⟩
      · rw [← hgC]
        exact hb
      · exact (P.heightExt_apply_ECM ⟨(T q).1, hs⟩).symm.trans_le hle
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      have hyB : P.proj y ∈ range g := hgC ▸ hy1
      let x' : EdgeBundle.TotalC_ECM hg :=
        ⟨y.1, EdgeBundle.sublevelFn_le_iff_ECM.mpr
          ⟨EdgeBundle.mem_overOpen_ECM.mpr ⟨y.2, hyB⟩,
            (P.heightExt_apply_ECM y).trans_le hy2⟩⟩
      obtain ⟨q, hq⟩ := T.surjective x'
      change T q = x' at hq
      exact ⟨q, congrArg Subtype.val hq⟩
  · intro w z
    exact ⟨P.total_mem_source_ECM (T (w, z)),
      EdgeBundle.totalProj_eq_iff_ECM.mp (hT (w, z))⟩
  · intro z
    obtain ⟨φ, hφe, hφr⟩ := P.fibre_disk (g z)
    have h1 : range (fun w : ClosedCell 2 => (T (w, z)).1) =
        Subtype.val '' range (fun w : ClosedCell 2 => T (w, z)) := by
      rw [← range_comp]
      rfl
    rw [h1, range_slice_edge_circle_product_ECM T hT z, ← EdgeBundle.range_liftDisk_ECM hg hφr,
      ← range_comp]
    exact hφr
  · intro z
    ext x
    constructor
    · rintro ⟨w, hw, rfl⟩
      have hb : (𝓡∂ 3).IsBoundaryPoint (T (w, z)) :=
        (isBoundaryPoint_edge_circle_product_ECM T z).mpr hw
      have hh := (P.total_isBoundaryPoint_iff_ECM.mp hb)
      refine ⟨⟨(T (w, z)).1, P.total_mem_source_ECM (T (w, z))⟩, ⟨?_, ?_⟩, rfl⟩
      · exact EdgeBundle.totalProj_eq_iff_ECM.mp (hT (w, z))
      · exact (P.heightExt_apply_ECM ⟨(T (w, z)).1, P.total_mem_source_ECM (T (w, z))⟩).symm.trans
          hh
    · rintro ⟨y, ⟨hy1, hy2⟩, rfl⟩
      have hyB : P.proj y ∈ range g := ⟨z, hy1.symm⟩
      let x' : EdgeBundle.TotalC_ECM hg :=
        ⟨y.1, EdgeBundle.sublevelFn_le_iff_ECM.mpr
          ⟨EdgeBundle.mem_overOpen_ECM.mpr ⟨y.2, hyB⟩,
            (P.heightExt_apply_ECM y).trans_le hy2.le⟩⟩
      obtain ⟨q, hq⟩ := T.surjective x'
      change T q = x' at hq
      have hpq : q.2 = z := by
        rw [← hT q, hq]
        exact EdgeBundle.totalProj_eq_iff_ECM.mpr hy1
      have hqz : q = (q.1, z) := Prod.ext rfl hpq
      refine ⟨q.1, ?_, ?_⟩
      · rw [← isBoundaryPoint_edge_circle_product_ECM (x := q.1) T z, ← hqz, hq]
        exact P.total_isBoundaryPoint_iff_ECM.mpr
          ((P.heightExt_apply_ECM y).trans hy2)
      · rw [hqz] at hq
        exact congrArg Subtype.val hq

/-- **Consumer: the edge component registry with the circle products produced by E4c.** All fields
of `EdgeComponentModels` other than the `circleTriv_*` clauses (counts, labels, base
parametrizations, endpoints, interval handles) are arguments; the circle clauses are
`edge_circle_product_ECM` at each circle component. -/
def EdgeComponentModels.ofCircleProducts_ECM {W : CompactCarrier.{u}} (P : EdgeBundle W)
    (intervalCount circleCount : ℕ)
    (componentEquiv : (Fin intervalCount ⊕ Fin circleCount) ≃ P.EdgeBaseComponent)
    (intervalBase : Fin intervalCount → Icc (0 : ℝ) 1 → P.Base)
    (intervalBase_embedding : ∀ i, IsSmoothEmbedding (𝓡∂ 1) (𝓡 1) ∞ (intervalBase i))
    (intervalBase_range : ∀ i, range (intervalBase i) = (componentEquiv (.inl i)).1)
    (circleBase : Fin circleCount → Circle → P.Base)
    (circleBase_embedding : ∀ j, IsSmoothEmbedding (𝓡 1) (𝓡 1) ∞ (circleBase j))
    (circleBase_range : ∀ j, range (circleBase j) = (componentEquiv (.inr j)).1)
    (endpointEquiv : (Fin intervalCount × Bool) ≃ P.EdgeEnd)
    (endpointEquiv_apply : ∀ i b, (endpointEquiv (i, b)).1 = intervalBase i (iccEnd b))
    (intervalTriv : Fin intervalCount → EdgeHandle W)
    (intervalTriv_range : ∀ i,
      range (intervalTriv i).map = P.wholeComponent (componentEquiv (.inl i)))
    (intervalTriv_proj : ∀ i w t, ∃ hx : (intervalTriv i).map (w, t) ∈ P.source,
      P.proj ⟨(intervalTriv i).map (w, t), hx⟩ = intervalBase i t)
    (intervalTriv_disk : ∀ i t,
      range (fun w => (intervalTriv i).map (w, t)) = P.disk (intervalBase i t))
    (intervalTriv_rim : ∀ i t,
      (fun w => (intervalTriv i).map (w, t)) '' diskRim = P.rim (intervalBase i t)) :
    EdgeComponentModels P where
  intervalCount := intervalCount
  circleCount := circleCount
  componentEquiv := componentEquiv
  intervalBase := intervalBase
  intervalBase_embedding := intervalBase_embedding
  intervalBase_range := intervalBase_range
  circleBase := circleBase
  circleBase_embedding := circleBase_embedding
  circleBase_range := circleBase_range
  endpointEquiv := endpointEquiv
  endpointEquiv_apply := endpointEquiv_apply
  intervalTriv := intervalTriv
  intervalTriv_range := intervalTriv_range
  intervalTriv_proj := intervalTriv_proj
  intervalTriv_disk := intervalTriv_disk
  intervalTriv_rim := intervalTriv_rim
  circleTriv j := Classical.choose (edge_circle_product_ECM P (componentEquiv (.inr j))
    (circleBase j) (circleBase_embedding j) (circleBase_range j))
  circleTriv_smooth j := (Classical.choose_spec (edge_circle_product_ECM P
    (componentEquiv (.inr j)) (circleBase j) (circleBase_embedding j) (circleBase_range j))).1
  circleTriv_mfderiv j := (Classical.choose_spec (edge_circle_product_ECM P
    (componentEquiv (.inr j)) (circleBase j) (circleBase_embedding j) (circleBase_range j))).2.1
  circleTriv_injective j := (Classical.choose_spec (edge_circle_product_ECM P
    (componentEquiv (.inr j)) (circleBase j) (circleBase_embedding j) (circleBase_range j))).2.2.1
  circleTriv_range j := (Classical.choose_spec (edge_circle_product_ECM P
    (componentEquiv (.inr j)) (circleBase j) (circleBase_embedding j)
    (circleBase_range j))).2.2.2.1
  circleTriv_proj j := (Classical.choose_spec (edge_circle_product_ECM P
    (componentEquiv (.inr j)) (circleBase j) (circleBase_embedding j)
    (circleBase_range j))).2.2.2.2.1
  circleTriv_disk j := (Classical.choose_spec (edge_circle_product_ECM P
    (componentEquiv (.inr j)) (circleBase j) (circleBase_embedding j)
    (circleBase_range j))).2.2.2.2.2.1
  circleTriv_rim j := (Classical.choose_spec (edge_circle_product_ECM P
    (componentEquiv (.inr j)) (circleBase j) (circleBase_embedding j)
    (circleBase_range j))).2.2.2.2.2.2

end GC.GraphManifold.Assembly.FC39P0
