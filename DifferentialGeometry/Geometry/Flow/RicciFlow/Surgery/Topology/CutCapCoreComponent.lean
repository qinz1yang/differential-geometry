import DifferentialGeometry.Topology.Connected.BoundaryCollarComponent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapRegionStructure
import DifferentialGeometry.Geometry.Neck.Spatial
import Mathlib.Topology.OpenPartialHomeomorph.Composition
import DifferentialGeometry.Topology.Manifold.ImmersionImageNhds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.MiddleSphereSliceSmoothEmbedding

section

open Set
open scoped Manifold ContDiff
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [T2Space M] (T : TubeSystem M)

theorem isClopen_preimage_of_capCore_outward_collar
    {K : Set M} (cap : CapCore K)
    (b : T.Boundary) (hdisj : Disjoint K (T.removedBand b.1))
    (e : OpenPartialHomeomorph (Sphere 2 × ℝ) M)
    {r : ℝ} (hr : 0 < r) (hsource : univ ×ˢ Ioo (-r) r ⊆ e.source)
    (hfront : frontier K = range (T.boundarySphere b))
    (hzero : ∀ z : Sphere 2, e (z, 0) = T.boundarySphere b z)
    (hpos : ∀ z : Sphere 2, ∀ t ∈ Ioo (0 : ℝ) r, e (z, t) ∈ T.removedBand b.1)
    : IsClopen ((Subtype.val : T.core → M) ⁻¹' K) := by
  let : ConnectedSpace (Sphere 2) := isConnected_iff_connectedSpace.mp
    (isConnected_sphere (E := EuclideanSpace ℝ (Fin 3))
      (Module.one_lt_rank_of_one_lt_finrank (by simp)) 0 zero_le_one)
  have hfront' : frontier K = range (fun z : Sphere 2 => e (z, 0)) := by
    simpa only [hzero] using hfront
  apply DifferentialGeometry.Topology.isClopen_preimage_of_outward_collar
    cap.closure_interior_carrier e hr hsource hfront'
  intro z t ht hy
  rcases hy with hyK | hycore
  · exact disjoint_left.mp hdisj hyK (hpos z t ht)
  · exact hycore (mem_iUnion.mpr ⟨b.1,hpos z t ht⟩)

theorem connectedComponent_eq_preimage_of_capCore_outward_collar
    {K : Set M} (cap : CapCore K) (hcore : K ⊆ T.core)
    (b : T.Boundary) (e : OpenPartialHomeomorph (Sphere 2 × ℝ) M)
    {r : ℝ} (hr : 0 < r) (hsource : univ ×ˢ Ioo (-r) r ⊆ e.source)
    (hfront : frontier K = range (T.boundarySphere b))
    (hzero : ∀ z : Sphere 2, e (z, 0) = T.boundarySphere b z)
    (hpos : ∀ z : Sphere 2, ∀ t ∈ Ioo (0 : ℝ) r, e (z, t) ∈ T.removedBand b.1)
    (x : T.core) (hx : x.val ∈ K) :
    connectedComponent x = (Subtype.val : T.core → M) ⁻¹' K := by
  have hdisj : Disjoint K (T.removedBand b.1) := disjoint_left.mpr
    (fun y hyK hyband => hcore hyK (mem_iUnion.mpr ⟨b.1,hyband⟩))
  have hcl := T.isClopen_preimage_of_capCore_outward_collar cap b hdisj e hr hsource hfront hzero hpos
  have hpre : IsPreconnected ((Subtype.val : T.core → M) ⁻¹' K) := by
    apply _root_.Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rw [Subtype.image_preimage_coe,inter_eq_right.mpr hcore]
    exact cap.isConnected_carrier.isPreconnected
  exact Subset.antisymm (hcl.connectedComponent_subset hx) (hpre.subset_connectedComponent hx)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

end

section

open Set
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M] (T : TubeSystem M)

theorem connectedComponent_eq_preimage_of_capCore_of_spatialNeck
    {K : Set M} (cap : CapCore K) (hcore : K ⊆ T.core)
    (b : T.Boundary) (hfront : frontier K = range (T.boundarySphere b))
    {g : SmoothRiemannianMetric ThreeModel M} {eps : ℝ} {p : M}
    (nk : SpatialNeck g eps p)
    (hmap : ∀ q : TubeDomain, q.2.val ∈ Icc (-1 : ℝ) 1 →
      T.tube b.1 q = nk.map (q.1, q.2.val))
    (x : T.core) (hx : x.val ∈ K) :
    connectedComponent x = (Subtype.val : T.core → M) ⁻¹' K := by
  let H : (Sphere 2 × ℝ) ≃ₜ (Sphere 2 × ℝ) :=
    { toFun := fun q => (q.1, if b.2 then 1 - q.2 else -1 + q.2)
      invFun := fun q => (q.1, if b.2 then 1 - q.2 else 1 + q.2)
      left_inv := by intro q; cases b.2 <;> simp
      right_inv := by intro q; cases b.2 <;> simp
      continuous_toFun := by
        cases hb : b.2
        · exact continuous_fst.prodMk (continuous_const.add continuous_snd)
        · exact continuous_fst.prodMk (continuous_const.sub continuous_snd)
      continuous_invFun := by
        cases hb : b.2
        · exact continuous_fst.prodMk (continuous_const.add continuous_snd)
        · exact continuous_fst.prodMk (continuous_const.sub continuous_snd) }
  let e := H.transOpenPartialHomeomorph nk.map.toOpenPartialHomeomorph
  have happ (z : Sphere 2) (t : ℝ) :
      e (z, t) = nk.map (z, if b.2 then 1 - t else -1 + t) := rfl
  have hrange : (2 : ℝ) < eps⁻¹ := by
    have heps : eps < (2 : ℝ)⁻¹ := nk.eps_small.trans (by norm_num)
    exact lt_inv_of_lt_inv₀ nk.eps_pos heps
  apply T.connectedComponent_eq_preimage_of_capCore_outward_collar cap hcore b e
    (r := 1) zero_lt_one _ hfront _ _ x hx
  · rintro ⟨z, t⟩ ⟨_, ht⟩
    change H (z, t) ∈ nk.map.source
    apply nk.domain
    change (z, if b.2 then 1 - t else -1 + t) ∈ univ ×ˢ Ioo (-eps⁻¹) eps⁻¹
    refine ⟨mem_univ _, ?_, ?_⟩ <;> cases b.2 <;>
      simp only [Bool.false_eq_true, ite_false, ite_true] <;> linarith [ht.1, ht.2]
  · intro z
    rw [happ]
    change _ = T.tube b.1 (z, boundaryLevel b.2)
    rw [hmap _ (by cases hb : b.2 <;> norm_num [boundaryLevel, hb])]
    cases b.2 <;> simp [boundaryLevel]
  · intro z t ht
    let v : ℝ := if b.2 then 1 - t else -1 + t
    have hv : v ∈ Ioo (-1 : ℝ) 1 := by
      cases hb : b.2 <;> simp only [v, hb, Bool.false_eq_true, ite_false, ite_true] <;>
        constructor <;> linarith [ht.1, ht.2]
    let q : TubeDomain := (z, ⟨v, by constructor <;> linarith [hv.1, hv.2]⟩)
    refine ⟨q, hv, ?_⟩
    rw [hmap q ⟨hv.1.le, hv.2.le⟩]
    rfl

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

end

noncomputable section

open Set Manifold
open scoped Manifold ContDiff Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] (T : TubeSystem M)

local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

omit [IsManifold ThreeModel ∞ M] in
theorem isSmoothEmbedding_boundarySphere (b : T.Boundary)
    (hs : IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube b.1)) :
    IsSmoothEmbedding (𝓡 2) ThreeModel ∞ (T.boundarySphere b) := by
  have hi : IsSmoothEmbedding (𝓡 2) ((𝓡 2).prod (𝓡∂ 1)) ∞
      (fun z : Sphere 2 => (z, boundaryLevel b.2)) :=
    _root_.Manifold.isSmoothEmbedding_prodMk_of_isInteriorPoint
      (Icc_isInteriorPoint_interior (by cases b.2 <;> norm_num [boundaryLevel]))
  exact IsSmoothEmbedding.comp (I := 𝓡 2) (J := (𝓡 2).prod (𝓡∂ 1)) (J' := ThreeModel)
    (f := fun z : Sphere 2 => (z, boundaryLevel b.2)) (g := fun z => T.tube b.1 z) hs hi
    (by decide)


omit [IsManifold ThreeModel ∞ M] in
private theorem exists_openPartialHomeomorph_tube_interior (a : T.Index)
    (hs : IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube a)) :
    ∃ e : OpenPartialHomeomorph (Sphere 2 × ℝ) M,
      univ ×ˢ Ioo (-2 : ℝ) 2 ⊆ e.source ∧
        ∀ (q : TubeDomain), q.2.val ∈ Ioo (-2 : ℝ) 2 → e (q.1, q.2.val) = T.tube a q := by
  let D : Set (Sphere 2 × ℝ) := univ ×ˢ Ioo (-2 : ℝ) 2
  have hD : IsOpen D := isOpen_univ.prod isOpen_Ioo
  let j : D → TubeDomain := fun q => (q.val.1, ⟨q.val.2, q.property.2.1.le, q.property.2.2.le⟩)
  have hj : _root_.Topology.IsEmbedding j := by
    have hk : _root_.Topology.IsEmbedding (fun q : TubeDomain => (q.1, q.2.val)) :=
      _root_.Topology.IsEmbedding.id.prodMap _root_.Topology.IsEmbedding.subtypeVal
    apply hk.of_comp_iff.mp
    exact _root_.Topology.IsEmbedding.subtypeVal
  let F : D → M := T.tube a ∘ j
  have hF : _root_.Topology.IsOpenEmbedding F := by
    refine ⟨(T.embedding a).comp hj, ?_⟩
    rw [isOpen_iff_mem_nhds]
    rintro y ⟨q, rfl⟩
    let A : Set TubeDomain := {q | q.2.val ∈ Ioo (-2 : ℝ) 2}
    have hA : IsOpen A := isOpen_Ioo.preimage (continuous_subtype_val.comp continuous_snd)
    have hqA : j q ∈ A := q.property.2
    have hqi : ((𝓡 2).prod (𝓡∂ 1)).IsInteriorPoint (j q) := by
      change j q ∈ ((𝓡 2).prod (𝓡∂ 1)).interior TubeDomain
      rw [ModelWithCorners.interior_prod]
      exact ⟨BoundarylessManifold.isInteriorPoint, Icc_isInteriorPoint_interior q.property.2⟩
    have hnh := DifferentialGeometry.Topology.immersion_image_mem_nhds
      (hs.isImmersion.isImmersionAt (j q)) (by simp [ThreeSpace, Module.finrank_prod])
      hqi (hA.mem_nhds hqA)
    apply Filter.mem_of_superset hnh
    rintro z ⟨w, hw, rfl⟩
    exact ⟨⟨(w.1, w.2.val), mem_univ _, hw⟩, rfl⟩
  let z : Sphere 2 := ⟨EuclideanSpace.single 0 1, by simp⟩
  let : Nonempty D := ⟨⟨(z, 0), mem_univ _, by norm_num⟩⟩
  let E₀ := hD.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph (Subtype.val : D → Sphere 2 × ℝ)
  let E₁ := hF.toOpenPartialHomeomorph F
  let e := E₀.symm.trans E₁
  refine ⟨e, ?_, ?_⟩
  · intro p hp
    change p ∈ E₀.target ∩ E₀.symm ⁻¹' E₁.source
    simp only [E₀, E₁, _root_.Topology.IsOpenEmbedding.toOpenPartialHomeomorph_target,
      _root_.Topology.IsOpenEmbedding.toOpenPartialHomeomorph_source, Subtype.range_coe,
      preimage_univ, inter_univ]
    exact hp
  · intro q hq
    have he : E₀.symm (q.1, q.2.val) = ⟨(q.1, q.2.val), mem_univ _, hq⟩ :=
      hD.isOpenEmbedding_subtypeVal.toOpenPartialHomeomorph_left_inv
        (x := (⟨(q.1, q.2.val), mem_univ _, hq⟩ : D))
    change E₁ (E₀.symm (q.1, q.2.val)) = _
    rw [he]
    rfl


omit [IsManifold ThreeModel ∞ M] in
theorem isClopen_preimage_of_capCore_of_boundarySphere
    [T2Space M] {K : Set M} (cap : CapCore K)
    (b : T.Boundary) (hdisj : Disjoint K (T.removedBand b.1)) (hfront : frontier K = range (T.boundarySphere b))
    (hs : IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube b.1))
    : IsClopen ((Subtype.val : T.core → M) ⁻¹' K) := by
  obtain ⟨E, hEsource, hE⟩ := T.exists_openPartialHomeomorph_tube_interior b.1 hs
  let H : (Sphere 2 × ℝ) ≃ₜ (Sphere 2 × ℝ) :=
    { toFun := fun q => (q.1, if b.2 then 1 - q.2 else -1 + q.2)
      invFun := fun q => (q.1, if b.2 then 1 - q.2 else 1 + q.2)
      left_inv := by intro q; cases b.2 <;> simp
      right_inv := by intro q; cases b.2 <;> simp
      continuous_toFun := by
        cases b.2
        · exact continuous_fst.prodMk (continuous_const.add continuous_snd)
        · exact continuous_fst.prodMk (continuous_const.sub continuous_snd)
      continuous_invFun := by
        cases b.2
        · exact continuous_fst.prodMk (continuous_const.add continuous_snd)
        · exact continuous_fst.prodMk (continuous_const.sub continuous_snd) }
  let e := H.transOpenPartialHomeomorph E
  have happ (z : Sphere 2) (t : ℝ) :
      e (z, t) = E (z, if b.2 then 1 - t else -1 + t) := rfl
  apply T.isClopen_preimage_of_capCore_outward_collar cap b hdisj e
    (r := 1) zero_lt_one _ hfront _ _
  · rintro ⟨z, t⟩ ⟨_, ht⟩
    change H (z, t) ∈ E.source
    apply hEsource
    change (z, if b.2 then 1 - t else -1 + t) ∈ univ ×ˢ Ioo (-2 : ℝ) 2
    refine ⟨mem_univ _, ?_, ?_⟩ <;> cases b.2 <;>
      simp only [Bool.false_eq_true, ite_false, ite_true] <;> linarith [ht.1, ht.2]
  · intro z
    rw [happ]
    change _ = T.tube b.1 (z, boundaryLevel b.2)
    rw [← hE (z, boundaryLevel b.2) (by cases b.2 <;> norm_num [boundaryLevel])]
    cases b.2 <;> simp [boundaryLevel]
  · intro z t ht
    let v : ℝ := if b.2 then 1 - t else -1 + t
    have hv : v ∈ Ioo (-1 : ℝ) 1 := by
      cases hb : b.2 <;> simp only [v, hb, Bool.false_eq_true, ite_false, ite_true] <;>
        constructor <;> linarith [ht.1, ht.2]
    let q : TubeDomain := (z, ⟨v, by constructor <;> linarith [hv.1, hv.2]⟩)
    refine ⟨q, hv, ?_⟩
    rw [← hE q (by constructor <;> linarith [hv.1, hv.2])]
    rfl

omit [IsManifold ThreeModel ∞ M] in
theorem connectedComponent_eq_preimage_of_capCore_of_boundarySphere
    [T2Space M] {K : Set M} (cap : CapCore K) (hcore : K ⊆ T.core)
    (b : T.Boundary) (hfront : frontier K = range (T.boundarySphere b))
    (hs : IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube b.1))
    (x : T.core) (hx : x.val ∈ K) :
    connectedComponent x = (Subtype.val : T.core → M) ⁻¹' K := by
  have hdisj : Disjoint K (T.removedBand b.1) := disjoint_left.mpr
    (fun y hyK hyband => hcore hyK (mem_iUnion.mpr ⟨b.1,hyband⟩))
  have hcl := T.isClopen_preimage_of_capCore_of_boundarySphere cap b hdisj hfront hs
  have hpre : IsPreconnected ((Subtype.val : T.core → M) ⁻¹' K) := by
    apply _root_.Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rw [Subtype.image_preimage_coe,inter_eq_right.mpr hcore]
    exact cap.isConnected_carrier.isPreconnected
  exact Subset.antisymm (hcl.connectedComponent_subset hx) (hpre.subset_connectedComponent hx)


omit [IsManifold ThreeModel ∞ M] in
theorem connectedComponent_subset_preimage_of_capCore_of_boundarySphere
    [T2Space M] {K : Set M} (cap : CapCore K)
    (b : T.Boundary) (hdisj : Disjoint K (T.removedBand b.1))
    (hfront : frontier K = range (T.boundarySphere b))
    (hs : IsSmoothEmbedding ((𝓡 2).prod (𝓡∂ 1)) ThreeModel ∞ (T.tube b.1))
    (x : T.core) (hx : x.val ∈ K) :
    connectedComponent x ⊆ (Subtype.val : T.core → M) ⁻¹' K :=
  (T.isClopen_preimage_of_capCore_of_boundarySphere cap b hdisj hfront hs).connectedComponent_subset hx

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem
