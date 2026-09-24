import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutBandCapCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CapCoreSphereFilling
import DifferentialGeometry.Geometry.Neck.SpatialLevelEmbedding
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CutCapCoreComponent
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalStrictBounds

noncomputable section
open Set Manifold
open DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [T2Space M] (T : TubeSystem M)

omit [ChartedSpace ThreeSpace M] [T2Space M] in
private theorem isPreconnected_band (a : T.Index) (I : Set ℝ) (hI : IsPreconnected I)
    (hsub : I ⊆ Icc (-2 : ℝ) 2) :
    IsPreconnected (T.tube a '' {q : TubeDomain | q.2.val ∈ I}) := by
  let : PreconnectedSpace (Sphere 2) := isPreconnected_iff_preconnectedSpace.mp
    (isPreconnected_sphere (Module.one_lt_rank_of_one_lt_finrank (by simp [ThreeSpace]))
      (0 : ThreeSpace) 1)
  let : PreconnectedSpace I := isPreconnected_iff_preconnectedSpace.mp hI
  let j : Sphere 2 × I → TubeDomain := fun q => (q.1, ⟨q.2.val, hsub q.2.property⟩)
  have hj : Continuous j := continuous_fst.prodMk
    ((continuous_subtype_val.comp continuous_snd).subtype_mk _)
  have hr : range (T.tube a ∘ j) = T.tube a '' {q : TubeDomain | q.2.val ∈ I} := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨j q, q.2.property, rfl⟩
    · rintro ⟨q, hq, rfl⟩
      exact ⟨(q.1, ⟨q.2.val, hq⟩), rfl⟩
  exact hr ▸ isPreconnected_range ((T.tube a).continuous.comp hj)

omit [ChartedSpace ThreeSpace M] [T2Space M] in
private theorem band_disjoint_boundary (a : T.Index) (side : Bool) {I : Set ℝ}
    (hI : ∀ s ∈ I, s ≠ (boundaryLevel side).val) :
    Disjoint (T.tube a '' {q : TubeDomain | q.2.val ∈ I})
      (range (T.boundarySphere (a, side))) := by
  rw [disjoint_left]
  rintro x ⟨q, hq, rfl⟩ ⟨z, hz⟩
  have he := congrArg (fun p : TubeDomain => p.2.val) ((T.embedding a).injective hz)
  exact hI q.2.val hq he.symm

omit [ChartedSpace ThreeSpace M] [T2Space M] in
private theorem band_subset_cap_of_center_mem
    (a : T.Index) (side : Bool) {K : Set M} (hfront : frontier K = range (T.boundarySphere (a, side)))
    (q : Sphere 2) (hq : T.tube a (q, ⟨0, by norm_num⟩) ∈ K) :
    T.removedBand a ⊆ interior K ∧ range (T.boundarySphere (a, !side)) ⊆ interior K := by
  let I : Set ℝ := if side then Ico (-1 : ℝ) 1 else Ioc (-1 : ℝ) 1
  have hI : IsPreconnected I := by
    cases side
    · exact isPreconnected_Ioc
    · exact isPreconnected_Ico
  have hsub : I ⊆ Icc (-2 : ℝ) 2 := by
    cases side <;> simp only [I, Bool.false_eq_true, if_false, if_true]
    · intro s hs; constructor <;> linarith [hs.1, hs.2]
    · intro s hs; constructor <;> linarith [hs.1, hs.2]
  have havoid : Disjoint (T.tube a '' {p : TubeDomain | p.2.val ∈ I}) (frontier K) := by
    rw [hfront]
    apply T.band_disjoint_boundary
    cases side <;> simp only [I, Bool.false_eq_true, if_false, if_true, boundaryLevel]
    · intro s hs; linarith [hs.1]
    · intro s hs; linarith [hs.2]
  have hzero : (0 : ℝ) ∈ I := by cases side <;> norm_num [I]
  have hin := isPreconnected_subset_interior_of_meets_of_disjoint_frontier
    (T.isPreconnected_band a I hI hsub)
    ⟨T.tube a (q, ⟨0, by norm_num⟩), ⟨(q, ⟨0, by norm_num⟩), hzero, rfl⟩, hq⟩ havoid
  constructor
  · rintro x ⟨z, hz, rfl⟩
    apply hin
    refine ⟨z, ?_, rfl⟩
    cases side <;> simp only [I, Bool.false_eq_true, if_false, if_true]
    · exact ⟨hz.1, hz.2.le⟩
    · exact ⟨hz.1.le, hz.2⟩
  · rintro x ⟨z, rfl⟩
    apply hin
    refine ⟨(z, boundaryLevel (!side)), ?_, rfl⟩
    cases side <;> norm_num [I, boundaryLevel]


theorem exists_capCore_cutting_side_of_boundary_spheres_subset
    (a : T.Index) {U : Set M} (cap : CapCore U)
    (hsmooth : ∀ side : Bool, IsSmoothEmbedding I2 I3 ∞ (T.boundarySphere (a, side)))
    (hinside : ∀ side : Bool, range (T.boundarySphere (a, side)) ⊆ interior U) :
    ∃ (side : Bool) (K : Set M), Nonempty (CapCore K) ∧ K ⊆ interior U ∧
      frontier K = range (T.boundarySphere (a, side)) ∧ Disjoint K (T.removedBand a) := by
  classical
  choose K hK hcompact hreg hfront hKU using fun side =>
    cap.exists_capCore_side_of_sphere_embedding (T.boundarySphere (a, side)) (hsmooth side) (hinside side)
  let q : Sphere 2 := ⟨EuclideanSpace.single 0 1, by simp⟩
  have hex : ∃ side : Bool, T.tube a (q, ⟨0, by norm_num⟩) ∉ K side := by
    by_contra h
    push Not at h
    have hf := (T.band_subset_cap_of_center_mem a false (hfront false) q (h false)).2
    have ht := (T.band_subset_cap_of_center_mem a true (hfront true) q (h true)).2
    have hfrontEmpty : frontier (K false ∪ K true) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      rcases frontier_union_subset (K false) (K true) hx with hx' | hx'
      · exact hx.2 (interior_mono subset_union_right (ht (hfront false ▸ hx'.1)))
      · exact hx.2 (interior_mono subset_union_left (hf (hfront true ▸ hx'.2)))
    have hclopen : IsClopen (K false ∪ K true) :=
      isClopen_iff_frontier_eq_empty.mpr hfrontEmpty
    obtain ⟨z, hz⟩ := (hK false).some.nonempty_carrier
    have hsub : U ⊆ K false ∪ K true := cap.isConnected_carrier.isPreconnected.subset_isClopen
      hclopen ⟨z, interior_subset (hKU false hz), Or.inl hz⟩
    obtain ⟨y, hy⟩ := cap.frontier_nonempty
    have hyU := cap.isCompact_carrier.isClosed.frontier_subset hy
    exact hy.2 ((hsub hyU).elim (fun h => hKU false h) (fun h => hKU true h))
  obtain ⟨side, hside⟩ := hex
  refine ⟨side, K side, hK side, hKU side, hfront side, ?_⟩
  have hband : IsPreconnected (T.removedBand a) :=
    T.isPreconnected_band a (Ioo (-1 : ℝ) 1) isPreconnected_Ioo
      (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  have havoid : Disjoint (T.removedBand a) (frontier ((K side)ᶜ)) := by
    rw [frontier_compl, hfront side]
    change Disjoint (T.tube a '' {q : TubeDomain | q.2.val ∈ Ioo (-1 : ℝ) 1}) _
    apply T.band_disjoint_boundary
    intro z hz
    cases side
    · change z ≠ -1
      linarith [hz.1]
    · change z ≠ 1
      linarith [hz.2]
  have hout := isPreconnected_subset_interior_of_meets_of_disjoint_frontier hband
    ⟨T.tube a (q, ⟨0, by norm_num⟩), ⟨(q, ⟨0, by norm_num⟩), by norm_num, rfl⟩, hside⟩ havoid
  exact disjoint_right.mpr fun x hxband hxK => interior_subset (hout hxband) hxK

theorem exists_capCore_cutting_side_of_closedBand_subset
    (a : T.Index) {U : Set M} (cap : CapCore U)
    (hsmooth : ∀ side : Bool, IsSmoothEmbedding I2 I3 ∞ (T.boundarySphere (a, side)))
    (hinside : T.tube a '' {q : TubeDomain | q.2.val ∈ Icc (-1 : ℝ) 1} ⊆ interior U) :
    ∃ (side : Bool) (K : Set M), Nonempty (CapCore K) ∧ K ⊆ interior U ∧
      frontier K = range (T.boundarySphere (a, side)) ∧ Disjoint K (T.removedBand a) :=
  T.exists_capCore_cutting_side_of_boundary_spheres_subset a cap hsmooth
    (T.central_and_boundary_spheres_subset_of_closedBand_subset a hinside).2

theorem exists_capCore_in_cutCore_of_boundary_spheres_subset
    (a : T.Index) {U : Set M} (cap : CapCore U)
    (hsmooth : ∀ side : Bool, IsSmoothEmbedding I2 I3 ∞ (T.boundarySphere (a, side)))
    (hinside : ∀ side : Bool, range (T.boundarySphere (a, side)) ⊆ interior U)
    (hanchor : ∀ j : T.Index, j ≠ a → ∃ z ∈ T.removedBand j, z ∉ interior U) :
    ∃ (side : Bool) (K : Set M), Nonempty (CapCore K) ∧ K ⊆ interior U ∧
      frontier K = range (T.boundarySphere (a, side)) ∧ K ⊆ T.core := by
  obtain ⟨side, K, hK, hKU, hfront, havoid⟩ :=
    T.exists_capCore_cutting_side_of_boundary_spheres_subset a cap hsmooth hinside
  refine ⟨side, K, hK, hKU, hfront, ?_⟩
  intro x hx hremoved
  obtain ⟨j, hxj⟩ := mem_iUnion.mp hremoved
  by_cases hja : j = a
  · exact disjoint_left.mp havoid hx (hja ▸ hxj)
  have hband : IsPreconnected (T.removedBand j) :=
    T.isPreconnected_band j (Ioo (-1 : ℝ) 1) isPreconnected_Ioo
      (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  have hfrontdis : Disjoint (T.removedBand j) (frontier (Kᶜ)) := by
    rw [frontier_compl, hfront]
    exact (T.disjoint hja).mono (image_subset_range _ _) (by
      rintro y ⟨z, rfl⟩
      exact mem_range_self (z, boundaryLevel side))
  obtain ⟨z, hz, hzU⟩ := hanchor j hja
  have hout := isPreconnected_subset_interior_of_meets_of_disjoint_frontier (R := Kᶜ) hband
    ⟨z, hz, fun hzK => hzU (hKU hzK)⟩ hfrontdis
  exact interior_subset (hout hxj) hx

theorem exists_capCore_in_cutCore_of_single_cut_boundary_spheres_subset
    [Subsingleton T.Index] (a : T.Index) {U : Set M} (cap : CapCore U)
    (hsmooth : ∀ side : Bool, IsSmoothEmbedding I2 I3 ∞ (T.boundarySphere (a, side)))
    (hinside : ∀ side : Bool, range (T.boundarySphere (a, side)) ⊆ interior U) :
    ∃ (side : Bool) (K : Set M), Nonempty (CapCore K) ∧ K ⊆ interior U ∧
      frontier K = range (T.boundarySphere (a, side)) ∧ K ⊆ T.core :=
  T.exists_capCore_in_cutCore_of_boundary_spheres_subset a cap hsmooth hinside
    (fun j hja => (hja (Subsingleton.elim j a)).elim)

theorem exists_capCore_in_cutCore_of_spatialNeck_center_close
    [IsManifold I3 ∞ M]
    {J : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) J}
    {eps epsc t : ℝ} {x p : M} {U : Set M} (cap : LocalCap S epsc x t U)
    (hdepth : ∀ y ∈ cap.tube,
      10000 / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x y)
    (nk : SpatialNeck (S.base.metric t) eps p) (a : T.Index)
    (hmap : ∀ q : TubeDomain, q.2.val ∈ Icc (-1 : ℝ) 1 →
      T.tube a q = nk.map (q.1, q.2.val))
    (hclose : riemannianEDistOf (S.base.metric t) x p +
      ENNReal.ofReal (7 * Real.sqrt (1 + eps) / Real.sqrt (metricScalarAt (S.base.metric t) p)) <
        ENNReal.ofReal (10000 / Real.sqrt (S.scalar t x)))
    (hanchor : ∀ j : T.Index, j ≠ a → ∃ z ∈ T.removedBand j, z ∉ interior cap.core.carrier) :
    ∃ (side : Bool) (K : Set M), Nonempty (CapCore K) ∧ K ⊆ interior cap.core.carrier ∧
      frontier K = range (T.boundarySphere (a, side)) ∧ K ⊆ T.core := by
  have hinside := T.closedBand_subset_cap_core_interior_of_spatialNeck_center_close
    cap hdepth nk a hmap hclose
  have hsmall : (1 : ℝ) < eps⁻¹ :=
    (one_lt_inv₀ nk.eps_pos).mpr (nk.eps_small.trans (by norm_num))
  have hsmooth : ∀ side : Bool, IsSmoothEmbedding I2 I3 ∞ (T.boundarySphere (a, side)) := by
    intro side
    have heq : (T.boundarySphere (a, side) : Sphere 2 → M) =
        fun z => nk.map (z, (boundaryLevel side).val) := by
      funext z
      exact hmap (z, boundaryLevel side) (by cases side <;> norm_num [boundaryLevel])
    rw [heq]
    apply nk.isSmoothEmbedding_level
    cases side <;> simpa only [boundaryLevel, Bool.false_eq_true, if_false, if_true,
      abs_neg, abs_one] using hsmall
  exact T.exists_capCore_in_cutCore_of_boundary_spheres_subset a cap.core_model hsmooth
    (T.central_and_boundary_spheres_subset_of_closedBand_subset a hinside).2 hanchor

section

variable [IsManifold I3 ∞ M]

theorem exists_capCore_component_of_spatialNeck_center_close
    {J : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) J}
    {eps epsc t : ℝ} {x p : M} {U : Set M} (cap : LocalCap S epsc x t U)
    (hdepth : ∀ y ∈ cap.tube,
      10000 / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x y)
    (nk : SpatialNeck (S.base.metric t) eps p) (a : T.Index)
    (hmap : ∀ q : TubeDomain, q.2.val ∈ Icc (-1 : ℝ) 1 →
      T.tube a q = nk.map (q.1, q.2.val))
    (hclose : riemannianEDistOf (S.base.metric t) x p +
      ENNReal.ofReal (7 * Real.sqrt (1 + eps) / Real.sqrt (metricScalarAt (S.base.metric t) p)) <
        ENNReal.ofReal (10000 / Real.sqrt (S.scalar t x)))
    (hanchor : ∀ j : T.Index, j ≠ a → ∃ z ∈ T.removedBand j, z ∉ interior cap.core.carrier) :
    ∃ (side : Bool) (K : Set M), Nonempty (CapCore K) ∧ K ⊆ interior cap.core.carrier ∧
      frontier K = range (T.boundarySphere (a, side)) ∧ K ⊆ T.core ∧
      ∀ z : T.core, z.val ∈ K → connectedComponent z = (Subtype.val : T.core → M) ⁻¹' K := by
  obtain ⟨side, K, hK, hKU, hfront, hcore⟩ :=
    T.exists_capCore_in_cutCore_of_spatialNeck_center_close cap hdepth nk a hmap hclose hanchor
  exact ⟨side, K, hK, hKU, hfront, hcore, fun z hz =>
    T.connectedComponent_eq_preimage_of_capCore_of_spatialNeck hK.some hcore (a, side)
      hfront nk hmap z hz⟩


variable [SigmaCompactSpace M]

theorem exists_capCore_discarded_component_of_spatialNeck_center_close
    {J : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) J}
    {eps epsc C1 C2 t : ℝ} {x p : M}
    (W : CanonicalWitness S epsc C1 C2 x t)
    (cap : LocalCap S epsc x t W.domain.carrier)
    (hdepth : ∀ y ∈ cap.tube,
      10000 / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x y)
    (nk : SpatialNeck (S.base.metric t) eps p) (a : T.Index)
    (hmap : ∀ q : TubeDomain, q.2.val ∈ Icc (-1 : ℝ) 1 →
      T.tube a q = nk.map (q.1, q.2.val))
    (hclose : riemannianEDistOf (S.base.metric t) x p +
      ENNReal.ofReal (7 * Real.sqrt (1 + eps) / Real.sqrt (metricScalarAt (S.base.metric t) p)) <
        ENNReal.ofReal (10000 / Real.sqrt (S.scalar t x)))
    (hanchor : ∀ j : T.Index, j ≠ a → ∃ z ∈ T.removedBand j, z ∉ interior cap.core.carrier)
    (R : Set (ConnectedComponents T.core))
    (hlow : ∀ c ∈ R, ∃ z : T.core, ConnectedComponents.mk z = c ∧
      C2 * S.scalar t z.val < S.scalar t x) :
    ∃ (side : Bool) (K : Set M), Nonempty (CapCore K) ∧ K ⊆ interior cap.core.carrier ∧
      frontier K = range (T.boundarySphere (a, side)) ∧ K ⊆ T.core ∧
      (∀ z : T.core, z.val ∈ K →
        connectedComponent z = (Subtype.val : T.core → M) ⁻¹' K) ∧
      ∀ z : T.core, z.val ∈ K → ConnectedComponents.mk z ∉ R := by
  obtain ⟨side, K, hK, hKU, hfront, hcore, hcomponent⟩ :=
    T.exists_capCore_component_of_spatialNeck_center_close cap hdepth nk a hmap hclose hanchor
  refine ⟨side, K, hK, hKU, hfront, hcore, hcomponent, ?_⟩
  intro z hz hret
  obtain ⟨y, hy, hscalar⟩ := hlow _ hret
  have hyz : y ∈ connectedComponent z := ConnectedComponents.coe_eq_coe'.mp hy
  have hyK : y.val ∈ K := by
    change y ∈ (Subtype.val : T.core → M) ⁻¹' K
    rw [← hcomponent z hz]
    exact hyz
  have hyU : y.val ∈ W.domain.carrier :=
    interior_subset (cap.core_inside (interior_subset (hKU hyK)))
  have hC2 : 0 < C2 := zero_lt_one.trans_le W.one_le_comparison_constant
  have hbound := mul_le_mul_of_nonneg_left (W.scalar_bounds y.val hyU).1 hC2.le
  rw [← mul_assoc, mul_inv_cancel₀ hC2.ne', one_mul] at hbound
  exact hscalar.not_ge hbound

end

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.TubeSystem
