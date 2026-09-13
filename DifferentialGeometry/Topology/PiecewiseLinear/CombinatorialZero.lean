import DifferentialGeometry.Topology.PiecewiseLinear.VertexChart

open Set Topology
open scoped Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

section Zero

variable (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]

omit [FiniteDimensional ℝ E] [Finite K.faces] in
open Classical in
theorem eq_singleton_of_isCombinatorialManifold_zero (hK : IsCombinatorialManifold 0 K)
    {t : Finset E} (ht : t ∈ K.faces) {v : E} (hv : v ∈ t) : t = {v} := by
  refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hv, fun w hw => ?_⟩
  by_contra hwv
  have hlink : ({w} : Finset E) ∈ (SimplicialComplex.geometricLink K {v}).faces := by
    refine (SimplicialComplex.mem_geometricLink_singleton K v {w}).mpr
      ⟨Finset.singleton_nonempty w, Finset.notMem_singleton.mpr (Ne.symm hwv), ?_⟩
    exact K.down_closed ht (Finset.insert_subset hv (Finset.singleton_subset_iff.mpr hw))
      (Finset.insert_nonempty v {w})
  have h0 : (SimplicialComplex.geometricLink K {v}).faces = ∅ :=
    hK v (K.down_closed ht (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v))
  rw [h0] at hlink
  exact Set.notMem_empty _ hlink

omit [FiniteDimensional ℝ E] in
theorem space_finite_of_isCombinatorialManifold_zero (hK : IsCombinatorialManifold 0 K) :
    K.space.Finite := by
  refine ((Set.toFinite K.faces).biUnion fun t _ => t.finite_toSet).subset ?_
  intro x hx
  obtain ⟨t, ht, hxt⟩ := K.mem_space_iff.mp hx
  obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces ht
  have ht' := eq_singleton_of_isCombinatorialManifold_zero K hK ht hv
  rw [ht', Finset.coe_singleton, convexHull_singleton] at hxt
  refine mem_iUnion₂.mpr ⟨t, ht, ?_⟩
  rw [ht', Finset.coe_singleton]
  exact hxt

omit [FiniteDimensional ℝ E] [Finite K.faces] in
theorem exists_vertex_eq_of_isCombinatorialManifold_zero (hK : IsCombinatorialManifold 0 K)
    (x : K.space) : ∃ p, {p} ∈ K.faces ∧ x.1 = p := by
  obtain ⟨t, ht, hxt⟩ := K.mem_space_iff.mp x.2
  obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces ht
  have ht' := eq_singleton_of_isCombinatorialManifold_zero K hK ht hv
  rw [ht', Finset.coe_singleton, convexHull_singleton] at hxt
  exact ⟨v, ht' ▸ ht, hxt⟩

theorem subsingleton_euclideanSpace_zero : Subsingleton (EuclideanSpace ℝ (Fin 0)) :=
  (WithLp.equiv 2 (Fin 0 → ℝ)).subsingleton

noncomputable def zeroChart (hK : IsCombinatorialManifold 0 K) {p : E} (hp : {p} ∈ K.faces) :
    OpenPartialHomeomorph K.space (EuclideanSpace ℝ (Fin 0)) where
  toFun _ := 0
  invFun _ := ⟨p, apex_mem_space' K hp⟩
  source := {x | x.1 = p}
  target := univ
  map_source' _ _ := mem_univ _
  map_target' _ _ := rfl
  left_inv' _ hx := Subtype.ext hx.symm
  right_inv' _ _ := by
    have := subsingleton_euclideanSpace_zero
    exact Subsingleton.elim _ _
  open_source := by
    have : Finite K.space := (space_finite_of_isCombinatorialManifold_zero K hK).to_subtype
    exact isOpen_discrete _
  open_target := isOpen_univ
  continuousOn_toFun := continuousOn_const
  continuousOn_invFun := continuousOn_const

omit [FiniteDimensional ℝ E] in
theorem zeroChart_source (hK : IsCombinatorialManifold 0 K) {p : E} (hp : {p} ∈ K.faces) :
    (zeroChart K hK hp).source = {x | x.1 = p} := rfl

omit [FiniteDimensional ℝ E] in
theorem zeroChart_target (hK : IsCombinatorialManifold 0 K) {p : E} (hp : {p} ∈ K.faces) :
    (zeroChart K hK hp).target = univ := rfl

omit [FiniteDimensional ℝ E] in
theorem zeroChart_symm_val (hK : IsCombinatorialManifold 0 K) {p : E} (hp : {p} ∈ K.faces)
    (y : EuclideanSpace ℝ (Fin 0)) : ((zeroChart K hK hp).symm y : E) = p := rfl

omit [FiniteDimensional ℝ E] in
theorem image_zeroChart_source (hK : IsCombinatorialManifold 0 K) {p : E} (hp : {p} ∈ K.faces) :
    Subtype.val '' (zeroChart K hK hp).source = {p} := by
  ext q
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hq
    rw [mem_singleton_iff] at hq
    exact ⟨⟨p, apex_mem_space' K hp⟩, rfl, hq.symm⟩

theorem isHPolytope_singleton (p : E) : IsHPolytope ({p} : Set E) := by
  have : Subsingleton {x // x ∈ ({p} : Finset E)} :=
    ⟨fun a b => Subtype.ext ((Finset.mem_singleton.mp a.2).trans
      (Finset.mem_singleton.mp b.2).symm)⟩
  have h := isHPolytope_convexHull_of_affineIndependent ({p} : Finset E)
    (affineIndependent_of_subsingleton ℝ _)
  rwa [Finset.coe_singleton, convexHull_singleton] at h

open Classical in
theorem isPiecewiseAffineOn_zeroChart (hK : IsCombinatorialManifold 0 K) {p : E}
    (hp : {p} ∈ K.faces) :
    IsPiecewiseAffineOn (fun q => if h : q ∈ K.space then zeroChart K hK hp ⟨q, h⟩ else 0)
      (Subtype.val '' (zeroChart K hK hp).source) := by
  have := subsingleton_euclideanSpace_zero
  rw [image_zeroChart_source]
  exact (isPiecewiseAffineOn_of_affine_of_isHPolytope
    (AffineMap.const ℝ E (0 : EuclideanSpace ℝ (Fin 0))) (isHPolytope_singleton p)).congr
    fun _ _ => Subsingleton.elim _ _

omit [FiniteDimensional ℝ E] in
theorem isPiecewiseAffineOn_zeroChart_symm (hK : IsCombinatorialManifold 0 K) {p : E}
    (hp : {p} ∈ K.faces) :
    IsPiecewiseAffineOn (fun y => ((zeroChart K hK hp).symm y : E))
      (zeroChart K hK hp).target := by
  rw [zeroChart_target]
  exact (isPiecewiseAffineOn_of_affine (AffineMap.const ℝ (EuclideanSpace ℝ (Fin 0)) p)
    isOpen_univ).congr fun y _ => zeroChart_symm_val K hK hp y

noncomputable def zeroChartAt (hK : IsCombinatorialManifold 0 K) (v : {v : E // {v} ∈ K.faces}) :
    OpenPartialHomeomorph K.space (EuclideanSpace ℝ (Fin 0)) :=
  zeroChart K hK v.2

noncomputable def zeroVertexOf (hK : IsCombinatorialManifold 0 K) (x : K.space) : E :=
  (exists_vertex_eq_of_isCombinatorialManifold_zero K hK x).choose

omit [FiniteDimensional ℝ E] [Finite K.faces] in
theorem zeroVertexOf_mem (hK : IsCombinatorialManifold 0 K) (x : K.space) :
    {zeroVertexOf K hK x} ∈ K.faces :=
  (exists_vertex_eq_of_isCombinatorialManifold_zero K hK x).choose_spec.1

omit [FiniteDimensional ℝ E] [Finite K.faces] in
theorem val_eq_zeroVertexOf (hK : IsCombinatorialManifold 0 K) (x : K.space) :
    x.1 = zeroVertexOf K hK x :=
  (exists_vertex_eq_of_isCombinatorialManifold_zero K hK x).choose_spec.2

@[instance_reducible] noncomputable def zeroChartedSpace (hK : IsCombinatorialManifold 0 K) :
    ChartedSpace (EuclideanSpace ℝ (Fin 0)) K.space where
  atlas := Set.range (zeroChartAt K hK)
  chartAt x := zeroChartAt K hK ⟨zeroVertexOf K hK x, zeroVertexOf_mem K hK x⟩
  mem_chart_source x := by
    rw [zeroChartAt, zeroChart_source]
    exact val_eq_zeroVertexOf K hK x
  chart_mem_atlas x := Set.mem_range_self _

omit [FiniteDimensional ℝ E] in
theorem mem_zeroChartedSpace_atlas (hK : IsCombinatorialManifold 0 K)
    {e : OpenPartialHomeomorph K.space (EuclideanSpace ℝ (Fin 0))}
    (he : e ∈ (zeroChartedSpace K hK).atlas) :
    ∃ (p : E) (hp : {p} ∈ K.faces), e = zeroChart K hK hp := by
  obtain ⟨v, hv⟩ := he
  exact ⟨v.1, v.2, by rw [← hv]; rfl⟩

omit [FiniteDimensional ℝ E] in
theorem zeroChartedSpace_hasGroupoid (hK : IsCombinatorialManifold 0 K) :
    letI := zeroChartedSpace K hK
    HasGroupoid K.space (plGroupoid 0) := by
  let _ := zeroChartedSpace K hK
  have := subsingleton_euclideanSpace_zero
  constructor
  intro e e' _ _
  exact mem_plGroupoid_of_isPiecewiseAffineOn (isPiecewiseAffineOn_of_subsingleton _ _)

end Zero

theorem combinatorialManifoldPLStructure_zero : CombinatorialManifoldPLStructure 0 := by
  intro N K hfin hK
  refine ⟨zeroChartedSpace K hK, zeroChartedSpace_hasGroupoid K hK, ?_⟩
  intro e he
  obtain ⟨p, hp, rfl⟩ := mem_zeroChartedSpace_atlas K hK he
  exact ⟨isPiecewiseAffineOn_zeroChart K hK hp, isPiecewiseAffineOn_zeroChart_symm K hK hp⟩

theorem combinatorialManifoldPLStructure : ∀ n : ℕ, CombinatorialManifoldPLStructure n
  | 0 => combinatorialManifoldPLStructure_zero
  | n + 1 => combinatorialManifoldPLStructure_succ n

end DifferentialGeometry.Topology.PiecewiseLinear
