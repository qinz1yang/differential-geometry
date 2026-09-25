import DifferentialGeometry.Topology.PiecewiseLinear.WalkArcPath
import DifferentialGeometry.Topology.PiecewiseLinear.PLPath
import DifferentialGeometry.Topology.PiecewiseLinear.Triangulation
import DifferentialGeometry.Topology.SimplicialComplex.EdgeConnectivity

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
private theorem isPLPath_edgePath {K : Geometry.SimplicialComplex ℝ E}
    {u v : K.vertices} (h : (SimplicialComplex.edgeGraph K).Adj u v) : IsPLPath (edgePath h) := by
  refine (isPiecewiseAffineOn_of_affine_of_isHPolytope
    (AffineMap.lineMap (u : E) (v : E)) isHPolytope_Icc).congr fun t ht => ?_
  rw [Path.extend_apply _ ht, edgePath_apply, AffineMap.lineMap_apply_module]

open Classical in
private theorem isPLPath_arcPath {K : Geometry.SimplicialComplex ℝ E} :
    ∀ {u v : K.vertices} (p : (SimplicialComplex.edgeGraph K).Walk u v), IsPLPath (arcPath p)
  | _, _, .nil => isPLPath_of_forall_eq _ (fun t ht => by
      rw [arcPath_nil, Path.extend_apply _ ht]; rfl)
  | _, _, .cons h .nil => by rw [arcPath_cons_nil]; exact isPLPath_edgePath h
  | _, _, .cons h (.cons h' p) => by
      rw [arcPath_cons_cons]
      exact (isPLPath_edgePath h).trans (isPLPath_arcPath (.cons h' p))

open Classical in
theorem exists_isPLHomeomorphOn_Icc_arcCarrier_of_isPath
    [FiniteDimensional ℝ E] {K : Geometry.SimplicialComplex ℝ E}
    {u v : K.vertices} (p : (SimplicialComplex.edgeGraph K).Walk u v)
    (hp : p.IsPath) (hpos : 0 < p.length) :
    ∃ γ : ℝ → E, IsPLHomeomorphOn γ (Icc 0 1) (arcCarrier p) ∧
      γ 0 = u ∧ γ 1 = v := by
  let γ : ℝ → E := fun t => (arcPath p).extend t
  have himage : γ '' Icc (0 : ℝ) 1 = arcCarrier p := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨⟨t, ht⟩, by dsimp [γ]; rw [Path.extend_apply _ ht]⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, t.2, by dsimp [γ]; rw [Path.extend_apply _ t.2]⟩
  have hinj : InjOn γ (Icc 0 1) := by
    intro s hs t ht hst
    have heq := arcPath_injective p hp hpos (Subtype.ext
      (show (arcPath p ⟨s, hs⟩ : E) = (arcPath p ⟨t, ht⟩ : E) by
        simpa only [γ, Path.extend_apply _ hs, Path.extend_apply _ ht] using hst))
    exact congrArg Subtype.val heq
  refine ⟨γ, ?_, ?_, ?_⟩
  · rw [← himage]
    exact isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn
      isHPolytope_Icc.isPolyhedron (isPLPath_arcPath p) hinj.bijOn_image
  · change ((arcPath p).extend 0 : E) = u
    rw [Path.extend_zero]
    rfl
  · change ((arcPath p).extend 1 : E) = v
    rw [Path.extend_one]
    rfl

open Classical in
theorem IsPolyhedron.exists_isPLHomeomorphOn_Icc_subset_of_isPreconnected
    [FiniteDimensional ℝ E] {P : Set E} (hP : IsPolyhedron P) (hconn : IsPreconnected P)
    {x y : E} (hx : x ∈ P) (hy : y ∈ P) (hne : x ≠ y) :
    ∃ γ : ℝ → E, IsPLHomeomorphOn γ (Icc 0 1) (γ '' Icc 0 1) ∧
      γ 0 = x ∧ γ 1 = y ∧ γ '' Icc 0 1 ⊆ P := by
  obtain ⟨K, hKfin, hKspace⟩ := hP.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  let q : Fin 2 → E := ![x, y]
  obtain ⟨L, hLK, hLfin, hLq⟩ := exists_isSubdivision_subcomplexes K
    (fun i : Fin 2 => ({q i} : Set E)) (fun _ => (isHPolytope_singleton _).isPolyhedron)
    (fun i => singleton_subset_iff.mpr (hKspace.symm ▸ by fin_cases i <;> assumption))
  let _ : Finite L.faces := hLfin.to_subtype
  have hLspace : L.space = P := hLK.space_eq.trans hKspace
  have hv (i : Fin 2) : q i ∈ L.vertices := by
    obtain ⟨s, ⟨hs, hsub⟩, -⟩ := mem_iUnion₂.mp ((hLq i).subset (mem_singleton (q i)))
    obtain ⟨v, hv⟩ := L.nonempty_of_mem_faces hs
    have heq : v = q i := hsub (subset_convexHull ℝ _ hv)
    rw [← heq]
    exact L.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  let a : L.vertices := ⟨x, hv 0⟩
  let b : L.vertices := ⟨y, hv 1⟩
  obtain ⟨p, hp⟩ := (edgeGraph_preconnected_of_isPreconnected_space L
    (hLspace.symm ▸ hconn)).exists_isPath a b
  have hpos : 0 < p.length := by
    by_contra h
    have heq := p.eq_of_length_eq_zero (Nat.eq_zero_of_not_pos h)
    exact hne (congrArg Subtype.val heq)
  obtain ⟨γ, hγ, hγ0, hγ1⟩ := exists_isPLHomeomorphOn_Icc_arcCarrier_of_isPath p hp hpos
  refine ⟨γ, ?_, hγ0, hγ1, ?_⟩
  · rw [hγ.image_eq]
    exact hγ
  · rw [hγ.image_eq, ← hLspace]
    exact pathCarrier_subset_space (arcPath p)

end DifferentialGeometry.Topology.PiecewiseLinear
