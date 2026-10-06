import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBoundaryCollar
import DifferentialGeometry.Topology.ThreeManifold.TorusCut.Decomposition

/-!
# CH12-S34 G2: restriction of a smooth lift of the thin collar to one piece

`cuspDomain` is preconnected, so a smooth map `L : cuspDomain → C` into a compact carrier meeting the
clopen piece `D.piece j` lands in it; the corestriction to `GC.Topology.componentCarrier C D j` is smooth.
-/

set_option autoImplicit false

noncomputable section

open Set TopologicalSpace DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
  GC.Endpoint DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff

namespace GC.LongTime.Ch12

universe u

theorem halfSpaceOneLift_coord_S34 (p : EuclideanHalfSpace 1) :
    halfSpaceOneLift (p.1 0) = p := by
  rw [halfSpaceOneLift_eq]
  have heq : (⟨max 0 (p.1 0), le_max_left 0 (p.1 0)⟩ : Ici (0 : ℝ)) =
      halfSpaceOneHomeomorph p := Subtype.ext (max_eq_right p.2)
  rw [heq]
  exact halfSpaceOneHomeomorph.symm_apply_apply p

theorem isPreconnected_cuspDomain_S34 : IsPreconnected cuspDomain := by
  have hS : IsPreconnected ((univ : Set GC.Endpoint.Torus) ×ˢ Ico (0 : ℝ) 100) :=
    isPreconnected_univ.prod isPreconnected_Ico
  have hcont : ContinuousOn
      (fun q : GC.Endpoint.Torus × ℝ => ((q.1, halfSpaceOneLift q.2) : CuspHalfSpace))
      ((univ : Set GC.Endpoint.Torus) ×ˢ Ico (0 : ℝ) 100) := by
    refine continuousOn_fst.prodMk ?_
    exact contMDiffOn_halfSpaceOneLift.continuousOn.comp continuousOn_snd
      (fun q hq => (mem_Ico.mp hq.2).1)
  have himg := hS.image _ hcont
  convert himg using 1
  ext p
  constructor
  · intro hp
    refine ⟨(p.1, p.2.1 0), ⟨mem_univ _, p.2.2, hp⟩, ?_⟩
    exact Prod.ext rfl (halfSpaceOneLift_coord_S34 p.2)
  · rintro ⟨q, ⟨-, hq0, hq1⟩, rfl⟩
    change max q.2 0 < 100
    exact max_lt hq1 (by norm_num)

/-- Corestriction of a smooth map to a (clopen) piece of a compact carrier. -/
theorem exists_pieceLift_S34 {C : CompactCarrier.{u}} (D : C.Components) (j : Fin D.count)
    (L : CuspHalfSpace → C.Carrier) (hL : ContMDiffOn halfCollarModel C.model ∞ L cuspDomain)
    (q₀ : CuspHalfSpace) (hq₀ : q₀ ∈ cuspDomain) (hq₀j : L q₀ ∈ D.piece j) :
    ∃ L' : CuspHalfSpace → (GC.Topology.componentCarrier C D j).Carrier,
      (∀ p ∈ cuspDomain, (L' p).val = L p) ∧
      ContMDiffOn halfCollarModel (GC.Topology.componentCarrier C D j).model ∞ L' cuspDomain := by
  classical
  have hmem : ∀ p ∈ cuspDomain, L p ∈ D.piece j := by
    have hpre : IsPreconnected (L '' cuspDomain) :=
      isPreconnected_cuspDomain_S34.image L hL.continuousOn
    have hsub : L '' cuspDomain ⊆ (D.piece j : Set C.Carrier) :=
      IsPreconnected.subset_left_of_subset_union (D.piece j).isOpen (D.closed j).isOpen_compl
        disjoint_compl_right (by rw [union_compl_self]; exact subset_univ _)
        ⟨L q₀, ⟨q₀, hq₀, rfl⟩, hq₀j⟩ hpre
    intro p hp
    exact hsub ⟨p, hp, rfl⟩
  have hq₀j' : L q₀ ∈ (D.piece j : Set C.Carrier) := hq₀j
  refine ⟨fun p => if h : L p ∈ (D.piece j : Set C.Carrier) then ⟨L p, h⟩ else ⟨L q₀, hq₀j'⟩,
    fun p hp => ?_, fun p hp => ?_⟩
  · exact congrArg Subtype.val (dite_eq_left (hmem p hp))
  · refine (ContMDiffWithinAt.subtypeVal_comp_iff (I := halfCollarModel) (I' := C.model)
      (D.piece j) _ cuspDomain p).mp ?_
    refine (hL p hp).congr (fun q hq => ?_) ?_
    · exact congrArg Subtype.val (dite_eq_left (hmem q hq))
    · exact congrArg Subtype.val (dite_eq_left (hmem p hp))

end GC.LongTime.Ch12
