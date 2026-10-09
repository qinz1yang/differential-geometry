import DifferentialGeometry.Topology.ThreeManifold.CutCapMarkedGraphBridge
import DifferentialGeometry.Topology.ThreeManifold.CutCapCollaredQuotientGluing

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set TopologicalSpace Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology

universe u

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "Tube" => S2 × Set.Icc (-2 : ℝ) 2

local instance : Fact ((-2 : ℝ) < 2) := ⟨by norm_num⟩

namespace SphericalTubeSystem

variable {M : ClosedOrientedManifold.{u} 3} (T : SphericalTubeSystem M)

def tubeImage (a : T.Index) : Set M.Carrier := range (T.tube a)

def tubeRange : Set M.Carrier := ⋃ a, T.tubeImage a

theorem mem_tubeRange {x : M.Carrier} :
    x ∈ T.tubeRange ↔ ∃ (a : T.Index) (z : Tube), T.tube a z = x := by
  simp only [tubeRange, tubeImage, mem_iUnion, mem_range]

theorem removedBand_subset_tubeImage (a : T.Index) : T.removedBand a ⊆ T.tubeImage a := by
  rintro x ⟨z, -, rfl⟩
  exact mem_range_self _

theorem removedBand_subset_tubeRange (a : T.Index) : T.removedBand a ⊆ T.tubeRange :=
  (T.removedBand_subset_tubeImage a).trans (subset_iUnion T.tubeImage a)

theorem core_union_tubeRange : T.core ∪ T.tubeRange = univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  by_cases hx : x ∈ T.core
  · exact Or.inl hx
  · have hx' : x ∈ ⋃ a, T.removedBand a := by
      simpa only [SphericalTubeSystem.core, mem_compl_iff, not_not] using hx
    obtain ⟨a, ha⟩ := mem_iUnion.mp hx'
    exact Or.inr (T.removedBand_subset_tubeRange a ha)

theorem one_le_abs_of_notMem_removedBand {a : T.Index} {z : Tube}
    (hz : T.tube a z ∉ T.removedBand a) : 1 ≤ |(z.2 : ℝ)| := by
  by_contra h
  have habs : |(z.2 : ℝ)| < 1 := not_le.mp h
  rw [abs_lt] at habs
  exact hz ⟨z, habs, rfl⟩

theorem abs_lt_one_of_mem_removedBand {a : T.Index} {z : Tube}
    (hz : T.tube a z ∈ T.removedBand a) : |(z.2 : ℝ)| < 1 := by
  obtain ⟨z', hz', heq⟩ := hz
  have hzz : z' = z := (T.smooth a).isEmbedding.injective heq
  subst hzz
  rw [abs_lt]
  exact hz'

theorem mem_core_iff (x : M.Carrier) :
    x ∈ T.core ↔ ∀ (a : T.Index) (z : Tube), T.tube a z = x → 1 ≤ |(z.2 : ℝ)| := by
  constructor
  · intro hx a z hz
    by_contra h
    have habs : |(z.2 : ℝ)| < 1 := not_le.mp h
    rw [abs_lt] at habs
    exact hx (mem_iUnion.mpr ⟨a, ⟨z, habs, hz⟩⟩)
  · intro hx
    rw [SphericalTubeSystem.core, mem_compl_iff, mem_iUnion]
    rintro ⟨a, z, hz, heq⟩
    have h1 := hx a z heq
    have habs : |(z.2 : ℝ)| < 1 := by
      rw [abs_lt]
      exact hz
    linarith

theorem core_inter_tubeImage (a : T.Index) :
    T.core ∩ T.tubeImage a = T.tube a '' {z : Tube | 1 ≤ |(z.2 : ℝ)|} := by
  ext x
  constructor
  · rintro ⟨hx, z, rfl⟩
    exact ⟨z, (T.mem_core_iff _).mp hx a z rfl, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    refine ⟨(T.mem_core_iff _).mpr ?_, mem_range_self _⟩
    intro b w hw
    by_cases hb : b = a
    · rw [hb] at hw
      rw [(T.smooth a).isEmbedding.injective hw]
      exact hz
    · exact (Set.disjoint_left.mp (T.disjoint hb) (mem_range_self w)
        (hw ▸ mem_range_self z)).elim

theorem boundaryLevel_abs_one (b : Bool) :
    1 ≤ |((SphericalTubeSystem.boundaryLevel b : Set.Icc (-2 : ℝ) 2) : ℝ)| := by
  cases b <;> norm_num [SphericalTubeSystem.boundaryLevel]

theorem boundaryLevel_mem_band (b : Bool) :
    -1 ≤ ((SphericalTubeSystem.boundaryLevel b : Set.Icc (-2 : ℝ) 2) : ℝ) ∧
      ((SphericalTubeSystem.boundaryLevel b : Set.Icc (-2 : ℝ) 2) : ℝ) ≤ 1 := by
  cases b <;> norm_num [SphericalTubeSystem.boundaryLevel]

theorem boundarySphere_mem_tubeImage (b : T.Boundary) (z : S2) :
    T.boundarySphere b z ∈ T.tubeImage b.1 :=
  mem_range_self _

theorem boundarySphere_subset_core_tubeImage (b : T.Boundary) :
    range (T.boundarySphere b) ⊆ T.core ∩ T.tubeImage b.1 := by
  rintro x ⟨z, rfl⟩
  exact ⟨T.boundarySphere_mem_core b z, T.boundarySphere_mem_tubeImage b z⟩

def band (a : T.Index) : Set M.Carrier :=
  T.tube a '' {z : Tube | -1 ≤ (z.2 : ℝ) ∧ (z.2 : ℝ) ≤ 1}

def bandRange : Set M.Carrier := ⋃ a, T.band a

theorem band_subset_tubeImage (a : T.Index) : T.band a ⊆ T.tubeImage a := by
  rintro x ⟨z, -, rfl⟩
  exact mem_range_self _

theorem removedBand_subset_band (a : T.Index) : T.removedBand a ⊆ T.band a := by
  rintro x ⟨z, hz, rfl⟩
  exact ⟨z, ⟨le_of_lt hz.1, le_of_lt hz.2⟩, rfl⟩

theorem band_subset_tubeRange (a : T.Index) : T.band a ⊆ T.tubeRange :=
  (T.band_subset_tubeImage a).trans (subset_iUnion T.tubeImage a)

theorem core_union_bandRange : T.core ∪ T.bandRange = univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  by_cases hx : x ∈ T.core
  · exact Or.inl hx
  · have hx' : x ∈ ⋃ a, T.removedBand a := by
      simpa only [SphericalTubeSystem.core, mem_compl_iff, not_not] using hx
    obtain ⟨a, ha⟩ := mem_iUnion.mp hx'
    exact Or.inr (mem_iUnion.mpr ⟨a, T.removedBand_subset_band a ha⟩)

theorem eq_boundaryLevel_of_mem_band_of_mem_core {a : T.Index} {z : Tube}
    (hband : -1 ≤ (z.2 : ℝ) ∧ (z.2 : ℝ) ≤ 1) (hcore : T.tube a z ∈ T.core) :
    (z.2 : ℝ) = -1 ∨ (z.2 : ℝ) = 1 := by
  have h1 : 1 ≤ |(z.2 : ℝ)| := (T.mem_core_iff _).mp hcore a z rfl
  have h2 : |(z.2 : ℝ)| ≤ 1 := abs_le.mpr hband
  have h3 : |(z.2 : ℝ)| = 1 := le_antisymm h2 h1
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp h3 with h | h
  · exact Or.inr h
  · exact Or.inl h

theorem boundarySphere_mem_band (a : T.Index) (b : Bool) (z : S2) :
    T.boundarySphere (a, b) z ∈ T.band a :=
  ⟨(z, SphericalTubeSystem.boundaryLevel b),
    SphericalTubeSystem.boundaryLevel_mem_band b,
    rfl⟩

theorem core_inter_band (a : T.Index) :
    T.core ∩ T.band a =
      range (T.boundarySphere (a, false)) ∪ range (T.boundarySphere (a, true)) := by
  ext x
  constructor
  · rintro ⟨hx, z, hz, rfl⟩
    rcases T.eq_boundaryLevel_of_mem_band_of_mem_core hz hx with h | h
    · refine Or.inl ⟨z.1, ?_⟩
      have hzT : z = (z.1, SphericalTubeSystem.boundaryLevel false) :=
        Prod.ext rfl (Subtype.ext (by simpa [SphericalTubeSystem.boundaryLevel] using h))
      rw [SphericalTubeSystem.boundarySphere, ContinuousMap.comp_apply]
      exact (congrArg (T.tube a) hzT).symm
    · refine Or.inr ⟨z.1, ?_⟩
      have hzT : z = (z.1, SphericalTubeSystem.boundaryLevel true) :=
        Prod.ext rfl (Subtype.ext (by simpa [SphericalTubeSystem.boundaryLevel] using h))
      rw [SphericalTubeSystem.boundarySphere, ContinuousMap.comp_apply]
      exact (congrArg (T.tube a) hzT).symm
  · rintro (⟨z, rfl⟩ | ⟨z, rfl⟩)
    · exact ⟨T.boundarySphere_mem_core (a, false) z, T.boundarySphere_mem_band a false z⟩
    · exact ⟨T.boundarySphere_mem_core (a, true) z, T.boundarySphere_mem_band a true z⟩

theorem core_inter_bandRange : T.core ∩ T.bandRange = ⋃ b : T.Boundary, range (T.boundarySphere b) := by
  rw [bandRange, Set.inter_iUnion]
  ext x
  simp only [mem_iUnion]
  constructor
  · rintro ⟨a, hx⟩
    rw [core_inter_band] at hx
    rcases hx with hx | hx
    · exact ⟨(a, false), hx⟩
    · exact ⟨(a, true), hx⟩
  · rintro ⟨b, hx⟩
    obtain ⟨a, side⟩ := b
    refine ⟨a, ?_⟩
    rw [core_inter_band]
    cases side
    · exact Or.inl hx
    · exact Or.inr hx

end SphericalTubeSystem

namespace SphericalCapping

variable {M N : ClosedOrientedManifold.{u} 3} {T : SphericalTubeSystem M}
  (C : SphericalCapping M N T)

theorem iUnion_range_cap_eq_iUnion_index :
    (⋃ b : T.Boundary, range (C.cap b)) =
      ⋃ a : T.Index, (range (C.cap (a, false)) ∪ range (C.cap (a, true))) := by
  ext x
  simp only [mem_iUnion, mem_union]
  constructor
  · rintro ⟨⟨a, side⟩, h⟩
    cases side
    · exact ⟨a, Or.inl h⟩
    · exact ⟨a, Or.inr h⟩
  · rintro ⟨a, h | h⟩
    · exact ⟨(a, false), h⟩
    · exact ⟨(a, true), h⟩

theorem capRange_inter_coreRange (b : T.Boundary) :
    range (C.cap b) ∩ range C.coreInclusion =
      range (C.coreInclusion.comp (T.coreBoundarySphere b)) := by
  rw [Set.inter_comm]
  exact C.core_cap_intersection b

theorem capBoundaryRange_eq_coreBoundaryRange (b : T.Boundary) :
    range (fun z : S2 => C.cap b (sphereToClosedCell z)) =
      range (fun z : S2 => C.coreInclusion (T.coreBoundarySphere b z)) := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨(C.attaching b) z, (C.boundary_eq b z).symm⟩
  · rintro ⟨w, rfl⟩
    refine ⟨(C.attaching b).symm w, ?_⟩
    change C.cap b (sphereToClosedCell ((C.attaching b).symm w)) =
      C.coreInclusion (T.coreBoundarySphere b w)
    rw [C.boundary_eq b ((C.attaching b).symm w), Diffeomorph.apply_symm_apply]

theorem capRange_subset_coreRange_union_capRange (b : T.Boundary) :
    range (C.cap b) ⊆ range C.coreInclusion ∪ ⋃ b' : T.Boundary, range (C.cap b') :=
  fun _ hx => Or.inr (mem_iUnion.mpr ⟨b, hx⟩)

def openCapRange (b : T.Boundary) : Set N.Carrier := range (C.cap b) \ range C.coreInclusion

theorem openCapRange_subset_capRange (b : T.Boundary) :
    C.openCapRange b ⊆ range (C.cap b) :=
  Set.sdiff_subset

theorem openCapRange_eq_capRange_diff_capBoundaryRange (b : T.Boundary) :
    C.openCapRange b = range (C.cap b) \
      range (fun z : S2 => C.cap b (sphereToClosedCell z)) := by
  have hboundary : range (fun z : S2 => C.cap b (sphereToClosedCell z)) =
      range (fun z : S2 => C.coreInclusion (T.coreBoundarySphere b z)) :=
    C.capBoundaryRange_eq_coreBoundaryRange b
  have hinter : range C.coreInclusion ∩ range (C.cap b) =
      range (fun z : S2 => C.coreInclusion (T.coreBoundarySphere b z)) := by
    simpa only [ContinuousMap.coe_comp, Function.comp_def] using C.core_cap_intersection b
  ext x
  rw [openCapRange, Set.mem_sdiff, Set.mem_sdiff, hboundary, ← hinter, Set.mem_inter_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h3 => h2 h3.1⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h3 => h2 ⟨h3, h1⟩⟩

theorem iUnion_openCapRange_eq_compl_coreRange :
    (⋃ b : T.Boundary, C.openCapRange b) = (range C.coreInclusion)ᶜ := by
  ext x
  rw [mem_iUnion]
  constructor
  · rintro ⟨b, hb⟩
    rw [openCapRange, Set.mem_sdiff] at hb
    exact hb.2
  · intro hx
    have hxu : x ∈ range C.coreInclusion ∪ ⋃ b : T.Boundary, range (C.cap b) := by
      rw [C.exhaustive]
      trivial
    rcases hxu with h | h
    · exact absurd h hx
    · obtain ⟨b, hb⟩ := mem_iUnion.mp h
      exact ⟨b, by rw [openCapRange, Set.mem_sdiff]; exact ⟨hb, hx⟩⟩

theorem disjoint_coreRange_iUnion_openCapRange :
    Disjoint (range C.coreInclusion) (⋃ b : T.Boundary, C.openCapRange b) := by
  rw [C.iUnion_openCapRange_eq_compl_coreRange]
  exact Set.disjoint_left.mpr fun x hx hx' => hx' hx

theorem coreRange_union_iUnion_openCapRange_eq_univ :
    range C.coreInclusion ∪ (⋃ b : T.Boundary, C.openCapRange b) = univ := by
  rw [C.iUnion_openCapRange_eq_compl_coreRange, Set.union_compl_self]

theorem pairwiseDisjoint_openCapRange : Pairwise (Disjoint on C.openCapRange) := by
  intro b b' hne
  exact (C.cap_disjoint hne).mono (C.openCapRange_subset_capRange b)
    (C.openCapRange_subset_capRange b')

theorem capRange_subset_coreRange_union_openCapRange (b : T.Boundary) :
    range (C.cap b) ⊆ range C.coreInclusion ∪ ⋃ b' : T.Boundary, C.openCapRange b' := by
  rw [C.coreRange_union_iUnion_openCapRange_eq_univ]
  exact subset_univ _

theorem exists_openCapRange_of_notMem_coreRange {x : N.Carrier} (hx : x ∉ range C.coreInclusion) :
    ∃ b : T.Boundary, x ∈ C.openCapRange b := by
  have h : (⋃ b : T.Boundary, C.openCapRange b) = (range C.coreInclusion)ᶜ :=
    C.iUnion_openCapRange_eq_compl_coreRange
  exact mem_iUnion.mp (h ▸ hx)

end SphericalCapping

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

private theorem coe_transport_symm {v v' : ConnectedComponents E.capped.Carrier} (h : v = v')
    (y : (E.capped.component v').Carrier) :
    (h.symm ▸ y : (E.capped.component v).Carrier).val = y.val := by
  cases h
  rfl

private theorem coefficient_val_cutCapMarkedGraph (K : E.CutCapNeighborhoodFamily)
    (e : ULift.{u, 0} E.tubes.Index) (side : Bool) {v : ConnectedComponents E.capped.Carrier}
    (hv : (E.cutCapMarkedGraph K).endpoint e side = v)
    (y : ((E.cutCapMarkedGraph K).vertexManifold v).Carrier) :
    ((hv.symm ▸ y :
        ((E.cutCapMarkedGraph K).vertexManifold
          ((E.cutCapMarkedGraph K).endpoint e side)).Carrier)).val = y.val := by
  cases hv
  rfl

private theorem mem_range_flag_ball_cutCapMarkedGraph (K : E.CutCapNeighborhoodFamily)
    (e : ULift.{u, 0} E.tubes.Index) (side : Bool)
    (z : ((E.cutCapMarkedGraph K).vertexManifold
      ((E.cutCapMarkedGraph K).endpoint e side)).Carrier) :
    z ∈ range ((E.cutCapMarkedGraph K).flag e side).ball ↔
      z.val ∈ range (E.capping.cap (e.down, side)) := by
  constructor
  · rintro ⟨x, rfl⟩
    rw [E.cutCapMarkedGraph_flag_ball K e side x]
    exact mem_range_self _
  · rintro ⟨x, hx⟩
    refine ⟨x, ?_⟩
    rw [E.cutCapMarkedGraph_flag_ball K e side x]
    exact Subtype.ext hx

private theorem mem_range_flag_ball_comp_sphereToClosedCell_cutCapMarkedGraph
    (K : E.CutCapNeighborhoodFamily) (e : ULift.{u, 0} E.tubes.Index) (side : Bool)
    (z : ((E.cutCapMarkedGraph K).vertexManifold
      ((E.cutCapMarkedGraph K).endpoint e side)).Carrier) :
    z ∈ range (((E.cutCapMarkedGraph K).flag e side).ball ∘ sphereToClosedCell) ↔
      z.val ∈ range (fun z' : S2 => E.capping.cap (e.down, side) (sphereToClosedCell z')) := by
  constructor
  · rintro ⟨x, hx⟩
    exact ⟨x, by
      rw [← hx]
      exact (congrArg Subtype.val (E.cutCapMarkedGraph_flag_ball K e side
        (sphereToClosedCell x))).symm⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, Subtype.ext (by
      simpa only [Function.comp_apply, E.cutCapMarkedGraph_flag_ball K e side
        (sphereToClosedCell x), Subtype.coe_mk] using hx)⟩

private theorem mem_flagInterior_cutCapMarkedGraph (K : E.CutCapNeighborhoodFamily)
    (e : ULift.{u, 0} E.tubes.Index) (side : Bool)
    (z : ((E.cutCapMarkedGraph K).vertexManifold
      ((E.cutCapMarkedGraph K).endpoint e side)).Carrier) :
    z ∈ range ((E.cutCapMarkedGraph K).flag e side).ball \
        range (((E.cutCapMarkedGraph K).flag e side).ball ∘ sphereToClosedCell) ↔
      z.val ∈ E.capping.openCapRange (e.down, side) := by
  simp only [Set.mem_sdiff, mem_range_flag_ball_cutCapMarkedGraph E K e side z,
    mem_range_flag_ball_comp_sphereToClosedCell_cutCapMarkedGraph E K e side z,
    SphericalCapping.openCapRange_eq_capRange_diff_capBoundaryRange E.capping (e.down, side)]

theorem mem_removedBallSet_cutCapMarkedGraph_iff (K : E.CutCapNeighborhoodFamily)
    (S : Finset (ULift.{u, 0} E.tubes.Index)) (v : (E.cutCapMarkedGraph K).Vertex)
    (y : ((E.cutCapMarkedGraph K).vertexManifold v).Carrier) :
    y ∈ (E.cutCapMarkedGraph K).removedBallSet S v ↔
      ∃ (a : E.tubes.Index) (side : Bool), ULift.up a ∈ S ∧ y.val ∈ E.capping.openCapRange (a, side) := by
  constructor
  · rintro ⟨e, he, side, hv, hmem⟩
    have hmem1 : (hv.symm ▸ y) ∈ range ((E.cutCapMarkedGraph K).flag e side).ball \
        range (((E.cutCapMarkedGraph K).flag e side).ball ∘ sphereToClosedCell) :=
      (MarkedManifoldGraph.mem_flagInterior_cast_iff (E.cutCapMarkedGraph K) e side v hv y).mp hmem
    have hmem2 : ((hv.symm ▸ y) :
        ((E.cutCapMarkedGraph K).vertexManifold
          ((E.cutCapMarkedGraph K).endpoint e side)).Carrier).val ∈
        E.capping.openCapRange (e.down, side) :=
      (mem_flagInterior_cutCapMarkedGraph E K e side (hv.symm ▸ y)).mp hmem1
    exact ⟨e.down, side, he, coefficient_val_cutCapMarkedGraph E K e side hv y ▸ hmem2⟩
  · rintro ⟨a, side, hS, hmem⟩
    have hsub : y.val ∈ ClosedOrientedManifold.componentSet E.capped (E.cutCapVertex a side) :=
      E.capRange_subset_componentSet a side
        (E.capping.openCapRange_subset_capRange (a, side) hmem)
    have hv : E.cutCapVertex a side = v := by
      have hmk : ConnectedComponents.mk y.val = E.cutCapVertex a side := by
        rw [← ClosedOrientedManifold.mem_componentSet]
        exact hsub
      exact hmk.symm.trans y.2
    have hv' : (E.cutCapMarkedGraph K).endpoint (ULift.up a) side = v := by
      rw [E.cutCapMarkedGraph_endpoint]
      exact hv
    refine ⟨ULift.up a, hS, side, hv', ?_⟩
    have hmem' : ((hv'.symm ▸ y) :
        ((E.cutCapMarkedGraph K).vertexManifold
          ((E.cutCapMarkedGraph K).endpoint (ULift.up a) side)).Carrier).val ∈
        E.capping.openCapRange (a, side) :=
      (coefficient_val_cutCapMarkedGraph E K (ULift.up a) side hv' y).symm ▸ hmem
    have hflag : (hv'.symm ▸ y) ∈ range ((E.cutCapMarkedGraph K).flag (ULift.up a) side).ball \
        range (((E.cutCapMarkedGraph K).flag (ULift.up a) side).ball ∘ sphereToClosedCell) :=
      (mem_flagInterior_cutCapMarkedGraph E K (ULift.up a) side (hv'.symm ▸ y)).mpr hmem'
    exact (MarkedManifoldGraph.mem_flagInterior_cast_iff
      (E.cutCapMarkedGraph K) (ULift.up a) side v hv' y).mpr hflag

theorem mem_removedBallSet_singleton_cutCapMarkedGraph (K : E.CutCapNeighborhoodFamily)
    (e : (E.cutCapMarkedGraph K).Edge) (v : (E.cutCapMarkedGraph K).Vertex)
    (y : ((E.cutCapMarkedGraph K).vertexManifold v).Carrier) :
    y ∈ (E.cutCapMarkedGraph K).removedBallSet ({e} : Finset (E.cutCapMarkedGraph K).Edge) v ↔
      y.val ∈ E.capping.openCapRange (e.down, false) ∨
        y.val ∈ E.capping.openCapRange (e.down, true) := by
  constructor
  · intro h
    obtain ⟨a, side, hmem, hx⟩ := (mem_removedBallSet_cutCapMarkedGraph_iff E K {e} v y).mp h
    have ha : a = e.down := ULift.up_injective (by
      rw [Finset.mem_singleton.mp hmem]
      exact (ULift.up_down e).symm)
    subst ha
    rcases side with _ | _
    · exact Or.inl hx
    · exact Or.inr hx
  · rintro (h | h)
    · exact (mem_removedBallSet_cutCapMarkedGraph_iff E K {e} v y).mpr
        ⟨e.down, false, Finset.mem_singleton_self _, h⟩
    · exact (mem_removedBallSet_cutCapMarkedGraph_iff E K {e} v y).mpr
        ⟨e.down, true, Finset.mem_singleton_self _, h⟩

theorem notMem_removedBallSet_univ_cutCapMarkedGraph (K : E.CutCapNeighborhoodFamily)
    (v : (E.cutCapMarkedGraph K).Vertex)
    (y : ((E.cutCapMarkedGraph K).vertexManifold v).Carrier) :
    y ∉ (E.cutCapMarkedGraph K).removedBallSet Finset.univ v ↔
      y.val ∈ range E.capping.coreInclusion := by
  have hcompl : y.val ∈ range E.capping.coreInclusion ↔
      y.val ∉ ⋃ b : E.tubes.Boundary, E.capping.openCapRange b := by
    rw [E.capping.iUnion_openCapRange_eq_compl_coreRange, mem_compl_iff, not_not]
  constructor
  · intro hy
    refine hcompl.mpr fun hmem => hy ?_
    obtain ⟨b, hb⟩ := mem_iUnion.mp hmem
    obtain ⟨a, side⟩ := b
    exact (mem_removedBallSet_cutCapMarkedGraph_iff E K Finset.univ v y).mpr
      ⟨a, side, Finset.mem_univ _, hb⟩
  · intro hy h
    obtain ⟨a, side, -, hx⟩ :=
      (mem_removedBallSet_cutCapMarkedGraph_iff E K Finset.univ v y).mp h
    exact (hcompl.mp hy) (mem_iUnion.mpr ⟨(a, side), hx⟩)

end SphericalCutCapTransition

namespace SphericalTubeSystem

variable {M : ClosedOrientedManifold.{u} 3} (T : SphericalTubeSystem M)

theorem tubeImage_nonempty (a : T.Index) : (T.tubeImage a).Nonempty :=
  ⟨T.tube a (sphereBasePoint, ⟨0, by norm_num⟩), mem_range_self _⟩

theorem band_nonempty (a : T.Index) : (T.band a).Nonempty :=
  ⟨T.tube a (sphereBasePoint, ⟨0, by norm_num⟩),
    ⟨(sphereBasePoint, ⟨0, by norm_num⟩), ⟨by norm_num, by norm_num⟩, rfl⟩⟩

theorem core_nonempty_of_boundary (b : T.Boundary) : T.core.Nonempty :=
  ⟨T.boundarySphere b sphereBasePoint, T.boundarySphere_mem_core b sphereBasePoint⟩

theorem bandRange_eq_empty_of_isEmpty_index [IsEmpty T.Index] : T.bandRange = ∅ := by
  rw [bandRange, Set.iUnion_eq_empty]
  exact fun a => isEmptyElim a

theorem tubeRange_eq_empty_of_isEmpty_index [IsEmpty T.Index] : T.tubeRange = ∅ := by
  rw [tubeRange, Set.iUnion_eq_empty]
  exact fun a => isEmptyElim a

end SphericalTubeSystem

namespace SphericalCutCapTransition

variable {M Q : ClosedOrientedManifold.{u} 3} (E : SphericalCutCapTransition M Q)

structure CutCapTubeGluingStep (K : E.CutCapNeighborhoodFamily)
    (Z : ConnectedClosedOrientedManifold.{u} 3) where
  step : ∀ (S : Finset (ULift.{u, 0} E.tubes.Index))
    (P : PartialRealization (E.cutCapMarkedGraph K) S) (e : ULift.{u, 0} E.tubes.Index),
    e ∉ S → P.IsBlockInvariant Z →
      ∃ D : PartialRealization.StepAssemblyData (E.cutCapMarkedGraph K) S e,
        (D.partialRealization).FlagCovered e ∧
          (D.partialRealization).componentCorrespondence ∧
          (D.partialRealization).HasBlockPresentation Z

theorem collaredQuotientStep_of_cutCapTubeGluingStep (K : E.CutCapNeighborhoodFamily)
    {Z : ConnectedClosedOrientedManifold.{u} 3} (h : E.CutCapTubeGluingStep K Z) :
    CollaredQuotientStep (E.cutCapMarkedGraph K) Z :=
  ⟨fun S P e he hP => by
    obtain ⟨D, hcover, hcorr, hpres⟩ := h.step S P e he hP
    exact ⟨D.partialRealization, hcover, D.partialRealization_seamEquation, hcorr, hpres⟩⟩

theorem hasRealizationStep_of_cutCapTubeGluingStep (K : E.CutCapNeighborhoodFamily)
    {Z : ConnectedClosedOrientedManifold.{u} 3} (h : E.CutCapTubeGluingStep K Z) :
    HasRealizationStep (E.cutCapMarkedGraph K) Z :=
  hasRealizationStep_of_collaredQuotientStep
    (E.collaredQuotientStep_of_cutCapTubeGluingStep K h)

theorem blockStepLaw_of_cutCapTubeGluingStep (K : E.CutCapNeighborhoodFamily)
    {Z : ConnectedClosedOrientedManifold.{u} 3} (h : E.CutCapTubeGluingStep K Z) :
    BlockStepLaw (E.cutCapMarkedGraph K) Z :=
  blockStepLaw_of_collaredQuotientStep_of_initial
    (E.exists_cutCapEmptyRealization_blockInvariant K Z)
    (E.collaredQuotientStep_of_cutCapTubeGluingStep K h)

theorem nonempty_cutCapTubeGluingStep_of_isEmpty_index (K : E.CutCapNeighborhoodFamily)
    (Z : ConnectedClosedOrientedManifold.{u} 3) [IsEmpty E.tubes.Index] :
    Nonempty (E.CutCapTubeGluingStep K Z) := by
  have hEdge : IsEmpty (E.cutCapMarkedGraph K).Edge :=
    ⟨fun e => isEmptyElim (e : ULift.{u, 0} E.tubes.Index).down⟩
  exact ⟨⟨fun S P e _ _ => (hEdge.false e).elim⟩⟩

theorem nonempty_cutCapMarkedGraph_edge_iff (K : E.CutCapNeighborhoodFamily) :
    Nonempty (E.cutCapMarkedGraph K).Edge ↔ Nonempty E.tubes.Index :=
  ⟨fun ⟨e⟩ => ⟨(e : ULift.{u, 0} E.tubes.Index).down⟩, fun ⟨a⟩ => ⟨ULift.up a⟩⟩

theorem core_and_band_nonempty_of_nonempty_index [Nonempty E.tubes.Index] :
    E.tubes.core.Nonempty ∧ ∃ a : E.tubes.Index, (E.tubes.band a).Nonempty := by
  obtain ⟨a⟩ := (inferInstance : Nonempty E.tubes.Index)
  exact ⟨E.tubes.core_nonempty_of_boundary (a, false), a, E.tubes.band_nonempty a⟩

end SphericalCutCapTransition

end DifferentialGeometry.Topology
