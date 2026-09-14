import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ChildCarrierCollaredStarCover
import DifferentialGeometry.Topology.ClosedCover
import DifferentialGeometry.Topology.ClosedBall.RadialShell

noncomputable section

open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace SmoothCutCapTransition

variable {P Q D N : OrientedThreeStage.{u}} (E : SmoothCutCapTransition P Q D N)

private theorem childSeamSphere_eq_childCap (c : ConnectedComponents Q.Carrier)
    (b : E.ChildCapBoundary c) (y : Sphere 2) :
    E.childSeamSphere c b y = E.childCap c b (sphereToThreeBall y) :=
  (E.childCap_boundary_eq c b y).symm

theorem childSeamSphere_isEmbedding (c : ConnectedComponents Q.Carrier)
    (b : E.ChildCapBoundary c) : _root_.Topology.IsEmbedding (E.childSeamSphere c b) := by
  have hs : _root_.Topology.IsEmbedding sphereToThreeBall := by
    apply _root_.Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
    exact _root_.Topology.IsEmbedding.subtypeVal
  have hEq : (E.childSeamSphere c b : Sphere 2 → E.ChildCarrier c) =
      E.childCap c b ∘ sphereToThreeBall :=
    funext (fun y => (E.childCap_boundary_eq c b y).symm)
  rw [hEq]
  exact (E.childCap_isEmbedding c b).comp hs

theorem childSeamSphere_isClosedEmbedding (c : ConnectedComponents Q.Carrier)
    (b : E.ChildCapBoundary c) : _root_.Topology.IsClosedEmbedding (E.childSeamSphere c b) :=
  (E.childSeamSphere c b).continuous.isClosedEmbedding (E.childSeamSphere_isEmbedding c b).injective

theorem range_childCoreInclusion_inter_range_childCap (c : ConnectedComponents Q.Carrier)
    (b : E.ChildCapBoundary c) :
    Set.range (E.childCoreInclusion c) ∩ Set.range (E.childCap c b) =
      Set.range (E.childSeamSphere c b) := by
  apply Set.Subset.antisymm
  · rintro x ⟨⟨k, hk⟩, ⟨z, hz⟩⟩
    have hpres : E.trace.presentation (E.trace.capping.coreInclusion k.1) =
        E.trace.presentation (E.trace.capping.cap b.1 z) := by
      rw [E.childCoreInclusionFun_eq c k, E.childCapFun_eq c b z]
      exact congrArg Sum.inl (congrArg Subtype.val (hk.trans hz.symm))
    have hcap : E.trace.capping.coreInclusion k.1 = E.trace.capping.cap b.1 z :=
      E.trace.presentation.injective hpres
    have hmem : E.trace.capping.cap b.1 z ∈
        Set.range E.trace.capping.coreInclusion ∩ Set.range (E.trace.capping.cap b.1) :=
      ⟨⟨k.1, hcap⟩, ⟨z, rfl⟩⟩
    rw [E.trace.capping.core_cap_intersection b.1] at hmem
    obtain ⟨y, hy⟩ := hmem
    refine ⟨(E.trace.capping.attaching b.1).symm y, ?_⟩
    rw [E.childSeamSphere_eq_childCap]
    have hcap' : E.trace.capping.cap b.1
        (sphereToThreeBall ((E.trace.capping.attaching b.1).symm y)) =
      E.trace.capping.cap b.1 z := by
      rw [E.trace.capping.boundary_eq, Homeomorph.apply_symm_apply]
      exact hy
    rw [(E.trace.capping.capEmbedding b.1).injective hcap']
    exact hz
  · rintro _ ⟨y, rfl⟩
    refine ⟨⟨E.childCapSeam c b y, rfl⟩, ?_⟩
    exact ⟨sphereToThreeBall y, (E.childCap_boundary_eq c b y)⟩

def childCoreNeighborhood (c : ConnectedComponents Q.Carrier) (r : ℝ) :
    Set (E.ChildCarrier c) :=
  (⋃ b : E.ChildCapBoundary c, E.childCap c b '' {x : ThreeBall | ‖x.1‖ ≤ r})ᶜ

theorem isOpen_childCoreNeighborhood (c : ConnectedComponents Q.Carrier) (r : ℝ) :
    IsOpen (E.childCoreNeighborhood c r) := by
  have hc : IsClosed (⋃ b : E.ChildCapBoundary c,
      E.childCap c b '' {x : ThreeBall | ‖x.1‖ ≤ r}) := by
    apply isClosed_iUnion_of_finite
    intro b
    have hk : IsCompact {x : ThreeBall | ‖x.1‖ ≤ r} :=
      (isClosed_le (continuous_norm.comp continuous_subtype_val) continuous_const).isCompact
    exact (hk.image (E.childCap c b).continuous).isClosed
  exact hc.isOpen_compl

theorem range_childCoreInclusion_subset_childCoreNeighborhood
    (c : ConnectedComponents Q.Carrier) {r : ℝ} (hr : r < 1) :
    Set.range (E.childCoreInclusion c) ⊆ E.childCoreNeighborhood c r := by
  intro x hx hnot
  obtain ⟨b, z, hz, hzx⟩ := Set.mem_iUnion.mp hnot
  have hs : x ∈ Set.range (E.childSeamSphere c b) := by
    rw [← E.range_childCoreInclusion_inter_range_childCap]
    exact ⟨hx, ⟨z, hzx⟩⟩
  obtain ⟨y, hy⟩ := hs
  have heq : sphereToThreeBall y = z := by
    apply (E.childCap_isEmbedding c b).injective
    rw [E.childCap_boundary_eq c b y]
    exact hy.trans hzx.symm
  have hn : ‖z.1‖ = 1 := by
    rw [← heq]
    exact norm_eq_of_mem_sphere y
  exact (not_le_of_gt hr) (hn ▸ hz)

theorem childCap_mem_childCoreNeighborhood_iff (c : ConnectedComponents Q.Carrier)
    (b : E.ChildCapBoundary c) (r : ℝ) (x : ThreeBall) :
    E.childCap c b x ∈ E.childCoreNeighborhood c r ↔ r < ‖x.1‖ := by
  constructor
  · intro h
    by_contra hn
    exact h (Set.mem_iUnion.mpr ⟨b, x, le_of_not_gt hn, rfl⟩)
  · intro hx h
    obtain ⟨b', x', hx', heq⟩ := Set.mem_iUnion.mp h
    by_cases hb : b' = b
    · subst b'
      have hxx : x' = x := (E.childCap_isEmbedding c b).injective heq
      exact not_le_of_gt hx (hxx ▸ hx')
    · exact Set.disjoint_left.mp (E.disjoint_range_childCap hb)
        ⟨x', heq⟩ (Set.mem_range_self x)

theorem childCoreNeighborhood_union_iUnion_range_childCap
    (c : ConnectedComponents Q.Carrier) (r : ℝ) :
    E.childCoreNeighborhood c r ∪
      (⋃ b : E.ChildCapBoundary c, Set.range (E.childCap c b)) = univ := by
  apply Set.eq_univ_of_forall
  intro x
  by_cases hx : x ∈ E.childCoreNeighborhood c r
  · exact Or.inl hx
  · right
    have hx' : x ∈ ⋃ b : E.ChildCapBoundary c,
        E.childCap c b '' {z : ThreeBall | ‖z.1‖ ≤ r} := by
      simpa only [childCoreNeighborhood, Set.mem_compl_iff, not_not] using hx
    obtain ⟨b, z, _, hzx⟩ := Set.mem_iUnion.mp hx'
    exact Set.mem_iUnion.mpr ⟨b, z, hzx⟩

private def childCapShellMap (c : ConnectedComponents Q.Carrier) (b : E.ChildCapBoundary c) (r : ℝ) :
    C({x : ThreeBall | r < ‖x.1‖},
      {x : E.childCoreNeighborhood c r | x.1 ∈ Set.range (E.childCap c b)}) where
  toFun x := ⟨⟨E.childCap c b x.1,
    (E.childCap_mem_childCoreNeighborhood_iff c b r x.1).mpr x.2⟩, ⟨x.1, rfl⟩⟩
  continuous_toFun :=
    (((E.childCap c b).continuous.comp continuous_subtype_val).subtype_mk _).subtype_mk _

private theorem childCapShellMap_isEmbedding (c : ConnectedComponents Q.Carrier)
    (b : E.ChildCapBoundary c) (r : ℝ) :
    _root_.Topology.IsEmbedding (E.childCapShellMap c b r) := by
  apply _root_.Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
  apply _root_.Topology.IsEmbedding.subtypeVal.of_comp_iff.mp
  exact (E.childCap_isEmbedding c b).comp _root_.Topology.IsEmbedding.subtypeVal

private theorem childCapShellMap_surjective (c : ConnectedComponents Q.Carrier)
    (b : E.ChildCapBoundary c) (r : ℝ) :
    Function.Surjective (E.childCapShellMap c b r) := by
  intro x
  obtain ⟨z, hz⟩ := x.2
  have hm : E.childCap c b z ∈ E.childCoreNeighborhood c r := hz ▸ x.1.2
  refine ⟨⟨z, (E.childCap_mem_childCoreNeighborhood_iff c b r z).mp hm⟩, ?_⟩
  exact Subtype.ext (Subtype.ext hz)

def childCapShellHomeomorph (c : ConnectedComponents Q.Carrier) (b : E.ChildCapBoundary c) (r : ℝ) :
    {x : ThreeBall | r < ‖x.1‖} ≃ₜ
      {x : E.childCoreNeighborhood c r | x.1 ∈ Set.range (E.childCap c b)} :=
  (E.childCapShellMap_isEmbedding c b r).toHomeomorphOfSurjective
    (E.childCapShellMap_surjective c b r)

@[simp] theorem childCapShellHomeomorph_apply_val (c : ConnectedComponents Q.Carrier)
    (b : E.ChildCapBoundary c) (r : ℝ) (x : {x : ThreeBall | r < ‖x.1‖}) :
    ((E.childCapShellHomeomorph c b r x).1 : E.ChildCarrier c) = E.childCap c b x.1 := rfl

private def coreCapPiece (c : ConnectedComponents Q.Carrier) (U : Set (E.ChildCarrier c)) :
    Option (E.ChildCapBoundary c) → Set U
  | none => Subtype.val ⁻¹' Set.range (E.childCoreInclusion c)
  | some b => Subtype.val ⁻¹' Set.range (E.childCap c b)

private theorem coreCapPiece_isClosed (c : ConnectedComponents Q.Carrier)
    (U : Set (E.ChildCarrier c)) (o : Option (E.ChildCapBoundary c)) :
    IsClosed (coreCapPiece E c U o) := by
  cases o with
  | none =>
      let : CompactSpace (E.ChildCore c) := E.childCore_compactSpace c
      exact (isCompact_range (E.childCoreInclusion c).continuous).isClosed.preimage
        continuous_subtype_val
  | some b =>
      exact (isCompact_range (E.childCap c b).continuous).isClosed.preimage
        continuous_subtype_val

private theorem iUnion_coreCapPiece (c : ConnectedComponents Q.Carrier)
    (U : Set (E.ChildCarrier c)) : ⋃ o, coreCapPiece E c U o = univ := by
  rw [Set.iUnion_option]
  change (Subtype.val ⁻¹' Set.range (E.childCoreInclusion c)) ∪
    (⋃ b, Subtype.val ⁻¹' Set.range (E.childCap c b)) = univ
  rw [← Set.preimage_iUnion, ← Set.preimage_union,
    E.range_childCoreInclusion_union_range_childCap c, Set.preimage_univ]

private def corePieceInverse (c : ConnectedComponents Q.Carrier) (r : ℝ) :
    C(coreCapPiece E c (E.childCoreNeighborhood c r) none, E.ChildCore c) :=
  (⟨(E.childCoreInclusion_isEmbedding c).toHomeomorph.symm,
    (E.childCoreInclusion_isEmbedding c).toHomeomorph.symm.continuous⟩ : C(_, _)).comp
    ⟨fun x => ⟨x.1.1, x.2⟩,
      (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _⟩

private theorem childCoreInclusion_corePieceInverse (c : ConnectedComponents Q.Carrier) (r : ℝ)
    (x : coreCapPiece E c (E.childCoreNeighborhood c r) none) :
    E.childCoreInclusion c (corePieceInverse E c r x) = x.1.1 := by
  exact congrArg Subtype.val
    ((E.childCoreInclusion_isEmbedding c).toHomeomorph.apply_symm_apply ⟨x.1.1, x.2⟩)

private def capPieceRetraction (c : ConnectedComponents Q.Carrier) (b : E.ChildCapBoundary c)
    {r : ℝ} (hr : 0 ≤ r) :
    C(coreCapPiece E c (E.childCoreNeighborhood c r) (some b), E.ChildCore c) :=
  (E.childCapSeam c b).comp
    ((DifferentialGeometry.Topology.ClosedBall.unitShellRadialMap hr).comp
      (⟨(E.childCapShellHomeomorph c b r).symm,
        (E.childCapShellHomeomorph c b r).symm.continuous⟩ : C(_, _)))

private theorem capPieceRetraction_eq_corePieceInverse (c : ConnectedComponents Q.Carrier)
    (b : E.ChildCapBoundary c) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (x : E.childCoreNeighborhood c r)
    (hxcore : x ∈ coreCapPiece E c (E.childCoreNeighborhood c r) none)
    (hxcap : x ∈ coreCapPiece E c (E.childCoreNeighborhood c r) (some b)) :
    capPieceRetraction E c b hr ⟨x, hxcap⟩ = corePieceInverse E c r ⟨x, hxcore⟩ := by
  have hseam : x.1 ∈ Set.range (E.childSeamSphere c b) := by
    rw [← E.range_childCoreInclusion_inter_range_childCap]
    exact ⟨hxcore, hxcap⟩
  obtain ⟨y, hy⟩ := hseam
  have hball : E.childCap c b (sphereToThreeBall y) = x.1 :=
    (E.childCap_boundary_eq c b y).trans hy
  have hshell : (E.childCapShellHomeomorph c b r).symm ⟨x, hxcap⟩ =
      DifferentialGeometry.Topology.ClosedBall.sphereToUnitShell hr1 y := by
    apply (E.childCapShellHomeomorph c b r).injective
    rw [Homeomorph.apply_symm_apply]
    apply Subtype.ext
    apply Subtype.ext
    exact hball.symm
  apply E.childCoreInclusion_injective c
  change E.childCoreInclusion c
    (E.childCapSeam c b (DifferentialGeometry.Topology.ClosedBall.unitShellRadialMap hr
      ((E.childCapShellHomeomorph c b r).symm ⟨x, hxcap⟩))) = _
  rw [hshell, DifferentialGeometry.Topology.ClosedBall.unitShellRadialMap_sphereToUnitShell,
    childCoreInclusion_corePieceInverse]
  exact hy

private def coreCapRetractionPiece (c : ConnectedComponents Q.Carrier)
    {r : ℝ} (hr : 0 ≤ r) (o : Option (E.ChildCapBoundary c)) :
    C(coreCapPiece E c (E.childCoreNeighborhood c r) o, E.ChildCore c) :=
  match o with
  | none => corePieceInverse E c r
  | some b => capPieceRetraction E c b hr

private theorem coreCapRetractionPiece_agree (c : ConnectedComponents Q.Carrier)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (i j : Option (E.ChildCapBoundary c))
    (x : E.childCoreNeighborhood c r)
    (hxi : x ∈ coreCapPiece E c (E.childCoreNeighborhood c r) i)
    (hxj : x ∈ coreCapPiece E c (E.childCoreNeighborhood c r) j) :
    coreCapRetractionPiece E c hr i ⟨x, hxi⟩ = coreCapRetractionPiece E c hr j ⟨x, hxj⟩ := by
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some b => exact (capPieceRetraction_eq_corePieceInverse E c b hr hr1 x hxi hxj).symm
  | some b =>
    cases j with
    | none => exact capPieceRetraction_eq_corePieceInverse E c b hr hr1 x hxj hxi
    | some b' =>
      by_cases hb : b = b'
      · subst b'
        rfl
      · exact (Set.disjoint_left.mp (E.disjoint_range_childCap hb) hxi hxj).elim

def childCoreNeighborhoodRetraction (c : ConnectedComponents Q.Carrier)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    C(E.childCoreNeighborhood c r, E.ChildCore c) :=
  ContinuousMap.liftClosedCover (coreCapPiece E c (E.childCoreNeighborhood c r))
    (coreCapRetractionPiece E c hr) (coreCapRetractionPiece_agree E c hr hr1)
    (iUnion_coreCapPiece E c _) (coreCapPiece_isClosed E c _) (locallyFinite_of_finite _)

theorem childCoreNeighborhoodRetraction_childCoreInclusion (c : ConnectedComponents Q.Carrier)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (x : E.ChildCore c) :
    E.childCoreNeighborhoodRetraction c hr hr1
      ⟨E.childCoreInclusion c x,
        E.range_childCoreInclusion_subset_childCoreNeighborhood c hr1 (Set.mem_range_self x)⟩ = x := by
  change (ContinuousMap.liftClosedCover _ _ _ _ _ _) _ = _
  rw [ContinuousMap.liftClosedCover_coe (i := none)
    (⟨⟨E.childCoreInclusion c x, _⟩, Set.mem_range_self x⟩ :
      coreCapPiece E c (E.childCoreNeighborhood c r) none)]
  exact (E.childCoreInclusion_isEmbedding c).toHomeomorph.symm_apply_apply x

private def capPieceDeformation (c : ConnectedComponents Q.Carrier)
    (b : E.ChildCapBoundary c) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    C(unitInterval × coreCapPiece E c (E.childCoreNeighborhood c r) (some b),
      E.childCoreNeighborhood c r) where
  toFun tx := (E.childCapShellHomeomorph c b r
    (DifferentialGeometry.Topology.ClosedBall.unitShellRadialDeformation hr hr1
      (tx.1, (E.childCapShellHomeomorph c b r).symm tx.2))).1
  continuous_toFun := continuous_subtype_val.comp
    ((E.childCapShellHomeomorph c b r).continuous.comp
      ((DifferentialGeometry.Topology.ClosedBall.unitShellRadialDeformation hr hr1).continuous.comp
        (continuous_fst.prodMk
          ((E.childCapShellHomeomorph c b r).symm.continuous.comp continuous_snd))))

private theorem capPieceDeformation_zero (c : ConnectedComponents Q.Carrier)
    (b : E.ChildCapBoundary c) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (x : coreCapPiece E c (E.childCoreNeighborhood c r) (some b)) :
    capPieceDeformation E c b hr hr1 (0, x) = x.1 := by
  change (E.childCapShellHomeomorph c b r
    (DifferentialGeometry.Topology.ClosedBall.unitShellRadialDeformation hr hr1
      (0, (E.childCapShellHomeomorph c b r).symm ⟨x.1, x.2⟩))).1 = x.1
  rw [ContinuousMap.HomotopyWith.apply_zero, ContinuousMap.id_apply,
    Homeomorph.apply_symm_apply]

private theorem capPieceDeformation_one (c : ConnectedComponents Q.Carrier)
    (b : E.ChildCapBoundary c) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (x : coreCapPiece E c (E.childCoreNeighborhood c r) (some b)) :
    (capPieceDeformation E c b hr hr1 (1, x)).1 =
      E.childCoreInclusion c (capPieceRetraction E c b hr x) := by
  change (E.childCapShellHomeomorph c b r
    (DifferentialGeometry.Topology.ClosedBall.unitShellRadialDeformation hr hr1
      (1, (E.childCapShellHomeomorph c b r).symm ⟨x.1, x.2⟩))).1.1 = _
  rw [ContinuousMap.HomotopyWith.apply_one]
  exact E.childCap_boundary_eq c b _

private theorem capPieceDeformation_eq_self_of_mem_core (c : ConnectedComponents Q.Carrier)
    (b : E.ChildCapBoundary c) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (t : unitInterval) (x : coreCapPiece E c (E.childCoreNeighborhood c r) (some b))
    (hxcore : x.1 ∈ coreCapPiece E c (E.childCoreNeighborhood c r) none) :
    capPieceDeformation E c b hr hr1 (t, x) = x.1 := by
  have hseam : x.1.1 ∈ Set.range (E.childSeamSphere c b) := by
    rw [← E.range_childCoreInclusion_inter_range_childCap]
    exact ⟨hxcore, x.2⟩
  obtain ⟨y, hy⟩ := hseam
  have hball : E.childCap c b (sphereToThreeBall y) = x.1.1 :=
    (E.childCap_boundary_eq c b y).trans hy
  have hshell : (E.childCapShellHomeomorph c b r).symm ⟨x.1, x.2⟩ =
      DifferentialGeometry.Topology.ClosedBall.sphereToUnitShell hr1 y := by
    apply (E.childCapShellHomeomorph c b r).injective
    rw [Homeomorph.apply_symm_apply]
    apply Subtype.ext
    apply Subtype.ext
    exact hball.symm
  have hfixed := (DifferentialGeometry.Topology.ClosedBall.unitShellRadialDeformation
    (E := ThreeSpace) hr hr1).eq_fst t (x := (E.childCapShellHomeomorph c b r).symm ⟨x.1, x.2⟩)
      (by
        change ‖((E.childCapShellHomeomorph c b r).symm ⟨x.1, x.2⟩).1.1‖ = 1
        rw [hshell]
        exact norm_eq_of_mem_sphere y)
  change (E.childCapShellHomeomorph c b r
    (DifferentialGeometry.Topology.ClosedBall.unitShellRadialDeformation hr hr1
      (t, (E.childCapShellHomeomorph c b r).symm ⟨x.1, x.2⟩))).1 = x.1
  rw [hfixed, ContinuousMap.id_apply, Homeomorph.apply_symm_apply]

private def coreCapHomotopyPiece (c : ConnectedComponents Q.Carrier)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (o : Option (E.ChildCapBoundary c)) :
    C((Prod.snd : unitInterval × E.childCoreNeighborhood c r → E.childCoreNeighborhood c r) ⁻¹' coreCapPiece E c (E.childCoreNeighborhood c r) o,
      E.childCoreNeighborhood c r) :=
  match o with
  | none => ⟨fun tx => tx.1.2, continuous_snd.comp continuous_subtype_val⟩
  | some b => (capPieceDeformation E c b hr hr1).comp
      ⟨fun tx => (tx.1.1, ⟨tx.1.2, tx.2⟩),
        (continuous_fst.comp continuous_subtype_val).prodMk
          ((continuous_snd.comp continuous_subtype_val).subtype_mk _)⟩

private theorem coreCapHomotopyPiece_agree (c : ConnectedComponents Q.Carrier)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (i j : Option (E.ChildCapBoundary c))
    (tx : unitInterval × E.childCoreNeighborhood c r)
    (hxi : tx ∈ (Prod.snd : unitInterval × E.childCoreNeighborhood c r → E.childCoreNeighborhood c r) ⁻¹' coreCapPiece E c (E.childCoreNeighborhood c r) i)
    (hxj : tx ∈ (Prod.snd : unitInterval × E.childCoreNeighborhood c r → E.childCoreNeighborhood c r) ⁻¹' coreCapPiece E c (E.childCoreNeighborhood c r) j) :
    coreCapHomotopyPiece E c hr hr1 i ⟨tx, hxi⟩ =
      coreCapHomotopyPiece E c hr hr1 j ⟨tx, hxj⟩ := by
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some b => exact (capPieceDeformation_eq_self_of_mem_core E c b hr hr1 tx.1
        ⟨tx.2, hxj⟩ hxi).symm
  | some b =>
    cases j with
    | none =>
      exact capPieceDeformation_eq_self_of_mem_core E c b hr hr1 tx.1 ⟨tx.2, hxi⟩ hxj
    | some b' =>
      by_cases hb : b = b'
      · subst b'
        rfl
      · exact (Set.disjoint_left.mp (E.disjoint_range_childCap hb) hxi hxj).elim

private def childCoreNeighborhoodHomotopyMap (c : ConnectedComponents Q.Carrier)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    C(unitInterval × E.childCoreNeighborhood c r, E.childCoreNeighborhood c r) :=
  ContinuousMap.liftClosedCover
    (fun o => (Prod.snd : unitInterval × E.childCoreNeighborhood c r → E.childCoreNeighborhood c r) ⁻¹' coreCapPiece E c (E.childCoreNeighborhood c r) o)
    (coreCapHomotopyPiece E c hr hr1) (coreCapHomotopyPiece_agree E c hr hr1)
    (by rw [← Set.preimage_iUnion, iUnion_coreCapPiece, Set.preimage_univ])
    (fun o => (coreCapPiece_isClosed E c _ o).preimage continuous_snd)
    (locallyFinite_of_finite _)

private theorem childCoreNeighborhoodHomotopyMap_piece (c : ConnectedComponents Q.Carrier)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (o : Option (E.ChildCapBoundary c))
    (tx : unitInterval × E.childCoreNeighborhood c r)
    (hx : tx.2 ∈ coreCapPiece E c (E.childCoreNeighborhood c r) o) :
    childCoreNeighborhoodHomotopyMap E c hr hr1 tx =
      coreCapHomotopyPiece E c hr hr1 o ⟨tx, hx⟩ := by
  exact ContinuousMap.liftClosedCover_coe
    (S := fun o => (Prod.snd : unitInterval × E.childCoreNeighborhood c r →
      E.childCoreNeighborhood c r) ⁻¹' coreCapPiece E c (E.childCoreNeighborhood c r) o)
    (φ := coreCapHomotopyPiece E c hr hr1)
    (hφ := coreCapHomotopyPiece_agree E c hr hr1)
    (hcov := by rw [← Set.preimage_iUnion, iUnion_coreCapPiece, Set.preimage_univ])
    (hclosed := fun o => (coreCapPiece_isClosed E c _ o).preimage continuous_snd)
    (hfinite := locallyFinite_of_finite _) (i := o) ⟨tx, hx⟩

private theorem childCoreNeighborhoodHomotopyMap_core (c : ConnectedComponents Q.Carrier)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (t : unitInterval)
    (x : E.childCoreNeighborhood c r) (hx : x.1 ∈ Set.range (E.childCoreInclusion c)) :
    childCoreNeighborhoodHomotopyMap E c hr hr1 (t, x) = x :=
  childCoreNeighborhoodHomotopyMap_piece E c hr hr1 none (t, x) hx

private theorem childCoreNeighborhoodHomotopyMap_zero (c : ConnectedComponents Q.Carrier)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (x : E.childCoreNeighborhood c r) :
    childCoreNeighborhoodHomotopyMap E c hr hr1 (0, x) = x := by
  have hx : x ∈ ⋃ o, coreCapPiece E c (E.childCoreNeighborhood c r) o := by
    rw [iUnion_coreCapPiece]
    trivial
  obtain ⟨o, hxo⟩ := Set.mem_iUnion.mp hx
  rw [childCoreNeighborhoodHomotopyMap_piece E c hr hr1 o (0, x) hxo]
  cases o with
  | none => rfl
  | some b => exact capPieceDeformation_zero E c b hr hr1 ⟨x, hxo⟩

private theorem childCoreNeighborhoodHomotopyMap_one (c : ConnectedComponents Q.Carrier)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (x : E.childCoreNeighborhood c r) :
    (childCoreNeighborhoodHomotopyMap E c hr hr1 (1, x)).1 =
      E.childCoreInclusion c (E.childCoreNeighborhoodRetraction c hr hr1 x) := by
  have hx : x ∈ ⋃ o, coreCapPiece E c (E.childCoreNeighborhood c r) o := by
    rw [iUnion_coreCapPiece]
    trivial
  obtain ⟨o, hxo⟩ := Set.mem_iUnion.mp hx
  rw [childCoreNeighborhoodHomotopyMap_piece E c hr hr1 o (1, x) hxo]
  have hret : E.childCoreNeighborhoodRetraction c hr hr1 x =
      coreCapRetractionPiece E c hr o ⟨x, hxo⟩ :=
    ContinuousMap.liftClosedCover_coe
      (S := coreCapPiece E c (E.childCoreNeighborhood c r))
      (φ := coreCapRetractionPiece E c hr)
      (hφ := coreCapRetractionPiece_agree E c hr hr1)
      (hcov := iUnion_coreCapPiece E c _) (hclosed := coreCapPiece_isClosed E c _)
      (hfinite := locallyFinite_of_finite _) ⟨x, hxo⟩
  rw [hret]
  cases o with
  | none => exact (childCoreInclusion_corePieceInverse E c r ⟨x, hxo⟩).symm
  | some b => exact capPieceDeformation_one E c b hr hr1 ⟨x, hxo⟩

def childCoreNeighborhoodDeformation (c : ConnectedComponents Q.Carrier)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    ContinuousMap.HomotopyRel
      (ContinuousMap.id (E.childCoreNeighborhood c r))
      ((E.childCoreInclusionRestrict c
        (E.range_childCoreInclusion_subset_childCoreNeighborhood c hr1)).comp
          (E.childCoreNeighborhoodRetraction c hr hr1))
      (Set.range (E.childCoreInclusionRestrict c
        (E.range_childCoreInclusion_subset_childCoreNeighborhood c hr1))) where
  toContinuousMap := childCoreNeighborhoodHomotopyMap E c hr hr1
  map_zero_left := childCoreNeighborhoodHomotopyMap_zero E c hr hr1
  map_one_left x := Subtype.ext (childCoreNeighborhoodHomotopyMap_one E c hr hr1 x)
  prop' t x hx := by
    obtain ⟨y, rfl⟩ := hx
    exact childCoreNeighborhoodHomotopyMap_core E c hr hr1 t _ ⟨y, rfl⟩

def childCoreNeighborhoodHomotopyEquiv (c : ConnectedComponents Q.Carrier)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    ContinuousMap.HomotopyEquiv (E.ChildCore c) (E.childCoreNeighborhood c r) :=
  homotopyEquiv_of_retraction
    (E.childCoreInclusionRestrict c
      (E.range_childCoreInclusion_subset_childCoreNeighborhood c hr1))
    (E.childCoreNeighborhoodRetraction c hr hr1)
    (by
      apply ContinuousMap.ext
      intro x
      exact E.childCoreNeighborhoodRetraction_childCoreInclusion c hr hr1 x)
    ⟨(E.childCoreNeighborhoodDeformation c hr hr1).toHomotopy.symm⟩

theorem simplyConnectedSpace_childCoreNeighborhood (c : ConnectedComponents Q.Carrier)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) [SimplyConnectedSpace (E.ChildCore c)] :
    SimplyConnectedSpace (E.childCoreNeighborhood c r) :=
  (E.childCoreNeighborhoodHomotopyEquiv c hr hr1).symm.simplyConnectedSpace

end SmoothCutCapTransition

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
