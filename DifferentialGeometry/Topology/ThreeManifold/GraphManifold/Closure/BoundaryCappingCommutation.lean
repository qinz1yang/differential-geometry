import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.BoundaryPortPairing
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.SphereCappingCore
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FillingProductCharts

/-!
The same physical torus gluing commutes with actual relative sphere capping at the level of
whole topological quotients, retaining the original uncapped quotient as the true cap puncture.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.Endpoint.CompactCarrier
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.RelativeSphereCapping

local instance cappingCommutationBallCharts :
    ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2

variable (C1 C2 Q2 : CompactCarrier.{u})
variable (hC1 : C1.kind = .withBoundary) (hC2 : C2.kind = .withBoundary)
variable (hQ2 : Q2.kind = .withBoundary)
variable [Nonempty C1.Carrier] [Nonempty C2.Carrier] [Nonempty Q2.Carrier]
variable (B : MixedBoundaryCertificate C2) (ht : B.torusCount = 1)
variable (K : RelativeSphereCapping C2 Q2 B) (E1 : BoundaryTori C1 1)
variable (f : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)

def boundaryCappingTori : BoundaryTori C2 1 := ht ▸ B.tori

def boundaryCappingRetained : BoundaryTori Q2 1 := ht ▸ K.retained

variable (hrev0 : ReversesBoundaryOrientation (withBoundarySum C1 C2 hC1 hC2)
  (boundaryPortLeftCollar C1 C2 hC1 hC2 E1)
  (fun p => boundaryPortRightCollar C1 C2 hC1 hC2 (boundaryCappingTori C2 B ht) 0
    (f p.1, p.2)))
variable (hrev1 : ReversesBoundaryOrientation (withBoundarySum C1 Q2 hC1 hQ2)
  (boundaryPortLeftCollar C1 Q2 hC1 hQ2 E1)
  (fun p => boundaryPortRightCollar C1 Q2 hC1 hQ2
    (boundaryCappingRetained C2 Q2 B ht K) 0 (f p.1, p.2)))

def boundaryCappingUncappedPairing : TorusPairing (withBoundarySum C1 C2 hC1 hC2) :=
  boundaryPortPairing C1 C2 hC1 hC2 E1 (boundaryCappingTori C2 B ht) f hrev0

def boundaryCappingCappedPairing : TorusPairing (withBoundarySum C1 Q2 hC1 hQ2) :=
  boundaryPortPairing C1 Q2 hC1 hQ2 E1 (boundaryCappingRetained C2 Q2 B ht K) f hrev1

local notation "P0" => boundaryCappingUncappedPairing C1 C2 hC1 hC2 B ht E1 f hrev0
local notation "P1" => boundaryCappingCappedPairing C1 C2 Q2 hC1 hQ2 B ht K E1 f hrev1

private theorem boundaryTori_cast_map {C : CompactCarrier.{u}} {n m : ℕ}
    (hn : n = m) (E : BoundaryTori C n) (i : Fin m) (t : Torus) :
    (hn ▸ E).torusMap i t = E.torusMap (Fin.cast hn.symm i) t := by
  cases hn
  rfl

omit [Nonempty C2.Carrier] [Nonempty Q2.Carrier] in
private theorem cappingRetained_zero (t : Torus) :
    (boundaryCappingRetained C2 Q2 B ht K).torusMap 0 t =
      K.core ((boundaryCappingTori C2 B ht).torusMap 0 t) := by
  unfold boundaryCappingRetained boundaryCappingTori
  rw [boundaryTori_cast_map ht K.retained, boundaryTori_cast_map ht B.tori]
  exact K.retained_zero (Fin.cast ht.symm 0) t

private theorem boundaryPort_relation {C D : CompactCarrier.{u}}
    (hC : C.kind = .withBoundary) (hD : D.kind = .withBoundary)
    [Nonempty C.Carrier] [Nonempty D.Carrier]
    (E : BoundaryTori C 1) (F : BoundaryTori D 1)
    (g : Torus ≃ₘ⟮torusModel, torusModel⟯ Torus)
    (hg : ReversesBoundaryOrientation (withBoundarySum C D hC hD)
      (boundaryPortLeftCollar C D hC hD E)
      (fun p => boundaryPortRightCollar C D hC hD F 0 (g p.1, p.2)))
    (x y : (withBoundarySum C D hC hD).Carrier) :
    (boundaryPortPairing C D hC hD E F g hg).gluing.rel x y ↔
      x = y ∨ ∃ t : Torus,
        (x = Sum.inl (E.torusMap 0 t) ∧ y = Sum.inr (F.torusMap 0 (g t))) ∨
        (y = Sum.inl (E.torusMap 0 t) ∧ x = Sum.inr (F.torusMap 0 (g t))) := by
  rw [GC.Seifert.TorusPairing.rel_iff_params]
  constructor
  · rintro (he | ⟨j, t, he⟩)
    · exact Or.inl he
    · exact Or.inr ⟨t, he⟩
  · rintro (he | ⟨t, he⟩)
    · exact Or.inl he
    · exact Or.inr ⟨⟨0, Nat.one_pos⟩, t, he⟩

private def cappingSumMap : C1.Carrier ⊕ C2.Carrier → C1.Carrier ⊕ Q2.Carrier :=
  Sum.map id K.core

set_option backward.isDefEq.respectTransparency false in
private theorem cappingSumMap_relation (x y : C1.Carrier ⊕ C2.Carrier) :
    (P0).gluing.rel x y ↔ (P1).gluing.rel (cappingSumMap C1 C2 Q2 B K x)
      (cappingSumMap C1 C2 Q2 B K y) := by
  unfold boundaryCappingUncappedPairing boundaryCappingCappedPairing
  rw [boundaryPort_relation, boundaryPort_relation]
  have hinj : Injective (cappingSumMap C1 C2 Q2 B K) :=
    Function.Injective.sumMap Function.injective_id K.core_embedding.isEmbedding.injective
  constructor
  · rintro (rfl | ⟨t, he | he⟩)
    · exact Or.inl rfl
    · obtain ⟨rfl, rfl⟩ := he
      right
      refine ⟨t, Or.inl ⟨rfl, ?_⟩⟩
      exact congrArg Sum.inr (cappingRetained_zero C2 Q2 B ht K (f t)).symm
    · obtain ⟨rfl, rfl⟩ := he
      right
      refine ⟨t, Or.inr ⟨rfl, ?_⟩⟩
      exact congrArg Sum.inr (cappingRetained_zero C2 Q2 B ht K (f t)).symm
  · rintro (he | ⟨t, he | he⟩)
    · exact Or.inl (hinj he)
    · refine Or.inr ⟨t, Or.inl ⟨hinj he.1, ?_⟩⟩
      apply hinj
      exact he.2.trans (congrArg Sum.inr (cappingRetained_zero C2 Q2 B ht K (f t)))
    · refine Or.inr ⟨t, Or.inr ⟨hinj he.1, ?_⟩⟩
      apply hinj
      exact he.2.trans (congrArg Sum.inr (cappingRetained_zero C2 Q2 B ht K (f t)))

def boundaryCappingCore : C((P0).QuotientSpace, (P1).QuotientSpace) where
  toFun := Quotient.map (cappingSumMap C1 C2 Q2 B K)
    (fun x y hxy => (cappingSumMap_relation C1 C2 Q2 hC1 hC2 hQ2 B ht K E1 f
      hrev0 hrev1 x y).mp hxy)
  continuous_toFun := (((P1).quotientMap.continuous.comp
    (continuous_id.sumMap K.core.continuous))).quotient_lift
      (fun x y (hxy : (P0).gluing.rel x y) => Quotient.sound
        ((cappingSumMap_relation C1 C2 Q2 hC1 hC2 hQ2 B ht K E1 f hrev0 hrev1 x y).mp hxy))

def boundaryCappingCap (i : Fin B.sphereCount) : C(ClosedCell 3, (P1).QuotientSpace) :=
  ⟨fun x => (P1).quotientMap (Sum.inr (K.cap i x)),
    (P1).quotientMap.continuous.comp (continuous_inr.comp (K.cap i).continuous)⟩

local notation "qcore" =>
  boundaryCappingCore C1 C2 Q2 hC1 hC2 hQ2 B ht K E1 f hrev0 hrev1
local notation "qcap" => boundaryCappingCap C1 C2 Q2 hC1 hQ2 B ht K E1 f hrev1

def boundaryCappingOpenCaps : Set (P1).QuotientSpace :=
  ⋃ i, qcap i '' {x : ClosedCell 3 | ‖x.val‖ < 1}

local notation "qopen" => boundaryCappingOpenCaps C1 C2 Q2 hC1 hQ2 B ht K E1 f hrev1

theorem boundaryCappingCore_mk (x : (withBoundarySum C1 C2 hC1 hC2).Carrier) :
    qcore ((P0).quotientMap x) = (P1).quotientMap (Sum.map id K.core x) := rfl

theorem boundaryCappingCore_left (x : C1.Carrier) :
    qcore ((P0).quotientMap (Sum.inl x)) = (P1).quotientMap (Sum.inl x) := rfl

theorem boundaryCappingCore_right (x : C2.Carrier) :
    qcore ((P0).quotientMap (Sum.inr x)) = (P1).quotientMap (Sum.inr (K.core x)) := rfl

omit [Nonempty C2.Carrier] in
theorem boundaryCappingCap_apply (i : Fin B.sphereCount) (x : ClosedCell 3) :
    qcap i x = (P1).quotientMap (Sum.inr (K.cap i x)) := rfl

private theorem cappingCore_injective : Injective qcore := by
  intro x y
  induction x using Quotient.inductionOn with
  | h x =>
    induction y using Quotient.inductionOn with
    | h y =>
      intro he
      apply Quotient.sound
      exact (cappingSumMap_relation C1 C2 Q2 hC1 hC2 hQ2 B ht K E1 f hrev0 hrev1 x y).mpr
        (Quotient.exact he)

theorem boundaryCappingCore_isEmbedding : _root_.Topology.IsEmbedding qcore :=
  (qcore).continuous.isClosedEmbedding
    (cappingCore_injective C1 C2 Q2 hC1 hC2 hQ2 B ht K E1 f hrev0 hrev1) |>.isEmbedding

omit [Nonempty C2.Carrier] in
set_option backward.isDefEq.respectTransparency false in
private theorem cappingRight_injective :
    Injective (fun x : Q2.Carrier => (P1).quotientMap (Sum.inr x)) := by
  intro x y he
  have hr := Quotient.exact he
  change (P1).gluing.rel (Sum.inr x) (Sum.inr y) at hr
  unfold boundaryCappingCappedPairing at hr
  rw [boundaryPort_relation] at hr
  rcases hr with he | ⟨t, he | he⟩
  · exact Sum.inr_injective he
  · exact False.elim (Sum.inr_ne_inl he.1)
  · exact False.elim (Sum.inr_ne_inl he.1)

omit [Nonempty C2.Carrier] in
theorem boundaryCappingCap_isEmbedding (i : Fin B.sphereCount) :
    _root_.Topology.IsEmbedding (qcap i) :=
  (qcap i).continuous.isClosedEmbedding
    ((cappingRight_injective C1 C2 Q2 hC1 hQ2 B ht K E1 f hrev1).comp
      (K.cap_embedding i).isEmbedding.injective) |>.isEmbedding

omit [Nonempty C2.Carrier] [Nonempty Q2.Carrier] in
private theorem cappingCap_ne_retained (i : Fin B.sphereCount) (a : ClosedCell 3)
    (t : Torus) : K.cap i a ≠ (boundaryCappingRetained C2 Q2 B ht K).torusMap 0 t := by
  intro he
  have hi : K.core ((boundaryCappingTori C2 B ht).torusMap 0 t) ∈
      range K.core ∩ range (K.cap i) :=
    ⟨⟨_, rfl⟩, ⟨a, he.trans (cappingRetained_zero C2 Q2 B ht K t)⟩⟩
  rw [K.core_cap_intersection] at hi
  obtain ⟨z, hz⟩ := hi
  have heq := K.core_embedding.isEmbedding.injective hz
  change B.sphere i (z, halfZero) = (boundaryCappingTori C2 B ht).torusMap 0 t at heq
  unfold boundaryCappingTori at heq
  rw [boundaryTori_cast_map ht B.tori] at heq
  have htor : B.tori.torusMap (Fin.cast ht.symm 0) t ∈
      (B.tori.collar (Fin.cast ht.symm 0)).target :=
    (B.tori.collar (Fin.cast ht.symm 0)).map_source (by
      rw [B.tori.source_eq]
      change (0 : ℝ) < 1
      norm_num)
  have hsphere : B.sphere i (z, halfZero) ∈ (B.sphere i).target :=
    (B.sphere i).map_source (by
      rw [B.sphere_source]
      change (0 : ℝ) < 1
      norm_num)
  exact (B.cross_disjoint (Fin.cast ht.symm 0) i).le_bot ⟨htor, heq ▸ hsphere⟩

omit [Nonempty C2.Carrier] in
set_option backward.isDefEq.respectTransparency false in
private theorem cappingLeft_cap_ne (x : C1.Carrier) (i : Fin B.sphereCount)
    (a : ClosedCell 3) : (P1).quotientMap (Sum.inl x) ≠ qcap i a := by
  intro he
  have hr := Quotient.exact he
  change (P1).gluing.rel (Sum.inl x) (Sum.inr (K.cap i a)) at hr
  unfold boundaryCappingCappedPairing at hr
  rw [boundaryPort_relation] at hr
  rcases hr with he | ⟨t, he | he⟩
  · exact Sum.inl_ne_inr he
  · exact cappingCap_ne_retained C2 Q2 B ht K i a (f t) (Sum.inr_injective he.2)
  · exact Sum.inr_ne_inl he.1

theorem boundaryCapping_covers :
    range qcore ∪ (⋃ i, range (qcap i)) = univ := by
  apply eq_univ_of_forall
  intro x
  induction x using Quotient.inductionOn with
  | h x =>
    rcases x with x | x
    · exact Or.inl ⟨(P0).quotientMap (Sum.inl x), rfl⟩
    · rcases K.every_point x with ⟨y, rfl⟩ | ⟨i, a, rfl⟩
      · exact Or.inl ⟨(P0).quotientMap (Sum.inr y), rfl⟩
      · exact Or.inr (mem_iUnion.mpr ⟨i, a, rfl⟩)

theorem boundaryCapping_core_cap_intersection (i : Fin B.sphereCount) :
    range qcore ∩ range (qcap i) =
      range (fun z => qcore ((P0).quotientMap (Sum.inr (B.sphere i (z, halfZero))))) := by
  ext y
  constructor
  · rintro ⟨⟨x, rfl⟩, a, ha⟩
    induction x using Quotient.inductionOn with
    | h x =>
      rcases x with x | x
      · exact False.elim
          (cappingLeft_cap_ne C1 C2 Q2 hC1 hQ2 B ht K E1 f hrev1 x i a ha.symm)
      · have he : K.cap i a = K.core x :=
          cappingRight_injective C1 C2 Q2 hC1 hQ2 B ht K E1 f hrev1 ha
        have hi : K.core x ∈ range K.core ∩ range (K.cap i) :=
          ⟨⟨x, rfl⟩, ⟨a, he⟩⟩
        rw [K.core_cap_intersection] at hi
        obtain ⟨z, hz⟩ := hi
        refine ⟨z, ?_⟩
        exact congrArg (fun w => (P1).quotientMap (Sum.inr w)) hz
  · rintro ⟨z, rfl⟩
    refine ⟨⟨_, rfl⟩, closureSphereToBall ((K.attaching i).symm z), ?_⟩
    change (P1).quotientMap (Sum.inr (K.cap i _)) =
      (P1).quotientMap (Sum.inr (K.core (B.sphere i (z, halfZero))))
    rw [K.boundary_eq, Diffeomorph.apply_symm_apply]

omit [Nonempty C2.Carrier] in
theorem boundaryCapping_cap_disjoint : Pairwise fun i j =>
    Disjoint (range (qcap i)) (range (qcap j)) := by
  intro i j hij
  apply disjoint_left.mpr
  rintro y ⟨a, rfl⟩ ⟨b, hb⟩
  have he : K.cap j b = K.cap i a :=
    cappingRight_injective C1 C2 Q2 hC1 hQ2 B ht K E1 f hrev1 hb
  exact (K.cap_disjoint hij).le_bot ⟨⟨a, rfl⟩, ⟨b, he⟩⟩

theorem boundaryCappingCore_range : range qcore = (qopen)ᶜ := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩ hy
    obtain ⟨i, a, ha, he⟩ := mem_iUnion.mp hy
    have hi : qcore x ∈ range qcore ∩ range (qcap i) :=
      ⟨⟨x, rfl⟩, ⟨a, he⟩⟩
    rw [boundaryCapping_core_cap_intersection] at hi
    obtain ⟨z, hz⟩ := hi
    let w := (K.attaching i).symm z
    have hw : qcap i (closureSphereToBall w) = qcore x := by
      change (P1).quotientMap (Sum.inr (K.cap i (closureSphereToBall w))) = _
      rw [K.boundary_eq]
      change (P1).quotientMap (Sum.inr (K.core (B.sphere i (z, halfZero)))) = qcore x at hz
      simpa only [w, Diffeomorph.apply_symm_apply] using hz
    have hae : a = closureSphereToBall w :=
      (boundaryCappingCap_isEmbedding C1 C2 Q2 hC1 hQ2 B ht K E1 f hrev1 i).injective
        (he.trans hw.symm)
    have hn : ‖(closureSphereToBall w).val‖ = 1 := by
      simpa only [closureSphereToBall, sphereToClosedCell, Metric.mem_sphere,
        dist_zero_right] using w.down.property
    exact (not_lt_of_ge hn.ge) (hae ▸ ha)
  · intro hy
    have hcover := boundaryCapping_covers C1 C2 Q2 hC1 hC2 hQ2 B ht K E1 f hrev0 hrev1
    have hh : y ∈ range qcore ∪ (⋃ i, range (qcap i)) := hcover ▸ mem_univ y
    rcases hh with hcore | hcap
    · exact hcore
    · obtain ⟨i, a, rfl⟩ := mem_iUnion.mp hcap
      have hn : ¬‖a.val‖ < 1 := by
        intro ha
        exact hy (mem_iUnion.mpr ⟨i, a, ha, rfl⟩)
      have he : ‖a.val‖ = 1 := le_antisymm a.property (not_lt.mp hn)
      let z : ClosureSphere.{u} := ULift.up ⟨a.val, by simpa using he⟩
      have hz : closureSphereToBall z = a := Subtype.ext rfl
      refine ⟨(P0).quotientMap (Sum.inr (B.sphere i (K.attaching i z, halfZero))), ?_⟩
      change (P1).quotientMap (Sum.inr (K.core (B.sphere i (K.attaching i z, halfZero)))) = _
      rw [← K.boundary_eq, hz]
      rfl

def boundaryCappingCorePunctureHomeomorph : (P0).QuotientSpace ≃ₜ ↥(qopen)ᶜ :=
  (boundaryCappingCore_isEmbedding C1 C2 Q2 hC1 hC2 hQ2 B ht K E1 f hrev0
    hrev1).toHomeomorph.trans
    (Homeomorph.setCongr
      (boundaryCappingCore_range C1 C2 Q2 hC1 hC2 hQ2 B ht K E1 f hrev0 hrev1))

theorem boundaryCappingCorePunctureHomeomorph_apply (x : (P0).QuotientSpace) :
    (boundaryCappingCorePunctureHomeomorph C1 C2 Q2 hC1 hC2 hQ2 B ht K E1 f hrev0 hrev1 x).val =
      qcore x := rfl

end GC.GraphManifold.RelativeSphereCapping
