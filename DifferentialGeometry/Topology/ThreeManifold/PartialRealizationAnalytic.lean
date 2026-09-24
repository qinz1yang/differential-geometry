import DifferentialGeometry.Topology.ThreeManifold.PartialGraphRealization

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u v w

local notation "S²" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "Tube" => S² × Set.Icc (-2 : ℝ) 2

namespace MarkedBall

variable {N : ClosedOrientedManifold.{u} 3}

theorem disjoint_range_ball {B B' : MarkedBall N} (h : Disjoint B.collar B'.collar) :
    Disjoint (range B.ball) (range B'.ball) :=
  h.mono B.ball_subset_collar B'.ball_subset_collar

theorem boundary_not_mem_own_interior (B : MarkedBall N) (z : S²) :
    B.boundary z ∉ (range B.ball \ range (B.ball ∘ sphereToClosedCell)) :=
  fun hx => hx.2 (mem_range_self (f := B.ball ∘ sphereToClosedCell) z)

end MarkedBall

namespace MarkedManifoldGraph

variable (G : MarkedManifoldGraph.{u})

theorem mem_flagBall_cast_iff (e : G.Edge) (b : Bool) (v : G.Vertex)
    (hv : G.endpoint e b = v) (x : (G.vertexManifold v).Carrier) :
    (x ∈ hv ▸ range (G.flag e b).ball) ↔ (hv.symm ▸ x ∈ range (G.flag e b).ball) := by
  cases hv
  exact Iff.rfl

theorem mem_flagInterior_cast_iff (e : G.Edge) (b : Bool) (v : G.Vertex)
    (hv : G.endpoint e b = v) (x : (G.vertexManifold v).Carrier) :
    (x ∈ hv ▸ (range (G.flag e b).ball \
        range ((G.flag e b).ball ∘ sphereToClosedCell))) ↔
      (hv.symm ▸ x ∈ range (G.flag e b).ball \
        range ((G.flag e b).ball ∘ sphereToClosedCell)) := by
  cases hv
  exact Iff.rfl

theorem flagBall_cast_subset_collar (e : G.Edge) (b : Bool) (v : G.Vertex)
    (hv : G.endpoint e b = v) :
    hv ▸ range (G.flag e b).ball ⊆ hv ▸ (G.flag e b).collar := by
  cases hv
  exact (G.flag e b).ball_subset_collar

theorem flagBoundary_not_mem_own_flagInterior_cast (e : G.Edge) (b : Bool)
    (hv : G.endpoint e b = G.endpoint e b) (z : S²) :
    ¬ ((G.flag e b).ball (sphereToClosedCell z) ∈ hv ▸
      (range (G.flag e b).ball \ range ((G.flag e b).ball ∘ sphereToClosedCell))) := by
  intro hx
  rw [Subsingleton.elim hv rfl] at hx
  exact hx.2 (mem_range_self (f := (G.flag e b).ball ∘ sphereToClosedCell) z)

theorem flagBoundary_not_mem_removedBallSet (S : Finset G.Edge) (e : G.Edge) (b : Bool)
    (z : S²) :
    (G.flag e b).boundary z ∉ G.removedBallSet S (G.endpoint e b) := by
  rintro ⟨e', he', b', hv', hmem⟩
  by_cases hsame : (e, b) = (e', b')
  · cases hsame
    exact flagBoundary_not_mem_own_flagInterior_cast G e b hv' z hmem
  · have hne : (⟨(e, b), rfl⟩ :
        {p : G.Edge × Bool // G.endpoint p.1 p.2 = G.endpoint e b}) ≠
        ⟨(e', b'), hv'⟩ := fun hh => hsame (congrArg Subtype.val hh)
    have hdisj := G.flag_collar_disjoint (G.endpoint e b) ⟨(e, b), rfl⟩ ⟨(e', b'), hv'⟩ hne
    have hball : Disjoint (range (G.flag e b).ball)
        (hv' ▸ range (G.flag e' b').ball) :=
      hdisj.mono (G.flag e b).ball_subset_collar
        (flagBall_cast_subset_collar G e' b' (G.endpoint e b) hv')
    refine Set.disjoint_left.mp hball
      (mem_range_self (f := (G.flag e b).ball) (sphereToClosedCell z)) ?_
    exact (mem_flagBall_cast_iff G e' b' (G.endpoint e b) hv' _).mpr
      (((mem_flagInterior_cast_iff G e' b' (G.endpoint e b) hv' _).mp hmem).1)

theorem flagBall_not_mem_removedBallSet (S : Finset G.Edge) (e : G.Edge) (b : Bool)
    (he : e ∉ S) (x : ClosedCell 3) :
    (G.flag e b).ball x ∉ G.removedBallSet S (G.endpoint e b) := by
  rintro ⟨e', he', b', hv', hmem⟩
  have hne : (⟨(e, b), rfl⟩ :
      {p : G.Edge × Bool // G.endpoint p.1 p.2 = G.endpoint e b}) ≠
      ⟨(e', b'), hv'⟩ := by
    intro hh
    have hv : e = e' := congrArg (fun p : G.Edge × Bool => p.1) (congrArg Subtype.val hh)
    exact he (hv ▸ he')
  have hdisj := G.flag_collar_disjoint (G.endpoint e b) ⟨(e, b), rfl⟩ ⟨(e', b'), hv'⟩ hne
  have hball : Disjoint (range (G.flag e b).ball)
      (hv' ▸ range (G.flag e' b').ball) :=
    hdisj.mono (G.flag e b).ball_subset_collar
      (flagBall_cast_subset_collar G e' b' (G.endpoint e b) hv')
  refine Set.disjoint_left.mp hball (mem_range_self (f := (G.flag e b).ball) x) ?_
  exact (mem_flagBall_cast_iff G e' b' (G.endpoint e b) hv' _).mpr
    (((mem_flagInterior_cast_iff G e' b' (G.endpoint e b) hv' _).mp hmem).1)

def flagBoundaryPoint (S : Finset G.Edge) (e : G.Edge) (b : Bool) (z : S²) :
    G.puncturedCarrier S (G.endpoint e b) :=
  ⟨(G.flag e b).boundary z, G.flagBoundary_not_mem_removedBallSet S e b z⟩

def flagBallPoint (S : Finset G.Edge) (e : G.Edge) (b : Bool) (he : e ∉ S)
    (x : ClosedCell 3) : G.puncturedCarrier S (G.endpoint e b) :=
  ⟨(G.flag e b).ball x, G.flagBall_not_mem_removedBallSet S e b he x⟩

theorem flagBoundaryPoint_coe (S : Finset G.Edge) (e : G.Edge) (b : Bool) (z : S²) :
    (G.flagBoundaryPoint S e b z).1 = (G.flag e b).boundary z := rfl

theorem flagBallPoint_coe (S : Finset G.Edge) (e : G.Edge) (b : Bool) (he : e ∉ S)
    (x : ClosedCell 3) : (G.flagBallPoint S e b he x).1 = (G.flag e b).ball x := rfl

end MarkedManifoldGraph

def tubeEndLevel (b : Bool) : Set.Icc (-2 : ℝ) 2 :=
  if b then ⟨2, by norm_num⟩ else ⟨-2, by norm_num⟩

@[simp] theorem tubeEndLevel_false : tubeEndLevel false = ⟨-2, by norm_num⟩ := rfl

@[simp] theorem tubeEndLevel_true : tubeEndLevel true = ⟨2, by norm_num⟩ := rfl

def sphereBasePoint : S² := ⟨EuclideanSpace.single 0 1, by simp⟩

namespace MarkedManifoldGraph

variable (G : MarkedManifoldGraph.{u})

abbrev stepCarrier (S : Finset G.Edge) (e : G.Edge) : Type u :=
  G.puncturedCarrier (insert e S) (G.endpoint e false) ⊕ Tube ⊕
    G.puncturedCarrier (insert e S) (G.endpoint e true)

def stepRel (S : Finset G.Edge) (e : G.Edge) :
    G.stepCarrier S e → G.stepCarrier S e → Prop :=
  fun x y =>
    (∃ z : S², x = Sum.inl (G.flagBoundaryPoint (insert e S) e false z) ∧
      y = Sum.inr (Sum.inl (z, tubeEndLevel false))) ∨
    (∃ z : S², y = Sum.inl (G.flagBoundaryPoint (insert e S) e false z) ∧
      x = Sum.inr (Sum.inl (z, tubeEndLevel false))) ∨
    (∃ z : S², x = Sum.inr (Sum.inl (z, tubeEndLevel true)) ∧
      y = Sum.inr (Sum.inr (G.flagBoundaryPoint (insert e S) e true z))) ∨
    (∃ z : S², y = Sum.inr (Sum.inl (z, tubeEndLevel true)) ∧
      x = Sum.inr (Sum.inr (G.flagBoundaryPoint (insert e S) e true z)))

abbrev stepQuotient (S : Finset G.Edge) (e : G.Edge) : Type u := Quot (G.stepRel S e)

def stepQuotientMap (S : Finset G.Edge) (e : G.Edge) :
    C(G.stepCarrier S e, G.stepQuotient S e) :=
  ⟨Quot.mk _, continuous_quot_mk⟩

theorem stepQuotientMap_isQuotientMap (S : Finset G.Edge) (e : G.Edge) :
    Topology.IsQuotientMap (G.stepQuotientMap S e :
      G.stepCarrier S e → G.stepQuotient S e) :=
  isQuotientMap_quot_mk

theorem stepQuotient_seam_source (S : Finset G.Edge) (e : G.Edge) (z : S²) :
    Quot.mk (G.stepRel S e) (Sum.inl (G.flagBoundaryPoint (insert e S) e false z)) =
      Quot.mk (G.stepRel S e) (Sum.inr (Sum.inl (z, tubeEndLevel false))) :=
  Quot.sound (Or.inl ⟨z, rfl, rfl⟩)

theorem stepQuotient_seam_target (S : Finset G.Edge) (e : G.Edge) (z : S²) :
    Quot.mk (G.stepRel S e) (Sum.inr (Sum.inl (z, tubeEndLevel true))) =
      Quot.mk (G.stepRel S e) (Sum.inr (Sum.inr (G.flagBoundaryPoint (insert e S) e true z))) :=
  Quot.sound (Or.inr (Or.inr (Or.inl ⟨z, rfl, rfl⟩)))

theorem nonempty_stepQuotient (S : Finset G.Edge) (e : G.Edge) :
    Nonempty (G.stepQuotient S e) :=
  ⟨Quot.mk (G.stepRel S e)
    (Sum.inl (G.flagBoundaryPoint (insert e S) e false sphereBasePoint))⟩

theorem stepQuotient_seam_source_sphereBasePoint (S : Finset G.Edge) (e : G.Edge) :
    Quot.mk (G.stepRel S e)
        (Sum.inl (G.flagBoundaryPoint (insert e S) e false sphereBasePoint)) =
      Quot.mk (G.stepRel S e) (Sum.inr (Sum.inl (sphereBasePoint, tubeEndLevel false))) :=
  G.stepQuotient_seam_source S e sphereBasePoint

theorem adjunctionCell_flagBoundaryPoint_eq_adjunctionLower (S : Finset G.Edge) (e : G.Edge)
    (z : S²) :
    adjunctionCell (G.flagBoundaryPoint (insert e S) e false)
        (fun z : S² => (z, tubeEndLevel false))
        (G.flagBoundaryPoint (insert e S) e false z) =
      adjunctionLower (i := G.flagBoundaryPoint (insert e S) e false)
        (fun z : S² => (z, tubeEndLevel false)) (z, tubeEndLevel false) :=
  adjunction_coherence _ _ z

end MarkedManifoldGraph

namespace PartialRealization

variable {G : MarkedManifoldGraph.{u}} {S : Finset G.Edge}

def cylinderEnd (P : PartialRealization G S) (e : G.Edge) (he : e ∈ S) (b : Bool) :
    S² → P.realization.Carrier :=
  fun z => P.cylinderPiece e he (z, tubeEndLevel b)

def SeamEquation (P : PartialRealization G S) (e : G.Edge) (he : e ∈ S) : Prop :=
  (∀ z : S², P.cylinderEnd e he false z =
      P.vertexPiece (G.endpoint e false) (G.flagBoundaryPoint S e false z)) ∧
    (∀ z : S², P.cylinderEnd e he true z =
      P.vertexPiece (G.endpoint e true) (G.flagBoundaryPoint S e true z))

theorem range_cylinderEnd_source_eq (P : PartialRealization G S) (e : G.Edge) (he : e ∈ S)
    (h : P.SeamEquation e he) :
    range (P.cylinderEnd e he false) =
      range (fun z : S² => P.vertexPiece (G.endpoint e false) (G.flagBoundaryPoint S e false z)) :=
  congrArg range (funext h.1)

theorem range_cylinderEnd_target_eq (P : PartialRealization G S) (e : G.Edge) (he : e ∈ S)
    (h : P.SeamEquation e he) :
    range (P.cylinderEnd e he true) =
      range (fun z : S² => P.vertexPiece (G.endpoint e true) (G.flagBoundaryPoint S e true z)) :=
  congrArg range (funext h.2)

theorem range_cylinderEnd_source_subset_vertexPiece (P : PartialRealization G S) (e : G.Edge)
    (he : e ∈ S) (h : P.SeamEquation e he) :
    range (P.cylinderEnd e he false) ⊆ range (P.vertexPiece (G.endpoint e false)) :=
  fun _ ⟨z, hz⟩ => ⟨G.flagBoundaryPoint S e false z, (h.1 z).symm.trans hz⟩

theorem range_cylinderEnd_target_subset_vertexPiece (P : PartialRealization G S) (e : G.Edge)
    (he : e ∈ S) (h : P.SeamEquation e he) :
    range (P.cylinderEnd e he true) ⊆ range (P.vertexPiece (G.endpoint e true)) :=
  fun _ ⟨z, hz⟩ => ⟨G.flagBoundaryPoint S e true z, (h.2 z).symm.trans hz⟩

variable {e : G.Edge}

def stepMap (P : PartialRealization G (insert e S)) :
    G.stepCarrier S e → P.realization.Carrier :=
  Sum.elim (P.vertexPiece (G.endpoint e false))
    (Sum.elim (P.cylinderPiece e (Finset.mem_insert_self e S))
      (P.vertexPiece (G.endpoint e true)))

@[simp] theorem stepMap_left (P : PartialRealization G (insert e S))
    (y : G.puncturedCarrier (insert e S) (G.endpoint e false)) :
    P.stepMap (Sum.inl y) = P.vertexPiece (G.endpoint e false) y := rfl

@[simp] theorem stepMap_cylinder (P : PartialRealization G (insert e S))
    (q : Tube) :
    P.stepMap (Sum.inr (Sum.inl q)) = P.cylinderPiece e (Finset.mem_insert_self e S) q := rfl

@[simp] theorem stepMap_right (P : PartialRealization G (insert e S))
    (w : G.puncturedCarrier (insert e S) (G.endpoint e true)) :
    P.stepMap (Sum.inr (Sum.inr w)) = P.vertexPiece (G.endpoint e true) w := rfl

theorem stepMap_continuous (P : PartialRealization G (insert e S)) :
    Continuous (P.stepMap) :=
  (P.vertexPiece (G.endpoint e false)).continuous.sumElim
    ((P.cylinderPiece e (Finset.mem_insert_self e S)).continuous.sumElim
      (P.vertexPiece (G.endpoint e true)).continuous)

theorem seamEquation_iff_stepRel_related (P : PartialRealization G (insert e S)) :
    P.SeamEquation e (Finset.mem_insert_self e S) ↔
      ∀ x y, G.stepRel S e x y → P.stepMap x = P.stepMap y := by
  constructor
  · rintro ⟨hs, ht⟩ x y h
    rcases h with ⟨z, rfl, rfl⟩ | ⟨z, rfl, rfl⟩ | ⟨z, rfl, rfl⟩ | ⟨z, rfl, rfl⟩
    · simpa [cylinderEnd] using (hs z).symm
    · simpa [cylinderEnd] using hs z
    · simpa [cylinderEnd] using ht z
    · simpa [cylinderEnd] using (ht z).symm
  · intro h
    exact ⟨fun z => by simpa [cylinderEnd] using (h _ _ (Or.inl ⟨z, rfl, rfl⟩)).symm,
      fun z => by
        simpa [cylinderEnd] using h _ _ (Or.inr (Or.inr (Or.inl ⟨z, rfl, rfl⟩)))⟩

theorem eqvGen_stepMap_eq (P : PartialRealization G (insert e S))
    (h : ∀ x y, G.stepRel S e x y → P.stepMap x = P.stepMap y) {x y : G.stepCarrier S e}
    (hxy : Relation.EqvGen (G.stepRel S e) x y) : P.stepMap x = P.stepMap y := by
  induction hxy with
  | rel a b hab => exact h a b hab
  | refl => rfl
  | symm a b hab ih => exact ih.symm
  | trans a b c hab hbc ih1 ih2 => exact ih1.trans ih2

theorem seamEquation_iff_factorsThrough (P : PartialRealization G (insert e S)) :
    P.SeamEquation e (Finset.mem_insert_self e S) ↔
      Function.FactorsThrough (P.stepMap) (Quot.mk (G.stepRel S e)) := by
  constructor
  · intro hs x y hxy
    exact P.eqvGen_stepMap_eq ((P.seamEquation_iff_stepRel_related).mp hs)
      (Quot.eq.mp hxy)
  · intro hf
    exact (P.seamEquation_iff_stepRel_related).mpr fun x y hr => hf (Quot.sound hr)

theorem exists_stepLift (P : PartialRealization G (insert e S))
    (h : P.SeamEquation e (Finset.mem_insert_self e S)) :
    ∃ F : C(G.stepQuotient S e, P.realization.Carrier),
      ∀ x, F (Quot.mk (G.stepRel S e) x) = P.stepMap x := by
  have hq := G.stepQuotientMap_isQuotientMap S e
  refine ⟨hq.lift ⟨P.stepMap, P.stepMap_continuous⟩
    ((P.seamEquation_iff_factorsThrough).mp h), ?_⟩
  intro x
  exact congrArg (fun k : C(G.stepCarrier S e, P.realization.Carrier) =>
    (k : G.stepCarrier S e → P.realization.Carrier) x)
    (hq.lift_comp ⟨P.stepMap, P.stepMap_continuous⟩
      ((P.seamEquation_iff_factorsThrough).mp h))

end PartialRealization

theorem adjunctionLower_eq_of_not_mem_range {A : Type v} {B : Type w} {X : Type u}
    {i : A → B} {φ : A → X} {x y : X} (hx : x ∉ range φ)
    (h : adjunctionLower (i := i) φ x = adjunctionLower (i := i) φ y) : x = y := by
  have key : ∀ p q : B ⊕ X, Relation.EqvGen (adjunctionRel i φ) p q →
      (p = Sum.inr x ↔ q = Sum.inr x) := by
    intro p q hpq
    induction hpq with
    | rel a b hab =>
      obtain ⟨c, hc | hc⟩ := hab
      · obtain ⟨rfl, rfl⟩ := hc
        exact ⟨fun h => absurd h (by simp),
          fun h => absurd (hx ⟨c, Sum.inr.inj h⟩) (by simp)⟩
      · obtain ⟨rfl, rfl⟩ := hc
        exact ⟨fun h => absurd (hx ⟨c, Sum.inr.inj h⟩) (by simp),
          fun h => absurd h (by simp)⟩
    | refl a => exact Iff.rfl
    | symm a b hab ih => exact ih.symm
    | trans a b c hab hbc ih1 ih2 => exact ih1.trans ih2
  have hgen : Relation.EqvGen (adjunctionRel i φ) (Sum.inr x) (Sum.inr y) :=
    Quot.eq.mp (show Quot.mk (adjunctionRel i φ) (Sum.inr x) =
      Quot.mk (adjunctionRel i φ) (Sum.inr y) from h)
  exact (Sum.inr.inj ((key (Sum.inr x) (Sum.inr y) hgen).mp rfl)).symm

theorem injOn_adjunctionLower_compl_range {A : Type v} {B : Type w} {X : Type u}
    {i : A → B} (φ : A → X) :
    Set.InjOn (adjunctionLower (i := i) φ) (range φ)ᶜ := by
  intro x hx y hy h
  exact adjunctionLower_eq_of_not_mem_range hx h


namespace MarkedManifoldGraph

theorem disjoint_collar_if_flags_ne {N : ClosedOrientedManifold.{u} 3} {B B' : MarkedBall N}
    (hdisj : Disjoint B.collar B'.collar) {b b' : Bool} (hbb : b ≠ b') :
    Disjoint (if b then B' else B).collar (if b' then B' else B).collar := by
  have hsymm := hdisj.symm
  cases b <;> cases b' <;> simp_all

abbrev oneVertexLoop (N : ConnectedClosedOrientedManifold.{0} 3)
    (B B' : MarkedBall N.toClosedOrientedManifold) (hdisj : Disjoint B.collar B'.collar) :
    MarkedManifoldGraph.{0} where
  Vertex := PUnit
  Edge := PUnit
  vertexFintype := inferInstance
  edgeFintype := inferInstance
  edgeDecidableEq := inferInstance
  endpoint := fun _ _ => PUnit.unit
  vertexManifold := fun _ => N
  flag := fun _ b => if b then B' else B
  flag_collar_disjoint := fun v f f' hne => by
    obtain ⟨⟨u, b⟩, hb⟩ := f
    obtain ⟨⟨u', b'⟩, hb'⟩ := f'
    have hbb : b ≠ b' := fun h => hne (Subtype.ext (Prod.ext (Subsingleton.elim u u') h))
    subst hb
    cases hb'
    exact disjoint_collar_if_flags_ne hdisj hbb
  attach := fun _ b => (if b then B' else B).boundary
  attach_eq := fun _ b z => rfl

end MarkedManifoldGraph

namespace PartialRealization

variable {G : MarkedManifoldGraph.{u}} {S : Finset G.Edge}

def FlagMarkerTransport (P : PartialRealization G S) (marked : Bool → MarkedBall P.realization)
    (e : G.Edge) (he : e ∉ S) : Prop :=
  ∀ (b : Bool) (x : ClosedCell 3),
    (marked b).ball x = P.vertexPiece (G.endpoint e b) (G.flagBallPoint S e b he x)

def MarkerReserve (P : PartialRealization G S) (marked : Bool → MarkedBall P.realization)
    (e : G.Edge) : Prop :=
  ∀ b : Bool, (marked b).collarBudget ≤ (G.flag e b).collarBudget

def MarkerCollarTransport (P : PartialRealization G S) (marked : Bool → MarkedBall P.realization)
    (e : G.Edge) : Prop :=
  ∀ b : Bool, range (fun x : {y : (G.vertexManifold (G.endpoint e b)).Carrier //
      y ∈ (G.flag e b).collar ∧ y ∉ G.removedBallSet S (G.endpoint e b)} =>
        P.vertexPiece (G.endpoint e b) ⟨x.1, x.2.2⟩) ⊆ (marked b).collar

theorem range_markedBall_subset_vertexPiece (P : PartialRealization G S)
    {marked : Bool → MarkedBall P.realization} {e : G.Edge} {he : e ∉ S}
    (h : P.FlagMarkerTransport marked e he) (b : Bool) :
    range (marked b).ball ⊆ range (P.vertexPiece (G.endpoint e b)) :=
  fun _ ⟨x, hx⟩ => ⟨G.flagBallPoint S e b he x, (h b x).symm.trans hx⟩

theorem exists_markedBall_eq_vertexPiece (P : PartialRealization G S)
    {marked : Bool → MarkedBall P.realization} {e : G.Edge} {he : e ∉ S}
    (h : P.FlagMarkerTransport marked e he) (b : Bool) (x : ClosedCell 3) :
    ∃ y : G.puncturedCarrier S (G.endpoint e b),
      (marked b).ball x = P.vertexPiece (G.endpoint e b) y :=
  ⟨G.flagBallPoint S e b he x, h b x⟩

end PartialRealization

namespace PartialRealization

def oneVertexLoopEmpty (N : ConnectedClosedOrientedManifold.{0} 3)
    (B B' : MarkedBall N.toClosedOrientedManifold) (hdisj : Disjoint B.collar B'.collar) :
    PartialRealization (MarkedManifoldGraph.oneVertexLoop N B B' hdisj) (∅ : Finset PUnit) where
  realization := N.toClosedOrientedManifold
  vertexPiece := fun _ => ⟨Subtype.val, continuous_subtype_val⟩
  cylinderPiece := fun e he => absurd he (Finset.notMem_empty e)
  survivingFlag := fun _ _ => B
  covers := fun x =>
    Or.inl ⟨PUnit.unit,
      ⟨x, by rintro ⟨e, he, -, -⟩; exact Finset.notMem_empty e he⟩, rfl⟩
  survivingFlag_collar_disjoint := fun _ _ _ _ hne => absurd rfl hne

theorem flagMarkerTransport_oneVertexLoopEmpty (N : ConnectedClosedOrientedManifold.{0} 3)
    (B B' : MarkedBall N.toClosedOrientedManifold) (hdisj : Disjoint B.collar B'.collar) :
    (oneVertexLoopEmpty N B B' hdisj).FlagMarkerTransport (fun b => if b then B' else B)
      PUnit.unit (Finset.notMem_empty PUnit.unit) :=
  fun _ _ => rfl

theorem markerReserve_oneVertexLoopEmpty (N : ConnectedClosedOrientedManifold.{0} 3)
    (B B' : MarkedBall N.toClosedOrientedManifold) (hdisj : Disjoint B.collar B'.collar) :
    (oneVertexLoopEmpty N B B' hdisj).MarkerReserve (fun b => if b then B' else B) PUnit.unit :=
  fun _ => le_refl _

theorem markerCollarTransport_oneVertexLoopEmpty (N : ConnectedClosedOrientedManifold.{0} 3)
    (B B' : MarkedBall N.toClosedOrientedManifold) (hdisj : Disjoint B.collar B'.collar) :
    (oneVertexLoopEmpty N B B' hdisj).MarkerCollarTransport (fun b => if b then B' else B)
      PUnit.unit := by
  intro b y hy
  obtain ⟨x, rfl⟩ := hy
  exact x.2.1

theorem injOn_vertexPiece_oneVertexLoopEmpty (N : ConnectedClosedOrientedManifold.{0} 3)
    (B B' : MarkedBall N.toClosedOrientedManifold) (hdisj : Disjoint B.collar B'.collar) :
    Set.InjOn ((oneVertexLoopEmpty N B B' hdisj).vertexPiece PUnit.unit)
      (range ((MarkedManifoldGraph.oneVertexLoop N B B' hdisj).flagBallPoint ∅ PUnit.unit false
          (Finset.notMem_empty PUnit.unit)) ∪
        range ((MarkedManifoldGraph.oneVertexLoop N B B' hdisj).flagBallPoint ∅ PUnit.unit true
          (Finset.notMem_empty PUnit.unit))) := by
  intro a _ b _ h
  exact Subtype.ext h

theorem not_flagMarkerTransport_survivingFlag_oneVertexLoopEmpty
    (N : ConnectedClosedOrientedManifold.{0} 3)
    (B B' : MarkedBall N.toClosedOrientedManifold) (hdisj : Disjoint B.collar B'.collar)
    (hinj : Set.InjOn ((oneVertexLoopEmpty N B B' hdisj).vertexPiece PUnit.unit)
      (range ((MarkedManifoldGraph.oneVertexLoop N B B' hdisj).flagBallPoint ∅ PUnit.unit false
          (Finset.notMem_empty PUnit.unit)) ∪
        range ((MarkedManifoldGraph.oneVertexLoop N B B' hdisj).flagBallPoint ∅ PUnit.unit true
          (Finset.notMem_empty PUnit.unit)))) :
    ¬ (oneVertexLoopEmpty N B B' hdisj).FlagMarkerTransport
      (fun _ => (oneVertexLoopEmpty N B B' hdisj).survivingFlag PUnit.unit
        (Finset.notMem_empty PUnit.unit))
      PUnit.unit (Finset.notMem_empty PUnit.unit) := by
  intro htrans
  have hballs : B.ball = B'.ball := by
    funext x
    have h1 := htrans false x
    have h2 := htrans true x
    have h3 := h1.symm.trans h2
    exact congrArg Subtype.val (hinj
      (Or.inl (mem_range_self (f := (MarkedManifoldGraph.oneVertexLoop N B B' hdisj).flagBallPoint
        ∅ PUnit.unit false (Finset.notMem_empty PUnit.unit)) x))
      (Or.inr (mem_range_self (f := (MarkedManifoldGraph.oneVertexLoop N B B' hdisj).flagBallPoint
        ∅ PUnit.unit true (Finset.notMem_empty PUnit.unit)) x)) h3)
  refine Set.disjoint_left.mp (MarkedBall.disjoint_range_ball hdisj)
    (mem_range_self (f := B.ball) (⟨0, by simp⟩ : ClosedCell 3)) ?_
  rw [← hballs]
  exact mem_range_self (f := B.ball) (⟨0, by simp⟩ : ClosedCell 3)

end PartialRealization

section OrientationSign

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

theorem det_neg_trans_neg_pos (L M : E ≃ₗ[ℝ] E) (hL : (LinearEquiv.det L : ℝ) < 0)
    (hM : (LinearEquiv.det M : ℝ) < 0) : 0 < (LinearEquiv.det (L.trans M) : ℝ) := by
  rw [LinearEquiv.det_trans, Units.val_mul]
  exact mul_pos_of_neg_of_neg hM hL

theorem det_neg_symm_neg (L : E ≃ₗ[ℝ] E) (hL : (LinearEquiv.det L : ℝ) < 0) :
    (LinearEquiv.det L.symm : ℝ) < 0 := by
  rw [LinearEquiv.det_symm, map_inv, Units.val_inv_eq_inv_val]
  exact inv_lt_zero'.mpr hL

theorem exists_det_neg : ∃ σ : ℝ, σ < 0 := ⟨-1, by norm_num⟩

end OrientationSign

end DifferentialGeometry.Topology
