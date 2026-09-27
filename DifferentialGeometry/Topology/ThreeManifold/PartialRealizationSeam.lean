import DifferentialGeometry.Topology.ThreeManifold.PartialRealizationAnalytic
import DifferentialGeometry.Topology.Attachment.SequentialGluing

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology

local instance seamClosedCellCharted : ChartedSpace (EuclideanHalfSpace 3) (ClosedCell 3) :=
  Handle.closedCellChartedSpaceSucc 2

local instance seamClosedCellIsManifold : IsManifold (𝓡∂ 3) ∞ (ClosedCell 3) :=
  Handle.closedCellIsManifold 2

universe u

local notation "S²" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "Tube" => S² × Set.Icc (-2 : ℝ) 2

theorem sphereToClosedCell_injective : Function.Injective sphereToClosedCell := by
  intro z w h
  exact Subtype.ext (congrArg (fun u : ClosedCell 3 => (u : EuclideanSpace ℝ (Fin 3))) h)

theorem isEmbedding_sphereToClosedCell : Topology.IsEmbedding sphereToClosedCell :=
  ⟨Topology.IsInducing.subtypeVal.of_comp_iff.mp
      (show Topology.IsInducing
        ((Subtype.val : ClosedCell 3 → EuclideanSpace ℝ (Fin 3)) ∘ sphereToClosedCell)
        from Topology.IsInducing.subtypeVal),
    sphereToClosedCell_injective⟩

theorem tubeEndLevel_false_ne_true : tubeEndLevel false ≠ tubeEndLevel true := by
  intro h
  have hval := congrArg (fun t : Set.Icc (-2 : ℝ) 2 => (t : ℝ)) h
  rw [tubeEndLevel_false, tubeEndLevel_true] at hval
  norm_num at hval

theorem tubeEndLevel_ne {b b' : Bool} (h : b ≠ b') : tubeEndLevel b ≠ tubeEndLevel b' := by
  cases b <;> cases b'
  · exact absurd rfl h
  · exact tubeEndLevel_false_ne_true
  · exact fun hh => tubeEndLevel_false_ne_true hh.symm
  · exact absurd rfl h

namespace MarkedBall

variable {N : ClosedOrientedManifold.{u} 3}

theorem ball_ne_of_disjoint_collar {B B' : MarkedBall N} (h : Disjoint B.collar B'.collar) :
    B.ball ≠ B'.ball := by
  intro hball
  have hx : B.ball (closedCellCenter 3) ∈ range B.ball := mem_range_self _
  exact (Set.disjoint_left.mp (disjoint_range_ball h) hx) (by rw [← hball]; exact hx)

end MarkedBall

namespace MarkedManifoldGraph

variable (G : MarkedManifoldGraph.{u})

theorem flagBoundary_injective (S : Finset G.Edge) (e : G.Edge) (b : Bool) :
    Function.Injective (G.flagBoundaryPoint S e b) := by
  intro z w h
  have hb : (G.flag e b).ball (sphereToClosedCell z) =
      (G.flag e b).ball (sphereToClosedCell w) := congrArg Subtype.val h
  exact sphereToClosedCell_injective ((G.flag e b).ball_embedding.isEmbedding.injective hb)

theorem isEmbedding_flagBoundaryPoint (S : Finset G.Edge) (e : G.Edge) (b : Bool) :
    Topology.IsEmbedding (G.flagBoundaryPoint S e b) :=
  ((G.flag e b).ball_embedding.isEmbedding.comp isEmbedding_sphereToClosedCell).codRestrict
    {x | x ∉ G.removedBallSet S (G.endpoint e b)} fun z => (G.flagBoundaryPoint S e b z).2

def stepLeftLeg (S : Finset G.Edge) (e : G.Edge) : Bool → S² → G.stepCarrier S e
  | false, z => Sum.inl (G.flagBoundaryPoint (insert e S) e false z)
  | true, z => Sum.inr (Sum.inr (G.flagBoundaryPoint (insert e S) e true z))

def stepTubeEndLeg (S : Finset G.Edge) (e : G.Edge) (b : Bool) : S² → G.stepCarrier S e :=
  fun z => Sum.inr (Sum.inl (z, tubeEndLevel b))

theorem isEmbedding_stepLeftLeg (S : Finset G.Edge) (e : G.Edge) (b : Bool) :
    Topology.IsEmbedding (G.stepLeftLeg S e b) := by
  cases b with
  | false =>
    exact Topology.IsEmbedding.inl.comp (isEmbedding_flagBoundaryPoint G (insert e S) e false)
  | true =>
    exact Topology.IsEmbedding.inr.comp (Topology.IsEmbedding.inr.comp
      (isEmbedding_flagBoundaryPoint G (insert e S) e true))

theorem isEmbedding_stepTubeEndLeg (S : Finset G.Edge) (e : G.Edge) (b : Bool) :
    Topology.IsEmbedding (G.stepTubeEndLeg S e b) :=
  Topology.IsEmbedding.inr.comp
    (Topology.IsEmbedding.inl.comp (isEmbedding_prodMkLeft (tubeEndLevel b)))

def stepAttaching (S : Finset G.Edge) (e : G.Edge) (b : Bool) :
    ↥(range (G.stepLeftLeg S e b)) ≃ₜ ↥(range (G.stepTubeEndLeg S e b)) :=
  ((isEmbedding_stepLeftLeg G S e b).toHomeomorph).symm.trans
    ((isEmbedding_stepTubeEndLeg G S e b).toHomeomorph)

def stepBoundaryGluing (S : Finset G.Edge) (e : G.Edge) :
    BoundaryGluing (G.stepCarrier S e) Bool where
  left b := range (G.stepLeftLeg S e b)
  right b := range (G.stepTubeEndLeg S e b)
  attaching b := stepAttaching G S e b
  isClosed_left b := isClosed_range_of_continuous_of_compactSpace
    (isEmbedding_stepLeftLeg G S e b).toIsInducing.continuous
  isClosed_right b := isClosed_range_of_continuous_of_compactSpace
    (isEmbedding_stepTubeEndLeg G S e b).toIsInducing.continuous
  disjoint_left_right b := by
    rw [Set.disjoint_left]
    intro x hx hy
    cases b with
    | false =>
      rcases hx with ⟨z, rfl⟩
      rcases hy with ⟨w, hw⟩
      have hw' : (Sum.inr (Sum.inl (w, tubeEndLevel false)) : G.stepCarrier S e) =
          Sum.inl (G.flagBoundaryPoint (insert e S) e false z) := hw
      injection hw'
    | true =>
      rcases hx with ⟨z, rfl⟩
      rcases hy with ⟨w, hw⟩
      have hw' : (Sum.inr (Sum.inl (w, tubeEndLevel true)) : G.stepCarrier S e) =
          Sum.inr (Sum.inr (G.flagBoundaryPoint (insert e S) e true z)) := hw
      injection hw' with h1
      injection h1
  disjoint_blocks i j hij := by
    cases i <;> cases j
    · exact absurd rfl hij
    · rw [Set.disjoint_left]
      intro x hx hy
      rcases hx with ⟨z, rfl⟩ | ⟨z, rfl⟩
      · rcases hy with ⟨w, hw⟩ | ⟨w, hw⟩
        · have hw' : (Sum.inr (Sum.inr (G.flagBoundaryPoint (insert e S) e true w)) :
              G.stepCarrier S e) = Sum.inl (G.flagBoundaryPoint (insert e S) e false z) := hw
          injection hw'
        · have hw' : (Sum.inr (Sum.inl (w, tubeEndLevel true)) : G.stepCarrier S e) =
              Sum.inl (G.flagBoundaryPoint (insert e S) e false z) := hw
          injection hw'
      · rcases hy with ⟨w, hw⟩ | ⟨w, hw⟩
        · have hw' : (Sum.inr (Sum.inr (G.flagBoundaryPoint (insert e S) e true w)) :
              G.stepCarrier S e) = Sum.inr (Sum.inl (z, tubeEndLevel false)) := hw
          injection hw' with h1
          injection h1
        · have hw' : (Sum.inr (Sum.inl (w, tubeEndLevel true)) : G.stepCarrier S e) =
              Sum.inr (Sum.inl (z, tubeEndLevel false)) := hw
          injection hw' with h1
          injection h1 with h2
          injection h2 with _ h3
          exact tubeEndLevel_ne (by simp) h3
    · rw [Set.disjoint_left]
      intro x hx hy
      rcases hx with ⟨z, rfl⟩ | ⟨z, rfl⟩
      · rcases hy with ⟨w, hw⟩ | ⟨w, hw⟩
        · have hw' : (Sum.inl (G.flagBoundaryPoint (insert e S) e false w) :
              G.stepCarrier S e) =
              Sum.inr (Sum.inr (G.flagBoundaryPoint (insert e S) e true z)) := hw
          injection hw'
        · have hw' : (Sum.inr (Sum.inl (w, tubeEndLevel false)) : G.stepCarrier S e) =
              Sum.inr (Sum.inr (G.flagBoundaryPoint (insert e S) e true z)) := hw
          injection hw' with h1
          injection h1
      · rcases hy with ⟨w, hw⟩ | ⟨w, hw⟩
        · have hw' : (Sum.inl (G.flagBoundaryPoint (insert e S) e false w) :
              G.stepCarrier S e) = Sum.inr (Sum.inl (z, tubeEndLevel true)) := hw
          injection hw'
        · have hw' : (Sum.inr (Sum.inl (w, tubeEndLevel false)) : G.stepCarrier S e) =
              Sum.inr (Sum.inl (z, tubeEndLevel true)) := hw
          injection hw' with h1
          injection h1 with h2
          injection h2 with _ h3
          exact tubeEndLevel_ne (by simp) h3
    · exact absurd rfl hij

theorem stepAttaching_coe (S : Finset G.Edge) (e : G.Edge) (b : Bool) (z : S²)
    (hx : G.stepLeftLeg S e b z ∈ range (G.stepLeftLeg S e b)) :
    ((stepAttaching G S e b) ⟨G.stepLeftLeg S e b z, hx⟩ : G.stepCarrier S e) =
      G.stepTubeEndLeg S e b z := by
  have hstep : ((isEmbedding_stepLeftLeg G S e b).toHomeomorph).symm
      ⟨G.stepLeftLeg S e b z, hx⟩ = z := by
    refine ((isEmbedding_stepLeftLeg G S e b).toHomeomorph).injective ?_
    rw [Homeomorph.apply_symm_apply]
    exact Subtype.ext
      (Topology.IsEmbedding.toHomeomorph_apply_coe (isEmbedding_stepLeftLeg G S e b) z)
  rw [stepAttaching, Homeomorph.trans_apply, hstep]
  exact Topology.IsEmbedding.toHomeomorph_apply_coe (isEmbedding_stepTubeEndLeg G S e b) z

theorem stepBoundaryGluing_attaching_coe (S : Finset G.Edge) (e : G.Edge) (b : Bool) (z : S²)
    (hx : G.stepLeftLeg S e b z ∈ (G.stepBoundaryGluing S e).left b) :
    ((G.stepBoundaryGluing S e).attaching b ⟨G.stepLeftLeg S e b z, hx⟩ :
        G.stepCarrier S e) = G.stepTubeEndLeg S e b z :=
  stepAttaching_coe G S e b z hx

theorem stepBoundaryGluing_attaching_symm_coe (S : Finset G.Edge) (e : G.Edge) (b : Bool)
    (z : S²) (hy : G.stepTubeEndLeg S e b z ∈ (G.stepBoundaryGluing S e).right b) :
    (((G.stepBoundaryGluing S e).attaching b).symm ⟨G.stepTubeEndLeg S e b z, hy⟩ :
        G.stepCarrier S e) = G.stepLeftLeg S e b z := by
  have hs : ((G.stepBoundaryGluing S e).attaching b).symm
      ⟨G.stepTubeEndLeg S e b z, hy⟩ =
      ⟨G.stepLeftLeg S e b z, mem_range_self z⟩ := by
    apply ((G.stepBoundaryGluing S e).attaching b).injective
    rw [Homeomorph.apply_symm_apply]
    exact Subtype.ext (stepBoundaryGluing_attaching_coe G S e b z (mem_range_self _)).symm
  exact congrArg Subtype.val hs

theorem stepBoundaryGluing_flip_left (S : Finset G.Edge) (e : G.Edge) (b : Bool) (z : S²) :
    (G.stepBoundaryGluing S e).flip b (G.stepLeftLeg S e b z) = G.stepTubeEndLeg S e b z := by
  rw [BoundaryGluing.flip_of_mem_left (G := G.stepBoundaryGluing S e) (mem_range_self _)]
  exact stepBoundaryGluing_attaching_coe G S e b z (mem_range_self _)

theorem stepBoundaryGluing_flip_right (S : Finset G.Edge) (e : G.Edge) (b : Bool) (z : S²) :
    (G.stepBoundaryGluing S e).flip b (G.stepTubeEndLeg S e b z) = G.stepLeftLeg S e b z := by
  rw [BoundaryGluing.flip_of_mem_right (G := G.stepBoundaryGluing S e) (mem_range_self _)]
  exact stepBoundaryGluing_attaching_symm_coe G S e b z (mem_range_self _)

theorem stepBoundaryGluing_rel_of_stepRel (S : Finset G.Edge) (e : G.Edge)
    {x y : G.stepCarrier S e} (h : G.stepRel S e x y) :
    (G.stepBoundaryGluing S e).rel x y := by
  have hsymm : ∀ {a b : G.stepCarrier S e}, (G.stepBoundaryGluing S e).rel a b →
      (G.stepBoundaryGluing S e).rel b a := fun hab =>
    (G.stepBoundaryGluing S e).isEquivalence_rel.symm hab
  rcases h with ⟨z, rfl, rfl⟩ | ⟨z, rfl, rfl⟩ | ⟨z, rfl, rfl⟩ | ⟨z, rfl, rfl⟩
  · have hrel := BoundaryGluing.rel_of_attaching (G.stepBoundaryGluing S e) false
      ⟨G.stepLeftLeg S e false z, mem_range_self _⟩
    rw [stepBoundaryGluing_attaching_coe G S e false z (mem_range_self _)] at hrel
    exact hsymm hrel
  · have hrel := BoundaryGluing.rel_of_attaching (G.stepBoundaryGluing S e) false
      ⟨G.stepLeftLeg S e false z, mem_range_self _⟩
    rw [stepBoundaryGluing_attaching_coe G S e false z (mem_range_self _)] at hrel
    exact hrel
  · have hrel := BoundaryGluing.rel_of_attaching (G.stepBoundaryGluing S e) true
      ⟨G.stepLeftLeg S e true z, mem_range_self _⟩
    rw [stepBoundaryGluing_attaching_coe G S e true z (mem_range_self _)] at hrel
    exact hrel
  · have hrel := BoundaryGluing.rel_of_attaching (G.stepBoundaryGluing S e) true
      ⟨G.stepLeftLeg S e true z, mem_range_self _⟩
    rw [stepBoundaryGluing_attaching_coe G S e true z (mem_range_self _)] at hrel
    exact hsymm hrel

theorem stepBoundaryGluing_rel_of_eqvGen (S : Finset G.Edge) (e : G.Edge)
    {x y : G.stepCarrier S e} (h : Relation.EqvGen (G.stepRel S e) x y) :
    (G.stepBoundaryGluing S e).rel x y := by
  induction h with
  | rel a b hab => exact stepBoundaryGluing_rel_of_stepRel G S e hab
  | refl => exact Or.inl rfl
  | symm a b hab ih => exact (G.stepBoundaryGluing S e).isEquivalence_rel.symm ih
  | trans a b c hab hbc ih1 ih2 =>
    exact (G.stepBoundaryGluing S e).isEquivalence_rel.trans ih1 ih2

theorem eqvGen_stepRel_of_stepBoundaryGluing_rel (S : Finset G.Edge) (e : G.Edge)
    {x y : G.stepCarrier S e} (h : (G.stepBoundaryGluing S e).rel x y) :
    Relation.EqvGen (G.stepRel S e) x y := by
  rcases h with rfl | ⟨i, hx, hy⟩
  · exact Relation.EqvGen.refl x
  · subst hy
    cases i with
    | false =>
      rcases (mem_union x _ _).mp hx with hxl | hxr
      · obtain ⟨z, rfl⟩ := hxl
        rw [stepBoundaryGluing_flip_left]
        exact Relation.EqvGen.rel _ _ (Or.inl ⟨z, rfl, rfl⟩)
      · obtain ⟨z, rfl⟩ := hxr
        rw [stepBoundaryGluing_flip_right]
        exact Relation.EqvGen.rel _ _ (Or.inr (Or.inl ⟨z, rfl, rfl⟩))
    | true =>
      rcases (mem_union x _ _).mp hx with hxl | hxr
      · obtain ⟨z, rfl⟩ := hxl
        rw [stepBoundaryGluing_flip_left]
        exact Relation.EqvGen.rel _ _ (Or.inr (Or.inr (Or.inr ⟨z, rfl, rfl⟩)))
      · obtain ⟨z, rfl⟩ := hxr
        rw [stepBoundaryGluing_flip_right]
        exact Relation.EqvGen.rel _ _ (Or.inr (Or.inr (Or.inl ⟨z, rfl, rfl⟩)))

theorem stepBoundaryGluing_rel_iff_eqvGen (S : Finset G.Edge) (e : G.Edge)
    (x y : G.stepCarrier S e) :
    (G.stepBoundaryGluing S e).rel x y ↔ Relation.EqvGen (G.stepRel S e) x y :=
  ⟨eqvGen_stepRel_of_stepBoundaryGluing_rel G S e,
    stepBoundaryGluing_rel_of_eqvGen G S e⟩

theorem eq_of_eqvGen_stepRel_of_notMem_block (S : Finset G.Edge) (e : G.Edge)
    {x y : G.stepCarrier S e} (hx : ∀ i : Bool, x ∉ (G.stepBoundaryGluing S e).block i)
    (h : Relation.EqvGen (G.stepRel S e) x y) : x = y :=
  BoundaryGluing.eq_of_rel_of_notMem (G.stepBoundaryGluing S e) hx
    ((stepBoundaryGluing_rel_iff_eqvGen G S e x y).mpr h)

def stepQuotientHomeomorphBoundaryGluing (S : Finset G.Edge) (e : G.Edge) :
    G.stepQuotient S e ≃ₜ Quotient (G.stepBoundaryGluing S e).setoid where
  toFun := Quot.lift (fun x => Quotient.mk'' x)
    (fun _ _ hab => Quotient.sound (stepBoundaryGluing_rel_of_stepRel G S e hab))
  invFun := Quotient.lift (fun x => Quot.mk (G.stepRel S e) x)
    (fun _ _ hab => Quot.eq.mpr ((stepBoundaryGluing_rel_iff_eqvGen G S e _ _).mp hab))
  left_inv := by
    intro q
    induction q using Quot.inductionOn with
    | _ x => rfl
  right_inv := by
    intro q
    induction q using Quotient.inductionOn with
    | _ x => rfl
  continuous_toFun := continuous_quot_lift _ continuous_quotient_mk'
  continuous_invFun := Continuous.quotient_lift continuous_quot_mk _

theorem stepBoundaryGluing_setoid_eq_sup (S : Finset G.Edge) (e : G.Edge) :
    (G.stepBoundaryGluing S e).setoid =
      ((G.stepBoundaryGluing S e).restrict ({false} : Set Bool)).setoid ⊔
        ((G.stepBoundaryGluing S e).restrict ({true} : Set Bool)).setoid := by
  have huniv : (({false} : Set Bool) ∪ {true}) = univ := by
    ext b
    cases b <;> simp
  have hsup := BoundaryGluing.setoid_restrict_union (G.stepBoundaryGluing S e)
    ({false} : Set Bool) {true}
  rw [huniv, BoundaryGluing.setoid_restrict_univ] at hsup
  exact hsup

theorem t2Space_stepQuotient (S : Finset G.Edge) (e : G.Edge)
    [CompactSpace (G.stepCarrier S e)] : T2Space (G.stepQuotient S e) :=
  Homeomorph.t2Space (G.stepQuotientHomeomorphBoundaryGluing S e).symm

abbrev assemblyCarrier (S : Finset G.Edge) : Type u :=
  (Σ v : G.Vertex, G.puncturedCarrier S v) ⊕
    (Σ f : {f : G.Edge // f ∈ S}, G.cylinderCarrier f.1)

def stepAssemblyRel (S : Finset G.Edge) (e : G.Edge) :
    G.assemblyCarrier (insert e S) → G.assemblyCarrier (insert e S) → Prop :=
  fun x y =>
    (∃ z : S², x = Sum.inl ⟨G.endpoint e false,
        G.flagBoundaryPoint (insert e S) e false z⟩ ∧
      y = Sum.inr ⟨⟨e, Finset.mem_insert_self e S⟩, (z, tubeEndLevel false)⟩) ∨
    (∃ z : S², y = Sum.inl ⟨G.endpoint e false,
        G.flagBoundaryPoint (insert e S) e false z⟩ ∧
      x = Sum.inr ⟨⟨e, Finset.mem_insert_self e S⟩, (z, tubeEndLevel false)⟩) ∨
    (∃ z : S², x = Sum.inr ⟨⟨e, Finset.mem_insert_self e S⟩, (z, tubeEndLevel true)⟩ ∧
      y = Sum.inl ⟨G.endpoint e true,
        G.flagBoundaryPoint (insert e S) e true z⟩) ∨
    (∃ z : S², y = Sum.inr ⟨⟨e, Finset.mem_insert_self e S⟩, (z, tubeEndLevel true)⟩ ∧
      x = Sum.inl ⟨G.endpoint e true,
        G.flagBoundaryPoint (insert e S) e true z⟩)

theorem stepAssemblyRel_quot_mk_pointSet (S : Finset G.Edge) (e : G.Edge) :
    Continuous (Quot.mk (G.stepAssemblyRel S e)) ∧
      Function.Surjective (Quot.mk (G.stepAssemblyRel S e)) ∧
      (∀ z : S², Quot.mk (G.stepAssemblyRel S e)
          (Sum.inl ⟨G.endpoint e false,
            G.flagBoundaryPoint (insert e S) e false z⟩) =
        Quot.mk (G.stepAssemblyRel S e)
          (Sum.inr ⟨⟨e, Finset.mem_insert_self e S⟩, (z, tubeEndLevel false)⟩)) ∧
      (∀ z : S², Quot.mk (G.stepAssemblyRel S e)
          (Sum.inr ⟨⟨e, Finset.mem_insert_self e S⟩, (z, tubeEndLevel true)⟩) =
        Quot.mk (G.stepAssemblyRel S e)
          (Sum.inl ⟨G.endpoint e true,
            G.flagBoundaryPoint (insert e S) e true z⟩)) ∧
      (∀ p q : G.assemblyCarrier (insert e S),
        Quot.mk (G.stepAssemblyRel S e) p = Quot.mk (G.stepAssemblyRel S e) q →
          Relation.EqvGen (G.stepAssemblyRel S e) p q) :=
  ⟨continuous_quot_mk, Quot.exists_rep, fun z => Quot.sound (Or.inl ⟨z, rfl, rfl⟩),
    fun z => Quot.sound (Or.inr (Or.inr (Or.inl ⟨z, rfl, rfl⟩))),
    fun _ _ h => Quot.eq.mp h⟩

end MarkedManifoldGraph

namespace PartialRealization

variable {G : MarkedManifoldGraph.{u}} {S : Finset G.Edge} {e : G.Edge}

structure FlagMarking (P : PartialRealization G S) where
  marked : (e : G.Edge) → (b : Bool) → e ∉ S → MarkedBall P.realization
  transport : ∀ (e : G.Edge) (b : Bool) (he : e ∉ S) (x : ClosedCell 3),
    (marked e b he).ball x = P.vertexPiece (G.endpoint e b) (G.flagBallPoint S e b he x)
  reserve : ∀ (e : G.Edge) (b : Bool) (he : e ∉ S),
    (marked e b he).collarBudget ≤ (G.flag e b).collarBudget
  collar_disjoint : ∀ (e e' : G.Edge) (b b' : Bool) (he : e ∉ S) (he' : e' ∉ S),
    (e, b) ≠ (e', b') → Disjoint (marked e b he).collar (marked e' b' he').collar

namespace FlagMarking

variable {P : PartialRealization G S} (M : P.FlagMarking)

def toSurvivingFlag (e : G.Edge) (he : e ∉ S) : MarkedBall P.realization :=
  M.marked e false he

theorem disjoint_toSurvivingFlag (e e' : G.Edge) (he : e ∉ S) (he' : e' ∉ S) (hne : e ≠ e') :
    Disjoint (M.toSurvivingFlag e he).collar (M.toSurvivingFlag e' he').collar :=
  M.collar_disjoint e e' false false he he' fun h => hne (Prod.mk.inj h).1

theorem toSurvivingFlag_transport (e : G.Edge) (he : e ∉ S) (x : ClosedCell 3) :
    (M.toSurvivingFlag e he).ball x = P.vertexPiece (G.endpoint e false)
      (G.flagBallPoint S e false he x) :=
  M.transport e false he x

end FlagMarking

def flagMarkingOneVertexLoopEmpty (N : ConnectedClosedOrientedManifold.{0} 3)
    (B B' : MarkedBall N.toClosedOrientedManifold) (hdisj : Disjoint B.collar B'.collar) :
    (oneVertexLoopEmpty N B B' hdisj).FlagMarking where
  marked := fun _ b _ => if b then B' else B
  transport := fun _ _ _ _ => rfl
  reserve := fun _ _ _ => le_refl _
  collar_disjoint := fun _ _ b b' _ _ hne => by
    have hbb : b ≠ b' := fun h => hne (Prod.ext rfl h)
    exact MarkedManifoldGraph.disjoint_collar_if_flags_ne hdisj hbb

theorem not_flagMarkerTransport_constBall_oneVertexLoopEmpty
    (N : ConnectedClosedOrientedManifold.{0} 3)
    (B B' : MarkedBall N.toClosedOrientedManifold) (hdisj : Disjoint B.collar B'.collar) :
    ¬ (oneVertexLoopEmpty N B B' hdisj).FlagMarkerTransport (fun _ => B)
      PUnit.unit (Finset.notMem_empty PUnit.unit) := by
  intro htrans
  have htrue : B.ball = B'.ball := by
    funext x
    have h : B.ball x = (if true then B' else B).ball x := htrans true x
    simpa using h
  exact MarkedBall.ball_ne_of_disjoint_collar hdisj htrue

theorem seamEquation_iff_boundaryGluing_rel (P : PartialRealization G (insert e S)) :
    P.SeamEquation e (Finset.mem_insert_self e S) ↔
      ∀ x y : G.stepCarrier S e,
        (G.stepBoundaryGluing S e).rel x y → P.stepMap x = P.stepMap y := by
  constructor
  · intro h x y hxy
    exact P.eqvGen_stepMap_eq ((P.seamEquation_iff_stepRel_related).mp h)
      (MarkedManifoldGraph.eqvGen_stepRel_of_stepBoundaryGluing_rel G S e hxy)
  · intro h
    exact (P.seamEquation_iff_stepRel_related).mpr fun x y hxy =>
      h x y (MarkedManifoldGraph.stepBoundaryGluing_rel_of_stepRel G S e hxy)

structure StepAssemblyData (G : MarkedManifoldGraph.{u}) (S : Finset G.Edge) (e : G.Edge) where
  realization : ClosedOrientedManifold.{u} 3
  quotient : Quot (G.stepAssemblyRel S e) ≃ₜ realization.Carrier
  survivingFlag : (f : G.Edge) → (b : Bool) → f ∉ insert e S → MarkedBall realization
  survivingFlag_transport : ∀ (f : G.Edge) (b : Bool) (hf : f ∉ insert e S)
    (x : ClosedCell 3),
    (survivingFlag f b hf).ball x = quotient (Quot.mk (G.stepAssemblyRel S e)
      (Sum.inl ⟨G.endpoint f b, G.flagBallPoint (insert e S) f b hf x⟩))
  survivingFlag_reserve : ∀ (f : G.Edge) (b : Bool) (hf : f ∉ insert e S),
    (survivingFlag f b hf).collarBudget ≤ (G.flag f b).collarBudget
  survivingFlag_collar_disjoint : ∀ (f f' : G.Edge) (b b' : Bool) (hf : f ∉ insert e S)
    (hf' : f' ∉ insert e S), (f, b) ≠ (f', b') →
    Disjoint (survivingFlag f b hf).collar (survivingFlag f' b' hf').collar

namespace StepAssemblyData

variable {G : MarkedManifoldGraph.{u}} {S : Finset G.Edge} {e : G.Edge}
variable (D : StepAssemblyData G S e)

def partialRealization : PartialRealization G (insert e S) where
  realization := D.realization
  vertexPiece v :=
    ⟨fun y => D.quotient (Quot.mk (G.stepAssemblyRel S e) (Sum.inl ⟨v, y⟩)),
      D.quotient.continuous.comp ((continuous_quot_mk).comp
        (continuous_inl.comp continuous_sigmaMk))⟩
  cylinderPiece f hf :=
    ⟨fun q => D.quotient (Quot.mk (G.stepAssemblyRel S e) (Sum.inr ⟨⟨f, hf⟩, q⟩)),
      D.quotient.continuous.comp ((continuous_quot_mk).comp
        (continuous_inr.comp continuous_sigmaMk))⟩
  survivingFlag f hf := D.survivingFlag f false hf
  covers x := by
    obtain ⟨s, hs⟩ := Quot.exists_rep (D.quotient.symm x)
    have hx : D.quotient (Quot.mk (G.stepAssemblyRel S e) s) = x := by
      rw [hs, Homeomorph.apply_symm_apply]
    rcases s with p | q
    · refine Or.inl ⟨p.1, ⟨p.2, ?_⟩⟩
      change D.quotient (Quot.mk (G.stepAssemblyRel S e) (Sum.inl ⟨p.1, p.2⟩)) = x
      exact hx
    · refine Or.inr ⟨q.1.1, q.1.2, ⟨q.2, ?_⟩⟩
      change D.quotient (Quot.mk (G.stepAssemblyRel S e) (Sum.inr ⟨q.1, q.2⟩)) = x
      exact hx
  survivingFlag_collar_disjoint f f' hf hf' hne :=
    D.survivingFlag_collar_disjoint f f' false false hf hf'
      (fun h => hne (Prod.mk.inj h).1)

theorem partialRealization_seamEquation :
    (D.partialRealization).SeamEquation e (Finset.mem_insert_self e S) := by
  constructor
  · intro z
    have hq : Quot.mk (G.stepAssemblyRel S e)
          (Sum.inr ⟨⟨e, Finset.mem_insert_self e S⟩, (z, tubeEndLevel false)⟩) =
        Quot.mk (G.stepAssemblyRel S e)
          (Sum.inl ⟨G.endpoint e false, G.flagBoundaryPoint (insert e S) e false z⟩) :=
      Quot.sound (Or.inr (Or.inl ⟨z, rfl, rfl⟩))
    exact congrArg D.quotient hq
  · intro z
    have hq : Quot.mk (G.stepAssemblyRel S e)
          (Sum.inr ⟨⟨e, Finset.mem_insert_self e S⟩, (z, tubeEndLevel true)⟩) =
        Quot.mk (G.stepAssemblyRel S e)
          (Sum.inl ⟨G.endpoint e true, G.flagBoundaryPoint (insert e S) e true z⟩) :=
      Quot.sound (Or.inr (Or.inr (Or.inl ⟨z, rfl, rfl⟩)))
    exact congrArg D.quotient hq

def partialRealizationFlagMarking : (D.partialRealization).FlagMarking where
  marked := D.survivingFlag
  transport := fun f b hf x => D.survivingFlag_transport f b hf x
  reserve := fun f b hf => D.survivingFlag_reserve f b hf
  collar_disjoint := fun f f' b b' hf hf' hne =>
    D.survivingFlag_collar_disjoint f f' b b' hf hf' hne

theorem exists_partialRealization_and_flagMarking (D : StepAssemblyData G S e) :
    ∃ P' : PartialRealization G (insert e S),
      P'.SeamEquation e (Finset.mem_insert_self e S) ∧ Nonempty P'.FlagMarking :=
  ⟨D.partialRealization, D.partialRealization_seamEquation,
    ⟨D.partialRealizationFlagMarking⟩⟩

end StepAssemblyData

end PartialRealization

end DifferentialGeometry.Topology
