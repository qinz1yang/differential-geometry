import DifferentialGeometry.Topology.Algebra.Group.FreeProduct.FreeFactor
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import DifferentialGeometry.Topology.VanKampen.TorsionFreeCover
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open CategoryTheory Set
open DifferentialGeometry.Topology.VanKampen
namespace GC.Topology
universe u
open private exists_coherent_connectors conjugationFunctor coboundaryFunctor
  from DifferentialGeometry.Topology.VanKampen.TorsionFreeCover

variable {X : Type u} [TopologicalSpace X] (U V : Set X) (x₀ : ↥(U ∩ V))

abbrev coreBase : U := ⟨x₀.val, x₀.property.1⟩
abbrev capBase : V := ⟨x₀.val, x₀.property.2⟩

structure CoherentCoreConnectors where
  path : ∀ x : U, FundamentalGroupoid.mk (coreBase U V x₀) ⟶ FundamentalGroupoid.mk x
  at_base : path (coreBase U V x₀) = 𝟙 _
  coherent : ∀ (x y : ↥(U ∩ V)) (p : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y),
    path (interToLeft U V x) ≫ (FundamentalGroupoid.map (interToLeft U V)).map p =
      path (interToLeft U V y)

theorem nonempty_coherentCoreConnectors [PathConnectedSpace U]
    (hthin : ∀ x y : ↥(U ∩ V), Subsingleton (Path.Homotopic.Quotient x y)) :
    Nonempty (CoherentCoreConnectors U V x₀) := by
  classical
  obtain ⟨k, hk⟩ := exists_coherent_connectors (interToLeft U V) (coreBase U V x₀) hthin
  let q : ∀ x : U, FundamentalGroupoid.mk (coreBase U V x₀) ⟶ FundamentalGroupoid.mk x :=
    fun x => if hx : x.val ∈ V then
      Groupoid.inv (k x₀) ≫ k ⟨x.val, x.property, hx⟩
    else ⟦PathConnectedSpace.somePath (coreBase U V x₀) x⟧
  refine ⟨⟨q, ?_, ?_⟩⟩
  · simp [q, x₀.property.2]
  · intro x y p
    change q ⟨x.val, x.property.1⟩ ≫ _ = q ⟨y.val, y.property.1⟩
    simp only [q, x.property.2, y.property.2, ↓reduceDIte]
    rw [Category.assoc, hk x y p]

abbrev OverlapGenerator := {c : ZerothHomotopy ↥(U ∩ V) // c ≠ ZerothHomotopy.mk x₀}
abbrev ThinOverlapGroup := Monoid.Coprod
  (FundamentalGroup U (coreBase U V x₀)) (FreeGroup (OverlapGenerator U V x₀))

noncomputable def overlapMark (c : ZerothHomotopy ↥(U ∩ V)) : ThinOverlapGroup U V x₀ := by
  classical
  exact if h : c = ZerothHomotopy.mk x₀ then 1 else
    Monoid.Coprod.inr (FreeGroup.of ⟨c, h⟩)

@[simp] theorem overlapMark_base : overlapMark U V x₀ (ZerothHomotopy.mk x₀) = 1 := by
  classical
  simp [overlapMark]

noncomputable def capWeight (x : V) : ThinOverlapGroup U V x₀ := by
  classical
  exact if hx : x.val ∈ U then
    overlapMark U V x₀ (ZerothHomotopy.mk ⟨x.val, hx, x.property⟩) else 1

@[simp] theorem capWeight_overlap (x : ↥(U ∩ V)) :
    capWeight U V x₀ (interToRight U V x) = overlapMark U V x₀ (ZerothHomotopy.mk x) := by
  classical
  simp [capWeight, interToRight, x.property.1]

@[simp] theorem capWeight_base : capWeight U V x₀ (capBase U V x₀) = 1 := by
  classical
  simp [capWeight, x₀.property.1]

def thinOverlapFunctorData (q : CoherentCoreConnectors U V x₀) :
    LocalFunctorData U V (SingleObj (ThinOverlapGroup U V x₀)) where
  left := (conjugationFunctor (FundamentalGroupoid.mk (coreBase U V x₀)) (fun x => q.path x.as)) ⋙
    (Monoid.Coprod.inl : FundamentalGroup U (coreBase U V x₀) →* ThinOverlapGroup U V x₀).toFunctor
  right := coboundaryFunctor (fun x : FundamentalGroupoid V => capWeight U V x₀ x.as)
  compatibility := by
    apply Functor.hext
    · intro x; rfl
    · intro x y p
      apply heq_of_eq
      change (Monoid.Coprod.inl : FundamentalGroup U (coreBase U V x₀) →* ThinOverlapGroup U V x₀) ((q.path (interToLeft U V x.as) ≫
          (FundamentalGroupoid.map (interToLeft U V)).map p ≫
          Groupoid.inv (q.path (interToLeft U V y.as))) : FundamentalGroup U (coreBase U V x₀)) =
        (capWeight U V x₀ (interToRight U V y.as))⁻¹ *
          capWeight U V x₀ (interToRight U V x.as)
      rw [← Category.assoc, q.coherent x.as y.as p, Groupoid.comp_inv]
      change (Monoid.Coprod.inl : FundamentalGroup U (coreBase U V x₀) →* ThinOverlapGroup U V x₀) 1 = _
      rw [map_one, capWeight_overlap, capWeight_overlap]
      have hc : ZerothHomotopy.mk x.as = ZerothHomotopy.mk y.as := ZerothHomotopy.sound p.out
      rw [hc, inv_mul_cancel]

section SimplyConnectedCap
variable [SimplyConnectedSpace V]

noncomputable def capConnector (x : V) :
    FundamentalGroupoid.mk (capBase U V x₀) ⟶ FundamentalGroupoid.mk x :=
  ⟦PathConnectedSpace.somePath (capBase U V x₀) x⟧

@[simp] theorem capConnector_base : capConnector U V x₀ (capBase U V x₀) = 𝟙 _ :=
  (inferInstance : Subsingleton (Path.Homotopic.Quotient (capBase U V x₀) (capBase U V x₀))).elim _ _

theorem capConnector_coherent (x y : V)
    (p : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) :
    capConnector U V x₀ x ≫ p = capConnector U V x₀ y :=
  (inferInstance : Subsingleton (Path.Homotopic.Quotient (capBase U V x₀) y)).elim _ _

variable (q : CoherentCoreConnectors U V x₀)

noncomputable def overlapLoop (x : ↥(U ∩ V)) : FundamentalGroup X x₀.val := by
  let a : FundamentalGroupoid.mk (x₀.val : X) ⟶ FundamentalGroupoid.mk (x.val : X) :=
    (FundamentalGroupoid.map (subsetToAmbient U)).map
      (X := FundamentalGroupoid.mk (coreBase U V x₀))
      (Y := FundamentalGroupoid.mk (interToLeft U V x)) (q.path (interToLeft U V x))
  let b : FundamentalGroupoid.mk (x₀.val : X) ⟶ FundamentalGroupoid.mk (x.val : X) :=
    (FundamentalGroupoid.map (subsetToAmbient V)).map
      (X := FundamentalGroupoid.mk (capBase U V x₀))
      (Y := FundamentalGroupoid.mk (interToRight U V x)) (capConnector U V x₀ (interToRight U V x))
  exact a ≫ Groupoid.inv b

theorem overlapLoop_eq {x y : ↥(U ∩ V)} (p : Path x y) :
    overlapLoop U V x₀ q x = overlapLoop U V x₀ q y := by
  let a : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y := ⟦p⟧
  let r : FundamentalGroupoid.mk x.val ⟶ FundamentalGroupoid.mk y.val :=
    (FundamentalGroupoid.map (subsetToAmbient (U ∩ V))).map a
  have hU := congrArg (fun t => (FundamentalGroupoid.map (subsetToAmbient U)).map t)
    (q.coherent x y a)
  have hV := congrArg (fun t => (FundamentalGroupoid.map (subsetToAmbient V)).map t)
    (capConnector_coherent U V x₀ (interToRight U V x) (interToRight U V y)
      ((FundamentalGroupoid.map (interToRight U V)).map a))
  rw [Functor.map_comp] at hU hV
  change (FundamentalGroupoid.map (subsetToAmbient U)).map
    (X := FundamentalGroupoid.mk (coreBase U V x₀)) (q.path (interToLeft U V x)) ≫ r =
    (FundamentalGroupoid.map (subsetToAmbient U)).map
    (X := FundamentalGroupoid.mk (coreBase U V x₀)) (q.path (interToLeft U V y)) at hU
  change (FundamentalGroupoid.map (subsetToAmbient V)).map
      (capConnector U V x₀ (interToRight U V x)) ≫ r =
    (FundamentalGroupoid.map (subsetToAmbient V)).map
      (capConnector U V x₀ (interToRight U V y)) at hV
  unfold overlapLoop
  rw [← hU, ← hV]
  simp [Category.assoc]

@[simp] theorem overlapLoop_base : overlapLoop U V x₀ q x₀ = 1 := by
  change (FundamentalGroupoid.map (subsetToAmbient U)).map
    (X := FundamentalGroupoid.mk (coreBase U V x₀))
    (Y := FundamentalGroupoid.mk (coreBase U V x₀)) (q.path (coreBase U V x₀)) ≫
    Groupoid.inv ((FundamentalGroupoid.map (subsetToAmbient V)).map
      (X := FundamentalGroupoid.mk (capBase U V x₀))
      (Y := FundamentalGroupoid.mk (capBase U V x₀)) (capConnector U V x₀ (capBase U V x₀))) = _
  rw [q.at_base, capConnector_base]
  simp only [CategoryTheory.Functor.map_id]
  simp
  rfl

noncomputable def overlapLoopClass : ZerothHomotopy ↥(U ∩ V) → FundamentalGroup X x₀.val :=
  ZerothHomotopy.lift (overlapLoop U V x₀ q) (fun {_ _} p => overlapLoop_eq U V x₀ q p)

@[simp] theorem overlapLoopClass_mk (x : ↥(U ∩ V)) :
    overlapLoopClass U V x₀ q (ZerothHomotopy.mk x) = overlapLoop U V x₀ q x := rfl

noncomputable def thinOverlapRealization : ThinOverlapGroup U V x₀ →* FundamentalGroup X x₀.val :=
  Monoid.Coprod.lift (FundamentalGroup.map (subsetToAmbient U) (coreBase U V x₀))
    (FreeGroup.lift (fun c : OverlapGenerator U V x₀ => overlapLoopClass U V x₀ q c.val))

theorem thinOverlapRealization_mark (c : ZerothHomotopy ↥(U ∩ V)) :
    thinOverlapRealization U V x₀ q (overlapMark U V x₀ c) = overlapLoopClass U V x₀ q c := by
  classical
  by_cases hc : c = ZerothHomotopy.mk x₀
  · subst c
    simp
  · simp [overlapMark, hc, thinOverlapRealization]

noncomputable def ambientCoreConnector (x : U) :
    FundamentalGroupoid.mk (x₀.val : X) ⟶ FundamentalGroupoid.mk (x.val : X) :=
  (FundamentalGroupoid.map (subsetToAmbient U)).map
    (X := FundamentalGroupoid.mk (coreBase U V x₀))
    (Y := FundamentalGroupoid.mk x) (q.path x)

noncomputable def ambientCapConnector (x : V) :
    FundamentalGroupoid.mk (x₀.val : X) ⟶ FundamentalGroupoid.mk (x.val : X) :=
  (FundamentalGroupoid.map (subsetToAmbient V)).map
    (X := FundamentalGroupoid.mk (capBase U V x₀))
    (Y := FundamentalGroupoid.mk x) (capConnector U V x₀ x)

theorem ambientCapConnector_coherent (x y : V)
    (p : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) :
    ambientCapConnector U V x₀ x ≫ (FundamentalGroupoid.map (subsetToAmbient V)).map p =
      ambientCapConnector U V x₀ y := by
  have h := congrArg (fun t => (FundamentalGroupoid.map (subsetToAmbient V)).map t)
    (capConnector_coherent U V x₀ x y p)
  rw [Functor.map_comp] at h
  exact h

noncomputable def gluedConnector (hcover : U ∪ V = univ)
    (x : FundamentalGroupoid X) : FundamentalGroupoid.mk x₀.val ⟶ x := by
  classical
  by_cases hx : x.as ∈ U
  · exact ambientCoreConnector U V x₀ q ⟨x.as, hx⟩
  · have hxV : x.as ∈ V := by
      have : x.as ∈ U ∪ V := by rw [hcover]; trivial
      exact this.resolve_left hx
    exact ambientCapConnector U V x₀ ⟨x.as, hxV⟩

@[simp] theorem gluedConnector_left (hcover : U ∪ V = univ) (x : U) :
    gluedConnector U V x₀ q hcover (FundamentalGroupoid.mk x.val) =
      ambientCoreConnector U V x₀ q x := by
  classical
  simp only [gluedConnector, x.property, ↓reduceDIte]

@[simp] theorem gluedConnector_base (hcover : U ∪ V = univ) :
    gluedConnector U V x₀ q hcover (FundamentalGroupoid.mk x₀.val) = 𝟙 _ := by
  change gluedConnector U V x₀ q hcover
    (FundamentalGroupoid.mk ((coreBase U V x₀).val)) = _
  rw [gluedConnector_left]
  unfold ambientCoreConnector
  rw [q.at_base, CategoryTheory.Functor.map_id]
  rfl

theorem thinOverlapRealization_weight (hcover : U ∪ V = univ) (x : V) :
    thinOverlapRealization U V x₀ q (capWeight U V x₀ x) =
      gluedConnector U V x₀ q hcover (FundamentalGroupoid.mk x.val) ≫
        Groupoid.inv (ambientCapConnector U V x₀ x) := by
  classical
  by_cases hx : x.val ∈ U
  · simp only [capWeight, hx, ↓reduceDIte, thinOverlapRealization_mark,
      overlapLoopClass_mk, gluedConnector]
    rfl
  · simp [capWeight, gluedConnector, hx]

theorem thinOverlapReconstruction_left (hcover : U ∪ V = univ) :
    FundamentalGroupoid.map (subsetToAmbient U) ⋙
        conjugationFunctor (FundamentalGroupoid.mk x₀.val) (gluedConnector U V x₀ q hcover) =
      (thinOverlapFunctorData U V x₀ q).left ⋙ (thinOverlapRealization U V x₀ q).toFunctor := by
  apply Functor.hext
  · intro x; rfl
  · intro x y p
    apply heq_of_eq
    change gluedConnector U V x₀ q hcover (FundamentalGroupoid.mk x.as.val) ≫
        (FundamentalGroupoid.map (subsetToAmbient U)).map p ≫
          Groupoid.inv (gluedConnector U V x₀ q hcover (FundamentalGroupoid.mk y.as.val)) =
      thinOverlapRealization U V x₀ q
        ((Monoid.Coprod.inl : FundamentalGroup U (coreBase U V x₀) →* ThinOverlapGroup U V x₀)
          ((q.path x.as ≫ p ≫ Groupoid.inv (q.path y.as)) : FundamentalGroup U (coreBase U V x₀)))
    rw [gluedConnector_left, gluedConnector_left]
    simp only [thinOverlapRealization, Monoid.Coprod.lift_apply_inl]
    change _ = (FundamentalGroupoid.map (subsetToAmbient U)).map
      (q.path x.as ≫ p ≫ Groupoid.inv (q.path y.as))
    simp only [Functor.map_comp]
    simp only [ambientCoreConnector, Groupoid.inv_eq_inv, Functor.map_inv]

theorem thinOverlapReconstruction_right (hcover : U ∪ V = univ) :
    FundamentalGroupoid.map (subsetToAmbient V) ⋙
        conjugationFunctor (FundamentalGroupoid.mk x₀.val) (gluedConnector U V x₀ q hcover) =
      (thinOverlapFunctorData U V x₀ q).right ⋙ (thinOverlapRealization U V x₀ q).toFunctor := by
  apply Functor.hext
  · intro x; rfl
  · intro x y p
    apply heq_of_eq
    change gluedConnector U V x₀ q hcover (FundamentalGroupoid.mk x.as.val) ≫
        (FundamentalGroupoid.map (subsetToAmbient V)).map p ≫
          Groupoid.inv (gluedConnector U V x₀ q hcover (FundamentalGroupoid.mk y.as.val)) =
      thinOverlapRealization U V x₀ q ((capWeight U V x₀ y.as)⁻¹ * capWeight U V x₀ x.as)
    rw [map_mul, map_inv, thinOverlapRealization_weight, thinOverlapRealization_weight]
    change gluedConnector U V x₀ q hcover (FundamentalGroupoid.mk x.as.val) ≫
        (FundamentalGroupoid.map (subsetToAmbient V)).map p ≫
          Groupoid.inv (gluedConnector U V x₀ q hcover (FundamentalGroupoid.mk y.as.val)) =
      (gluedConnector U V x₀ q hcover (FundamentalGroupoid.mk x.as.val) ≫
          Groupoid.inv (ambientCapConnector U V x₀ x.as)) ≫
        Groupoid.inv (gluedConnector U V x₀ q hcover (FundamentalGroupoid.mk y.as.val) ≫
          Groupoid.inv (ambientCapConnector U V x₀ y.as))
    rw [← ambientCapConnector_coherent U V x₀ x.as y.as p]
    simp [Category.assoc]

theorem thinOverlapReconstruction (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) :
    (thinOverlapFunctorData U V x₀ q).extension hU hV hcover ⋙
        (thinOverlapRealization U V x₀ q).toFunctor =
      conjugationFunctor (FundamentalGroupoid.mk x₀.val) (gluedConnector U V x₀ q hcover) := by
  let F := thinOverlapFunctorData U V x₀ q
  let H : LocalFunctorData U V (SingleObj (FundamentalGroup X x₀.val)) :=
    { left := F.left ⋙ (thinOverlapRealization U V x₀ q).toFunctor
      right := F.right ⋙ (thinOverlapRealization U V x₀ q).toFunctor
      compatibility := by rw [← Functor.assoc, ← Functor.assoc, F.compatibility] }
  have h₁ := H.extension_unique hU hV hcover
    (F.extension hU hV hcover ⋙ (thinOverlapRealization U V x₀ q).toFunctor)
    (by dsimp only [H]; rw [← Functor.assoc, F.extension_comp_left])
    (by dsimp only [H]; rw [← Functor.assoc, F.extension_comp_right])
  have h₂ := H.extension_unique hU hV hcover
    (conjugationFunctor (FundamentalGroupoid.mk x₀.val) (gluedConnector U V x₀ q hcover))
    (thinOverlapReconstruction_left U V x₀ q hcover)
    (thinOverlapReconstruction_right U V x₀ q hcover)
  exact h₁.trans h₂.symm

noncomputable def thinOverlapWordMap (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) : FundamentalGroup X x₀.val →* ThinOverlapGroup U V x₀ :=
  ((thinOverlapFunctorData U V x₀ q).extension hU hV hcover).mapEnd
    (FundamentalGroupoid.mk x₀.val)

theorem thinOverlapRealization_wordMap (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) (p : FundamentalGroup X x₀.val) :
    thinOverlapRealization U V x₀ q (thinOverlapWordMap U V x₀ q hU hV hcover p) = p := by
  have h : thinOverlapRealization U V x₀ q (thinOverlapWordMap U V x₀ q hU hV hcover p) =
      gluedConnector U V x₀ q hcover (FundamentalGroupoid.mk x₀.val) ≫ p ≫
        Groupoid.inv (gluedConnector U V x₀ q hcover (FundamentalGroupoid.mk x₀.val)) :=
    eq_of_heq (Functor.hcongr_hom (thinOverlapReconstruction U V x₀ q hU hV hcover) p)
  simpa using h

omit [SimplyConnectedSpace V] in
theorem thinOverlapExtension_core (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) (x y : U)
    (p : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) :
    ((thinOverlapFunctorData U V x₀ q).extension hU hV hcover).map
        ((FundamentalGroupoid.map (subsetToAmbient U)).map p) =
      (Monoid.Coprod.inl : FundamentalGroup U (coreBase U V x₀) →* ThinOverlapGroup U V x₀)
        ((q.path x ≫ p ≫ Groupoid.inv (q.path y)) : FundamentalGroup U (coreBase U V x₀)) :=
  eq_of_heq (Functor.hcongr_hom
    ((thinOverlapFunctorData U V x₀ q).extension_comp_left hU hV hcover) p)

omit [SimplyConnectedSpace V] in
theorem thinOverlapExtension_cap (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) (x y : V)
    (p : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) :
    ((thinOverlapFunctorData U V x₀ q).extension hU hV hcover).map
        ((FundamentalGroupoid.map (subsetToAmbient V)).map p) =
      (capWeight U V x₀ y)⁻¹ * capWeight U V x₀ x :=
  eq_of_heq (Functor.hcongr_hom
    ((thinOverlapFunctorData U V x₀ q).extension_comp_right hU hV hcover) p)

omit [SimplyConnectedSpace V] in

theorem thinOverlapWordMap_core (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) (p : FundamentalGroup U (coreBase U V x₀)) :
    thinOverlapWordMap U V x₀ q hU hV hcover
      (FundamentalGroup.map (subsetToAmbient U) (coreBase U V x₀) p) =
      Monoid.Coprod.inl p := by
  have h := thinOverlapExtension_core U V x₀ q hU hV hcover
    (coreBase U V x₀) (coreBase U V x₀) p
  change thinOverlapWordMap U V x₀ q hU hV hcover
    (FundamentalGroup.map (subsetToAmbient U) (coreBase U V x₀) p) = _ at h
  simpa [q.at_base] using h

theorem thinOverlapWordMap_overlapLoop (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) (x : ↥(U ∩ V)) :
    thinOverlapWordMap U V x₀ q hU hV hcover (overlapLoop U V x₀ q x) =
      overlapMark U V x₀ (ZerothHomotopy.mk x) := by
  let L : FundamentalGroupoid X ⥤ SingleObj (ThinOverlapGroup U V x₀) :=
    (thinOverlapFunctorData U V x₀ q).extension hU hV hcover
  have ha : (L.map (ambientCoreConnector U V x₀ q (interToLeft U V x)) : ThinOverlapGroup U V x₀) = (1 : ThinOverlapGroup U V x₀) := by
    have h := thinOverlapExtension_core U V x₀ q hU hV hcover
      (coreBase U V x₀) (interToLeft U V x) (q.path (interToLeft U V x))
    rw [q.at_base, Category.id_comp, Groupoid.comp_inv] at h
    change L.map (ambientCoreConnector U V x₀ q (interToLeft U V x)) =
      (Monoid.Coprod.inl : FundamentalGroup U (coreBase U V x₀) →* ThinOverlapGroup U V x₀) 1 at h
    simpa only [map_one] using h
  have hb : (L.map (ambientCapConnector U V x₀ (interToRight U V x)) : ThinOverlapGroup U V x₀) =
      (overlapMark U V x₀ (ZerothHomotopy.mk x))⁻¹ := by
    have h := thinOverlapExtension_cap U V x₀ q hU hV hcover
      (capBase U V x₀) (interToRight U V x) (capConnector U V x₀ (interToRight U V x))
    change (L.map (ambientCapConnector U V x₀ (interToRight U V x)) : ThinOverlapGroup U V x₀) = _ at h
    simpa only [capWeight_base, capWeight_overlap, mul_one] using h
  change L.map (ambientCoreConnector U V x₀ q (interToLeft U V x) ≫
    Groupoid.inv (ambientCapConnector U V x₀ (interToRight U V x))) = _
  rw [Functor.map_comp]
  simp only [Groupoid.inv_eq_inv, Functor.map_inv, SingleObj.comp_as_mul, SingleObj.inv_as_inv]
  rw [ha, hb]
  change (overlapMark U V x₀ (ZerothHomotopy.mk x))⁻¹⁻¹ * 1 = _
  exact (mul_one _).trans (inv_inv _)

theorem thinOverlapWordMap_overlapLoopClass (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) (c : ZerothHomotopy ↥(U ∩ V)) :
    thinOverlapWordMap U V x₀ q hU hV hcover (overlapLoopClass U V x₀ q c) =
      overlapMark U V x₀ c := by
  obtain ⟨x, rfl⟩ := ZerothHomotopy.mk_surjective c
  exact thinOverlapWordMap_overlapLoop U V x₀ q hU hV hcover x

theorem thinOverlapWordMap_realization (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) (a : ThinOverlapGroup U V x₀) :
    thinOverlapWordMap U V x₀ q hU hV hcover (thinOverlapRealization U V x₀ q a) = a := by
  classical
  let f := thinOverlapWordMap U V x₀ q hU hV hcover
  let h := thinOverlapRealization U V x₀ q
  have he : f.comp h = MonoidHom.id _ := by
    apply Monoid.Coprod.hom_ext
    · ext p
      exact thinOverlapWordMap_core U V x₀ q hU hV hcover p
    · apply FreeGroup.lift.symm.injective
      funext c
      change f (h (Monoid.Coprod.inr (FreeGroup.of c))) = Monoid.Coprod.inr (FreeGroup.of c)
      simp only [h, thinOverlapRealization, Monoid.Coprod.lift_apply_inr, FreeGroup.lift_apply_of]
      rw [thinOverlapWordMap_overlapLoopClass]
      simp [overlapMark, c.property]
  exact DFunLike.congr_fun he a

noncomputable def thinOverlapMulEquiv (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) : FundamentalGroup X x₀.val ≃* ThinOverlapGroup U V x₀ where
  toFun := thinOverlapWordMap U V x₀ q hU hV hcover
  invFun := thinOverlapRealization U V x₀ q
  left_inv := thinOverlapRealization_wordMap U V x₀ q hU hV hcover
  right_inv := thinOverlapWordMap_realization U V x₀ q hU hV hcover
  map_mul' := (thinOverlapWordMap U V x₀ q hU hV hcover).map_mul

theorem thinOverlapMulEquiv_core (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) (p : FundamentalGroup U (coreBase U V x₀)) :
    thinOverlapMulEquiv U V x₀ q hU hV hcover
      (FundamentalGroup.map (subsetToAmbient U) (coreBase U V x₀) p) =
      Monoid.Coprod.inl p :=
  thinOverlapWordMap_core U V x₀ q hU hV hcover p

theorem isFreeFactor_fundamentalGroup_thinOverlap [PathConnectedSpace U]
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (hthin : ∀ x y : ↥(U ∩ V), Subsingleton (Path.Homotopic.Quotient x y)) :
    GC.Group.IsFreeFactor (FundamentalGroup U (coreBase U V x₀))
      (FundamentalGroup X x₀.val) := by
  obtain ⟨q⟩ := nonempty_coherentCoreConnectors U V x₀ hthin
  exact ⟨FreeGroup (OverlapGenerator U V x₀), inferInstance,
    ⟨thinOverlapMulEquiv U V x₀ q hU hV hcover⟩⟩

end SimplyConnectedCap

end GC.Topology
