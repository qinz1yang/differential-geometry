import DifferentialGeometry.Topology.VanKampen.FullGroupoid
import Mathlib.AlgebraicTopology.FundamentalGroupoid.FundamentalGroup
import Mathlib.CategoryTheory.SingleObj
import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Set

namespace Poincare.Topology.VanKampen

private theorem exists_coherent_connectors
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PathConnectedSpace X] (f : C(Y, X)) (x₀ : X)
    (hY : ∀ y z : Y, Subsingleton (Path.Homotopic.Quotient y z)) :
    ∃ q : ∀ y : Y, FundamentalGroupoid.mk x₀ ⟶
        (FundamentalGroupoid.map f).obj (FundamentalGroupoid.mk y),
      ∀ (y z : Y) (p : Path.Homotopic.Quotient y z),
        q y ≫ (FundamentalGroupoid.map f).map
          (X := FundamentalGroupoid.mk y) (Y := FundamentalGroupoid.mk z) p = q z := by
  classical
  let r : ZerothHomotopy Y → Y := Quotient.out
  have hr (y : Y) : Joined (r (ZerothHomotopy.mk y)) y :=
    Quotient.exact (Quotient.out_eq (ZerothHomotopy.mk y))
  let a (y : Y) : FundamentalGroupoid.mk (r (ZerothHomotopy.mk y)) ⟶
      FundamentalGroupoid.mk y :=
    ⟦(hr y).somePath⟧
  let b (c : ZerothHomotopy Y) :
      FundamentalGroupoid.mk x₀ ⟶
        (FundamentalGroupoid.map f).obj (FundamentalGroupoid.mk (r c)) :=
    ⟦PathConnectedSpace.somePath x₀ (f (r c))⟧
  refine ⟨fun y ↦ b (ZerothHomotopy.mk y) ≫ (FundamentalGroupoid.map f).map (a y), ?_⟩
  intro y z p
  have hc : ZerothHomotopy.mk y = ZerothHomotopy.mk z :=
    ZerothHomotopy.sound p.out
  let e := congrArg (fun c ↦ FundamentalGroupoid.mk (r c)) hc
  have ha : a y ≫ (show FundamentalGroupoid.mk y ⟶ FundamentalGroupoid.mk z from p) =
      eqToHom e ≫ a z := (hY _ _).elim _ _
  have hb : b (ZerothHomotopy.mk y) ≫ (FundamentalGroupoid.map f).map (eqToHom e) =
      b (ZerothHomotopy.mk z) := by
    have transport {c d : ZerothHomotopy Y} (h : c = d) :
        b c ≫ (FundamentalGroupoid.map f).map
          (eqToHom (congrArg (fun t ↦ FundamentalGroupoid.mk (r t)) h)) = b d := by
      cases h
      change b c ≫ (FundamentalGroupoid.map f).map
        (𝟙 (FundamentalGroupoid.mk (r c))) = b c
      rw [(FundamentalGroupoid.map f).map_id, Category.comp_id]
    exact transport hc
  dsimp only
  rw [Category.assoc, ← Functor.map_comp, ha, Functor.map_comp, ← Category.assoc, hb]

private def conjugationFunctor
    {C : Type*} [Groupoid C] (b : C) (q : ∀ x : C, b ⟶ x) :
    C ⥤ SingleObj (End b) where
  obj _ := SingleObj.star _
  map {x y} f := (q x ≫ f ≫ Groupoid.inv (q y) : b ⟶ b)
  map_id x := by
    change q x ≫ 𝟙 x ≫ Groupoid.inv (q x) = 𝟙 b
    simp
  map_comp {x y z} f g := by
    change q x ≫ (f ≫ g) ≫ Groupoid.inv (q z) =
      (q x ≫ f ≫ Groupoid.inv (q y)) ≫ (q y ≫ g ≫ Groupoid.inv (q z))
    simp [Category.assoc]

private def coboundaryFunctor
    {C G : Type*} [Category C] [Group G] (d : C → G) : C ⥤ SingleObj G where
  obj _ := SingleObj.star _
  map {x y} _ := (d y)⁻¹ * d x
  map_id x := by simp; rfl
  map_comp {x y z} f g := by
    change (d z)⁻¹ * d x = ((d z)⁻¹ * d y) * ((d y)⁻¹ * d x)
    simp [mul_assoc]

private def coverComponentWeight
    {X : Type*} [TopologicalSpace X] (U V : Set X) (x : FundamentalGroupoid V) :
    FreeGroup (ZerothHomotopy (↑(U ∩ V))) := by
  classical
  exact if hx : x.as.val ∈ U then
    FreeGroup.of (ZerothHomotopy.mk ⟨x.as.val, hx, x.as.property⟩) else 1

private def coverComponentFunctorData
    {X : Type*} [TopologicalSpace X] (U V : Set X) :
    LocalFunctorData U V (SingleObj (FreeGroup (ZerothHomotopy (↑(U ∩ V))))) where
  left := (Functor.const _).obj (SingleObj.star _)
  right := coboundaryFunctor (coverComponentWeight U V)
  compatibility := by
    classical
    apply Functor.hext
    · intro z
      rfl
    · intro x y p
      apply heq_of_eq
      change (1 : FreeGroup (ZerothHomotopy (↑(U ∩ V)))) =
        (coverComponentWeight U V ((FundamentalGroupoid.map (interToRight U V)).obj y))⁻¹ *
          coverComponentWeight U V ((FundamentalGroupoid.map (interToRight U V)).obj x)
      have hx : x.as.val ∈ U := x.as.property.1
      have hy : y.as.val ∈ U := y.as.property.1
      have he : ZerothHomotopy.mk x.as = ZerothHomotopy.mk y.as :=
        ZerothHomotopy.sound p.out
      change 1 =
        (if h : y.as.val ∈ U then
          FreeGroup.of (ZerothHomotopy.mk
            (⟨y.as.val, h, y.as.property.2⟩ : ↑(U ∩ V))) else 1)⁻¹ *
        (if h : x.as.val ∈ U then
          FreeGroup.of (ZerothHomotopy.mk
            (⟨x.as.val, h, x.as.property.2⟩ : ↑(U ∩ V))) else 1)
      rw [dif_pos hy, dif_pos hx]
      change 1 = (FreeGroup.of (ZerothHomotopy.mk y.as))⁻¹ *
        FreeGroup.of (ZerothHomotopy.mk x.as)
      rw [he, inv_mul_cancel]

private structure CoverConnectors
    {X : Type*} [TopologicalSpace X] (U V : Set X) (x₀ : X) where
  left : ∀ x : U, FundamentalGroupoid.mk x₀ ⟶ FundamentalGroupoid.mk x.val
  right : ∀ x : V, FundamentalGroupoid.mk x₀ ⟶ FundamentalGroupoid.mk x.val
  left_comp : ∀ (x y : U) (p : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y),
    left x ≫ (FundamentalGroupoid.map (subsetToAmbient U)).map p = left y
  right_comp : ∀ (x y : V) (p : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y),
    right x ≫ (FundamentalGroupoid.map (subsetToAmbient V)).map p = right y

private def CoverConnectors.overlapLoop
    {X : Type*} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    (q : CoverConnectors U V x₀) (x : ↑(U ∩ V)) : FundamentalGroup X x₀ :=
  q.left ⟨x.val, x.property.1⟩ ≫ Groupoid.inv (q.right ⟨x.val, x.property.2⟩)

private theorem CoverConnectors.overlapLoop_eq
    {X : Type*} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    (q : CoverConnectors U V x₀) {x y : ↑(U ∩ V)} (p : Path x y) :
    q.overlapLoop x = q.overlapLoop y := by
  let a : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y := ⟦p⟧
  have hU := q.left_comp _ _ ((FundamentalGroupoid.map (interToLeft U V)).map a)
  have hV := q.right_comp _ _ ((FundamentalGroupoid.map (interToRight U V)).map a)
  let r : FundamentalGroupoid.mk x.val ⟶ FundamentalGroupoid.mk y.val :=
    (FundamentalGroupoid.map (subsetToAmbient (U ∩ V))).map a
  change q.left ⟨x.val, x.property.1⟩ ≫ r = q.left ⟨y.val, y.property.1⟩ at hU
  change q.right ⟨x.val, x.property.2⟩ ≫ r = q.right ⟨y.val, y.property.2⟩ at hV
  dsimp only [overlapLoop]
  rw [← hU, ← hV]
  simp [Category.assoc]

private def CoverConnectors.realization
    {X : Type*} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    (q : CoverConnectors U V x₀) :
    FreeGroup (ZerothHomotopy (↑(U ∩ V))) →* FundamentalGroup X x₀ :=
  FreeGroup.lift (ZerothHomotopy.lift q.overlapLoop (fun {_ _} p ↦ q.overlapLoop_eq p))

private def CoverConnectors.glued
    {X : Type*} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    (q : CoverConnectors U V x₀) (hcover : U ∪ V = univ)
    (x : FundamentalGroupoid X) : FundamentalGroupoid.mk x₀ ⟶ x := by
  classical
  by_cases hx : x.as ∈ U
  · exact q.left ⟨x.as, hx⟩
  · have hxV : x.as ∈ V := by
      have : x.as ∈ U ∪ V := by rw [hcover]; trivial
      exact this.resolve_left hx
    exact q.right ⟨x.as, hxV⟩

private theorem CoverConnectors.glued_left
    {X : Type*} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    (q : CoverConnectors U V x₀) (hcover : U ∪ V = univ) (x : U) :
    q.glued hcover (FundamentalGroupoid.mk x.val) = q.left x := by
  classical
  simp only [glued, x.property, ↓reduceDIte]

private theorem CoverConnectors.realization_weight
    {X : Type*} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    (q : CoverConnectors U V x₀) (hcover : U ∪ V = univ) (x : V) :
    q.realization (coverComponentWeight U V (FundamentalGroupoid.mk x)) =
      q.glued hcover (FundamentalGroupoid.mk x.val) ≫ Groupoid.inv (q.right x) := by
  classical
  by_cases hx : x.val ∈ U
  · simp [coverComponentWeight, realization, overlapLoop, glued, hx]
  · simp [coverComponentWeight, glued, hx]

private theorem CoverConnectors.reconstruction_left
    {X : Type*} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    (q : CoverConnectors U V x₀) (hcover : U ∪ V = univ) :
    FundamentalGroupoid.map (subsetToAmbient U) ⋙
        conjugationFunctor (FundamentalGroupoid.mk x₀) (q.glued hcover) =
      (coverComponentFunctorData U V).left ⋙ q.realization.toFunctor := by
  apply Functor.hext
  · intro x; rfl
  · intro x y p
    apply heq_of_eq
    change q.glued hcover (FundamentalGroupoid.mk x.as.val) ≫
        (FundamentalGroupoid.map (subsetToAmbient U)).map p ≫
          Groupoid.inv (q.glued hcover (FundamentalGroupoid.mk y.as.val)) =
      q.realization 1
    rw [map_one, q.glued_left, q.glued_left, ← Category.assoc, q.left_comp]
    exact Groupoid.comp_inv _

private theorem CoverConnectors.reconstruction_right
    {X : Type*} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    (q : CoverConnectors U V x₀) (hcover : U ∪ V = univ) :
    FundamentalGroupoid.map (subsetToAmbient V) ⋙
        conjugationFunctor (FundamentalGroupoid.mk x₀) (q.glued hcover) =
      (coverComponentFunctorData U V).right ⋙ q.realization.toFunctor := by
  apply Functor.hext
  · intro x; rfl
  · intro x y p
    apply heq_of_eq
    change q.glued hcover (FundamentalGroupoid.mk x.as.val) ≫
        (FundamentalGroupoid.map (subsetToAmbient V)).map p ≫
          Groupoid.inv (q.glued hcover (FundamentalGroupoid.mk y.as.val)) =
      q.realization ((coverComponentWeight U V y)⁻¹ * coverComponentWeight U V x)
    rw [map_mul, map_inv, q.realization_weight hcover y.as,
      q.realization_weight hcover x.as]
    change q.glued hcover (FundamentalGroupoid.mk x.as.val) ≫
        (FundamentalGroupoid.map (subsetToAmbient V)).map p ≫
          Groupoid.inv (q.glued hcover (FundamentalGroupoid.mk y.as.val)) =
      (q.glued hcover (FundamentalGroupoid.mk x.as.val) ≫ Groupoid.inv (q.right x.as)) ≫
        Groupoid.inv
          (q.glued hcover (FundamentalGroupoid.mk y.as.val) ≫ Groupoid.inv (q.right y.as))
    rw [← q.right_comp x.as y.as p]
    simp [Category.assoc]

private theorem CoverConnectors.reconstruction
    {X : Type*} [TopologicalSpace X] {U V : Set X} {x₀ : X}
    (q : CoverConnectors U V x₀) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = univ) :
    (coverComponentFunctorData U V).extension hU hV hcover ⋙ q.realization.toFunctor =
      conjugationFunctor (FundamentalGroupoid.mk x₀) (q.glued hcover) := by
  let F := coverComponentFunctorData U V
  let H : LocalFunctorData U V (SingleObj (FundamentalGroup X x₀)) :=
    { left := F.left ⋙ q.realization.toFunctor
      right := F.right ⋙ q.realization.toFunctor
      compatibility := by rw [← Functor.assoc, ← Functor.assoc, F.compatibility] }
  have h₁ := H.extension_unique hU hV hcover
    (F.extension hU hV hcover ⋙ q.realization.toFunctor)
    (by dsimp only [H]; rw [← Functor.assoc, F.extension_comp_left])
    (by dsimp only [H]; rw [← Functor.assoc, F.extension_comp_right])
  have h₂ := H.extension_unique hU hV hcover
    (conjugationFunctor (FundamentalGroupoid.mk x₀) (q.glued hcover))
    (q.reconstruction_left hcover) (q.reconstruction_right hcover)
  exact h₁.trans h₂.symm

theorem exists_injective_fundamentalGroup_hom_freeGroup_of_open_cover
    {X : Type*} [TopologicalSpace X] [PathConnectedSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (hUsc : ∀ x y : U, Subsingleton (Path.Homotopic.Quotient x y))
    (hVsc : ∀ x y : V, Subsingleton (Path.Homotopic.Quotient x y)) (x₀ : X) :
    ∃ f : FundamentalGroup X x₀ →* FreeGroup (ZerothHomotopy (↑(U ∩ V))),
      Function.Injective f := by
  obtain ⟨qU, hqU⟩ := exists_coherent_connectors (subsetToAmbient U) x₀ hUsc
  obtain ⟨qV, hqV⟩ := exists_coherent_connectors (subsetToAmbient V) x₀ hVsc
  let q : CoverConnectors U V x₀ := ⟨qU, qV, hqU, hqV⟩
  let F := (coverComponentFunctorData U V).extension hU hV hcover
  let f : FundamentalGroup X x₀ →* FreeGroup (ZerothHomotopy (↑(U ∩ V))) :=
    F.mapEnd (FundamentalGroupoid.mk x₀)
  have hf (p : FundamentalGroup X x₀) :
      q.realization (f p) = q.glued hcover (FundamentalGroupoid.mk x₀) ≫ p ≫
        Groupoid.inv (q.glued hcover (FundamentalGroupoid.mk x₀)) :=
    eq_of_heq (Functor.hcongr_hom (q.reconstruction hU hV hcover) p)
  refine ⟨f, fun p r h ↦ ?_⟩
  have he := congrArg q.realization h
  rw [hf, hf] at he
  have he' := congrArg
    (fun s : FundamentalGroup X x₀ ↦
      Groupoid.inv (q.glued hcover (FundamentalGroupoid.mk x₀)) ≫ s ≫
        q.glued hcover (FundamentalGroupoid.mk x₀)) he
  simpa [Category.assoc] using he'

theorem isMulTorsionFree_fundamentalGroup_of_open_cover
    {X : Type*} [TopologicalSpace X] [PathConnectedSpace X]
    (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (hUsc : ∀ x y : U, Subsingleton (Path.Homotopic.Quotient x y))
    (hVsc : ∀ x y : V, Subsingleton (Path.Homotopic.Quotient x y)) (x₀ : X) :
    IsMulTorsionFree (FundamentalGroup X x₀) := by
  obtain ⟨f, hf⟩ := exists_injective_fundamentalGroup_hom_freeGroup_of_open_cover
    U V hU hV hcover hUsc hVsc x₀
  exact hf.isMulTorsionFree f

private def overlapRetractionWeight
    {X : Type*} [TopologicalSpace X] {U V : Set X} (x₀ : U)
    (q : ∀ x : FundamentalGroupoid U, FundamentalGroupoid.mk x₀ ⟶ x)
    (k : ∀ x : ↑(U ∩ V), FundamentalGroupoid.mk x₀ ⟶
      FundamentalGroupoid.mk (⟨x.val, x.property.1⟩ : U))
    (y : FundamentalGroupoid V) : FundamentalGroup U x₀ := by
  classical
  exact if hy : y.as.val ∈ U then
    q (FundamentalGroupoid.mk ⟨y.as.val, hy⟩) ≫
      Groupoid.inv (k ⟨y.as.val, hy, y.as.property⟩)
  else 1

private def overlapRetractionData
    {X : Type*} [TopologicalSpace X] {U V : Set X} (x₀ : U)
    (q : ∀ x : FundamentalGroupoid U, FundamentalGroupoid.mk x₀ ⟶ x)
    (k : ∀ x : ↑(U ∩ V), FundamentalGroupoid.mk x₀ ⟶
      FundamentalGroupoid.mk (⟨x.val, x.property.1⟩ : U))
    (hk : ∀ (x y : ↑(U ∩ V)) (p : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y),
      k x ≫ (FundamentalGroupoid.map (interToLeft U V)).map p = k y) :
    LocalFunctorData U V (SingleObj (FundamentalGroup U x₀)) where
  left := conjugationFunctor (FundamentalGroupoid.mk x₀) q
  right := coboundaryFunctor (overlapRetractionWeight x₀ q k)
  compatibility := by
    classical
    apply Functor.hext
    · intro x; rfl
    · intro x y p
      apply heq_of_eq
      change q ((FundamentalGroupoid.map (interToLeft U V)).obj x) ≫
          (FundamentalGroupoid.map (interToLeft U V)).map p ≫
            Groupoid.inv (q ((FundamentalGroupoid.map (interToLeft U V)).obj y)) =
        (overlapRetractionWeight x₀ q k
          ((FundamentalGroupoid.map (interToRight U V)).obj y))⁻¹ *
        overlapRetractionWeight x₀ q k
          ((FundamentalGroupoid.map (interToRight U V)).obj x)
      have hx : x.as.val ∈ U := x.as.property.1
      have hy : y.as.val ∈ U := y.as.property.1
      simp only [overlapRetractionWeight, FundamentalGroupoid.map, interToRight,
        ContinuousMap.coe_mk, hy, hx, ↓reduceDIte]
      change q (FundamentalGroupoid.mk (⟨x.as.val, hx⟩ : U)) ≫
          (FundamentalGroupoid.map (interToLeft U V)).map p ≫
            Groupoid.inv (q (FundamentalGroupoid.mk (⟨y.as.val, hy⟩ : U))) =
        (q (FundamentalGroupoid.mk (⟨x.as.val, hx⟩ : U)) ≫ Groupoid.inv (k x.as)) ≫
          Groupoid.inv
            (q (FundamentalGroupoid.mk (⟨y.as.val, hy⟩ : U)) ≫ Groupoid.inv (k y.as))
      rw [← hk x.as y.as p]
      simp [Category.assoc]

theorem injective_fundamentalGroup_map_of_open_cover_of_overlap_components
    {X : Type*} [TopologicalSpace X] (U V : Set X) [PathConnectedSpace U]
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = univ)
    (hsc : ∀ x y : ↑(U ∩ V), Subsingleton (Path.Homotopic.Quotient x y)) (x₀ : U) :
    Function.Injective (FundamentalGroup.map (subsetToAmbient U) x₀) := by
  obtain ⟨k, hk⟩ := exists_coherent_connectors (interToLeft U V) x₀ hsc
  let q (x : FundamentalGroupoid U) : FundamentalGroupoid.mk x₀ ⟶ x :=
    ⟦PathConnectedSpace.somePath x₀ x.as⟧
  let F := overlapRetractionData x₀ q k hk
  let L := F.extension hU hV hcover
  have hL (p : FundamentalGroup U x₀) :
      L.map ((FundamentalGroupoid.map (subsetToAmbient U)).map p) =
        q (FundamentalGroupoid.mk x₀) ≫ p ≫
          Groupoid.inv (q (FundamentalGroupoid.mk x₀)) :=
    eq_of_heq (Functor.hcongr_hom (F.extension_comp_left hU hV hcover) p)
  intro p r h
  have he := congrArg
    (fun a : FundamentalGroup X x₀.val ↦ L.map a) h
  change L.map ((FundamentalGroupoid.map (subsetToAmbient U)).map p) =
    L.map ((FundamentalGroupoid.map (subsetToAmbient U)).map r) at he
  rw [hL, hL] at he
  have he' := congrArg (fun s : FundamentalGroup U x₀ ↦
    Groupoid.inv (q (FundamentalGroupoid.mk x₀)) ≫ s ≫ q (FundamentalGroupoid.mk x₀)) he
  simpa [Category.assoc] using he'

end Poincare.Topology.VanKampen
