import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Gluing
import Mathlib.GroupTheory.HNNExtension

/-!
# Gluing along a non-separating seam

Chapter 6, K09, second tier. `TwoComponentCover U V` records an open cover of a space by
path-connected `U` and `V` whose intersection has exactly two path components, through `base` and
`far`, such that π₁ of the `base` component maps bijectively to π₁(V), both components are
π₁-injective into `U`, and the `far` component is π₁-injective into `V`. From the groupoid van
Kampen theorem (`seifertVanKampen`) and anchor paths chosen in each piece, `equivExtension`
identifies π₁ of the space at `base` with the HNN extension of π₁(U) whose stable letter conjugates
the image of the `far` component through `V` (`rightEdge`) to its image through `U` (`leftEdge`):
the anchored functors on the fundamental groupoids of `U` and `V` descend through the pushout, and
the inverse is `HNNExtension.lift` with the loop `connectorLoop`. The base group embeds
(`injective_fundamentalGroup_map_left`, from `HNNExtension.of_injective`).

For a torus presentation and a seam `j` that does not separate (`¬ IsSeparating`), the complement of
the seam torus and the open collar form such a cover (`nonSeparatingCover`): the complement is the
common side, and the two halves of the collar off the torus are the components, told apart by the
collar coordinate `gapTime`. The torus pushed to level `∓1/2` is a π₁-isomorphism onto each half
(`bijective_gapLevel_neg`, `bijective_gapLevel_pos`, by a clopen retraction onto a slab and
`slabHomotopyEquiv`). `nonSeparatingVanKampen` is the resulting HNN description of π₁(W) when the
two ends `leftEnd`, `rightEnd` (the pushed-off tori in the complement) are π₁-injective at one
basepoint, and then the seam torus is π₁-injective at every basepoint
(`injective_seamTorus_of_not_isSeparating`). `SeamInjective` combines this with the separating case
of `Gluing`, and `incompressible_toTorusDecomposition_of_seamInjective` gives the incompressibility
of the K04 torus decomposition from these per-seam hypotheses.
-/

set_option autoImplicit false

noncomputable section
open CategoryTheory DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold DifferentialGeometry.Topology.VanKampen
open scoped ContDiff Topology ContinuousMap

universe u

namespace GC.Seifert

attribute [local instance] uliftGroupoid

section Anchored
variable {C : Type u} [Groupoid.{u} C] {H : Type u} [Group H]

theorem map_comp_end {c₀ : C} (h : End c₀ →* H) (x y : c₀ ⟶ c₀) : h (x ≫ y) = h y * h x :=
  h.map_mul y x

theorem map_id_end {c₀ : C} (h : End c₀ →* H) : h (𝟙 c₀) = 1 :=
  h.map_one

def anchoredFunctor (c₀ : C) (τ : ∀ c, c₀ ⟶ c) (h : End c₀ →* H) (κ : C → H) :
    C ⥤ ULift.{u} (SingleObj H) where
  obj _ := ⟨SingleObj.star H⟩
  map {a b} p := (κ b * h (τ a ≫ p ≫ Groupoid.inv (τ b)) * (κ a)⁻¹ : H)
  map_id a := by
    have h1 : τ a ≫ 𝟙 a ≫ Groupoid.inv (τ a) = 𝟙 c₀ := by simp
    change κ a * h (τ a ≫ 𝟙 a ≫ Groupoid.inv (τ a)) * (κ a)⁻¹ = (1 : H)
    rw [h1, map_id_end, mul_one, mul_inv_cancel]
  map_comp {a b c} p q := by
    have hm : τ a ≫ (p ≫ q) ≫ Groupoid.inv (τ c) =
        (τ a ≫ p ≫ Groupoid.inv (τ b)) ≫ (τ b ≫ q ≫ Groupoid.inv (τ c)) := by
      simp
    change κ c * h (τ a ≫ (p ≫ q) ≫ Groupoid.inv (τ c)) * (κ a)⁻¹ =
      (κ c * h (τ b ≫ q ≫ Groupoid.inv (τ c)) * (κ b)⁻¹) *
        (κ b * h (τ a ≫ p ≫ Groupoid.inv (τ b)) * (κ a)⁻¹)
    rw [hm, map_comp_end]
    group

end Anchored

section JoinedAnchor
variable {Y : Type u} [TopologicalSpace Y]

open Classical in
def joinedAnchor (a b : Y) (h : Joined a b) :
    FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b :=
  if hab : a = b then eqToHom (congrArg FundamentalGroupoid.mk hab)
  else Path.Homotopic.Quotient.mk h.somePath

theorem joinedAnchor_self (a : Y) (h : Joined a a) :
    joinedAnchor a a h = 𝟙 (FundamentalGroupoid.mk a) := by
  rw [joinedAnchor, dite_eq_left rfl, eqToHom_refl]

theorem joined_of_hom {a b : FundamentalGroupoid Y} (p : a ⟶ b) : Joined a.as b.as :=
  Path.Homotopic.Quotient.ind (motive := fun _ => Joined a.as b.as) (fun q => ⟨q⟩) p

end JoinedAnchor

section GroupoidLemmas
variable {C : Type*} [Groupoid C]

theorem groupoidInv_comp_cancel {a b c : C} (f : a ⟶ b) (g : b ⟶ c) :
    Groupoid.inv f ≫ f ≫ g = g := by
  rw [← Category.assoc, Groupoid.inv_comp, Category.id_comp]

theorem comp_groupoidInv_comp_cancel {a b c d : C} (m : a ⟶ b) (γ : c ⟶ b) (k : b ⟶ d) :
    (m ≫ Groupoid.inv γ) ≫ γ ≫ k = m ≫ k := by
  rw [Category.assoc, groupoidInv_comp_cancel]

theorem id_conj {x : C} (g : x ⟶ x) : 𝟙 x ≫ g ≫ Groupoid.inv (𝟙 x) = g := by
  simp

theorem id_comp_comp_groupoidInv {x y : C} (δ : x ⟶ y) : 𝟙 x ≫ δ ≫ Groupoid.inv δ = 𝟙 x := by
  simp

theorem groupoidInv_id_comp {x y : C} (f : x ⟶ y) : Groupoid.inv (𝟙 x) ≫ f = f := by
  simp

theorem groupoidInv_comp_groupoidInv_cancel {a b c d : C} (γ : a ⟶ b) (δ : c ⟶ b)
    (k : b ⟶ d) : Groupoid.inv (γ ≫ Groupoid.inv δ) ≫ γ ≫ k = δ ≫ k := by
  simp

def endOf {x : C} (f : x ⟶ x) : End x := f

theorem twist_conj {x y z : C} (ka kb : x ⟶ x) (A : x ⟶ y) (P : y ⟶ z) (B : x ⟶ z) :
    endOf kb * endOf (A ≫ P ≫ Groupoid.inv B) * (endOf ka)⁻¹ =
      (Groupoid.inv ka ≫ A) ≫ P ≫ Groupoid.inv (Groupoid.inv kb ≫ B) := by
  change Groupoid.inv ka ≫ (A ≫ P ≫ Groupoid.inv B) ≫ kb = _
  simp

theorem map_groupoidInv {D : Type*} [Groupoid D] (F : C ⥤ D) {a b : C} (f : a ⟶ b) :
    F.map (Groupoid.inv f) = Groupoid.inv (F.map f) := by
  simp

theorem map_conj_three {D : Type*} [Groupoid D] (F : C ⥤ D) {a b c d : C} (f : a ⟶ b)
    (g : b ⟶ c) (h : d ⟶ c) :
    F.map (f ≫ g ≫ Groupoid.inv h) = F.map f ≫ F.map g ≫ Groupoid.inv (F.map h) := by
  simp

def conjHom {a b : C} (γ : a ⟶ b) : End b →* End a where
  toFun x := γ ≫ x ≫ Groupoid.inv γ
  map_one' := by
    simp [End.one_def]
  map_mul' x y := by
    simp [End.mul_def]

theorem conjHom_apply {a b : C} (γ : a ⟶ b) (x : End b) :
    conjHom γ x = γ ≫ x ≫ Groupoid.inv γ :=
  rfl

theorem conjHom_injective {a b : C} (γ : a ⟶ b) : Function.Injective (conjHom γ) := by
  intro x y h
  have h' := congrArg (fun z : End a => Groupoid.inv γ ≫ z ≫ γ) h
  simpa [conjHom_apply] using h'

theorem conjHom_map_conj {D : Type*} [Groupoid D] (F : C ⥤ D) {a b c d : C} (δ : F.obj a ⟶ F.obj b)
    (f : b ⟶ c) (g : c ⟶ d) (h : b ⟶ d) :
    conjHom δ (F.map (f ≫ g ≫ Groupoid.inv h)) =
      (δ ≫ F.map f) ≫ F.map g ≫ Groupoid.inv (δ ≫ F.map h) := by
  simp [conjHom_apply]

end GroupoidLemmas

section HomFunctor
variable {G H : Type u} [Group G] [Group H]

def homFunctor (f : G →* H) : ULift.{u} (SingleObj G) ⥤ ULift.{u} (SingleObj H) where
  obj _ := ⟨SingleObj.star H⟩
  map g := (f g : H)
  map_id _ := f.map_one
  map_comp g h := f.map_mul h g

end HomFunctor

theorem mem_right_of_not_mem_left {X : Type u} {U V : Set X} (hc : U ∪ V = Set.univ) {x : X}
    (h : x ∉ U) : x ∈ V := by
  have hx : x ∈ U ∪ V := by
    rw [hc]
    trivial
  exact hx.resolve_left h

section Ambient
variable {X : Type u} [TopologicalSpace X] {U V : Set X}

theorem ambient_left_map {a b : ↑(U ∩ V)}
    (p : FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b) :
    (FundamentalGroupoid.map (subsetToAmbient U)).map
        ((FundamentalGroupoid.map (interToLeft U V)).map p) =
      (FundamentalGroupoid.map (subsetToAmbient (U ∩ V))).map p :=
  (Path.Homotopic.Quotient.map_comp (p := p)).symm

theorem ambient_right_map {a b : ↑(U ∩ V)}
    (p : FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b) :
    (FundamentalGroupoid.map (subsetToAmbient V)).map
        ((FundamentalGroupoid.map (interToRight U V)).map p) =
      (FundamentalGroupoid.map (subsetToAmbient (U ∩ V))).map p :=
  (Path.Homotopic.Quotient.map_comp (p := p)).symm

end Ambient

structure TwoComponentCover {X : Type u} [TopologicalSpace X] (U V : Set X) where
  left_connected : PathConnectedSpace U
  right_connected : PathConnectedSpace V
  isOpen_left : IsOpen U
  isOpen_right : IsOpen V
  cover : U ∪ V = Set.univ
  base : ↑(U ∩ V)
  far : ↑(U ∩ V)
  not_joined : ¬ Joined base far
  joined : ∀ a : ↑(U ∩ V), Joined base a ∨ Joined far a
  right_bijective : Function.Bijective (FundamentalGroup.map (interToRight U V) base)
  left_injective : Function.Injective (FundamentalGroup.map (interToLeft U V) base)
  left_injective_far : Function.Injective (FundamentalGroup.map (interToLeft U V) far)
  right_injective_far : Function.Injective (FundamentalGroup.map (interToRight U V) far)

namespace TwoComponentCover
variable {X : Type u} [TopologicalSpace X] {U V : Set X} (K : TwoComponentCover U V)

def leftConnector :
    (FundamentalGroupoid.map (interToLeft U V)).obj (FundamentalGroupoid.mk K.base) ⟶
      (FundamentalGroupoid.map (interToLeft U V)).obj (FundamentalGroupoid.mk K.far) :=
  Path.Homotopic.Quotient.mk (@PathConnectedSpace.somePath _ _ K.left_connected _ _)

def rightConnector :
    (FundamentalGroupoid.map (interToRight U V)).obj (FundamentalGroupoid.mk K.base) ⟶
      (FundamentalGroupoid.map (interToRight U V)).obj (FundamentalGroupoid.mk K.far) :=
  Path.Homotopic.Quotient.mk (@PathConnectedSpace.somePath _ _ K.right_connected _ _)

open Classical in
def interLeftAnchor (a : ↑(U ∩ V)) :
    (FundamentalGroupoid.map (interToLeft U V)).obj (FundamentalGroupoid.mk K.base) ⟶
      (FundamentalGroupoid.map (interToLeft U V)).obj (FundamentalGroupoid.mk a) :=
  if hj : Joined K.base a then
    (FundamentalGroupoid.map (interToLeft U V)).map (joinedAnchor K.base a hj)
  else K.leftConnector ≫ (FundamentalGroupoid.map (interToLeft U V)).map
    (joinedAnchor K.far a ((K.joined a).resolve_left hj))

open Classical in
def interRightAnchor (a : ↑(U ∩ V)) :
    (FundamentalGroupoid.map (interToRight U V)).obj (FundamentalGroupoid.mk K.base) ⟶
      (FundamentalGroupoid.map (interToRight U V)).obj (FundamentalGroupoid.mk a) :=
  if hj : Joined K.base a then
    (FundamentalGroupoid.map (interToRight U V)).map (joinedAnchor K.base a hj)
  else K.rightConnector ≫ (FundamentalGroupoid.map (interToRight U V)).map
    (joinedAnchor K.far a ((K.joined a).resolve_left hj))

open Classical in
def leftAnchor (x : U) :
    (FundamentalGroupoid.map (interToLeft U V)).obj (FundamentalGroupoid.mk K.base) ⟶
      FundamentalGroupoid.mk x :=
  if h : (x : X) ∈ V then K.interLeftAnchor ⟨x.1, x.2, h⟩
  else Path.Homotopic.Quotient.mk (@PathConnectedSpace.somePath _ _ K.left_connected _ _)

open Classical in
def rightAnchor (x : V) :
    (FundamentalGroupoid.map (interToRight U V)).obj (FundamentalGroupoid.mk K.base) ⟶
      FundamentalGroupoid.mk x :=
  if h : (x : X) ∈ U then K.interRightAnchor ⟨x.1, h, x.2⟩
  else Path.Homotopic.Quotient.mk (@PathConnectedSpace.somePath _ _ K.right_connected _ _)

open Classical in
def interTwist {H : Type*} [Group H] (s : H) (a : ↑(U ∩ V)) : H :=
  if Joined K.base a then 1 else s

open Classical in
def rightTwist {H : Type*} [Group H] (s : H) (x : V) : H :=
  if h : (x : X) ∈ U then K.interTwist s ⟨x.1, h, x.2⟩ else 1

theorem leftAnchor_interToLeft (a : ↑(U ∩ V)) :
    K.leftAnchor (interToLeft U V a) = K.interLeftAnchor a :=
  dite_eq_left a.2.2

theorem rightAnchor_interToRight (a : ↑(U ∩ V)) :
    K.rightAnchor (interToRight U V a) = K.interRightAnchor a :=
  dite_eq_left a.2.1

theorem rightTwist_interToRight {H : Type*} [Group H] (s : H) (a : ↑(U ∩ V)) :
    K.rightTwist s (interToRight U V a) = K.interTwist s a :=
  dite_eq_left a.2.1

theorem interLeftAnchor_of_joined {a : ↑(U ∩ V)} (hj : Joined K.base a) :
    K.interLeftAnchor a =
      (FundamentalGroupoid.map (interToLeft U V)).map (joinedAnchor K.base a hj) :=
  dite_eq_left hj

theorem interLeftAnchor_of_not_joined {a : ↑(U ∩ V)} (hj : ¬ Joined K.base a) :
    K.interLeftAnchor a = K.leftConnector ≫ (FundamentalGroupoid.map (interToLeft U V)).map
      (joinedAnchor K.far a ((K.joined a).resolve_left hj)) :=
  dite_eq_right hj

theorem interRightAnchor_of_joined {a : ↑(U ∩ V)} (hj : Joined K.base a) :
    K.interRightAnchor a =
      (FundamentalGroupoid.map (interToRight U V)).map (joinedAnchor K.base a hj) :=
  dite_eq_left hj

theorem interRightAnchor_of_not_joined {a : ↑(U ∩ V)} (hj : ¬ Joined K.base a) :
    K.interRightAnchor a = K.rightConnector ≫ (FundamentalGroupoid.map (interToRight U V)).map
      (joinedAnchor K.far a ((K.joined a).resolve_left hj)) :=
  dite_eq_right hj

theorem interTwist_of_joined {H : Type*} [Group H] (s : H) {a : ↑(U ∩ V)}
    (hj : Joined K.base a) : K.interTwist s a = 1 :=
  ite_eq_left hj

theorem interTwist_of_not_joined {H : Type*} [Group H] (s : H) {a : ↑(U ∩ V)}
    (hj : ¬ Joined K.base a) : K.interTwist s a = s :=
  ite_eq_right hj

theorem interLeftAnchor_base : K.interLeftAnchor K.base = 𝟙 _ := by
  rw [interLeftAnchor_of_joined K (Joined.refl _), joinedAnchor_self,
    CategoryTheory.Functor.map_id]

theorem interRightAnchor_base : K.interRightAnchor K.base = 𝟙 _ := by
  rw [interRightAnchor_of_joined K (Joined.refl _), joinedAnchor_self,
    CategoryTheory.Functor.map_id]

theorem interLeftAnchor_far : K.interLeftAnchor K.far = K.leftConnector := by
  rw [interLeftAnchor_of_not_joined K K.not_joined, joinedAnchor_self,
    CategoryTheory.Functor.map_id, Category.comp_id]

theorem interRightAnchor_far : K.interRightAnchor K.far = K.rightConnector := by
  rw [interRightAnchor_of_not_joined K K.not_joined, joinedAnchor_self,
    CategoryTheory.Functor.map_id, Category.comp_id]

def transition : FundamentalGroup V (interToRight U V K.base) →*
    FundamentalGroup U (interToLeft U V K.base) :=
  (FundamentalGroup.map (interToLeft U V) K.base).comp
    (MulEquiv.ofBijective _ K.right_bijective).symm.toMonoidHom

theorem transition_map (g : FundamentalGroup (↑(U ∩ V)) K.base) :
    K.transition (FundamentalGroup.map (interToRight U V) K.base g) =
      FundamentalGroup.map (interToLeft U V) K.base g := by
  rw [transition, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    ← MulEquiv.ofBijective_apply _ K.right_bijective, MulEquiv.symm_apply_apply]

theorem transition_injective : Function.Injective K.transition := by
  rw [transition, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom]
  exact K.left_injective.comp (MulEquiv.injective _)

def rightEdge :
    FundamentalGroup (↑(U ∩ V)) K.far →* FundamentalGroup U (interToLeft U V K.base) :=
  K.transition.comp ((conjHom K.rightConnector).comp
    (FundamentalGroup.map (interToRight U V) K.far))

def leftEdge :
    FundamentalGroup (↑(U ∩ V)) K.far →* FundamentalGroup U (interToLeft U V K.base) :=
  (conjHom K.leftConnector).comp (FundamentalGroup.map (interToLeft U V) K.far)

theorem rightEdge_injective : Function.Injective K.rightEdge :=
  K.transition_injective.comp
    ((conjHom_injective K.rightConnector).comp K.right_injective_far)

theorem leftEdge_injective : Function.Injective K.leftEdge :=
  (conjHom_injective K.leftConnector).comp K.left_injective_far

def edgePairing : K.rightEdge.range ≃* K.leftEdge.range :=
  (MonoidHom.ofInjective K.rightEdge_injective).symm.trans
    (MonoidHom.ofInjective K.leftEdge_injective)

theorem edgePairing_ofInjective (ℓ : FundamentalGroup (↑(U ∩ V)) K.far) :
    K.edgePairing (MonoidHom.ofInjective K.rightEdge_injective ℓ) =
      MonoidHom.ofInjective K.leftEdge_injective ℓ := by
  rw [edgePairing, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]

abbrev Extension :=
  HNNExtension (FundamentalGroup U (interToLeft U V K.base)) K.rightEdge.range K.leftEdge.range
    K.edgePairing

theorem t_conj (ℓ : FundamentalGroup (↑(U ∩ V)) K.far) :
    (HNNExtension.t : K.Extension) * HNNExtension.of (K.rightEdge ℓ) * HNNExtension.t⁻¹ =
      HNNExtension.of (K.leftEdge ℓ) := by
  have h := HNNExtension.equiv_eq_conj (φ := K.edgePairing)
    (MonoidHom.ofInjective K.rightEdge_injective ℓ)
  rw [K.edgePairing_ofInjective, MonoidHom.ofInjective_apply, MonoidHom.ofInjective_apply] at h
  exact h.symm

def leftFunctor : FundamentalGroupoid U ⥤ ULift.{u} (SingleObj K.Extension) :=
  anchoredFunctor ((FundamentalGroupoid.map (interToLeft U V)).obj (FundamentalGroupoid.mk K.base))
    (fun c => K.leftAnchor c.as) HNNExtension.of 1

def rightFunctor : FundamentalGroupoid V ⥤ ULift.{u} (SingleObj K.Extension) :=
  anchoredFunctor ((FundamentalGroupoid.map (interToRight U V)).obj (FundamentalGroupoid.mk K.base))
    (fun c => K.rightAnchor c.as) (HNNExtension.of.comp K.transition)
    (fun c => K.rightTwist HNNExtension.t c.as)

theorem leftFunctor_map_inter {a b : ↑(U ∩ V)}
    (p : FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b) :
    @Eq K.Extension (K.leftFunctor.map ((FundamentalGroupoid.map (interToLeft U V)).map p))
      (HNNExtension.of (K.interLeftAnchor a ≫ (FundamentalGroupoid.map (interToLeft U V)).map p ≫
        Groupoid.inv (K.interLeftAnchor b))) := by
  change (1 : K.Extension) * (HNNExtension.of (K.leftAnchor (interToLeft U V a) ≫
      (FundamentalGroupoid.map (interToLeft U V)).map p ≫
      Groupoid.inv (K.leftAnchor (interToLeft U V b))) : K.Extension) * (1 : K.Extension)⁻¹ = _
  rw [K.leftAnchor_interToLeft, K.leftAnchor_interToLeft, one_mul, inv_one, mul_one]
  rfl

theorem rightFunctor_map_inter {a b : ↑(U ∩ V)}
    (p : FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b) :
    @Eq K.Extension (K.rightFunctor.map ((FundamentalGroupoid.map (interToRight U V)).map p))
      (K.interTwist HNNExtension.t b * (HNNExtension.of (K.transition (K.interRightAnchor a ≫
        (FundamentalGroupoid.map (interToRight U V)).map p ≫
        Groupoid.inv (K.interRightAnchor b))) : K.Extension) *
        (K.interTwist HNNExtension.t a)⁻¹) := by
  change K.rightTwist HNNExtension.t (interToRight U V b) * (HNNExtension.of (K.transition
      (K.rightAnchor (interToRight U V a) ≫ (FundamentalGroupoid.map (interToRight U V)).map p ≫
      Groupoid.inv (K.rightAnchor (interToRight U V b)))) : K.Extension) *
      (K.rightTwist HNNExtension.t (interToRight U V a))⁻¹ = _
  rw [K.rightAnchor_interToRight, K.rightAnchor_interToRight, K.rightTwist_interToRight,
    K.rightTwist_interToRight]
  rfl

theorem compat_map (a b : ↑(U ∩ V)) (p : FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b) :
    @Eq K.Extension (K.leftFunctor.map ((FundamentalGroupoid.map (interToLeft U V)).map p))
      (K.rightFunctor.map ((FundamentalGroupoid.map (interToRight U V)).map p)) := by
  have hab : Joined a b := joined_of_hom p
  rw [K.leftFunctor_map_inter, K.rightFunctor_map_inter]
  by_cases hj : Joined K.base a
  · have hjb : Joined K.base b := hj.trans hab
    rw [K.interLeftAnchor_of_joined hj, K.interLeftAnchor_of_joined hjb,
      K.interRightAnchor_of_joined hj, K.interRightAnchor_of_joined hjb,
      K.interTwist_of_joined _ hj, K.interTwist_of_joined _ hjb, one_mul, inv_one, mul_one]
    have e1 := map_conj_three (FundamentalGroupoid.map (interToLeft U V))
      (joinedAnchor K.base a hj) p (joinedAnchor K.base b hjb)
    have e2 := map_conj_three (FundamentalGroupoid.map (interToRight U V))
      (joinedAnchor K.base a hj) p (joinedAnchor K.base b hjb)
    have e3 := K.transition_map (joinedAnchor K.base a hj ≫ p ≫
      Groupoid.inv (joinedAnchor K.base b hjb))
    exact (congrArg (fun z => (HNNExtension.of z : K.Extension)) e1.symm).trans
      ((congrArg (fun z => (HNNExtension.of z : K.Extension)) e3.symm).trans
        (congrArg (fun z => (HNNExtension.of (K.transition z) : K.Extension)) e2))
  · have hjb : ¬ Joined K.base b := fun h => hj (h.trans hab.symm)
    rw [K.interLeftAnchor_of_not_joined hj, K.interLeftAnchor_of_not_joined hjb,
      K.interRightAnchor_of_not_joined hj, K.interRightAnchor_of_not_joined hjb,
      K.interTwist_of_not_joined _ hj, K.interTwist_of_not_joined _ hjb]
    have e1 := conjHom_map_conj (FundamentalGroupoid.map (interToLeft U V)) K.leftConnector
      (joinedAnchor K.far a ((K.joined a).resolve_left hj)) p
      (joinedAnchor K.far b ((K.joined b).resolve_left hjb))
    have e2 := conjHom_map_conj (FundamentalGroupoid.map (interToRight U V)) K.rightConnector
      (joinedAnchor K.far a ((K.joined a).resolve_left hj)) p
      (joinedAnchor K.far b ((K.joined b).resolve_left hjb))
    exact (congrArg (fun z => (HNNExtension.of z : K.Extension)) e1.symm).trans
      ((K.t_conj _).symm.trans (congrArg (fun z => HNNExtension.t *
        (HNNExtension.of (K.transition z) : K.Extension) * HNNExtension.t⁻¹) e2))

theorem compat : FundamentalGroupoid.map (interToLeft U V) ⋙ K.leftFunctor =
    FundamentalGroupoid.map (interToRight U V) ⋙ K.rightFunctor := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) (fun a b p => heq_of_eq ?_)
  exact K.compat_map a.as b.as p

def ambientFunctor : FundamentalGroupoid X ⥤ ULift.{u} (SingleObj K.Extension) :=
  IsPushout.desc (seifertVanKampen U V K.isOpen_left K.isOpen_right K.cover)
    (W := Grpd.of (ULift.{u} (SingleObj K.Extension))) K.leftFunctor K.rightFunctor K.compat

theorem ambientFunctor_left :
    FundamentalGroupoid.map (subsetToAmbient U) ⋙ K.ambientFunctor = K.leftFunctor :=
  IsPushout.inl_desc (seifertVanKampen U V K.isOpen_left K.isOpen_right K.cover)
    (W := Grpd.of (ULift.{u} (SingleObj K.Extension))) K.leftFunctor K.rightFunctor K.compat

theorem ambientFunctor_right :
    FundamentalGroupoid.map (subsetToAmbient V) ⋙ K.ambientFunctor = K.rightFunctor :=
  IsPushout.inr_desc (seifertVanKampen U V K.isOpen_left K.isOpen_right K.cover)
    (W := Grpd.of (ULift.{u} (SingleObj K.Extension))) K.leftFunctor K.rightFunctor K.compat

theorem ambientFunctor_map_left {a b : FundamentalGroupoid U} (p : a ⟶ b) :
    @Eq K.Extension (K.ambientFunctor.map ((FundamentalGroupoid.map (subsetToAmbient U)).map p))
      (K.leftFunctor.map p) :=
  eq_of_heq (CategoryTheory.Functor.hcongr_hom K.ambientFunctor_left p)

theorem ambientFunctor_map_right {a b : FundamentalGroupoid V} (p : a ⟶ b) :
    @Eq K.Extension (K.ambientFunctor.map ((FundamentalGroupoid.map (subsetToAmbient V)).map p))
      (K.rightFunctor.map p) :=
  eq_of_heq (CategoryTheory.Functor.hcongr_hom K.ambientFunctor_right p)

def toExtension :
    FundamentalGroup X ((subsetToAmbient U) (interToLeft U V K.base)) →* K.Extension where
  toFun g := (K.ambientFunctor.map g : K.Extension)
  map_one' := K.ambientFunctor.map_id _
  map_mul' g h := K.ambientFunctor.map_comp h g

def rightConnectorAmbient : FundamentalGroupoid.mk K.base.1 ⟶ FundamentalGroupoid.mk K.far.1 :=
  (FundamentalGroupoid.map (subsetToAmbient V)).map K.rightConnector

def leftConnectorAmbient : FundamentalGroupoid.mk K.base.1 ⟶ FundamentalGroupoid.mk K.far.1 :=
  (FundamentalGroupoid.map (subsetToAmbient U)).map K.leftConnector

def connectorPath : FundamentalGroup X K.base.1 :=
  K.rightConnectorAmbient ≫ Groupoid.inv K.leftConnectorAmbient

def connectorLoop : FundamentalGroup X ((subsetToAmbient U) (interToLeft U V K.base)) :=
  K.connectorPath

theorem ambient_transition (z : FundamentalGroup V (interToRight U V K.base)) :
    FundamentalGroup.map (subsetToAmbient U) (interToLeft U V K.base) (K.transition z) =
      FundamentalGroup.map (subsetToAmbient V) (interToRight U V K.base) z := by
  obtain ⟨y, rfl⟩ := K.right_bijective.2 z
  rw [K.transition_map]
  exact (ambient_left_map y).trans (ambient_right_map y).symm

theorem connectorLoop_relation (a : K.rightEdge.range) :
    K.connectorLoop * FundamentalGroup.map (subsetToAmbient U) (interToLeft U V K.base) a =
      FundamentalGroup.map (subsetToAmbient U) (interToLeft U V K.base) (K.edgePairing a) *
        K.connectorLoop := by
  obtain ⟨ℓ, rfl⟩ := (MonoidHom.ofInjective K.rightEdge_injective).surjective a
  rw [K.edgePairing_ofInjective, MonoidHom.ofInjective_apply, MonoidHom.ofInjective_apply]
  have hR : @Eq (FundamentalGroup X K.base.1)
      (FundamentalGroup.map (subsetToAmbient U) (interToLeft U V K.base) (K.rightEdge ℓ))
      (K.rightConnectorAmbient ≫ FundamentalGroup.map (subsetToAmbient (U ∩ V)) K.far ℓ ≫
        Groupoid.inv K.rightConnectorAmbient) := by
    refine (K.ambient_transition _).trans ?_
    change (FundamentalGroupoid.map (subsetToAmbient V)).map (K.rightConnector ≫
      (FundamentalGroupoid.map (interToRight U V)).map ℓ ≫ Groupoid.inv K.rightConnector) = _
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, map_groupoidInv,
      ambient_right_map]
    rfl
  have hL : @Eq (FundamentalGroup X K.base.1)
      (FundamentalGroup.map (subsetToAmbient U) (interToLeft U V K.base) (K.leftEdge ℓ))
      (K.leftConnectorAmbient ≫ FundamentalGroup.map (subsetToAmbient (U ∩ V)) K.far ℓ ≫
        Groupoid.inv K.leftConnectorAmbient) := by
    change (FundamentalGroupoid.map (subsetToAmbient U)).map (K.leftConnector ≫
      (FundamentalGroupoid.map (interToLeft U V)).map ℓ ≫ Groupoid.inv K.leftConnector) = _
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, map_groupoidInv,
      ambient_left_map]
    rfl
  rw [hR, hL]
  change (K.rightConnectorAmbient ≫ FundamentalGroup.map (subsetToAmbient (U ∩ V)) K.far ℓ ≫
      Groupoid.inv K.rightConnectorAmbient) ≫
      (K.rightConnectorAmbient ≫ Groupoid.inv K.leftConnectorAmbient) =
    (K.rightConnectorAmbient ≫ Groupoid.inv K.leftConnectorAmbient) ≫
      (K.leftConnectorAmbient ≫ FundamentalGroup.map (subsetToAmbient (U ∩ V)) K.far ℓ ≫
      Groupoid.inv K.leftConnectorAmbient)
  simp only [Category.assoc]
  exact congrArg (fun z => K.rightConnectorAmbient ≫ z)
    ((comp_groupoidInv_comp_cancel (FundamentalGroup.map (subsetToAmbient (U ∩ V)) K.far ℓ)
      K.rightConnectorAmbient (Groupoid.inv K.leftConnectorAmbient)).trans
      (groupoidInv_comp_cancel K.leftConnectorAmbient _).symm)

def ofExtension :
    K.Extension →* FundamentalGroup X ((subsetToAmbient U) (interToLeft U V K.base)) :=
  HNNExtension.lift (FundamentalGroup.map (subsetToAmbient U) (interToLeft U V K.base))
    K.connectorLoop K.connectorLoop_relation

theorem leftFunctor_map_base (g : FundamentalGroup U (interToLeft U V K.base)) :
    @Eq K.Extension (K.leftFunctor.map g) (HNNExtension.of g) := by
  change (1 : K.Extension) * (HNNExtension.of (K.leftAnchor (interToLeft U V K.base) ≫ g ≫
      Groupoid.inv (K.leftAnchor (interToLeft U V K.base))) : K.Extension) *
      (1 : K.Extension)⁻¹ = _
  rw [K.leftAnchor_interToLeft, K.interLeftAnchor_base, one_mul, inv_one, mul_one]
  exact congrArg (fun z => (HNNExtension.of z : K.Extension)) (id_conj g)

theorem ambientFunctor_leftConnectorAmbient :
    @Eq K.Extension (K.ambientFunctor.map K.leftConnectorAmbient) 1 := by
  refine (K.ambientFunctor_map_left K.leftConnector).trans ?_
  change (1 : K.Extension) * (HNNExtension.of (K.leftAnchor (interToLeft U V K.base) ≫
      K.leftConnector ≫ Groupoid.inv (K.leftAnchor (interToLeft U V K.far))) : K.Extension) *
      (1 : K.Extension)⁻¹ = 1
  rw [K.leftAnchor_interToLeft, K.leftAnchor_interToLeft, K.interLeftAnchor_base,
    K.interLeftAnchor_far, one_mul, inv_one, mul_one]
  exact (congrArg (fun z => (HNNExtension.of z : K.Extension))
    (id_comp_comp_groupoidInv K.leftConnector)).trans (map_one _)

theorem ambientFunctor_rightConnectorAmbient :
    @Eq K.Extension (K.ambientFunctor.map K.rightConnectorAmbient) HNNExtension.t := by
  refine (K.ambientFunctor_map_right K.rightConnector).trans ?_
  change K.rightTwist HNNExtension.t (interToRight U V K.far) * (HNNExtension.of (K.transition
      (K.rightAnchor (interToRight U V K.base) ≫ K.rightConnector ≫
      Groupoid.inv (K.rightAnchor (interToRight U V K.far)))) : K.Extension) *
      (K.rightTwist HNNExtension.t (interToRight U V K.base))⁻¹ = _
  rw [K.rightAnchor_interToRight, K.rightAnchor_interToRight, K.interRightAnchor_base,
    K.interRightAnchor_far, K.rightTwist_interToRight, K.rightTwist_interToRight,
    K.interTwist_of_not_joined _ K.not_joined, K.interTwist_of_joined _ (Joined.refl _),
    inv_one, mul_one]
  calc _ = HNNExtension.t * (HNNExtension.of (K.transition 1) : K.Extension) :=
        congrArg (fun z => HNNExtension.t * (HNNExtension.of (K.transition z) : K.Extension))
          (id_comp_comp_groupoidInv K.rightConnector)
    _ = HNNExtension.t := by rw [map_one, map_one, mul_one]

theorem toExtension_connectorLoop : K.toExtension K.connectorLoop = HNNExtension.t := by
  change @Eq K.Extension (K.ambientFunctor.map (K.rightConnectorAmbient ≫
    Groupoid.inv K.leftConnectorAmbient)) _
  rw [CategoryTheory.Functor.map_comp, map_groupoidInv, K.ambientFunctor_leftConnectorAmbient,
    K.ambientFunctor_rightConnectorAmbient]
  exact (by rw [inv_one, one_mul] : (1 : K.Extension)⁻¹ * HNNExtension.t = HNNExtension.t)

theorem toExtension_comp_ofExtension : K.toExtension.comp K.ofExtension = MonoidHom.id _ := by
  apply HNNExtension.hom_ext
  · ext g
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.id_apply,
      ofExtension, HNNExtension.lift_of]
    change @Eq K.Extension
      (K.ambientFunctor.map ((FundamentalGroupoid.map (subsetToAmbient U)).map g)) _
    rw [K.ambientFunctor_map_left, K.leftFunctor_map_base]
  · rw [MonoidHom.comp_apply, MonoidHom.id_apply, ofExtension, HNNExtension.lift_t]
    exact K.toExtension_connectorLoop


open Classical in
def ambientAnchor (x : X) :
    FundamentalGroupoid.mk ((subsetToAmbient U) (interToLeft U V K.base)) ⟶
      FundamentalGroupoid.mk x :=
  if h : x ∈ U then (FundamentalGroupoid.map (subsetToAmbient U)).map (K.leftAnchor ⟨x, h⟩)
  else (FundamentalGroupoid.map (subsetToAmbient V)).map
    (K.rightAnchor ⟨x, mem_right_of_not_mem_left K.cover h⟩)

def identityFunctor : FundamentalGroupoid X ⥤
    ULift.{u} (SingleObj (FundamentalGroup X ((subsetToAmbient U) (interToLeft U V K.base)))) :=
  anchoredFunctor (FundamentalGroupoid.mk ((subsetToAmbient U) (interToLeft U V K.base)))
    (fun c => K.ambientAnchor c.as) (MonoidHom.id _) 1

theorem ambientAnchor_left (x : U) :
    K.ambientAnchor x.1 = (FundamentalGroupoid.map (subsetToAmbient U)).map (K.leftAnchor x) :=
  dite_eq_left x.2

theorem ambientAnchor_base :
    K.ambientAnchor ((subsetToAmbient U) (interToLeft U V K.base)) = 𝟙 _ := by
  refine (K.ambientAnchor_left (interToLeft U V K.base)).trans ?_
  rw [K.leftAnchor_interToLeft, K.interLeftAnchor_base]
  exact CategoryTheory.Functor.map_id _ _

def rightAnchorAmbient (x : V) :
    FundamentalGroupoid.mk ((subsetToAmbient U) (interToLeft U V K.base)) ⟶
      FundamentalGroupoid.mk x.1 :=
  (FundamentalGroupoid.map (subsetToAmbient V)).map
    (X := (FundamentalGroupoid.map (interToRight U V)).obj (FundamentalGroupoid.mk K.base))
    (Y := FundamentalGroupoid.mk x) (K.rightAnchor x)

def twistLoop (x : V) :
    FundamentalGroupoid.mk ((subsetToAmbient U) (interToLeft U V K.base)) ⟶
      FundamentalGroupoid.mk ((subsetToAmbient U) (interToLeft U V K.base)) :=
  K.ofExtension (K.rightTwist HNNExtension.t x)

theorem ambientAnchor_right (x : V) :
    K.ambientAnchor x.1 = Groupoid.inv (K.twistLoop x) ≫ K.rightAnchorAmbient x := by
  by_cases h : (x : X) ∈ U
  · let a : ↑(U ∩ V) := ⟨x.1, h, x.2⟩
    have hA : K.ambientAnchor x.1 =
        (FundamentalGroupoid.map (subsetToAmbient U)).map (K.interLeftAnchor a) := by
      refine (K.ambientAnchor_left ⟨x.1, h⟩).trans ?_
      rw [show K.leftAnchor ⟨x.1, h⟩ = K.interLeftAnchor a from K.leftAnchor_interToLeft a]
      rfl
    have hR : K.rightAnchorAmbient x =
        (FundamentalGroupoid.map (subsetToAmbient V)).map (K.interRightAnchor a) := by
      change (FundamentalGroupoid.map (subsetToAmbient V)).map
        (K.rightAnchor (interToRight U V a)) = _
      rw [K.rightAnchor_interToRight]
      rfl
    have hT : K.twistLoop x = K.ofExtension (K.interTwist HNNExtension.t a) := by
      change K.ofExtension (K.rightTwist HNNExtension.t (interToRight U V a)) = _
      rw [K.rightTwist_interToRight]
    rw [hA, hR, hT]
    by_cases hj : Joined K.base a
    · rw [K.interLeftAnchor_of_joined hj, K.interRightAnchor_of_joined hj,
        K.interTwist_of_joined _ hj, map_one]
      exact (ambient_left_map _).trans
        ((ambient_right_map _).symm.trans (groupoidInv_id_comp _).symm)
    · rw [K.interLeftAnchor_of_not_joined hj, K.interRightAnchor_of_not_joined hj,
        K.interTwist_of_not_joined _ hj, ofExtension, HNNExtension.lift_t]
      have e1 := CategoryTheory.Functor.map_comp (FundamentalGroupoid.map (subsetToAmbient U))
        K.leftConnector ((FundamentalGroupoid.map (interToLeft U V)).map
          (joinedAnchor K.far a ((K.joined a).resolve_left hj)))
      have e2 := CategoryTheory.Functor.map_comp (FundamentalGroupoid.map (subsetToAmbient V))
        K.rightConnector ((FundamentalGroupoid.map (interToRight U V)).map
          (joinedAnchor K.far a ((K.joined a).resolve_left hj)))
      rw [e1, e2, ambient_left_map, ambient_right_map]
      exact (groupoidInv_comp_groupoidInv_cancel K.rightConnectorAmbient K.leftConnectorAmbient
        _).symm
  · have hA : K.ambientAnchor x.1 = K.rightAnchorAmbient x := dite_eq_right h
    have hT : K.twistLoop x = 1 := by
      change K.ofExtension (K.rightTwist HNNExtension.t x) = 1
      rw [show K.rightTwist HNNExtension.t x = 1 from dite_eq_right h, map_one]
    rw [hA, hT]
    exact (groupoidInv_id_comp _).symm

theorem agree_left {a b : FundamentalGroupoid U} (p : a ⟶ b) :
    K.ofExtension (K.leftFunctor.map p) =
      K.identityFunctor.map ((FundamentalGroupoid.map (subsetToAmbient U)).map p) := by
  have hl : K.ofExtension (K.leftFunctor.map p) =
      (FundamentalGroupoid.map (subsetToAmbient U)).map
        (K.leftAnchor a.as ≫ p ≫ Groupoid.inv (K.leftAnchor b.as)) := by
    change K.ofExtension ((1 : K.Extension) * (HNNExtension.of (K.leftAnchor a.as ≫ p ≫
      Groupoid.inv (K.leftAnchor b.as)) : K.Extension) * (1 : K.Extension)⁻¹) = _
    rw [one_mul, inv_one, mul_one, ofExtension, HNNExtension.lift_of]
    rfl
  have hr : K.identityFunctor.map ((FundamentalGroupoid.map (subsetToAmbient U)).map p) =
      K.ambientAnchor a.as.1 ≫ (FundamentalGroupoid.map (subsetToAmbient U)).map p ≫
        Groupoid.inv (K.ambientAnchor b.as.1) := by
    change (1 : FundamentalGroup X ((subsetToAmbient U) (interToLeft U V K.base))) *
      MonoidHom.id (FundamentalGroup X ((subsetToAmbient U) (interToLeft U V K.base)))
        (K.ambientAnchor a.as.1 ≫ (FundamentalGroupoid.map (subsetToAmbient U)).map p ≫
        Groupoid.inv (K.ambientAnchor b.as.1)) *
      (1 : FundamentalGroup X ((subsetToAmbient U) (interToLeft U V K.base)))⁻¹ = _
    rw [one_mul, inv_one, mul_one, MonoidHom.id_apply]
  rw [hl, hr, K.ambientAnchor_left, K.ambientAnchor_left]
  exact map_conj_three _ _ _ _

theorem agree_right {a b : FundamentalGroupoid V} (p : a ⟶ b) :
    K.ofExtension (K.rightFunctor.map p) =
      K.identityFunctor.map ((FundamentalGroupoid.map (subsetToAmbient V)).map p) := by
  have hl : K.ofExtension (K.rightFunctor.map p) =
      endOf (K.twistLoop b.as) * endOf (K.rightAnchorAmbient a.as ≫
        (FundamentalGroupoid.map (subsetToAmbient V)).map p ≫
        Groupoid.inv (K.rightAnchorAmbient b.as)) * (endOf (K.twistLoop a.as))⁻¹ := by
    change K.ofExtension (K.rightTwist HNNExtension.t b.as * (HNNExtension.of (K.transition
      (K.rightAnchor a.as ≫ p ≫ Groupoid.inv (K.rightAnchor b.as))) : K.Extension) *
      (K.rightTwist HNNExtension.t a.as)⁻¹) = _
    rw [map_mul, map_mul, map_inv]
    rw [show K.ofExtension (HNNExtension.of (K.transition (K.rightAnchor a.as ≫ p ≫
        Groupoid.inv (K.rightAnchor b.as)))) =
        FundamentalGroup.map (subsetToAmbient U) (interToLeft U V K.base) (K.transition
          (K.rightAnchor a.as ≫ p ≫ Groupoid.inv (K.rightAnchor b.as))) from
        HNNExtension.lift_of _ _ _ _, K.ambient_transition]
    exact congrArg (fun w : FundamentalGroup X ((subsetToAmbient U) (interToLeft U V K.base)) =>
      K.ofExtension (K.rightTwist HNNExtension.t b.as) * w *
        (K.ofExtension (K.rightTwist HNNExtension.t a.as))⁻¹)
      (map_conj_three (FundamentalGroupoid.map (subsetToAmbient V)) (K.rightAnchor a.as) p
        (K.rightAnchor b.as))
  have hr : K.identityFunctor.map ((FundamentalGroupoid.map (subsetToAmbient V)).map p) =
      K.ambientAnchor a.as.1 ≫ (FundamentalGroupoid.map (subsetToAmbient V)).map p ≫
        Groupoid.inv (K.ambientAnchor b.as.1) := by
    change (1 : FundamentalGroup X ((subsetToAmbient U) (interToLeft U V K.base))) *
      MonoidHom.id (FundamentalGroup X ((subsetToAmbient U) (interToLeft U V K.base)))
        (K.ambientAnchor a.as.1 ≫ (FundamentalGroupoid.map (subsetToAmbient V)).map p ≫
        Groupoid.inv (K.ambientAnchor b.as.1)) *
      (1 : FundamentalGroup X ((subsetToAmbient U) (interToLeft U V K.base)))⁻¹ = _
    rw [one_mul, inv_one, mul_one, MonoidHom.id_apply]
  rw [hl, hr, K.ambientAnchor_right, K.ambientAnchor_right]
  exact twist_conj _ _ _ _ _

theorem ambient_comp_eq : K.ambientFunctor ⋙ homFunctor K.ofExtension = K.identityFunctor := by
  apply IsPushout.hom_ext (seifertVanKampen U V K.isOpen_left K.isOpen_right K.cover)
    (W := Grpd.of (ULift.{u}
      (SingleObj (FundamentalGroup X ((subsetToAmbient U) (interToLeft U V K.base))))))
  · refine CategoryTheory.Functor.hext (fun _ => rfl) (fun a b p => heq_of_eq ?_)
    exact (congrArg K.ofExtension (K.ambientFunctor_map_left p)).trans (K.agree_left p)
  · refine CategoryTheory.Functor.hext (fun _ => rfl) (fun a b p => heq_of_eq ?_)
    exact (congrArg K.ofExtension (K.ambientFunctor_map_right p)).trans (K.agree_right p)

theorem ofExtension_comp_toExtension : K.ofExtension.comp K.toExtension = MonoidHom.id _ := by
  ext g
  rw [MonoidHom.comp_apply, MonoidHom.id_apply]
  refine (eq_of_heq (CategoryTheory.Functor.hcongr_hom K.ambient_comp_eq g)).trans ?_
  change (1 : FundamentalGroup X ((subsetToAmbient U) (interToLeft U V K.base))) *
    MonoidHom.id (FundamentalGroup X ((subsetToAmbient U) (interToLeft U V K.base)))
      (K.ambientAnchor ((subsetToAmbient U) (interToLeft U V K.base)) ≫ g ≫
        Groupoid.inv (K.ambientAnchor ((subsetToAmbient U) (interToLeft U V K.base)))) *
    (1 : FundamentalGroup X ((subsetToAmbient U) (interToLeft U V K.base)))⁻¹ = g
  rw [one_mul, inv_one, mul_one, MonoidHom.id_apply, K.ambientAnchor_base]
  exact id_conj g

def equivExtension :
    FundamentalGroup X ((subsetToAmbient U) (interToLeft U V K.base)) ≃* K.Extension :=
  MonoidHom.toMulEquiv K.toExtension K.ofExtension K.ofExtension_comp_toExtension
    K.toExtension_comp_ofExtension

theorem equivExtension_symm_of (g : FundamentalGroup U (interToLeft U V K.base)) :
    K.equivExtension.symm (HNNExtension.of g) =
      FundamentalGroup.map (subsetToAmbient U) (interToLeft U V K.base) g :=
  HNNExtension.lift_of (FundamentalGroup.map (subsetToAmbient U) (interToLeft U V K.base))
    K.connectorLoop K.connectorLoop_relation g

theorem injective_fundamentalGroup_map_left :
    Function.Injective (FundamentalGroup.map (subsetToAmbient U) (interToLeft U V K.base)) := by
  intro g h hgh
  apply HNNExtension.of_injective (A := K.rightEdge.range) (B := K.leftEdge.range)
    (φ := K.edgePairing)
  apply K.equivExtension.symm.injective
  rw [K.equivExtension_symm_of, K.equivExtension_symm_of]
  exact hgh

end TwoComponentCover

section Retract
variable {Y Z T : Type*} [TopologicalSpace Y] [TopologicalSpace Z] [TopologicalSpace T]

theorem surjective_fundamentalGroup_map_of_clopen (i : C(Z, Y)) (r : C(Y, Z))
    (hr : Function.LeftInverse r i) (S : Set Y) (hS : IsClopen S)
    (hiS : ∀ y ∈ S, i (r y) = y) (z : Z) (hz : i z ∈ S) :
    Function.Surjective (FundamentalGroup.map i z) := by
  intro γ
  refine ⟨FundamentalGroup.mapOfEq r (hr z) γ, ?_⟩
  induction γ using Path.Homotopic.Quotient.ind with
  | mk p =>
    have hpS : ∀ s, p s ∈ S := by
      have hcl : IsClopen (p ⁻¹' S) := hS.preimage p.continuous
      have h0 : (0 : unitInterval) ∈ p ⁻¹' S := by
        change p 0 ∈ S
        rw [Path.source]
        exact hz
      have huniv := hcl.eq_univ ⟨0, h0⟩
      intro s
      have hs : s ∈ p ⁻¹' S := huniv ▸ Set.mem_univ s
      exact hs
    rw [FundamentalGroup.mapOfEq_apply]
    change Path.Homotopic.Quotient.mk
      (((p.map r.continuous).cast (hr z).symm (hr z).symm).map i.continuous) =
        Path.Homotopic.Quotient.mk p
    congr 1
    ext s
    exact hiS _ (hpS s)

theorem bijective_fundamentalGroup_map_of_clopen (i : C(Z, Y)) (r : C(Y, Z))
    (hr : Function.LeftInverse r i) (S : Set Y) (hS : IsClopen S)
    (hiS : ∀ y ∈ S, i (r y) = y) (z : Z) (hz : i z ∈ S) :
    Function.Bijective (FundamentalGroup.map i z) :=
  ⟨injective_fundamentalGroup_map_of_leftInverse i r hr z,
    surjective_fundamentalGroup_map_of_clopen i r hr S hS hiS z hz⟩

theorem bijective_fundamentalGroup_map_of_comp (f : C(T, Y)) (g : C(Y, Z)) (t : T)
    (hf : Function.Bijective (FundamentalGroup.map f t))
    (hgf : Function.Bijective (FundamentalGroup.map (g.comp f) t)) :
    Function.Bijective (FundamentalGroup.map g (f t)) := by
  rw [GC.Topology.fundamentalGroup_map_comp, MonoidHom.coe_comp] at hgf
  refine ⟨fun a b hab => ?_, fun c => ?_⟩
  · obtain ⟨a', rfl⟩ := hf.2 a
    obtain ⟨b', rfl⟩ := hf.2 b
    rw [hgf.1 hab]
  · obtain ⟨x, hx⟩ := hgf.2 c
    exact ⟨_, hx⟩

theorem injective_fundamentalGroup_map_of_comp (f : C(T, Y)) (g : C(Y, Z)) (t : T)
    (hf : Function.Surjective (FundamentalGroup.map f t))
    (hgf : Function.Injective (FundamentalGroup.map (g.comp f) t)) :
    Function.Injective (FundamentalGroup.map g (f t)) := by
  rw [GC.Topology.fundamentalGroup_map_comp, MonoidHom.coe_comp] at hgf
  intro a b hab
  obtain ⟨a', rfl⟩ := hf a
  obtain ⟨b', rfl⟩ := hf b
  rw [hgf hab]

end Retract

section Slab

def slab (a b : ℝ) : Set (Torus × ℝ) := {p | a < p.2 ∧ p.2 < b}

private theorem convex_mem_slab {a b c s : ℝ} (hc : a < c ∧ c < b) (hs : a < s ∧ s < b)
    (τ : unitInterval) : a < (1 - (τ : ℝ)) * c + (τ : ℝ) * s ∧
      (1 - (τ : ℝ)) * c + (τ : ℝ) * s < b := by
  have h0 := τ.2.1
  have h1 := τ.2.2
  rcases le_total c s with hcs | hcs
  · constructor
    · nlinarith [mul_nonneg h0 (sub_nonneg.2 hcs)]
    · nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 hcs)]
  · constructor
    · nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 hcs)]
    · nlinarith [mul_nonneg h0 (sub_nonneg.2 hcs)]

def slabCore (a b c : ℝ) (hc : a < c ∧ c < b) : C(Torus, slab a b) :=
  ⟨fun t => ⟨(t, c), hc⟩, by fun_prop⟩

def slabProjection (a b : ℝ) : C(slab a b, Torus) :=
  ⟨fun p => p.1.1, by fun_prop⟩

def slabShrink (a b c : ℝ) (hc : a < c ∧ c < b) :
    ((slabCore a b c hc).comp (slabProjection a b)).Homotopy (ContinuousMap.id (slab a b)) where
  toFun z := ⟨(z.2.1.1, (1 - (z.1 : ℝ)) * c + (z.1 : ℝ) * z.2.1.2),
    convex_mem_slab hc z.2.2 z.1⟩
  continuous_toFun := Continuous.subtype_mk (by fun_prop) _
  map_zero_left p := Subtype.ext (Prod.ext rfl (by simp [slabCore, slabProjection]))
  map_one_left _ := Subtype.ext (Prod.ext rfl (by simp))

def slabHomotopyEquiv (a b c : ℝ) (hc : a < c ∧ c < b) : slab a b ≃ₕ Torus where
  toFun := slabProjection a b
  invFun := slabCore a b c hc
  left_inv := ⟨slabShrink a b c hc⟩
  right_inv := ContinuousMap.Homotopic.refl _

theorem bijective_slabCore (a b c : ℝ) (hc : a < c ∧ c < b) (t : Torus) :
    Function.Bijective (FundamentalGroup.map (slabCore a b c hc) t) :=
  bijective_fundamentalGroup_map_of_homotopyEquiv_leftInverse (slabHomotopyEquiv a b c hc) _
    (fun _ => rfl) t

end Slab

namespace TorusPresentation
variable {W : CompactCarrier.{u}} (G : TorusPresentation W) (j : Fin G.pairing.count)

theorem seam_mem_seamCollar {p : Torus × ℝ} (hp : -1 < p.2 ∧ p.2 < 1) :
    G.seam j p ∈ G.seamCollar j :=
  (G.seam j).map_source' (G.mem_seam_source j hp)

theorem seam_not_mem_seamSurface {p : Torus × ℝ} (hp : -1 < p.2 ∧ p.2 < 1) (h0 : p.2 ≠ 0) :
    G.seam j p ∉ G.seamSurface j := by
  rintro ⟨t, ht⟩
  have h := (G.seam j).toPartialEquiv.injOn
    (G.mem_seam_source j (⟨by norm_num, by norm_num⟩ : (t, (0 : ℝ)) ∈ signedCollarSource))
    (G.mem_seam_source j hp) ht
  exact h0 (by rw [← h])

def gapPoint (p : Torus × ℝ) (hp : -1 < p.2 ∧ p.2 < 1) (h0 : p.2 ≠ 0) :
    ↑((G.seamSurface j)ᶜ ∩ G.seamCollar j) :=
  ⟨G.seam j p, G.seam_not_mem_seamSurface j hp h0, G.seam_mem_seamCollar j hp⟩

def gapTime (y : ↑((G.seamSurface j)ᶜ ∩ G.seamCollar j)) : ℝ :=
  ((G.seam j).toPartialEquiv.symm y.1).2

theorem continuousOn_seam_symm :
    ContinuousOn (G.seam j).toPartialEquiv.symm (G.seam j).target :=
  (G.seam j).symm.contMDiffOn.continuousOn

theorem continuous_seam_symm_gap :
    Continuous fun y : ↑((G.seamSurface j)ᶜ ∩ G.seamCollar j) =>
      (G.seam j).toPartialEquiv.symm y.1 :=
  (G.continuousOn_seam_symm j).comp_continuous continuous_subtype_val fun y => y.2.2

theorem continuous_gapTime : Continuous (G.gapTime j) :=
  (G.continuous_seam_symm_gap j).snd

theorem seam_symm_mem_source (y : ↑((G.seamSurface j)ᶜ ∩ G.seamCollar j)) :
    -1 < ((G.seam j).toPartialEquiv.symm y.1).2 ∧ ((G.seam j).toPartialEquiv.symm y.1).2 < 1 := by
  have h := (G.seam j).toPartialEquiv.map_target y.2.2
  rw [G.seam_source j] at h
  exact h

theorem seam_seam_symm (y : ↑((G.seamSurface j)ᶜ ∩ G.seamCollar j)) :
    G.seam j ((G.seam j).toPartialEquiv.symm y.1) = y.1 :=
  (G.seam j).toPartialEquiv.right_inv y.2.2

theorem gapTime_ne_zero (y : ↑((G.seamSurface j)ᶜ ∩ G.seamCollar j)) : G.gapTime j y ≠ 0 := by
  intro h0
  apply y.2.1
  refine ⟨((G.seam j).toPartialEquiv.symm y.1).1, ?_⟩
  rw [seamTorus_apply, show (0 : ℝ) = ((G.seam j).toPartialEquiv.symm y.1).2 from h0.symm]
  exact G.seam_seam_symm j y

theorem gapTime_gapPoint (p : Torus × ℝ) (hp : -1 < p.2 ∧ p.2 < 1) (h0 : p.2 ≠ 0) :
    G.gapTime j (G.gapPoint j p hp h0) = p.2 := by
  change ((G.seam j).toPartialEquiv.symm (G.seam j p)).2 = p.2
  rw [(G.seam j).toPartialEquiv.left_inv (G.mem_seam_source j hp)]

theorem isPathConnected_seam_slab {a b : ℝ} (ha : -1 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    IsPathConnected (G.seam j '' slab a b) := by
  have hs : slab a b = (Set.univ : Set Torus) ×ˢ Set.Ioo a b := by
    ext p
    simp [slab]
  rw [hs]
  exact (isPathConnected_univ.prod ((convex_Ioo a b).isPathConnected
    (Set.nonempty_Ioo.mpr hab))).image' ((G.continuousOn_seam j).mono fun p hp =>
      G.mem_seam_source j ⟨lt_of_le_of_lt ha hp.2.1, lt_of_lt_of_le hp.2.2 hb⟩)

theorem seam_slab_subset_gap {a b : ℝ} (ha : -1 ≤ a) (hb : b ≤ 1) (h0 : (0 : ℝ) ∉ Set.Ioo a b) :
    G.seam j '' slab a b ⊆ (G.seamSurface j)ᶜ ∩ G.seamCollar j := by
  rintro _ ⟨p, hp, rfl⟩
  have hp' : -1 < p.2 ∧ p.2 < 1 := ⟨lt_of_le_of_lt ha hp.1, lt_of_lt_of_le hp.2 hb⟩
  have hne : p.2 ≠ 0 := fun h => h0 (h ▸ hp)
  exact (G.gapPoint j p hp' hne).2

theorem mem_seam_slab_of_gapTime {a b : ℝ} (y : ↑((G.seamSurface j)ᶜ ∩ G.seamCollar j))
    (hy : a < G.gapTime j y ∧ G.gapTime j y < b) :
    y.1 ∈ G.seam j '' slab a b :=
  ⟨(G.seam j).toPartialEquiv.symm y.1, hy, G.seam_seam_symm j y⟩

theorem joined_of_gapTime {a b : ℝ} (ha : -1 ≤ a) (hab : a < b) (hb : b ≤ 1)
    (h0 : (0 : ℝ) ∉ Set.Ioo a b) (y z : ↑((G.seamSurface j)ᶜ ∩ G.seamCollar j))
    (hy : a < G.gapTime j y ∧ G.gapTime j y < b) (hz : a < G.gapTime j z ∧ G.gapTime j z < b) :
    Joined y z :=
  (((G.isPathConnected_seam_slab j ha hab hb).joinedIn y.1
    (G.mem_seam_slab_of_gapTime j y hy) z.1
    (G.mem_seam_slab_of_gapTime j z hz)).mono
    (G.seam_slab_subset_gap j ha hb h0)).joined_subtype

def gapLevel (c : ℝ) (hc : -1 < c ∧ c < 1) (h0 : c ≠ 0) :
    C(Torus, ↑((G.seamSurface j)ᶜ ∩ G.seamCollar j)) :=
  ⟨fun t => G.gapPoint j (t, c) hc h0, Continuous.subtype_mk
    ((G.continuousOn_seam j).comp_continuous (by fun_prop) fun _ => G.mem_seam_source j hc) _⟩

theorem gapTime_gapLevel (c : ℝ) (hc : -1 < c ∧ c < 1) (h0 : c ≠ 0) (t : Torus) :
    G.gapTime j (G.gapLevel j c hc h0 t) = c :=
  G.gapTime_gapPoint j (t, c) hc h0

theorem bijective_collar_gapLevel (c : ℝ) (hc : -1 < c ∧ c < 1) (h0 : c ≠ 0) (t : Torus) :
    Function.Bijective (FundamentalGroup.map
      ((interToRight (G.seamSurface j)ᶜ (G.seamCollar j)).comp (G.gapLevel j c hc h0)) t) := by
  refine bijective_fundamentalGroup_map_of_homotopyEquiv_leftInverse
    (G.seamCollarHomotopyEquiv j) _ (fun s => ?_) t
  change ((G.seam j).toPartialEquiv.symm (G.seam j (s, c))).1 = s
  rw [(G.seam j).toPartialEquiv.left_inv (G.mem_seam_source j hc)]

def negativeInclusion : C(slab (-1) 0, ↑((G.seamSurface j)ᶜ ∩ G.seamCollar j)) :=
  ⟨fun p => G.gapPoint j p.1 ⟨p.2.1, by linarith [p.2.2]⟩ (ne_of_lt p.2.2),
    Continuous.subtype_mk ((G.continuousOn_seam j).comp_continuous continuous_subtype_val
      fun p => G.mem_seam_source j ⟨p.2.1, by linarith [p.2.2]⟩) _⟩

def positiveInclusion : C(slab 0 1, ↑((G.seamSurface j)ᶜ ∩ G.seamCollar j)) :=
  ⟨fun p => G.gapPoint j p.1 ⟨by linarith [p.2.1], p.2.2⟩ (ne_of_gt p.2.1),
    Continuous.subtype_mk ((G.continuousOn_seam j).comp_continuous continuous_subtype_val
      fun p => G.mem_seam_source j ⟨by linarith [p.2.1], p.2.2⟩) _⟩

theorem abs_gapTime_lt_one (y : ↑((G.seamSurface j)ᶜ ∩ G.seamCollar j)) :
    |G.gapTime j y| < 1 :=
  abs_lt.mpr (G.seam_symm_mem_source j y)

theorem abs_gapTime_pos (y : ↑((G.seamSurface j)ᶜ ∩ G.seamCollar j)) : 0 < |G.gapTime j y| :=
  abs_pos.mpr (G.gapTime_ne_zero j y)

def negativeRetraction : C(↑((G.seamSurface j)ᶜ ∩ G.seamCollar j), slab (-1) 0) :=
  ⟨fun y => ⟨(((G.seam j).toPartialEquiv.symm y.1).1, -|G.gapTime j y|),
    by linarith [G.abs_gapTime_lt_one j y], by linarith [G.abs_gapTime_pos j y]⟩,
    Continuous.subtype_mk ((G.continuous_seam_symm_gap j).fst.prodMk
      (G.continuous_gapTime j).abs.neg) _⟩

def positiveRetraction : C(↑((G.seamSurface j)ᶜ ∩ G.seamCollar j), slab 0 1) :=
  ⟨fun y => ⟨(((G.seam j).toPartialEquiv.symm y.1).1, |G.gapTime j y|),
    G.abs_gapTime_pos j y, G.abs_gapTime_lt_one j y⟩,
    Continuous.subtype_mk ((G.continuous_seam_symm_gap j).fst.prodMk
      (G.continuous_gapTime j).abs) _⟩

theorem negativeRetraction_leftInverse :
    Function.LeftInverse (G.negativeRetraction j) (G.negativeInclusion j) := by
  intro p
  have hp : -1 < p.1.2 ∧ p.1.2 < 1 := ⟨p.2.1, by linarith [p.2.2]⟩
  have hl := (G.seam j).toPartialEquiv.left_inv (G.mem_seam_source j hp)
  apply Subtype.ext
  apply Prod.ext
  · change ((G.seam j).toPartialEquiv.symm (G.seam j p.1)).1 = p.1.1
    rw [hl]
  · change -|G.gapTime j (G.gapPoint j p.1 hp (ne_of_lt p.2.2))| = p.1.2
    rw [G.gapTime_gapPoint, abs_of_neg p.2.2, neg_neg]

theorem positiveRetraction_leftInverse :
    Function.LeftInverse (G.positiveRetraction j) (G.positiveInclusion j) := by
  intro p
  have hp : -1 < p.1.2 ∧ p.1.2 < 1 := ⟨by linarith [p.2.1], p.2.2⟩
  have hl := (G.seam j).toPartialEquiv.left_inv (G.mem_seam_source j hp)
  apply Subtype.ext
  apply Prod.ext
  · change ((G.seam j).toPartialEquiv.symm (G.seam j p.1)).1 = p.1.1
    rw [hl]
  · change |G.gapTime j (G.gapPoint j p.1 hp (ne_of_gt p.2.1))| = p.1.2
    rw [G.gapTime_gapPoint, abs_of_pos p.2.1]

theorem isClopen_gapTime_neg : IsClopen {y | G.gapTime j y < 0} := by
  have he : {y | G.gapTime j y < 0} = {y | G.gapTime j y ≤ 0} := by
    ext y
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun h => le_of_lt h, fun h => lt_of_le_of_ne h (G.gapTime_ne_zero j y)⟩
  refine ⟨?_, isOpen_lt (G.continuous_gapTime j) continuous_const⟩
  rw [he]
  exact isClosed_le (G.continuous_gapTime j) continuous_const

theorem isClopen_gapTime_pos : IsClopen {y | 0 < G.gapTime j y} := by
  have he : {y | 0 < G.gapTime j y} = {y | 0 ≤ G.gapTime j y} := by
    ext y
    simp only [Set.mem_ofPred_eq]
    exact ⟨fun h => le_of_lt h, fun h => lt_of_le_of_ne h (G.gapTime_ne_zero j y).symm⟩
  refine ⟨?_, isOpen_lt continuous_const (G.continuous_gapTime j)⟩
  rw [he]
  exact isClosed_le continuous_const (G.continuous_gapTime j)

theorem negativeInclusion_retraction (y : ↑((G.seamSurface j)ᶜ ∩ G.seamCollar j))
    (hy : y ∈ {y | G.gapTime j y < 0}) :
    G.negativeInclusion j (G.negativeRetraction j y) = y := by
  apply Subtype.ext
  change G.seam j (((G.seam j).toPartialEquiv.symm y.1).1, -|G.gapTime j y|) = y.1
  rw [abs_of_neg hy, neg_neg]
  exact G.seam_seam_symm j y

theorem positiveInclusion_retraction (y : ↑((G.seamSurface j)ᶜ ∩ G.seamCollar j))
    (hy : y ∈ {y | 0 < G.gapTime j y}) :
    G.positiveInclusion j (G.positiveRetraction j y) = y := by
  apply Subtype.ext
  change G.seam j (((G.seam j).toPartialEquiv.symm y.1).1, |G.gapTime j y|) = y.1
  rw [abs_of_pos hy]
  exact G.seam_seam_symm j y

theorem bijective_gapLevel_neg (t : Torus) :
    Function.Bijective (FundamentalGroup.map (G.gapLevel j (-2⁻¹) ⟨by norm_num, by norm_num⟩
      (by norm_num)) t) := by
  have hc : G.gapLevel j (-2⁻¹) ⟨by norm_num, by norm_num⟩ (by norm_num) =
      (G.negativeInclusion j).comp (slabCore (-1) 0 (-2⁻¹) ⟨by norm_num, by norm_num⟩) := rfl
  rw [hc, GC.Topology.fundamentalGroup_map_comp, MonoidHom.coe_comp]
  refine (bijective_fundamentalGroup_map_of_clopen _ _ (G.negativeRetraction_leftInverse j) _
    (G.isClopen_gapTime_neg j) (G.negativeInclusion_retraction j) _ ?_).comp
    (bijective_slabCore _ _ _ _ t)
  change G.gapTime j (G.gapLevel j (-2⁻¹) ⟨by norm_num, by norm_num⟩ (by norm_num) t) < 0
  rw [G.gapTime_gapLevel]
  norm_num

theorem bijective_gapLevel_pos (t : Torus) :
    Function.Bijective (FundamentalGroup.map (G.gapLevel j 2⁻¹ ⟨by norm_num, by norm_num⟩
      (by norm_num)) t) := by
  have hc : G.gapLevel j 2⁻¹ ⟨by norm_num, by norm_num⟩ (by norm_num) =
      (G.positiveInclusion j).comp (slabCore 0 1 2⁻¹ ⟨by norm_num, by norm_num⟩) := rfl
  rw [hc, GC.Topology.fundamentalGroup_map_comp, MonoidHom.coe_comp]
  refine (bijective_fundamentalGroup_map_of_clopen _ _ (G.positiveRetraction_leftInverse j) _
    (G.isClopen_gapTime_pos j) (G.positiveInclusion_retraction j) _ ?_).comp
    (bijective_slabCore _ _ _ _ t)
  change 0 < G.gapTime j (G.gapLevel j 2⁻¹ ⟨by norm_num, by norm_num⟩ (by norm_num) t)
  rw [G.gapTime_gapLevel]
  norm_num

def leftEnd : C(Torus, ↑(G.seamSurface j)ᶜ) :=
  (interToLeft (G.seamSurface j)ᶜ (G.seamCollar j)).comp
    (G.gapLevel j (-2⁻¹) ⟨by norm_num, by norm_num⟩ (by norm_num))

def rightEnd : C(Torus, ↑(G.seamSurface j)ᶜ) :=
  (interToLeft (G.seamSurface j)ᶜ (G.seamCollar j)).comp
    (G.gapLevel j 2⁻¹ ⟨by norm_num, by norm_num⟩ (by norm_num))

theorem compl_seamSurface_eq_leftSide [ConnectedSpace W.Carrier] (h : ¬ G.IsSeparating j) :
    (G.seamSurface j)ᶜ = G.leftSide j := by
  rw [IsSeparating, Set.not_disjoint_iff] at h
  obtain ⟨y, hyl, hyr⟩ := h
  have he : G.rightSide j = G.leftSide j :=
    (pathComponentIn_congr hyr).symm.trans (pathComponentIn_congr hyl)
  rw [G.compl_seamSurface_eq j, he, Set.union_self]

theorem pathConnectedSpace_compl_seamSurface [ConnectedSpace W.Carrier]
    (h : ¬ G.IsSeparating j) : PathConnectedSpace ↑(G.seamSurface j)ᶜ := by
  rw [← isPathConnected_iff_pathConnectedSpace, G.compl_seamSurface_eq_leftSide j h]
  exact isPathConnected_pathComponentIn (G.leftPoint_mem_compl j)

theorem seamSurface_compl_union_seamCollar :
    (G.seamSurface j)ᶜ ∪ G.seamCollar j = Set.univ := by
  refine Set.eq_univ_of_forall fun y => ?_
  by_cases hy : y ∈ G.seamSurface j
  · exact Or.inr (G.seamSurface_subset_seamCollar j hy)
  · exact Or.inl hy

def nonSeparatingCover [ConnectedSpace W.Carrier] (h : ¬ G.IsSeparating j) (t₀ : Torus)
    (hl : Function.Injective (FundamentalGroup.map (G.leftEnd j) t₀))
    (hr : Function.Injective (FundamentalGroup.map (G.rightEnd j) t₀)) :
    TwoComponentCover (G.seamSurface j)ᶜ (G.seamCollar j) where
  left_connected := G.pathConnectedSpace_compl_seamSurface j h
  right_connected := isPathConnected_iff_pathConnectedSpace.mp (G.isPathConnected_seamCollar j)
  isOpen_left := (G.isClosed_seamSurface j).isOpen_compl
  isOpen_right := G.isOpen_seamCollar j
  cover := G.seamSurface_compl_union_seamCollar j
  base := G.gapLevel j (-2⁻¹) ⟨by norm_num, by norm_num⟩ (by norm_num) t₀
  far := G.gapLevel j 2⁻¹ ⟨by norm_num, by norm_num⟩ (by norm_num) t₀
  not_joined := by
    rintro ⟨γ⟩
    have hc : Continuous (G.gapTime j ∘ γ) := (G.continuous_gapTime j).comp γ.continuous
    have h0 : (0 : ℝ) ∈ Set.Icc ((G.gapTime j ∘ γ) 0) ((G.gapTime j ∘ γ) 1) := by
      simp only [Function.comp_apply, Path.source, Path.target, gapTime_gapLevel]
      norm_num
    obtain ⟨s, hs⟩ := intermediate_value_univ 0 1 hc h0
    exact G.gapTime_ne_zero j (γ s) hs
  joined a := by
    rcases lt_or_gt_of_ne (G.gapTime_ne_zero j a) with ha | ha
    · refine Or.inl (G.joined_of_gapTime j le_rfl (by norm_num) (by norm_num) (by simp) _ _
        ?_ ⟨by linarith [G.abs_gapTime_lt_one j a, neg_abs_le (G.gapTime j a)], ha⟩)
      rw [G.gapTime_gapLevel]
      norm_num
    · refine Or.inr (G.joined_of_gapTime j (by norm_num) (by norm_num) le_rfl (by simp) _ _
        ?_ ⟨ha, by linarith [G.abs_gapTime_lt_one j a, le_abs_self (G.gapTime j a)]⟩)
      rw [G.gapTime_gapLevel]
      norm_num
  right_bijective := bijective_fundamentalGroup_map_of_comp _ _ t₀
    (G.bijective_gapLevel_neg j t₀) (G.bijective_collar_gapLevel j _ _ _ t₀)
  left_injective := injective_fundamentalGroup_map_of_comp _ _ t₀
    (G.bijective_gapLevel_neg j t₀).2 hl
  left_injective_far := injective_fundamentalGroup_map_of_comp _ _ t₀
    (G.bijective_gapLevel_pos j t₀).2 hr
  right_injective_far := (bijective_fundamentalGroup_map_of_comp _ _ t₀
    (G.bijective_gapLevel_pos j t₀) (G.bijective_collar_gapLevel j _ _ _ t₀)).1

def nonSeparatingVanKampen [ConnectedSpace W.Carrier] (h : ¬ G.IsSeparating j) (t₀ : Torus)
    (hl : Function.Injective (FundamentalGroup.map (G.leftEnd j) t₀))
    (hr : Function.Injective (FundamentalGroup.map (G.rightEnd j) t₀)) :
    FundamentalGroup W.Carrier (G.seam j (t₀, -2⁻¹)) ≃*
      (G.nonSeparatingCover j h t₀ hl hr).Extension :=
  (G.nonSeparatingCover j h t₀ hl hr).equivExtension

theorem nonSeparatingVanKampen_symm_of [ConnectedSpace W.Carrier] (h : ¬ G.IsSeparating j)
    (t₀ : Torus) (hl : Function.Injective (FundamentalGroup.map (G.leftEnd j) t₀))
    (hr : Function.Injective (FundamentalGroup.map (G.rightEnd j) t₀))
    (g : FundamentalGroup (↑(G.seamSurface j)ᶜ) (G.leftEnd j t₀)) :
    (G.nonSeparatingVanKampen j h t₀ hl hr).symm (HNNExtension.of g) =
      FundamentalGroup.map (subsetToAmbient (G.seamSurface j)ᶜ) (G.leftEnd j t₀) g :=
  (G.nonSeparatingCover j h t₀ hl hr).equivExtension_symm_of g

theorem injective_seamTorus_of_not_isSeparating [ConnectedSpace W.Carrier]
    (h : ¬ G.IsSeparating j) (t₀ : Torus)
    (hl : Function.Injective (FundamentalGroup.map (G.leftEnd j) t₀))
    (hr : Function.Injective (FundamentalGroup.map (G.rightEnd j) t₀)) (t : Torus) :
    Function.Injective (FundamentalGroup.map (G.seamTorus j) t) := by
  have hV : PathConnectedSpace ↑(G.seamCollar j) :=
    isPathConnected_iff_pathConnectedSpace.mp (G.isPathConnected_seamCollar j)
  have h1 : Function.Injective (FundamentalGroup.map
      ((subsetToAmbient (G.seamSurface j)ᶜ).comp (G.leftEnd j)) t₀) := by
    rw [GC.Topology.fundamentalGroup_map_comp, MonoidHom.coe_comp]
    exact (G.nonSeparatingCover j h t₀ hl hr).injective_fundamentalGroup_map_left.comp hl
  have h2 : (subsetToAmbient (G.seamSurface j)ᶜ).comp (G.leftEnd j) =
      (subsetToAmbient (G.seamCollar j)).comp
        ((interToRight (G.seamSurface j)ᶜ (G.seamCollar j)).comp
          (G.gapLevel j (-2⁻¹) ⟨by norm_num, by norm_num⟩ (by norm_num))) := rfl
  rw [h2] at h1
  have h3 := injective_fundamentalGroup_map_of_comp _ _ t₀
    (G.bijective_collar_gapLevel j _ _ _ t₀).2 h1
  have h4 := (GC.Topology.injective_fundamentalGroup_map_iff (subsetToAmbient (G.seamCollar j)) _
    (G.seamTorusIn j (G.seamCollar j) le_rfl t₀)).mp h3
  have h5 : Function.Injective (FundamentalGroup.map ((subsetToAmbient (G.seamCollar j)).comp
      (G.seamTorusIn j (G.seamCollar j) le_rfl)) t₀) := by
    rw [GC.Topology.fundamentalGroup_map_comp, MonoidHom.coe_comp]
    exact h4.comp (G.bijective_seamTorusIn j (G.seamCollar j) rfl t₀).1
  rw [GC.Topology.injective_fundamentalGroup_map_iff (G.seamTorus j) t t₀]
  exact h5

def SeamInjective (t₀ : Torus) : Prop :=
  (G.IsSeparating j ∧ Function.Injective (FundamentalGroup.map (G.seamTorusToLeft j) t₀) ∧
      Function.Injective (FundamentalGroup.map (G.seamTorusToRight j) t₀)) ∨
    (¬ G.IsSeparating j ∧ Function.Injective (FundamentalGroup.map (G.leftEnd j) t₀) ∧
      Function.Injective (FundamentalGroup.map (G.rightEnd j) t₀))

theorem injective_seamTorus_of_seamInjective [ConnectedSpace W.Carrier] (t₀ : Torus)
    (h : G.SeamInjective j t₀) (t : Torus) :
    Function.Injective (FundamentalGroup.map (G.seamTorus j) t) := by
  rcases h with ⟨hs, hl, hr⟩ | ⟨hs, hl, hr⟩
  · exact G.injective_seamTorus j hs t₀ hl hr t
  · exact G.injective_seamTorus_of_not_isSeparating j hs t₀ hl hr t

section Closed
variable {P : ConnectedClosedOrientedManifold.{u} 3} (T : TorusPresentation (NoCuts.carrier P))

theorem injective_torusInPrime_of_not_isSeparating (i : Fin T.pairing.count)
    (h : ¬ T.IsSeparating i) (t₀ : Torus)
    (hl : Function.Injective (FundamentalGroup.map (T.leftEnd i) t₀))
    (hr : Function.Injective (FundamentalGroup.map (T.rightEnd i) t₀)) (x : Torus) :
    Function.Injective (FundamentalGroup.map
      (T.toTorusDecomposition.reconstructionAtlas.torusInPrime
        T.toTorusDecomposition.reconstruction i) x) := by
  rw [T.toTorusDecomposition_torusInPrime_eq i]
  exact T.injective_seamTorus_of_not_isSeparating i h t₀ hl hr x

theorem incompressible_toTorusDecomposition_of_seamInjective
    (h : ∀ i, T.SeamInjective i (1, 1)) :
    T.toTorusDecomposition.reconstructionAtlas.Incompressible
      T.toTorusDecomposition.reconstruction := by
  intro i x
  rw [T.toTorusDecomposition_torusInPrime_eq i]
  exact T.injective_seamTorus_of_seamInjective i (1, 1) (h i) x

end Closed

end TorusPresentation

end GC.Seifert
