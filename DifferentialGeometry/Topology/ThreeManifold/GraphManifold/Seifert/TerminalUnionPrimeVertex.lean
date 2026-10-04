import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TerminalUnionPrimeRegions
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.TwoFillingDetection
import DifferentialGeometry.Topology.FundamentalGroup.CircleDegree

/-!
# Vertex groups of good blocks

Chapter 5 plan P4, the vertex condition of T2 for good Seifert blocks with a free port.

Loops of a self-homotopy. For a homotopy `H` from the identity of `X` to itself, the trajectory
loop `turnLoop H x` commutes with every loop at `x` (`commute_turnLoop`, from
`Path.Homotopic.map_trans_evalAt`), and the trajectories at two points are conjugate along any
path, also after pushing forward (`turnLoop_naturality`). Hence an element conjugate to it is
central, resp. trivial, as soon as it is (`commute_iff_of_conj`, `eq_one_of_conj`).

Fibre loops. On a product-fibred piece the fibre rotation `ProductFibredPiece.turn` (rotating the
circle factor of the trivialization once) is such a homotopy. On a port it rotates the second
torus coordinate (`turn_portMap`), whose loop `torusTurnLoop` is nontrivial in π₁ of the torus
(`torusTurnLoop_ne_one`, through the generator of π₁ of the unit circle).

Blocks. `SeifertBlock.fibreClass p` is the fibre loop at a point `p` of the product piece, pushed
into the block. On a free port it is nontrivial when the block is good
(`fibreClass_freePort_ne_one`), and the free port makes π₁ non-cyclic. It is central: without
fillings the product piece is the whole block; with one filling by van Kampen along the filling
seam (`commute_of_openCover`), the solid-torus region having cyclic π₁ and the product region
being π₁-isomorphic to the product piece (K10b's region retractions). A central nontrivial fibre
makes π₁ freely indecomposable (`indecomposableNoncyclic_of_commute`).
-/

set_option autoImplicit false

noncomputable section
open CategoryTheory DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold DifferentialGeometry.Topology.VanKampen
open scoped Topology ContinuousMap unitInterval

universe u

namespace GC.Seifert

section Turn
variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def turnLoop (H : (ContinuousMap.id X).Homotopy (ContinuousMap.id X)) (x : X) :
    FundamentalGroup X x :=
  FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (H.evalAt x))

theorem map_id_path {x y : X} (p : Path x y) :
    p.map (ContinuousMap.id X).continuous = p := by
  ext t
  rfl

theorem commute_turnLoop (H : (ContinuousMap.id X).Homotopy (ContinuousMap.id X)) (x : X)
    (g : FundamentalGroup X x) : g * turnLoop H x = turnLoop H x * g := by
  induction g using Path.Homotopic.Quotient.ind with
  | mk p =>
    let ℓ : Path x x := H.evalAt x
    have h : (p.trans ℓ).Homotopic (ℓ.trans p) := by
      have h' := Path.Homotopic.map_trans_evalAt H p
      rw [map_id_path] at h'
      exact h'
    change Path.Homotopic.Quotient.mk (ℓ.trans p) = Path.Homotopic.Quotient.mk (p.trans ℓ)
    exact Path.Homotopic.Quotient.eq.mpr h.symm

theorem turnLoop_naturality (H : (ContinuousMap.id X).Homotopy (ContinuousMap.id X))
    (f : C(X, Y)) {x y : X} (γ : Path x y) :
    Path.Homotopic.Quotient.trans (Path.Homotopic.Quotient.mk (γ.map f.continuous))
        (FundamentalGroup.map f y (turnLoop H y)) =
      Path.Homotopic.Quotient.trans (FundamentalGroup.map f x (turnLoop H x))
        (Path.Homotopic.Quotient.mk (γ.map f.continuous)) := by
  let ℓx : Path x x := H.evalAt x
  let ℓy : Path y y := H.evalAt y
  have h : (γ.trans ℓy).Homotopic (ℓx.trans γ) := by
    have h' := Path.Homotopic.map_trans_evalAt H γ
    rw [map_id_path] at h'
    exact h'
  change Path.Homotopic.Quotient.mk ((γ.map f.continuous).trans (ℓy.map f.continuous)) =
    Path.Homotopic.Quotient.mk ((ℓx.map f.continuous).trans (γ.map f.continuous))
  rw [← Path.map_trans, ← Path.map_trans]
  exact Path.Homotopic.Quotient.eq.mpr (h.map f)

end Turn

section Conj
variable {X : Type*} [TopologicalSpace X] {a b : X}

theorem commute_iff_of_conj (γ : Path.Homotopic.Quotient a b) (za : FundamentalGroup X a)
    (zb : FundamentalGroup X b)
    (h : Path.Homotopic.Quotient.trans γ zb = Path.Homotopic.Quotient.trans za γ) :
    (∀ g : FundamentalGroup X a, g * za = za * g) →
      ∀ g : FundamentalGroup X b, g * zb = zb * g := by
  intro hza g
  let γ' : FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b := γ
  let za' : FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk a := za
  let zb' : FundamentalGroupoid.mk b ⟶ FundamentalGroupoid.mk b := zb
  let g' : FundamentalGroupoid.mk b ⟶ FundamentalGroupoid.mk b := g
  have h' : γ' ≫ zb' = za' ≫ γ' := h
  have hz : zb' = Groupoid.inv γ' ≫ za' ≫ γ' := by
    rw [← h', ← Category.assoc, Groupoid.inv_comp, Category.id_comp]
  have hc := hza (γ' ≫ g' ≫ Groupoid.inv γ')
  change za' ≫ γ' ≫ g' ≫ Groupoid.inv γ' = (γ' ≫ g' ≫ Groupoid.inv γ') ≫ za' at hc
  change zb' ≫ g' = g' ≫ zb'
  rw [hz]
  calc (Groupoid.inv γ' ≫ za' ≫ γ') ≫ g'
      = Groupoid.inv γ' ≫ (za' ≫ γ' ≫ g' ≫ Groupoid.inv γ') ≫ γ' := by
        simp only [Category.assoc, Groupoid.inv_comp, Category.comp_id]
    _ = Groupoid.inv γ' ≫ ((γ' ≫ g' ≫ Groupoid.inv γ') ≫ za') ≫ γ' := by rw [hc]
    _ = g' ≫ Groupoid.inv γ' ≫ za' ≫ γ' := by
        simp only [Category.assoc]
        rw [← Category.assoc (Groupoid.inv γ'), Groupoid.inv_comp, Category.id_comp]

theorem eq_one_of_conj (γ : Path.Homotopic.Quotient a b) (za : FundamentalGroup X a)
    (zb : FundamentalGroup X b)
    (h : Path.Homotopic.Quotient.trans γ zb = Path.Homotopic.Quotient.trans za γ)
    (hb : zb = 1) : za = 1 := by
  let γ' : FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b := γ
  let za' : FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk a := za
  let zb' : FundamentalGroupoid.mk b ⟶ FundamentalGroupoid.mk b := zb
  have h' : γ' ≫ zb' = za' ≫ γ' := h
  have hb' : zb' = 𝟙 _ := hb
  rw [hb', Category.comp_id] at h'
  change za' = 𝟙 _
  have := congrArg (fun q => q ≫ Groupoid.inv γ') h'
  simp only [Groupoid.comp_inv, Category.assoc, Category.comp_id] at this
  exact this.symm

end Conj

section Circle

def circleTurn (θ : I) : Circle := AddCircle.toCircle (((θ : ℝ) : UnitAddCircle))

theorem continuous_circleTurn : Continuous circleTurn :=
  AddCircle.continuous_toCircle.comp ((AddCircle.continuous_mk' (1 : ℝ)).comp
    continuous_subtype_val)

theorem circleTurn_zero : circleTurn 0 = 1 := by
  simp [circleTurn]

theorem circleTurn_one : circleTurn 1 = 1 := by
  simp only [circleTurn, Set.Icc.coe_one]
  rw [AddCircle.coe_period, AddCircle.toCircle_zero]

def circleTurnLoop (u : Circle) : Path u u where
  toFun θ := circleTurn θ * u
  continuous_toFun := continuous_circleTurn.mul continuous_const
  source' := by simp [circleTurn_zero]
  target' := by simp [circleTurn_one]

def torusTurnLoop (t : Torus) : Path t t where
  toFun θ := (t.1, circleTurn θ * t.2)
  continuous_toFun := continuous_const.prodMk (continuous_circleTurn.mul continuous_const)
  source' := by simp [circleTurn_zero]
  target' := by simp [circleTurn_one]

theorem circleTurnLoop_ne_one (u : Circle) :
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (circleTurnLoop u)) :
      FundamentalGroup Circle u) ≠ 1 := by
  let e : UnitAddCircle ≃ₜ Circle :=
    (AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0)).trans (Homeomorph.mulRight u)
  have he : e.symm u = 0 := by
    rw [Homeomorph.symm_apply_eq]
    change u = AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0) 0 * u
    rw [AddCircle.homeomorphCircle_apply, AddCircle.toCircle_zero, one_mul]
  have hgen : FundamentalGroup.mapOfEq (e.symm : C(Circle, UnitAddCircle)) he
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (circleTurnLoop u))) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk circleGeneratorPath) := by
    rw [FundamentalGroup.mapOfEq_apply]
    change Path.Homotopic.Quotient.mk
      (((circleTurnLoop u).map (e.symm : C(Circle, UnitAddCircle)).continuous).cast
        he.symm he.symm) = _
    congr 1
    ext θ
    change e.symm (circleTurn θ * u) = ((θ : ℝ) : UnitAddCircle)
    rw [Homeomorph.symm_apply_eq]
    change circleTurn θ * u =
      AddCircle.homeomorphCircle (one_ne_zero : (1 : ℝ) ≠ 0) ((θ : ℝ) : UnitAddCircle) * u
    rw [AddCircle.homeomorphCircle_apply]
    rfl
  intro h1
  have h2 := congrArg (FundamentalGroup.mapOfEq (e.symm : C(Circle, UnitAddCircle)) he) h1
  rw [hgen, map_one] at h2
  have h3 := congrArg fundamentalGroupUnitAddCircleEquivInt h2
  rw [fundamentalGroupUnitAddCircleEquivInt_generator,
    map_one fundamentalGroupUnitAddCircleEquivInt] at h3
  have h4 : (1 : ℤ) = 0 := congrArg Multiplicative.toAdd h3
  exact one_ne_zero h4

theorem torusTurnLoop_ne_one (t : Torus) :
    (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (torusTurnLoop t)) :
      FundamentalGroup Torus t) ≠ 1 := by
  intro h
  have h2 := congrArg (FundamentalGroup.map (ContinuousMap.snd : C(Torus, Circle)) t) h
  rw [map_one] at h2
  apply circleTurnLoop_ne_one t.2
  have he : (torusTurnLoop t).map (ContinuousMap.snd : C(Torus, Circle)).continuous =
      circleTurnLoop t.2 := by
    ext θ
    rfl
  rw [← he]
  exact h2

end Circle

section Cover
variable {X : Type u} [TopologicalSpace X]

theorem mapOfEq_rfl' {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z] (f : C(Y, Z))
    (y : Y) : FundamentalGroup.mapOfEq f (rfl : f y = f y) = FundamentalGroup.map f y := by
  ext p
  rw [FundamentalGroup.mapOfEq_apply]
  exact Path.Homotopic.Quotient.cast_rfl_rfl _

theorem commute_of_openCover (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcov : U ∪ V = Set.univ) (x : ↑(U ∩ V)) [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace ↑(U ∩ V)] (c : FundamentalGroup ↑(U ∩ V) x)
    (hcU : ∀ a : FundamentalGroup U (interToLeft U V x),
      a * FundamentalGroup.map (interToLeft U V) x c =
        FundamentalGroup.map (interToLeft U V) x c * a)
    (hcV : ∀ b : FundamentalGroup V (interToRight U V x),
      b * FundamentalGroup.map (interToRight U V) x c =
        FundamentalGroup.map (interToRight U V) x c * b)
    (g : FundamentalGroup X (subsetToAmbient (U ∩ V) x)) :
    g * FundamentalGroup.map (subsetToAmbient (U ∩ V)) x c =
      FundamentalGroup.map (subsetToAmbient (U ∩ V)) x c * g := by
  let e := fundamentalGroupEquivAmalgamatedProduct U V hU hV hcov x.1 x.2
  let φ := fundamentalGroupAmalgamation U V x.1 x.2
  have hb : FundamentalGroup.map (subsetToAmbient (U ∩ V)) x c =
      e (Monoid.PushoutI.base φ c) :=
    (fundamentalGroupEquivAmalgamatedProduct_base U V hU hV hcov x c).symm
  have hφ0 : φ false c = FundamentalGroup.map (interToLeft U V) x c := by
    change FundamentalGroup.mapOfEq (interToLeft U V)
      (rfl : interToLeft U V x = interToLeft U V x) c = _
    rw [mapOfEq_rfl']
  have hφ1 : φ true c = FundamentalGroup.map (interToRight U V) x c := by
    change FundamentalGroup.mapOfEq (interToRight U V)
      (rfl : interToRight U V x = interToRight U V x) c = _
    rw [mapOfEq_rfl']
  have hof : ∀ i a, Monoid.PushoutI.of (φ := φ) i a * Monoid.PushoutI.base φ c =
      Monoid.PushoutI.base φ c * Monoid.PushoutI.of (φ := φ) i a := by
    intro i a
    rw [← Monoid.PushoutI.of_apply_eq_base φ i c, ← map_mul, ← map_mul]
    congr 1
    cases i
    · rw [hφ0]
      exact hcU a
    · rw [hφ1]
      exact hcV a
  obtain ⟨w, rfl⟩ := e.surjective g
  rw [hb]
  change (e w * e (Monoid.PushoutI.base φ c) : FundamentalGroup X x.1) =
    e (Monoid.PushoutI.base φ c) * e w
  rw [← map_mul, ← map_mul]
  congr 1
  induction w using Monoid.PushoutI.induction_on with
  | of i a => exact hof i a
  | base c' =>
    rw [← Monoid.PushoutI.of_apply_eq_base φ false c']
    exact hof _ _
  | mul a b ha hb' => rw [mul_assoc, hb', ← mul_assoc, ha, mul_assoc]

theorem commute_map_of_surjective {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) (y : Y) (hs : Function.Surjective (FundamentalGroup.map f y))
    (z : FundamentalGroup Y y) (hz : ∀ g, g * z = z * g)
    (g : FundamentalGroup Z (f y)) :
    g * FundamentalGroup.map f y z = FundamentalGroup.map f y z * g := by
  obtain ⟨a, rfl⟩ := hs g
  rw [← map_mul, ← map_mul, hz]

theorem commute_of_injective_isCyclic {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) [IsCyclic H] (a b : G) : a * b = b * a := by
  apply hf
  rw [map_mul, map_mul]
  exact IsCyclic.commGroup.mul_comm _ _

end Cover

namespace ProductFibredPiece

variable {W : CompactCarrier.{u}} {T : TorusPresentation.{u} W} {i : Fin T.components.count}
  {k : ℕ}

def turn (P : ProductFibredPiece T i k) :
    (ContinuousMap.id (T.components.piece i)).Homotopy
      (ContinuousMap.id (T.components.piece i)) where
  toFun q := P.trivialization ((P.trivialization.symm q.2).1,
    circleTurn q.1 * (P.trivialization.symm q.2).2)
  continuous_toFun := P.trivialization.continuous.comp
    ((continuous_fst.comp (P.trivialization.symm.continuous.comp continuous_snd)).prodMk
      ((continuous_circleTurn.comp continuous_fst).mul
        (continuous_snd.comp (P.trivialization.symm.continuous.comp continuous_snd))))
  map_zero_left q := by
    change P.trivialization ((P.trivialization.symm q).1,
      circleTurn 0 * (P.trivialization.symm q).2) = q
    rw [circleTurn_zero, one_mul, Prod.mk.eta, Diffeomorph.apply_symm_apply]
  map_one_left q := by
    change P.trivialization ((P.trivialization.symm q).1,
      circleTurn 1 * (P.trivialization.symm q).2) = q
    rw [circleTurn_one, one_mul, Prod.mk.eta, Diffeomorph.apply_symm_apply]

theorem turn_portMap (P : ProductFibredPiece T i k) (j : Fin k) (θ : I) (x : Torus) :
    P.turn (θ, P.portMap j x) = P.portMap j (torusTurnLoop x θ) := by
  change P.trivialization ((P.trivialization.symm (P.portMap j x)).1,
    circleTurn θ * (P.trivialization.symm (P.portMap j x)).2) = _
  rw [P.portMap_apply, Diffeomorph.symm_apply_apply, P.portMap_apply]
  rfl

theorem turnLoop_portMap (P : ProductFibredPiece T i k) (j : Fin k) (x : Torus) :
    turnLoop P.turn (P.portMap j x) = FundamentalGroup.map (P.portMap j) x
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (torusTurnLoop x))) := by
  change Path.Homotopic.Quotient.mk (P.turn.evalAt (P.portMap j x)) =
    Path.Homotopic.Quotient.mk ((torusTurnLoop x).map (P.portMap j).continuous)
  congr 1
  ext θ
  exact congrArg Subtype.val (P.turn_portMap j θ x)

end ProductFibredPiece

namespace SeifertBlock

variable {W : CompactCarrier.{u}} {d : SeifertData} (B : SeifertBlock W d)

def fibreClass (p : B.presentation.components.piece (B.piece none)) :
    FundamentalGroup W.Carrier (B.productToCarrier p) :=
  FundamentalGroup.map B.productToCarrier p (turnLoop B.product.turn p)

theorem fibreClass_commute_transfer (p q : B.presentation.components.piece (B.piece none))
    (h : ∀ g : FundamentalGroup W.Carrier (B.productToCarrier p),
      g * B.fibreClass p = B.fibreClass p * g) :
    ∀ g : FundamentalGroup W.Carrier (B.productToCarrier q),
      g * B.fibreClass q = B.fibreClass q * g := by
  have := B.presentation.pathConnectedSpace_piece (B.piece none)
  exact commute_iff_of_conj _ _ _
    (turnLoop_naturality B.product.turn B.productToCarrier (PathConnectedSpace.somePath p q)) h

theorem fibreClass_ne_one_transfer (p q : B.presentation.components.piece (B.piece none))
    (h : B.fibreClass q ≠ 1) : B.fibreClass p ≠ 1 := by
  have := B.presentation.pathConnectedSpace_piece (B.piece none)
  exact fun hp => h (eq_one_of_conj _ _ _
    (turnLoop_naturality B.product.turn B.productToCarrier (PathConnectedSpace.somePath q p)) hp)

theorem injective_freePort (hB : B.IsGoodBlock) (r : Fin d.ports) (x : Torus) :
    Function.Injective ((FundamentalGroup.map B.productToCarrier
      (B.product.portMap (B.port (.inl r)) x)).comp
        (FundamentalGroup.map (B.product.portMap (B.port (.inl r))) x)) := by
  have hinj := (B.isGoodBlock_iff.mp hB) r x
  rw [B.external_boundaryMap_free r, GC.Topology.fundamentalGroup_map_comp] at hinj
  exact hinj

theorem fibreClass_freePort_ne_one (hB : B.IsGoodBlock) (r : Fin d.ports) (x : Torus) :
    B.fibreClass (B.product.portMap (B.port (.inl r)) x) ≠ 1 := by
  intro h
  apply torusTurnLoop_ne_one x
  apply B.injective_freePort hB r x
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← ProductFibredPiece.turnLoop_portMap,
    map_one, map_one]
  exact h

theorem fibreClass_commute_of_fillingCount_eq_zero (h0 : d.fillingCount = 0)
    (p : B.presentation.components.piece (B.piece none))
    (g : FundamentalGroup W.Carrier (B.productToCarrier p)) :
    g * B.fibreClass p = B.fibreClass p * g := by
  have : CompactSpace (B.presentation.components.piece (B.piece none)) :=
    isCompact_iff_compactSpace.mp (B.presentation.components.piece_compact _)
  let e := B.productToCarrier.continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective _
      ⟨B.productToCarrier_injective h0, B.productToCarrier_surjective h0⟩)
  exact commute_map_of_surjective _ p (bijective_map_homeomorph e p).2 _
    (commute_turnLoop _ p) g

theorem exists_fibreClass_commute_of_fillingCount_eq_one (h1 : d.fillingCount = 1) :
    ∃ p, ∀ g : FundamentalGroup W.Carrier (B.productToCarrier p),
      g * B.fibreClass p = B.fibreClass p * g := by
  have hW := B.connectedSpace
  let m0 : Fin d.fillingCount := ⟨0, by omega⟩
  have hc : B.presentation.pairing.count = 1 := B.pairing_count.trans h1
  have hLR := B.leftPiece_ne_rightPiece (B.seam m0)
  have hsep := B.isSeparating_seam m0
  set G := B.presentation with hG
  set j := B.seam m0 with hj
  let t₀ : Torus := (1, 1)
  let p₀ := B.product.portMap (B.port (.inr m0)) (G.pairing.matching j t₀)
  refine ⟨p₀, ?_⟩
  have hval : ∀ w : Torus, B.productToCarrier (B.product.portMap (B.port (.inr m0)) w) =
      G.seamTorus j ((G.pairing.matching j).symm w) := by
    intro w
    rw [G.seamTorus_eq_cutMap_right, Diffeomorph.apply_symm_apply]
    change G.cutMap (B.product.portMap (B.port (.inr m0)) w : G.cutCarrier.Carrier) = _
    rw [B.portMap_filled_val]
  have hmem : ∀ θ : I, B.productToCarrier (B.product.turn (θ, p₀)) ∈
      G.leftRegion j ∩ G.rightRegion j := by
    intro θ
    rw [B.product.turn_portMap, hval]
    exact G.seamTorus_mem_inter j _
  have hx : B.productToCarrier p₀ ∈ G.leftRegion j ∩ G.rightRegion j := by
    rw [hval]
    exact G.seamTorus_mem_inter j _
  let x : ↑(G.leftRegion j ∩ G.rightRegion j) := ⟨B.productToCarrier p₀, hx⟩
  let γ : Path x x :=
    { toFun := fun θ => ⟨B.productToCarrier (B.product.turn (θ, p₀)), hmem θ⟩
      continuous_toFun := ((B.productToCarrier.continuous.comp B.product.turn.continuous).comp
        (continuous_id.prodMk continuous_const)).subtype_mk _
      source' := Subtype.ext (congrArg B.productToCarrier (B.product.turn.apply_zero p₀))
      target' := Subtype.ext (congrArg B.productToCarrier (B.product.turn.apply_one p₀)) }
  let c : FundamentalGroup ↑(G.leftRegion j ∩ G.rightRegion j) x :=
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ)
  have hcW : FundamentalGroup.map (subsetToAmbient _) x c = B.fibreClass p₀ := by
    change Path.Homotopic.Quotient.mk (γ.map (subsetToAmbient _).continuous) =
      Path.Homotopic.Quotient.mk ((B.product.turn.evalAt p₀).map B.productToCarrier.continuous)
    congr 1
  have hr : G.rightPiece j = B.piece none := B.rightPiece_seam m0
  have hfR := G.exists_rightRegionRetraction j hc hLR
  have hPR := G.pieceImage_right_subset_rightRegion j hc hLR
  rw [hr] at hfR hPR
  obtain ⟨fR, hfRb, hfRx⟩ := hfR
  let incl : C(G.components.piece (B.piece none), G.rightRegion j) :=
    ⟨fun q => ⟨B.productToCarrier q, hPR ⟨q.1, q.2, rfl⟩⟩,
      B.productToCarrier.continuous.subtype_mk _⟩
  have hcomp : fR.comp incl = ContinuousMap.id _ := ContinuousMap.ext fun q => hfRx q _
  have hid : Function.Bijective (FundamentalGroup.map (fR.comp incl) p₀) := by
    rw [hcomp]
    exact bijective_map_homeomorph (Homeomorph.refl _) p₀
  rw [GC.Topology.fundamentalGroup_map_comp, MonoidHom.coe_comp] at hid
  have hincl : Function.Bijective (FundamentalGroup.map incl p₀) :=
    (Function.Bijective.of_comp_iff' (hfRb _) _).mp hid
  have hl : G.leftPiece j = B.piece (some m0) := B.leftPiece_seam m0
  have hfL := G.exists_leftRegionRetraction j hc hLR
  rw [hl] at hfL
  obtain ⟨fL, hfLb, -⟩ := hfL
  have := isPathConnected_iff_pathConnectedSpace.mp (G.isPathConnected_leftRegion j)
  have := isPathConnected_iff_pathConnectedSpace.mp (G.isPathConnected_rightRegion j)
  have := G.pathConnectedSpace_inter j hsep
  have hcU : ∀ a : FundamentalGroup (G.leftRegion j) (interToLeft _ _ x),
      a * FundamentalGroup.map (interToLeft _ _) x c =
        FundamentalGroup.map (interToLeft _ _) x c * a := by
    have := (B.solid m0).isCyclic_fundamentalGroup (fL (interToLeft _ _ x))
    exact fun a => commute_of_injective_isCyclic (FundamentalGroup.map fL _) (hfLb _).1 _ _
  have hcR : FundamentalGroup.map (interToRight (G.leftRegion j) (G.rightRegion j)) x c =
      FundamentalGroup.map incl p₀ (turnLoop B.product.turn p₀) := by
    change Path.Homotopic.Quotient.mk (γ.map (interToRight _ _).continuous) =
      Path.Homotopic.Quotient.mk ((B.product.turn.evalAt p₀).map incl.continuous)
    congr 1
  have hcV : ∀ b : FundamentalGroup (G.rightRegion j) (interToRight _ _ x),
      b * FundamentalGroup.map (interToRight _ _) x c =
        FundamentalGroup.map (interToRight _ _) x c * b := by
    intro b
    rw [hcR]
    exact commute_map_of_surjective incl p₀ hincl.2 _ (commute_turnLoop _ p₀) b
  intro g
  have key := commute_of_openCover (G.leftRegion j) (G.rightRegion j) (G.isOpen_leftRegion j)
    (G.isOpen_rightRegion j) (G.leftRegion_union_rightRegion j) x c hcU hcV g
  rw [hcW] at key
  exact key

theorem exists_fibreClass_commute_of_fillingCount_le_one (h : d.fillingCount ≤ 1) :
    ∃ p, ∀ g : FundamentalGroup W.Carrier (B.productToCarrier p),
      g * B.fibreClass p = B.fibreClass p * g := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp h with h0 | h1
  · have := B.presentation.pathConnectedSpace_piece (B.piece none)
    obtain ⟨p⟩ := (inferInstance : Nonempty (B.presentation.components.piece (B.piece none)))
    exact ⟨p, B.fibreClass_commute_of_fillingCount_eq_zero h0 p⟩
  · exact B.exists_fibreClass_commute_of_fillingCount_eq_one h1

theorem indecomposableNoncyclic_of_commute (hB : B.IsGoodBlock) (hp : d.ports ≠ 0)
    (hcen : ∃ p, ∀ g : FundamentalGroup W.Carrier (B.productToCarrier p),
      g * B.fibreClass p = B.fibreClass p * g)
    (x : W.Carrier) : IndecomposableNoncyclic (FundamentalGroup W.Carrier x) := by
  obtain ⟨p, hp'⟩ := hcen
  let r : Fin d.ports := ⟨0, Nat.pos_of_ne_zero hp⟩
  let q := B.product.portMap (B.port (.inl r)) (1, 1)
  have hq := B.fibreClass_commute_transfer p q hp'
  have hz := B.fibreClass_freePort_ne_one hB r (1, 1)
  have hnc : ¬ IsCyclic (FundamentalGroup W.Carrier (B.productToCarrier q)) :=
    not_isCyclic_of_injective _ (B.injective_freePort hB r (1, 1))
      (indecomposableNoncyclic_torus _).2
  have hq' : IndecomposableNoncyclic (FundamentalGroup W.Carrier (B.productToCarrier q)) :=
    ⟨GC.Group.freelyIndecomposable_of_center_nontrivial _ _ hz hq, hnc⟩
  have := B.connectedSpace
  have := Manifold.locallyPathConnectedSpace_of_modelWithCorners (M := W.Carrier) W.model
  have : PathConnectedSpace W.Carrier := PathConnectedSpace.of_locallyPathConnectedSpace
  exact hq'.of_mulEquiv (FundamentalGroup.fundamentalGroupMulEquivOfPathConnected _ x)

end SeifertBlock

end GC.Seifert
