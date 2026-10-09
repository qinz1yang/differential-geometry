import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTerminalFinitePants
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTerminalFiniteRelations

/-!
# Transport from the compact pants to the original product host

The actual planar embedding identifies every pants base with the compact planar model,
including its original boundary maps. Product trivializations then transport the boundary
and fibre generators into the original host piece and its actual filling quotient.
-/

set_option autoImplicit false
noncomputable section
open Multiplicative
open Set DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Topology ContinuousMap unitInterval
universe u
namespace GC.Seifert
section GroupGeneration
variable {G H : Type*} [Group G] [Group H]

theorem closure_image_eq_top_of_surjective (f : G →* H) (hf : Function.Surjective f)
    (s : Set G) (hs : Subgroup.closure s = ⊤) : Subgroup.closure (f '' s) = ⊤ := by
  rw [← MonoidHom.map_closure, hs, Subgroup.map_top_of_surjective f hf]

theorem closure_product_circle_generators (x : Fin 3 → G) (z : H)
    (hx : Subgroup.closure (Set.range x) = ⊤) (hz : ∀ a : H, ∃ n : ℤ, z ^ n = a) :
    Subgroup.closure (Set.range (fun j => (x j, (1 : H))) ∪ {(1, z)}) = ⊤ := by
  let K := Subgroup.closure (Set.range (fun j => (x j, (1 : H))) ∪ {(1, z)})
  apply (Subgroup.eq_top_iff' _).mpr
  intro a
  have hle : Subgroup.closure (Set.range x) ≤ K.comap (MonoidHom.inl G H) := by
    apply (Subgroup.closure_le _).mpr
    rintro b ⟨j, rfl⟩
    exact Subgroup.subset_closure (Or.inl ⟨j, rfl⟩)
  have hl : (a.1, (1 : H)) ∈ K := hle (hx.symm ▸ Subgroup.mem_top a.1)
  obtain ⟨n, hn⟩ := hz a.2
  have hr : ((1 : G), a.2) ∈ K := by
    have h := K.zpow_mem (Subgroup.subset_closure (Or.inr rfl)) n
    change ((1 : G) ^ n, z ^ n) ∈ K at h
    simpa only [one_zpow, hn] using h
  have h := K.mul_mem hl hr
  simpa only [Prod.mk_mul_mk, mul_one, one_mul, Prod.mk.eta] using h

end GroupGeneration

theorem torusSection_circleLoop :
    torusCoordinates.symm (Multiplicative.ofAdd ![1, 0]) =
      FundamentalGroup.map circleInc 1 (FundamentalGroup.fromPath ⟦circleLoop⟧) := by
  apply torusCoordinates.injective
  apply Multiplicative.toAdd.injective
  rw [MulEquiv.apply_symm_apply, toAdd_ofAdd, toAdd_torusCoordinates_circleInc,
    circleInt_circleLoop, toAdd_ofAdd]

namespace ProductFibredPiece
variable {W : CompactCarrier.{u}} {T : TorusPresentation.{u} W}
  {i : Fin T.components.count} {k : ℕ} (P : ProductFibredPiece T i k)

def closedTriangleBaseSlice : C(P.base.surface.Carrier, T.components.piece i) :=
  P.trivializationMap.comp ((ContinuousMap.id _).prodMk (ContinuousMap.const _ (1 : Circle)))

theorem closedTriangleBaseSlice_boundary (j : Fin k) :
    P.closedTriangleBaseSlice.comp (P.base.boundaryCircle j) = (P.portMap j).comp circleInc :=
  ContinuousMap.ext fun t => Eq.refl (P.portMap j (circleInc t))

theorem fundamentalGroupEquiv_map_trivialization (b : P.base.surface.Carrier)
    (v : Circle) (a : FundamentalGroup (P.base.surface.Carrier × Circle) (b, v)) :
    P.fundamentalGroupEquiv b v (FundamentalGroup.map P.trivializationMap (b, v) a) =
      fundamentalGroupProdEquiv b v a := by
  change fundamentalGroupProdEquiv b v
    ((MulEquiv.ofBijective _ (P.bijective_map_trivializationMap (b, v))).symm
      ((MulEquiv.ofBijective _ (P.bijective_map_trivializationMap (b, v))) a)) = _
  rw [MulEquiv.symm_apply_apply]

set_option backward.isDefEq.respectTransparency false in
theorem fundamentalGroupEquiv_baseSlice (b : P.base.surface.Carrier)
    (a : FundamentalGroup P.base.surface.Carrier b) :
    P.fundamentalGroupEquiv b 1 (FundamentalGroup.map P.closedTriangleBaseSlice b a) =
      (a, 1) := by
  let f := (ContinuousMap.id P.base.surface.Carrier).prodMk
    (ContinuousMap.const P.base.surface.Carrier (1 : Circle))
  have hmap : FundamentalGroup.map P.closedTriangleBaseSlice b a =
      FundamentalGroup.map P.trivializationMap (b, 1) (FundamentalGroup.map f b a) :=
    DFunLike.congr_fun (GC.Topology.fundamentalGroup_map_comp f P.trivializationMap b) a
  rw [hmap, P.fundamentalGroupEquiv_map_trivialization]
  apply Prod.ext
  · induction a using Path.Homotopic.Quotient.ind with
    | mk α => rfl
  · change FundamentalGroup.map ContinuousMap.snd (b, (1 : Circle))
      (FundamentalGroup.map ((ContinuousMap.id _).prodMk
        (ContinuousMap.const _ (1 : Circle))) b a) = 1
    have hconst : FundamentalGroup.map ContinuousMap.snd (b, (1 : Circle))
        (FundamentalGroup.map f b a) =
          FundamentalGroup.map (ContinuousMap.const _ (1 : Circle)) b a :=
      (DFunLike.congr_fun (GC.Topology.fundamentalGroup_map_comp f ContinuousMap.snd b) a).symm
    exact hconst.trans (fundamentalGroup_map_const (1 : Circle) b a)

def closedTriangleFibreSlice (b : P.base.surface.Carrier) :
    C(Circle, T.components.piece i) :=
  P.trivializationMap.comp ((ContinuousMap.const _ b).prodMk (ContinuousMap.id _))

theorem closedTriangleFibreSlice_turnLoop (b : P.base.surface.Carrier) :
    FundamentalGroup.map (P.closedTriangleFibreSlice b) 1
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (circleTurnLoop 1))) =
        turnLoop P.turn (P.closedTriangleBaseSlice b) := by
  have hpoint : ∀ θ : I, P.closedTriangleFibreSlice b (circleTurnLoop 1 θ) =
      P.turn (θ, P.closedTriangleBaseSlice b) := by
    intro θ
    change P.trivialization (b, circleTurn θ * 1) =
      P.trivialization ((P.trivialization.symm (P.trivialization (b, 1))).1,
        circleTurn θ * (P.trivialization.symm (P.trivialization (b, 1))).2)
    rw [Diffeomorph.symm_apply_apply]
  change Path.Homotopic.Quotient.mk
    ((circleTurnLoop 1).map (P.closedTriangleFibreSlice b).continuous) =
      Path.Homotopic.Quotient.mk (P.turn.evalAt (P.closedTriangleBaseSlice b))
  apply congrArg Path.Homotopic.Quotient.mk
  exact Path.ext (funext hpoint)

set_option backward.isDefEq.respectTransparency false in
theorem fundamentalGroupEquiv_turnLoop (b : P.base.surface.Carrier) :
    P.fundamentalGroupEquiv b 1 (turnLoop P.turn (P.closedTriangleBaseSlice b)) =
      (1, FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (circleTurnLoop 1))) := by
  let f := (ContinuousMap.const Circle b).prodMk (ContinuousMap.id Circle)
  let a : FundamentalGroup Circle 1 :=
    FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (circleTurnLoop 1))
  have hmap : FundamentalGroup.map (P.closedTriangleFibreSlice b) 1 a =
      FundamentalGroup.map P.trivializationMap (b, 1) (FundamentalGroup.map f 1 a) :=
    DFunLike.congr_fun (GC.Topology.fundamentalGroup_map_comp f P.trivializationMap 1) a
  rw [← P.closedTriangleFibreSlice_turnLoop, hmap, P.fundamentalGroupEquiv_map_trivialization]
  apply Prod.ext
  · change FundamentalGroup.map ContinuousMap.fst (b, (1 : Circle))
      (FundamentalGroup.map ((ContinuousMap.const _ b).prodMk
        (ContinuousMap.id _)) 1
          (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (circleTurnLoop 1)))) = 1
    exact fundamentalGroup_map_const b 1
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (circleTurnLoop 1)))
  · rfl

theorem circleTurnLoop_generates (a : FundamentalGroup Circle 1) :
    ∃ n : ℤ,
      (FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (circleTurnLoop 1))) ^ n = a := by
  refine ⟨toAdd (fundamentalGroupCircleEquivInt a), ?_⟩
  apply fundamentalGroupCircleEquivInt.injective
  apply toAdd.injective
  rw [map_zpow, circleTurnLoop_degree_one, toAdd_zpow, toAdd_ofAdd]
  simp

set_option backward.isDefEq.respectTransparency false in
theorem closure_baseSlice_turnLoop (b : P.base.surface.Carrier)
    (x : Fin 3 → FundamentalGroup P.base.surface.Carrier b)
    (hx : Subgroup.closure (Set.range x) = ⊤) :
    Subgroup.closure (Set.range (fun j => FundamentalGroup.map P.closedTriangleBaseSlice b (x j)) ∪
      {turnLoop P.turn (P.closedTriangleBaseSlice b)}) = ⊤ := by
  let E := P.fundamentalGroupEquiv b 1
  apply Subgroup.map_injective (f := E.toMonoidHom) E.injective
  rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective E.toMonoidHom E.surjective]
  rw [Set.image_union, ← Set.range_comp, Set.image_singleton]
  have hs : (fun j => E (FundamentalGroup.map P.closedTriangleBaseSlice b (x j))) =
      fun j => (x j, (1 : FundamentalGroup Circle 1)) := by
    funext j
    exact P.fundamentalGroupEquiv_baseSlice b (x j)
  change Subgroup.closure (Set.range (fun j =>
    E (FundamentalGroup.map P.closedTriangleBaseSlice b (x j))) ∪
      {E (turnLoop P.turn (P.closedTriangleBaseSlice b))}) = ⊤
  have ht : E (turnLoop P.turn (P.closedTriangleBaseSlice b)) =
      (1, FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk (circleTurnLoop 1))) :=
    P.fundamentalGroupEquiv_turnLoop b
  rw [hs, ht]
  exact closure_product_circle_generators x _ hx circleTurnLoop_generates

end ProductFibredPiece


namespace SeifertData

theorem closedThreeCones_kind (d : SeifertData) (hclosed : d.ports = 0)
    (hcones : d.cones.length = 3) : d.k = 3 := by
  have hc := d.ports_add_length_add_length
  have hk := d.k_le_three
  omega

theorem closedThreeCones_normals (d : SeifertData) (hclosed : d.ports = 0)
    (hcones : d.cones.length = 3) : d.normals = [] := by
  have hc := d.ports_add_length_add_length
  have hk := d.k_le_three
  exact List.eq_nil_of_length_eq_zero (by omega)

end SeifertData

namespace SeifertBlock
variable {W : CompactCarrier.{u}} {d : SeifertData} (B : SeifertBlock W d)

theorem fibreClass_central_of_closed_three_cones (hclosed : d.ports = 0)
    (hcones : d.cones.length = 3) (p : B.presentation.components.piece (B.piece none))
    (g : FundamentalGroup W.Carrier (B.productToCarrier p)) :
    g * B.fibreClass p = B.fibreClass p * g := by
  exact commute_map_of_surjective _ p
    (B.surjective_productToCarrier_of_closed_three_cones hclosed hcones p) _
      (commute_turnLoop _ p) g

set_option backward.isDefEq.respectTransparency false in
theorem filledMarkedSection_eq_baseSlice
    (b : B.product.base.surface.Carrier) (m : Fin d.fillingCount)
    (β : Path b (B.product.base.boundaryCircle (B.port (.inr m)) 1)) :
    B.filledMarkedSectionClass (B.product.closedTriangleBaseSlice b) m
        (β.map B.product.closedTriangleBaseSlice.continuous) =
      FundamentalGroup.map (B.productToCarrier.comp B.product.closedTriangleBaseSlice) b
        (GC.Topology.markedMap (B.product.base.boundaryCircle (B.port (.inr m))) 1 β
          (FundamentalGroup.fromPath ⟦circleLoop⟧)) := by
  have h := DFunLike.congr_fun (map_comp_markedMap
    (B.product.base.boundaryCircle (B.port (.inr m)))
    (B.productToCarrier.comp B.product.closedTriangleBaseSlice) 1 β)
      (FundamentalGroup.fromPath ⟦circleLoop⟧)
  change _ = fundamentalGroupChangeBasepoint
    ((β.map B.product.closedTriangleBaseSlice.continuous).map B.productToCarrier.continuous)
      (FundamentalGroup.map ((B.filledBoundaryMap m).comp circleInc) 1
        (FundamentalGroup.fromPath ⟦circleLoop⟧)) at h
  rw [GC.Topology.fundamentalGroup_map_comp] at h
  change _ = fundamentalGroupChangeBasepoint
    ((β.map B.product.closedTriangleBaseSlice.continuous).map B.productToCarrier.continuous)
      (FundamentalGroup.map (B.filledBoundaryMap m) torusBase
        (FundamentalGroup.map circleInc 1 (FundamentalGroup.fromPath ⟦circleLoop⟧))) at h
  rw [filledMarkedSectionClass, filledSectionClass, torusSection_circleLoop]
  exact h.symm

set_option backward.isDefEq.respectTransparency false in
theorem filledBaseSlice_fibre_relation (b : B.product.base.surface.Carrier)
    (m : Fin d.fillingCount)
    (β : Path b (B.product.base.boundaryCircle (B.port (.inr m)) 1)) :
    (show FundamentalGroup W.Carrier (B.productToCarrier (B.product.closedTriangleBaseSlice b))
      from FundamentalGroup.map (B.productToCarrier.comp B.product.closedTriangleBaseSlice) b
        (GC.Topology.markedMap (B.product.base.boundaryCircle (B.port (.inr m))) 1 β
          (FundamentalGroup.fromPath ⟦circleLoop⟧))) ^ (d.fillingSlope m).1 *
      B.fibreClass (B.product.closedTriangleBaseSlice b) ^ (d.fillingSlope m).2 = 1 := by
  rw [← B.filledMarkedSection_eq_baseSlice b m β]
  exact B.filledMarkedSection_fibre_relation _ m
    (β.map B.product.closedTriangleBaseSlice.continuous)

def closedFillingPortEquiv (hclosed : d.ports = 0) : Fin d.fillingCount ≃ Fin d.k := by
  have : IsEmpty (Fin d.ports) := hclosed ▸ inferInstance
  exact (Equiv.emptySum (Fin d.ports) (Fin d.fillingCount)).symm.trans B.port

theorem closedFillingPortEquiv_apply (hclosed : d.ports = 0) (m : Fin d.fillingCount) :
    B.closedFillingPortEquiv hclosed m = B.port (.inr m) := rfl

def closedConeFillingEquiv (hclosed : d.ports = 0) (hcones : d.cones.length = 3) :
    Fin d.cones.length ≃ Fin d.fillingCount :=
  finCongr (by simp only [SeifertData.fillingCount,
    d.closedThreeCones_normals hclosed hcones, List.length_nil, add_zero])

theorem closedConeFillingEquiv_slope (hclosed : d.ports = 0)
    (hcones : d.cones.length = 3) (c : Fin d.cones.length) :
    d.fillingSlope (closedConeFillingEquiv (d := d) hclosed hcones c) =
      ((d.cones[c].1 : ℤ), d.cones[c].2) := by
  have heq : closedConeFillingEquiv (d := d) hclosed hcones c = Fin.castAdd d.normals.length c :=
    Fin.ext rfl
  rw [heq, SeifertData.fillingSlope, Fin.append_left]

def closedTriangleNativeConeEquiv (hclosed : d.ports = 0) (hcones : d.cones.length = 3) :
    Fin 3 ≃ Fin d.cones.length :=
  (finCongr (d.closedThreeCones_kind hclosed hcones)).symm.trans
    ((closedConeFillingEquiv (d := d) hclosed hcones).trans (B.closedFillingPortEquiv hclosed)).symm

theorem closedTriangleNativeConeEquiv_port (hclosed : d.ports = 0)
    (hcones : d.cones.length = 3) (j : Fin 3) :
    B.port (.inr (closedConeFillingEquiv (d := d) hclosed hcones
      (B.closedTriangleNativeConeEquiv hclosed hcones j))) =
        Fin.cast (d.closedThreeCones_kind hclosed hcones).symm j := by
  change ((closedConeFillingEquiv (d := d) hclosed hcones).trans (B.closedFillingPortEquiv hclosed))
    (((closedConeFillingEquiv (d := d) hclosed hcones).trans
      (B.closedFillingPortEquiv hclosed)).symm
        ((finCongr (d.closedThreeCones_kind hclosed hcones)).symm j)) = _
  rw [Equiv.apply_symm_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem closure_baseSlice_fibreClass_of_closed_three_cones (hclosed : d.ports = 0)
    (hcones : d.cones.length = 3) (b : B.product.base.surface.Carrier)
    (x : Fin 3 → FundamentalGroup B.product.base.surface.Carrier b)
    (hx : Subgroup.closure (Set.range x) = ⊤) :
    Subgroup.closure (Set.range (fun j =>
      FundamentalGroup.map (B.productToCarrier.comp B.product.closedTriangleBaseSlice) b (x j)) ∪
        {B.fibreClass (B.product.closedTriangleBaseSlice b)}) = ⊤ := by
  let f := FundamentalGroup.map B.productToCarrier (B.product.closedTriangleBaseSlice b)
  have hs := closure_image_eq_top_of_surjective f
    (B.surjective_productToCarrier_of_closed_three_cones hclosed hcones _)
    _ (B.product.closure_baseSlice_turnLoop b x hx)
  rw [Set.image_union, ← Set.range_comp, Set.image_singleton] at hs
  have heq : (f ∘ fun j => FundamentalGroup.map B.product.closedTriangleBaseSlice b (x j)) =
      fun j => FundamentalGroup.map (B.productToCarrier.comp B.product.closedTriangleBaseSlice)
        b (x j) := by
    funext j
    exact (DFunLike.congr_fun (GC.Topology.fundamentalGroup_map_comp
      B.product.closedTriangleBaseSlice B.productToCarrier b) (x j)).symm
  rw [heq] at hs
  exact hs

end SeifertBlock
end GC.Seifert
