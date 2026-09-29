import DifferentialGeometry.Geometry.Boundary.Manifold.CollaredQuotientAtlas

open Set Function Topology
open scoped Manifold ContDiff

noncomputable section
set_option autoImplicit false

namespace ModelWithCorners

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {M' : Type*} [TopologicalSpace M'] [ChartedSpace H M']

theorem isBoundaryPoint_inl_iff {x : M} :
    I.IsBoundaryPoint (Sum.inl x : M ⊕ M') ↔ I.IsBoundaryPoint x := by
  refine ⟨fun h => ?_, fun h => ModelWithCorners.boundaryPoint_inl (I := I) x h⟩
  by_contra hx
  have hix : I.IsInteriorPoint x := (I.isInteriorPoint_iff_not_isBoundaryPoint x).mpr hx
  exact (I.disjoint_interior_boundary).le_bot
    ⟨ModelWithCorners.interiorPoint_inl (I := I) x hix, h⟩

theorem isBoundaryPoint_inr_iff {x : M'} :
    I.IsBoundaryPoint (Sum.inr x : M ⊕ M') ↔ I.IsBoundaryPoint x := by
  refine ⟨fun h => ?_, fun h => ModelWithCorners.boundaryPoint_inr (I := I) x h⟩
  by_contra hx
  have hix : I.IsInteriorPoint x := (I.isInteriorPoint_iff_not_isBoundaryPoint x).mpr hx
  exact (I.disjoint_interior_boundary).le_bot
    ⟨ModelWithCorners.interiorPoint_inr (I := I) x hix, h⟩

end ModelWithCorners

namespace DifferentialGeometry.Geometry.Boundary

universe u v

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type v} [TopologicalSpace N] [ChartedSpace H N]

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

private theorem range_restrict_eq {α : Type*} {β : Type*}
    {f : α → β} {p : α → Prop} {q : β → Prop} (H : ∀ x, p x → q (f x))
    (H' : ∀ x, q (f x) → p x) :
    range (MapsTo.restrict f p q H) = Subtype.val ⁻¹' range f := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    rw [Set.mem_preimage]
    exact ⟨x, rfl⟩
  · intro hy
    obtain ⟨x, hx⟩ := hy
    exact ⟨⟨x, H' x (hx ▸ y.2)⟩, Subtype.ext hx⟩

private theorem image_connectedComponent_restrict {α : Type*} {β : Type*}
    [TopologicalSpace α] [TopologicalSpace β] {f : α → β} (hf : IsEmbedding f)
    {p : α → Prop} {q : β → Prop} (H : ∀ x, p x → q (f x)) (H' : ∀ x, q (f x) → p x)
    (hcl : IsClopen (range f)) (z : Subtype p) :
    MapsTo.restrict f p q H '' connectedComponent z =
      connectedComponent (MapsTo.restrict f p q H z) := by
  have hT : IsClopen (range (MapsTo.restrict f p q H)) := by
    rw [range_restrict_eq H H']
    exact hcl.preimage continuous_subtype_val
  let phi : Subtype p ≃ₜ ↥(range (MapsTo.restrict f p q H)) := (hf.restrict H).toHomeomorph
  have h1 : phi '' connectedComponent z = connectedComponent (phi z) := by
    simpa [phi, connectedComponentIn_univ] using
      Homeomorph.image_connectedComponentIn phi (mem_univ z)
  have h3 : Subtype.val '' connectedComponent (phi z) =
      connectedComponent (MapsTo.restrict f p q H z) := by
    have hphi : (⟨MapsTo.restrict f p q H z, mem_range_self z⟩ :
        ↥(range (MapsTo.restrict f p q H))) = phi z := Subtype.ext rfl
    rw [← hT.connectedComponentIn_eq (x := MapsTo.restrict f p q H z) (mem_range_self z),
      connectedComponentIn_eq_image (F := range (MapsTo.restrict f p q H))
        (x := MapsTo.restrict f p q H z) (mem_range_self z), hphi]
  have h4 : MapsTo.restrict f p q H '' connectedComponent z =
      Subtype.val '' (phi '' connectedComponent z) := by
    change (fun a : Subtype p => (phi a).1) '' connectedComponent z =
      Subtype.val '' (phi '' connectedComponent z)
    rw [← Set.image_comp]
    rfl
  rw [h4, h1, h3]

def sumInlBoundaryManifold (y : BoundaryManifold I M) : BoundaryManifold I (M ⊕ N) :=
  ⟨Sum.inl (y : M), ModelWithCorners.boundaryPoint_inl (I := I) (y : M) y.2⟩

def sumInrBoundaryManifold (y : BoundaryManifold I N) : BoundaryManifold I (M ⊕ N) :=
  ⟨Sum.inr (y : N), ModelWithCorners.boundaryPoint_inr (I := I) (y : N) y.2⟩

theorem image_connectedComponent_sumInlBoundaryManifold (z : BoundaryManifold I M) :
    sumInlBoundaryManifold (I := I) (N := N) '' connectedComponent z =
      connectedComponent (sumInlBoundaryManifold (I := I) (N := N) z) :=
  image_connectedComponent_restrict (f := (Sum.inl : M → M ⊕ N))
    (Topology.IsOpenEmbedding.inl (X := M) (Y := N)).toIsEmbedding
    (fun x hx => ModelWithCorners.boundaryPoint_inl (I := I) x hx)
    (fun x hx => (ModelWithCorners.isBoundaryPoint_inl_iff (I := I) (x := x)).mp hx)
    isClopen_range_inl z

theorem image_connectedComponent_sumInrBoundaryManifold (z : BoundaryManifold I N) :
    sumInrBoundaryManifold (I := I) (M := M) '' connectedComponent z =
      connectedComponent (sumInrBoundaryManifold (I := I) (M := M) z) :=
  image_connectedComponent_restrict (f := (Sum.inr : N → M ⊕ N))
    (Topology.IsOpenEmbedding.inr (X := M) (Y := N)).toIsEmbedding
    (fun x hx => ModelWithCorners.boundaryPoint_inr (I := I) x hx)
    (fun x hx => (ModelWithCorners.isBoundaryPoint_inr_iff (I := I) (x := x)).mp hx)
    isClopen_range_inr z

namespace BoundaryComponent

def sumInl (C : BoundaryComponent I M) : BoundaryComponent I (M ⊕ N) :=
  Quotient.map (sumInlBoundaryManifold (I := I) (N := N))
    (fun a b hab => by
      change connectedComponent a = connectedComponent b at hab
      change connectedComponent (sumInlBoundaryManifold (I := I) (N := N) a) =
        connectedComponent (sumInlBoundaryManifold (I := I) (N := N) b)
      rw [← image_connectedComponent_sumInlBoundaryManifold a,
        ← image_connectedComponent_sumInlBoundaryManifold b, hab]) C

def sumInr (C : BoundaryComponent I N) : BoundaryComponent I (M ⊕ N) :=
  Quotient.map (sumInrBoundaryManifold (I := I) (M := M))
    (fun a b hab => by
      change connectedComponent a = connectedComponent b at hab
      change connectedComponent (sumInrBoundaryManifold (I := I) (M := M) a) =
        connectedComponent (sumInrBoundaryManifold (I := I) (M := M) b)
      rw [← image_connectedComponent_sumInrBoundaryManifold a,
        ← image_connectedComponent_sumInrBoundaryManifold b, hab]) C

@[simp]
theorem sumInl_mk (y : BoundaryManifold I M) :
    sumInl (I := I) (N := N) (ConnectedComponents.mk y) =
      ConnectedComponents.mk (sumInlBoundaryManifold (I := I) (N := N) y) :=
  Quotient.map_mk _ _ _

@[simp]
theorem sumInr_mk (y : BoundaryManifold I N) :
    sumInr (I := I) (M := M) (ConnectedComponents.mk y) =
      ConnectedComponents.mk (sumInrBoundaryManifold (I := I) (M := M) y) :=
  Quotient.map_mk _ _ _

theorem carrier_sumInl (C : BoundaryComponent I M) :
    carrier (sumInl (I := I) (N := N) C) = Sum.inl '' carrier C := by
  obtain ⟨z, rfl⟩ := ConnectedComponents.surjective_coe C
  refine Subset.antisymm ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    have hy' : ConnectedComponents.mk y = ConnectedComponents.mk
        (sumInlBoundaryManifold (I := I) (N := N) z) := by
      rw [← sumInl_mk]
      exact hy
    have hy1 : y ∈ connectedComponent (sumInlBoundaryManifold (I := I) (N := N) z) :=
      ConnectedComponents.coe_eq_coe'.mp hy'
    rw [← image_connectedComponent_sumInlBoundaryManifold z] at hy1
    obtain ⟨v, hv, hvy⟩ := hy1
    exact ⟨(v : M), by rw [carrier_mk]; exact ⟨v, hv, rfl⟩, by rw [← hvy]; rfl⟩
  · rintro x ⟨w, hw, rfl⟩
    rw [carrier_mk] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    refine ⟨sumInlBoundaryManifold (I := I) (N := N) v, ?_, rfl⟩
    exact (sumInl_mk (I := I) (N := N) v).symm.trans
      (congrArg (sumInl (I := I) (N := N)) (ConnectedComponents.coe_eq_coe'.mpr hv))

theorem carrier_sumInr (C : BoundaryComponent I N) :
    carrier (sumInr (I := I) (M := M) C) = Sum.inr '' carrier C := by
  obtain ⟨z, rfl⟩ := ConnectedComponents.surjective_coe C
  refine Subset.antisymm ?_ ?_
  · rintro x ⟨y, hy, rfl⟩
    have hy' : ConnectedComponents.mk y = ConnectedComponents.mk
        (sumInrBoundaryManifold (I := I) (M := M) z) := by
      rw [← sumInr_mk]
      exact hy
    have hy1 : y ∈ connectedComponent (sumInrBoundaryManifold (I := I) (M := M) z) :=
      ConnectedComponents.coe_eq_coe'.mp hy'
    rw [← image_connectedComponent_sumInrBoundaryManifold z] at hy1
    obtain ⟨v, hv, hvy⟩ := hy1
    exact ⟨(v : N), by rw [carrier_mk]; exact ⟨v, hv, rfl⟩, by rw [← hvy]; rfl⟩
  · rintro x ⟨w, hw, rfl⟩
    rw [carrier_mk] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    refine ⟨sumInrBoundaryManifold (I := I) (M := M) v, ?_, rfl⟩
    exact (sumInr_mk (I := I) (M := M) v).symm.trans
      (congrArg (sumInr (I := I) (M := M)) (ConnectedComponents.coe_eq_coe'.mpr hv))

theorem sumInl_ne_sumInr (C : BoundaryComponent I M) (D : BoundaryComponent I N) :
    sumInl (I := I) (N := N) C ≠ sumInr (I := I) (M := M) D := by
  intro h
  obtain ⟨x, hx⟩ := carrier_nonempty (sumInl (I := I) (N := N) C)
  have hx' : x ∈ carrier (sumInr (I := I) (M := M) D) := h ▸ hx
  rw [carrier_sumInl] at hx
  rw [carrier_sumInr] at hx'
  obtain ⟨a, -, ha⟩ := hx
  obtain ⟨b, -, hb⟩ := hx'
  exact Sum.inl_ne_inr (ha.trans hb.symm)

end BoundaryComponent

noncomputable def carrierHomeomorphInl (C : BoundaryComponent I M) :
    ↥(BoundaryComponent.carrier C) ≃ₜ
      ↥((Sum.inl : M → M ⊕ N) '' BoundaryComponent.carrier C) :=
  (Homeomorph.setCongr (Set.preimage_image_eq (BoundaryComponent.carrier C)
      Sum.inl_injective).symm).trans
    ((Topology.IsOpenEmbedding.inl (X := M) (Y := N)).toIsEmbedding.homeomorphOfSubsetRange
      (Set.image_subset_range _ _))

omit [ChartedSpace H N] in
theorem carrierHomeomorphInl_apply_coe (C : BoundaryComponent I M)
    (y : ↥(BoundaryComponent.carrier C)) :
    ((carrierHomeomorphInl (I := I) (N := N) C y :
      ↥((Sum.inl : M → M ⊕ N) '' BoundaryComponent.carrier C)) : M ⊕ N) =
      Sum.inl (y : M) := by
  simp [carrierHomeomorphInl, Homeomorph.trans_apply, Homeomorph.setCongr]

noncomputable def carrierEquivInl (C : BoundaryComponent I M) :
    ↥(BoundaryComponent.carrier (BoundaryComponent.sumInl (I := I) (N := N) C)) ≃ₜ
      ↥(BoundaryComponent.carrier C) :=
  (Homeomorph.setCongr (BoundaryComponent.carrier_sumInl (I := I) (N := N) C)).trans
    (carrierHomeomorphInl (I := I) (N := N) C).symm

omit [ChartedSpace H N] in
theorem carrierHomeomorphInl_symm_apply_coe (C : BoundaryComponent I M)
    (x : ↥((Sum.inl : M → M ⊕ N) '' BoundaryComponent.carrier C)) :
    Sum.inl (((carrierHomeomorphInl (I := I) (N := N) C).symm x :
      ↥(BoundaryComponent.carrier C)) : M) = (x : M ⊕ N) := by
  rw [← carrierHomeomorphInl_apply_coe (I := I) (N := N) C
      ((carrierHomeomorphInl (I := I) (N := N) C).symm x),
    Homeomorph.apply_symm_apply]

theorem carrierEquivInl_apply_coe (C : BoundaryComponent I M)
    (p : ↥(BoundaryComponent.carrier (BoundaryComponent.sumInl (I := I) (N := N) C))) :
    Sum.inl (((carrierEquivInl (I := I) (N := N) C p :
      ↥(BoundaryComponent.carrier C)) : M)) = (p : M ⊕ N) := by
  have h2 : ((Homeomorph.setCongr
      (BoundaryComponent.carrier_sumInl (I := I) (N := N) C)) p : M ⊕ N) = (p : M ⊕ N) := by
    simp [Homeomorph.setCongr]
  rw [carrierEquivInl, Homeomorph.trans_apply]
  exact (carrierHomeomorphInl_symm_apply_coe (I := I) (N := N) C _).trans h2



noncomputable def carrierHomeomorphInr (C : BoundaryComponent I N) :
    ↥(BoundaryComponent.carrier C) ≃ₜ
      ↥((Sum.inr : N → M ⊕ N) '' BoundaryComponent.carrier C) :=
  (Homeomorph.setCongr (Set.preimage_image_eq (BoundaryComponent.carrier C)
      Sum.inr_injective).symm).trans
    ((Topology.IsOpenEmbedding.inr (X := M) (Y := N)).toIsEmbedding.homeomorphOfSubsetRange
      (Set.image_subset_range _ _))

omit [ChartedSpace H M] in
theorem carrierHomeomorphInr_apply_coe (C : BoundaryComponent I N)
    (y : ↥(BoundaryComponent.carrier C)) :
    ((carrierHomeomorphInr (I := I) (M := M) C y :
      ↥((Sum.inr : N → M ⊕ N) '' BoundaryComponent.carrier C)) : M ⊕ N) =
      Sum.inr (y : N) := by
  simp [carrierHomeomorphInr, Homeomorph.trans_apply, Homeomorph.setCongr]

omit [ChartedSpace H M] in
theorem carrierHomeomorphInr_symm_apply_coe (C : BoundaryComponent I N)
    (x : ↥((Sum.inr : N → M ⊕ N) '' BoundaryComponent.carrier C)) :
    Sum.inr (((carrierHomeomorphInr (I := I) (M := M) C).symm x :
      ↥(BoundaryComponent.carrier C)) : N) = (x : M ⊕ N) := by
  rw [← carrierHomeomorphInr_apply_coe (I := I) (M := M) C
      ((carrierHomeomorphInr (I := I) (M := M) C).symm x),
    Homeomorph.apply_symm_apply]

noncomputable def carrierEquivInr (C : BoundaryComponent I N) :
    ↥(BoundaryComponent.carrier (BoundaryComponent.sumInr (I := I) (M := M) C)) ≃ₜ
      ↥(BoundaryComponent.carrier C) :=
  (Homeomorph.setCongr (BoundaryComponent.carrier_sumInr (I := I) (M := M) C)).trans
    (carrierHomeomorphInr (I := I) (M := M) C).symm

theorem carrierEquivInr_apply_coe (C : BoundaryComponent I N)
    (p : ↥(BoundaryComponent.carrier (BoundaryComponent.sumInr (I := I) (M := M) C))) :
    Sum.inr (((carrierEquivInr (I := I) (M := M) C p :
      ↥(BoundaryComponent.carrier C)) : N)) = (p : M ⊕ N) := by
  have h2 : ((Homeomorph.setCongr
      (BoundaryComponent.carrier_sumInr (I := I) (M := M) C)) p : M ⊕ N) = (p : M ⊕ N) := by
    simp [Homeomorph.setCongr]
  rw [carrierEquivInr, Homeomorph.trans_apply]
  exact (carrierHomeomorphInr_symm_apply_coe (I := I) (M := M) C _).trans h2


structure BinaryCollaredGluing (I : ModelWithCorners ℝ E H) (M : Type u) (N : Type v)
    [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace N] [ChartedSpace H N] where
  left : BoundaryComponent I M
  right : BoundaryComponent I N
  ε : ℝ
  ε_pos : 0 < ε
  collarLeft : C(↥left.carrier × Icc (0 : ℝ) ε, M)
  collarRight : C(↥right.carrier × Icc (0 : ℝ) ε, N)
  collarLeft_zero : ∀ z : ↥left.carrier, collarLeft (z, ⟨0, le_rfl, ε_pos.le⟩) = (z : M)
  collarRight_zero : ∀ z : ↥right.carrier, collarRight (z, ⟨0, le_rfl, ε_pos.le⟩) = (z : N)
  collarLeft_injective : Function.Injective collarLeft
  collarRight_injective : Function.Injective collarRight
  collarLeft_inward : ∀ (z : ↥left.carrier) (t : Icc (0 : ℝ) ε),
    0 < (t : ℝ) → ¬ I.IsBoundaryPoint (collarLeft (z, t))
  collarRight_inward : ∀ (z : ↥right.carrier) (t : Icc (0 : ℝ) ε),
    0 < (t : ℝ) → ¬ I.IsBoundaryPoint (collarRight (z, t))
  attaching : ↥left.carrier ≃ₜ ↥right.carrier

namespace BinaryCollaredGluing

variable {G : BinaryCollaredGluing I M N}

def toCollaredGluing (G : BinaryCollaredGluing I M N) : CollaredGluing I (M ⊕ N) (Fin 1) where
  left _ := BoundaryComponent.sumInl (I := I) (N := N) G.left
  right _ := BoundaryComponent.sumInr (I := I) (M := M) G.right
  blocks_injective := by
    rintro ⟨i, b⟩ ⟨j, c⟩ h
    have hij : i = j := Subsingleton.elim i j
    subst hij
    cases b <;> cases c <;> simp only [Bool.cond_true, Bool.cond_false] at h ⊢
    all_goals first
      | rfl
      | exact absurd h (BoundaryComponent.sumInl_ne_sumInr (I := I) G.left G.right)
      | exact absurd h.symm (BoundaryComponent.sumInl_ne_sumInr (I := I) G.left G.right)
  ε _ := G.ε
  ε_pos _ := G.ε_pos
  collarLeft _ :=
    { toFun := fun p => Sum.inl (G.collarLeft
        ((carrierEquivInl (I := I) (N := N) G.left p.1, p.2)))
      continuous_toFun := by fun_prop }
  collarRight _ :=
    { toFun := fun p => Sum.inr (G.collarRight
        ((carrierEquivInr (I := I) (M := M) G.right p.1, p.2)))
      continuous_toFun := by fun_prop }
  collarLeft_zero _ z := by
    simp only [ContinuousMap.coe_mk]
    have hz : G.collarLeft ((carrierEquivInl (I := I) (N := N) G.left z,
        ⟨0, le_rfl, G.ε_pos.le⟩)) = (carrierEquivInl (I := I) (N := N) G.left z : M) :=
      G.collarLeft_zero _
    rw [hz]
    exact carrierEquivInl_apply_coe (I := I) (N := N) G.left z
  collarRight_zero _ z := by
    simp only [ContinuousMap.coe_mk]
    have hz : G.collarRight ((carrierEquivInr (I := I) (M := M) G.right z,
        ⟨0, le_rfl, G.ε_pos.le⟩)) = (carrierEquivInr (I := I) (M := M) G.right z : N) :=
      G.collarRight_zero _
    rw [hz]
    exact carrierEquivInr_apply_coe (I := I) (M := M) G.right z
  collarLeft_injective _ := by
    rintro ⟨z, t⟩ ⟨z', t'⟩ h
    have h' : G.collarLeft ((carrierEquivInl (I := I) (N := N) G.left z, t)) =
        G.collarLeft ((carrierEquivInl (I := I) (N := N) G.left z', t')) :=
      Sum.inl_injective h
    obtain ⟨hz, ht⟩ := Prod.mk.inj (G.collarLeft_injective h')
    exact Prod.ext ((carrierEquivInl (I := I) (N := N) G.left).injective hz) ht
  collarRight_injective _ := by
    rintro ⟨z, t⟩ ⟨z', t'⟩ h
    have h' : G.collarRight ((carrierEquivInr (I := I) (M := M) G.right z, t)) =
        G.collarRight ((carrierEquivInr (I := I) (M := M) G.right z', t')) :=
      Sum.inr_injective h
    obtain ⟨hz, ht⟩ := Prod.mk.inj (G.collarRight_injective h')
    exact Prod.ext ((carrierEquivInr (I := I) (M := M) G.right).injective hz) ht
  collarLeft_inward _ z t ht hb :=
    G.collarLeft_inward _ _ ht ((ModelWithCorners.isBoundaryPoint_inl_iff (I := I)).mp hb)
  collarRight_inward _ z t ht hb :=
    G.collarRight_inward _ _ ht ((ModelWithCorners.isBoundaryPoint_inr_iff (I := I)).mp hb)
  collar_disjoint _ := by
    rw [Set.disjoint_left]
    rintro x ⟨p, hp⟩ ⟨q, hq⟩
    exact Sum.inl_ne_inr (hp.trans hq.symm)
  attaching _ := (carrierEquivInl (I := I) (N := N) G.left).trans
    (G.attaching.trans (carrierEquivInr (I := I) (M := M) G.right).symm)


theorem blocks_ne (G : BinaryCollaredGluing I M N) :
    BoundaryComponent.sumInl (I := I) (N := N) G.left ≠
      BoundaryComponent.sumInr (I := I) (M := M) G.right :=
  BoundaryComponent.sumInl_ne_sumInr (I := I) G.left G.right

noncomputable def toBoundaryGluing (G : BinaryCollaredGluing I M N) [IsManifold I 1 M]
    [IsManifold I 1 N] : Topology.BoundaryGluing (M ⊕ N) (Fin 1) := by
  letI : ChartedSpace H (M ⊕ N) := ChartedSpace.sum
  have hman : IsManifold I 1 (M ⊕ N) := IsManifold.disjointUnion
  exact G.toCollaredGluing.toBoundaryGluing

theorem t2Space_quotient (G : BinaryCollaredGluing I M N) [IsManifold I 1 M] [IsManifold I 1 N]
    [T2Space M] [T2Space N] [CompactSpace M] [CompactSpace N] :
    T2Space (Quotient G.toBoundaryGluing.setoid) :=
  Topology.BoundaryGluing.instT2SpaceQuotient (G := G.toBoundaryGluing)

theorem seamChart_eq (G : BinaryCollaredGluing I M N) [IsManifold I 1 M] [IsManifold I 1 N]
    (i j : Fin 1) :
    G.toCollaredGluing.seamChart i = G.toCollaredGluing.seamChart j := by
  rw [Subsingleton.elim i j]

theorem seamChart_injective (G : BinaryCollaredGluing I M N) [IsManifold I 1 M]
    [IsManifold I 1 N] (i : Fin 1) :
    Function.Injective (G.toCollaredGluing.seamChart i) := by
  have hman : IsManifold I 1 (M ⊕ N) := IsManifold.disjointUnion
  exact G.toCollaredGluing.seamChart_injective i

theorem exists_ungluedChart_or_seamChart (G : BinaryCollaredGluing I M N) [IsManifold I 1 M]
    [IsManifold I 1 N] (x : M ⊕ N) :
    (∃ chart : OpenPartialHomeomorph (Quotient G.toCollaredGluing.toBoundaryGluing.setoid) H,
      Quotient.mk'' (s₁ := G.toCollaredGluing.toBoundaryGluing.setoid) x ∈ chart.source ∧
        chart (Quotient.mk'' (s₁ := G.toCollaredGluing.toBoundaryGluing.setoid) x)
          = chartAt H x x)
      ∨ ∃ (i : Fin 1) (z : ↥(G.toCollaredGluing.left i).carrier),
          G.toCollaredGluing.seamChart i
              (z, ⟨0, neg_nonpos.mpr (G.toCollaredGluing.ε_pos i).le,
                (G.toCollaredGluing.ε_pos i).le⟩)
            = Quotient.mk'' (s₁ := G.toCollaredGluing.toBoundaryGluing.setoid) x := by
  have hman : IsManifold I 1 (M ⊕ N) := IsManifold.disjointUnion
  exact G.toCollaredGluing.exists_ungluedChart_or_seamChart x


def ofCollaredGluing (G : CollaredGluing I M (Fin 1)) : BinaryCollaredGluing I M M where
  left := G.left 0
  right := G.right 0
  ε := G.ε 0
  ε_pos := G.ε_pos 0
  collarLeft := G.collarLeft 0
  collarRight := G.collarRight 0
  collarLeft_zero := G.collarLeft_zero 0
  collarRight_zero := G.collarRight_zero 0
  collarLeft_injective := G.collarLeft_injective 0
  collarRight_injective := G.collarRight_injective 0
  collarLeft_inward := G.collarLeft_inward 0
  collarRight_inward := G.collarRight_inward 0
  attaching := G.attaching 0

end BinaryCollaredGluing

section UnitInterval

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

noncomputable def unitIntervalBinaryCollaredGluing :
    BinaryCollaredGluing (𝓡∂ 1) (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) :=
  BinaryCollaredGluing.ofCollaredGluing unitIntervalCollaredGluing

theorem unitIntervalBinaryCollaredGluing_blocks_ne :
    BoundaryComponent.sumInl (I := 𝓡∂ 1) unitIntervalBinaryCollaredGluing.left ≠
      BoundaryComponent.sumInr (I := 𝓡∂ 1) unitIntervalBinaryCollaredGluing.right :=
  BinaryCollaredGluing.blocks_ne unitIntervalBinaryCollaredGluing

theorem unitIntervalBinaryCollaredGluing_t2Space :
    T2Space (Quotient unitIntervalBinaryCollaredGluing.toBoundaryGluing.setoid) :=
  BinaryCollaredGluing.t2Space_quotient unitIntervalBinaryCollaredGluing

theorem unitIntervalCollaredGluing_notMem_carrier :
    (⟨1 / 2, by norm_num⟩ : Icc (0 : ℝ) 1) ∉
      BoundaryComponent.carrier (unitIntervalCollaredGluing.left 0) ∪
        BoundaryComponent.carrier (unitIntervalCollaredGluing.right 0) := by
  have h := unitIntervalCollaredGluing_notMem_block 0
  rwa [CollaredGluing.block_eq] at h

theorem unitIntervalBinaryCollaredGluing_notMem_block :
    (Sum.inl (⟨1 / 2, by norm_num⟩ : Icc (0 : ℝ) 1) :
        Icc (0 : ℝ) 1 ⊕ Icc (0 : ℝ) 1) ∉
      unitIntervalBinaryCollaredGluing.toBoundaryGluing.block 0 := by
  intro hmem
  have hmem' : (Sum.inl (⟨1 / 2, by norm_num⟩ : Icc (0 : ℝ) 1) :
      Icc (0 : ℝ) 1 ⊕ Icc (0 : ℝ) 1) ∈ BoundaryComponent.carrier
        (BoundaryComponent.sumInl (I := 𝓡∂ 1) (unitIntervalCollaredGluing.left 0)) ∪
        BoundaryComponent.carrier (BoundaryComponent.sumInr (I := 𝓡∂ 1)
          (unitIntervalCollaredGluing.right 0)) := hmem
  rcases hmem' with h | h
  · rw [BoundaryComponent.carrier_sumInl] at h
    obtain ⟨w, hw, hwx⟩ := h
    exact unitIntervalCollaredGluing_notMem_carrier
      (Or.inl (Sum.inl_injective hwx ▸ hw))
  · rw [BoundaryComponent.carrier_sumInr] at h
    obtain ⟨w, -, hwx⟩ := h
    exact Sum.inr_ne_inl hwx

theorem unitIntervalBinaryCollaredGluing_mk_inl_ne_mk_inr :
    Quotient.mk'' (s₁ := unitIntervalBinaryCollaredGluing.toBoundaryGluing.setoid)
        (Sum.inl (⟨1 / 2, by norm_num⟩ : Icc (0 : ℝ) 1)) ≠
      Quotient.mk'' (s₁ := unitIntervalBinaryCollaredGluing.toBoundaryGluing.setoid)
        (Sum.inr (⟨1 / 2, by norm_num⟩ : Icc (0 : ℝ) 1)) := by
  intro h
  have hrel := (Quotient.eq'' (s₁ := unitIntervalBinaryCollaredGluing.toBoundaryGluing.setoid)).mp h
  have heq := unitIntervalBinaryCollaredGluing.toBoundaryGluing.eq_of_rel_of_notMem
    (fun i => by
      have hi : i = 0 := Subsingleton.elim i 0
      rw [hi]
      exact unitIntervalBinaryCollaredGluing_notMem_block) hrel
  exact Sum.inl_ne_inr heq

theorem unitIntervalBinaryCollaredGluing_exists_ungluedChart :
    ∃ chart : OpenPartialHomeomorph
        (Quotient unitIntervalBinaryCollaredGluing.toBoundaryGluing.setoid)
        (EuclideanHalfSpace 1),
      Quotient.mk'' (s₁ := unitIntervalBinaryCollaredGluing.toBoundaryGluing.setoid)
          (Sum.inl (⟨1 / 2, by norm_num⟩ : Icc (0 : ℝ) 1) :
            Icc (0 : ℝ) 1 ⊕ Icc (0 : ℝ) 1) ∈ chart.source ∧
        chart (Quotient.mk'' (s₁ := unitIntervalBinaryCollaredGluing.toBoundaryGluing.setoid)
          (Sum.inl (⟨1 / 2, by norm_num⟩ : Icc (0 : ℝ) 1) :
            Icc (0 : ℝ) 1 ⊕ Icc (0 : ℝ) 1))
          = chartAt (EuclideanHalfSpace 1)
              (Sum.inl (⟨1 / 2, by norm_num⟩ : Icc (0 : ℝ) 1) :
                Icc (0 : ℝ) 1 ⊕ Icc (0 : ℝ) 1)
              (Sum.inl (⟨1 / 2, by norm_num⟩ : Icc (0 : ℝ) 1) :
                Icc (0 : ℝ) 1 ⊕ Icc (0 : ℝ) 1) := by
  have hman : IsManifold (𝓡∂ 1) 1 (Icc (0 : ℝ) 1 ⊕ Icc (0 : ℝ) 1) :=
    IsManifold.disjointUnion
  exact unitIntervalBinaryCollaredGluing.toCollaredGluing.exists_ungluedChart (fun i => by
    have hi : i = 0 := Subsingleton.elim i 0
    rw [hi]
    exact unitIntervalBinaryCollaredGluing_notMem_block)

theorem unitIntervalBinaryCollaredGluing_quotient_nonempty :
    Nonempty (Quotient unitIntervalBinaryCollaredGluing.toBoundaryGluing.setoid) :=
  ⟨Quotient.mk'' (Sum.inl (⟨0, by norm_num⟩ : Icc (0 : ℝ) 1))⟩

end UnitInterval

end DifferentialGeometry.Geometry.Boundary
