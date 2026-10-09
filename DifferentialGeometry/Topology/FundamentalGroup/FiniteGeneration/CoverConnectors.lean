import DifferentialGeometry.Topology.FundamentalGroup.FiniteGeneration.FiniteCoverGroups
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set CategoryTheory
open DifferentialGeometry.Topology.VanKampen
namespace GC.Topology
universe u v
variable {X : Type u} [TopologicalSpace X]

theorem map_inclusion_toAmbient {A W : Set X} (hAW : A ⊆ W) {x y : A}
    (p : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) :
    (FundamentalGroupoid.map (subsetToAmbient W)).map
      ((FundamentalGroupoid.map (ContinuousMap.inclusion hAW)).map p) =
    (FundamentalGroupoid.map (subsetToAmbient A)).map p := by
  refine Quotient.inductionOn p ?_
  intro p
  rfl

theorem inclusion_paths_eq_of_simplyConnected {A W : Set X} (hAW : A ⊆ W)
    [SimplyConnectedSpace W] {x y : A}
    (p q : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) :
    (FundamentalGroupoid.map (subsetToAmbient A)).map p =
    (FundamentalGroupoid.map (subsetToAmbient A)).map q := by
  let F := FundamentalGroupoid.map (ContinuousMap.inclusion hAW)
  have he : F.map p = F.map q :=
    (inferInstance : Subsingleton (Path.Homotopic.Quotient
      (⟨x.val, hAW x.property⟩ : W) (⟨y.val, hAW y.property⟩ : W))).elim _ _
  have hm := congrArg (fun f => (FundamentalGroupoid.map (subsetToAmbient W)).map f) he
  simpa only [F, map_inclusion_toAmbient] using hm

section Construction
variable [PathConnectedSpace X] {ι : Type v} (V : ι → Set X)
  [∀ i, PathConnectedSpace (V i)] (x₀ : X)

noncomputable def coverCenter (i : ι) : V i := Classical.choice inferInstance

noncomputable def coverInnerPath (i : ι) (x : V i) :
    FundamentalGroupoid.mk (coverCenter V i) ⟶ FundamentalGroupoid.mk x :=
  ⟦PathConnectedSpace.somePath (coverCenter V i) x⟧

noncomputable def coverAnchor (i : ι) :
    FundamentalGroupoid.mk x₀ ⟶ FundamentalGroupoid.mk (coverCenter V i).val :=
  ⟦PathConnectedSpace.somePath x₀ (coverCenter V i).val⟧

noncomputable def actualCoverPath (i : ι) (x : V i) :
    FundamentalGroupoid.mk x₀ ⟶ FundamentalGroupoid.mk x.val :=
  coverAnchor V x₀ i ≫ (FundamentalGroupoid.map (subsetToAmbient (V i))).map
    (coverInnerPath V i x)

variable (hpair : ∀ i j, (V i ∩ V j).Nonempty →
  ∃ W : Set X, SimplyConnectedSpace W ∧ V i ∪ V j ⊆ W)

include hpair in
theorem actualCoverPath_coherent (i : ι) (x y : V i)
    (p : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) :
    actualCoverPath V x₀ i x ≫ (FundamentalGroupoid.map (subsetToAmbient (V i))).map p =
      actualCoverPath V x₀ i y := by
  obtain ⟨W, hW, hsub⟩ := hpair i i ⟨(coverCenter V i).val,
    (coverCenter V i).property, (coverCenter V i).property⟩
  let : SimplyConnectedSpace W := hW
  have hVi : V i ⊆ W := fun _ hx => hsub (Or.inl hx)
  have he := inclusion_paths_eq_of_simplyConnected hVi
    (coverInnerPath V i x ≫ p) (coverInnerPath V i y)
  unfold actualCoverPath
  rw [Category.assoc, ← CategoryTheory.Functor.map_comp, he]

include hpair in
theorem actualCoverPath_overlap (i j : ι) (x y : ↥(V i ∩ V j)) :
    (actualCoverPath V x₀ i ⟨x.val, x.property.1⟩ ≫
      Groupoid.inv (actualCoverPath V x₀ j ⟨x.val, x.property.2⟩) : FundamentalGroup X x₀) =
    (actualCoverPath V x₀ i ⟨y.val, y.property.1⟩ ≫
      Groupoid.inv (actualCoverPath V x₀ j ⟨y.val, y.property.2⟩) : FundamentalGroup X x₀) := by
  obtain ⟨W, hW, hsub⟩ := hpair i j ⟨x.val, x.property⟩
  let : SimplyConnectedSpace W := hW
  have hVi : V i ⊆ W := fun _ hx => hsub (Or.inl hx)
  have hVj : V j ⊆ W := fun _ hx => hsub (Or.inr hx)
  let Fi := FundamentalGroupoid.map (ContinuousMap.inclusion hVi)
  let Fj := FundamentalGroupoid.map (ContinuousMap.inclusion hVj)
  let a : W := ⟨(coverCenter V i).val, hVi (coverCenter V i).property⟩
  let b : W := ⟨(coverCenter V j).val, hVj (coverCenter V j).property⟩
  let middle (z : ↥(V i ∩ V j)) : FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b :=
    Fi.map (X := FundamentalGroupoid.mk (coverCenter V i))
      (Y := FundamentalGroupoid.mk (⟨z.val, z.property.1⟩ : V i))
      (coverInnerPath V i ⟨z.val, z.property.1⟩) ≫
      Groupoid.inv (Fj.map (X := FundamentalGroupoid.mk (coverCenter V j))
        (Y := FundamentalGroupoid.mk (⟨z.val, z.property.2⟩ : V j))
        (coverInnerPath V j ⟨z.val, z.property.2⟩))
  have he : middle x = middle y :=
    (inferInstance : Subsingleton (Path.Homotopic.Quotient a b)).elim _ _
  have hm := congrArg (fun f : FundamentalGroupoid.mk a ⟶ FundamentalGroupoid.mk b =>
    (FundamentalGroupoid.map (subsetToAmbient W)).map f) he
  simp only [middle, CategoryTheory.Functor.map_comp, Groupoid.inv_eq_inv,
    CategoryTheory.Functor.map_inv, Fi, Fj, map_inclusion_toAmbient] at hm
  have hh := congrArg (fun f => coverAnchor V x₀ i ≫ f ≫ Groupoid.inv (coverAnchor V x₀ j)) hm
  simpa [actualCoverPath, Groupoid.inv_eq_inv, Category.assoc] using hh

def actualCoverConnectors : CoverConnectors V x₀ where
  path := actualCoverPath V x₀
  coherent := actualCoverPath_coherent V x₀ hpair
  overlap := actualCoverPath_overlap V x₀ hpair

include hpair in
theorem groupFG_of_finite_pairwise_cover [Finite ι]
    (hopen : ∀ i, IsOpen (V i)) (hcover : (⋃ i, V i) = univ) :
    Group.FG (FundamentalGroup X x₀) :=
  (actualCoverConnectors V x₀ hpair).groupFG hopen hcover

end Construction
end GC.Topology
