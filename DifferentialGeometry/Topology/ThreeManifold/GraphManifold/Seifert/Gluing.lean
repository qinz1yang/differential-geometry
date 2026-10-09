import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.Decomposition
import DifferentialGeometry.Topology.ThreeManifold.TorusCut.Sides
import DifferentialGeometry.Topology.VanKampen.AmalgamatedProduct
import DifferentialGeometry.Topology.FundamentalGroup.Retraction
import DifferentialGeometry.Topology.FundamentalGroup.MarkedFundamentalGroup
import DifferentialGeometry.Topology.Manifold.LocallyPathConnected

/-!
# Gluing along one seam

Chapter 6, K09, first tier. For a seam `j` of a torus presentation `G` of `W`, the open collar
`seamCollar` (the target of `G.seam j`) is homotopy equivalent to the torus through the seam torus
`seamTorus` (`t ↦ G.seam j (t, 0)`, the image of both sides of the pairing torus,
`seamTorus_eq_cutMap`, `seamTorus_eq_cutMap_right`), so the seam torus is a π₁-isomorphism onto the
collar (`bijective_seamTorusIn`). The sides `leftSide`, `rightSide` are the path components of the
complement of the seam torus through the two halves of the collar; if `W` is connected they exhaust
the complement (`compl_seamSurface_eq`), and the seam separates (`IsSeparating`, `isSeparating_iff`)
when they are disjoint. Then the unions `leftRegion` and `rightRegion` of either side with the
collar are path-connected open sets covering `W` and meeting exactly in the collar, and van Kampen
identifies π₁ of `W` with the amalgamated product of the two regions over the collar
(`seamVanKampen`). Base and factor maps of an amalgamated product with injective edge maps are
injective (`Monoid.PushoutI.base_injective`, `of_injective`), so if the seam torus is π₁-injective
into both regions at one basepoint, it is π₁-injective into `W` at every basepoint
(`injective_seamTorus`) and both regions are π₁-injective (`injective_leftRegion`,
`injective_rightRegion`). These open-cover statements are proved for arbitrary spaces first
(`injective_fundamentalGroup_map_of_openCover`). For a closed presentation the seam torus is the
torus of `toTorusDecomposition` (`toTorusDecomposition_torusInPrime_eq`), which is therefore
incompressible when every seam separates with injective sides
(`incompressible_toTorusDecomposition`).
-/

set_option autoImplicit false

noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.VanKampen
open scoped Manifold ContDiff Topology ContinuousMap

universe u v

namespace GC.Seifert

section OpenCover
variable {X : Type u} [TopologicalSpace X] {T : Type v} [TopologicalSpace T]

private theorem mapOfEq_rfl {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : C(Y, Z)) (y : Y) :
    FundamentalGroup.mapOfEq f (rfl : f y = f y) = FundamentalGroup.map f y := by
  ext p
  rw [FundamentalGroup.mapOfEq_apply]
  exact Path.Homotopic.Quotient.cast_rfl_rfl _

theorem fundamentalGroupAmalgamation_injective (U V : Set X) (x : ↑(U ∩ V))
    (hl : Function.Injective (FundamentalGroup.map (interToLeft U V) x))
    (hr : Function.Injective (FundamentalGroup.map (interToRight U V) x)) :
    ∀ i, Function.Injective (fundamentalGroupAmalgamation U V x.1 x.2 i)
  | false => by
    change Function.Injective (FundamentalGroup.mapOfEq (interToLeft U V)
      (rfl : interToLeft U V x = interToLeft U V x))
    rw [mapOfEq_rfl]
    exact hl
  | true => by
    change Function.Injective (FundamentalGroup.mapOfEq (interToRight U V)
      (rfl : interToRight U V x = interToRight U V x))
    rw [mapOfEq_rfl]
    exact hr

theorem fundamentalGroupEquivAmalgamatedProduct_of_false (U V : Set X) (hU : IsOpen U)
    (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (x : ↑(U ∩ V)) [PathConnectedSpace U]
    [PathConnectedSpace V] [PathConnectedSpace (↑(U ∩ V))]
    (g : FundamentalGroup U (interToLeft U V x)) :
    fundamentalGroupEquivAmalgamatedProduct U V hU hV hcover x.1 x.2
        (Monoid.PushoutI.of (φ := fundamentalGroupAmalgamation U V x.1 x.2) false g) =
      FundamentalGroup.map (subsetToAmbient U) (interToLeft U V x) g := by
  have h := DFunLike.congr_fun
    (fundamentalGroupEquivAmalgamatedProduct_comp_left U V hU hV hcover x.1 x.2) g
  change _ = FundamentalGroup.mapOfEq (subsetToAmbient U)
    (rfl : subsetToAmbient U (interToLeft U V x) = subsetToAmbient U (interToLeft U V x)) g at h
  rw [mapOfEq_rfl] at h
  exact h

theorem fundamentalGroupEquivAmalgamatedProduct_of_true (U V : Set X) (hU : IsOpen U)
    (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (x : ↑(U ∩ V)) [PathConnectedSpace U]
    [PathConnectedSpace V] [PathConnectedSpace (↑(U ∩ V))]
    (g : FundamentalGroup V (interToRight U V x)) :
    fundamentalGroupEquivAmalgamatedProduct U V hU hV hcover x.1 x.2
        (Monoid.PushoutI.of (φ := fundamentalGroupAmalgamation U V x.1 x.2) true g) =
      FundamentalGroup.map (subsetToAmbient V) (interToRight U V x) g := by
  have h := DFunLike.congr_fun
    (fundamentalGroupEquivAmalgamatedProduct_comp_right U V hU hV hcover x.1 x.2) g
  change _ = FundamentalGroup.mapOfEq (subsetToAmbient V)
    (rfl : subsetToAmbient V (interToRight U V x) = subsetToAmbient V (interToRight U V x)) g at h
  rw [mapOfEq_rfl] at h
  exact h

theorem fundamentalGroupEquivAmalgamatedProduct_base (U V : Set X) (hU : IsOpen U)
    (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (x : ↑(U ∩ V)) [PathConnectedSpace U]
    [PathConnectedSpace V] [PathConnectedSpace (↑(U ∩ V))]
    (w : FundamentalGroup (↑(U ∩ V)) x) :
    fundamentalGroupEquivAmalgamatedProduct U V hU hV hcover x.1 x.2
        (Monoid.PushoutI.base (fundamentalGroupAmalgamation U V x.1 x.2) w) =
      FundamentalGroup.map (subsetToAmbient (U ∩ V)) x w := by
  rw [← Monoid.PushoutI.of_apply_eq_base _ false]
  refine (fundamentalGroupEquivAmalgamatedProduct_of_false U V hU hV hcover x _).trans ?_
  have h2 : fundamentalGroupAmalgamation U V x.1 x.2 false w =
      FundamentalGroup.map (interToLeft U V) x w := by
    change FundamentalGroup.mapOfEq (interToLeft U V)
      (rfl : interToLeft U V x = interToLeft U V x) w = _
    rw [mapOfEq_rfl]
  rw [h2]
  exact (DFunLike.congr_fun
    (GC.Topology.fundamentalGroup_map_comp (interToLeft U V) (subsetToAmbient U) x) w).symm

theorem injective_fundamentalGroup_map_inter (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (x : ↑(U ∩ V)) [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace (↑(U ∩ V))]
    (hl : Function.Injective (FundamentalGroup.map (interToLeft U V) x))
    (hr : Function.Injective (FundamentalGroup.map (interToRight U V) x)) :
    Function.Injective (FundamentalGroup.map (subsetToAmbient (U ∩ V)) x) := by
  intro a b hab
  apply Monoid.PushoutI.base_injective (fundamentalGroupAmalgamation_injective U V x hl hr)
  apply (fundamentalGroupEquivAmalgamatedProduct U V hU hV hcover x.1 x.2).injective
  rw [fundamentalGroupEquivAmalgamatedProduct_base, fundamentalGroupEquivAmalgamatedProduct_base]
  exact hab

theorem injective_fundamentalGroup_map_left (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (x : ↑(U ∩ V)) [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace (↑(U ∩ V))]
    (hl : Function.Injective (FundamentalGroup.map (interToLeft U V) x))
    (hr : Function.Injective (FundamentalGroup.map (interToRight U V) x)) :
    Function.Injective (FundamentalGroup.map (subsetToAmbient U) (interToLeft U V x)) := by
  intro a b hab
  apply Monoid.PushoutI.of_injective (fundamentalGroupAmalgamation_injective U V x hl hr) false
  apply (fundamentalGroupEquivAmalgamatedProduct U V hU hV hcover x.1 x.2).injective
  rw [fundamentalGroupEquivAmalgamatedProduct_of_false,
    fundamentalGroupEquivAmalgamatedProduct_of_false]
  exact hab

theorem injective_fundamentalGroup_map_right (U V : Set X) (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (x : ↑(U ∩ V)) [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace (↑(U ∩ V))]
    (hl : Function.Injective (FundamentalGroup.map (interToLeft U V) x))
    (hr : Function.Injective (FundamentalGroup.map (interToRight U V) x)) :
    Function.Injective (FundamentalGroup.map (subsetToAmbient V) (interToRight U V x)) := by
  intro a b hab
  apply Monoid.PushoutI.of_injective (fundamentalGroupAmalgamation_injective U V x hl hr) true
  apply (fundamentalGroupEquivAmalgamatedProduct U V hU hV hcover x.1 x.2).injective
  rw [fundamentalGroupEquivAmalgamatedProduct_of_true,
    fundamentalGroupEquivAmalgamatedProduct_of_true]
  exact hab

private theorem injective_of_surjective_comp {Y Z : Type*} [TopologicalSpace Y]
    [TopologicalSpace Z] (f : C(T, Y)) (g : C(Y, Z)) (t : T)
    (hf : Function.Surjective (FundamentalGroup.map f t))
    (h : Function.Injective (FundamentalGroup.map (g.comp f) t)) :
    Function.Injective (FundamentalGroup.map g (f t)) := by
  intro a b hab
  obtain ⟨a', rfl⟩ := hf a
  obtain ⟨b', rfl⟩ := hf b
  have hab' : FundamentalGroup.map (g.comp f) t a' = FundamentalGroup.map (g.comp f) t b' := by
    rw [GC.Topology.fundamentalGroup_map_comp]
    exact hab
  rw [h hab']

theorem injective_fundamentalGroup_map_of_openCover (U V : Set X) (hU : IsOpen U)
    (hV : IsOpen V) (hcover : U ∪ V = Set.univ) [PathConnectedSpace U] [PathConnectedSpace V]
    [PathConnectedSpace (↑(U ∩ V))] (f : C(T, ↑(U ∩ V))) (t : T)
    (hf : Function.Surjective (FundamentalGroup.map f t))
    (hfU : Function.Injective (FundamentalGroup.map ((interToLeft U V).comp f) t))
    (hfV : Function.Injective (FundamentalGroup.map ((interToRight U V).comp f) t)) :
    Function.Injective (FundamentalGroup.map ((subsetToAmbient (U ∩ V)).comp f) t) := by
  rw [GC.Topology.fundamentalGroup_map_comp]
  exact (injective_fundamentalGroup_map_inter U V hU hV hcover (f t)
    (injective_of_surjective_comp f _ t hf hfU) (injective_of_surjective_comp f _ t hf hfV)).comp
    (GC.Topology.injective_inner_of_composite f (interToLeft U V) t hfU)

end OpenCover

section Collar

private theorem zero_mem_signedCollarSource (t : Torus) : (t, (0 : ℝ)) ∈ signedCollarSource :=
  ⟨by norm_num, by norm_num⟩

private theorem mul_mem_signedCollarSource (τ : unitInterval) {p : Torus × ℝ}
    (hp : p ∈ signedCollarSource) : (p.1, (τ : ℝ) * p.2) ∈ signedCollarSource := by
  obtain ⟨h1, h2⟩ := hp
  have h0 := τ.2.1
  have h1' := τ.2.2
  rcases le_or_gt 0 p.2 with hs | hs
  · constructor <;> nlinarith
  · constructor <;> nlinarith

def signedCollarCore : C(Torus, signedCollarSource) :=
  ⟨fun t => ⟨(t, 0), zero_mem_signedCollarSource t⟩, by fun_prop⟩

def signedCollarProjection : C(signedCollarSource, Torus) :=
  ⟨fun p => p.1.1, by fun_prop⟩

def signedCollarShrink : (signedCollarCore.comp signedCollarProjection).Homotopy
    (ContinuousMap.id signedCollarSource) where
  toFun z := ⟨(z.2.1.1, (z.1 : ℝ) * z.2.1.2), mul_mem_signedCollarSource z.1 z.2.2⟩
  continuous_toFun := Continuous.subtype_mk (by fun_prop) _
  map_zero_left p := Subtype.ext (Prod.ext rfl (by simp [signedCollarCore, signedCollarProjection]))
  map_one_left _ := Subtype.ext (Prod.ext rfl (by simp))

def signedCollarHomotopyEquiv : signedCollarSource ≃ₕ Torus where
  toFun := signedCollarProjection
  invFun := signedCollarCore
  left_inv := ⟨signedCollarShrink⟩
  right_inv := ContinuousMap.Homotopic.refl _

end Collar

namespace TorusPresentation
variable {W : CompactCarrier.{u}} (G : TorusPresentation W) (j : Fin G.pairing.count)

theorem mem_seam_source {p : Torus × ℝ} (hp : p ∈ signedCollarSource) :
    p ∈ (G.seam j).source :=
  (G.seam_source j).symm ▸ hp

theorem continuousOn_seam : ContinuousOn (G.seam j) (G.seam j).source :=
  (G.seam j).contMDiffOn.continuousOn

def seamCollar : Set W.Carrier := (G.seam j).target

theorem isOpen_seamCollar : IsOpen (G.seamCollar j) := (G.seam j).open_target

def seamTorus : C(Torus, W.Carrier) where
  toFun t := G.seam j (t, 0)
  continuous_toFun := (G.continuousOn_seam j).comp_continuous (by fun_prop)
    fun t => G.mem_seam_source j (zero_mem_signedCollarSource t)

theorem seamTorus_apply (t : Torus) : G.seamTorus j t = G.seam j (t, 0) := rfl

theorem seamTorus_eq_cutMap (t : Torus) :
    G.seamTorus j t = G.cutMap (G.pairing.leftParam j t) :=
  G.seam_zero j t

theorem seamTorus_eq_cutMap_right (t : Torus) :
    G.seamTorus j t = G.cutMap (G.pairing.rightParam j (G.pairing.matching j t)) := by
  rw [← G.pairing.right_zero, G.cutMap_rightCollar j (zero_mem_halfCollarSource _),
    Diffeomorph.symm_apply_apply]
  rfl

theorem seamTorus_mem_seamCollar (t : Torus) : G.seamTorus j t ∈ G.seamCollar j :=
  (G.seam j).map_source' (G.mem_seam_source j (zero_mem_signedCollarSource t))

def seamTorusIn (S : Set W.Carrier) (hS : G.seamCollar j ⊆ S) : C(Torus, S) :=
  ⟨fun t => ⟨G.seamTorus j t, hS (G.seamTorus_mem_seamCollar j t)⟩,
    (G.seamTorus j).continuous.subtype_mk _⟩

def seamCollarHomotopyEquiv : G.seamCollar j ≃ₕ Torus :=
  (((G.seam j).toOpenPartialHomeomorph.toHomeomorphSourceTarget.symm.trans
    (Homeomorph.setCongr (G.seam_source j))).toHomotopyEquiv).trans signedCollarHomotopyEquiv

theorem bijective_seamTorusIn (S : Set W.Carrier) (hS : S = G.seamCollar j) (t : Torus) :
    Function.Bijective (FundamentalGroup.map (G.seamTorusIn j S hS.ge) t) := by
  refine bijective_fundamentalGroup_map_of_homotopyEquiv_leftInverse
    ((Homeomorph.setCongr hS).toHomotopyEquiv.trans (G.seamCollarHomotopyEquiv j)) _
    (fun s => ?_) t
  change ((G.seam j).toPartialEquiv.symm (G.seam j (s, 0))).1 = s
  rw [(G.seam j).toPartialEquiv.left_inv (G.mem_seam_source j (zero_mem_signedCollarSource s))]

def seamSurface : Set W.Carrier := Set.range (G.seamTorus j)

theorem isClosed_seamSurface : IsClosed (G.seamSurface j) :=
  (isCompact_range (G.seamTorus j).continuous).isClosed

theorem seamSurface_subset_seamCollar : G.seamSurface j ⊆ G.seamCollar j :=
  Set.range_subset_iff.mpr (G.seamTorus_mem_seamCollar j)

private theorem snd_eq_zero_of_mem_seamSurface {p : Torus × ℝ} (hp : p ∈ signedCollarSource)
    (h : G.seam j p ∈ G.seamSurface j) : p.2 = 0 := by
  obtain ⟨t, ht⟩ := h
  rw [← (G.seam j).toPartialEquiv.injOn
    (G.mem_seam_source j (zero_mem_signedCollarSource t)) (G.mem_seam_source j hp) ht]

private theorem prod_Ioo_subset {a b : ℝ} (ha : -1 ≤ a) (hb : b ≤ 1) :
    (Set.univ : Set Torus) ×ˢ Set.Ioo a b ⊆ signedCollarSource :=
  fun _ hp => ⟨lt_of_le_of_lt ha hp.2.1, lt_of_lt_of_le hp.2.2 hb⟩

private theorem isPathConnected_seam_image {a b : ℝ} (ha : -1 ≤ a) (hab : a < b)
    (hb : b ≤ 1) : IsPathConnected (G.seam j '' ((Set.univ : Set Torus) ×ˢ Set.Ioo a b)) :=
  (isPathConnected_univ.prod ((convex_Ioo a b).isPathConnected (Set.nonempty_Ioo.mpr hab))).image'
    ((G.continuousOn_seam j).mono fun _ hp => G.mem_seam_source j (prod_Ioo_subset ha hb hp))

private theorem seam_image_subset_compl {a b : ℝ} (ha : -1 ≤ a) (hb : b ≤ 1)
    (h0 : (0 : ℝ) ∉ Set.Ioo a b) :
    G.seam j '' ((Set.univ : Set Torus) ×ˢ Set.Ioo a b) ⊆ (G.seamSurface j)ᶜ := by
  rintro _ ⟨p, hp, rfl⟩ hs
  apply h0
  rw [← G.snd_eq_zero_of_mem_seamSurface j (prod_Ioo_subset ha hb hp) hs]
  exact hp.2

theorem isPathConnected_seamCollar : IsPathConnected (G.seamCollar j) := by
  have h : G.seamCollar j = G.seam j '' ((Set.univ : Set Torus) ×ˢ Set.Ioo (-1) 1) := by
    rw [seamCollar, ← (G.seam j).toPartialEquiv.image_source_eq_target]
    congr 1
    rw [G.seam_source j]
    ext p
    simp [signedCollarSource]
  rw [h]
  exact G.isPathConnected_seam_image j le_rfl (by norm_num) le_rfl

def leftPoint : W.Carrier := G.seam j ((1, 1), -2⁻¹)

def rightPoint : W.Carrier := G.seam j ((1, 1), 2⁻¹)

private theorem leftPoint_mem_image :
    G.leftPoint j ∈ G.seam j '' ((Set.univ : Set Torus) ×ˢ Set.Ioo (-1) 0) :=
  ⟨_, ⟨trivial, by norm_num, by norm_num⟩, rfl⟩

private theorem rightPoint_mem_image :
    G.rightPoint j ∈ G.seam j '' ((Set.univ : Set Torus) ×ˢ Set.Ioo 0 1) :=
  ⟨_, ⟨trivial, by norm_num, by norm_num⟩, rfl⟩

def leftSide : Set W.Carrier := pathComponentIn (G.seamSurface j)ᶜ (G.leftPoint j)

def rightSide : Set W.Carrier := pathComponentIn (G.seamSurface j)ᶜ (G.rightPoint j)

def IsSeparating : Prop := Disjoint (G.leftSide j) (G.rightSide j)

def leftRegion : Set W.Carrier := G.leftSide j ∪ G.seamCollar j

def rightRegion : Set W.Carrier := G.rightSide j ∪ G.seamCollar j

private theorem negative_subset_leftSide :
    G.seam j '' ((Set.univ : Set Torus) ×ˢ Set.Ioo (-1) 0) ⊆ G.leftSide j :=
  (G.isPathConnected_seam_image j le_rfl (by norm_num) (by norm_num)).subset_pathComponentIn
    (G.leftPoint_mem_image j) (G.seam_image_subset_compl j le_rfl (by norm_num) (by simp))

private theorem positive_subset_rightSide :
    G.seam j '' ((Set.univ : Set Torus) ×ˢ Set.Ioo 0 1) ⊆ G.rightSide j :=
  (G.isPathConnected_seam_image j (by norm_num) (by norm_num) le_rfl).subset_pathComponentIn
    (G.rightPoint_mem_image j) (G.seam_image_subset_compl j (by norm_num) le_rfl (by simp))

theorem leftPoint_mem_compl : G.leftPoint j ∈ (G.seamSurface j)ᶜ :=
  G.seam_image_subset_compl j le_rfl (by norm_num) (by simp) (G.leftPoint_mem_image j)

theorem rightPoint_mem_compl : G.rightPoint j ∈ (G.seamSurface j)ᶜ :=
  G.seam_image_subset_compl j (by norm_num) le_rfl (by simp) (G.rightPoint_mem_image j)

theorem leftPoint_mem_seamCollar : G.leftPoint j ∈ G.seamCollar j :=
  (G.seam j).map_source' (G.mem_seam_source j ⟨by norm_num, by norm_num⟩)

theorem rightPoint_mem_seamCollar : G.rightPoint j ∈ G.seamCollar j :=
  (G.seam j).map_source' (G.mem_seam_source j ⟨by norm_num, by norm_num⟩)

theorem isSeparating_iff : G.IsSeparating j ↔ G.rightPoint j ∉ G.leftSide j := by
  constructor
  · intro h hr
    exact Set.disjoint_left.mp h hr (mem_pathComponentIn_self (G.rightPoint_mem_compl j))
  · intro h
    rw [IsSeparating, Set.disjoint_left]
    intro x hl hr
    apply h
    rw [leftSide, ← pathComponentIn_congr hl, pathComponentIn_congr hr]
    exact mem_pathComponentIn_self (G.rightPoint_mem_compl j)

theorem isOpen_leftRegion : IsOpen (G.leftRegion j) :=
  haveI := Manifold.locallyPathConnectedSpace_of_modelWithCorners (M := W.Carrier) W.model
  ((G.isClosed_seamSurface j).isOpen_compl.pathComponentIn _).union (G.isOpen_seamCollar j)

theorem isOpen_rightRegion : IsOpen (G.rightRegion j) :=
  haveI := Manifold.locallyPathConnectedSpace_of_modelWithCorners (M := W.Carrier) W.model
  ((G.isClosed_seamSurface j).isOpen_compl.pathComponentIn _).union (G.isOpen_seamCollar j)

theorem isPathConnected_leftRegion : IsPathConnected (G.leftRegion j) :=
  (isPathConnected_pathComponentIn (G.leftPoint_mem_compl j)).union
    (G.isPathConnected_seamCollar j)
    ⟨G.leftPoint j, mem_pathComponentIn_self (G.leftPoint_mem_compl j),
      G.leftPoint_mem_seamCollar j⟩

theorem isPathConnected_rightRegion : IsPathConnected (G.rightRegion j) :=
  (isPathConnected_pathComponentIn (G.rightPoint_mem_compl j)).union
    (G.isPathConnected_seamCollar j)
    ⟨G.rightPoint j, mem_pathComponentIn_self (G.rightPoint_mem_compl j),
      G.rightPoint_mem_seamCollar j⟩

private theorem pathComponentIn_meets_seamCollar [ConnectedSpace W.Carrier] {y : W.Carrier}
    (hy : y ∈ (G.seamSurface j)ᶜ) :
    (pathComponentIn (G.seamSurface j)ᶜ y ∩ G.seamCollar j).Nonempty := by
  have := Manifold.locallyPathConnectedSpace_of_modelWithCorners (M := W.Carrier) W.model
  by_contra hne
  have hO : IsOpen (G.seamSurface j)ᶜ := (G.isClosed_seamSurface j).isOpen_compl
  have hclosed : IsClosed (pathComponentIn (G.seamSurface j)ᶜ y) := by
    rw [← closure_subset_iff_isClosed]
    intro z hz
    by_cases hzU : z ∈ G.seamCollar j
    · obtain ⟨w, hwU, hwC⟩ := mem_closure_iff.mp hz _ (G.isOpen_seamCollar j) hzU
      exact (hne ⟨w, hwC, hwU⟩).elim
    · have hzO : z ∈ (G.seamSurface j)ᶜ := fun h => hzU (G.seamSurface_subset_seamCollar j h)
      obtain ⟨w, hwz, hwC⟩ :=
        mem_closure_iff.mp hz _ (hO.pathComponentIn z) (mem_pathComponentIn_self hzO)
      rw [← pathComponentIn_congr hwC, pathComponentIn_congr hwz]
      exact mem_pathComponentIn_self hzO
  have huniv := IsClopen.eq_univ ⟨hclosed, hO.pathComponentIn y⟩
    ⟨y, mem_pathComponentIn_self hy⟩
  have hmem : G.seamTorus j (1, 1) ∈ pathComponentIn (G.seamSurface j)ᶜ y :=
    huniv ▸ Set.mem_univ _
  exact pathComponentIn_subset hmem ⟨(1, 1), rfl⟩

theorem mem_leftSide_or_mem_rightSide [ConnectedSpace W.Carrier] {y : W.Carrier}
    (hy : y ∈ (G.seamSurface j)ᶜ) : y ∈ G.leftSide j ∨ y ∈ G.rightSide j := by
  obtain ⟨w, hwC, hwU⟩ := G.pathComponentIn_meets_seamCollar j hy
  have hwO : w ∈ (G.seamSurface j)ᶜ := pathComponentIn_subset hwC
  rw [seamCollar, ← (G.seam j).toPartialEquiv.image_source_eq_target] at hwU
  obtain ⟨p, hp, rfl⟩ := hwU
  have hp' : p ∈ signedCollarSource := G.seam_source j ▸ hp
  have hne : p.2 ≠ 0 := fun h0 => hwO ⟨p.1, by rw [seamTorus_apply, ← h0]⟩
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hw : G.seam j p ∈ G.leftSide j :=
      G.negative_subset_leftSide j ⟨p, ⟨trivial, hp'.1, hneg⟩, rfl⟩
    left
    rw [leftSide, ← pathComponentIn_congr hw, pathComponentIn_congr hwC]
    exact mem_pathComponentIn_self hy
  · have hw : G.seam j p ∈ G.rightSide j :=
      G.positive_subset_rightSide j ⟨p, ⟨trivial, hpos, hp'.2⟩, rfl⟩
    right
    rw [rightSide, ← pathComponentIn_congr hw, pathComponentIn_congr hwC]
    exact mem_pathComponentIn_self hy

theorem compl_seamSurface_eq [ConnectedSpace W.Carrier] :
    (G.seamSurface j)ᶜ = G.leftSide j ∪ G.rightSide j := by
  ext y
  refine ⟨G.mem_leftSide_or_mem_rightSide j, ?_⟩
  rintro (hy | hy)
  · exact pathComponentIn_subset hy
  · exact pathComponentIn_subset hy

theorem leftRegion_union_rightRegion [ConnectedSpace W.Carrier] :
    G.leftRegion j ∪ G.rightRegion j = Set.univ := by
  refine Set.eq_univ_of_forall fun y => ?_
  by_cases hyU : y ∈ G.seamCollar j
  · exact Or.inl (Or.inr hyU)
  rcases G.mem_leftSide_or_mem_rightSide j
    (fun h => hyU (G.seamSurface_subset_seamCollar j h)) with hy | hy
  · exact Or.inl (Or.inl hy)
  · exact Or.inr (Or.inl hy)

theorem leftRegion_inter_rightRegion (h : G.IsSeparating j) :
    G.leftRegion j ∩ G.rightRegion j = G.seamCollar j := by
  ext x
  constructor
  · rintro ⟨hl | hl, hr | hr⟩
    · exact (Set.disjoint_left.mp h hl hr).elim
    all_goals assumption
  · intro hx
    exact ⟨Or.inr hx, Or.inr hx⟩

instance pathConnectedSpace_leftRegion : PathConnectedSpace (G.leftRegion j) :=
  isPathConnected_iff_pathConnectedSpace.mp (G.isPathConnected_leftRegion j)

instance pathConnectedSpace_rightRegion : PathConnectedSpace (G.rightRegion j) :=
  isPathConnected_iff_pathConnectedSpace.mp (G.isPathConnected_rightRegion j)

theorem pathConnectedSpace_inter (h : G.IsSeparating j) :
    PathConnectedSpace ↑(G.leftRegion j ∩ G.rightRegion j) := by
  rw [← isPathConnected_iff_pathConnectedSpace, G.leftRegion_inter_rightRegion j h]
  exact G.isPathConnected_seamCollar j

theorem seamTorus_mem_inter (t : Torus) :
    G.seamTorus j t ∈ G.leftRegion j ∩ G.rightRegion j :=
  ⟨Or.inr (G.seamTorus_mem_seamCollar j t), Or.inr (G.seamTorus_mem_seamCollar j t)⟩

def seamVanKampen [ConnectedSpace W.Carrier] (h : G.IsSeparating j) (t : Torus) :
    fundamentalGroupAmalgamatedProduct (G.leftRegion j) (G.rightRegion j) (G.seamTorus j t)
        (G.seamTorus_mem_inter j t) ≃*
      FundamentalGroup W.Carrier (G.seamTorus j t) :=
  haveI := G.pathConnectedSpace_inter j h
  fundamentalGroupEquivAmalgamatedProduct _ _ (G.isOpen_leftRegion j) (G.isOpen_rightRegion j)
    (G.leftRegion_union_rightRegion j) _ _

def seamTorusToLeft : C(Torus, G.leftRegion j) :=
  G.seamTorusIn j _ Set.subset_union_right

def seamTorusToRight : C(Torus, G.rightRegion j) :=
  G.seamTorusIn j _ Set.subset_union_right

theorem injective_seamTorus [ConnectedSpace W.Carrier] (h : G.IsSeparating j) (t₀ : Torus)
    (hl : Function.Injective (FundamentalGroup.map (G.seamTorusToLeft j) t₀))
    (hr : Function.Injective (FundamentalGroup.map (G.seamTorusToRight j) t₀)) (t : Torus) :
    Function.Injective (FundamentalGroup.map (G.seamTorus j) t) := by
  have := G.pathConnectedSpace_inter j h
  rw [GC.Topology.injective_fundamentalGroup_map_iff (G.seamTorus j) t t₀]
  have hinter := G.leftRegion_inter_rightRegion j h
  exact injective_fundamentalGroup_map_of_openCover _ _ (G.isOpen_leftRegion j)
    (G.isOpen_rightRegion j) (G.leftRegion_union_rightRegion j) (G.seamTorusIn j _ hinter.ge) t₀
    (G.bijective_seamTorusIn j _ hinter t₀).2 hl hr

private theorem injective_inter_maps [ConnectedSpace W.Carrier] (h : G.IsSeparating j)
    (t₀ : Torus) (hl : Function.Injective (FundamentalGroup.map (G.seamTorusToLeft j) t₀))
    (hr : Function.Injective (FundamentalGroup.map (G.seamTorusToRight j) t₀)) :
    Function.Injective (FundamentalGroup.map (interToLeft (G.leftRegion j) (G.rightRegion j))
        (G.seamTorusIn j _ (G.leftRegion_inter_rightRegion j h).ge t₀)) ∧
      Function.Injective (FundamentalGroup.map (interToRight (G.leftRegion j) (G.rightRegion j))
        (G.seamTorusIn j _ (G.leftRegion_inter_rightRegion j h).ge t₀)) :=
  ⟨injective_of_surjective_comp _ _ t₀
      (G.bijective_seamTorusIn j _ (G.leftRegion_inter_rightRegion j h) t₀).2 hl,
    injective_of_surjective_comp _ _ t₀
      (G.bijective_seamTorusIn j _ (G.leftRegion_inter_rightRegion j h) t₀).2 hr⟩

theorem injective_leftRegion [ConnectedSpace W.Carrier] (h : G.IsSeparating j) (t₀ : Torus)
    (hl : Function.Injective (FundamentalGroup.map (G.seamTorusToLeft j) t₀))
    (hr : Function.Injective (FundamentalGroup.map (G.seamTorusToRight j) t₀)) :
    Function.Injective
      (FundamentalGroup.map (subsetToAmbient (G.leftRegion j)) (G.seamTorusToLeft j t₀)) := by
  have := G.pathConnectedSpace_inter j h
  have hi := G.injective_inter_maps j h t₀ hl hr
  exact injective_fundamentalGroup_map_left _ _ (G.isOpen_leftRegion j) (G.isOpen_rightRegion j)
    (G.leftRegion_union_rightRegion j) _ hi.1 hi.2

theorem injective_rightRegion [ConnectedSpace W.Carrier] (h : G.IsSeparating j) (t₀ : Torus)
    (hl : Function.Injective (FundamentalGroup.map (G.seamTorusToLeft j) t₀))
    (hr : Function.Injective (FundamentalGroup.map (G.seamTorusToRight j) t₀)) :
    Function.Injective
      (FundamentalGroup.map (subsetToAmbient (G.rightRegion j)) (G.seamTorusToRight j t₀)) := by
  have := G.pathConnectedSpace_inter j h
  have hi := G.injective_inter_maps j h t₀ hl hr
  exact injective_fundamentalGroup_map_right _ _ (G.isOpen_leftRegion j)
    (G.isOpen_rightRegion j) (G.leftRegion_union_rightRegion j) _ hi.1 hi.2

section Closed
variable {P : ConnectedClosedOrientedManifold.{u} 3} (T : TorusPresentation (NoCuts.carrier P))

theorem toTorusDecomposition_torusInPrime_eq (i : Fin T.pairing.count) :
    T.toTorusDecomposition.reconstructionAtlas.torusInPrime T.toTorusDecomposition.reconstruction
      i = T.seamTorus i :=
  ContinuousMap.ext (T.toTorusDecomposition_torusInPrime i)

theorem injective_torusInPrime (i : Fin T.pairing.count) (h : T.IsSeparating i) (t₀ : Torus)
    (hl : Function.Injective (FundamentalGroup.map (T.seamTorusToLeft i) t₀))
    (hr : Function.Injective (FundamentalGroup.map (T.seamTorusToRight i) t₀)) (x : Torus) :
    Function.Injective (FundamentalGroup.map
      (T.toTorusDecomposition.reconstructionAtlas.torusInPrime
        T.toTorusDecomposition.reconstruction i) x) := by
  rw [T.toTorusDecomposition_torusInPrime_eq i]
  exact T.injective_seamTorus i h t₀ hl hr x

theorem incompressible_toTorusDecomposition (hsep : ∀ i, T.IsSeparating i)
    (hl : ∀ i, Function.Injective (FundamentalGroup.map (T.seamTorusToLeft i) (1, 1)))
    (hr : ∀ i, Function.Injective (FundamentalGroup.map (T.seamTorusToRight i) (1, 1))) :
    T.toTorusDecomposition.reconstructionAtlas.Incompressible
      T.toTorusDecomposition.reconstruction :=
  fun i x => T.injective_torusInPrime i (hsep i) (1, 1) (hl i) (hr i) x

end Closed

end TorusPresentation
end GC.Seifert
