/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.EmbeddedDisk
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.LemmaTwo

/-!
# Reading a nonsingular two cell of the double back as an embedded disk

The surgery half of Moise's Lemma 2 works with a `SingularTwoCell` of `(double 3 K).space`, where
`K` is the manifold complex of a normal system `S`, and ends with a cell that is injective on its
source disk.  `NormalSystem.EmbeddedDisk S` instead wants a proper piecewise linear embedded disk
inside `S.manifoldComplex`.  `NormalSystem.exists_embeddedDisk_of_nonsingular_two_cell_in_double`
is the conversion; `exists_nonsingular_two_cell_of_disk_in_double_boundary_eqOn` goes the other
way.

## What the conversion consumes

Besides injectivity, three things.

* The image of the cell stays in the copy `ι '' K.space` of `|K|` inside the double.  This is a
  genuine extra hypothesis: the double carries two copies of `|K|`, a `NormalSingularCellData`
  says nothing about which one the cell meets, and the whole construction below is the transport
  of the cell along the inverse of `ι`, so it cannot be dropped.  Whatever produces the cell has
  to carry this along.
* The trace of the cell on the seam is exactly its boundary circle.  This is
  `NormalSingularCellData.image_inter_boundary` for
  `BdM = Subtype.val ⁻¹' (ι '' (boundaryComplex 3 K).space)`, taken verbatim; together with
  injectivity it is what gives properness of the resulting disk.  No other field of a
  `NormalSingularCellData` is used.
* A parametrisation of the boundary circle by a free loop `δ` of `S.boundaryNeighborhoodSpace`
  whose class avoids `S.normalSubgroup`.  The clause `∀ θ, ρ (δ θ) = D (c θ)` produced by the
  induction, with `ρ` the evident map through `ι`, is equivalent to the clause below by
  `Subtype.ext`, so no adapter is needed beyond that.

## Supporting results

`isPiecewiseAffineOn_val_comp_of_isPLOn` reads a piecewise linear map into a combinatorially
charted complex in the ambient coordinates; it is the missing direction of `PLPieceIn.isPLOn_comp`
for this charted structure, and it is what lets the cell be fed to `exists_isPLHomeomorphOn_image`.
`normalSystemLoopConjugacyClass_eq_conjugacyClass` identifies the two spellings of the avoidance
condition used on the two sides of the conversion.

`NormalSystem.exists_embeddedDisk_of_isNonsingular` is the non-vacuity check: the cell that
`NormalSystem.exists_singular_two_cell_in_double` produces for a nonsingular normal system
satisfies all four hypotheses at once, and the conversion recovers an embedded disk from it.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

/-- The class of a free loop taken along a connecting path is its free homotopy conjugacy class.
The connecting path plays no role, so the avoidance condition of a normal system, written with
`normalSystemLoopConjugacyClass`, is the negation of `loopClassMeets`. -/
theorem normalSystemLoopConjugacyClass_eq_conjugacyClass {X : Type*} [TopologicalSpace X]
    [PathConnectedSpace X] {x : X} (γ : freeLoop X) (q : Path x (γ 0)) :
    normalSystemLoopConjugacyClass x γ q = FreeLoop.conjugacyClass γ x :=
  (FreeLoop.conjugacyClass_eq_mk_loopRepresentativeAlong q ⟨γ, rfl⟩).symm

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- A piecewise linear map of a subset of a model space into a combinatorial manifold complex is
piecewise affine when read in the ambient coordinates of the complex.  The vertex chart inverse is
piecewise affine on its target, so composing it with the chart description of the map recovers the
map itself near each point. -/
theorem isPiecewiseAffineOn_val_comp_of_isPLOn {n m : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold (n + 1) K) (s : Set (EuclideanSpace ℝ (Fin m))) :
    letI := combinatorialChartedSpace K hK
    ∀ f : EuclideanSpace ℝ (Fin m) → K.space, IsPLOn m (n + 1) f s →
      IsPiecewiseAffineOn (fun x => (f x : E)) s := by
  classical
  let _ := combinatorialChartedSpace K hK
  intro f hf x hx
  obtain ⟨hcont, hchart⟩ := (StructureGroupoid.liftPropWithinAt_self_source).mp (hf x hx)
  obtain ⟨p, hp, hpe⟩ := mem_combinatorialChartedSpace_atlas K hK
    (chart_mem_atlas (EuclideanSpace ℝ (Fin (n + 1))) (f x))
  have hchart' : IsPiecewiseAffineWithinAt
      ((chartAt (EuclideanSpace ℝ (Fin (n + 1))) (f x) :
        K.space → EuclideanSpace ℝ (Fin (n + 1))) ∘ f) s x := hchart
  have hxsrc : f x ∈ (chartAt (EuclideanSpace ℝ (Fin (n + 1))) (f x)).source :=
    mem_chart_source _ _
  rw [hpe] at hchart' hxsrc
  have hsymm := isPiecewiseAffineOn_vertexChart_symm K hp (hK.isPLSphere_link hp)
  set c := vertexChart K hp (hK.isPLSphere_link hp)
  have hcomp := IsPiecewiseAffineWithinAt.comp
    (f := (c : K.space → EuclideanSpace ℝ (Fin (n + 1))) ∘ f) (x := x) (s := s)
    (hsymm _ (c.map_source hxsrc)) hchart'
  obtain ⟨O, hO, hxO, hOsub⟩ := mem_nhdsWithin.mp
    (hcont.preimage_mem_nhdsWithin (c.open_source.mem_nhds hxsrc))
  have hlocal := hcomp.inter_of_mem_nhds (hO.mem_nhds hxO)
  have hsetEq :
      (s ∩ ((c : K.space → EuclideanSpace ℝ (Fin (n + 1))) ∘ f) ⁻¹' c.target) ∩ O = s ∩ O := by
    refine Subset.antisymm (inter_subset_inter_left _ inter_subset_left) ?_
    rintro z ⟨hzs, hzO⟩
    exact ⟨⟨hzs, c.map_source (hOsub ⟨hzO, hzs⟩)⟩, hzO⟩
  rw [hsetEq] at hlocal
  refine IsPiecewiseAffineWithinAt.of_inter_of_mem_nhds (hlocal.congr ?_) (hO.mem_nhds hxO)
  intro z hz
  have hzs : f z ∈ c.source := hOsub ⟨hz.2, hz.1⟩
  change ((f z : K.space) : E) = ((c.symm (c (f z)) : K.space) : E)
  rw [c.left_inv hzs]

namespace NormalSystem

open Classical in
/-- A nonsingular singular two cell of the double of the manifold complex of a normal system `S`,
whose image lies in the copy of `|S.manifoldComplex|`, whose trace on the seam is exactly its
boundary circle, and whose boundary circle is parametrised by a free loop of
`S.boundaryNeighborhoodSpace` avoiding `S.normalSubgroup`, is an embedded disk of `S`.

The map of the disk is the cell transported back along the inverse of the embedding `ι` of
`|S.manifoldComplex|` into the double; this is why the second hypothesis, which is not part of a
`NormalSingularCellData`, is needed.  The third hypothesis is
`NormalSingularCellData.image_inter_boundary` for the seam, and the fourth is the loop clause of
the complexity induction, with `∀ θ, ρ (δ θ) = D (c θ)` spelled out in ambient coordinates.

Path connectedness of the boundary neighborhood is an instance hypothesis because it is what
`loopClassMeets` needs; over `E : Type` it is supplied by
`NormalSystem.boundaryNeighborhoodPathConnectedSpace`. -/
theorem exists_embeddedDisk_of_nonsingular_two_cell_in_double (S : NormalSystem E)
    [PathConnectedSpace S.boundaryNeighborhoodSpace] :
    let K := S.manifoldComplex
    letI : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
    letI := combinatorialChartedSpace (double 3 K)
      (isCombinatorialManifold_double_succ_succ K S.isManifold)
    let ι := simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)
    ∀ D : SingularTwoCell (double 3 K).space, D.IsNonsingular →
      Subtype.val '' (D '' D.domain) ⊆ ι '' K.space →
      D '' D.domain ∩
          Subtype.val ⁻¹' (ι '' (PiecewiseLinear.boundaryComplex 3 K).space) =
        Set.range D.boundary →
      (∃ (c : loopCircle ≃ₜ frontier D.domain) (δ : freeLoop S.boundaryNeighborhoodSpace),
        (∀ θ, ((D (c θ) : (double 3 K).space) : E × E × ℝ) = ι (δ θ)) ∧
          ¬loopClassMeets δ S.basepoint S.normalSubgroup) →
      Nonempty (EmbeddedDisk S) := by
  classical
  let K := S.manifoldComplex
  let _ : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
  let L := double 3 K
  have hL : IsCombinatorialManifold 3 L :=
    isCombinatorialManifold_double_succ_succ K S.isManifold
  let _ := combinatorialChartedSpace L hL
  let B := PiecewiseLinear.boundaryComplex 3 K
  let ι : E → E × E × ℝ := simplicialMap K (glueEmbed₂ B id)
  dsimp only
  intro D hinj himg hbd hloop
  obtain ⟨c, δ, hcδ, hδN⟩ := hloop
  have hι : IsPLHomeomorphOn ι K.space (glued₂ K B id).space :=
    isPLHomeomorphOn_embedComplex K (glueEmbed₂ B id) (glueSnd E E) (fun _ _ _ _ => rfl)
  let g := Function.invFunOn ι K.space
  have hgι : ∀ y ∈ K.space, g (ι y) = y := fun _ hy => hι.bijOn.invOn_invFunOn.1 hy
  let f : EuclideanSpace ℝ (Fin 2) → E := fun x => g ((D x : L.space) : E × E × ℝ)
  have hmapmem : ∀ x ∈ D.domain, f x ∈ K.space ∧
      ι (f x) = ((D x : L.space) : E × E × ℝ) := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := himg ⟨D x, ⟨x, hx, rfl⟩, rfl⟩
    have hfx : f x = y := by
      change g ((D x : L.space) : E × E × ℝ) = y
      rw [← hyx]
      exact hgι y hy
    rw [hfx]
    exact ⟨hy, hyx⟩
  -- the cell, read in the ambient coordinates of the double, is a piecewise linear embedding
  have hval : IsPiecewiseAffineOn (fun x => ((D x : L.space) : E × E × ℝ)) D.domain :=
    isPiecewiseAffineOn_val_comp_of_isPLOn L hL D.domain D.toFun D.isPLOn
  have hvalinj : InjOn (fun x => ((D x : L.space) : E × E × ℝ)) D.domain :=
    fun _ ha _ hb hab => hinj ha hb (Subtype.ext hab)
  obtain ⟨P, hPfin, hPspace⟩ := D.isPLBall_domain.isPolyhedron.exists_simplicialComplex
  let _ : Finite P.faces := hPfin.to_subtype
  have hvalP : IsPiecewiseAffineOn (fun x => ((D x : L.space) : E × E × ℝ)) P.space := by
    rw [hPspace]; exact hval
  have hvalinjP : InjOn (fun x => ((D x : L.space) : E × E × ℝ)) P.space := by
    rw [hPspace]; exact hvalinj
  obtain ⟨Q, -, hQspace, hQ⟩ := exists_isPLHomeomorphOn_image P hvalP hvalinjP
  rw [hPspace] at hQspace hQ
  have hQpoly : IsPolyhedron Q.space := (D.isPLBall_domain.of_isPLHomeomorphOn hQ).isPolyhedron
  have hQsub : Q.space ⊆ (glued₂ K B id).space := by
    rw [hQspace, ← hι.image_eq]
    rintro _ ⟨x, hx, rfl⟩
    exact himg ⟨D x, ⟨x, hx, rfl⟩, rfl⟩
  have hg : IsPLHomeomorphOn g Q.space (g '' Q.space) := hι.symm.restrict hQpoly hQsub
  have hfPL : IsPLHomeomorphOn f D.domain (f '' D.domain) := by
    have h := hQ.trans hg
    have himage : f '' D.domain = g '' Q.space := h.image_eq
    rw [himage]
    exact h
  -- the boundary circle
  have hnbhdK : ∀ z : S.boundaryNeighborhoodSpace, (z : E) ∈ K.space := by
    intro z
    exact PiecewiseLinear.boundaryComplex_space_subset 3 K
      (derivedNeighborhood_space_subset S.boundaryComplex S.loopComplex z.2)
  have hfc : ∀ θ, f (c θ) = (δ θ : E) := by
    intro θ
    change g ((D (c θ) : L.space) : E × E × ℝ) = (δ θ : E)
    rw [hcδ θ]
    exact hgι _ (hnbhdK (δ θ))
  have hbrange : Set.range (fun θ => ((δ θ : S.boundaryNeighborhoodSpace) : E)) =
      f '' frontier D.domain := by
    apply Subset.antisymm
    · rintro _ ⟨θ, rfl⟩
      exact ⟨((c θ : frontier D.domain) : EuclideanSpace ℝ (Fin 2)), (c θ).2, hfc θ⟩
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨θ, hθ⟩ := c.surjective ⟨x, hx⟩
      have hxθ : ((c θ : frontier D.domain) : EuclideanSpace ℝ (Fin 2)) = x :=
        congrArg Subtype.val hθ
      refine ⟨θ, ?_⟩
      change ((δ θ : S.boundaryNeighborhoodSpace) : E) = f x
      rw [← hfc θ, hxθ]
  -- properness
  have hmemB : ∀ x ∈ D.domain,
      (f x ∈ B.space ↔ ((D x : L.space) : E × E × ℝ) ∈ ι '' B.space) := by
    intro x hx
    obtain ⟨hxK, hxι⟩ := hmapmem x hx
    refine ⟨fun h => ⟨f x, h, hxι⟩, ?_⟩
    rintro ⟨b, hb, hbx⟩
    have hbf : ι b = ι (f x) := hbx.trans hxι.symm
    have hbK : b ∈ K.space := PiecewiseLinear.boundaryComplex_space_subset 3 K hb
    rwa [hι.bijOn.injOn hbK hxK hbf] at hb
  have hpre : D.domain ∩ f ⁻¹' B.space = frontier D.domain := by
    apply Subset.antisymm
    · rintro x ⟨hx, hxB⟩
      have hDx : D x ∈ Set.range D.boundary := by
        rw [← hbd]
        exact ⟨⟨x, hx, rfl⟩, (hmemB x hx).mp hxB⟩
      obtain ⟨w, hw⟩ := hDx
      have hwx : (w : EuclideanSpace ℝ (Fin 2)) = x :=
        hinj (D.frontier_subset_domain w.2) hx hw
      exact hwx ▸ w.2
    · intro x hx
      have hxd : x ∈ D.domain := D.frontier_subset_domain hx
      have hDx : D x ∈ D '' D.domain ∩
          Subtype.val ⁻¹' (ι '' (PiecewiseLinear.boundaryComplex 3 K).space) := by
        rw [hbd]
        exact ⟨⟨x, hx⟩, rfl⟩
      exact ⟨hxd, (hmemB x hxd).mpr hDx.2⟩
  exact ⟨{ domain := D.domain
           isPLBall_domain := D.isPLBall_domain
           map := f
           isPLHomeomorphOn := hfPL
           mapsTo := fun x hx => (hmapmem x hx).1
           boundaryLoop := δ
           boundary_range := hbrange
           boundary_preimage := hpre
           connector := PathConnectedSpace.somePath S.basepoint (δ 0)
           loopClass_avoids_normal := by
             rw [normalSystemLoopConjugacyClass_eq_conjugacyClass]
             exact hδN }⟩

end NormalSystem

end General

section Euclidean

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

namespace NormalSystem

open Classical in
/-- Non-vacuity of the conversion: the singular two cell that
`NormalSystem.exists_singular_two_cell_in_double` produces for a nonsingular normal system meets
all four hypotheses of `exists_embeddedDisk_of_nonsingular_two_cell_in_double` simultaneously, so
a nonsingular normal system has a proper piecewise linear embedded disk.  The boundary circle of
the disk is the boundary loop of `S` itself, which avoids `S.normalSubgroup`, so the disk is not
degenerate. -/
theorem exists_embeddedDisk_of_isNonsingular (S : NormalSystem E) (hS : S.IsNonsingular) :
    Nonempty (EmbeddedDisk S) := by
  classical
  let K := S.manifoldComplex
  let _ : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
  let L := double 3 K
  have hL : IsCombinatorialManifold 3 L :=
    isCombinatorialManifold_double_succ_succ K S.isManifold
  let _ := combinatorialChartedSpace L hL
  let _ : PathConnectedSpace S.boundaryNeighborhoodSpace :=
    S.boundaryNeighborhoodPathConnectedSpace
  let B := PiecewiseLinear.boundaryComplex 3 K
  let ι : E → E × E × ℝ := simplicialMap K (glueEmbed₂ B id)
  obtain ⟨D, hdom, -, hDimg, hDbd, hDinter, hparam, hns⟩ := S.exists_singular_two_cell_in_double
  have himg : Subtype.val '' (D '' D.domain) ⊆ ι '' K.space := by
    rw [hDimg]
    exact image_mono S.image_space_subset_manifoldComplex
  have hkey : Subtype.val '' (D '' D.domain ∩ Subtype.val ⁻¹' (ι '' B.space)) =
      Subtype.val '' (Set.range D.boundary) := by
    rw [image_inter_preimage, hDinter, ← hDbd]
    exact range_comp _ _
  have hbd : D '' D.domain ∩ Subtype.val ⁻¹' (ι '' B.space) = Set.range D.boundary := by
    have h := congrArg (Set.preimage (Subtype.val : L.space → E × E × ℝ)) hkey
    rwa [preimage_image_eq _ Subtype.val_injective,
      preimage_image_eq _ Subtype.val_injective] at h
  let e : loopCircle ≃ₜ frontier D.domain :=
    S.boundaryParam.trans (Homeomorph.setCongr (congrArg frontier hdom.symm))
  have hcδ : ∀ θ, ((D (e θ) : L.space) : E × E × ℝ) = ι (S.boundaryLoop θ) := hparam
  have hδN : ¬loopClassMeets S.boundaryLoop S.basepoint S.normalSubgroup := by
    intro h
    refine S.loopClass_avoids_normal ?_
    rw [normalSystemLoopConjugacyClass_eq_conjugacyClass]
    exact h
  exact S.exists_embeddedDisk_of_nonsingular_two_cell_in_double D (hns.mpr hS) himg hbd
    ⟨e, S.boundaryLoop, hcδ, hδN⟩

end NormalSystem

end Euclidean

end DifferentialGeometry.Topology.PiecewiseLinear
