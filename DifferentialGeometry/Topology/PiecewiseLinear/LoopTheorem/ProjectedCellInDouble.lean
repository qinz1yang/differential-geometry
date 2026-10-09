/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BoundaryDouble
import DifferentialGeometry.Topology.PiecewiseLinear.CombinatorialPiece
import DifferentialGeometry.Topology.PiecewiseLinear.PieceMap
import DifferentialGeometry.Topology.PiecewiseLinear.LoopTheorem.ProjectedDoublePoints

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

open Classical in
theorem DoubleCoverDiagram.exists_projected_singular_two_cell_in_double
    {S : NormalSystem E} {T : NormalSystem F} (R : DoubleCoverDiagram S T)
    (D : EmbeddedDisk T) :
    let K := S.manifoldComplex
    letI : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
    letI := combinatorialChartedSpace (double 3 K)
      (isCombinatorialManifold_double_succ_succ K S.isManifold)
    let ι := simplicialMap K (glueEmbed₂ (PiecewiseLinear.boundaryComplex 3 K) id)
    let C := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹' (ι '' K.space)
    let Bd := ((↑) : (double 3 K).space → E × E × ℝ) ⁻¹'
      (ι '' (PiecewiseLinear.boundaryComplex 3 K).space)
    ∃ (G : SingularTwoCell (double 3 K).space) (γ : freeLoop S.boundaryNeighborhoodSpace)
      (q : Path S.basepoint (γ 0)),
      G.domain = D.domain ∧ γ = R.boundaryMap.comp D.boundaryLoop ∧
      EqOn (fun x => (G x : E × E × ℝ)) (ι ∘ R.projection ∘ D.map) D.domain ∧
      MapsTo G G.domain C ∧ frontier C = Bd ∧
      G.domain ∩ G ⁻¹' Bd = frontier G.domain ∧
      G '' G.domain ∩ frontier C = range G.boundary ∧
      range (fun x => (G.boundary x : E × E × ℝ)) =
        ι '' range (fun θ => (γ θ : E)) ∧
      ¬conjugacyClassMeets (normalSystemLoopConjugacyClass S.basepoint γ q) S.normalSubgroup ∧
      (∀ x ∈ D.domain, G.domain ∩ G ⁻¹' {G x} =
        D.domain ∩ (R.projection ∘ D.map) ⁻¹' {R.projection (D.map x)}) ∧
      IsLocallyInjective (G.domain.domRestrict G) ∧
      (∀ y, (G.domain ∩ G ⁻¹' {y}).encard ≤ 2) ∧
      ∀ (e : OpenPartialHomeomorph (double 3 K).space (EuclideanSpace ℝ (Fin 3)))
        (y : (double 3 K).space), y ∈ e.source →
        ∀ᶠ z in 𝓝 (e y), z ∈ frontier (e '' (e.source ∩ C)) ↔
          z ∈ e '' (e.source ∩ Bd) := by
  classical
  let K := S.manifoldComplex
  let _ : Finite K.faces := S.manifoldComplex_faces_finite.to_subtype
  let L := double 3 K
  have hL : IsCombinatorialManifold 3 L :=
    isCombinatorialManifold_double_succ_succ K S.isManifold
  let _ := combinatorialChartedSpace L hL
  let B := PiecewiseLinear.boundaryComplex 3 K
  let ι : E → E × E × ℝ := simplicialMap K (glueEmbed₂ B id)
  let C := ((↑) : L.space → E × E × ℝ) ⁻¹' (ι '' K.space)
  let Bd := ((↑) : L.space → E × E × ℝ) ⁻¹' (ι '' B.space)
  dsimp only
  obtain ⟨f, γ, q, rfl, hγ, hf, hmap, hloc, hcard, hpre, -, hboundary, havoid, -, -⟩ :=
    R.exists_projected_map_of_embeddedDisk D
  let f := R.projection ∘ D.map
  have hι : IsPLHomeomorphOn ι K.space (glued₂ K B id).space :=
    isPLHomeomorphOn_embedComplex K (glueEmbed₂ B id) (glueSnd E E) (fun _ _ _ _ => rfl)
  have hcopy : ι '' K.space ⊆ L.space := by
    rw [hι.image_eq]
    change (glued₂ K B id).space ⊆ (double 3 K).space
    rw [double, gluedComplex_space]
    exact subset_union_right
  let g := ι ∘ f
  have hgcopy : MapsTo g D.domain L.space := by
    intro x hx
    exact hcopy ⟨f x, hmap hx, rfl⟩
  have hg : IsPiecewiseAffineOn g D.domain := by
    have hcomp := hι.isPiecewiseAffineOn.comp hf
    have hinter : D.domain ∩ f ⁻¹' K.space = D.domain := inter_eq_left.mpr hmap
    rw [hinter] at hcomp
    exact hcomp
  obtain ⟨a, ha⟩ := D.isPLBall_domain.nonempty
  let U := combinatorialPLPieceIn L hL ⟨g a, hgcopy ha⟩
  have hval (y : E × E × ℝ) (hy : y ∈ L.space) : (U.map y : E × E × ℝ) = y := by
    simp only [U, combinatorialPLPieceIn, dite_eq_left hy]
  let G : SingularTwoCell L.space :=
    { domain := D.domain
      isPLBall_domain := D.isPLBall_domain
      toFun := U.map ∘ g
      isPLOn := U.isPLOn_comp hg hgcopy }
  have hGeq : EqOn (fun x => (G x : E × E × ℝ)) g D.domain := by
    intro x hx
    exact hval (g x) (hgcopy hx)
  have heq (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ D.domain)
      (z : EuclideanSpace ℝ (Fin 2)) (hz : z ∈ D.domain) : G x = G z ↔ f x = f z := by
    constructor
    · intro hxz
      exact hι.bijOn.injOn (hmap hx) (hmap hz)
        ((hGeq hx).symm.trans ((congrArg Subtype.val hxz).trans (hGeq hz)))
    · intro hxz
      exact Subtype.ext ((hGeq hx).trans ((congrArg ι hxz).trans (hGeq hz).symm))
  have hfiber (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ D.domain) :
      G.domain ∩ G ⁻¹' {G x} = D.domain ∩ f ⁻¹' {f x} := by
    ext z
    apply and_congr_right
    intro hz
    exact heq z hz x hx
  have hlocal : IsLocallyInjective (G.domain.domRestrict G) := by
    intro x
    obtain ⟨V, hV, hx, hinj⟩ := hloc x
    refine ⟨V, hV, hx, ?_⟩
    intro y hy z hz he
    exact hinj hy hz ((heq y y.2 z z.2).mp he)
  have hcardG (y : L.space) : (G.domain ∩ G ⁻¹' {y}).encard ≤ 2 := by
    by_cases hnonempty : (G.domain ∩ G ⁻¹' {y}).Nonempty
    · obtain ⟨x, hx, hxy⟩ := hnonempty
      change G x = y at hxy
      rw [← hxy, hfiber x hx]
      exact hcard (f x)
    · rw [not_nonempty_iff_eq_empty.mp hnonempty, encard_empty]
      exact zero_le
  have hC : C = ((↑) : L.space → E × E × ℝ) ⁻¹' (glued₂ K B id).space := by
    rw [glued₂_space]
  have hfront : frontier C = Bd := by
    rw [hC]
    exact frontier_preimage_glued₂_space_in_double K S.isManifold
  have hmapG : MapsTo G G.domain C := by
    intro x hx
    exact ⟨f x, hmap hx, (hGeq hx).symm⟩
  have hpreG : G.domain ∩ G ⁻¹' Bd = frontier G.domain := by
    apply Subset.antisymm
    · rintro x ⟨hx, b, hb, hbx⟩
      apply hpre.subset
      refine ⟨hx, ?_⟩
      have hfb : f x = b := hι.bijOn.injOn (hmap hx)
        (boundaryComplex_space_subset 3 K hb) ((hGeq hx).symm.trans hbx.symm)
      change f x ∈ B.space
      rw [hfb]
      exact hb
    · intro x hx
      have hp := hpre.superset hx
      exact ⟨hp.1, f x, hp.2, (hGeq hp.1).symm⟩
  have hinter : G '' G.domain ∩ frontier C = range G.boundary := by
    rw [hfront, ← image_inter_preimage, hpreG]
    ext y
    exact ⟨fun ⟨x, hx, hxy⟩ => ⟨⟨x, hx⟩, hxy⟩,
      fun ⟨x, hxy⟩ => ⟨x, x.2, hxy⟩⟩
  have hboundaryG : range (fun x => (G.boundary x : E × E × ℝ)) =
      ι '' range (fun θ => (γ θ : E)) := by
    change range ((fun x => (G x : E × E × ℝ)) ∘
      (Subtype.val : frontier D.domain → EuclideanSpace ℝ (Fin 2))) = _
    rw [range_comp, Subtype.range_coe, hboundary]
    rw [← image_comp]
    exact (hGeq.mono D.isPLBall_domain.isPolyhedron.isClosed.frontier_subset).image_eq
  refine ⟨G, γ, q, rfl, hγ, hGeq, hmapG, hfront, hpreG, hinter, hboundaryG,
    havoid, hfiber, hlocal, hcardG, ?_⟩
  intro e y hy
  change ∀ᶠ z in 𝓝 (e y), z ∈ frontier (e '' (e.source ∩ C)) ↔
    z ∈ e '' (e.source ∩ Bd)
  rw [hC]
  exact eventually_mem_frontier_image_glued₂_iff K S.isManifold e hy

end DifferentialGeometry.Topology.PiecewiseLinear.NormalSystem
