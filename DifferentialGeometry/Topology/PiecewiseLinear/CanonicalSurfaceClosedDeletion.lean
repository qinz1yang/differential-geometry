/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalSurfaceComponentComplement
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalSurfaceClosedNonseparation
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerSurfaceClosed
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldComponentComplement
import DifferentialGeometry.Topology.PiecewiseLinear.TowerSurfaceComponentDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.TubePairSimplyConnected
import DifferentialGeometry.Topology.Connected.PhragmenBrouwer

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3} {u v : E3} {W : Set E3} {P' : E3}
  {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}

open Classical in
theorem IsCanonicalSurface.exists_delete_closed_component [d : DecidableEq E3]
    (ht : IsTube K N C D Dbd h N')
    (hu : u ∈ K.vertices) (hv : v ∈ K.vertices) (huv : u ≠ v)
    (he : ({u, v} : Finset E3) ∈ K.faces)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' (h '' D {u, v}) (h '' Dbd {u, v}) W
      (interior (h '' C u ∪ h '' C v)) P')
    (havoid : ∀ k : ℤ, Disjoint (φ '' S k) ({h u, h v} : Set E3))
    {X : ℤ → Geometry.SimplicialComplex ℝ E3}
    (hX : IsCanonicalSurface X (fun j => φ '' S j) T''
      (interior (h '' C u ∪ h '' C v)) P' (h u) (h v))
    (i : ℤ) (c : ConnectedComponents (X i).space)
    (hclosed : (boundaryComplex 2 (connectedComponentComplex (X i) c)).space = ∅)
    {F : Set E3} (hF : Disjoint F (connectedComponentComplex (X i) c).space) :
    ∃ Y : ℤ → Geometry.SimplicialComplex ℝ E3,
      IsCanonicalSurface Y (fun j => φ '' S j) T''
        (interior (h '' C u ∪ h '' C v)) P' (h u) (h v) ∧
      (∀ j, j ≠ i → Y j = X j) ∧
      (Y i).space = (X i).space \ (connectedComponentComplex (X i) c).space ∧
      Nat.card (ConnectedComponents (Y i).space) + 1 = Nat.card (ConnectedComponents (X i).space) ∧
      IsTypeOneDeletion (interior (h '' C u ∪ h '' C v)) {h u} {h v}
        (connectedComponentComplex (X i) c).space (towerSurface T'' (fun j => (Y j).space) P')
        (towerSurface T'' (fun j => (X j).space) P')
        (towerSurface T'' (fun j => (Y j).space) P') F := by
  have hd : d = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst d
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  let U := interior (h '' C u ∪ h '' C v)
  let _ : SimplyConnectedSpace U := ht.simplyConnectedSpace_interior_image_pair hu hv huv (by
    exact (congrArg (fun d : DecidableEq E3 =>
      @insert E3 (Finset E3) (@Finset.instInsert E3 d) u {v} ∈ K.faces)
        (Subsingleton.elim _ _)).mp he)
  let _ : LocallyPathConnectedSpace U := isOpen_interior.locallyPathConnectedSpace
  let _ : Finite (X i).faces := (hX.finiteFaces i).to_subtype
  let _ : Finite (connectedComponentComplex (X i) c).faces :=
    (connectedComponentComplex_faces_finite (X i) c).to_subtype
  let Z := (connectedComponentComplex (X i) c).space
  have hZsub : Z ⊆ (X i).space :=
    (subset_iUnion (fun d => (connectedComponentComplex (X i) d).space) c).trans
      (iUnion_connectedComponentComplex_space (X i)).subset
  have hCT : ∀ k, Disjoint Z (T'' (2 * k)) :=
    hX.closed_component_disjoint_even htw i c hclosed
  have hCL : ∀ j, j ≠ i → Disjoint Z (X j).space :=
    fun j hji => (hX.piecesDisjoint (Ne.symm hji)).mono_left hZsub
  have hPZ : P' ∉ Z := fun hx => hX.centerNotMem i (hZsub hx)
  obtain ⟨R, hRfin, hR, hRo, hRspace, hRb, -, hcount⟩ :=
    (hX.manifold i).exists_closed_component_complement (X i) (hX.orientable i) c hclosed
  let _ : Finite R.faces := hRfin.to_subtype
  let Y := Function.update X i R
  let M₀ := towerSurface T'' (fun j => (X j).space) P'
  let M₁ := towerSurface T'' (fun j => (Y j).space) P'
  have hYsub : ∀ j, (Y j).space ⊆ (X j).space := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [Y, Function.update_self] using hRspace.subset.trans sdiff_subset
    · simpa only [Y, Function.update_of_ne hji] using
        (Subset.rfl : (X j).space ⊆ (X j).space)
  have hYpoly : ∀ j, IsPolyhedron (Y j).space := by
    intro j
    by_cases hji : j = i
    · subst j
      simpa only [Y, Function.update_self] using isPolyhedron_space R
    · simpa only [Y, Function.update_of_ne hji] using (hX.lowerTrace j).isPolyhedron
  have hMclosed : IsClosed (((↑) : U → E3) ⁻¹' M₁) :=
    htw.isClosed_towerSurface (fun j => (Y j).space) (fun j => (hYpoly j).isClosed)
      (fun j => (hYsub j).trans (hX.carrier j))
  have hrow : (fun j => (Y j).space) =
      Function.update (fun j => (X j).space) i ((X i).space \ Z) := by
    funext j
    by_cases hji : j = i
    · subst j
      simpa only [Y, Function.update_self] using hRspace
    · simp only [Y, Function.update_of_ne hji]
  have hdelete : M₁ = M₀ \ Z := by
    dsimp only [M₁, M₀]
    rw [hrow]
    exact towerSurface_update_eq_sdiff T'' (fun j => (X j).space) P' i Z hCT hCL hPZ
  have hZM : Z ⊆ M₀ := fun x hx => Or.inl (mem_iUnion.mpr ⟨i, Or.inr (hZsub hx)⟩)
  have hcover : M₀ = Z ∪ M₁ := by
    rw [hdelete]
    apply Subset.antisymm
    · intro x hx
      by_cases hxZ : x ∈ Z
      · exact Or.inl hxZ
      · exact Or.inr ⟨hx, hxZ⟩
    · rintro x (hx | hx)
      · exact hZM hx
      · exact hx.1
  have hdis : Disjoint Z M₁ := by
    rw [hdelete]
    exact disjoint_left.mpr fun _ hx hy => hy.2 hx
  have hZclosed : IsClosed (((↑) : U → E3) ⁻¹' Z) :=
    (isPolyhedron_space (connectedComponentComplex (X i) c)).isClosed.preimage
      continuous_subtype_val
  have hnon : ¬ Separates (((↑) : U → E3) ⁻¹' Z) (((↑) : U → E3) ⁻¹' {h u})
      (((↑) : U → E3) ⁻¹' {h v}) :=
    IsCanonicalSurface.closed_component_not_separates ht hu hv huv he htw havoid hX i c hclosed
  have hsing (z : E3) : IsPreconnected (((↑) : U → E3) ⁻¹' {z}) := by
    apply Set.Subsingleton.isPreconnected
    intro p hp q hq
    change (p : E3) = z at hp
    change (q : E3) = z at hq
    exact Subtype.ext (hp.trans hq.symm)
  have hsep : Separates (((↑) : U → E3) ⁻¹' M₁) (((↑) : U → E3) ⁻¹' {h u})
      (((↑) : U → E3) ⁻¹' {h v}) := by
    apply (Topology.phragmen_brouwer hZclosed hMclosed
      (disjoint_left.mpr fun x hx hy => disjoint_left.mp hdis hx hy)
      (hsing (h u)) (hsing (h v)) ?_).resolve_left hnon
    rw [← preimage_union, ← hcover]
    exact hX.separator.2
  have hfix : M₁ ∩ F = M₀ ∩ F := by
    rw [hdelete]
    ext x
    exact ⟨fun hx => ⟨hx.1.1, hx.2⟩,
      fun hx => ⟨⟨hx.1, disjoint_left.mp hF hx.2⟩, hx.2⟩⟩
  have hMY : IsSeparatorIn U M₁ {h u} {h v} := ⟨hMclosed, hsep⟩
  refine ⟨Y, hX.of_closed_component_complement htw i c hclosed R hR hRo hRspace hRb hMY,
    fun j hji => Function.update_of_ne hji R X, ?_, ?_, ?_⟩
  · simpa only [Y, Function.update_self] using hRspace
  · rw [show Y i = R from Function.update_self i R X]
    exact hcount
  · exact ⟨hcover, hdis, hZclosed, hMclosed, hnon, rfl, hMY, hfix⟩

end DifferentialGeometry.Topology.PiecewiseLinear
