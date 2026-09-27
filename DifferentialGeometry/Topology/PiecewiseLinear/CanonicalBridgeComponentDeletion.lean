/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalComponentDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalBridgeAnnulusDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerSurfaceClosed

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

def IsCanonicalBridgeComponent
    (X : ℤ → Geometry.SimplicialComplex ℝ E3) (T : ℤ → Set E3) (i : ℤ)
    (c : ConnectedComponents (X i).space) : Prop :=
  ∃ J₀ J₁ : Set E3,
    IsPLAnnulusWithEnds (connectedComponentComplex (X i) c).space J₀ J₁ ∧
    J₀ ∈ traceCircles (connectedComponentComplex (X i) c).space (T (2 * i)) ∧
    J₁ ∈ traceCircles (connectedComponentComplex (X i) c).space (T (2 * (i + 1))) ∧
    ¬ boundsDiskIn J₀ (T (2 * i + 1)) ∧ ¬ boundsDiskIn J₁ (T (2 * i + 1))

theorem IsCanonicalBridgeComponent.of_component_space_eq
    {X Y : ℤ → Geometry.SimplicialComplex ℝ E3} {T : ℤ → Set E3} {i : ℤ}
    {c : ConnectedComponents (X i).space} {q : ConnectedComponents (Y i).space}
    (h : IsCanonicalBridgeComponent X T i c)
    (hspace : (connectedComponentComplex (Y i) q).space =
      (connectedComponentComplex (X i) c).space) :
    IsCanonicalBridgeComponent Y T i q := by
  simpa only [IsCanonicalBridgeComponent, hspace] using h

variable {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' a b : E3}

open Classical in
theorem IsCanonicalAnnularWindow.exists_bridge_component_deletion [inst : DecidableEq E3]
    {X : ℤ → Geometry.SimplicialComplex ℝ E3} {rows : Finset ℤ}
    (hX : IsCanonicalAnnularWindow X (fun j => φ '' S j) S'' T'' I P' a b rows)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (h314 : Moise314) (hI : IsOpen I)
    (havoid : ∀ j : ℤ, Disjoint (φ '' S j) ({a, b} : Set E3))
    (i : ℤ) (c d : ConnectedComponents (X i).space) (hcd : c ≠ d)
    {J₀ J₁ K₀ K₁ : Set E3}
    (hC : IsPLAnnulusWithEnds (connectedComponentComplex (X i) c).space J₀ J₁)
    (hD : IsPLAnnulusWithEnds (connectedComponentComplex (X i) d).space K₀ K₁)
    (hJ₀ : J₀ ∈ traceCircles (connectedComponentComplex (X i) c).space (T'' (2 * i)))
    (hJ₁ : J₁ ∈ traceCircles (connectedComponentComplex (X i) c).space (T'' (2 * (i + 1))))
    (hK₀ : K₀ ∈ traceCircles (connectedComponentComplex (X i) d).space (T'' (2 * i)))
    (hK₁ : K₁ ∈ traceCircles (connectedComponentComplex (X i) d).space (T'' (2 * (i + 1))))
    (hJess₀ : ¬ boundsDiskIn J₀ (T'' (2 * i + 1)))
    (hJess₁ : ¬ boundsDiskIn J₁ (T'' (2 * i + 1)))
    (hKess₀ : ¬ boundsDiskIn K₀ (T'' (2 * i + 1)))
    (hKess₁ : ¬ boundsDiskIn K₁ (T'' (2 * i + 1)))
    {F : Set E3} (hF : Disjoint F ((connectedComponentComplex (X i) c).space \ (J₀ ∪ J₁))) :
    ∃ Y : ℤ → Geometry.SimplicialComplex ℝ E3,
      IsCanonicalAnnularWindow Y (fun j => φ '' S j) S'' T'' I P' a b rows ∧
      IsCanonicalComponentDeletion i X Y c ∧
      towerSurface T'' (fun j => (Y j).space) P' =
        towerSurface T'' (fun j => (X j).space) P' \
          ((connectedComponentComplex (X i) c).space \ (J₀ ∪ J₁)) ∧
      (connectedComponentComplex (X i) d).space ⊆ (Y i).space ∧
      (∃ q : ConnectedComponents (Y i).space,
        (connectedComponentComplex (Y i) q).space = (connectedComponentComplex (X i) d).space) ∧
      towerSurface T'' (fun j => (Y j).space) P' ∩ F =
        towerSurface T'' (fun j => (X j).space) P' ∩ F := by
  have hd : inst = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst inst
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  let _ : Finite (X i).faces := (hX.surface.finiteFaces i).to_subtype
  let _ : Finite (connectedComponentComplex (X i) c).faces :=
    (connectedComponentComplex_faces_finite (X i) c).to_subtype
  obtain ⟨R, hRfin, hR, hRo, hRspace, hRb, he, hcount⟩ :=
    (hX.surface.manifold i).exists_component_complement (X i) (hX.surface.orientable i) c
  let _ : Finite R.faces := hRfin.to_subtype
  let Y := Function.update X i R
  have hdel : IsCanonicalComponentDeletion i X Y c :=
    { unchanged := fun j hji => Function.update_of_ne hji R X
      space := by simpa only [Y, Function.update_self] using hRspace
      retained := by
        rw [show Y i = R from Function.update_self i R X]
        exact he
      componentCount := by
        rw [show Y i = R from Function.update_self i R X]
        exact hcount }
  have hbd : (boundaryComplex 2 (connectedComponentComplex (X i) c)).space = J₀ ∪ J₁ :=
    hC.boundaryComplex_space _
  have hsurface : towerSurface T'' (fun j => (Y j).space) P' =
      towerSurface T'' (fun j => (X j).space) P' \
        ((connectedComponentComplex (X i) c).space \ (J₀ ∪ J₁)) := by
    simpa only [hbd] using hdel.towerSurface_eq_sdiff_interior hX.surface htw
  have hclosed : IsClosed (((↑) : I → E3) ⁻¹'
      towerSurface T'' (fun j => (Y j).space) P') := by
    apply htw.isClosed_towerSurface
    · intro j
      by_cases hji : j = i
      · subst j
        simpa only [Y, Function.update_self] using (isPolyhedron_space R).isClosed
      · let _ : Finite (X j).faces := (hX.surface.finiteFaces j).to_subtype
        simpa only [hdel.unchanged j hji] using (isPolyhedron_space (X j)).isClosed
    · exact fun j => (hdel.space_subset j).trans (hX.surface.carrier j)
  have hsep : IsSeparatorIn I (towerSurface T'' (fun j => (Y j).space) P') {a} {b} := by
    rw [hsurface]
    exact hX.surface.isSeparatorIn_after_delete_bridge_component htw h314 hI havoid
      i c d hcd hC hD hJ₀ hJ₁ hK₀ hK₁ hJess₀ hJess₁ hKess₀ hKess₁
      (hsurface ▸ hclosed)
  have hY : IsCanonicalSurface Y (fun j => φ '' S j) T'' I P' a b :=
    hX.surface.of_component_complement i c R hR hRo hRspace hRb hsep
  have hkeep : (connectedComponentComplex (X i) d).space ⊆ (Y i).space := by
    intro x hx
    apply hdel.space.symm.subset
    refine ⟨(iUnion_connectedComponentComplex_space (X i)).subset
      (mem_iUnion.mpr ⟨d, hx⟩), ?_⟩
    intro hxc
    exact disjoint_left.mp (pairwise_disjoint_connectedComponentComplex_space (X i) hcd) hxc hx
  have hfixed : towerSurface T'' (fun j => (Y j).space) P' ∩ F =
      towerSurface T'' (fun j => (X j).space) P' ∩ F := by
    apply hdel.towerSurface_inter_eq hX.surface htw
    simpa only [hbd] using hF
  have hretained : ∃ q : ConnectedComponents (Y i).space,
      (connectedComponentComplex (Y i) q).space = (connectedComponentComplex (X i) d).space := by
    obtain ⟨e, heq⟩ := hdel.retained
    exact ⟨e ⟨d, Ne.symm hcd⟩, heq ⟨d, Ne.symm hcd⟩⟩
  exact ⟨Y, hX.of_component_deletion hdel hY, hdel, hsurface, hkeep, hretained, hfixed⟩

end DifferentialGeometry.Topology.PiecewiseLinear
