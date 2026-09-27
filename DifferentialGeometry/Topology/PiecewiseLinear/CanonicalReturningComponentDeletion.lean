/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalComponentDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalReturningAnnulusDeletion
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalTowerSurfaceClosed

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

def IsReturningAnnulusDeletion (I H K C J₀ J₁ T B₀ B₁ X X' F : Set E3) : Prop :=
  IsPLAnnulusWithEnds C J₀ J₁ ∧ IsPLAnnulusWithEnds B₀ J₀ J₁ ∧
    IsPLAnnulusWithEnds B₁ J₀ J₁ ∧ T = B₀ ∪ B₁ ∧ B₀ ∩ B₁ = J₀ ∪ J₁ ∧
    C ∩ T = J₀ ∪ J₁ ∧ C ⊆ X ∧ T ⊆ X ∧
    X' = X \ (C \ (J₀ ∪ J₁)) ∧ IsSeparatorIn I X' H K ∧ X' ∩ F = X ∩ F

def IsCanonicalReturningComponent
    (X : ℤ → Geometry.SimplicialComplex ℝ E3) (T : ℤ → Set E3) (i : ℤ)
    (c : ConnectedComponents (X i).space) : Prop :=
  ∃ (k : ℤ) (J₀ J₁ : Set E3), (k = i ∨ k = i + 1) ∧
    IsPLAnnulusWithEnds (connectedComponentComplex (X i) c).space J₀ J₁ ∧
    Disjoint J₀ J₁ ∧
    J₀ ∈ traceCircles (connectedComponentComplex (X i) c).space (T (2 * k)) ∧
    J₁ ∈ traceCircles (connectedComponentComplex (X i) c).space (T (2 * k)) ∧
    ¬ boundsDiskIn J₀ (T (2 * i + 1)) ∧ ¬ boundsDiskIn J₁ (T (2 * i + 1))

variable {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}
  {Dimg Dbdimg W I : Set E3} {P' a b : E3}

open Classical in
theorem IsCanonicalAnnularWindow.exists_returning_component_deletion [d : DecidableEq E3]
    {X : ℤ → Geometry.SimplicialComplex ℝ E3} {rows : Finset ℤ}
    (hX : IsCanonicalAnnularWindow X (fun j => φ '' S j) S'' T'' I P' a b rows)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' Dimg Dbdimg W I P')
    (h314 : Moise314) (hI : IsOpen I)
    (havoid : ∀ j : ℤ, Disjoint (φ '' S j) ({a, b} : Set E3))
    (i : ℤ) (c : ConnectedComponents (X i).space) {J₀ J₁ : Set E3}
    (hC : IsPLAnnulusWithEnds (connectedComponentComplex (X i) c).space J₀ J₁)
    (hdis : Disjoint J₀ J₁) (k : ℤ) (hk : k = i ∨ k = i + 1)
    (h₀ : J₀ ∈ traceCircles (connectedComponentComplex (X i) c).space (T'' (2 * k)))
    (h₁ : J₁ ∈ traceCircles (connectedComponentComplex (X i) c).space (T'' (2 * k)))
    (hess₀ : ¬ boundsDiskIn J₀ (T'' (2 * i + 1)))
    (hess₁ : ¬ boundsDiskIn J₁ (T'' (2 * i + 1)))
    {F : Set E3} (hF : Disjoint F ((connectedComponentComplex (X i) c).space \ (J₀ ∪ J₁))) :
    ∃ (Y : ℤ → Geometry.SimplicialComplex ℝ E3) (B₀ B₁ : Set E3),
      IsCanonicalAnnularWindow Y (fun j => φ '' S j) S'' T'' I P' a b rows ∧
      IsCanonicalComponentDeletion i X Y c ∧
      IsReturningAnnulusDeletion I {a} {b} (connectedComponentComplex (X i) c).space
        J₀ J₁ (T'' (2 * k)) B₀ B₁ (towerSurface T'' (fun j => (X j).space) P')
        (towerSurface T'' (fun j => (Y j).space) P') F := by
  have hd : d = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst d
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
    exact hX.surface.isSeparatorIn_after_delete_returning_component htw h314 hI havoid
      i c hC hdis k hk h₀ h₁ hess₀ hess₁ (hsurface ▸ hclosed)
  have hY : IsCanonicalSurface Y (fun j => φ '' S j) T'' I P' a b :=
    hX.surface.of_component_complement i c R hR hRo hRspace hRb hsep
  obtain ⟨B₀, B₁, hB₀, hB₁, hT, hBB, hCT⟩ :=
    hX.surface.exists_annulus_pair_of_returning_component htw h314
      i c hC hdis k hk h₀ h₁ hess₀ hess₁
  have hCM : (connectedComponentComplex (X i) c).space ⊆
      towerSurface T'' (fun j => (X j).space) P' := by
    intro x hx
    exact Or.inl (mem_iUnion.mpr ⟨i, Or.inr ((iUnion_connectedComponentComplex_space
      (X i)).subset (mem_iUnion.mpr ⟨c, hx⟩))⟩)
  have hTM : T'' (2 * k) ⊆ towerSurface T'' (fun j => (X j).space) P' :=
    fun x hx => Or.inl (mem_iUnion.mpr ⟨k, Or.inl hx⟩)
  have hfixed : towerSurface T'' (fun j => (Y j).space) P' ∩ F =
      towerSurface T'' (fun j => (X j).space) P' ∩ F := by
    apply hdel.towerSurface_inter_eq hX.surface htw
    simpa only [hbd] using hF
  exact ⟨Y, B₀, B₁, hX.of_component_deletion hdel hY, hdel,
    hC, hB₀, hB₁, hT, hBB, hCT, hCM, hTM, hsurface, hsep, hfixed⟩

end DifferentialGeometry.Topology.PiecewiseLinear
