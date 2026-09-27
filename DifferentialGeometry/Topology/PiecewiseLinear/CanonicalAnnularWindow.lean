/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalClosedWindowReduction

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

structure IsCanonicalAnnularWindow [DecidableEq E3]
    (Y : ℤ → Geometry.SimplicialComplex ℝ E3) (S' S'' T'' : ℤ → Set E3)
    (I : Set E3) (P' a b : E3) (rows : Finset ℤ) : Prop where
  surface : IsCanonicalSurface Y S' T'' I P' a b
  embeddings : ∀ i, HasEssentialBoundaryPLEmbeddings (Y i) (T'' (2 * i + 1))
  nullRank : windowNullRank Y T'' (towerWindowSeams rows) = 0
  generators : ∀ i ∈ towerWindowSeams rows,
    ∀ G ∈ traceCircles ((Y (i - 1)).space ∪ (Y i).space) (T'' (2 * i)),
      ∀ hsub : G ⊆ S'' (2 * i), ∀ x : G,
        Function.Surjective (FundamentalGroup.map
          (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ : C(G, S'' (2 * i))) x)
  components : ∀ i ∈ rows, ∀ c : ConnectedComponents (Y i).space,
    ∃ J₀ J₁ : Set E3, IsPLAnnulusWithEnds (connectedComponentComplex (Y i) c).space J₀ J₁ ∧
      Disjoint J₀ J₁ ∧
      (J₀ ∈ traceCircles (connectedComponentComplex (Y i) c).space (T'' (2 * i)) ∨
        J₀ ∈ traceCircles (connectedComponentComplex (Y i) c).space (T'' (2 * (i + 1)))) ∧
      (J₁ ∈ traceCircles (connectedComponentComplex (Y i) c).space (T'' (2 * i)) ∨
        J₁ ∈ traceCircles (connectedComponentComplex (Y i) c).space (T'' (2 * (i + 1)))) ∧
      ¬ boundsDiskIn J₀ (T'' (2 * i + 1)) ∧ ¬ boundsDiskIn J₁ (T'' (2 * i + 1))

theorem IsCanonicalWindowClassification.disjoint_row_interiors [DecidableEq E3]
    {X Y : ℤ → Geometry.SimplicialComplex ℝ E3} {S' S'' T'' : ℤ → Set E3}
    {I F : Set E3} {P' a b : E3} {rows : Finset ℤ}
    (hclass : IsCanonicalWindowClassification X Y S' S'' T'' I P' a b rows F)
    (hFO : ∀ k ∈ towerWindowSeams rows, Disjoint F (interior (S' (2 * k))))
    (hF : ∀ i ∈ rows, Disjoint F ((X i).space \ (boundaryComplex 2 (X i)).space)) :
    ∀ i ∈ rows, Disjoint F ((Y i).space \ (boundaryComplex 2 (Y i)).space) := by
  have hsupport : Disjoint F (towerWindowSupport S' (towerWindowSeams rows)) := by
    apply disjoint_left.mpr
    intro x hxF hx
    obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
    exact disjoint_left.mp (hFO k hk) hxF hxk
  intro i hi
  apply disjoint_left.mpr
  intro x hxF hxY
  have hout : x ∉ towerWindowSupport S' (towerWindowSeams rows) :=
    disjoint_left.mp hsupport hxF
  have hxX : x ∈ (X i).space := ((hclass.outside i).subset ⟨hxY.1, hout⟩).1
  apply disjoint_left.mp (hF i hi) hxF
  refine ⟨hxX, ?_⟩
  intro hxB
  have hxt := ((hclass.source.boundary i).subset hxB).2
  exact hxY.2 ((hclass.target.boundary i).symm.subset ⟨hxY.1, hxt⟩)

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3} {u v : E3} {W : Set E3} {P' : E3}
  {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}

open Classical in
theorem IsCanonicalWindowClassification.exists_annular_window [d : DecidableEq E3]
    (ht : IsTube K N C D Dbd h N')
    (hu : u ∈ K.vertices) (hv : v ∈ K.vertices) (huv : u ≠ v)
    (he : ({u, v} : Finset E3) ∈ K.faces)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' (h '' D {u, v}) (h '' Dbd {u, v}) W
      (interior (h '' C u ∪ h '' C v)) P')
    (havoid : ∀ i : ℤ, Disjoint (φ '' S i) ({h u, h v} : Set E3))
    {X₀ X : ℤ → Geometry.SimplicialComplex ℝ E3} {rows : Finset ℤ} {F : Set E3}
    (hclass : IsCanonicalWindowClassification X₀ X (fun i => φ '' S i) S'' T''
      (interior (h '' C u ∪ h '' C v)) P' (h u) (h v) rows F)
    (hF : ∀ i ∈ rows, Disjoint F ((X i).space \ (boundaryComplex 2 (X i)).space)) :
    ∃ Y : ℤ → Geometry.SimplicialComplex ℝ E3,
      IsCanonicalClosedWindowReduction X Y (fun i => φ '' S i) T''
        (interior (h '' C u ∪ h '' C v)) P' (h u) (h v) rows F ∧
      IsCanonicalAnnularWindow Y (fun i => φ '' S i) S'' T''
        (interior (h '' C u ∪ h '' C v)) P' (h u) (h v) rows := by
  have hd : d = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  subst d
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  obtain ⟨Y, hred⟩ := IsCanonicalSurface.exists_window_closed_reduction ht hu hv huv he htw
    havoid hclass.target hclass.embeddings rows hF
  refine ⟨Y, hred,
    { surface := hred.target
      embeddings := hred.embeddings
      nullRank := (hred.nullRankEq (towerWindowSeams rows)).trans hclass.nullRank
      generators := ?_
      components := ?_ }⟩
  · intro i hi G hG
    have htrace : traceCircles ((Y (i - 1)).space ∪ (Y i).space) (T'' (2 * i)) =
        traceCircles ((X (i - 1)).space ∪ (X i).space) (T'' (2 * i)) := by
      apply traceCircles_eq_of_inter_eq
      rw [union_inter_distrib_right, union_inter_distrib_right,
        hred.evenTrace (i - 1) i, hred.evenTrace i i]
    exact hclass.generators i hi G (htrace.subset hG)
  · intro i hi c
    let _ : Finite (X i).faces := (hclass.target.finiteFaces i).to_subtype
    let _ : Finite (Y i).faces := (hred.target.finiteFaces i).to_subtype
    let _ (q : ConnectedComponents (X i).space) :
        Finite (connectedComponentComplex (X i) q).faces :=
      (connectedComponentComplex_faces_finite (X i) q).to_subtype
    let _ (q : ConnectedComponents (Y i).space) :
        Finite (connectedComponentComplex (Y i) q).faces :=
      (connectedComponentComplex_faces_finite (Y i) q).to_subtype
    obtain ⟨e, heq⟩ := hred.componentEmbedding i
    have hf : IsPLHomeomorphOn (id : E3 → E3) (connectedComponentComplex (X i) (e c)).space
        (connectedComponentComplex (Y i) c).space := by
      rw [heq c]
      exact (isPolyhedron_space (connectedComponentComplex (X i) (e c))).isPLHomeomorphOn_id
    have hbd : (boundaryComplex 2 (connectedComponentComplex (Y i) c)).space =
        (boundaryComplex 2 (connectedComponentComplex (X i) (e c))).space := by
      simpa only [image_id] using boundaryComplex_space_of_isPLHomeomorphOn
        (connectedComponentComplex (X i) (e c)) (connectedComponentComplex (Y i) c)
        ((hclass.target.manifold i).connectedComponentComplex (e c)) hf
    rcases hclass.components i hi (e c) with hempty | hann
    · exact (hred.closedFree i hi c (hbd.trans hempty)).elim
    · simpa only [heq c] using hann

open Classical in
theorem IsCanonicalTower.exists_initial_annular_window [DecidableEq E3]
    (ht : IsTube K N C D Dbd h N')
    (hu : u ∈ K.vertices) (hv : v ∈ K.vertices) (huv : u ≠ v)
    (he : ({u, v} : Finset E3) ∈ K.faces)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' (h '' D {u, v}) (h '' Dbd {u, v}) W
      (interior (h '' C u ∪ h '' C v)) P')
    (havoid : ∀ i : ℤ, Disjoint (φ '' S i) ({h u, h v} : Set E3))
    (hcl : IsClosed (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹'
      initialSurface S'' T'' P'))
    (hsep : Separates (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹'
        initialSurface S'' T'' P')
      (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' {h u})
      (((↑) : interior (h '' C u ∪ h '' C v) → E3) ⁻¹' {h v}))
    (h303 : Moise303) (h286 : Moise286) (h314 : Moise314)
    (rows : Finset ℤ) {F : Set E3}
    (hFO : ∀ i ∈ towerWindowSeams rows, Disjoint F (interior (φ '' S (2 * i))))
    (hF : ∀ i ∈ rows, Disjoint F
      (canonicalOddPiece S'' T'' i \ (T'' (2 * i) ∪ T'' (2 * (i + 1))))) :
    ∃ X₀ X Y : ℤ → Geometry.SimplicialComplex ℝ E3,
      (∀ i, (X₀ i).space = canonicalOddPiece S'' T'' i) ∧
      towerSurface T'' (fun i => (X₀ i).space) P' = initialSurface S'' T'' P' ∧
      IsCanonicalWindowClassification X₀ X (fun i => φ '' S i) S'' T''
        (interior (h '' C u ∪ h '' C v)) P' (h u) (h v) rows F ∧
      IsCanonicalClosedWindowReduction X Y (fun i => φ '' S i) T''
        (interior (h '' C u ∪ h '' C v)) P' (h u) (h v) rows F ∧
      IsCanonicalAnnularWindow Y (fun i => φ '' S i) S'' T''
        (interior (h '' C u ∪ h '' C v)) P' (h u) (h v) rows ∧
      towerSurface T'' (fun i => (Y i).space) P' ∩ F = initialSurface S'' T'' P' ∩ F := by
  obtain ⟨X₀, X, hspace, hinit, hclass⟩ :=
    IsCanonicalTower.exists_initial_window_component_classification ht hu hv huv he htw havoid
      hcl hsep h303 h286 h314 rows hFO
  have hF₀ : ∀ i ∈ rows, Disjoint F ((X₀ i).space \ (boundaryComplex 2 (X₀ i)).space) := by
    intro i hi
    apply (hF i hi).mono_right
    intro x hx
    refine ⟨(hspace i).subset hx.1, ?_⟩
    intro hxt
    exact hx.2 ((hclass.source.boundary i).symm.subset ⟨hx.1, hxt⟩)
  obtain ⟨Y, hred, hann⟩ := hclass.exists_annular_window ht hu hv huv he htw havoid
    (hclass.disjoint_row_interiors hFO hF₀)
  refine ⟨X₀, X, Y, hspace, hinit, hclass, hred, hann, ?_⟩
  rw [hred.fixedSet, hclass.fixedSet, hinit]

end DifferentialGeometry.Topology.PiecewiseLinear
