/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalSurfaceAnnularComponents
import DifferentialGeometry.Topology.PiecewiseLinear.CanonicalSurfaceNullNormalization

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

def towerWindowSeams (rows : Finset ℤ) : Finset ℤ := rows ∪ rows.image (fun i => i + 1)

structure IsCanonicalWindowClassification [DecidableEq E3]
    (X Y : ℤ → Geometry.SimplicialComplex ℝ E3) (S' S'' T'' : ℤ → Set E3)
    (I : Set E3) (P' a b : E3) (rows : Finset ℤ) (F : Set E3) : Prop where
  source : IsCanonicalSurface X S' T'' I P' a b
  target : IsCanonicalSurface Y S' T'' I P' a b
  embeddings : ∀ i, HasEssentialBoundaryPLEmbeddings (Y i) (T'' (2 * i + 1))
  nullRank : windowNullRank Y T'' (towerWindowSeams rows) = 0
  splits : Relation.ReflTransGen (fun U V =>
    IsCanonicalSurface U S' T'' I P' a b ∧ IsCanonicalSurface V S' T'' I P' a b ∧
      ∃ i ∈ towerWindowSeams rows, IsCanonicalNullSplit S' T'' i U V) X Y
  outside : ∀ i, (Y i).space \ towerWindowSupport S' (towerWindowSeams rows) =
    (X i).space \ towerWindowSupport S' (towerWindowSeams rows)
  unchanged : ∀ i, i ∉ towerWindowSeams rows → i + 1 ∉ towerWindowSeams rows → Y i = X i
  fixedSet : towerSurface T'' (fun i => (Y i).space) P' ∩ F =
    towerSurface T'' (fun i => (X i).space) P' ∩ F
  generators : ∀ i ∈ towerWindowSeams rows,
    ∀ G ∈ traceCircles ((Y (i - 1)).space ∪ (Y i).space) (T'' (2 * i)),
      ∀ hsub : G ⊆ S'' (2 * i), ∀ x : G,
        Function.Surjective (FundamentalGroup.map
          (⟨Set.inclusion hsub, continuous_inclusion hsub⟩ : C(G, S'' (2 * i))) x)
  components : ∀ i ∈ rows, ∀ c : ConnectedComponents (Y i).space,
    (boundaryComplex 2 (connectedComponentComplex (Y i) c)).space = ∅ ∨
      ∃ J₀ J₁ : Set E3, IsPLAnnulusWithEnds (connectedComponentComplex (Y i) c).space J₀ J₁ ∧
        Disjoint J₀ J₁ ∧
        (J₀ ∈ traceCircles (connectedComponentComplex (Y i) c).space (T'' (2 * i)) ∨
          J₀ ∈ traceCircles (connectedComponentComplex (Y i) c).space (T'' (2 * (i + 1)))) ∧
        (J₁ ∈ traceCircles (connectedComponentComplex (Y i) c).space (T'' (2 * i)) ∨
          J₁ ∈ traceCircles (connectedComponentComplex (Y i) c).space (T'' (2 * (i + 1)))) ∧
        ¬ boundsDiskIn J₀ (T'' (2 * i + 1)) ∧ ¬ boundsDiskIn J₁ (T'' (2 * i + 1))

variable {K : Geometry.SimplicialComplex ℝ E3} {N N' : Set E3} {C : E3 → Set E3}
  {D Dbd : Finset E3 → Set E3} {h : E3 → E3} {u v : E3} {W : Set E3} {P' : E3}
  {φ : E3 → E3} {Pt : ℤ → E3} {Dp Dpint J A S T S'' T'' : ℤ → Set E3}

open Classical in
theorem IsCanonicalSurface.exists_window_component_classification [DecidableEq E3]
    (ht : IsTube K N C D Dbd h N')
    (hu : u ∈ K.vertices) (hv : v ∈ K.vertices) (huv : u ≠ v)
    (he : ({u, v} : Finset E3) ∈ K.faces)
    (htw : IsCanonicalTower φ Pt Dp Dpint J A S T S'' T'' (h '' D {u, v}) (h '' Dbd {u, v}) W
      (interior (h '' C u ∪ h '' C v)) P')
    (havoid : ∀ i : ℤ, Disjoint (φ '' S i) ({h u, h v} : Set E3))
    (h303 : Moise303) (h286 : Moise286) (h314 : Moise314)
    {X : ℤ → Geometry.SimplicialComplex ℝ E3}
    (hX : IsCanonicalSurface X (fun i => φ '' S i) T''
      (interior (h '' C u ∪ h '' C v)) P' (h u) (h v))
    (hmodel : ∀ i, HasEssentialBoundaryPLEmbeddings (X i) (T'' (2 * i + 1)))
    (rows : Finset ℤ) {F : Set E3}
    (hFO : ∀ i ∈ towerWindowSeams rows, Disjoint F (interior (φ '' S (2 * i)))) :
    ∃ Y : ℤ → Geometry.SimplicialComplex ℝ E3,
      IsCanonicalWindowClassification X Y (fun i => φ '' S i) S'' T''
        (interior (h '' C u ∪ h '' C v)) P' (h u) (h v) rows F := by
  obtain ⟨Y, hY, hzero, hpath, hout, hfix⟩ :=
    IsCanonicalSurface.exists_window_null_normalization ht hu hv huv he htw havoid h303
      hX (towerWindowSeams rows) hFO
  have hmodels := htw.subsurface_embeddings_of_null_splits h314 (towerWindowSeams rows)
    hmodel hpath
  have hzeroAt (i : ℤ) (hi : i ∈ towerWindowSeams rows) :
      nullTraceCount ((Y (i - 1)).space ∪ (Y i).space) (T'' (2 * i)) = 0 := by
    have hsum := hzero
    unfold windowNullRank at hsum
    exact (Finset.sum_eq_zero_iff.mp hsum) i hi
  have hunchanged : ∀ i, i ∉ towerWindowSeams rows → i + 1 ∉ towerWindowSeams rows → Y i = X i := by
    intro i hi hi₁
    clear hzeroAt hmodels hfix hout hzero hY
    induction hpath with
    | refl => rfl
    | tail hpath hlast ih =>
      obtain ⟨-, -, k, hk, hstep⟩ := hlast
      apply (hstep.unchanged i ?_ ?_).trans ih
      · intro hik
        have hik₁ : i + 1 = k := by omega
        exact hi₁ (hik₁.symm ▸ hk)
      · intro hik
        exact hi (hik.symm ▸ hk)
  refine ⟨Y,
    { source := hX
      target := hY
      embeddings := hmodels
      nullRank := hzero
      splits := hpath
      outside := hout
      unchanged := hunchanged
      fixedSet := hfix
      generators := ?_
      components := ?_ }⟩
  · intro i hi
    exact hY.seam_generators_of_nullTraceCount_eq_zero htw h314 i (hzeroAt i hi)
  · intro i hi c
    have hi₀ : i ∈ towerWindowSeams rows := Finset.mem_union_left _ hi
    have hi₁ : i + 1 ∈ towerWindowSeams rows :=
      Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
    have hright : nullTraceCount ((Y i).space ∪ (Y (i + 1)).space) (T'' (2 * (i + 1))) = 0 := by
      simpa only [add_sub_cancel_right] using hzeroAt (i + 1) hi₁
    exact hY.component_boundary_empty_or_annulus htw h286 h314 i (hmodels i)
      (hzeroAt i hi₀) hright c

open Classical in
theorem IsCanonicalTower.exists_initial_window_component_classification [DecidableEq E3]
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
    (hFO : ∀ i ∈ towerWindowSeams rows, Disjoint F (interior (φ '' S (2 * i)))) :
    ∃ X Y : ℤ → Geometry.SimplicialComplex ℝ E3,
      (∀ i, (X i).space = canonicalOddPiece S'' T'' i) ∧
      towerSurface T'' (fun i => (X i).space) P' = initialSurface S'' T'' P' ∧
      IsCanonicalWindowClassification X Y (fun i => φ '' S i) S'' T''
        (interior (h '' C u ∪ h '' C v)) P' (h u) (h v) rows F := by
  obtain ⟨X, hX, hspace⟩ := htw.exists_initial_surface_state (h u) (h v) hcl hsep
  have hmodel (i : ℤ) : HasEssentialBoundaryPLEmbeddings (X i) (T'' (2 * i + 1)) := by
    let _ : Finite (X i).faces := (hX.finiteFaces i).to_subtype
    apply HasEssentialBoundaryPLEmbeddings.of_subset (X i)
    rw [hspace i]
    exact sdiff_subset
  obtain ⟨Y, hclass⟩ := IsCanonicalSurface.exists_window_component_classification
    ht hu hv huv he htw havoid h303 h286 h314 hX hmodel rows hFO
  refine ⟨X, Y, hspace, ?_, hclass⟩
  rw [htw.initialSurface_eq_iUnion]
  simp only [towerSurface, hspace]

end DifferentialGeometry.Topology.PiecewiseLinear
