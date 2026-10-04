import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgeryTransitions
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgeryCoordinates
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CarrierSurgeryAtlas
import DifferentialGeometry.Topology.Manifold.ULift

/-!
The smooth half-space atlas on the actual abstract torus quotient, assembled from its interior,
signed seam and retained half-collar patches. All source coordinates and transitions are actual.
-/

set_option autoImplicit false

noncomputable section

open Set Topology TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open DifferentialGeometry.Topology.Manifold GC.Seifert
open scoped Manifold ContDiff

universe u

attribute [local instance] uliftChartedSpace isManifold_ulift

namespace GC.Seifert

section LiftTransitions

variable {E F H K M N M' N' Q : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace K]
  [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace M']
  [TopologicalSpace N'] [TopologicalSpace Q]
  [ChartedSpace H M] [ChartedSpace K N] [ChartedSpace H M'] [ChartedSpace K N']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F K}

private theorem contMDiffOn_surgeryLiftedTransition
    (a : M' ≃ₘ⟮I, I⟯ M) (b : N' ≃ₘ⟮J, J⟯ N)
    (e : OpenPartialHomeomorph M Q) (f : OpenPartialHomeomorph N Q)
    (hf : ContMDiffOn I J ∞ (e.trans f.symm) (e.trans f.symm).source)
    (hb : ContMDiffOn J I ∞ (f.trans e.symm) (f.trans e.symm).source) :
    ContMDiffOn I J ∞
      ((a.toHomeomorph.toOpenPartialHomeomorph.trans e).trans
        (b.toHomeomorph.toOpenPartialHomeomorph.trans f).symm)
      ((a.toHomeomorph.toOpenPartialHomeomorph.trans e).trans
        (b.toHomeomorph.toOpenPartialHomeomorph.trans f).symm).source := by
  let t : PartialDiffeomorph I J M N ∞ :=
    { toPartialEquiv := (e.trans f.symm).toPartialEquiv
      open_source := (e.trans f.symm).open_source
      open_target := (e.trans f.symm).open_target
      contMDiffOn_toFun := hf
      contMDiffOn_invFun := hb }
  have h := ((a.toPartialDiffeomorph.trans t).trans b.symm.toPartialDiffeomorph).contMDiffOn
  change ContMDiffOn I J ∞
    ((a.toHomeomorph.toOpenPartialHomeomorph.trans (e.trans f.symm)).trans
      b.symm.toHomeomorph.toOpenPartialHomeomorph)
    ((a.toHomeomorph.toOpenPartialHomeomorph.trans (e.trans f.symm)).trans
      b.symm.toHomeomorph.toOpenPartialHomeomorph).source at h
  simpa only [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.trans_assoc, Diffeomorph.symm_toHomeomorph,
    Homeomorph.symm_toOpenPartialHomeomorph] using h

end LiftTransitions

end GC.Seifert

namespace GC.GraphManifold.TorusPairing

variable {C : CompactCarrier.{u}}

abbrev SurgeryPatchIndex (P : TorusPairing C) (n : ℕ) := Option (Fin P.count) ⊕ Fin n

abbrev SurgeryPatchVector (P : TorusPairing C) (n : ℕ) : P.SurgeryPatchIndex n → Type
  | .inl none => EuclideanSpace ℝ (Fin 3)
  | .inl (some _) => ((EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1)) × ℝ
  | .inr _ => ((EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1)) ×
      EuclideanSpace ℝ (Fin 1)

abbrev SurgeryPatchModelSpace (P : TorusPairing C) (n : ℕ) : P.SurgeryPatchIndex n → Type
  | .inl none => C.kind.Space
  | .inl (some _) => ModelProd
      (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1))) ℝ
  | .inr _ => ModelProd
      (ModelProd (EuclideanSpace ℝ (Fin 1)) (EuclideanSpace ℝ (Fin 1)))
        (EuclideanHalfSpace 1)

abbrev SurgeryPatchSpace (P : TorusPairing C) (n : ℕ) : P.SurgeryPatchIndex n → Type u
  | .inl none => C.Carrier
  | .inl (some _) => ULift.{u} (Torus × ℝ)
  | .inr _ => ULift.{u} (Torus × EuclideanHalfSpace 1)

instance surgeryPatchVectorNormed (P : TorusPairing C) (n : ℕ) (i : P.SurgeryPatchIndex n) :
    NormedAddCommGroup (P.SurgeryPatchVector n i) := by
  rcases i with hi | hi
  · rcases hi with hj | hj <;> exact inferInstance
  · exact inferInstance

instance surgeryPatchVectorNormedSpace (P : TorusPairing C) (n : ℕ)
    (i : P.SurgeryPatchIndex n) : NormedSpace ℝ (P.SurgeryPatchVector n i) := by
  rcases i with hi | hi
  · rcases hi with hj | hj <;> exact inferInstance
  · exact inferInstance

instance surgeryPatchModelTopology (P : TorusPairing C) (n : ℕ)
    (i : P.SurgeryPatchIndex n) : TopologicalSpace (P.SurgeryPatchModelSpace n i) := by
  rcases i with hi | hi
  · rcases hi with hj | hj <;> exact inferInstance
  · exact inferInstance

instance surgeryPatchTopology (P : TorusPairing C) (n : ℕ) (i : P.SurgeryPatchIndex n) :
    TopologicalSpace (P.SurgeryPatchSpace n i) := by
  rcases i with hi | hi
  · rcases hi with hj | hj <;> exact inferInstance
  · exact inferInstance

instance surgeryPatchChartedSpace (P : TorusPairing C) (n : ℕ) (i : P.SurgeryPatchIndex n) :
    ChartedSpace (P.SurgeryPatchModelSpace n i) (P.SurgeryPatchSpace n i) := by
  rcases i with hi | hi
  · rcases hi with hj | hj
    · exact C.charts
    · exact uliftChartedSpace (P.SurgeryPatchModelSpace n (.inl (some hj))) (Torus × ℝ)
  · exact uliftChartedSpace (P.SurgeryPatchModelSpace n (.inr hi))
      (Torus × EuclideanHalfSpace 1)

abbrev surgeryPatchModel (P : TorusPairing C) (n : ℕ) (i : P.SurgeryPatchIndex n) :
    ModelWithCorners ℝ (P.SurgeryPatchVector n i) (P.SurgeryPatchModelSpace n i) := by
  rcases i with hi | hi
  · rcases hi with hj | hj
    · exact C.model
    · exact signedCollarModel
  · exact halfCollarModel

def surgeryPatch (P : TorusPairing C) (D : C.Components) {n : ℕ} (E : BoundaryTori C n)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target)
    (he : ∀ i j, Disjoint (E.collar i).target (P.surgerySideCollar j).target)
    (hb : C.model.boundary C.Carrier = (⋃ j, P.gluing.block j) ∪ E.image) :
    ∀ i : P.SurgeryPatchIndex n, OpenPartialHomeomorph (P.SurgeryPatchSpace n i)
      P.QuotientSpace := by
  intro i
  rcases i with hi | i
  · rcases hi with hi | j
    · exact P.surgeryInteriorPatch D (P.surgeryCoreBoundarySubset E hb)
    · let a := (uliftDiffeomorph.{0, u} signedCollarModel (Torus × ℝ)).symm
      exact a.toHomeomorph.toOpenPartialHomeomorph.trans (P.surgerySignedSeam hd j)
  · let a := (uliftDiffeomorph.{0, u} halfCollarModel (Torus × EuclideanHalfSpace 1)).symm
    exact a.toHomeomorph.toOpenPartialHomeomorph.trans (P.surgeryExternalCollar E he i)

theorem surgeryPatch_compatible (P : TorusPairing C) (D : C.Components) {n : ℕ}
    (E : BoundaryTori C n)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target)
    (he : ∀ i j, Disjoint (E.collar i).target (P.surgerySideCollar j).target)
    (hb : C.model.boundary C.Carrier = (⋃ j, P.gluing.block j) ∪ E.image)
    (i j : P.SurgeryPatchIndex n) :
    ContMDiffOn (P.surgeryPatchModel n i) (P.surgeryPatchModel n j) ∞
      ((P.surgeryPatch D E hd he hb i).trans (P.surgeryPatch D E hd he hb j).symm)
      ((P.surgeryPatch D E hd he hb i).trans (P.surgeryPatch D E hd he hb j).symm).source := by
  classical
  let hbound := P.surgeryCoreBoundarySubset E hb
  rcases i with hi | i
  · rcases hi with hi | i
    · rcases j with hj | j
      · rcases hj with hj | j
        · exact contMDiffOn_surgerySelfTransition _
        · have h := contMDiffOn_surgeryLiftedTransition
            (Diffeomorph.refl C.model C.Carrier ∞)
            (uliftDiffeomorph.{0, u} signedCollarModel (Torus × ℝ)).symm
            (P.surgeryInteriorPatch D hbound) (P.surgerySignedSeam hd j)
            (P.contMDiffOn_surgeryInteriorPatch_trans_seam_symm D hbound hd j)
            (P.contMDiffOn_surgerySeam_trans_interior_symm D hbound hd j)
          simpa [surgeryPatch] using h
      · have h := contMDiffOn_surgeryLiftedTransition
          (Diffeomorph.refl C.model C.Carrier ∞)
          (uliftDiffeomorph.{0, u} halfCollarModel (Torus × EuclideanHalfSpace 1)).symm
          (P.surgeryInteriorPatch D hbound) (P.surgeryExternalCollar E he j)
          (P.contMDiffOn_surgeryInteriorPatch_trans_external_symm D hbound E he j)
          (P.contMDiffOn_surgeryExternal_trans_interior_symm D hbound E he j)
        simpa [surgeryPatch] using h
    · rcases j with hj | j
      · rcases hj with hj | j
        · have h := contMDiffOn_surgeryLiftedTransition
            (uliftDiffeomorph.{0, u} signedCollarModel (Torus × ℝ)).symm
            (Diffeomorph.refl C.model C.Carrier ∞)
            (P.surgerySignedSeam hd i) (P.surgeryInteriorPatch D hbound)
            (P.contMDiffOn_surgerySeam_trans_interior_symm D hbound hd i)
            (P.contMDiffOn_surgeryInteriorPatch_trans_seam_symm D hbound hd i)
          simpa [surgeryPatch] using h
        · by_cases hij : i = j
          · subst j
            exact contMDiffOn_surgerySelfTransition _
          · exact contMDiffOn_surgeryLiftedTransition
              (uliftDiffeomorph.{0, u} signedCollarModel (Torus × ℝ)).symm
              (uliftDiffeomorph.{0, u} signedCollarModel (Torus × ℝ)).symm
              (P.surgerySignedSeam hd i) (P.surgerySignedSeam hd j)
              (contMDiffOn_surgeryDisjointTransition _ _
                (P.surgerySignedSeam_disjoint hd hij))
              (contMDiffOn_surgeryDisjointTransition _ _
                (P.surgerySignedSeam_disjoint hd (Ne.symm hij)))
      · exact contMDiffOn_surgeryLiftedTransition
          (uliftDiffeomorph.{0, u} signedCollarModel (Torus × ℝ)).symm
          (uliftDiffeomorph.{0, u} halfCollarModel (Torus × EuclideanHalfSpace 1)).symm
          (P.surgerySignedSeam hd i) (P.surgeryExternalCollar E he j)
          (contMDiffOn_surgeryDisjointTransition _ _
            (P.surgeryExternalCollar_seam_disjoint E he hd j i).symm)
          (contMDiffOn_surgeryDisjointTransition _ _
            (P.surgeryExternalCollar_seam_disjoint E he hd j i))
  · rcases j with hj | j
    · rcases hj with hj | j
      · have h := contMDiffOn_surgeryLiftedTransition
          (uliftDiffeomorph.{0, u} halfCollarModel (Torus × EuclideanHalfSpace 1)).symm
          (Diffeomorph.refl C.model C.Carrier ∞)
          (P.surgeryExternalCollar E he i) (P.surgeryInteriorPatch D hbound)
          (P.contMDiffOn_surgeryExternal_trans_interior_symm D hbound E he i)
          (P.contMDiffOn_surgeryInteriorPatch_trans_external_symm D hbound E he i)
        simpa [surgeryPatch] using h
      · exact contMDiffOn_surgeryLiftedTransition
          (uliftDiffeomorph.{0, u} halfCollarModel (Torus × EuclideanHalfSpace 1)).symm
          (uliftDiffeomorph.{0, u} signedCollarModel (Torus × ℝ)).symm
          (P.surgeryExternalCollar E he i) (P.surgerySignedSeam hd j)
          (contMDiffOn_surgeryDisjointTransition _ _
            (P.surgeryExternalCollar_seam_disjoint E he hd i j))
          (contMDiffOn_surgeryDisjointTransition _ _
            (P.surgeryExternalCollar_seam_disjoint E he hd i j).symm)
    · by_cases hij : i = j
      · subst j
        exact contMDiffOn_surgerySelfTransition _
      · exact contMDiffOn_surgeryLiftedTransition
          (uliftDiffeomorph.{0, u} halfCollarModel (Torus × EuclideanHalfSpace 1)).symm
          (uliftDiffeomorph.{0, u} halfCollarModel (Torus × EuclideanHalfSpace 1)).symm
          (P.surgeryExternalCollar E he i) (P.surgeryExternalCollar E he j)
          (contMDiffOn_surgeryDisjointTransition _ _
            (P.surgeryExternalCollar_targets_disjoint E he hij))
          (contMDiffOn_surgeryDisjointTransition _ _
            (P.surgeryExternalCollar_targets_disjoint E he (Ne.symm hij)))

theorem surgeryPatch_cover (P : TorusPairing C) (D : C.Components) {n : ℕ}
    (E : BoundaryTori C n)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target)
    (he : ∀ i j, Disjoint (E.collar i).target (P.surgerySideCollar j).target)
    (hb : C.model.boundary C.Carrier = (⋃ j, P.gluing.block j) ∪ E.image)
    (q : P.QuotientSpace) : ∃ i, q ∈ (P.surgeryPatch D E hd he hb i).target := by
  rcases P.surgeryPatches_cover D E hd he hb q with hi | hs | hext
  · exact ⟨.inl none, hi⟩
  · obtain ⟨j, hj⟩ := hs
    refine ⟨.inl (some j), ?_⟩
    simpa [surgeryPatch] using hj
  · obtain ⟨j, hj⟩ := hext
    refine ⟨.inr j, ?_⟩
    simpa [surgeryPatch] using hj

theorem surgeryPatch_half_coordinates (P : TorusPairing C) (D : C.Components) {n : ℕ}
    (E : BoundaryTori C n)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target)
    (he : ∀ i j, Disjoint (E.collar i).target (P.surgerySideCollar j).target)
    (hb : C.model.boundary C.Carrier = (⋃ j, P.gluing.block j) ∪ E.image)
    (i : P.SurgeryPatchIndex n) (x : P.SurgeryPatchSpace n i)
    (hx : x ∈ (P.surgeryPatch D E hd he hb i).source) :
    ∃ d : PartialDiffeomorph (P.surgeryPatchModel n i) (𝓡∂ 3)
      (P.SurgeryPatchSpace n i) (EuclideanHalfSpace 3) ∞, x ∈ d.source := by
  rcases i with hi | i
  · rcases hi with hi | i
    · have hxi : x ∈ C.interior := (P.surgeryInteriorPatch_source D
        (P.surgeryCoreBoundarySubset E hb)).subset hx
      obtain ⟨d, hd⟩ := exists_surgeryInteriorCoordinates C hxi
      exact exists_surgeryHalfCoordinates_of_euclidean d hd
    · obtain ⟨d, hd⟩ := exists_surgerySignedCoordinates x.down
      obtain ⟨a, ha⟩ := exists_surgeryHalfCoordinates_of_euclidean d hd
      let l := (uliftDiffeomorph.{0, u} signedCollarModel (Torus × ℝ)).symm
      exact ⟨l.toPartialDiffeomorph.trans a, mem_univ x, ha⟩
  · obtain ⟨d, hd⟩ := exists_surgeryHalfCollarCoordinates x.down
    let l := (uliftDiffeomorph.{0, u} halfCollarModel (Torus × EuclideanHalfSpace 1)).symm
    exact ⟨l.toPartialDiffeomorph.trans d, mem_univ x, hd⟩

theorem exists_surgeryHalfQuotientAtlas (P : TorusPairing C) (D : C.Components) {n : ℕ}
    (E : BoundaryTori C n)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target)
    (he : ∀ i j, Disjoint (E.collar i).target (P.surgerySideCollar j).target)
    (hb : C.model.boundary C.Carrier = (⋃ j, P.gluing.block j) ∪ E.image) :
    ∃ A : ChartedSpace (EuclideanHalfSpace 3) P.QuotientSpace, letI := A
      IsManifold (𝓡∂ 3) ∞ P.QuotientSpace ∧ ∀ i,
        ContMDiffOn (P.surgeryPatchModel n i) (𝓡∂ 3) ∞
          (P.surgeryPatch D E hd he hb i) (P.surgeryPatch D E hd he hb i).source ∧
        ContMDiffOn (𝓡∂ 3) (P.surgeryPatchModel n i) ∞
          (P.surgeryPatch D E hd he hb i).symm (P.surgeryPatch D E hd he hb i).target :=
  exists_carrierSurgeryAtlas_of_openCover (𝓡∂ 3) (P.surgeryPatch D E hd he hb)
    (P.surgeryPatch_cover D E hd he hb) (P.surgeryPatch_compatible D E hd he hb)
    (P.surgeryPatch_half_coordinates D E hd he hb)

theorem surgeryPatch_closed_coordinates (P : TorusPairing C) (D : C.Components)
    (E : BoundaryTori C 0)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target)
    (he : ∀ i j, Disjoint (E.collar i).target (P.surgerySideCollar j).target)
    (hb : C.model.boundary C.Carrier = (⋃ j, P.gluing.block j) ∪ E.image)
    (i : P.SurgeryPatchIndex 0) (x : P.SurgeryPatchSpace 0 i)
    (hx : x ∈ (P.surgeryPatch D E hd he hb i).source) :
    ∃ d : PartialDiffeomorph (P.surgeryPatchModel 0 i) (𝓡 3)
      (P.SurgeryPatchSpace 0 i) (EuclideanSpace ℝ (Fin 3)) ∞, x ∈ d.source := by
  rcases i with hi | i
  · rcases hi with hi | i
    · exact exists_surgeryInteriorCoordinates C ((P.surgeryInteriorPatch_source D
        (P.surgeryCoreBoundarySubset E hb)).subset hx)
    · obtain ⟨d, hd⟩ := exists_surgerySignedCoordinates x.down
      let l := (uliftDiffeomorph.{0, u} signedCollarModel (Torus × ℝ)).symm
      exact ⟨l.toPartialDiffeomorph.trans d, mem_univ x, hd⟩
  · exact i.elim0

theorem exists_surgeryClosedQuotientAtlas (P : TorusPairing C) (D : C.Components)
    (E : BoundaryTori C 0)
    (hd : Pairwise fun i j => Disjoint (P.surgerySideCollar i).target
      (P.surgerySideCollar j).target)
    (he : ∀ i j, Disjoint (E.collar i).target (P.surgerySideCollar j).target)
    (hb : C.model.boundary C.Carrier = (⋃ j, P.gluing.block j) ∪ E.image) :
    ∃ A : ChartedSpace (EuclideanSpace ℝ (Fin 3)) P.QuotientSpace, letI := A
      IsManifold (𝓡 3) ∞ P.QuotientSpace ∧ ∀ i,
        ContMDiffOn (P.surgeryPatchModel 0 i) (𝓡 3) ∞
          (P.surgeryPatch D E hd he hb i) (P.surgeryPatch D E hd he hb i).source ∧
        ContMDiffOn (𝓡 3) (P.surgeryPatchModel 0 i) ∞
          (P.surgeryPatch D E hd he hb i).symm (P.surgeryPatch D E hd he hb i).target :=
  exists_carrierSurgeryAtlas_of_openCover (𝓡 3) (P.surgeryPatch D E hd he hb)
    (P.surgeryPatch_cover D E hd he hb) (P.surgeryPatch_compatible D E hd he hb)
    (P.surgeryPatch_closed_coordinates D E hd he hb)

end GC.GraphManifold.TorusPairing
