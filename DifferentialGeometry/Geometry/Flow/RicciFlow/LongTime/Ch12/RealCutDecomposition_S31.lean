import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BlockCoreSlice_S28
import DifferentialGeometry.Topology.Manifold.InteriorBoundary

set_option autoImplicit false
noncomputable section
open Set Function Manifold TopologicalSpace DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime
open scoped Manifold ContDiff
universe u
namespace GC.LongTime.Ch12

/-!
# S31 group G1: port/seam equation and block/complement dichotomy for the REAL cut

`sliceTorusDecomposition_S31` is `sliceTorusDecomposition_S19` with the decomposition fixed to
`sliceDec_S28 D ht C` (the S12 cut presentation of the seam family of `C`), obtained by exposing the
witness of `cutAlongTori_C2a_S12` instead of an existential.  `blockCore_complement_S31` and its
companions classify the blocks of the real cut against the truncated cores (via S28).
-/

section Port

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K} {t : ℝ}
  (D : TruncatedCutData_IF4 cores t) (ht : cores.start ≤ t)

/-- **S31 (a).** Statement of `sliceTorusDecomposition_S19` with `G C := sliceDec_S28 D ht C`. -/
theorem sliceTorusDecomposition_S31 :
    ∃ port : (Σ C : ConnectedComponents (postStage F.observation t).toClosedOrientedManifold.Carrier,
        Fin (sliceDec_S28 D ht C).boundary.count) ≃
          Σ i : Fin cores.count, Fin (D.truncation i).count,
      ∀ C (s : Fin (sliceDec_S28 D ht C).boundary.count) (p : Torus),
        ((sliceDec_S28 D ht C).reconstructionAtlas.torusInPrime
            (sliceDec_S28 D ht C).reconstruction s p).val =
          cores.map (port ⟨C, s⟩).1 t ht
            ((D.truncation (port ⟨C, s⟩).1).cuspMap (port ⟨C, s⟩).2 (p, halfZero)) := by
  have hex : ∀ C : ConnectedComponents (postStage F.observation t).toClosedOrientedManifold.Carrier,
      ∃ e : CIdx_S19 D ht C ≃ Fin (sliceDec_S28 D ht C).boundary.count,
        ∀ (x : CIdx_S19 D ht C) (p : Torus),
          (((sliceDec_S28 D ht C).reconstructionAtlas.torusInPrime
            (sliceDec_S28 D ht C).reconstruction (e x) p).val :
              (postStage F.observation t).Carrier) = stageCollar_S19 D ht x.1 (p, 0) := by
    intro C
    refine ⟨cidxEquiv_S19 D ht C, fun x p => ?_⟩
    have h := (cutPresentation_S12 (sliceM_S28 C)
      (componentFamily_S19 D ht C)).toTorusDecomposition_torusInPrime (cidxEquiv_S19 D ht C x) p
    have key : ∀ k : Fin (componentFamily_S19 D ht C).count,
        ((((componentFamily_S19 D ht C).collar k) (p, 0)).val :
          (postStage F.observation t).Carrier) =
          stageCollar_S19 D ht ((cidxEquiv_S19 D ht C).symm k).1 (p, 0) := fun k =>
      restrictCollar_apply_S19 _ _ _ (cidx_target_subset_S19 D ht _) (p, 0)
        (by rw [stageCollar_source_S19]; exact zero_mem_source_S19 p)
    have key' := key (cidxEquiv_S19 D ht C x)
    rw [Equiv.symm_apply_apply] at key'
    exact (congrArg Subtype.val h).trans key'
  choose e he using hex
  refine ⟨(Equiv.sigmaCongrRight fun C => (e C).symm).trans
    (Equiv.sigmaFiberEquiv (comp_S19 D ht)), fun C s p => ?_⟩
  have h := he C ((e C).symm s) p
  rw [Equiv.apply_symm_apply] at h
  rw [h]
  exact stageCollar_zero_S19 D ht _ p

end Port

section Complement

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K} {t : ℝ}
  (D : TruncatedCutData_IF4 cores t) (ht : cores.start ≤ t)
  (hdom : ∀ i, range (D.truncation i).inclusion ⊆ (cores.domain i t : Set (cores.model i).Carrier))
include hdom

omit hdom in
/-- The interior of a truncated core is nonempty. -/
theorem core_interior_nonempty_S31 (c : Fin cores.count) :
    ((D.truncation c).core.interior : Set (D.truncation c).core.Carrier).Nonempty := by
  have hne : Nonempty (D.truncation c).core.Carrier := (D.truncation c).connected.toNonempty
  have := hne
  exact (ModelWithCorners.dense_interior (I := (D.truncation c).core.model)
    (M := (D.truncation c).core.Carrier)).nonempty

/-- **S31 (b).** A block `j` of the real cut of `C` which is not the core block (image equal to the
core interior image) of any core `c` with `coreComp c = C` has interior image disjoint from every
`corePhi c '' core.interior` with `coreComp c = C`. -/
theorem blockCore_complement_S31
    (C : ConnectedComponents (postStage F.observation t).toClosedOrientedManifold.Carrier)
    (j : Fin (sliceDec_S28 D ht C).components.count)
    (hj : ∀ c : Fin cores.count, coreComp_S28 D ht c = C →
      blockImage_S28 D ht C j ≠ corePhi_S28 D ht c '' ((D.truncation c).core.interior : Set _)) :
    ∀ c : Fin cores.count, coreComp_S28 D ht c = C →
      Disjoint (blockImage_S28 D ht C j)
        (corePhi_S28 D ht c '' ((D.truncation c).core.interior : Set _)) := by
  intro c hc
  subst hc
  obtain ⟨jc, -, himg, hdisj⟩ := blockCoreIdentification_S28 D ht hdom c
  by_cases hjj : j = jc
  · subst hjj
    exact absurd himg (hj c rfl)
  · exact hdisj j hjj

/-- **S31 (b), dichotomy.**  Every block of the real cut of `C` is either a complement block (its
interior image is disjoint from every core interior image) or is diffeomorphic to the interior of the
truncated core `c` it meets, with `coreComp c = C`. -/
theorem block_core_or_complement_S31
    (C : ConnectedComponents (postStage F.observation t).toClosedOrientedManifold.Carrier)
    (j : Fin (sliceDec_S28 D ht C).components.count) :
    (∀ c : Fin cores.count, coreComp_S28 D ht c = C →
        Disjoint (blockImage_S28 D ht C j)
          (corePhi_S28 D ht c '' ((D.truncation c).core.interior : Set _))) ∨
      ∃ c : Fin cores.count, coreComp_S28 D ht c = C ∧
        Nonempty (Diffeomorph (sliceDec_S28 D ht C).carrier.model (D.truncation c).core.model
          ((sliceDec_S28 D ht C).carrier.pieceInterior
            ((sliceDec_S28 D ht C).components.piece j))
          (D.truncation c).core.interior ∞) := by
  by_cases hall : ∀ c : Fin cores.count, coreComp_S28 D ht c = C →
      Disjoint (blockImage_S28 D ht C j)
        (corePhi_S28 D ht c '' ((D.truncation c).core.interior : Set _))
  · exact Or.inl hall
  · right
    push Not at hall
    obtain ⟨c, hc, hnd⟩ := hall
    subst hc
    obtain ⟨jc, hdiff, -, hdisj⟩ := blockCoreIdentification_S28 D ht hdom c
    by_cases hjj : j = jc
    · subst hjj
      exact ⟨c, rfl, hdiff⟩
    · exact absurd (hdisj j hjj) hnd

/-- **S31 (b), different cores give different blocks.**  If the block `j` has interior image equal
to that of the core `c` and the block `j'` that of the core `c' ≠ c` (both in `C`), then `j ≠ j'`. -/
theorem blockCore_injective_S31
    (C : ConnectedComponents (postStage F.observation t).toClosedOrientedManifold.Carrier)
    {c c' : Fin cores.count} (hcc : c ≠ c')
    (j j' : Fin (sliceDec_S28 D ht C).components.count)
    (hj : blockImage_S28 D ht C j = corePhi_S28 D ht c '' ((D.truncation c).core.interior : Set _))
    (hj' : blockImage_S28 D ht C j' =
      corePhi_S28 D ht c' '' ((D.truncation c').core.interior : Set _)) :
    j ≠ j' := by
  rintro rfl
  obtain ⟨x, hx⟩ := core_interior_nonempty_S31 D c
  have h1 : corePhi_S28 D ht c x ∈ blockImage_S28 D ht C j := by
    rw [hj]; exact ⟨x, hx, rfl⟩
  rw [hj'] at h1
  obtain ⟨y, -, hy⟩ := h1
  exact corePhi_ne_S28 D ht hdom hcc x y hy.symm

end Complement

end GC.LongTime.Ch12
