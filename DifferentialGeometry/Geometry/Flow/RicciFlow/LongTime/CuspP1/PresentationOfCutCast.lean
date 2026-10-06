import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.PortSelection
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.ExteriorDiskFlow

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.Topology Set
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {K : ℕ} {slices : ℕ → RegularSlice F.observation}

theorem exists_homeo_of_eq_CPG {X Y : OrientedThreeStage.{u}} (h : X = Y) :
    ∃ φ : X.Carrier ≃ₜ Y.Carrier,
      ∀ (S : Set X.Carrier) (T : Set Y.Carrier), HEq S T → φ '' S = T := by
  subst h
  exact ⟨Homeomorph.refl _, fun S T hST => by
    have := eq_of_heq hST
    subst this
    simp⟩

/-- Homeomorphism between the `postStage` at the slice time and the slice stage, compatible with
`HEq` of subsets. -/
theorem exists_slicePhi_CPG (s : RegularSlice F.observation) :
    ∃ φ : (postStage F.observation s.time).Carrier ≃ₜ s.stage.Carrier,
      ∀ (S : Set (postStage F.observation s.time).Carrier) (T : Set s.stage.Carrier),
        HEq S T → φ '' S = T :=
  exists_homeo_of_eq_CPG (postStage_regularSlice F.observation s)

/-- Continuous map of the `i`-th truncated core into the stage at the slice time. -/
def coreMap_CPG (L : LateCutFamily F K slices) (j : ℕ) (hj : L.first ≤ j)
    (i : Fin L.cores.count) : C((L.truncation j i).core.Carrier, (postStage F.observation (slices j).time).Carrier) :=
  ⟨fun c => L.cores.map i (slices j).time (L.time_late j hj) ((L.truncation j i).inclusion c), by
    have hmem := inclusion_mem_domain_CPE L j hj i
    have hcm := (L.cores.smooth i (slices j).time (L.time_late j hj)).continuousOn
    exact hcm.comp_continuous (L.truncation j i).inclusion.continuous hmem⟩

theorem coreMap_isEmbedding_CPG (L : LateCutFamily F K slices) (j : ℕ) (hj : L.first ≤ j)
    (i : Fin L.cores.count) : _root_.Topology.IsEmbedding (coreMap_CPG L j hj i) := by
  let ι' : C((L.truncation j i).core.Carrier, ↥(L.cores.domain i (slices j).time)) :=
    ⟨fun c => ⟨(L.truncation j i).inclusion c, inclusion_mem_domain_CPE L j hj i c⟩,
      Continuous.subtype_mk (L.truncation j i).inclusion.continuous _⟩
  have h1 : _root_.Topology.IsEmbedding (fun x : ↥(L.cores.domain i (slices j).time) =>
      L.cores.map i (slices j).time (L.time_late j hj) x) :=
    (L.cores.embedding i (slices j).time (L.time_late j hj)).isEmbedding
  have h2 : _root_.Topology.IsEmbedding ι' := by
    refine _root_.Topology.IsEmbedding.of_comp ι'.continuous continuous_subtype_val ?_
    exact (L.truncation j i).embedding.isEmbedding
  exact h1.comp h2

theorem coreMap_boundary_CPG (L : LateCutFamily F K slices) (j : ℕ) (hj : L.first ≤ j)
    (i : Fin L.cores.count) (q : Fin (L.truncation j i).count) (x : Torus) :
    coreMap_CPG L j hj i ((L.truncation j i).boundary.boundaryMap q x) = portPoint_CPE L j hj i q x := by
  change L.cores.map i (slices j).time (L.time_late j hj)
      ((L.truncation j i).inclusion ((L.truncation j i).boundary.torusMap q x)) = _
  rw [← (L.truncation j i).cusp_zero q x]
  rfl

theorem portPoint_isEmbedding_CPG (L : LateCutFamily F K slices) (j : ℕ) (hj : L.first ≤ j)
    (i : Fin L.cores.count) (q : Fin (L.truncation j i).count) :
    _root_.Topology.IsEmbedding (portPoint_CPE L j hj i q) := by
  have : portPoint_CPE L j hj i q = coreMap_CPG L j hj i ∘ (L.truncation j i).boundary.boundaryMap q := by
    funext x; exact (coreMap_boundary_CPG L j hj i q x).symm
  rw [this]
  exact (coreMap_isEmbedding_CPG L j hj i).comp ((L.truncation j i).boundary.torusMap_isEmbedding q)

/-- The seam torus of the decomposition and the cusp torus of its port agree up to a homeomorphism
of `Torus`. -/
theorem exists_seam_reparam_CPG (L : LateCutFamily F K slices) (j : ℕ) (hj : L.first ≤ j)
    (C : ConnectedComponents (slices j).stage.Carrier)
    (s : Fin (L.decomposition j C).boundary.count)
    (φ : (postStage F.observation (slices j).time).Carrier ≃ₜ (slices j).stage.Carrier)
    (hφ : ∀ (S : Set (postStage F.observation (slices j).time).Carrier)
      (T : Set (slices j).stage.Carrier), HEq S T → φ '' S = T) :
    ∃ e : Torus ≃ₜ Torus, ∀ x,
      (((L.decomposition j C).reconstructionAtlas.torusInPrime
        (L.decomposition j C).reconstruction s x).val) =
        φ (portPoint_CPE L j hj (L.port j hj ⟨C, s⟩).1 (L.port j hj ⟨C, s⟩).2 (e x)) := by
  have hrange := hφ _ _ (L.seam_image j hj C s)
  have hg : _root_.Topology.IsEmbedding (fun x : Torus =>
      ((L.decomposition j C).reconstructionAtlas.torusInPrime (L.decomposition j C).reconstruction s x).val) :=
    _root_.Topology.IsEmbedding.subtypeVal.comp ((L.decomposition j C).reconstructionAtlas.torusInPrime_isEmbedding (L.decomposition j C).reconstruction s)
  have hf : _root_.Topology.IsEmbedding (fun x : Torus =>
      φ (portPoint_CPE L j hj (L.port j hj ⟨C, s⟩).1 (L.port j hj ⟨C, s⟩).2 x)) :=
    φ.isEmbedding.comp (portPoint_isEmbedding_CPG L j hj _ _)
  have hr : Set.range (fun x : Torus =>
      φ (portPoint_CPE L j hj (L.port j hj ⟨C, s⟩).1 (L.port j hj ⟨C, s⟩).2 x)) =
      Set.range (fun x : Torus => ((L.decomposition j C).reconstructionAtlas.torusInPrime (L.decomposition j C).reconstruction s x).val) := by
    rw [← hrange, ← Set.image_univ, ← Set.image_univ, ← Set.image_comp]
    rfl
  let e : Torus ≃ₜ Torus := hg.toHomeomorph.trans
    ((Homeomorph.setCongr hr.symm).trans hf.toHomeomorph.symm)
  refine ⟨e, fun x => ?_⟩
  have hx := hf.toHomeomorph.apply_symm_apply
    ((Homeomorph.setCongr hr.symm) (hg.toHomeomorph x))
  exact (congrArg Subtype.val hx).symm

end GC.LongTime.CuspP1
