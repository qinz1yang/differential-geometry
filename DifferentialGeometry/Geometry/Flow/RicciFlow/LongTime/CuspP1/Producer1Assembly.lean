import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.Producer1AssemblyBasic
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspExteriorProducers

/-!
# Producer 1 (CP1-H): conditional assembly skeleton

`exists_primitive_meridian_of_compressible_seam_CPH` has the conclusion of
`GC.LongTime.exists_primitive_meridian_of_compressible_seam`; its hypotheses are those of that
theorem plus the explicit remaining inputs below.  Already-delivered theorems are called directly:
`exists_persistentCuspExterior_compressible_port_CPE2` (which wraps CPE port selection, CPE2 gluing
adapter and the tree's K09c `injective_seamTorus_of_ports`), and the tree's
`exists_decompositionPresentation` (via the glue lemma `hseam_of_decompositionPresentation_CPH`,
which discharges `G` and `hseam` of CPE2).

| remaining input | sub-package / lane | this round? |
|---|---|---|
| `hperi` (cusp torus pi1-injects into its truncated core) | HORO / CP1-F3 | in progress (CP1-F3) |
| `hports_of` (piece boundary tori of the tree's decomposition presentation incompressible given core + exterior ports pi1-injective) | CP1-G (`hports_of_CPG`) | in progress (CP1-G) |
| `hloop` (non-injective port => embedded primitive loop whose class dies; Loop Theorem) | P1c | NOT this round |
| `hshort` (deep truncation + embedded smooth primitive closed geodesic that is short, freely homotopic to the Loop-Theorem loop, still compressible in the deeper region at its start) | CP1-A2 (+ region transfer of the Loop-Theorem disk) | in progress (CP1-A2) / transfer not this round |
| `hpersist` (compressibility persists for all `t >= start`: kernel invariance across surgery times) | CP1-D2 (`kernel_const_Ici_CPD2`, `patch_kernel_const_across_events_CPD2`) + exterior-region isotopy | in progress (CP1-D2); exterior-region part not this round |
| `hspan` (compressible embedded loop => embedded spanning disk in the exterior region, `spans` field) | Meeks-Yau / P2 | NOT this round |

Already used and no longer assumptions: CP1-C/C2 (through K09c inside CPE2), CP1-E, CP1-E2,
CP1-F (reduction, not needed with explicit `hperi`), CP1-D/CP1-A (consumed by `hpersist`/`hshort`
dischargers, no shape mismatch found: `portLoopMap_CPH` is the common cusp-torus-to-stage map).
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Seifert GC.Topology
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

theorem exists_primitive_meridian_of_compressible_seam_CPH
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices)
    (j : ℕ) (hj : L.first ≤ j) (C : ConnectedComponents (slices j).stage.Carrier)
    (s : Fin (L.decomposition j C).boundary.count) (x : Torus)
    (hcomp : ¬ Function.Injective (FundamentalGroup.map
      ((L.decomposition j C).reconstructionAtlas.torusInPrime (L.decomposition j C).reconstruction s) x))
    -- HORO (CP1-F3)
    (hperi : ∀ (i : Fin L.cores.count) (q : Fin (L.truncation j i).count) (y : Torus),
      Function.Injective (FundamentalGroup.map ((L.truncation j i).boundary.boundaryMap q) y))
    -- CP1-G
    (hports_of : ∀ Pr : TorusDecomposition.DecompositionPresentation (L.decomposition j C),
      (∀ (s' : Fin (L.decomposition j C).boundary.count) (y : Torus),
        Function.Injective (FundamentalGroup.map
          (extPortMap_CPE L j hj (L.port j hj ⟨C, s'⟩).1 (L.port j hj ⟨C, s'⟩).2) y)) →
      (∀ (s' : Fin (L.decomposition j C).boundary.count) (y : Torus),
        Function.Injective (FundamentalGroup.map
          ((L.truncation j (L.port j hj ⟨C, s'⟩).1).boundary.boundaryMap
            (L.port j hj ⟨C, s'⟩).2) y)) →
      ∀ i, (Pr.presentation.pieceBoundaryTori i).incompressible)
    -- Loop Theorem (P1c), not this round
    (hloop : ∀ (E : PersistentCuspExterior L.cores), E = persistentExterior_CPE2 L j hj →
      ∀ (i : Fin L.cores.count) (q : Fin (E.truncation i).count) (y : Torus)
        (φ : C(Torus, ↥(E.region E.start))),
        (∀ z, (φ z : (postStage F.observation E.start).Carrier) =
          portLoopMap_CPH E i q E.start le_rfl z) →
        ¬ Function.Injective (FundamentalGroup.map φ y) →
        ∃ γ : freeLoop Torus, Topology.IsEmbedding γ ∧
          (∃ e : FundamentalGroup Torus (γ 0) ≃* Multiplicative ℤ × Multiplicative ℤ,
            e (loopDegreeClass γ 1) = (Multiplicative.ofAdd 1, 1)) ∧
          loopDegreeClass γ 1 ∈ (FundamentalGroup.map φ (γ 0)).ker)
    -- CP1-A2 (deep truncation, short geodesic) + region transfer
    (hshort : ∀ (E : PersistentCuspExterior L.cores), E = persistentExterior_CPE2 L j hj →
      ∀ (i : Fin L.cores.count) (q : Fin (E.truncation i).count)
        (φ : C(Torus, ↥(E.region E.start))),
        (∀ z, (φ z : (postStage F.observation E.start).Carrier) =
          portLoopMap_CPH E i q E.start le_rfl z) →
        ∀ γ : freeLoop Torus, Topology.IsEmbedding γ →
          (∃ e : FundamentalGroup Torus (γ 0) ≃* Multiplicative ℤ × Multiplicative ℤ,
            e (loopDegreeClass γ 1) = (Multiplicative.ofAdd 1, 1)) →
          loopDegreeClass γ 1 ∈ (FundamentalGroup.map φ (γ 0)).ker →
        ∃ (E' : PersistentCuspExterior L.cores) (i' : Fin L.cores.count)
          (q' : Fin (E'.truncation i').count) (loop : freeLoop Torus),
          Topology.IsEmbedding loop ∧
          ContMDiff 𝓘(ℝ, ℝ) torusModel ∞ (loopLift loop) ∧
          DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesic
            ((E'.truncation i').cusp q').torusMetric (loopLift loop) ∧
          (∃ e : FundamentalGroup Torus (loop 0) ≃* Multiplicative ℤ × Multiplicative ℤ,
            e (loopDegreeClass loop 1) = (Multiplicative.ofAdd 1, 1)) ∧
          (∃ L' : ℝ, 0 < L' ∧ L' < 1 ∧ ∀ s : ℝ,
            let v := mfderiv 𝓘(ℝ, ℝ) torusModel (loopLift loop) s 1;
            ((E'.truncation i').cusp q').torusMetric.inner (loopLift loop s) v v ≤ L' ^ 2) ∧
          (∃ φ' : C(Torus, ↥(E'.region E'.start)),
            (∀ z, (φ' z : (postStage F.observation E'.start).Carrier) =
              portLoopMap_CPH E' i' q' E'.start le_rfl z) ∧
            loopDegreeClass loop 1 ∈ (FundamentalGroup.map φ' (loop 0)).ker))
    -- CP1-D2 (+ exterior-region isotopy)
    (hpersist : ∀ (E' : PersistentCuspExterior L.cores) (i' : Fin L.cores.count)
        (q' : Fin (E'.truncation i').count) (loop : freeLoop Torus),
        Topology.IsEmbedding loop →
        ContMDiff 𝓘(ℝ, ℝ) torusModel ∞ (loopLift loop) →
        DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesic
          ((E'.truncation i').cusp q').torusMetric (loopLift loop) →
        (∃ e : FundamentalGroup Torus (loop 0) ≃* Multiplicative ℤ × Multiplicative ℤ,
          e (loopDegreeClass loop 1) = (Multiplicative.ofAdd 1, 1)) →
        (∃ φ' : C(Torus, ↥(E'.region E'.start)),
          (∀ z, (φ' z : (postStage F.observation E'.start).Carrier) =
            portLoopMap_CPH E' i' q' E'.start le_rfl z) ∧
          loopDegreeClass loop 1 ∈ (FundamentalGroup.map φ' (loop 0)).ker) →
        ∀ (t : ℝ) (ht : E'.start ≤ t),
          ∃ φt : C(Torus, ↥(E'.region t)),
            (∀ z, (φt z : (postStage F.observation t).Carrier) =
              portLoopMap_CPH E' i' q' t ht z) ∧
            loopDegreeClass loop 1 ∈ (FundamentalGroup.map φt (loop 0)).ker)
    -- Meeks-Yau / P2, not this round
    (hspan : ∀ (E' : PersistentCuspExterior L.cores) (i' : Fin L.cores.count)
        (q' : Fin (E'.truncation i').count) (loop : freeLoop Torus),
        Topology.IsEmbedding loop → ∀ (t : ℝ) (ht : E'.start ≤ t),
        (∃ φt : C(Torus, ↥(E'.region t)),
          (∀ z, (φt z : (postStage F.observation t).Carrier) =
            portLoopMap_CPH E' i' q' t ht z) ∧
          loopDegreeClass loop 1 ∈ (FundamentalGroup.map φt (loop 0)).ker) →
        ∃ u : C(closedDisk, (postStage F.observation t).Carrier),
          isExteriorSpanningDisk (E'.region t) ((portLoopMap_CPH E' i' q' t ht).comp loop) u) :
    Nonempty (PrescribedCuspMeridian L.cores) := by
  obtain ⟨Pr⟩ := TorusDecomposition.exists_decompositionPresentation _ (L.decomposition j C)
  obtain ⟨E, hE, i, q, y, φ, hφ, hn⟩ :=
    exists_persistentCuspExterior_compressible_port_CPE2 L j hj C s x hcomp hperi
      Pr.presentation (hseam_of_decompositionPresentation_CPH Pr) (hports_of Pr)
  have hφ' : ∀ z, (φ z : (postStage F.observation E.start).Carrier) =
      portLoopMap_CPH E i q E.start le_rfl z := fun z => hφ z
  obtain ⟨γ, hγe, hγp, hγk⟩ := hloop E hE i q y φ hφ' hn
  obtain ⟨E', i', q', loop, he, hsm, hgeo, hprim, hshortL, hc0⟩ :=
    hshort E hE i q φ hφ' γ hγe hγp hγk
  have hc := hpersist E' i' q' loop he hsm hgeo hprim hc0
  exact ⟨{
    exterior := E'
    model := i'
    port := q'
    loop := loop
    embedded := he
    smooth := hsm
    geodesic := hgeo
    primitive := hprim
    short := hshortL
    transported := fun t ht => (portLoopMap_CPH E' i' q' t ht).comp loop
    prescribed := fun t ht x => rfl
    spans := fun t ht => hspan E' i' q' loop he t ht (hc t ht) }⟩

end GC.LongTime.CuspP1
