import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.Producer1AssemblyBasic
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.PresentationOfCut
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspExteriorProducers

/-!
# Producer 1 (CP1-H2): assembly V2, `hports_of` removed

Same as `exists_primitive_meridian_of_compressible_seam_CPH`, but the presentation is the specific
`dp_CPG (L.decomposition j C)` and `hports_of_CPG` (CP1-G) discharges `hports_of`.
Remaining inputs: `hperi`, `hloop`, `hshort`, `hpersist`, `hspan` (unchanged shapes).
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Seifert GC.Topology
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

theorem exists_primitive_meridian_of_compressible_seam_CPH2
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
  obtain ⟨E, hE, i, q, y, φ, hφ, hn⟩ :=
    exists_persistentCuspExterior_compressible_port_CPE2 L j hj C s x hcomp hperi
      (dp_CPG (L.decomposition j C)).presentation
      (hseam_of_decompositionPresentation_CPH (dp_CPG (L.decomposition j C)))
      (hports_of_CPG L j hj C)
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
