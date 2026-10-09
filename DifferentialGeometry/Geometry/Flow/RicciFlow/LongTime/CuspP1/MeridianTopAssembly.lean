import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.Producer1AssemblyV2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.MeridianTop

/-!
# CP1-Q3: Producer 1 assembly V3 (Top interface)

`hspan` is removed (the continuous filling comes from the kernel via `exists_disk_of_ker_CPQ`).
`hloop` is narrowed per review Q2 to "non-injective port => essential embedded closed curve on `T`
that is nullhomotopic in the exterior region"; the extra input `hprim` says that an essential
embedded loop on `Torus` has primitive class.  Remaining inputs: `hperi`, `hloop`, `hprim`,
`hshort`, `hpersist`.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Seifert GC.Topology
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

theorem exists_primitive_meridian_top_CPQ
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
    -- Loop Theorem output, minimal form (review Q2): essential embedded curve, null in the exterior
    (hloop : ∀ (E : PersistentCuspExterior L.cores), E = persistentExterior_CPE2 L j hj →
      ∀ (i : Fin L.cores.count) (q : Fin (E.truncation i).count) (y : Torus)
        (φ : C(Torus, ↥(E.region E.start))),
        (∀ z, (φ z : (postStage F.observation E.start).Carrier) =
          portLoopMap_CPH E i q E.start le_rfl z) →
        ¬ Function.Injective (FundamentalGroup.map φ y) →
        ∃ γ : freeLoop Torus, Topology.IsEmbedding γ ∧ ¬ γ.Nullhomotopic ∧
          loopDegreeClass γ 1 ∈ (FundamentalGroup.map φ (γ 0)).ker)
    -- planar topology of the torus: essential embedded loop has primitive class
    (hprim : ∀ γ : freeLoop Torus, Topology.IsEmbedding γ → ¬ γ.Nullhomotopic →
      ∃ e : FundamentalGroup Torus (γ 0) ≃* Multiplicative ℤ × Multiplicative ℤ,
        e (loopDegreeClass γ 1) = (Multiplicative.ofAdd 1, 1))
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
            loopDegreeClass loop 1 ∈ (FundamentalGroup.map φt (loop 0)).ker) :
    Nonempty (PrescribedCuspMeridianTop_CPQ L.cores) := by
  obtain ⟨E, hE, i, q, y, φ, hφ, hn⟩ :=
    exists_persistentCuspExterior_compressible_port_CPE2 L j hj C s x hcomp hperi
      (dp_CPG (L.decomposition j C)).presentation
      (hseam_of_decompositionPresentation_CPH (dp_CPG (L.decomposition j C)))
      (hports_of_CPG L j hj C)
  have hφ' : ∀ z, (φ z : (postStage F.observation E.start).Carrier) =
      portLoopMap_CPH E i q E.start le_rfl z := fun z => hφ z
  obtain ⟨γ, hγe, hγn, hγk⟩ := hloop E hE i q y φ hφ' hn
  obtain ⟨E', i', q', loop, he, hsm, hgeo, hprim', hshortL, hc0⟩ :=
    hshort E hE i q φ hφ' γ hγe (hprim γ hγe hγn) hγk
  have hc := hpersist E' i' q' loop he hsm hgeo hprim' hc0
  exact ⟨{
    exterior := E'
    model := i'
    port := q'
    loop := loop
    embedded := he
    smooth := hsm
    geodesic := hgeo
    primitive := hprim'
    short := hshortL
    transported := fun t ht => (portLoopMap_CPH E' i' q' t ht).comp loop
    prescribed := fun t ht x => rfl
    fills := fun t ht => by
      obtain ⟨φt, hφt, hk⟩ := hc t ht
      obtain ⟨u, hu, hr⟩ := exists_disk_of_ker_CPQ φt loop hk
      refine ⟨u, ?_, hr⟩
      rw [hu]
      congr 1
      ext z
      exact hφt z }⟩

/-- Top version + bridge (producer 2 output as explicit hypothesis `hP2`) gives the original
conclusion of `exists_primitive_meridian_of_compressible_seam`. -/
theorem exists_primitive_meridian_of_compressible_seam_via_top_CPQ
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices)
    (j : ℕ) (hj : L.first ≤ j) (C : ConnectedComponents (slices j).stage.Carrier)
    (s : Fin (L.decomposition j C).boundary.count) (x : Torus)
    (hcomp : ¬ Function.Injective (FundamentalGroup.map
      ((L.decomposition j C).reconstructionAtlas.torusInPrime (L.decomposition j C).reconstruction s) x))
    (hperi : ∀ (i : Fin L.cores.count) (q : Fin (L.truncation j i).count) (y : Torus),
      Function.Injective (FundamentalGroup.map ((L.truncation j i).boundary.boundaryMap q) y))
    (hloop : ∀ (E : PersistentCuspExterior L.cores), E = persistentExterior_CPE2 L j hj →
      ∀ (i : Fin L.cores.count) (q : Fin (E.truncation i).count) (y : Torus)
        (φ : C(Torus, ↥(E.region E.start))),
        (∀ z, (φ z : (postStage F.observation E.start).Carrier) =
          portLoopMap_CPH E i q E.start le_rfl z) →
        ¬ Function.Injective (FundamentalGroup.map φ y) →
        ∃ γ : freeLoop Torus, Topology.IsEmbedding γ ∧ ¬ γ.Nullhomotopic ∧
          loopDegreeClass γ 1 ∈ (FundamentalGroup.map φ (γ 0)).ker)
    (hprim : ∀ γ : freeLoop Torus, Topology.IsEmbedding γ → ¬ γ.Nullhomotopic →
      ∃ e : FundamentalGroup Torus (γ 0) ≃* Multiplicative ℤ × Multiplicative ℤ,
        e (loopDegreeClass γ 1) = (Multiplicative.ofAdd 1, 1))
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
    -- producer 2 output (Meeks-Yau / P2): regular exterior spanning disk for every filled curve
    (hP2 : ∀ (M : PrescribedCuspMeridianTop_CPQ L.cores) (t : ℝ) (ht : M.exterior.start ≤ t),
      (∃ u : C(closedDisk, (postStage F.observation t).Carrier),
        diskTrace u = M.transported t ht ∧ Set.range u ⊆ M.exterior.region t) →
      ∃ u : C(closedDisk, (postStage F.observation t).Carrier),
        isExteriorSpanningDisk (M.exterior.region t) (M.transported t ht) u) :
    Nonempty (PrescribedCuspMeridian L.cores) := by
  obtain ⟨M⟩ := exists_primitive_meridian_top_CPQ K hK δ hadm hdec L j hj C s x hcomp hperi hloop
    hprim hshort hpersist
  exact ⟨M.toPrescribedCuspMeridian (hP2 M)⟩

end GC.LongTime.CuspP1
