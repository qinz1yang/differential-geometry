import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.Producer1AssemblyV2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.MeridianTopAssembly
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.HoroballFinal
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.PrimitiveCurveJordan
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.MeridianTopAssemblyV4
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.LoopTheoremExterior
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ExteriorWindowMain
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ExteriorKernel

/-!
# CP1-H4: Producer 1 assembly V5

V4 (`MeridianTopAssemblyV4`) with
* `hloop` deleted (discharged by `hloop_LTP4 L j hj`, LT-P4),
* `hpersist` replaced by the two exact CP1-D7 residues `hresLeft`, `hresBoundary`
  (via `hlocal_of_residual_CPD7` and `hpersist_of_locallyConstant_CPD3`).

Remaining inputs (who discharges):
* `hshort`      : CP1-A2 (deep truncation + region transfer),
* `hresLeft`    : CP1-D8 (surgery time, left side),
* `hresBoundary`: CP1-D8 (boundary time `cores.start`),
* `hP2`         : producer 2 (corollary only).
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Seifert GC.Topology
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

theorem exists_primitive_meridian_top_CPH4
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices)
    (j : ℕ) (hj : L.first ≤ j) (C : ConnectedComponents (slices j).stage.Carrier)
    (s : Fin (L.decomposition j C).boundary.count) (x : Torus)
    (hcomp : ¬ Function.Injective (FundamentalGroup.map
      ((L.decomposition j C).reconstructionAtlas.torusInPrime (L.decomposition j C).reconstruction s) x))
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
    (hresLeft : ∀ (E : PersistentCuspExterior L.cores) (i : Fin L.cores.count)
      (q : Fin (E.truncation i).count) (x : Torus) (τ : Ici E.start),
      L.cores.start < τ.1 → ¬ NonSurgeryTime_CPD7 F.observation τ.1 →
      ∃ ε : ℝ, 0 < ε ∧ ∀ s : Ici E.start, τ.1 - ε < s.1 → s.1 < τ.1 →
        (FundamentalGroup.map (portLoopRegionMap_CPD3 E i q s.1 s.2) x).ker =
          (FundamentalGroup.map (portLoopRegionMap_CPD3 E i q τ.1 τ.2) x).ker)
    (hresBoundary : ∀ (E : PersistentCuspExterior L.cores) (i : Fin L.cores.count)
      (q : Fin (E.truncation i).count) (x : Torus) (τ : Ici E.start),
      ¬ L.cores.start < τ.1 →
      ∃ ε : ℝ, 0 < ε ∧ ∀ s : Ici E.start, |s.1 - τ.1| < ε →
        (FundamentalGroup.map (portLoopRegionMap_CPD3 E i q s.1 s.2) x).ker =
          (FundamentalGroup.map (portLoopRegionMap_CPD3 E i q τ.1 τ.2) x).ker) :
    Nonempty (PrescribedCuspMeridianTop_CPQ L.cores) := by
  obtain ⟨E, hE, i, q, y, φ, hφ, hn⟩ :=
    exists_persistentCuspExterior_compressible_port_CPE2 L j hj C s x hcomp (hperi_CPF3 L j)
      (dp_CPG (L.decomposition j C)).presentation
      (hseam_of_decompositionPresentation_CPH (dp_CPG (L.decomposition j C)))
      (hports_of_CPG L j hj C)
  have hφ' : ∀ z, (φ z : (postStage F.observation E.start).Carrier) =
      portLoopMap_CPH E i q E.start le_rfl z := fun z => hφ z
  obtain ⟨γ, hγe, hγn, hγk⟩ := hloop_LTP4 L j hj E hE i q y φ hφ' hn
  obtain ⟨E', i', q', loop, he, hsm, hgeo, hprim', hshortL, hc0⟩ :=
    hshort E hE i q φ hφ' γ hγe (exists_primitive_of_embedded_CPP2 γ hγe hγn) hγk
  have hc := hpersist_of_locallyConstant_CPD3 (hlocal_of_residual_CPD7 hresLeft hresBoundary) E' i' q' loop he hsm hgeo hprim' hc0
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
theorem exists_primitive_meridian_of_compressible_seam_via_top_CPH4
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    (K : ℕ) (hK : lateDerivativeOrder ≤ K) (δ : ℝ → ℝ) (hadm : hasAnalyticAdmissibility F δ)
    (hdec : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, ∀ t : ℝ, B < t → δ t < ε)
    {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices)
    (j : ℕ) (hj : L.first ≤ j) (C : ConnectedComponents (slices j).stage.Carrier)
    (s : Fin (L.decomposition j C).boundary.count) (x : Torus)
    (hcomp : ¬ Function.Injective (FundamentalGroup.map
      ((L.decomposition j C).reconstructionAtlas.torusInPrime (L.decomposition j C).reconstruction s) x))
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
    (hresLeft : ∀ (E : PersistentCuspExterior L.cores) (i : Fin L.cores.count)
      (q : Fin (E.truncation i).count) (x : Torus) (τ : Ici E.start),
      L.cores.start < τ.1 → ¬ NonSurgeryTime_CPD7 F.observation τ.1 →
      ∃ ε : ℝ, 0 < ε ∧ ∀ s : Ici E.start, τ.1 - ε < s.1 → s.1 < τ.1 →
        (FundamentalGroup.map (portLoopRegionMap_CPD3 E i q s.1 s.2) x).ker =
          (FundamentalGroup.map (portLoopRegionMap_CPD3 E i q τ.1 τ.2) x).ker)
    (hresBoundary : ∀ (E : PersistentCuspExterior L.cores) (i : Fin L.cores.count)
      (q : Fin (E.truncation i).count) (x : Torus) (τ : Ici E.start),
      ¬ L.cores.start < τ.1 →
      ∃ ε : ℝ, 0 < ε ∧ ∀ s : Ici E.start, |s.1 - τ.1| < ε →
        (FundamentalGroup.map (portLoopRegionMap_CPD3 E i q s.1 s.2) x).ker =
          (FundamentalGroup.map (portLoopRegionMap_CPD3 E i q τ.1 τ.2) x).ker)
    -- producer 2 output (Meeks-Yau / P2): regular exterior spanning disk for every filled curve
    (hP2 : ∀ (M : PrescribedCuspMeridianTop_CPQ L.cores) (t : ℝ) (ht : M.exterior.start ≤ t),
      (∃ u : C(closedDisk, (postStage F.observation t).Carrier),
        diskTrace u = M.transported t ht ∧ Set.range u ⊆ M.exterior.region t) →
      ∃ u : C(closedDisk, (postStage F.observation t).Carrier),
        isExteriorSpanningDisk (M.exterior.region t) (M.transported t ht) u) :
    Nonempty (PrescribedCuspMeridian L.cores) := by
  obtain ⟨M⟩ := exists_primitive_meridian_top_CPH4 K hK δ hadm hdec L j hj C s x hcomp
    hshort hresLeft hresBoundary
  exact ⟨M.toPrescribedCuspMeridian (hP2 M)⟩

end GC.LongTime.CuspP1
