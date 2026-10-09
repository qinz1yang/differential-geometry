import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortMeridianKernel
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortMeridianDeep
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryExteriorMain
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.MeridianTopBasic
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.LoopTheoremCore
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.MeridianTopAssemblyV4

/-!
# CP1-A3 (G3): `hshort_CPA3`, the `hshort` input of `MeridianTopAssemblyV4`
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Seifert GC.Topology
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

theorem hshort_CPA3 {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {K : ℕ} {slices : ℕ → RegularSlice F.observation} (L : LateCutFamily F K slices)
    (j : ℕ) (hj : L.first ≤ j) :
    ∀ (E : PersistentCuspExterior L.cores), E = persistentExterior_CPE2 L j hj →
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
            loopDegreeClass loop 1 ∈ (FundamentalGroup.map φ' (loop 0)).ker) := by
  intro E _ i q φ hφ γ _ hprim hk
  obtain ⟨loop, hemb, hsm, hprim', ⟨β, hβ⟩, b₀, hgeo⟩ :=
    exists_meridian_deepCusp_of_class_CPA3 ((E.truncation i).cusp q) γ hprim
  have hb : 2 ≤ max 2 b₀ := le_max_left _ _
  obtain ⟨hgeo', hshort⟩ := hgeo (max 2 b₀) (le_max_right _ _)
  let E' := deepExteriorOf_CPA2 E hb
  have hEt : E.start ≤ E'.start :=
    deepExterior_start_CPA2 E (fun i q => isClosed_range_cuspMap_CPA2 (E.truncation i) q) hb
  have hφeq : φ = portLoopRegionMap_CPD3 E i q E.start le_rfl :=
    ContinuousMap.ext fun z => Subtype.ext (hφ z)
  subst hφeq
  have hk' := hmono_CPD8 E i q (γ 0) le_rfl hEt hk
  -- null-homotopy of the loop in the region of E at time E'.start
  have hnull : ((portLoopRegionMap_CPD3 E i q E'.start hEt).comp γ).Nullhomotopic := by
    apply nullhomotopic_of_loopDegreeClass_eq_one_CPQ
    have h : loopDegreeClass ((portLoopRegionMap_CPD3 E i q E'.start hEt).comp γ) 1 =
        FundamentalGroup.map (portLoopRegionMap_CPD3 E i q E'.start hEt) (γ 0)
          (loopDegreeClass γ 1) := by
      unfold loopDegreeClass
      change Path.Homotopic.Quotient.mk _ = Path.Homotopic.Quotient.mk _
      congr 1
    rw [h]
    exact hk'
  have hnull' := nullhomotopic_transfer_CPA3 E hb (le_refl E'.start) i q
    (portLoopRegionMap_CPD3 E i q E'.start hEt) (fun z => rfl)
    (portLoopRegionMap_CPD3 E' i q E'.start le_rfl) (fun z => rfl) γ hnull
  have hker := loopDegreeClass_one_mem_ker_LTP4 _ γ hnull'
  have hker' := mem_ker_of_changeBasepoint_CPA3 (portLoopRegionMap_CPD3 E' i q E'.start le_rfl)
    γ loop β hβ hker
  exact ⟨E', i, q, loop, hemb, hsm, hgeo', hprim', hshort,
    portLoopRegionMap_CPD3 E' i q E'.start le_rfl, fun z => rfl, hker'⟩

end GC.LongTime.CuspP1
