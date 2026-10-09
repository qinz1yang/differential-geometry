import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryExteriorMono
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryExteriorLeftMain
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.SurgeryExteriorBoundary

/-!
# CP1-D8 (G5): unconditional exterior kernel monotonicity and `hpersist`

`hmono_CPD8`: for `E.start ≤ s ≤ t`, `ker (π₁ Torus → π₁ (E.region s)) ⊆ ker (π₁ Torus → π₁ (E.region t))`.
`hpersist_CPD8`: exactly the `hpersist` input of `MeridianTopAssemblyV4`, no hypotheses.
-/

set_option autoImplicit false
noncomputable section
open Set DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.LongTime
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {K : ℕ} {slices : ℕ → RegularSlice F.observation}

theorem hmono_CPD8 {L : LateCutFamily F K slices}
    (E : PersistentCuspExterior L.cores) (i : Fin L.cores.count)
    (q : Fin (E.truncation i).count) (x : Torus) {s t : ℝ} (hs : E.start ≤ s) (hst : s ≤ t) :
    (FundamentalGroup.map (portLoopRegionMap_CPD3 E i q s hs) x).ker ≤
      (FundamentalGroup.map (portLoopRegionMap_CPD3 E i q t (hs.trans hst)) x).ker :=
  hmono_of_residual_CPD8 (fun E i q x τ hτ hne => hresLeft_CPD8 E i q x τ hτ hne)
    (fun E i q x hb => hresBoundary_CPD8 E i q x hb) E i q x hs hst

theorem hpersist_CPD8 {L : LateCutFamily F K slices}
    (E' : PersistentCuspExterior L.cores) (i' : Fin L.cores.count)
    (q' : Fin (E'.truncation i').count) (loop : freeLoop Torus) :
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
        loopDegreeClass loop 1 ∈ (FundamentalGroup.map φt (loop 0)).ker := by
  intro _ _ _ _ ⟨φ', hφ', hk⟩ t ht
  have hφeq : φ' = portLoopRegionMap_CPD3 E' i' q' E'.start le_rfl :=
    ContinuousMap.ext fun z => Subtype.ext (hφ' z)
  subst hφeq
  exact ⟨portLoopRegionMap_CPD3 E' i' q' t ht, fun z => rfl,
    hmono_CPD8 E' i' q' (loop 0) le_rfl ht hk⟩

end GC.LongTime.CuspP1
