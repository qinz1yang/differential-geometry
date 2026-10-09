import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.Producer1AssemblyBasic
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspExterior

/-!
# CP1-D3: exterior-region kernel persistence (reduction)

* `portLoopMap_mem_region_CPD3`: the cusp torus of a truncation lies in the exterior region.
* `hpersist_of_locallyConstant_CPD3`: kernel of `Torus -> E.region t` locally constant in `t`
  implies the `hpersist` conclusion of CP1-H.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {K : ℕ} {slices : ℕ → RegularSlice F.observation}

theorem portLoopMap_mem_region_CPD3 {L : LateCutFamily F K slices}
    (E : PersistentCuspExterior L.cores) (i : Fin L.cores.count)
    (q : Fin (E.truncation i).count) (t : ℝ) (ht : E.start ≤ t) (z : Torus) :
    (portLoopMap_CPH E i q t ht z : (postStage F.observation t).Carrier) ∈ E.region t := by
  have hs : E.start ≤ t := ht
  have hcore := E.after_cores.trans ht
  unfold PersistentCuspExterior.region
  rw [dif_pos hs]
  intro hmem
  rw [mem_iUnion] at hmem
  obtain ⟨j, w, ⟨c, hc, rfl⟩, hw⟩ := hmem
  -- both points in the domain
  have hdomc : ∀ y, (E.truncation j).inclusion y ∈ (L.cores.domain j t : Set (L.cores.model j).Carrier) :=
    fun y => L.cores.advertised_ball j t hcore (E.in_ball j t ht ⟨y, rfl⟩)
  have hdomq : (E.truncation i).cuspMap q (z, halfZero) ∈
      (L.cores.domain i t : Set (L.cores.model i).Carrier) := by
    rw [(E.truncation i).cusp_zero q z]
    exact L.cores.advertised_ball i t hcore (E.in_ball i t ht ⟨_, rfl⟩)
  by_cases hji : j = i
  · subst hji
    have hinj := (L.cores.embedding j t hcore).isEmbedding.injective
    have h1 : (E.truncation j).inclusion c = (E.truncation j).cuspMap q (z, halfZero) := by
      have := @hinj ⟨_, hdomc c⟩ ⟨_, hdomq⟩ (by simpa [portLoopMap_apply_CPH] using hw)
      exact congrArg Subtype.val this
    rw [(E.truncation j).cusp_zero q z] at h1
    have h2 := ((E.truncation j).embedding.isEmbedding.injective) h1
    have hb := (E.truncation j).boundary.boundary_zero q z
    have hb' : (E.truncation j).core.model.IsBoundaryPoint c := by
      rw [h2]; exact hb
    have hint : (E.truncation j).core.model.IsInteriorPoint c := hc
    exact ((ModelWithCorners.isBoundaryPoint_iff_not_isInteriorPoint _).mp hb') hint
  · have hdis := L.cores.disjoint t hcore hji
    refine Set.disjoint_left.mp hdis ⟨_, hdomc c, hw⟩ ?_
    exact ⟨_, hdomq, rfl⟩

/-- The cusp torus map into the exterior region. -/
def portLoopRegionMap_CPD3 {L : LateCutFamily F K slices} (E : PersistentCuspExterior L.cores)
    (i : Fin L.cores.count) (q : Fin (E.truncation i).count) (t : ℝ) (ht : E.start ≤ t) :
    C(Torus, ↥(E.region t)) :=
  ⟨fun z => ⟨portLoopMap_CPH E i q t ht z, portLoopMap_mem_region_CPD3 E i q t ht z⟩,
    (portLoopMap_CPH E i q t ht).continuous.subtype_mk _⟩

theorem portLoopRegionMap_apply_CPD3 {L : LateCutFamily F K slices}
    (E : PersistentCuspExterior L.cores) (i : Fin L.cores.count)
    (q : Fin (E.truncation i).count) (t : ℝ) (ht : E.start ≤ t) (z : Torus) :
    ((portLoopRegionMap_CPD3 E i q t ht z : E.region t) : (postStage F.observation t).Carrier) =
      portLoopMap_CPH E i q t ht z := rfl

/-- Local-to-global: if the kernel of `pi_1(Torus, x) -> pi_1(E.region t)` is locally constant in
`t ∈ [E.start, ∞)`, then compressibility persists.  Conclusion has the exact shape of the CP1-H
`hpersist` input. -/
theorem hpersist_of_locallyConstant_CPD3 {L : LateCutFamily F K slices}
    (hlocal : ∀ (E : PersistentCuspExterior L.cores) (i : Fin L.cores.count)
      (q : Fin (E.truncation i).count) (x : Torus),
      IsLocallyConstant (fun τ : Ici E.start =>
        (FundamentalGroup.map (portLoopRegionMap_CPD3 E i q τ.1 τ.2) x).ker))
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
  have hpre : PreconnectedSpace (Ici E'.start) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Ici
  have := (hlocal E' i' q' (loop 0)).apply_eq_of_preconnectedSpace
    ⟨E'.start, Set.mem_Ici.mpr le_rfl⟩ ⟨t, ht⟩
  refine ⟨portLoopRegionMap_CPD3 E' i' q' t ht, fun z => rfl, ?_⟩
  rw [← this]
  exact hk

end GC.LongTime.CuspP1
