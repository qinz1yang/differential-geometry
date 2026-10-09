import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.PortAdapterGlue

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold GC.Seifert
open DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {K : ℕ} {slices : ℕ → RegularSlice F.observation}

/-- A `PersistentCuspExterior` from the `j`-th truncation of a late cut family: the truncation
and start are frozen at `j` and `(slices j).time`.  Only `accuracy_antitone` of the cores is
needed: the advertised ball radius `(accuracy t)⁻¹` grows with `t`.  No extra `LateCutFamily`
field is required. -/
def persistentExterior_CPE2 (L : LateCutFamily F K slices) (j : ℕ) (hj : L.first ≤ j) :
    PersistentCuspExterior L.cores where
  truncation i := L.truncation j i
  start := (slices j).time
  after_cores := L.time_late j hj
  in_ball := by
    intro i t ht
    refine (L.core_in_ball j hj i).trans (riemannianBallOf_mono _ _ ?_)
    have h0 : 0 < L.cores.accuracy t :=
      L.cores.accuracy_pos t ((L.time_late j hj).trans ht)
    exact inv_anti₀ h0 (L.cores.accuracy_antitone (L.time_late j hj) ((L.time_late j hj).trans ht) ht)

theorem region_start_CPE2 (L : LateCutFamily F K slices) (j : ℕ) (hj : L.first ≤ j) :
    (persistentExterior_CPE2 L j hj).region (persistentExterior_CPE2 L j hj).start =
      exteriorRegion_CPE L j hj := by
  unfold PersistentCuspExterior.region
  simp only [le_refl, dite_true]
  rfl

/-- The cusp torus of port `(i, q)` as a map into the region of the persistent exterior at its
start time. -/
def persistentPortMap_CPE2 (L : LateCutFamily F K slices) (j : ℕ) (hj : L.first ≤ j)
    (i : Fin L.cores.count) (q : Fin (L.truncation j i).count) :
    C(Torus, ↥((persistentExterior_CPE2 L j hj).region (persistentExterior_CPE2 L j hj).start)) :=
  (ContinuousMap.mk (Homeomorph.setCongr (region_start_CPE2 L j hj).symm)
    (Homeomorph.setCongr (region_start_CPE2 L j hj).symm).continuous).comp
    (extPortMap_CPE L j hj i q)

theorem not_injective_persistentPortMap_CPE2 (L : LateCutFamily F K slices) (j : ℕ)
    (hj : L.first ≤ j) (i : Fin L.cores.count) (q : Fin (L.truncation j i).count) (y : Torus)
    (h : ¬ Function.Injective (FundamentalGroup.map (extPortMap_CPE L j hj i q) y)) :
    ¬ Function.Injective (FundamentalGroup.map (persistentPortMap_CPE2 L j hj i q) y) := by
  intro hinj
  apply h
  exact GC.Topology.injective_inner_of_composite (extPortMap_CPE L j hj i q) _ y hinj

/-- Composite: under the hypotheses of `exists_compressible_exterior_port_CPE` (peripheral
injection `hperi`, and `hglue`, which `hglue_of_presentation_CPE2` supplies from a
`TorusPresentation` cut), some port of the `PersistentCuspExterior` built from slice `j`
is not `π₁`-injective into the exterior region at its start time. -/
theorem exists_persistentCuspExterior_compressible_port_CPE2
    (L : LateCutFamily F K slices) (j : ℕ) (hj : L.first ≤ j)
    (C : ConnectedComponents (slices j).stage.Carrier)
    (s : Fin (L.decomposition j C).boundary.count) (x : Torus)
    (hcomp : ¬ Function.Injective (FundamentalGroup.map
      ((L.decomposition j C).reconstructionAtlas.torusInPrime (L.decomposition j C).reconstruction s) x))
    (hperi : ∀ (i : Fin L.cores.count) (q : Fin (L.truncation j i).count) (y : Torus),
      Function.Injective (FundamentalGroup.map ((L.truncation j i).boundary.boundaryMap q) y))
    (G : TorusPresentation (NoCuts.carrier ((slices j).stage.toClosedOrientedManifold.component C)))
    (hseam : ∀ s : Fin (L.decomposition j C).boundary.count, ∃ (k : Fin G.pairing.count)
      (e : Torus ≃ₜ Torus), ∀ x, (L.decomposition j C).reconstructionAtlas.torusInPrime
        (L.decomposition j C).reconstruction s x = G.seamTorus k (e x))
    (hports_of :
      (∀ (s' : Fin (L.decomposition j C).boundary.count) (y : Torus),
        Function.Injective (FundamentalGroup.map
          (extPortMap_CPE L j hj (L.port j hj ⟨C, s'⟩).1 (L.port j hj ⟨C, s'⟩).2) y)) →
      (∀ (s' : Fin (L.decomposition j C).boundary.count) (y : Torus),
        Function.Injective (FundamentalGroup.map
          ((L.truncation j (L.port j hj ⟨C, s'⟩).1).boundary.boundaryMap
            (L.port j hj ⟨C, s'⟩).2) y)) →
      ∀ i, (G.pieceBoundaryTori i).incompressible) :
    ∃ (E : PersistentCuspExterior L.cores) (hE : E = persistentExterior_CPE2 L j hj)
      (i : Fin L.cores.count) (q : Fin (E.truncation i).count) (y : Torus),
      ∃ φ : C(Torus, ↥(E.region E.start)),
        (∀ z, (φ z : (postStage F.observation E.start).Carrier) =
          L.cores.map i E.start E.after_cores ((E.truncation i).cuspMap q (z, halfZero))) ∧
        ¬ Function.Injective (FundamentalGroup.map φ y) := by
  obtain ⟨i, q, y, h⟩ := exists_compressible_exterior_port_index_CPE L j hj C s x hcomp hperi
    (hglue_of_presentation_CPE2 L j hj C G hseam hports_of)
  refine ⟨persistentExterior_CPE2 L j hj, rfl, i, q, y, persistentPortMap_CPE2 L j hj i q, ?_,
    not_injective_persistentPortMap_CPE2 L j hj i q y h⟩
  intro z
  rfl

end GC.LongTime.CuspP1
