import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.PresentationOfCutPorts

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.Topology GC.Seifert Set
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {K : ℕ} {slices : ℕ → RegularSlice F.observation}

/-- `hglue` of `exists_compressible_exterior_port_CPE`, with no extra hypotheses. -/
theorem hglue_CPG (L : LateCutFamily F K slices) (j : ℕ) (hj : L.first ≤ j)
    (C : ConnectedComponents (slices j).stage.Carrier) :
    (∀ (s' : Fin (L.decomposition j C).boundary.count) (y : Torus),
        Function.Injective (FundamentalGroup.map
          (extPortMap_CPE L j hj (L.port j hj ⟨C, s'⟩).1 (L.port j hj ⟨C, s'⟩).2) y)) →
      (∀ (s' : Fin (L.decomposition j C).boundary.count) (y : Torus),
        Function.Injective (FundamentalGroup.map
          ((L.truncation j (L.port j hj ⟨C, s'⟩).1).boundary.boundaryMap
            (L.port j hj ⟨C, s'⟩).2) y)) →
      ∀ (s' : Fin (L.decomposition j C).boundary.count) (y : Torus),
        Function.Injective (FundamentalGroup.map
          ((L.decomposition j C).reconstructionAtlas.torusInPrime
            (L.decomposition j C).reconstruction s') y) :=
  hglue_of_presentation_CPE2 L j hj C (dp_CPG (L.decomposition j C)).presentation
    (fun s => ⟨(dp_CPG (L.decomposition j C)).seamIndex s, Homeomorph.refl _, fun x =>
      ((dp_CPG (L.decomposition j C)).seam_zero_eq s x).symm⟩)
    (hports_of_CPG L j hj C)

theorem exists_compressible_exterior_port_CPG
    (L : LateCutFamily F K slices) (j : ℕ) (hj : L.first ≤ j)
    (C : ConnectedComponents (slices j).stage.Carrier)
    (s : Fin (L.decomposition j C).boundary.count) (x : Torus)
    (hcomp : ¬ Function.Injective (FundamentalGroup.map
      ((L.decomposition j C).reconstructionAtlas.torusInPrime (L.decomposition j C).reconstruction s) x))
    (hperi : ∀ (i : Fin L.cores.count) (q : Fin (L.truncation j i).count) (y : Torus),
      Function.Injective (FundamentalGroup.map ((L.truncation j i).boundary.boundaryMap q) y)) :
    ∃ (s' : Fin (L.decomposition j C).boundary.count) (y : Torus),
      ¬ Function.Injective (FundamentalGroup.map
        (extPortMap_CPE L j hj (L.port j hj ⟨C, s'⟩).1 (L.port j hj ⟨C, s'⟩).2) y) :=
  exists_compressible_exterior_port_CPE L j hj C s x hcomp hperi (hglue_CPG L j hj C)

end GC.LongTime.CuspP1
