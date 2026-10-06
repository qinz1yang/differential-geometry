import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.PortSelectionRegion

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint Set
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {K : ℕ} {slices : ℕ → RegularSlice F.observation}

/-- The cusp torus of port `q` of the `i`-th truncation, viewed inside the exterior region. -/
def extPortMap_CPE (L : LateCutFamily F K slices) (j : ℕ) (hj : L.first ≤ j)
    (i : Fin L.cores.count) (q : Fin (L.truncation j i).count) :
    C(Torus, ↥(exteriorRegion_CPE L j hj)) :=
  ⟨fun x => ⟨portPoint_CPE L j hj i q x, portPoint_mem_exterior_CPE L j hj i q x⟩, by
    refine Continuous.subtype_mk ?_ _
    have hc : Continuous fun x : Torus => (L.truncation j i).cuspMap q (x, halfZero) := by
      have := ((L.truncation j i).cuspEmbedding q).contMDiff.continuous
      exact this.comp (continuous_id.prodMk continuous_const)
    have hmem : ∀ x : Torus, (L.truncation j i).cuspMap q (x, halfZero) ∈
        (L.cores.domain i (slices j).time : Set (L.cores.model i).Carrier) := by
      intro x
      rw [(L.truncation j i).cusp_zero q x]
      exact inclusion_mem_domain_CPE L j hj i _
    have hcm := (L.cores.smooth i (slices j).time (L.time_late j hj)).continuousOn
    exact hcm.comp_continuous hc hmem⟩

/-- IMS02, contrapositive part (A:18254).  Suppose some seam torus of the decomposition of the
component `C` of the `j`-th late slice fails to be `π₁`-injective.  Assume

* `hperi`: the peripheral injection of the hyperbolic truncations (cusp torus `π₁`-injects
  into the truncated core); no proof of this is in the tree (HANDOVER estimates the scale);
* `hglue`: the finite collared gluing injection (B:11132) specialised to the cut of `C` into
  truncated cores and exterior region: if every core port and every exterior port of `C` is
  `π₁`-injective into its block, then every seam torus of `C` is `π₁`-injective into `C`
  (to be discharged from CP1-C together with the seam/port identification `seam_image`).

Then some exterior port of `C` is compressible in the exterior region, i.e. its torus fails to be
`π₁`-injective into `exteriorRegion_CPE`.  (It need not be the originally failing seam.) -/
theorem exists_compressible_exterior_port_CPE
    (L : LateCutFamily F K slices) (j : ℕ) (hj : L.first ≤ j)
    (C : ConnectedComponents (slices j).stage.Carrier)
    (s : Fin (L.decomposition j C).boundary.count) (x : Torus)
    (hcomp : ¬ Function.Injective (FundamentalGroup.map
      ((L.decomposition j C).reconstructionAtlas.torusInPrime (L.decomposition j C).reconstruction s) x))
    (hperi : ∀ (i : Fin L.cores.count) (q : Fin (L.truncation j i).count) (y : Torus),
      Function.Injective (FundamentalGroup.map ((L.truncation j i).boundary.boundaryMap q) y))
    (hglue :
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
            (L.decomposition j C).reconstruction s') y)) :
    ∃ (s' : Fin (L.decomposition j C).boundary.count) (y : Torus),
      ¬ Function.Injective (FundamentalGroup.map
        (extPortMap_CPE L j hj (L.port j hj ⟨C, s'⟩).1 (L.port j hj ⟨C, s'⟩).2) y) := by
  by_contra hno
  push Not at hno
  exact hcomp (hglue (fun s' y => hno s' y) (fun s' y => hperi _ _ y) s x)

/-- Port-indexed form: some exterior port `(i, q)` of the cut family is compressible. -/
theorem exists_compressible_exterior_port_index_CPE
    (L : LateCutFamily F K slices) (j : ℕ) (hj : L.first ≤ j)
    (C : ConnectedComponents (slices j).stage.Carrier)
    (s : Fin (L.decomposition j C).boundary.count) (x : Torus)
    (hcomp : ¬ Function.Injective (FundamentalGroup.map
      ((L.decomposition j C).reconstructionAtlas.torusInPrime (L.decomposition j C).reconstruction s) x))
    (hperi : ∀ (i : Fin L.cores.count) (q : Fin (L.truncation j i).count) (y : Torus),
      Function.Injective (FundamentalGroup.map ((L.truncation j i).boundary.boundaryMap q) y))
    (hglue :
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
            (L.decomposition j C).reconstruction s') y)) :
    ∃ (i : Fin L.cores.count) (q : Fin (L.truncation j i).count) (y : Torus),
      ¬ Function.Injective (FundamentalGroup.map (extPortMap_CPE L j hj i q) y) := by
  obtain ⟨s', y, h⟩ := exists_compressible_exterior_port_CPE L j hj C s x hcomp hperi hglue
  exact ⟨_, _, y, h⟩

end GC.LongTime.CuspP1
