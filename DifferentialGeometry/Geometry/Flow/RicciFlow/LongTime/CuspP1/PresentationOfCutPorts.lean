import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.PresentationOfCutMain

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.Topology GC.Seifert Set
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {K : ℕ} {slices : ℕ → RegularSlice F.observation}

theorem hports_of_CPG (L : LateCutFamily F K slices) (j : ℕ) (hj : L.first ≤ j)
    (C : ConnectedComponents (slices j).stage.Carrier) :
    (∀ (s' : Fin (L.decomposition j C).boundary.count) (y : Torus),
        Function.Injective (FundamentalGroup.map
          (extPortMap_CPE L j hj (L.port j hj ⟨C, s'⟩).1 (L.port j hj ⟨C, s'⟩).2) y)) →
      (∀ (s' : Fin (L.decomposition j C).boundary.count) (y : Torus),
        Function.Injective (FundamentalGroup.map
          ((L.truncation j (L.port j hj ⟨C, s'⟩).1).boundary.boundaryMap
            (L.port j hj ⟨C, s'⟩).2) y)) →
      ∀ i, ((dp_CPG (L.decomposition j C)).presentation.pieceBoundaryTori i).incompressible := by
  intro hE hC i m x
  let G := (dp_CPG (L.decomposition j C)).presentation
  obtain ⟨j', ν, hν⟩ := side_data_CPG L j C ((Fintype.equivFin (G.OwnedSide i)).symm m).val
  obtain ⟨e, he⟩ := exists_seam_reparam_CPG L j hj C j' (slicePhi_CPG (slices j))
    (slicePhi_spec_CPG (slices j))
  let port_m : C(Torus, (componentCarrier G.cutCarrier G.components i).Carrier) :=
    (G.pieceBoundaryTori i).boundaryMap m
  -- value of psi on the port
  have hpsi : ∀ t, psi_CPG L j C (port_m t).val =
      portPoint_CPE L j hj (L.port j hj ⟨C, j'⟩).1 (L.port j hj ⟨C, j'⟩).2 (e (ν t)) := by
    intro t
    have h1 : (port_m t).val = G.sideCollar ((Fintype.equivFin (G.OwnedSide i)).symm m).val (t, halfZero) :=
      G.pieceBoundaryTori_torusMap i m t
    have h2 := hν t
    have h3 : psi_CPG L j C (port_m t).val =
        (slicePhi_CPG (slices j)).symm
          ((G.cutMap (G.sideCollar ((Fintype.equivFin (G.OwnedSide i)).symm m).val (t, halfZero))).val) := by
      rw [← h1]; rfl
    rw [h3, h2, he (ν t)]
    simp
  have hmem : ∀ t, psi_CPG L j C (port_m t).val ∈ Set.range (coreMap_CPG L j hj
      (L.port j hj ⟨C, j'⟩).1) := fun t =>
    ⟨_, by rw [hpsi t]; exact coreMap_boundary_CPG L j hj _ _ _⟩
  let ε : Torus ≃ₜ Torus := ν.trans e
  rcases piece_dichotomy_CPG L j hj C i with ⟨i0, hi0⟩ | hext
  · have hii : (L.port j hj ⟨C, j'⟩).1 = i0 := by
      by_contra hne
      obtain ⟨c, hc⟩ := hmem 1
      have hc0 := hi0 (port_m 1).val (port_m 1).2
      exact Set.disjoint_left.mp (range_coreMap_disjoint_CPG L j hj hne) ⟨c, hc⟩ hc0
    subst hii
    obtain ⟨ψ, hψ⟩ := exists_lift_CPG (coreMap_CPG L j hj (L.port j hj ⟨C, j'⟩).1)
      (coreMap_isEmbedding_CPG L j hj _)
      ⟨fun z : (componentCarrier G.cutCarrier G.components i).Carrier => psi_CPG L j C z.val,
        (psi_CPG L j C).continuous.comp continuous_subtype_val⟩
      (fun z => hi0 z.val z.2)
    have hcomp : ψ.comp port_m = ((L.truncation j (L.port j hj ⟨C, j'⟩).1).boundary.boundaryMap
        (L.port j hj ⟨C, j'⟩).2).comp (ε : C(Torus, Torus)) := by
      ext t
      refine (coreMap_isEmbedding_CPG L j hj _).injective ?_
      exact (hψ (port_m t)).trans ((hpsi t).trans (coreMap_boundary_CPG L j hj _ _ _).symm)
    apply injective_inner_of_composite port_m ψ x
    have key : ∀ y : Torus, Function.Injective (FundamentalGroup.map (ψ.comp port_m) y) := by
      rw [hcomp]
      intro y
      rw [fundamentalGroup_map_comp, MonoidHom.coe_comp]
      exact (hC j' _).comp (fundamentalGroup_map_homeomorph_injective ε y)
    exact key x
  · let ψ : C((componentCarrier G.cutCarrier G.components i).Carrier, ↥(exteriorRegion_CPE L j hj)) :=
      ⟨fun z => ⟨psi_CPG L j C z.val, hext z.val z.2⟩,
        ((psi_CPG L j C).continuous.comp continuous_subtype_val).subtype_mk _⟩
    have hcomp : ψ.comp port_m = (extPortMap_CPE L j hj (L.port j hj ⟨C, j'⟩).1
        (L.port j hj ⟨C, j'⟩).2).comp (ε : C(Torus, Torus)) := by
      ext t
      exact hpsi t
    apply injective_inner_of_composite port_m ψ x
    have key : ∀ y : Torus, Function.Injective (FundamentalGroup.map (ψ.comp port_m) y) := by
      rw [hcomp]
      intro y
      rw [fundamentalGroup_map_comp, MonoidHom.coe_comp]
      exact (hE j' _).comp (fundamentalGroup_map_homeomorph_injective ε y)
    exact key x

end GC.LongTime.CuspP1
