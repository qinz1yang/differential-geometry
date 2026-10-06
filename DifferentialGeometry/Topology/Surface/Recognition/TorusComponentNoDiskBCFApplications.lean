import DifferentialGeometry.Topology.Surface.Recognition.TorusComponentNoDiskBCF

/-!
# Consumer of the torus no-disk kernel (lane S-BCF03b)

The torus `Bd = S¹ × S¹` (one component `Y = Bd`, `R_c = Bd`, no horizontal disk, `X₂ = ∅`): the
partition of `Y` built by the family transport (one piece `Y`, projection `fst`) and the torus
homeomorphism `Y ≃ₜ S¹ × S¹` feed `component_inter_source_eq_empty_of_torus_BCF`; the count `0`
of FC40 is `diskCount_eq_zero_of_torus` on that partition.
-/

set_option autoImplicit false

open Set Function Topology

noncomputable section

namespace DifferentialGeometry.Topology.Surface

open DifferentialGeometry.Topology

theorem torus_noDisk_example_BCF (x : Circle × Circle) :
    ∃ (Pt : EmbeddedFacePartition_BCF ↥(connectedComponentIn (univ : Set (Circle × Circle)) x)),
      Pt.diskCount = 0 ∧ connectedComponentIn (univ : Set (Circle × Circle)) x ∩
        (∅ : Set (Circle × Circle)) = ∅ := by
  have hcc : connectedComponentIn (univ : Set (Circle × Circle)) x = univ :=
    isPreconnected_univ.connectedComponentIn (mem_univ x)
  set Y : Set (Circle × Circle) := connectedComponentIn (univ : Set (Circle × Circle)) x with hY
  let ψ : ↥Y ≃ₜ Circle × Circle := (Homeomorph.setCongr hcc).trans (Homeomorph.Set.univ _)
  obtain ⟨Pt, eI, eJ, -, -, -, hpE, -⟩ := exists_embeddedFacePartition_of_family_BCF (Y := Y)
    (I := Empty) (J := Unit) (fun i => i.elim) (fun _ => Y) (fun i => i.elim) (fun i => i.elim)
    (fun _ => subset_rfl) (fun i => i.elim) (fun _ => by rw [hcc]; exact isClosed_univ)
    (fun _ => ⟨x, mem_connectedComponentIn (mem_univ x)⟩)
    (fun y hy => Or.inr (mem_iUnion.mpr ⟨(), hy⟩)) (fun i => i.elim)
    (fun i j hij => (hij (Subsingleton.elim i j)).elim) (fun i => i.elim)
    (fun _ => Or.inl (by simp)) (fun i => i.elim) (fun _ h => by simp at h)
    (fun _ _ => ⟨fun z => (ψ z).1, continuous_fst.comp ψ.continuous,
      isOpenMap_fst.comp ψ.isOpenMap⟩)
  have hpieces : Subtype.val '' (⋃ j, Pt.piece j) = Y ∩ (univ : Set (Circle × Circle)) := by
    have hall : (⋃ j, Pt.piece j) = univ := by
      refine eq_univ_of_forall fun z => mem_iUnion.mpr ⟨eJ (), ?_⟩
      rw [hpE ()]
      exact z.2
    rw [hall, image_univ, Subtype.range_coe, inter_univ]
  have hdk : Pt.diskCount = 0 := Pt.diskCount_eq_zero_of_torus ψ
  refine ⟨Pt, hdk, ?_⟩
  exact component_inter_source_eq_empty_of_torus_BCF (fib₁ := fun y : Circle =>
    (∅ : Set (Circle × Circle)) ∩ Prod.fst ⁻¹' {y}) (f₂ := Prod.fst) (T := fun _ => (0 : ℝ))
    (c := 0) (X₂ := ∅) (Bd := univ) (Rc := univ) (fun _ => rfl) (fun p hp => hp.2.elim)
    (fun p hp => hp.2.elim) (fun p hp => hp.2.elim) ψ Pt hpieces

end DifferentialGeometry.Topology.Surface
