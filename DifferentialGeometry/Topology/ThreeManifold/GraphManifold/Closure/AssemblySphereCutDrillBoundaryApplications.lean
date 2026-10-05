import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutDrillBoundary
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FibreExcisionWithBoundary

/-!
# Consumer of the drilled ports: drilling a carrier with ports

`exists_drilledCarrier_boundaryTori`: drilling the open unit tube of a regular-fibre chart out of a
carrier with torus ports `E` (`∂C = E.image`) gives a carrier `K` with `n + 1` ports whose images
exhaust `∂K`: the old ports, transported after ONE recorded shrinking `p ↦ (p.1, δ • p.2)`, and the
new radial torus. This is the carrier-level step of the relative drilling (row DRILL), in the form
needed for the drilled `W` (with `E = G.external`, `G.external_exhausted`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- **Drilling a carrier with ports.** -/
theorem exists_drilledCarrier_boundaryTori (C : CompactCarrier.{u}) {n : ℕ}
    (E : BoundaryTori C n) (hE : C.model.boundary C.Carrier = E.image)
    (φ : PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) C.model (PlaneLift.{u} × Circle) C.Carrier ∞)
    (h3 : {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ φ.source)
    (hI : φ.target ⊆ C.interior) :
    ∃ (K : CompactCarrier.{u}) (ι : K.Carrier → C.Carrier) (EK : BoundaryTori K (n + 1))
      (δ : ℝ) (hδ : 0 < δ), δ ≤ 1 ∧
      IsSmoothEmbedding K.model C.model ∞ ι ∧
      range ι = (φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ < 1})ᶜ ∧
      K.model.boundary K.Carrier = EK.image ∧
      (∀ j p, p ∈ halfCollarSource →
        ι (EK.collar (Fin.castSucc j) p) = shrinkHalfCollar hδ (E.collar j) p) ∧
      ∀ p, p ∈ halfCollarSource →
        ι (EK.collar (Fin.last n) p) = φ (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2) := by
  obtain ⟨K, ι, Γ, O, -, hι, hrange, -, -, hΓs, hΓb, hΓ, hbK, -, hOs, hO, -⟩ :=
    CircleFibration.exists_fibreExcisionWithBoundary C φ h3
  let T := φ '' {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 2}
  have hTI : T ⊆ C.interior := by
    rintro x ⟨p, hp, rfl⟩
    exact hI (φ.map_source (h3 (by
      change ‖p.1.down‖ ≤ 2 at hp
      change ‖p.1.down‖ ≤ 3
      linarith)))
  obtain ⟨δ, hδ, hδ1, hav⟩ := exists_shrinkHalfCollars_avoiding_compact E.collar E.source_eq
    E.boundary_zero (isCompact_image_closedRadius φ h3) hTI
  let s : Fin n → PartialDiffeomorph halfCollarModel C.model
      (Torus × EuclideanHalfSpace 1) C.Carrier ∞ := fun j => shrinkHalfCollar hδ (E.collar j)
  have hss (j : Fin n) : (s j).source = halfCollarSource :=
    shrinkHalfCollar_source hδ hδ1 (E.source_eq j)
  have hsT (j : Fin n) : (s j).target ⊆ Tᶜ :=
    shrinkHalfCollar_target_subset_compl hδ hδ1 (E.source_eq j) (hav j)
  have hsO (j : Fin n) : (s j).target ⊆ O.source := by
    rw [hOs]
    intro x hx hx1
    apply hsT j hx
    obtain ⟨p, hp, rfl⟩ := hx1
    refine ⟨p, ?_, rfl⟩
    change ‖p.1.down‖ ≤ 1 at hp
    change ‖p.1.down‖ ≤ 2
    linarith
  let c : Fin n → PartialDiffeomorph halfCollarModel K.model
      (Torus × EuclideanHalfSpace 1) K.Carrier ∞ := fun j => (s j).trans O
  have hcs (j : Fin n) : (c j).source = halfCollarSource :=
    transportCollar_source O (s j) (hss j) (hsO j)
  have hcapply (j : Fin n) (p : Torus × EuclideanHalfSpace 1) (hp : p ∈ halfCollarSource) :
      ι (c j p) = s j p :=
    transportCollar_apply ι O hO (s j) (hss j) (hsO j) p hp
  have hszero (j : Fin n) (t : Torus) : s j (t, halfZero) = E.collar j (t, halfZero) := by
    change shrinkHalfCollar hδ (E.collar j) (t, halfZero) = _
    rw [shrinkHalfCollar_apply, halfSpaceScale_halfZero]
  have hczero (j : Fin n) (t : Torus) : ι (c j (t, halfZero)) = E.torusMap j t :=
    (hcapply j (t, halfZero) (zero_mem_halfCollarSource t)).trans (hszero j t)
  have hcb (j : Fin n) (t : Torus) : K.model.IsBoundaryPoint (c j (t, halfZero)) := by
    apply isBoundaryPoint_of_image_boundary hι.isEmbedding.injective hbK
    rw [hczero]
    exact E.boundary_zero j t
  have hcd : Pairwise fun i j => Disjoint (c i).target (c j).target := by
    intro i j hij
    rw [Set.disjoint_left]
    intro x hxi hxj
    have hi := shrinkHalfCollar_target_subset hδ (E.collar i)
      (transportCollar_target ι O hO (s i) hxi)
    have hj := shrinkHalfCollar_target_subset hδ (E.collar j)
      (transportCollar_target ι O hO (s j) hxj)
    exact Set.disjoint_left.mp (E.disjoint hij) hi hj
  have hΓT (x : K.Carrier) (hx : x ∈ Γ.target) : ι x ∈ T := by
    have hp : Γ.symm x ∈ halfCollarSource := hΓs ▸ Γ.map_target hx
    have hxp : Γ (Γ.symm x) = x := Γ.toPartialEquiv.right_inv hx
    have he := hΓ (Γ.symm x) hp
    rw [hxp] at he
    rw [he]
    refine ⟨_, ?_, rfl⟩
    have hn := (Γ.symm x).2.property
    change (Γ.symm x).2.val 0 < 1 at hp
    change ‖(1 + (Γ.symm x).2.val 0 / 2) • ((Γ.symm x).1.1 : ℂ)‖ ≤ 2
    rw [norm_smul, Real.norm_of_nonneg (by linarith), Circle.norm_coe, mul_one]
    linarith
  have hΓd (j : Fin n) : Disjoint (c j).target Γ.target := by
    rw [Set.disjoint_left]
    intro x hxj hxΓ
    exact hsT j (transportCollar_target ι O hO (s j) hxj) (hΓT x hxΓ)
  let EK := appendBoundaryTori c hcs hcb hcd Γ hΓs hΓb hΓd
  have hl : EK.collar (Fin.last n) = Γ := by
    simp only [EK, appendBoundaryTori, Fin.lastCases_last]
  have hcc (j : Fin n) : EK.collar (Fin.castSucc j) = c j := by
    simp only [EK, appendBoundaryTori, Fin.lastCases_castSucc]
  have hnew (t : Torus) : ι (Γ (t, halfZero)) = φ (ULift.up (t.1 : ℂ), t.2) := by
    have he := hΓ (t, halfZero) (zero_mem_halfCollarSource t)
    change ι (Γ (t, halfZero)) = φ (ULift.up ((1 + 0 / 2) • (t.1 : ℂ)), t.2) at he
    simpa using he
  have hbC : C.model.boundary C.Carrier =
      (⋃ j : Fin 0, (∅ : Set C.Carrier)) ∪ ⋃ j, range (E.torusMap j) := by
    rw [hE, iUnion_of_empty, empty_union]
    rfl
  have hbound := boundary_eq_of_embedding_relative hι.isEmbedding.injective
    (fun _ : Fin 0 => (∅ : Set C.Carrier)) (fun _ : Fin 0 => (∅ : Set K.Carrier))
    (fun j => j.elim0) E.torusMap (fun j t => c j (t, halfZero)) hczero
    (fun t : Torus => φ (ULift.up (t.1 : ℂ), t.2)) (fun t => Γ (t, halfZero)) hnew hbC hbK
  refine ⟨K, ι, EK, δ, hδ, hδ1, hι, hrange, ?_, fun j p hp => ?_, fun p hp => ?_⟩
  · rw [hbound, iUnion_of_empty, empty_union, appendBoundaryTori_image]
  · rw [hcc]
    exact hcapply j p hp
  · rw [hl]
    exact hΓ p hp

end GC.GraphManifold.Assembly
