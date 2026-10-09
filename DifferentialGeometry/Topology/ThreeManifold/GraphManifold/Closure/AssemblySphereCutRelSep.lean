import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelSeamCutApplications

/-!
# Chapter-14 assembly, relative COMPARE G5 SEP: the separating assembly

Lane ASM-L2e3, group G5 (frozen statement: ASM-L2e `Targets.lean`, theorem G5). With two capped
components, the two drilled components (each a connected Raw carrier embedded off the open unit tube
of its own component, with its radial port), the placed plug piece of G4 and the fold of G1 give a
raw presentation of `W`: the generic tube cut (`SphereCutCapped.exists_rawGraphPresentation_of_tubeCut`)
with `k = m = 2`, the partition of the capped carrier into the two components of the cut spheres
(distinct: `spherePiece` is a surjection between sets of two elements) and the owner of the tube `t` the component `t`.

Deviation from the frozen text: the hypothesis `hν1 : ν ≤ 1` is dropped (unused; the frozen text is
checked verbatim in `build-logs/scratch/ASM-L2e3/CheckVerbatim.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- **G5.** The separating assembly: the two drilled capped components (each a connected Raw
carrier embedded off the open unit tube of its own component, with its radial port), the placed plug
piece of G4 and the fold of G1 give a raw presentation of `W` (a three-piece `RegularCutData`; the
ports of `W` are kept on a recorded shrinking with the same boundary image). -/
theorem exists_rawGraphPresentation_of_separatingPlacement (W : CompactCarrier.{u})
    [ConnectedSpace W.Carrier] {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
    (X : SphereCutCapped W S E) (DQ : X.Q.Components) (h2 : DQ.count = 2)
    (F : PartialDiffeomorph X.Q.model W.model X.Q.Carrier W.Carrier ∞)
    (hFs : F.source = (⋃ j, range (X.capping.cap j))ᶜ)
    (hFt : F.target = (range fun z => S.collar (z, 0))ᶜ)
    (hF : ∀ y, X.capping.core y ∈ F.source → F (X.capping.core y) = X.fold y)
    (Ψ : X.Q.Carrier ≃ₘ⟮X.Q.model, X.Q.model⟯ X.Q.Carrier) (K : Set X.Q.Carrier)
    (hK : IsCompact K) (hKI : K ⊆ X.Q.interior) (hΨK : ∀ x, x ∉ K → Ψ x = x)
    (φ : Fin 2 → PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) X.Q.model
      (PlaneLift.{u} × Circle) X.Q.Carrier ∞)
    (h3 : ∀ t, {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ (φ t).source)
    (hφI : ∀ t, (φ t).target ⊆ X.Q.interior)
    (hφo : ∀ t, (φ t).target ⊆ DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm t)))
    (L : Fin 2 → CompactCarrier.{u}) (hLk : ∀ t, (L t).kind = .withBoundary)
    (hLc : ∀ t, ConnectedSpace (L t).Carrier) (hLR : ∀ t, Nonempty (RawGraphPresentation (L t)))
    (η : ∀ t, (L t).Carrier → X.Q.Carrier)
    (hη : ∀ t, IsSmoothEmbedding (L t).model X.Q.model ∞ (η t))
    (hηb : ∀ t x, Bijective (mfderiv (L t).model X.Q.model (η t) x))
    (hηr : ∀ t, range (η t) =
      (DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm t)) : Set X.Q.Carrier) \
        (φ t '' {p | ‖p.1.down‖ < 1}))
    (Γ : ∀ t, PartialDiffeomorph halfCollarModel (L t).model
      (Torus × EuclideanHalfSpace 1) (L t).Carrier ∞)
    (hΓs : ∀ t, (Γ t).source = halfCollarSource)
    (hΓ : ∀ t p, p ∈ halfCollarSource →
      η t (Γ t p) = φ t (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2))
    (hLb : ∀ t, η t '' (L t).model.boundary (L t).Carrier =
      (X.Q.model.boundary X.Q.Carrier ∩ DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm t))) ∪
        range (fun τ : Torus => φ t (ULift.up (τ.1 : ℂ), τ.2)))
    (P : CompactCarrier.{u}) (hPR : Nonempty (RawGraphPresentation P)) (Pc : PieceFold W)
    (e : P.Carrier ≃ₘ⟮P.model, 𝓡∂ 3⟯ Pc.Piece) (ν : ℝ) (hν : 0 < ν)
    (lift : Fin 2 → PartialDiffeomorph halfCollarModel (𝓡∂ 3)
      (Torus × EuclideanHalfSpace 1) Pc.Piece ∞)
    (hls : ∀ t, (lift t).source = halfCollarSource)
    (hl : ∀ t p, p ∈ halfCollarSource → Pc.map (lift t p) =
      F (Ψ.symm (φ t (ULift.up ((1 - ν * p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2))))
    (hPb : (𝓡∂ 3).boundary Pc.Piece = ⋃ t, range fun τ => lift t (τ, halfZero))
    (hPi : Injective Pc.map)
    (hPr : range Pc.map = F '' ((Ψ.symm '' ⋃ t, φ t '' {p | ‖p.1.down‖ ≤ 1}) ∩ F.source) ∪
      range (fun z => S.collar (z, 0)))
    (hcap : ∀ t, range (X.capping.cap (Fin.cast X.h2.symm t)) ⊆
      Ψ.symm '' (φ t '' {p | ‖p.1.down‖ < 1 - ν})) :
    Nonempty (RawGraphPresentation W) := by
  have hcc : ∀ j : Fin X.B.sphereCount, Fin.cast X.h2.symm (Fin.cast X.h2 j) = j :=
    fun j => Fin.ext rfl
  let O : Fin 2 → Set X.Q.Carrier :=
    fun t => (DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm t)) : Set X.Q.Carrier)
  have hinj : Injective (X.spherePiece DQ) :=
    ((Fintype.bijective_iff_surjective_and_card (X.spherePiece DQ)).mpr
      ⟨X.spherePiece_surjective DQ, by simp [X.h2, h2]⟩).1
  have hOd : Pairwise (Disjoint on O) := by
    intro t t' htt
    refine DQ.disjoint fun h => htt ?_
    have h' := hinj h
    exact Fin.ext (by have h'' := congrArg Fin.val h'; exact h'')
  have hOc : ∀ x, ∃ t, x ∈ O t := by
    intro x
    obtain ⟨i, hi⟩ := exists_mem_componentsPiece DQ x
    obtain ⟨j, rfl⟩ := X.spherePiece_surjective DQ i
    refine ⟨Fin.cast X.h2 j, ?_⟩
    change x ∈ DQ.piece (X.spherePiece DQ (Fin.cast X.h2.symm (Fin.cast X.h2 j)))
    rw [hcc]
    exact hi
  have hsub : ∀ t {ρ : ℝ}, ρ ≤ 3 → φ t '' {p | ‖p.1.down‖ ≤ ρ} ⊆ O t := by
    rintro t ρ hρ _ ⟨p, hp, rfl⟩
    exact hφo t ((φ t).map_source (h3 t (le_trans (show ‖p.1.down‖ ≤ ρ from hp) hρ)))
  have hφd : Pairwise fun t t' =>
      Disjoint (φ t '' {p | ‖p.1.down‖ ≤ 1}) (φ t' '' {p | ‖p.1.down‖ ≤ 1}) :=
    fun t t' htt => (hOd htt).mono (hsub t (by norm_num)) (hsub t' (by norm_num))
  have hηr' : ∀ t, range (η t) = O t \ ⋃ t', φ t' '' {p | ‖p.1.down‖ < 1} := by
    intro t
    rw [hηr t]
    ext x
    constructor
    · rintro ⟨hxO, hxt⟩
      refine ⟨hxO, fun h => ?_⟩
      obtain ⟨t', hx'⟩ := mem_iUnion.mp h
      by_cases htt : t' = t
      · subst htt
        exact hxt hx'
      · obtain ⟨p, hp, rfl⟩ := hx'
        exact disjoint_left.mp (hOd htt)
          (hsub t' (show (1 : ℝ) ≤ 3 by norm_num) ⟨p, (show ‖p.1.down‖ < 1 from hp).le, rfl⟩) hxO
    · rintro ⟨hxO, hx⟩
      exact ⟨hxO, fun h => hx (mem_iUnion.mpr ⟨t, h⟩)⟩
  have hLb' : ∀ t, η t '' (L t).model.boundary (L t).Carrier ⊆
      X.Q.model.boundary X.Q.Carrier ∪
        ⋃ t', range (fun τ : Torus => φ t' (ULift.up (τ.1 : ℂ), τ.2)) := by
    intro t
    rw [hLb t]
    exact union_subset_union inter_subset_left
      (subset_iUnion (fun t' => range fun τ : Torus => φ t' (ULift.up (τ.1 : ℂ), τ.2)) t)
  have hcap' : ∀ j, ∃ t, range (X.capping.cap j) ⊆
      Ψ.symm '' (φ t '' {p | ‖p.1.down‖ < 1 - ν}) := by
    intro j
    refine ⟨Fin.cast X.h2 j, ?_⟩
    have h := hcap (Fin.cast X.h2 j)
    rwa [hcc] at h
  exact X.exists_rawGraphPresentation_of_tubeCut F hFs hFt hF Ψ K hK hKI hΨK φ h3 hφI hφd O
    (fun t => (DQ.piece _).isOpen) hOd hOc L hLk hLc hLR η hη hηb hηr' (fun t => t) Γ hΓs hΓ hLb'
    P hPR Pc e hν lift hls hl hPb.subset hPi hPr hcap'

end GC.GraphManifold.Assembly
