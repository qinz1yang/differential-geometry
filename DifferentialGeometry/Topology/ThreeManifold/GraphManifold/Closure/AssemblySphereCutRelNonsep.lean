import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelSeamCutApplications

/-!
# Chapter-14 assembly, relative COMPARE G6′ NONSEP: the non-separating assembly

Lane ASM-L2e3, group G6′ (frozen statement: ASM-L2e `Targets.lean`, theorem G6, plus the
disjointness of the two closed unit tubes, which the placement adapter `exists_nonseparatingPlacement`
supplies). With one capped component, the double drill of that component (a connected Raw carrier
embedded off both open unit tubes, with its two radial ports), the placed plug piece of G4 and the
fold of G1 give a raw presentation of `W`: the generic tube cut
(`SphereCutCapped.exists_rawGraphPresentation_of_tubeCut`) with `k = 2` tubes, `m = 1` drilled
carrier over the trivial partition, both tubes owned by it (a two-piece `RegularCutData`).

Deviations from the frozen G6 text (decided by main, 2026-10-04): the added hypothesis `hφd`
(disjoint closed unit tubes; without it the two tubes may share their open unit tube, a degenerate
configuration the assembly A3 never produces); the unused hypotheses `[ConnectedSpace W.Carrier]`
and `hν1 : ν ≤ 1` are dropped. The frozen G6 text itself is not needed for A3 (superseded by G6′).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- **G6′.** The non-separating assembly: the double drill of the one capped component (a connected
Raw carrier embedded off both open unit tubes, with its two radial ports), the placed plug piece of
G4 and the fold of G1 give a raw presentation of `W` (a two-piece `RegularCutData`), once the two
closed unit tubes are disjoint. -/
theorem exists_rawGraphPresentation_of_nonseparatingPlacement_of_disjoint (W : CompactCarrier.{u})
    {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
    (X : SphereCutCapped W S E)
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
    (hφd : Disjoint (φ 0 '' {p | ‖p.1.down‖ ≤ 1}) (φ 1 '' {p | ‖p.1.down‖ ≤ 1}))
    (L : CompactCarrier.{u}) (hLk : L.kind = .withBoundary) (hLc : ConnectedSpace L.Carrier)
    (hLR : Nonempty (RawGraphPresentation L)) (η : L.Carrier → X.Q.Carrier)
    (hη : IsSmoothEmbedding L.model X.Q.model ∞ η)
    (hηb : ∀ x, Bijective (mfderiv L.model X.Q.model η x))
    (hηr : range η = (⋃ t, φ t '' {p | ‖p.1.down‖ < 1})ᶜ)
    (Γ : Fin 2 → PartialDiffeomorph halfCollarModel L.model
      (Torus × EuclideanHalfSpace 1) L.Carrier ∞)
    (hΓs : ∀ t, (Γ t).source = halfCollarSource)
    (hΓ : ∀ t p, p ∈ halfCollarSource →
      η (Γ t p) = φ t (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2))
    (hLb : η '' L.model.boundary L.Carrier = X.Q.model.boundary X.Q.Carrier ∪
      ⋃ t, range (fun τ : Torus => φ t (ULift.up (τ.1 : ℂ), τ.2)))
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
  have hφd' : Pairwise fun t t' : Fin 2 =>
      Disjoint (φ t '' {p | ‖p.1.down‖ ≤ 1}) (φ t' '' {p | ‖p.1.down‖ ≤ 1}) := by
    intro t t' htt
    fin_cases t <;> fin_cases t'
    · exact (htt rfl).elim
    · exact hφd
    · exact hφd.symm
    · exact (htt rfl).elim
  have hOd : Pairwise (Disjoint on fun _ : Fin 1 => (univ : Set X.Q.Carrier)) :=
    fun t t' htt => (htt (Subsingleton.elim t t')).elim
  have hcap' : ∀ j, ∃ t, range (X.capping.cap j) ⊆
      Ψ.symm '' (φ t '' {p | ‖p.1.down‖ < 1 - ν}) := by
    intro j
    refine ⟨Fin.cast X.h2 j, ?_⟩
    have h := hcap (Fin.cast X.h2 j)
    rwa [show Fin.cast X.h2.symm (Fin.cast X.h2 j) = j from Fin.ext rfl] at h
  exact X.exists_rawGraphPresentation_of_tubeCut F hFs hFt hF Ψ K hK hKI hΨK φ h3 hφI hφd'
    (fun _ : Fin 1 => (univ : Set X.Q.Carrier)) (fun _ => isOpen_univ) hOd
    (fun _ => ⟨0, mem_univ _⟩) (fun _ => L) (fun _ => hLk) (fun _ => hLc) (fun _ => hLR)
    (fun _ => η) (fun _ => hη) (fun _ => hηb) (fun _ => by rw [hηr, compl_eq_univ_sdiff])
    (fun _ => 0) Γ hΓs hΓ (fun _ => hLb.subset) P hPR Pc e hν lift hls hl hPb.subset hPi hPr hcap'

end GC.GraphManifold.Assembly
