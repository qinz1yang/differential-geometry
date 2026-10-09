import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelSeamCut
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelCutDataBoundary

/-!
# Consumer of the generic tube cut: the tube cut of a sphere-cut-capped carrier

`SphereCutCapped.exists_rawGraphPresentation_of_tubeCut` specializes the generic tube cut
(`exists_rawGraphPresentation_of_tubeCut`) to a sphere-cut-capped carrier `X` of `W` with a fold `F`
off the caps (the G1 shape): the ports of `W` are the ports `E` of the cut data (`boundary_eq_image`),
the ports of the capped carrier are its retained ports renumbered along `X.hn`
(`SphereCutCapped.retainedPorts`), the set off the target of `F` is the seam sphere, and the caps lie
in the radius `1 - ν` tubes read through `Ψ⁻¹`. Used by G5 SEP (two drilled components) and G6
NONSEP (one drilled component).
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

namespace SphereCutCapped

variable {W : CompactCarrier.{u}} {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
  (X : SphereCutCapped W S E)

/-- The retained ports of the capped carrier, numbered as the ports of `W`. -/
def retainedPorts : BoundaryTori X.Q n where
  collar i := X.capping.retained.collar (Fin.cast X.hn.symm i)
  source_eq i := X.capping.retained.source_eq _
  boundary_zero i t := X.capping.retained.boundary_zero _ t
  disjoint i j hij := X.capping.retained.disjoint fun h =>
    hij (Fin.ext (by have h' := congrArg Fin.val h; exact h'))

theorem retainedPorts_collar (i : Fin n) :
    (X.retainedPorts).collar i = X.capping.retained.collar (Fin.cast X.hn.symm i) :=
  rfl

theorem retainedPorts_image : X.retainedPorts.image = X.capping.retained.image := by
  ext x
  constructor
  · rintro ⟨_, ⟨i, rfl⟩, hx⟩
    exact mem_iUnion.mpr ⟨Fin.cast X.hn.symm i, hx⟩
  · rintro ⟨_, ⟨i, rfl⟩, hx⟩
    refine mem_iUnion.mpr ⟨Fin.cast X.hn i, ?_⟩
    have hi : Fin.cast X.hn.symm (Fin.cast X.hn i) = i := Fin.ext rfl
    change x ∈ range fun t => X.capping.retained.collar (Fin.cast X.hn.symm (Fin.cast X.hn i))
      (t, halfZero)
    rw [hi]
    exact hx

theorem boundary_eq_retainedPorts_image :
    X.Q.model.boundary X.Q.Carrier = X.retainedPorts.image := by
  rw [retainedPorts_image]
  exact X.capping.boundary_exhausted

/-- A fold off the caps carries the renumbered retained ports onto the ports of `W`. -/
theorem fold_retainedPorts (F : PartialDiffeomorph X.Q.model W.model X.Q.Carrier W.Carrier ∞)
    (hF : ∀ y, X.capping.core y ∈ F.source → F (X.capping.core y) = X.fold y) (i : Fin n)
    (p : Torus × EuclideanHalfSpace 1) (hp : p ∈ halfCollarSource)
    (hs : X.retainedPorts.collar i p ∈ F.source) :
    F (X.retainedPorts.collar i p) = E.collar i p := by
  have hcore : X.retainedPorts.collar i p =
      X.capping.core (X.B.tori.collar (Fin.cast X.hn.symm i) p) :=
    X.capping.retained_collar _ p hp
  rw [hcore] at hs ⊢
  rw [hF _ hs]
  exact X.tori i p hp

/-- **The tube cut of a sphere-cut-capped carrier.** -/
theorem exists_rawGraphPresentation_of_tubeCut
    (F : PartialDiffeomorph X.Q.model W.model X.Q.Carrier W.Carrier ∞)
    (hFs : F.source = (⋃ j, range (X.capping.cap j))ᶜ)
    (hFt : F.target = (range fun z => S.collar (z, 0))ᶜ)
    (hF : ∀ y, X.capping.core y ∈ F.source → F (X.capping.core y) = X.fold y)
    (Ψ : X.Q.Carrier ≃ₘ⟮X.Q.model, X.Q.model⟯ X.Q.Carrier) (K : Set X.Q.Carrier)
    (hK : IsCompact K) (hKI : K ⊆ X.Q.interior) (hΨK : ∀ x, x ∉ K → Ψ x = x) {k : ℕ}
    (φ : Fin k → PartialDiffeomorph (𝓘(ℝ, ℂ).prod (𝓡 1)) X.Q.model
      (PlaneLift.{u} × Circle) X.Q.Carrier ∞)
    (h3 : ∀ t, {p : PlaneLift.{u} × Circle | ‖p.1.down‖ ≤ 3} ⊆ (φ t).source)
    (hφI : ∀ t, (φ t).target ⊆ X.Q.interior)
    (hφd : Pairwise fun t t' =>
      Disjoint (φ t '' {p | ‖p.1.down‖ ≤ 1}) (φ t' '' {p | ‖p.1.down‖ ≤ 1}))
    {m : ℕ} (O : Fin m → Set X.Q.Carrier) (hOo : ∀ j, IsOpen (O j))
    (hOd : Pairwise (Disjoint on O)) (hOc : ∀ x, ∃ j, x ∈ O j)
    (L : Fin m → CompactCarrier.{u}) (hLk : ∀ j, (L j).kind = .withBoundary)
    (hLc : ∀ j, ConnectedSpace (L j).Carrier) (hLR : ∀ j, Nonempty (RawGraphPresentation (L j)))
    (η : ∀ j, (L j).Carrier → X.Q.Carrier)
    (hη : ∀ j, IsSmoothEmbedding (L j).model X.Q.model ∞ (η j))
    (hηb : ∀ j x, Bijective (mfderiv (L j).model X.Q.model (η j) x))
    (hηr : ∀ j, range (η j) = O j \ ⋃ t, φ t '' {p | ‖p.1.down‖ < 1})
    (o : Fin k → Fin m)
    (Γ : ∀ t, PartialDiffeomorph halfCollarModel (L (o t)).model
      (Torus × EuclideanHalfSpace 1) (L (o t)).Carrier ∞)
    (hΓs : ∀ t, (Γ t).source = halfCollarSource)
    (hΓ : ∀ t p, p ∈ halfCollarSource →
      η (o t) (Γ t p) = φ t (ULift.up ((1 + p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2))
    (hLb : ∀ j, η j '' (L j).model.boundary (L j).Carrier ⊆ X.Q.model.boundary X.Q.Carrier ∪
      ⋃ t, range (fun τ : Torus => φ t (ULift.up (τ.1 : ℂ), τ.2)))
    (P : CompactCarrier.{u}) (hPR : Nonempty (RawGraphPresentation P)) (Pc : PieceFold W)
    (e : P.Carrier ≃ₘ⟮P.model, 𝓡∂ 3⟯ Pc.Piece) {ν : ℝ} (hν : 0 < ν)
    (lift : Fin k → PartialDiffeomorph halfCollarModel (𝓡∂ 3)
      (Torus × EuclideanHalfSpace 1) Pc.Piece ∞)
    (hls : ∀ t, (lift t).source = halfCollarSource)
    (hl : ∀ t p, p ∈ halfCollarSource → Pc.map (lift t p) =
      F (Ψ.symm (φ t (ULift.up ((1 - ν * p.2.val 0 / 2) • (p.1.1 : ℂ)), p.1.2))))
    (hPb : (𝓡∂ 3).boundary Pc.Piece ⊆ ⋃ t, range fun τ => lift t (τ, halfZero))
    (hPi : Injective Pc.map)
    (hPr : range Pc.map = F '' ((Ψ.symm '' ⋃ t, φ t '' {p | ‖p.1.down‖ ≤ 1}) ∩ F.source) ∪
      range (fun z => S.collar (z, 0)))
    (hcap : ∀ j, ∃ t, range (X.capping.cap j) ⊆ Ψ.symm '' (φ t '' {p | ‖p.1.down‖ < 1 - ν})) :
    Nonempty (RawGraphPresentation W) := by
  have hsrc : ∀ x, Ψ x ∉ ⋃ t, φ t '' {p | ‖p.1.down‖ < 1 - ν} → x ∈ F.source := by
    intro x hx
    rw [hFs]
    intro hcx
    obtain ⟨j, hj⟩ := mem_iUnion.mp hcx
    obtain ⟨t, ht⟩ := hcap j
    obtain ⟨y, hy, hyx⟩ := ht hj
    refine hx (mem_iUnion.mpr ⟨t, ?_⟩)
    rw [← hyx, Ψ.apply_symm_apply]
    exact hy
  exact GC.GraphManifold.Assembly.exists_rawGraphPresentation_of_tubeCut E X.boundary_eq_image
    X.retainedPorts X.boundary_eq_retainedPorts_image F (X.fold_retainedPorts F hF) _ hFt Ψ K hK
    hKI hΨK φ h3 hφI hφd O hOo hOd hOc L hLk hLc hLR η hη hηb hηr o Γ hΓs hΓ hLb P hPR Pc e hν
    lift hls hl hPb hPi hPr hsrc

end SphereCutCapped

end GC.GraphManifold.Assembly
