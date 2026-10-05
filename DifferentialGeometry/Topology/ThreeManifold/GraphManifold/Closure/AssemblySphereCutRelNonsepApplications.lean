import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelNonsep
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelPlugApplications
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblySphereCutRelAdapterNonsep

/-!
# Chapter-14 assembly, relative COMPARE A3: the non-separating sphere cut (V2 text)

Lane ASM-L2e3. `exists_rawGraphPresentation_of_sphereCut_nonseparating` is the V2 theorem of the
relative `S² × S¹` summand (FC42Dry `dry_L2_nonseparating`, text verbatim): a connected carrier `W`
cut along an interior sphere seam into a capped carrier with ONE component carrying a raw
presentation has a raw presentation. Proof (ASM-L2e plan, `Targets.lean`): the fold off the caps
(G1, `SphereCutCapped.exists_capComplementFold`), the bounded fibre plug with its solid cap charts
(G4, `exists_fibrePlugPiece`), the double drill of the component and the two placements of the shell
charts onto the plug's solid charts in two disjoint tubes (`exists_nonseparatingPlacement`), the
placed plug piece (G4 at `ν₀ = 1`), and the two-piece tube cut (G6′,
`exists_rawGraphPresentation_of_nonseparatingPlacement_of_disjoint`, fed with the disjointness of the
two tubes produced by the placement).

Deviation from the V2 text: the binder `[ConnectedSpace W.Carrier]` is not used by this proof (it is
used by the separating case A4) and is dropped (a strengthening, call-compatible); the verbatim V2
text is kept below as an `example`, proved by the theorem.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly

/-- **[A3]** V2 `exists_rawGraphPresentation_of_sphereCut_nonseparating` (FC42Dry
`dry_L2_nonseparating`, without the unused `[ConnectedSpace W.Carrier]`). -/
theorem exists_rawGraphPresentation_of_sphereCut_nonseparating (W : CompactCarrier.{u})
    {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
    (X : SphereCutCapped W S E) (DQ : X.Q.Components) (h1 : DQ.count = 1)
    (R : ∀ i, RawGraphPresentation (GC.Topology.componentCarrier X.Q DQ i)) :
    Nonempty (RawGraphPresentation W) := by
  obtain ⟨F, hFs, hFt, hF⟩ := X.exists_capComplementFold
  obtain ⟨P, v, hPR, -, -, hv, hvI, hplug⟩ := exists_fibrePlugPiece.{u}
  obtain ⟨Ψ, K, φ, L, η, Γ, c, s₀, μ, hs₀, hμ, Θ, ε, r, hK, hKI, hΨK, h3, hφI, hφd, hLk,
    hLc, hLR, hη, hηb, hηr, hΓs, hΓ, hLb, hsμ, hc, hshell, hball, hr, hΘ, hmatch⟩ :=
    exists_nonseparatingPlacement W X DQ h1 R v hv hvI
  obtain ⟨Pc, e, ν, lift, hν, -, -, hls, hl, hPb, hPi, hPr, hcap⟩ :=
    hplug X F hFs hF Ψ φ h3 hφI hφd c s₀ μ hs₀ hμ hsμ hc hshell hball Θ ε r hr hΘ hmatch
      zero_lt_one
  exact exists_rawGraphPresentation_of_nonseparatingPlacement_of_disjoint W X F hFs hFt hF Ψ K hK
    hKI hΨK φ h3 hφI hφd L hLk hLc hLR η hη hηb hηr Γ hΓs hΓ hLb P hPR Pc e ν hν lift hls hl hPb
    hPi hPr hcap

/-- The V2 text of A3 (FC42Dry `dry_L2_nonseparating`, verbatim). -/
example (W : CompactCarrier.{u}) [ConnectedSpace W.Carrier]
    {S : SphereSeam W} {n : ℕ} {E : BoundaryTori W n}
    (X : SphereCutCapped W S E) (DQ : X.Q.Components) (h1 : DQ.count = 1)
    (R : ∀ i, RawGraphPresentation (GC.Topology.componentCarrier X.Q DQ i)) :
    Nonempty (RawGraphPresentation W) :=
  exists_rawGraphPresentation_of_sphereCut_nonseparating W X DQ h1 R

end GC.GraphManifold.Assembly
