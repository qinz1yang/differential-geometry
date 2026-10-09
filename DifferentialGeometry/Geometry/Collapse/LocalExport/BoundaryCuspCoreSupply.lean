import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreSpec
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedInterior

/-!
# BCG06, G4: the zero-ball clauses bound to the stored supply (lane BCG6-Kb)

Blueprint BCG06: "The `C_b` are pairwise disjoint and disjoint from all the actual zero domains of
ZSP02" — proof: "Each collar core lies inside `B_b`, and BCP03–BCP05 separate these from one
another and from the selected zero balls containing ZSP02's domains". Review 65 M4 (D65-5):
zero-ball separation FIRST for the original zero balls of the SAME family, then transported to the
actual `Z_i` (never left as an arbitrary-set kernel).

Here the kernel's indexed family `Zb` of G1 is bound to the stored supply `S : BoundarySupplyCore`
(BAUG-A G4, D61-2): the packet is `S.packet` (tolerance `cuspTolerance_BCUSP1 ≤ 1/1000`), the zero
balls are the ORIGINAL selected zero balls `B_g(z, r_z)` of the zero centres `z` of the ONE stored
family `S.family` (`zeroBall_BCG6K`), and T3B's alternative is the stored `S.geometric_cases`.

* `zeroIndex_BCG6K`, `zeroBall_BCG6K`: the zero centres of `S.family` and their original balls;
* `geometric_alternative_BCG6K`: `S.geometric_cases` in the kernel's shape (labelled product, or
  enlarged-collar separation and zero balls off the enlarged collars);
* `boundaryGeometricOutput_supply_BCG6K`: BCG06's geometric output on the supply with the actual
  zero balls, for every boundary pair `(u, v)` satisfying (BI), (BFM), (BD);
* transport to actual zero domains: `cuspCore_disjoint_of_subset_zeroBall_BCG6K` (kernel) and
  `cuspCore_disjoint_of_subset_supplyZeroBall_BCG6K` (any family of sets each inside the original
  selected zero ball of a zero centre of `S.family` — the shape of the chain's zero cores, field
  `core_subset_ball` of the boundary initial-core spec — is disjoint from every core).

No new structure, no named hypothesis.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Analysis DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

namespace BoundaryCollarPacket

variable {W : CompactCarrier.{0}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
  {A : ℝ → ℝ} {w₀ ε : ℝ}

/-- **Transport to actual zero domains (kernel)**: a set inside one of the separated zero balls
is disjoint from every core. -/
theorem cuspCore_disjoint_of_subset_zeroBall_BCG6K {P : BoundaryCollarPacket W g K A w₀ ε}
    {u v : Fin P.cusp.count → W.Carrier → ℝ} {ζ : Type*} {Zb : ζ → Set W.Carrier}
    (h : P.BoundaryCuspCoreSpec_BCG6K u v Zb) {Z : Set W.Carrier} {j : ζ} (hZ : Z ⊆ Zb j)
    (b : Fin P.cusp.count) : Disjoint (P.cuspCore_BCG6K b u v) Z :=
  (h.disjoint_original_zero_balls b j).mono_right hZ

end BoundaryCollarPacket

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundarySupplyCore

variable (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
  ζ Λz W g δn n B oM)

/-- The zero centres of the ONE stored family `S.family` (the index type of its selected zero
balls). -/
def zeroIndex_BCG6K : Type :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  letI := S.family.instMetricN
  letI := S.family.instChartedN
  letI := S.family.instMetricC
  {z : W.pieceInterior ⊤ // z ∈ S.family.zero.centres}

/-- **The original selected zero ball** `B_g(z, r_z)` of a zero centre `z` of the stored family
(original metric `g`; `S.transport_spec` identifies it with the family's `ĝ`-ball). -/
def zeroBall_BCG6K (z : S.zeroIndex_BCG6K) : Set W.Carrier :=
  letI := inducedMetricSpace S.completion.metric
  letI := S.completion.complete
  letI := S.family.instMetricN
  letI := S.family.instChartedN
  letI := S.family.instMetricC
  riemannianBallOf g z.1.val (S.family.zero.zero z.1 z.2).radius

/-- **T3B's alternative of the stored supply in the kernel's shape**: the labelled whole product,
or the enlarged collars pairwise disjoint and every original selected zero ball of `S.family` off
every enlarged collar. -/
theorem geometric_alternative_BCG6K :
    (∃ (i j : Fin S.packet.cusp.count), i ≠ j ∧
        ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) W.model (Torus × Icc (0 : ℝ) 1) W.Carrier ∞,
          (∀ p, D p ∈ S.packet.cusp.component i ↔ (p.2 : ℝ) = 0) ∧
            ∀ p, D p ∈ S.packet.cusp.component j ↔ (p.2 : ℝ) = 1) ∨
      ((∀ i j : Fin S.packet.cusp.count, i ≠ j →
        Disjoint ((S.packet.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})
          ((S.packet.cusp.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})) ∧
        ∀ (z : S.zeroIndex_BCG6K) (i : Fin S.packet.cusp.count),
          Disjoint (S.zeroBall_BCG6K z)
            ((S.packet.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})) := by
  rcases S.geometric_cases with hprod | ⟨hsep, hZ, -⟩
  · exact Or.inl hprod
  · exact Or.inr ⟨fun i j hij => (hsep i j hij).1, fun z i => hZ z.1 z.2 i⟩

/-- **BCG06 on the stored supply with the actual zero balls**: for boundary pairs `(u_b, v_b)`
with (BI), (BFM), (BD) (`ε∂ < 10⁻⁶`, `c₃ < 10⁻⁵`), the geometric output — the labelled whole
product, or the separated branch whose cores are disjoint from every original selected zero ball
of the stored family. -/
theorem boundaryGeometricOutput_supply_BCG6K
    {u v : Fin S.packet.cusp.count → W.Carrier → ℝ}
    (hu : ∀ i, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (u i))
    {εd c₃ : ℝ} (hεd : εd < 1 / 1000000) (hc₃0 : 0 ≤ c₃) (hc₃ : c₃ < 1 / 100000)
    (hBI : ∀ i x, |u i x - (S.packet.block i x).1| < εd ∧ |v i x - (S.packet.block i x).2| < εd)
    (hBFM : ∀ i, ∀ x ∈ S.packet.safeBand_BAUGA i, v i x = 1)
    (hBD : ∀ i, ∀ x ∈ S.packet.collarBand_BAUGA i, 38 ≤ S.packet.height i x →
      S.packet.height i x ≤ 42 →
      ∀ y : TangentSpace W.model x, |mvfderiv W.model (fun z => u i z - S.packet.height i z) x y| ≤
        c₃ * Real.sqrt (g.inner x y y)) :
    BoundaryCollarPacket.BoundaryGeometricOutput_BCG6K S.packet.toBoundaryCollarPacket u v
      S.zeroBall_BCG6K :=
  S.packet.toBoundaryCollarPacket.boundaryGeometricOutput_BCG6K
    (cuspTolerance_le_thousandth_BCUSP1 _ _ _) hu
    hεd hc₃0 hc₃ hBI hBFM hBD S.zeroBall_BCG6K S.geometric_alternative_BCG6K

/-- **Transport to the actual zero domains on the supply**: a family of sets `Z k`, each inside the
original selected zero ball of a zero centre `c k` of the stored family (the shape of the chain's
zero cores), is disjoint from every core of the separated branch. -/
theorem cuspCore_disjoint_of_subset_supplyZeroBall_BCG6K
    {u v : Fin S.packet.cusp.count → W.Carrier → ℝ}
    (h : S.packet.toBoundaryCollarPacket.BoundaryCuspCoreSpec_BCG6K u v S.zeroBall_BCG6K)
    {κ : Type*} (Z : κ → Set W.Carrier) (c : κ → W.pieceInterior ⊤)
    (hZ : ∀ k,
      letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      letI := S.family.instMetricN
      letI := S.family.instChartedN
      letI := S.family.instMetricC
      ∃ hk : c k ∈ S.family.zero.centres,
        Z k ⊆ riemannianBallOf g (c k).val (S.family.zero.zero (c k) hk).radius)
    (i : Fin S.packet.cusp.count) (k : κ) :
    Disjoint (S.packet.cuspCore_BCG6K i u v) (Z k) := by
  obtain ⟨hk, hsub⟩ := hZ k
  exact BoundaryCollarPacket.cuspCore_disjoint_of_subset_zeroBall_BCG6K h
    (j := (⟨c k, hk⟩ : S.zeroIndex_BCG6K)) hsub i

end BoundarySupplyCore

end DifferentialGeometry.Geometry.Collapse
