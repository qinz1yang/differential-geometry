import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreRow
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryInterfaceAugmented

/-!
# BCG06: the collar flow fixes every original zero ball (review 72 D72-2; lane B-BCG-ROWS)

Blueprint `master207B.tex`, BCG06 (B:9290–9469) with BCG07's use of it (B:9546–9558); external
review 72 §1(e), disposition D72-2 (the remaining corollary). The whole-inner-collar clause of
`BoundaryCuspCoreComponent_BCG6K` carries the jointly smooth relative ambient isotopy `Φ`,
reparametrized by the smooth transition and transporting all level values at once, supported in a
compact `K'` inside the collar band at heights `38 < η_b < 42`. On the SAME stored supply, T3's
separated clause puts every original selected zero ball off the enlarged collars `e_b{z < 92}`;
`K' ⊂ e_b{z < 92}` (the height is within the tolerance `ε ≤ 1` of the collar coordinate), so
`Φ` fixes every original zero ball pointwise — hence every actual zero domain inside it
(`core_subset_ball`). Disjointness `C_b ∩ Z_k = ∅` alone would not suffice (the support of `Φ`
reaches `40 < η_b < 42`, outside `C_b`).

* `BoundaryCollarPacket.mem_collar_lt_ninetyTwo_of_band_BGR` (`η_b < 42` on the band ⟹
  `e_b{z < 92}`), `BoundaryCollarPacket.fixes_of_disjoint_collar_BGR` (support in the band, a set
  off the enlarged collar is fixed pointwise);
* **`BoundarySupplyCore.flow_fixes_zeroBalls_BGR`**: in the separated branch, every component's
  whole-inner-collar isotopy (the clause verbatim) fixes every `S.zeroBall_BCG6K z` pointwise.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

universe u

namespace BoundaryCollarPacket

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
  {A : ℝ → ℝ} {w₀ ε : ℝ} (P : BoundaryCollarPacket W g K A w₀ ε) {b : Fin P.cusp.count}

/-- A band point of height `< 42` lies in the enlarged collar `e_b{z < 92}`. -/
theorem mem_collar_lt_ninetyTwo_of_band_BGR {x : W.Carrier} (hx : x ∈ P.collarBand_BAUGA b)
    (hη : P.height b x < 42) :
    x ∈ (P.cusp.collar b).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92} := by
  obtain ⟨q, ⟨h2, h98⟩, rfl⟩ := hx
  have hq := (P.height_contract b q
    (cusp_mem_cuspDomain_of_le (b := 98) (by norm_num [cuspDepth]) h98.le) h2.le h98.le).1
  have hε := P.tolerance_le_one
  refine ⟨q, ?_, rfl⟩
  change q.2.val 0 < 92
  linarith [(abs_lt.mp hq).1]

/-- **An isotopy supported in the band at heights `< 42` fixes every set off the enlarged
collar.** -/
theorem fixes_of_disjoint_collar_BGR {K' Z : Set W.Carrier} {Φ : ℝ → W.Carrier → W.Carrier}
    (hK : ∀ x ∈ K', x ∈ P.collarBand_BAUGA b ∧ 38 < P.height b x ∧ P.height b x < 42)
    (hfix : ∀ t x, x ∉ K' → Φ t x = x)
    (hZ : Disjoint Z ((P.cusp.collar b).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})) :
    ∀ t, ∀ x ∈ Z, Φ t x = x := fun t x hx => hfix t x fun hxK =>
  Set.disjoint_left.mp hZ hx (P.mem_collar_lt_ninetyTwo_of_band_BGR (hK x hxK).1 (hK x hxK).2.2)

end BoundaryCollarPacket

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundarySupplyCore

variable (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
  ζ Λz W g δn n B oM)

/-- **BCG06's collar isotopy fixes every original zero ball** (D72-2, separated branch of the SAME
`S.geometric_cases`): every component's whole-inner-collar clause holds with an isotopy `Φ` (the
jointly smooth relative ambient isotopy, reparametrized by the smooth transition, transporting all
level values at once) that is the identity at every point of every original selected zero ball
`S.zeroBall_BCG6K z`, for every time. -/
theorem flow_fixes_zeroBalls_BGR (hsep : S.SeparatedCollarZero_BIF)
    {u v : Fin S.packet.toBoundaryCollarPacket.cusp.count → W.Carrier → ℝ}
    {i : Fin S.packet.toBoundaryCollarPacket.cusp.count}
    (hC : S.packet.toBoundaryCollarPacket.BoundaryCuspCoreComponent_BCG6K u v i) :
    ∃ (K' : Set W.Carrier) (Φ : ℝ → Diffeomorph W.model W.model W.Carrier W.Carrier ∞),
      IsCompact K' ∧
      (∀ x ∈ K', x ∈ S.packet.toBoundaryCollarPacket.collarBand_BAUGA i ∧
        38 < S.packet.toBoundaryCollarPacket.height i x ∧
        S.packet.toBoundaryCollarPacket.height i x < 42) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod W.model) W.model ∞ (fun q : ℝ × W.Carrier => Φ q.1 q.2) ∧
      (∀ x, Φ 0 x = x) ∧ (∀ t x, x ∉ K' → Φ t x = x) ∧
      (∀ y, ¬ W.model.IsInteriorPoint y → ∀ᶠ z in 𝓝 y, ∀ t, Φ t z = z) ∧
      (∀ t x, S.packet.toBoundaryCollarPacket.coreLevelT_BCG6K i (u i) (Real.smoothTransition t)
        (Φ t x) = S.packet.toBoundaryCollarPacket.level i x) ∧
      (∀ τ ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1, ∀ x,
        S.packet.toBoundaryCollarPacket.coreLevelT_BCG6K i (u i) τ (Φ t x) =
          S.packet.toBoundaryCollarPacket.level i x) ∧
      (∀ c : ℝ, Φ 1 '' {x | S.packet.toBoundaryCollarPacket.level i x ≤ c} =
        {x | S.packet.toBoundaryCollarPacket.coreLevel_BCG6K i (u i) x ≤ c}) ∧
      Φ 1 '' {x | S.packet.toBoundaryCollarPacket.level i x ≤ 40} =
        S.packet.toBoundaryCollarPacket.cuspCore_BCG6K i u v ∧
      Φ 1 '' {x | S.packet.toBoundaryCollarPacket.level i x = 40} =
        S.packet.toBoundaryCollarPacket.cuspFront_BCG6K i u v ∧
      ∀ (z : S.zeroIndex_BCG6K) (t : ℝ), ∀ x ∈ S.zeroBall_BCG6K z, Φ t x = x := by
  obtain ⟨K', Φ, h1, hK, h3, h4, hfix, h6, h7, h8, h9, h10, h11⟩ := hC.whole_inner_collar
  refine ⟨K', Φ, h1, hK, h3, h4, hfix, h6, h7, h8, h9, h10, h11, fun z t x hx => ?_⟩
  exact S.packet.toBoundaryCollarPacket.fixes_of_disjoint_collar_BGR (Φ := fun t y => Φ t y) hK
    hfix (hsep.2.1 z.1 z.2 i) t x hx

end BoundarySupplyCore

end DifferentialGeometry.Geometry.Collapse
