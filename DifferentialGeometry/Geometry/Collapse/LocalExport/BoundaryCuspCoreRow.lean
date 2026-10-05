import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreFlowW
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreSupply

/-!
# BCG06, G6: the whole row (lane BCG6-Kb)

Blueprint BCG06 (`master207B.tex:9290–9323`) clause by clause, on ONE packet `P`, for boundary
pairs `(u, v)` with (BI), (BFM), (BD) (`ε∂ < 10⁻⁶`, `0 ≤ c₃ < 10⁻⁵`):

* `BoundaryCuspCoreComponent_BCG6K P u v b` (Prop, OUTPUT only): every clause of BCG06 that holds
  for ONE component in BOTH branches of T3's alternative — compactness, the WHOLE inner collar (the
  relative supported flow on `W` carrying `{level_b ≤ 40}` onto `C_b`, `G ∘ Φ_t = level_b` at all
  levels), the labelled smooth product `T² × [0, 1]` with `∂C_b = ∂_bW ⊔ H_b`, the external label
  `C_b ∩ ∂W = ∂_bW`, the relative frontier `frontier C_b = H_b`, `H_b ⊆ Safe_b ∩
  {39.99 < η_b < 40.01}`, `v_b = 1` on and near `H_b`, `d(u_b − 40) ≠ 0` and `d(u_b − 40 v_b) ≠ 0`
  on `H_b`, `C_b ⊆ e_b{z < 42}`, the strict-marker equivalence;
* new clause lemmas: `marker_eq_one_on_front_BCG6K`, `front_height_bounds_BCG6K`,
  `mfderiv_u_sub_forty_ne_zero_BCG6K`, `cuspCore_inter_boundary_BCG6K`;
* `boundaryCuspCoreComponent_BCG6K` (per component) and the row `bcg06_row_BCG6K`:
  `(∀ b, component clauses) ∧ BoundaryGeometricOutput_BCG6K P u v Zb` (product branch: labelled
  whole product, no cores; separated branch: pairwise disjoint cores, disjoint from the zero balls);
* on the stored supply: `bcg06_row_supply_BCG6K` with the actual original zero balls
  `S.zeroBall_BCG6K`.

No named hypothesis; the new structure is inhabited in `BoundaryCuspCoreRowApplications` (double cusp).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Analysis DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Geometry.Collapse

universe u

section Kernel

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
  {A : ℝ → ℝ} {w₀ ε : ℝ}

namespace BoundaryCollarPacket

variable {P : BoundaryCollarPacket W g K A w₀ ε} {b : Fin P.cusp.count}

/-- On the front the marker is exactly `1`. -/
theorem marker_eq_one_on_front_BCG6K {u v : Fin P.cusp.count → W.Carrier → ℝ} {εd : ℝ}
    (hεd : εd < 1 / 1000000)
    (hBI : ∀ x, |u b x - (P.block b x).1| < εd ∧ |v b x - (P.block b x).2| < εd)
    (hBFM : ∀ x ∈ P.safeBand_BAUGA b, v b x = 1) {x : W.Carrier}
    (hx : x ∈ P.cuspFront_BCG6K b u v) : v b x = 1 :=
  (P.front_localization_BCG6K hεd hBI hBFM hx).2.2.1

/-- The front lies in `Safe_b ∩ {39.99 < η_b < 40.01}`. -/
theorem front_height_bounds_BCG6K {u v : Fin P.cusp.count → W.Carrier → ℝ} {εd : ℝ}
    (hεd : εd < 1 / 1000000)
    (hBI : ∀ x, |u b x - (P.block b x).1| < εd ∧ |v b x - (P.block b x).2| < εd)
    (hBFM : ∀ x ∈ P.safeBand_BAUGA b, v b x = 1) {x : W.Carrier}
    (hx : x ∈ P.cuspFront_BCG6K b u v) :
    x ∈ P.safeBand_BAUGA b ∧ 3999 / 100 < P.height b x ∧ P.height b x < 4001 / 100 := by
  obtain ⟨hsafe, hloc, -, -⟩ := P.front_localization_BCG6K hεd hBI hBFM hx
  have h := abs_lt.mp hloc
  exact ⟨hsafe, by linarith [h.1], by linarith [h.2]⟩

/-- **`u_b − 40` has nonzero differential on the front** (blueprint BCG06): near a front point
`v_b ≡ 1`, so `u_b − 40 = u_b − 40 v_b` there. -/
theorem mfderiv_u_sub_forty_ne_zero_BCG6K (hε : ε ≤ 1 / 1000)
    {u v : Fin P.cusp.count → W.Carrier → ℝ} (hu : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (u b))
    {εd c₃ : ℝ} (hεd : εd < 1 / 1000000) (hc₃ : 0 ≤ c₃) (hR : 80 * εd + 102 / 100 * c₃ < 1)
    (hBI : ∀ x, |u b x - (P.block b x).1| < εd ∧ |v b x - (P.block b x).2| < εd)
    (hBFM : ∀ x ∈ P.safeBand_BAUGA b, v b x = 1)
    (hBD : ∀ x ∈ P.collarBand_BAUGA b, 38 ≤ P.height b x → P.height b x ≤ 42 →
      ∀ w : TangentSpace W.model x, |mvfderiv W.model (fun y => u b y - P.height b y) x w| ≤
        c₃ * Real.sqrt (g.inner x w w))
    {x : W.Carrier} (hx : x ∈ P.cuspFront_BCG6K b u v) :
    mfderiv W.model 𝓘(ℝ, ℝ) (fun y => u b y - 40) x ≠ 0 := by
  have hdd := P.defining_differential_ne_zero_BCG6K hε hu hεd hc₃ hR hBI hBFM hBD hx
  have heq : (fun y => u b y - 40) =ᶠ[𝓝 x] fun y => u b y - 40 * v b y := by
    filter_upwards [P.marker_eq_one_near_front_BCG6K hεd hBI hBFM hx] with y hy
    rw [hy, mul_one]
  rw [heq.mfderiv_eq]
  exact hdd

/-- **The external label is kept**: `C_b ∩ ∂W = ∂_b W`. -/
theorem cuspCore_inter_boundary_BCG6K {u v : Fin P.cusp.count → W.Carrier → ℝ} {εd : ℝ}
    (hεd : εd < 1 / 1000000)
    (hBI : ∀ x, |u b x - (P.block b x).1| < εd ∧ |v b x - (P.block b x).2| < εd)
    (hBFM : ∀ x ∈ P.safeBand_BAUGA b, v b x = 1) :
    P.cuspCore_BCG6K b u v ∩ {y | W.model.IsBoundaryPoint y} = P.cusp.component b := by
  rw [P.cuspCore_eq_BCG6K hεd hBI hBFM]
  ext y
  constructor
  · rintro ⟨hy, hb⟩
    exact P.mem_component_of_isBoundaryPoint_BCG6K hεd hBI hBFM hb hy
  · intro hy
    refine ⟨?_, ?_⟩
    · change P.coreLevel_BCG6K b (u b) y ≤ 40
      rw [P.coreLevel_eq_levelBase_BCG6K b (u b) hy]
      linarith [P.levelBase_lt_thirtyNine_BCG6K b]
    · exact (W.model.isInteriorPoint_or_isBoundaryPoint y).resolve_left
        (not_isInteriorPoint_of_mem_component_BCG6K P b hy)

variable (P) in
/-- **BCG06 for one component** (OUTPUT only; every clause that holds in both branches of T3's
alternative). -/
structure BoundaryCuspCoreComponent_BCG6K (u v : Fin P.cusp.count → W.Carrier → ℝ)
    (b : Fin P.cusp.count) : Prop where
  compact_core : IsCompact (P.cuspCore_BCG6K b u v)
  whole_inner_collar :
    ∃ (K' : Set W.Carrier) (Φ : ℝ → Diffeomorph W.model W.model W.Carrier W.Carrier ∞),
      IsCompact K' ∧
      (∀ x ∈ K', x ∈ P.collarBand_BAUGA b ∧ 38 < P.height b x ∧ P.height b x < 42) ∧
      ContMDiff (𝓘(ℝ, ℝ).prod W.model) W.model ∞ (fun q : ℝ × W.Carrier => Φ q.1 q.2) ∧
      (∀ x, Φ 0 x = x) ∧ (∀ t x, x ∉ K' → Φ t x = x) ∧
      (∀ y, ¬ W.model.IsInteriorPoint y → ∀ᶠ z in 𝓝 y, ∀ t, Φ t z = z) ∧
      (∀ t x, P.coreLevelT_BCG6K b (u b) (Real.smoothTransition t) (Φ t x) = P.level b x) ∧
      (∀ τ ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
        ∀ x, P.coreLevelT_BCG6K b (u b) τ (Φ t x) = P.level b x) ∧
      (∀ c : ℝ, Φ 1 '' {x | P.level b x ≤ c} = {x | P.coreLevel_BCG6K b (u b) x ≤ c}) ∧
      Φ 1 '' {x | P.level b x ≤ 40} = P.cuspCore_BCG6K b u v ∧
      Φ 1 '' {x | P.level b x = 40} = P.cuspFront_BCG6K b u v
  labelled_smooth_product :
    ∃ cs : ChartedSpace (EuclideanHalfSpace 3) (P.cuspCore_BCG6K b u v),
      letI := cs
      IsManifold (𝓡∂ 3) ∞ (P.cuspCore_BCG6K b u v) ∧
      ContMDiff (𝓡∂ 3) W.model ∞ (fun y : P.cuspCore_BCG6K b u v => (y : W.Carrier)) ∧
      (∀ y : P.cuspCore_BCG6K b u v, (𝓡∂ 3).IsBoundaryPoint y ↔
        ((y : W.Carrier) ∈ P.cusp.component b ∨ (y : W.Carrier) ∈ P.cuspFront_BCG6K b u v)) ∧
      ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) (𝓡∂ 3) (Torus × Icc (0 : ℝ) 1)
          (P.cuspCore_BCG6K b u v) ∞,
        (∀ p, (D p : W.Carrier) ∈ P.cusp.component b ↔ (p.2 : ℝ) = 0) ∧
        ∀ p, (D p : W.Carrier) ∈ P.cuspFront_BCG6K b u v ↔ (p.2 : ℝ) = 1
  boundary_label :
    P.cuspCore_BCG6K b u v ∩ {y | W.model.IsBoundaryPoint y} = P.cusp.component b
  boundary_front_disjoint : Disjoint (P.cusp.component b) (P.cuspFront_BCG6K b u v)
  relative_frontier_eq : frontier (P.cuspCore_BCG6K b u v) = P.cuspFront_BCG6K b u v
  front_localization : ∀ x ∈ P.cuspFront_BCG6K b u v,
    x ∈ P.safeBand_BAUGA b ∧ 3999 / 100 < P.height b x ∧ P.height b x < 4001 / 100
  marker_on_front : ∀ x ∈ P.cuspFront_BCG6K b u v, v b x = 1 ∧ ∀ᶠ y in 𝓝 x, v b y = 1
  u_differential_ne_zero : ∀ x ∈ P.cuspFront_BCG6K b u v,
    mfderiv W.model 𝓘(ℝ, ℝ) (fun y => u b y - 40) x ≠ 0
  defining_differential_ne_zero : ∀ x ∈ P.cuspFront_BCG6K b u v,
    mfderiv W.model 𝓘(ℝ, ℝ) (fun y => u b y - 40 * v b y) x ≠ 0
  core_subset_collar :
    P.cuspCore_BCG6K b u v ⊆ (P.cusp.collar b).toFun '' {q : CuspHalfSpace | q.2.val 0 < 42}
  strict_marker_equivalence :
    P.cuspCore_BCG6K b u v =
        P.cuspNbhd35_BCG6K b ∪ {x | (9 / 10 : ℝ) < v b x ∧ u b x ≤ 40 * v b x} ∧
      P.cuspFront_BCG6K b u v = {x | (9 / 10 : ℝ) < v b x ∧ u b x = 40 * v b x}

/-- **BCG06 for one component** from the kernel premises. -/
theorem boundaryCuspCoreComponent_BCG6K (hε : ε ≤ 1 / 1000)
    {u v : Fin P.cusp.count → W.Carrier → ℝ} (hu : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (u b))
    {εd c₃ : ℝ} (hεd : εd < 1 / 1000000) (hc₃0 : 0 ≤ c₃) (hc₃ : c₃ < 1 / 100000)
    (hBI : ∀ x, |u b x - (P.block b x).1| < εd ∧ |v b x - (P.block b x).2| < εd)
    (hBFM : ∀ x ∈ P.safeBand_BAUGA b, v b x = 1)
    (hBD : ∀ x ∈ P.collarBand_BAUGA b, 38 ≤ P.height b x → P.height b x ≤ 42 →
      ∀ w : TangentSpace W.model x, |mvfderiv W.model (fun y => u b y - P.height b y) x w| ≤
        c₃ * Real.sqrt (g.inner x w w)) :
    P.BoundaryCuspCoreComponent_BCG6K u v b := by
  have hR := register_R_BCG6K hεd hc₃
  refine ⟨?_, cuspCore_relative_flow_BCG6K hε hu hεd hc₃0 hR hBI hBFM hBD,
    P.cuspCore_labelled_product_BCG6K hε hu hεd hc₃0 hR hBI hBFM hBD,
    cuspCore_inter_boundary_BCG6K hεd hBI hBFM, ?_,
    P.frontier_cuspCore_BCG6K hε hu hεd hc₃0 hR hBI hBFM hBD,
    fun x hx => front_height_bounds_BCG6K hεd hBI hBFM hx,
    fun x hx => ⟨marker_eq_one_on_front_BCG6K hεd hBI hBFM hx,
      P.marker_eq_one_near_front_BCG6K hεd hBI hBFM hx⟩,
    fun x hx => mfderiv_u_sub_forty_ne_zero_BCG6K hε hu hεd hc₃0 hR hBI hBFM hBD hx,
    fun x hx => P.defining_differential_ne_zero_BCG6K hε hu hεd hc₃0 hR hBI hBFM hBD hx,
    P.cuspCore_subset_collar_BCG6K hεd hBI,
    ⟨P.cuspCore_eq_strict_BCG6K hεd hBI hBFM, P.cuspFront_eq_strict_BCG6K hεd hBI hBFM⟩⟩
  · rw [P.cuspCore_eq_BCG6K hεd hBI hBFM]
    exact (isClosed_le (P.contMDiff_coreLevel_BCG6K b hu).continuous
      continuous_const).isCompact
  · rw [Set.disjoint_left]
    intro x hX hH
    have h40 : P.coreLevel_BCG6K b (u b) x = 40 := by
      rw [P.cuspFront_eq_BCG6K hεd hBI hBFM] at hH
      exact hH
    rw [P.coreLevel_eq_levelBase_BCG6K b (u b) hX] at h40
    linarith [P.levelBase_lt_thirtyNine_BCG6K b]

variable (P) in
/-- **The BCG06 row (kernel form)**: every component satisfies the branch-free clauses, and T3's
alternative gives the geometric output (labelled whole product, no cores; or pairwise disjoint
cores, disjoint from the zero balls `Zb`). -/
theorem bcg06_row_BCG6K (hε : ε ≤ 1 / 1000) {u v : Fin P.cusp.count → W.Carrier → ℝ}
    (hu : ∀ b, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (u b))
    {εd c₃ : ℝ} (hεd : εd < 1 / 1000000) (hc₃0 : 0 ≤ c₃) (hc₃ : c₃ < 1 / 100000)
    (hBI : ∀ b x, |u b x - (P.block b x).1| < εd ∧ |v b x - (P.block b x).2| < εd)
    (hBFM : ∀ b, ∀ x ∈ P.safeBand_BAUGA b, v b x = 1)
    (hBD : ∀ b, ∀ x ∈ P.collarBand_BAUGA b, 38 ≤ P.height b x → P.height b x ≤ 42 →
      ∀ w : TangentSpace W.model x, |mvfderiv W.model (fun y => u b y - P.height b y) x w| ≤
        c₃ * Real.sqrt (g.inner x w w))
    {ζ : Type*} (Zb : ζ → Set W.Carrier)
    (halt : (∃ (i j : Fin P.cusp.count), i ≠ j ∧
        ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) W.model (Torus × Icc (0 : ℝ) 1) W.Carrier ∞,
          (∀ p, D p ∈ P.cusp.component i ↔ (p.2 : ℝ) = 0) ∧
            ∀ p, D p ∈ P.cusp.component j ↔ (p.2 : ℝ) = 1) ∨
      ((∀ i j : Fin P.cusp.count, i ≠ j →
        Disjoint ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})
          ((P.cusp.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})) ∧
        ∀ j (i : Fin P.cusp.count),
          Disjoint (Zb j) ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}))) :
    (∀ b, P.BoundaryCuspCoreComponent_BCG6K u v b) ∧ P.BoundaryGeometricOutput_BCG6K u v Zb :=
  ⟨fun b => boundaryCuspCoreComponent_BCG6K hε (hu b) hεd hc₃0 hc₃ (hBI b) (hBFM b) (hBD b),
    P.boundaryGeometricOutput_BCG6K hε hu hεd hc₃0 hc₃ hBI hBFM hBD Zb halt⟩

end BoundaryCollarPacket

end Kernel

section Supply

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundarySupplyCore

variable (S : BoundarySupplyCore K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
  ζ Λz W g δn n B oM)

/-- **The BCG06 row on the stored supply**: for boundary pairs with (BI), (BFM), (BD), every
component satisfies the branch-free clauses, and the geometric output holds with the ACTUAL
original selected zero balls of the stored family. -/
theorem bcg06_row_supply_BCG6K {u v : Fin S.packet.cusp.count → W.Carrier → ℝ}
    (hu : ∀ i, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (u i))
    {εd c₃ : ℝ} (hεd : εd < 1 / 1000000) (hc₃0 : 0 ≤ c₃) (hc₃ : c₃ < 1 / 100000)
    (hBI : ∀ i x, |u i x - (S.packet.block i x).1| < εd ∧ |v i x - (S.packet.block i x).2| < εd)
    (hBFM : ∀ i, ∀ x ∈ S.packet.safeBand_BAUGA i, v i x = 1)
    (hBD : ∀ i, ∀ x ∈ S.packet.collarBand_BAUGA i, 38 ≤ S.packet.height i x →
      S.packet.height i x ≤ 42 →
      ∀ y : TangentSpace W.model x, |mvfderiv W.model (fun z => u i z - S.packet.height i z) x y| ≤
        c₃ * Real.sqrt (g.inner x y y)) :
    (∀ i, S.packet.toBoundaryCollarPacket.BoundaryCuspCoreComponent_BCG6K u v i) ∧
      BoundaryCollarPacket.BoundaryGeometricOutput_BCG6K S.packet.toBoundaryCollarPacket u v
        S.zeroBall_BCG6K :=
  S.packet.toBoundaryCollarPacket.bcg06_row_BCG6K (cuspTolerance_le_thousandth_BCUSP1 _ _ _) hu
    hεd hc₃0 hc₃ hBI hBFM hBD S.zeroBall_BCG6K S.geometric_alternative_BCG6K

end BoundarySupplyCore

end Supply

end DifferentialGeometry.Geometry.Collapse
