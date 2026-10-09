import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreGraph
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspSaturationBC7C
import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.InnerCollarProduct
import DifferentialGeometry.Topology.Ehresmann.Interval

/-!
# BCG06, G4a: the labelled smooth product, the core spec and the geometric output (lane BCG6-K)

Draft 61 §4.1, §4.4–§4.5, dispositions D61-9, D65-2..D65-5. KERNEL form; the binding to the chain
map uses BCG7-COLLAR's block coordinates `J_b = augmentedBoundaryCoord_BC7C b`:
`(u_b, v_b) := J_b ∘ E` (`chainBoundaryU_BCG6K`, `chainBoundaryV_BCG6K`), so the front is literally
the set of BC7C's saturation exits (`cuspFront_chain_eq_BCG6K`).

* `cuspCore_labelled_product_BCG6K`: the tree's E6 kernel
  (`CuspEmbedding.exists_sublevel_diffeomorph_torus_Icc`) applied to the modified level `G` with its
  six inputs exported separately (`a < 40`, `G` smooth, no critical point on the whole `{G ≤ 40}`,
  `G = 40` attained, `G = a` on `∂_b W`, boundary points of `{G ≤ 40}` in `∂_b W`), transported to
  `↥C_b` by the global identities: `C_b` is a compact smooth manifold with boundary, its manifold
  boundary is `∂_b W ∪ H_b`, and `(C_b, ∂_b W, H_b) ≅ (T² × [0, 1], T² × {0}, T² × {1})`. The cusp
  embedding is never promoted to `C^∞` (E6 uses the `C^{K+1}` boundary parametrisation).
* `BoundaryCuspCoreSpec_BCG6K` (output structure, separated branch) and
  `boundaryCuspCoreSpec_BCG6K`; `BoundaryGeometricOutput_BCG6K` (`product` — no cores — or
  `separated` with the spec) and `boundaryGeometricOutput_BCG6K`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open scoped Manifold ContDiff Topology ENNReal
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Analysis DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Topology.Manifold

namespace DifferentialGeometry.Geometry.Collapse

local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

universe u

section Binding

variable {M : Type*} {ι κ : Type*}

/-- `u_b := (J_b ∘ E).1` with BCG7-COLLAR's block coordinates. -/
def chainBoundaryU_BCG6K (E : M → BlockSpace (fun _ : ι ⊕ κ => ℝ²)) (b : κ) (x : M) : ℝ :=
  (augmentedBoundaryCoord_BC7C b (E x)).1

/-- `v_b := (J_b ∘ E).2` with BCG7-COLLAR's block coordinates. -/
def chainBoundaryV_BCG6K (E : M → BlockSpace (fun _ : ι ⊕ κ => ℝ²)) (b : κ) (x : M) : ℝ :=
  (augmentedBoundaryCoord_BC7C b (E x)).2

end Binding

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
  {A : ℝ → ℝ} {w₀ ε : ℝ}

namespace BoundaryCollarPacket

/-- The front of `J_b ∘ E` is exactly the set of BCG7-COLLAR's saturation exits. -/
theorem cuspFront_chain_eq_BCG6K (P : BoundaryCollarPacket W g K A w₀ ε) {ι : Type*}
    (E : W.Carrier → BlockSpace (fun _ : ι ⊕ Fin P.cusp.count => ℝ²)) (b : Fin P.cusp.count) :
    P.cuspFront_BCG6K b (chainBoundaryU_BCG6K E) (chainBoundaryV_BCG6K E) =
      {x | 9 / 10 ≤ (augmentedBoundaryCoord_BC7C b (E x)).2 ∧
        (augmentedBoundaryCoord_BC7C b (E x)).1 = 40 * (augmentedBoundaryCoord_BC7C b (E x)).2} :=
  rfl

/-- (BI) for `J_b ∘ E` from the slot errors against BAUG-A's original augmented map
(`J_b ∘ F_∂ = P.block b`). -/
theorem chain_BI_of_original_BCG6K (P : BoundaryCollarPacket W g K A w₀ ε) {ι : Type*}
    (Fint : W.Carrier → BlockSpace (fun _ : ι => ℝ²))
    (E : W.Carrier → BlockSpace (fun _ : ι ⊕ Fin P.cusp.count => ℝ²)) (b : Fin P.cusp.count)
    {εd : ℝ} {x : W.Carrier}
    (h : |(augmentedBoundaryCoord_BC7C b (E x)).1 -
          (augmentedBoundaryCoord_BC7C b (boundaryOriginalMap_BAUGA P Fint x)).1| < εd ∧
        |(augmentedBoundaryCoord_BC7C b (E x)).2 -
          (augmentedBoundaryCoord_BC7C b (boundaryOriginalMap_BAUGA P Fint x)).2| < εd) :
    |chainBoundaryU_BCG6K E b x - (P.block b x).1| < εd ∧
      |chainBoundaryV_BCG6K E b x - (P.block b x).2| < εd := by
  rw [boundaryOriginalMap_BAUGA, augmentedBoundaryCoord_boundaryAugmentedMap_BC7C] at h
  exact h

variable {P : BoundaryCollarPacket W g K A w₀ ε} {b : Fin P.cusp.count}

/-- The registered condition (R) of review 65 from the blueprint thresholds. -/
theorem register_R_BCG6K {εd c₃ : ℝ} (hεd : εd < 1 / 1000000) (hc₃ : c₃ < 1 / 100000) :
    80 * εd + 102 / 100 * c₃ < 1 := by
  linarith

/-- **The labelled smooth product (G4a, E6)**: `C_b` is a compact smooth manifold with boundary
`∂_b W ∪ H_b`, diffeomorphic to `T² × [0, 1]` with `∂_b W ↦ T² × {0}` and `H_b ↦ T² × {1}`. -/
theorem cuspCore_labelled_product_BCG6K (hε : ε ≤ 1 / 1000)
    {u v : Fin P.cusp.count → W.Carrier → ℝ} (hu : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (u b))
    {εd c₃ : ℝ} (hεd : εd < 1 / 1000000) (hc₃ : 0 ≤ c₃) (hR : 80 * εd + 102 / 100 * c₃ < 1)
    (hBI : ∀ x, |u b x - (P.block b x).1| < εd ∧ |v b x - (P.block b x).2| < εd)
    (hBFM : ∀ x ∈ P.safeBand_BAUGA b, v b x = 1)
    (hBD : ∀ x ∈ P.collarBand_BAUGA b, 38 ≤ P.height b x → P.height b x ≤ 42 →
      ∀ w : TangentSpace W.model x, |mvfderiv W.model (fun y => u b y - P.height b y) x w| ≤
        c₃ * Real.sqrt (g.inner x w w)) :
    ∃ cs : ChartedSpace (EuclideanHalfSpace 3) (P.cuspCore_BCG6K b u v),
      letI := cs
      IsManifold (𝓡∂ 3) ∞ (P.cuspCore_BCG6K b u v) ∧
      ContMDiff (𝓡∂ 3) W.model ∞ (fun y : P.cuspCore_BCG6K b u v => (y : W.Carrier)) ∧
      (∀ y : P.cuspCore_BCG6K b u v, (𝓡∂ 3).IsBoundaryPoint y ↔
        ((y : W.Carrier) ∈ P.cusp.component b ∨ (y : W.Carrier) ∈ P.cuspFront_BCG6K b u v)) ∧
      ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) (𝓡∂ 3) (Torus × Icc (0 : ℝ) 1)
          (P.cuspCore_BCG6K b u v) ∞,
        (∀ p, (D p : W.Carrier) ∈ P.cusp.component b ↔ (p.2 : ℝ) = 0) ∧
        ∀ p, (D p : W.Carrier) ∈ P.cuspFront_BCG6K b u v ↔ (p.2 : ℝ) = 1 := by
  have ha39 := P.levelBase_lt_thirtyNine_BCG6K b
  have har : P.levelBase b < 40 := by linarith
  have hF := P.contMDiff_coreLevel_BCG6K b hu
  have hreg : ∀ x, P.coreLevel_BCG6K b (u b) x ≤ 40 →
      mfderiv W.model 𝓘(ℝ, ℝ) (P.coreLevel_BCG6K b (u b)) x ≠ 0 := fun x hx =>
    P.mfderiv_coreLevel_ne_zero_BCG6K b hε hu hc₃ hR (fun y _ => (hBI y).1) hBD hx
  have hr := P.exists_coreLevel_eq_forty_BCG6K b hu
  have hXa : ∀ x ∈ P.cusp.component b, P.coreLevel_BCG6K b (u b) x = P.levelBase b :=
    fun x hx => P.coreLevel_eq_levelBase_BCG6K b (u b) hx
  have hbd : ∀ x, W.model.IsBoundaryPoint x → P.coreLevel_BCG6K b (u b) x ≤ 40 →
      x ∈ P.cusp.component b := fun x hx hle =>
    P.mem_component_of_isBoundaryPoint_BCG6K hεd hBI hBFM hx hle
  obtain ⟨cs, hman, hval, hbdy, D, hDF, hDX⟩ :=
    (P.cusp.collar b).exists_sublevel_diffeomorph_torus_Icc har hF hreg hr hXa hbd
  rw [P.cuspCore_eq_BCG6K hεd hBI hBFM, P.cuspFront_eq_BCG6K hεd hBI hBFM]
  have : Fact (P.levelBase b < 40) := ⟨har⟩
  let cs' : ChartedSpace (EuclideanHalfSpace 3) {x | P.coreLevel_BCG6K b (u b) x ≤ 40} := cs
  let := cs'
  refine ⟨cs', hman, hval, hbdy,
    DifferentialGeometry.Topology.Ehresmann.unitCylinderDiffeomorphOfProduct (P.levelBase b) 40
      (Diffeomorph.refl torusModel Torus _) D, fun p => ?_, fun p => ?_⟩
  · rw [DifferentialGeometry.Topology.Ehresmann.unitCylinderDiffeomorphOfProduct_apply, hDX,
      DifferentialGeometry.Topology.Ehresmann.affineIntervalDiffeomorph_apply]
    constructor
    · intro h
      have h1 : (40 - P.levelBase b) * (p.2 : ℝ) = 0 := by linarith
      rcases mul_eq_zero.mp h1 with h2 | h2
      · linarith
      · exact h2
    · intro h
      rw [h]
      ring
  · rw [DifferentialGeometry.Topology.Ehresmann.unitCylinderDiffeomorphOfProduct_apply,
      Set.mem_ofPred_eq, hDF, DifferentialGeometry.Topology.Ehresmann.affineIntervalDiffeomorph_apply]
    constructor
    · intro h
      have h1 : (40 - P.levelBase b) * ((p.2 : ℝ) - 1) = 0 := by linarith
      rcases mul_eq_zero.mp h1 with h2 | h2
      · linarith
      · linarith
    · intro h
      rw [h]
      ring

/-- The core lies in the collar below height `42` (`N₃₅` below `35.01`, the marked branch below
`η_b < 40.001`). -/
theorem cuspCore_subset_collar_BCG6K {u v : Fin P.cusp.count → W.Carrier → ℝ} {εd : ℝ}
    (hεd : εd < 1 / 1000000)
    (hBI : ∀ x, |u b x - (P.block b x).1| < εd ∧ |v b x - (P.block b x).2| < εd) :
    P.cuspCore_BCG6K b u v ⊆ (P.cusp.collar b).toFun '' {q : CuspHalfSpace | q.2.val 0 < 42} := by
  rintro x (hN | ⟨h9, hle⟩)
  · obtain ⟨q, -, hqx, hqz⟩ := P.exists_height_lt_of_mem_cuspNbhd35_BCG6K b hN
    exact ⟨q, by change q.2.val 0 < 42; linarith, hqx⟩
  · obtain ⟨-, hband, -, -⟩ := P.mem_collarBand_of_marker_BCG6K b (by linarith) (hBI x).2 h9
    have hlt := P.height_lt_of_marked_BCG6K b (by linarith) (hBI x).1 (hBI x).2 h9 hle
    have hloc := loc_constant_lt_BCG6K hεd
    obtain ⟨p, hp, rfl⟩ := hband
    have hpd : p ∈ cuspDomain :=
      cusp_mem_cuspDomain_of_le (b := 98) (by norm_num [cuspDepth]) hp.2.le
    have hc := abs_lt.mp (P.height_contract b p hpd hp.1.le hp.2.le).1
    have hε1 := P.tolerance_le_one
    exact ⟨p, by change p.2.val 0 < 42; linarith, rfl⟩

/-- **The marker is identically one near the front** (BCG05 on the open safe band). -/
theorem marker_eq_one_near_front_BCG6K {u v : Fin P.cusp.count → W.Carrier → ℝ} {εd : ℝ}
    (hεd : εd < 1 / 1000000)
    (hBI : ∀ x, |u b x - (P.block b x).1| < εd ∧ |v b x - (P.block b x).2| < εd)
    (hBFM : ∀ x ∈ P.safeBand_BAUGA b, v b x = 1) {x : W.Carrier}
    (hx : x ∈ P.cuspFront_BCG6K b u v) : ∀ᶠ y in 𝓝 x, v b y = 1 := by
  obtain ⟨hsafe, hloc, -, -⟩ := P.front_localization_BCG6K hεd hBI hBFM hx
  have hl := abs_lt.mp hloc
  have hO : IsOpen (P.collarBand_BAUGA b ∩ {y | 32 < P.height b y ∧ P.height b y < 78}) :=
    (P.isOpen_collarBand_BAUGA b).inter ((isOpen_lt continuous_const
      (P.contMDiff_height b).continuous).inter (isOpen_lt (P.contMDiff_height b).continuous
        continuous_const))
  filter_upwards [hO.mem_nhds ⟨hsafe.1, by linarith, by linarith⟩] with y hy
  exact hBFM y ⟨hy.1, hy.2.1.le, hy.2.2.le⟩

/-- **The defining differential of the front is nonzero** (review 65 M4): near a front point
`v ≡ 1` and `u = G`, so `d(u - 40 v) = dG ≠ 0`. -/
theorem defining_differential_ne_zero_BCG6K (hε : ε ≤ 1 / 1000)
    {u v : Fin P.cusp.count → W.Carrier → ℝ} (hu : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (u b))
    {εd c₃ : ℝ} (hεd : εd < 1 / 1000000) (hc₃ : 0 ≤ c₃) (hR : 80 * εd + 102 / 100 * c₃ < 1)
    (hBI : ∀ x, |u b x - (P.block b x).1| < εd ∧ |v b x - (P.block b x).2| < εd)
    (hBFM : ∀ x ∈ P.safeBand_BAUGA b, v b x = 1)
    (hBD : ∀ x ∈ P.collarBand_BAUGA b, 38 ≤ P.height b x → P.height b x ≤ 42 →
      ∀ w : TangentSpace W.model x, |mvfderiv W.model (fun y => u b y - P.height b y) x w| ≤
        c₃ * Real.sqrt (g.inner x w w))
    {x : W.Carrier} (hx : x ∈ P.cuspFront_BCG6K b u v) :
    mfderiv W.model 𝓘(ℝ, ℝ) (fun y => u b y - 40 * v b y) x ≠ 0 := by
  obtain ⟨hsafe, hloc, -, -⟩ := P.front_localization_BCG6K hεd hBI hBFM hx
  obtain ⟨hxS, -⟩ := P.mem_strip_of_mem_front_BCG6K hεd hBI hx
  have hl := abs_lt.mp hloc
  have hx40 : P.coreLevel_BCG6K b (u b) x = 40 := by
    have h := hx
    rw [P.cuspFront_eq_BCG6K hεd hBI hBFM] at h
    exact h
  have hreg := P.mfderiv_coreLevel_ne_zero_BCG6K b hε hu hc₃ hR (fun y _ => (hBI y).1) hBD
    (le_of_eq hx40)
  have hO : IsOpen (P.coreStrip_BCG6K b ∩ {y | 79 / 2 < P.height b y ∧ P.height b y < 81 / 2}) :=
    (P.isOpen_coreStrip_BCG6K b).inter ((isOpen_lt continuous_const
      (P.contMDiff_height b).continuous).inter (isOpen_lt (P.contMDiff_height b).continuous
        continuous_const))
  have heq : (fun y => u b y - 40 * v b y) =ᶠ[𝓝 x]
      fun y => P.coreLevel_BCG6K b (u b) y + (-40) := by
    filter_upwards [hO.mem_nhds ⟨hxS, by linarith, by linarith⟩,
      P.marker_eq_one_near_front_BCG6K hεd hBI hBFM hx] with y hy hv1
    rw [P.coreLevel_eq_on_strip_BCG6K b (u b) hy.1,
      coreCutoff_eq_one_BCG6K hy.2.1.le hy.2.2.le, hv1]
    ring
  have hGd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) (P.coreLevel_BCG6K b (u b)) x :=
    ((P.contMDiff_coreLevel_BCG6K b hu) x).mdifferentiableAt (by simp)
  rw [← mvfderiv_ne_zero_iff_BCG6K, mvfderiv_congr_BCG6K heq,
    mvfderiv_fun_add hGd mdifferentiableAt_const, mvfderiv_const, add_zero,
    mvfderiv_ne_zero_iff_BCG6K]
  exact hreg

variable (P) in
/-- **BCG06 output on the separated branch** (draft 61 §4.1, review 65 M4), for the boundary pairs
`(u_b, v_b)` of all components and an indexed family `Zb` of original selected zero balls. -/
structure BoundaryCuspCoreSpec_BCG6K (u v : Fin P.cusp.count → W.Carrier → ℝ) {ζ : Type*}
    (Zb : ζ → Set W.Carrier) : Prop where
  compact_core : ∀ b, IsCompact (P.cuspCore_BCG6K b u v)
  relative_frontier_eq : ∀ b, frontier (P.cuspCore_BCG6K b u v) = P.cuspFront_BCG6K b u v
  front_localization : ∀ b, ∀ x ∈ P.cuspFront_BCG6K b u v,
    x ∈ P.safeBand_BAUGA b ∧ |P.height b x - 40| < 1 / 1000
  marker_eq_one_near_front : ∀ b, ∀ x ∈ P.cuspFront_BCG6K b u v, ∀ᶠ y in 𝓝 x, v b y = 1
  defining_differential_ne_zero : ∀ b, ∀ x ∈ P.cuspFront_BCG6K b u v,
    mfderiv W.model 𝓘(ℝ, ℝ) (fun y => u b y - 40 * v b y) x ≠ 0
  labelled_smooth_product : ∀ b,
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
  boundary_front_disjoint : ∀ b, Disjoint (P.cusp.component b) (P.cuspFront_BCG6K b u v)
  core_subset_collar : ∀ b,
    P.cuspCore_BCG6K b u v ⊆ (P.cusp.collar b).toFun '' {q : CuspHalfSpace | q.2.val 0 < 42}
  pairwise_disjoint : ∀ b b', b ≠ b' →
    Disjoint (P.cuspCore_BCG6K b u v) (P.cuspCore_BCG6K b' u v)
  disjoint_original_zero_balls : ∀ b j, Disjoint (P.cuspCore_BCG6K b u v) (Zb j)
  strict_marker_equivalence : ∀ b,
    P.cuspCore_BCG6K b u v =
        P.cuspNbhd35_BCG6K b ∪ {x | (9 / 10 : ℝ) < v b x ∧ u b x ≤ 40 * v b x} ∧
      P.cuspFront_BCG6K b u v = {x | (9 / 10 : ℝ) < v b x ∧ u b x = 40 * v b x}

/-- **BCG06 (kernel, separated branch)**: with the BCG04 / BCG05 conclusions as explicit
premises for every component (`ε∂ < 10⁻⁶`, `c₃ < 10⁻⁵`), the enlarged-collar separation and the
separation of the original zero balls from the enlarged collars, the cores satisfy the spec. -/
theorem boundaryCuspCoreSpec_BCG6K (P : BoundaryCollarPacket W g K A w₀ ε) (hε : ε ≤ 1 / 1000)
    {u v : Fin P.cusp.count → W.Carrier → ℝ} (hu : ∀ b, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (u b))
    {εd c₃ : ℝ} (hεd : εd < 1 / 1000000) (hc₃0 : 0 ≤ c₃) (hc₃ : c₃ < 1 / 100000)
    (hBI : ∀ b x, |u b x - (P.block b x).1| < εd ∧ |v b x - (P.block b x).2| < εd)
    (hBFM : ∀ b, ∀ x ∈ P.safeBand_BAUGA b, v b x = 1)
    (hBD : ∀ b, ∀ x ∈ P.collarBand_BAUGA b, 38 ≤ P.height b x → P.height b x ≤ 42 →
      ∀ w : TangentSpace W.model x, |mvfderiv W.model (fun y => u b y - P.height b y) x w| ≤
        c₃ * Real.sqrt (g.inner x w w))
    (hsep : ∀ i j : Fin P.cusp.count, i ≠ j →
      Disjoint ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})
        ((P.cusp.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}))
    {ζ : Type*} (Zb : ζ → Set W.Carrier)
    (hZ : ∀ j (i : Fin P.cusp.count),
      Disjoint (Zb j) ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})) :
    BoundaryCuspCoreSpec_BCG6K P u v Zb := by
  have hR := register_R_BCG6K hεd hc₃
  have hsub : ∀ b, P.cuspCore_BCG6K b u v ⊆
      (P.cusp.collar b).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92} := fun b x hx => by
    obtain ⟨q, hq, hqx⟩ := P.cuspCore_subset_collar_BCG6K hεd (hBI b) hx
    exact ⟨q, by change q.2.val 0 < 92; linarith [show q.2.val 0 < 42 from hq], hqx⟩
  refine ⟨fun b => ?_, fun b => ?_, fun b x hx => ?_, fun b x hx => ?_, fun b x hx => ?_,
    fun b => ?_, fun b => ?_, fun b => P.cuspCore_subset_collar_BCG6K hεd (hBI b),
    fun b b' hbb' => ?_, fun b j => ?_, fun b => ?_⟩
  · rw [P.cuspCore_eq_BCG6K hεd (hBI b) (hBFM b)]
    exact (isClosed_le (P.contMDiff_coreLevel_BCG6K b (hu b)).continuous
      continuous_const).isCompact
  · exact P.frontier_cuspCore_BCG6K hε (hu b) hεd hc₃0 hR (hBI b) (hBFM b) (hBD b)
  · obtain ⟨h1, h2, -, -⟩ := P.front_localization_BCG6K hεd (hBI b) (hBFM b) hx
    exact ⟨h1, h2⟩
  · exact P.marker_eq_one_near_front_BCG6K hεd (hBI b) (hBFM b) hx
  · exact P.defining_differential_ne_zero_BCG6K hε (hu b) hεd hc₃0 hR (hBI b) (hBFM b) (hBD b) hx
  · exact P.cuspCore_labelled_product_BCG6K hε (hu b) hεd hc₃0 hR (hBI b) (hBFM b) (hBD b)
  · rw [Set.disjoint_left]
    intro x hX hH
    have h40 : P.coreLevel_BCG6K b (u b) x = 40 := by
      rw [P.cuspFront_eq_BCG6K hεd (hBI b) (hBFM b)] at hH
      exact hH
    rw [P.coreLevel_eq_levelBase_BCG6K b (u b) hX] at h40
    linarith [P.levelBase_lt_thirtyNine_BCG6K b]
  · exact (hsep b b' hbb').mono (hsub b) (hsub b')
  · exact ((hZ j b).symm).mono_left (hsub b)
  · exact ⟨P.cuspCore_eq_strict_BCG6K hεd (hBI b) (hBFM b),
      P.cuspFront_eq_strict_BCG6K hεd (hBI b) (hBFM b)⟩

variable (P) in
/-- **The geometric output of the boundary branch** (draft 61 §4.5): the labelled whole product
(no cores are constructed) OR the separated branch with the core spec. -/
inductive BoundaryGeometricOutput_BCG6K (u v : Fin P.cusp.count → W.Carrier → ℝ) {ζ : Type*}
    (Zb : ζ → Set W.Carrier) : Prop where
  | product (h : ∃ (i j : Fin P.cusp.count), i ≠ j ∧
      ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) W.model (Torus × Icc (0 : ℝ) 1) W.Carrier ∞,
        (∀ p, D p ∈ P.cusp.component i ↔ (p.2 : ℝ) = 0) ∧
          ∀ p, D p ∈ P.cusp.component j ↔ (p.2 : ℝ) = 1)
  | separated
      (hsep : ∀ i j : Fin P.cusp.count, i ≠ j →
        Disjoint ((P.cusp.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})
          ((P.cusp.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}))
      (spec : BoundaryCuspCoreSpec_BCG6K P u v Zb)

/-- **BCG06 (kernel)**: T3's alternative (labelled product, OR enlarged-collar separation with
the separation of the original zero balls) and the BCG04 / BCG05 premises give the geometric
output. -/
theorem boundaryGeometricOutput_BCG6K (P : BoundaryCollarPacket W g K A w₀ ε)
    (hε : ε ≤ 1 / 1000) {u v : Fin P.cusp.count → W.Carrier → ℝ}
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
    BoundaryGeometricOutput_BCG6K P u v Zb := by
  rcases halt with hprod | ⟨hsep, hZ⟩
  · exact BoundaryGeometricOutput_BCG6K.product hprod
  · exact BoundaryGeometricOutput_BCG6K.separated hsep
      (boundaryCuspCoreSpec_BCG6K P hε hu hεd hc₃0 hc₃ hBI hBFM hBD hsep Zb hZ)

end BoundaryCollarPacket

end DifferentialGeometry.Geometry.Collapse
