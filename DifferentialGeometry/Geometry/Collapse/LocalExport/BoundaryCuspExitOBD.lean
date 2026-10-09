import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoresCollarHCOL

/-!
# BD0 for the rows link: the cusp rows with `cuspFn = u_b − 40 v_b` (lane O-BD1, draft 74 BD2)

`BoundaryRowsLink.cusp` (text v3.1 §R) asks the rows' cusp defining function to BE `u_b − 40 v_b`
on the rows' `near`. BD0 (`cuspFnData_BGR`) uses `G_b − 40` on `{39 < G_b < 41}`, where `G_b` is
BCG6-K's modified level; the two agree where the strip cutoff is `1` and the marker is `1`. So the
`near` is shrunk to `N_b = W° ∩ strip ∩ {79/2 < η_b < 81/2} ∩ int {v_b = 1}`: there `G_b = u_b`
(`coreLevel_eq_on_strip_BCG6K`, `coreCutoff_eq_one_BCG6K`), `v_b = 1`, and every front point lies
in `N_b` (E4b: `front_localization`, `marker_eq_one_near_front`, `mem_strip_of_mem_front_BCG6K`):

* `cuspFnLink_OBD`: `N_b` open in `W°`, `u_b − 40 v_b` smooth on `N_b`, regular at its zeros
  (E4b `defining_differential_ne_zero`), front `= {N_b ∧ u_b − 40 v_b = 0}`, core `∩ N_b =
  {N_b ∧ u_b − 40 v_b ≤ 0}`;
* **`exists_cuspExit_OBD`**: boundary tori `Et` (labels: the packet's components; collars from the
  half-collar kernel, lane S-COLLAR) and `CuspCores W Et` built from the SAME E4c product, with the
  link of the rows: ranges = cores, internal ends = fronts, `cuspFn = u_b − 40 v_b` on `near`.
Premises of E4b only.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology GC.GraphManifold
  GC.GraphManifold.Assembly GC.GraphManifold.Assembly.FC39P0
open DifferentialGeometry.Topology.HalfCollarHCOL

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ W g
    δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ cadj : ℝ}

namespace BoundaryGaf02ChainE

variable (C : BoundaryGaf02ChainE DP Kj Ξ c cw bcut bder κ cadj)

/-- **The cusp defining function of the rows link**: on the shrunk open `N_b ⊆ W°` the function
`u_b − 40 v_b` is smooth, regular at its zeros, its zero set is the front and its sublevel is the
core. Premises of E4b. -/
theorem cuspFnLink_OBD {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) (i : Fin S.packet.cusp.count) :
    ∃ near : TopologicalSpace.Opens W.Carrier,
      (near : Set W.Carrier) ⊆ W.interior ∧
      ContMDiffOn W.model 𝓘(ℝ, ℝ) ∞ (fun x => chainBoundaryU_BCG6K C.toChain.E i x -
        40 * chainBoundaryV_BCG6K C.toChain.E i x) near ∧
      (∀ x ∈ near, chainBoundaryU_BCG6K C.toChain.E i x -
          40 * chainBoundaryV_BCG6K C.toChain.E i x = 0 →
        mfderiv W.model 𝓘(ℝ, ℝ) (fun x => chainBoundaryU_BCG6K C.toChain.E i x -
          40 * chainBoundaryV_BCG6K C.toChain.E i x) x ≠ 0) ∧
      C.toChain.cuspFront_BIF i = {x | x ∈ near ∧ chainBoundaryU_BCG6K C.toChain.E i x -
        40 * chainBoundaryV_BCG6K C.toChain.E i x = 0} ∧
      C.toChain.cuspCore_BIF i ∩ near = {x | x ∈ near ∧ chainBoundaryU_BCG6K C.toChain.E i x -
        40 * chainBoundaryV_BCG6K C.toChain.E i x ≤ 0} := by
  have hεd := epsBoundary_lt_BGR hrd hrdc
  have hBI := (C.bcg04_row_BGR hrd hprem).2.1 3
  have hBFM := (C.bcg05_row_BGR hθ hrd hrd4 hprem).1 3
  have hspec := C.bcg06_coreSpec_on_chain_BGR hrd hrd4 hrdc hprem hθ
  let P := S.packet.toBoundaryCollarPacket
  let u := chainBoundaryU_BCG6K C.toChain.E
  let v := chainBoundaryV_BCG6K C.toChain.E
  have hu : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ (u i) :=
    contMDiff_chainBoundaryU_BCG6K (C.stage_smooth_BAUGD 3) i
  have hη : Continuous (P.height i) := (P.contMDiff_height i).continuous
  have hcore : C.toChain.cuspCore_BIF i = {x | P.coreLevel_BCG6K i (u i) x ≤ 40} :=
    P.cuspCore_eq_BCG6K hεd (hBI i) (hBFM i)
  let N : Set W.Carrier := (W.interior : Set W.Carrier) ∩ (P.coreStrip_BCG6K i ∩
    ({x | 79 / 2 < P.height i x} ∩ {x | P.height i x < 81 / 2})) ∩ interior {x | v i x = 1}
  have hNo : IsOpen N := (W.interior.isOpen.inter ((P.isOpen_coreStrip_BCG6K i).inter
    ((isOpen_lt continuous_const hη).inter (isOpen_lt hη continuous_const)))).inter isOpen_interior
  have hNv : ∀ x ∈ N, v i x = 1 := fun x hx => by
    have h : x ∈ {x | v i x = 1} := interior_subset hx.2
    exact h
  have hNG : ∀ x ∈ N, P.coreLevel_BCG6K i (u i) x = u i x := fun x hx => by
    rw [P.coreLevel_eq_on_strip_BCG6K i (u i) hx.1.2.1,
      coreCutoff_eq_one_BCG6K hx.1.2.2.1.le hx.1.2.2.2.le]
    ring
  have hfN : ∀ x ∈ C.toChain.cuspFront_BIF i, x ∈ N := fun x hx => by
    have hint := (P.mem_strip_of_mem_front_BCG6K hεd (hBI i) hx).2
    have hstrip := (P.mem_strip_of_mem_front_BCG6K hεd (hBI i) hx).1
    have hloc := (hspec.front_localization i x hx).2
    have hv := hspec.marker_eq_one_near_front i x hx
    refine ⟨⟨(mem_pieceInterior_of_isInteriorPoint_BCG6K hint).2, hstrip, ?_, ?_⟩,
      mem_interior_iff_mem_nhds.mpr hv⟩
    · have := (abs_lt.mp hloc).1
      change 79 / 2 < P.height i x
      linarith
    · have := (abs_lt.mp hloc).2
      change P.height i x < 81 / 2
      linarith
  have hfront_def : ∀ x, x ∈ C.toChain.cuspFront_BIF i ↔ (9 / 10 : ℝ) ≤ v i x ∧
      u i x = 40 * v i x := fun x => Iff.rfl
  refine ⟨⟨N, hNo⟩, fun x hx => hx.1.1, ?_, ?_, ?_, ?_⟩
  · exact (hu.sub (contMDiff_const.mul contMDiff_const)).contMDiffOn.congr fun x hx => by
      change u i x - 40 * v i x = u i x - 40 * 1
      rw [hNv x hx]
  · intro x hx hx0
    have hx0' : u i x - 40 * v i x = 0 := hx0
    have hxF : x ∈ C.toChain.cuspFront_BIF i := by
      rw [hfront_def, hNv x hx]
      rw [hNv x hx] at hx0'
      exact ⟨by norm_num, by linarith⟩
    exact hspec.defining_differential_ne_zero i x hxF
  · ext x
    constructor
    · intro hx
      refine ⟨hfN x hx, ?_⟩
      have h := (hfront_def x).mp hx
      change u i x - 40 * v i x = 0
      linarith [h.2]
    · rintro ⟨hxN, hx0⟩
      rw [hfront_def, hNv x hxN]
      change u i x - 40 * v i x = 0 at hx0
      rw [hNv x hxN] at hx0
      exact ⟨by norm_num, by linarith⟩
  · ext x
    constructor
    · rintro ⟨hxC, hxN⟩
      refine ⟨hxN, ?_⟩
      have hG : P.coreLevel_BCG6K i (u i) x ≤ 40 := by
        rw [hcore] at hxC
        exact hxC
      change u i x - 40 * v i x ≤ 0
      rw [hNv x hxN, ← hNG x hxN]
      linarith
    · rintro ⟨hxN, hx0⟩
      refine ⟨?_, hxN⟩
      rw [hcore]
      change P.coreLevel_BCG6K i (u i) x ≤ 40
      change u i x - 40 * v i x ≤ 0 at hx0
      rw [hNv x hxN] at hx0
      rw [hNG x hxN]
      linarith

/-- **The cusp rows of the boundary landing, linked** (BD0 for `BoundaryRowsLink.cusp`): boundary
tori `Et` whose torus maps are the packet's components, and `CuspCores W Et` from the SAME E4c
product (half-collar ports, lane S-COLLAR) with ranges = cores, internal ends = fronts and
`cuspFn = u_b − 40 v_b` on `near`. Premises of E4b. -/
theorem exists_cuspExit_OBD {rd : ℝ} (hrd : 0 < rd) (hrd4 : rd < 1 / 10000)
    (hrdc : 20 * (c 2 + 1) * rd < 1 / 1000000)
    (hprem : 1000 * δn ^ 2 < w / (2 * (1 + 2 * Λ⁻¹) ^ 3) * min (1 / 2) (rd / 4) ^ 2)
    (hθ : θ < 1 / 100) :
    ∃ (Et : BoundaryTori W S.packet.cusp.count) (cc : CuspCores W Et),
      (∀ i, range (Et.torusMap i) = S.packet.cusp.component i) ∧
      ∀ i, range (cc.piece i).map = C.toChain.cuspCore_BIF i ∧
        (range fun t => (cc.piece i).map (cc.product i (t, iccEnd true))) =
          C.toChain.cuspFront_BIF i ∧
        ∀ x ∈ cc.near i, cc.cuspFn i x =
          chainBoundaryU_BCG6K C.toChain.E i x - 40 * chainBoundaryV_BCG6K C.toChain.E i x := by
  have hE := C.bcg06_labelled_product_embedding_on_chain_OCX hrd hrd4 hrdc hprem hθ
  have hpt := fun i => C.cuspPieceEmb_of_same_product_HCOL hrd hrd4 hrdc hprem hθ i (hE i)
  choose piece product hrange hend0 hend1 hemb hfaces using hpt
  choose F0 F1 hF1 hF0 hFall using hfaces
  have hfn := fun i => C.cuspFnLink_OBD hrd hrd4 hrdc hprem hθ i
  choose near hnear hsm hreg hfront hcore using hfn
  have hspec := C.bcg06_coreSpec_on_chain_BGR hrd hrd4 hrdc hprem hθ
  have hdisj : Pairwise fun i j => Disjoint (range (piece i).map) (range (piece j).map) :=
    fun i j hij => by
      change Disjoint (range (piece i).map) (range (piece j).map)
      rw [hrange, hrange]
      exact hspec.pairwise_disjoint i j hij
  have hbd : ∀ i t, W.model.IsBoundaryPoint ((piece i).map (product i (t, iccEnd false))) := by
    intro i t
    have hmem : (piece i).map (product i (t, iccEnd false)) ∈ S.packet.cusp.component i := by
      rw [← hend0 i]
      exact ⟨t, rfl⟩
    have hb : (piece i).map (product i (t, iccEnd false)) ∈ W.model.boundary W.Carrier := by
      rw [← S.packet.cusp.covers]
      exact mem_iUnion.mpr ⟨i, hmem⟩
    exact hb
  obtain ⟨Et, hext, hown, hclos⟩ := boundaryTori_of_pieces_HCOL W piece product hemb hbd hdisj
  refine ⟨Et, { ports := ?_
                piece := piece
                product := product
                external_end := hext
                collar_owned := hown
                collar_closure_off := hclos
                disjoint := hdisj
                cuspFn := fun i x => chainBoundaryU_BCG6K C.toChain.E i x -
                  40 * chainBoundaryV_BCG6K C.toChain.E i x
                near := near
                near_interior := hnear
                fn_smooth := hsm
                fn_regular := hreg
                internal_eq := fun i => by rw [hend1 i]; exact hfront i
                near_eq := fun i => by rw [hrange i]; exact hcore i
                internalModelFace := F1
                internalModelFace_eq := hF1
                externalModelFace := F0
                externalModelFace_eq := hF0
                modelFace_cases := hFall }, ?_, fun i => ⟨hrange i, hend1 i, fun _ _ => rfl⟩⟩
  · rw [← S.packet.cusp.covers]
    ext x
    simp only [BoundaryTori.image, mem_iUnion]
    constructor
    · rintro ⟨i, hx⟩
      rw [← hend0 i] at hx
      obtain ⟨t, rfl⟩ := hx
      exact ⟨i, t, (hext i t).symm⟩
    · rintro ⟨i, t, ht⟩
      refine ⟨i, ?_⟩
      rw [← hend0 i, ← ht]
      exact ⟨t, hext i t⟩
  · intro i
    rw [← hend0 i]
    ext x
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨t, hext i t⟩
    · rintro ⟨t, rfl⟩
      exact ⟨t, (hext i t).symm⟩

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
