import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryReplacementInterfaceBCF2K

/-!
# BCF02: the actual edge piece `P_e = M₂ ∩ X₂` is compact (lane BCF2-K, G5)

The compactness clause of the frozen `bcf02_pieces_BCF02` on lane BIFACE's interface (BIFACE G1'):
`IsCompact Kc.edgePiece`. Inputs, all from the interface or proved here:

* `M₂` closed (`M₂ = M₁ ∖ int_{M₁} S` with `M₁ = W ∖ int(Z ∪ C_∂)` closed);
* `M₂`'s original-coordinate consequences: `D ≥ 35` and the slim exclusion (lane BCF2-K G5a,
  `BoundaryCompactSlimChoice.M₂_original_consequences_BCF2K`), the zero exclusion from ZSP02's
  `BoundaryInitialCoresSpec.zero_cover` (`B(z, .38r_z) ⊆ int Z_k`);
* the vertical cut `{T ≤ 4Δ}` closed (`BoundaryGaf02Bases.heightRatio_continuous`);
* EDP02's (ELoc) `BoundaryGaf02Bases.edge_localization` and (ENTRY) `BoundaryGaf02Bases.edge_entry`;
* the E-free strict replacement (Repl_∂) at BCF02's EGP04 constants (`bcf02Sigma_BCF2K`,
  `bcf02Eta_BCF2K`, chosen ONCE from `LocalPacketsOnBFRZ.bcf02_original_replacement_BCF2K` and
  depending on `Δ` only; the register's later parameters `b`, `Lmax` must satisfy
  `σ(Δ)⁻¹ ≤ Lmax`, `b ≤ η(Δ)`, `3b ≤ σ(Δ)`).

The proof is the finite closed cover of `P_e ∩ W°` by the original domains
`{d(·, i) ≤ 6Δρ_i, |η_i| ≤ 4.01Δ, t_B ≤ 4.01Δ}` (`isClosed_of_finite_cover_BCF2K`), inside the
compact `{D ≥ 35} ⊆ W°` (`isCompact_le_distanceToBoundary_BDRY1`): closed in compact `W`, not
"a closed subset of an open base".

* `bcf02Sigma_BCF2K`, `bcf02Eta_BCF2K`, `bcf02_constants_spec_BCF2K`;
* `BoundaryCompactSlimChoice.isClosed_M₂_BCF2K`;
* `BoundaryCompactSlimChoice.zero_exclusion_of_mem_M₂_BCF2K` (premise hZ of (Repl_∂));
* `BoundaryCompactSlimChoice.isCompact_edgePiece_BCF2K`;
* consumer `BoundaryCompactSlimChoice.isCompact_pieces_BCF2K` (`M₂`, `P_e`, `R_c`, `P_e ∩ R_c`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis DifferentialGeometry.Topology

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

open Classical in
/-- **BCF02's EGP04 constant `σ(Δ)`** (chosen once, for `Δ ≥ 2`, from the E-free (Repl_∂)
`LocalPacketsOnBFRZ.bcf02_original_replacement_BCF2K`; `1` otherwise). -/
def bcf02Sigma_BCF2K (Δ : ℝ) : ℝ :=
  if h : 2 ≤ Δ then Classical.choose (LocalPacketsOnBFRZ.bcf02_original_replacement_BCF2K h)
  else 1

open Classical in
/-- **BCF02's EGP04 constant `η(Δ)`** (the raw quality bound, chosen with `bcf02Sigma_BCF2K`). -/
def bcf02Eta_BCF2K (Δ : ℝ) : ℝ :=
  if h : 2 ≤ Δ then
    Classical.choose (Classical.choose_spec
      (LocalPacketsOnBFRZ.bcf02_original_replacement_BCF2K h)).2.2
  else 1

/-- **The E-free (Repl_∂) at BCF02's constants**: `0 < σ(Δ) < 1`, `0 < η(Δ)`, and the statement of
`LocalPacketsOnBFRZ.bcf02_original_replacement_BCF2K` with `σ = σ(Δ)`, `η = η(Δ)`. -/
theorem bcf02_constants_spec_BCF2K {Δ : ℝ} (hΔ : 2 ≤ Δ) :
    0 < bcf02Sigma_BCF2K Δ ∧ bcf02Sigma_BCF2K Δ < 1 ∧ 0 < bcf02Eta_BCF2K Δ ∧
    ∀ (W : CompactCarrier.{0}) [ConnectedSpace W.Carrier]
      (g : SmoothRiemannianMetric W.model W.Carrier)
      (ĝ : SmoothRiemannianMetric (𝓡 3) (W.pieceInterior ⊤)),
      (∀ (x : W.pieceInterior ⊤) (v : TangentSpace (𝓡 3) x),
        (pieceInteriorMetric W g ⊤).inner x v v ≤ ĝ.inner x v v) →
    ∀ (ρ : W.Carrier → ℝ) (hρ : ∀ p, 0 < ρ p) {n : ℝ},
      (∀ p, 0 < distanceToBoundary W g p →
        n * (distanceToBoundary W g p).toReal / ((distanceToBoundary W g p).toReal + 3) <
          (distanceToBoundary W g p).toReal / ρ p) →
    ∀ {Λ : ℝ} {β : ℕ → ℝ} {σs : ℝ} {K : ℕ}
      {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz : ℝ},
      0 ≤ Λ → μ ≤ 1 / 10 ^ 8 → τ ≤ 1 / 10 ^ 8 → σc ≤ 1 / 1000 → 1140 * Δ ≤ 35 * n →
      1000 * Δ ≤ T → 0 ≤ σs → σs ≤ 1 / 100 → b < 1 / 1000000 → s < 1 / 1000000 →
      β 2 < 1 / 1000000 →
      (bcf02Sigma_BCF2K Δ)⁻¹ ≤ Lmax → b ≤ bcf02Eta_BCF2K Δ → 3 * b ≤ bcf02Sigma_BCF2K Δ →
      b * (2 * (20 * Δ + 1)) ≤ 1 → 1000000 * Δ * Λ < 1 / 100000 → μ * Δ < 1 / 10000 →
    ∀ (oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3),
    letI := inducedMetricSpace ĝ
    ∀ [CompleteSpace (W.pieceInterior ⊤)]
      (F : LocalPacketsOnBFRZ (W.pieceInterior ⊤) ĝ (inducedMetricSpace_hmetric ĝ)
        (fun x => ρ x) (fun x => hρ x) Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs
        ζ Λz {x | ENNReal.ofReal 10 < distanceToBoundary W g x}
        {x | ENNReal.ofReal 20 ≤ distanceToBoundary W g x}
        {x | ENNReal.ofReal 20 < distanceToBoundary W g x}
        {x | ENNReal.ofReal 35 ≤ distanceToBoundary W g x} oM),
      ∀ i : W.pieceInterior ⊤, i ∈ F.edgeB.centres →
      ∀ q : W.pieceInterior ⊤, dist q i < 100 * Δ * ρ i →
        |F.edgeB.coord_BAUGA i q| ≤ 401 / 100 * Δ →
        F.edgeB.smoothing q / ρ q ≤ 401 / 100 * Δ →
        ENNReal.ofReal 35 ≤ distanceToBoundary W g q →
        (letI := F.instMetricN; letI := F.instChartedN; letI := F.instMetricC
          ∀ z (hz : z ∈ F.zero.centres), 38 / 100 * (F.zero.zero z hz).radius ≤ dist q z) →
        (∀ k (hk : k ∈ F.slim.centres), dist q k < 9 * Δ * ρ k →
          10 * Δ ≤ |(F.slim.centre k hk).coord_BCG2 q|) →
        ∃ j ∈ F.edgeB.centres, q ∈ ball j (100 * Δ * ρ j) ∧
          |F.edgeB.coord_BAUGA j q| < 2 * Δ ∧ F.edgeB.cutoff_BAUGA j q = 1 := by
  have h := LocalPacketsOnBFRZ.bcf02_original_replacement_BCF2K hΔ
  have hs : bcf02Sigma_BCF2K Δ = Classical.choose h := by
    unfold bcf02Sigma_BCF2K
    rw [dite_eq_left hΔ]
  have he : bcf02Eta_BCF2K Δ = Classical.choose (Classical.choose_spec h).2.2 := by
    unfold bcf02Eta_BCF2K
    rw [dite_eq_left hΔ]
  rw [hs, he]
  obtain ⟨h1, h2, h3⟩ := Classical.choose_spec h
  exact ⟨h1, h2, (Classical.choose_spec h3).1, (Classical.choose_spec h3).2⟩

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}
  {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
    Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {D : BoundaryAugmentedData S Φ}
  {Kj : ℕ} {Ξ Sg eg c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  {C : BoundaryGaf02Chain D Kj Ξ Sg eg c cw bcut bder κ}
  {Bs : BoundaryGaf02Bases C} {ZC : BoundaryInitialCoresSpec C}

namespace BoundaryCompactSlimChoice

/-- **`M₂` is closed**: `M₁ = W ∖ int(Z ∪ C_∂)` is closed and `int_{M₁} S` is relatively open. -/
theorem isClosed_M₂_BCF2K (Kc : BoundaryCompactSlimChoice Bs ZC) : IsClosed Kc.M₂ := by
  have hM₁ : IsClosed ZC.M₁ := isOpen_interior.isClosed_compl
  obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp
    (isOpen_interior : IsOpen (interior (Subtype.val ⁻¹' Kc.piece : Set ZC.M₁)))
  have heq : Kc.M₂ = ZC.M₁ ∩ Oᶜ := by
    ext x
    constructor
    · rintro ⟨hx1, hx2⟩
      refine ⟨hx1, fun hxO => hx2 ⟨⟨x, hx1⟩, ?_, rfl⟩⟩
      rw [← hOeq]
      exact hxO
    · rintro ⟨hx1, hx2⟩
      refine ⟨hx1, ?_⟩
      rintro ⟨y, hy, hyx⟩
      rw [← hOeq] at hy
      apply hx2
      rw [← hyx]
      exact hy
  rw [heq]
  exact hM₁.inter hO.isClosed_compl

/-- **The zero exclusion on `M₂`** (premise hZ of (Repl_∂), from ZSP02's `zero_cover`): a point of
`W°` in `M₂` is outside every selected zero ball `B(z, .38r_z)`, since that ball lies in the
interior of a zero core, hence in `int(Z ∪ C_∂)`, removed from `M₁ ⊇ M₂`. -/
theorem zero_exclusion_of_mem_M₂_BCF2K (Kc : BoundaryCompactSlimChoice Bs ZC) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    ∀ q : W.pieceInterior ⊤, q.val ∈ Kc.M₂ →
      (letI := S.family.instMetricN; letI := S.family.instChartedN
        letI := S.family.instMetricC
        ∀ z (hz : z ∈ S.family.zero.centres),
          38 / 100 * (S.family.zero.zero z hz).radius ≤ dist q z) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  intro q hq z hz
  by_contra h
  push Not at h
  obtain ⟨k, -, hk⟩ := ZC.zero_cover z hz
  have hint := hk q h
  have hsub : ZC.core k ⊆ ZC.union ∪ C.cuspCores_BIF :=
    fun x hx => Or.inl (mem_iUnion.mpr ⟨k, hx⟩)
  exact hq.1 (interior_mono hsub hint)

/-- **BCF02: the actual edge piece `P_e = M₂ ∩ X₂` is compact** (the compactness clause of
`bcf02_pieces_BCF02`). Numerical premises: the step-one–three bounds on the supply's parameters and
BCF02's EGP04 tail requests `σ(Δ)⁻¹ ≤ Lmax`, `b ≤ η(Δ)`, `3b ≤ σ(Δ)`, `b(2(20Δ + 1)) ≤ 1`,
`10⁶ΔΛ < 10⁻⁵`, `μΔ < 10⁻⁴` (register clauses; `σ(Δ)`, `η(Δ)` depend on `Δ` only). -/
theorem isCompact_edgePiece_BCF2K (Kc : BoundaryCompactSlimChoice Bs ZC) (hΔ : 2 ≤ Δ)
    (hΛ : 0 ≤ Λ) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8) (hσc : σc ≤ 1 / 1000)
    (hn : 1140 * Δ ≤ 35 * (n : ℝ)) (hT : 1000 * Δ ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hb : b < 1 / 1000000) (hs : s < 1 / 1000000) (hβ2 : β 2 < 1 / 1000000)
    (hσL : (bcf02Sigma_BCF2K Δ)⁻¹ ≤ Lmax) (hbη : b ≤ bcf02Eta_BCF2K Δ)
    (h3b : 3 * b ≤ bcf02Sigma_BCF2K Δ) (hbH : b * (2 * (20 * Δ + 1)) ≤ 1)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hμΔ : μ * Δ < 1 / 10000) :
    IsCompact Kc.edgePiece := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  obtain ⟨-, -, -, hR⟩ := bcf02_constants_spec_BCF2K hΔ
  have hΔ0 : 0 < Δ := by linarith
  have hlam : 100 * Δ * Λ ≤ 1 / 10 ^ 8 := by nlinarith
  -- the BIFACE vocabulary in the family's terms
  have heta : ∀ j (hj : j ∈ S.family.edgeB.centres) (p : W.pieceInterior ⊤),
      S.edgeEta_BIF j p = S.family.edgeB.coord_BAUGA j p := by
    intro j hj p
    unfold BoundarySupplyCore.edgeEta_BIF
    rw [dite_eq_left hj, S.family.edgeB.coord_BAUGA_of_mem hj]
  have hht : ∀ p : W.pieceInterior ⊤,
      S.edgeHeightRaw p = S.family.edgeB.smoothing p / S.rho p := fun p => rfl
  -- the pieces on `W°`
  have hM : IsClosed (Subtype.val ⁻¹' Kc.M₂ : Set (W.pieceInterior ⊤)) :=
    Kc.isClosed_M₂_BCF2K.preimage continuous_subtype_val
  have hV : IsClosed (Subtype.val ⁻¹' {p | C.heightRatio p ≤ 4 * Δ} :
      Set (W.pieceInterior ⊤)) :=
    (isClosed_le Bs.heightRatio_continuous continuous_const).preimage continuous_subtype_val
  have hbase : ∀ x ∈ (Subtype.val ⁻¹' Kc.edgePiece : Set (W.pieceInterior ⊤)),
      x ∈ (Subtype.val ⁻¹' Kc.M₂ : Set (W.pieceInterior ⊤)) ∧
      x ∈ (Subtype.val ⁻¹' {p | C.heightRatio p ≤ 4 * Δ} : Set (W.pieceInterior ⊤)) ∧
      ∃ i ∈ S.family.edgeB.centres, x ∈ {p | dist p i ≤ 6 * Δ * S.rho i ∧
        |S.family.edgeB.coord_BAUGA i p| ≤ 401 / 100 * Δ ∧
        S.family.edgeB.smoothing p / S.rho p ≤ 401 / 100 * Δ} := by
    intro x hx
    obtain ⟨hxM, hxX⟩ := hx
    have hxX' := hxX
    rw [Bs.edge_source_eq] at hxX'
    obtain ⟨q, hqx, i, hi, hqi, hηi, hti⟩ := Bs.edge_localization x.val hxX
    have hqx' : q = x := Subtype.ext hqx
    subst hqx'
    have hic : i ∈ S.family.edgeB.centres := hi
    rw [heta i hic] at hηi
    rw [hht] at hti
    have henc := (S.family.toLocalPacketsOnB.edgeB_enclosure_BCF2K hΔ0 hμ hτ hlam hic
      (a := 401 / 100) (by norm_num) (by norm_num) (mem_ball.mpr hqi) hηi.le hti.le).2
      (by norm_num)
    exact ⟨hxM, hxX'.2, i, hic, henc.le, hηi.le, hti.le⟩
  have hre : ∀ x ∈ (Subtype.val ⁻¹' Kc.M₂ : Set (W.pieceInterior ⊤)),
      x ∈ (Subtype.val ⁻¹' {p | C.heightRatio p ≤ 4 * Δ} : Set (W.pieceInterior ⊤)) →
      ∀ i ∈ S.family.edgeB.centres, x ∈ {p | dist p i ≤ 6 * Δ * S.rho i ∧
        |S.family.edgeB.coord_BAUGA i p| ≤ 401 / 100 * Δ ∧
        S.family.edgeB.smoothing p / S.rho p ≤ 401 / 100 * Δ} →
      x ∈ (Subtype.val ⁻¹' Kc.edgePiece : Set (W.pieceInterior ⊤)) := by
    rintro x hxM hxV i hi ⟨hxi, hηi, hti⟩
    have hri := S.rho_pos i
    have hxi' : dist x i < 100 * Δ * S.rho i := by nlinarith
    obtain ⟨h35, hS⟩ := Kc.M₂_original_consequences_BCF2K hΔ0.le hσs x hxM
    have hZ := Kc.zero_exclusion_of_mem_M₂_BCF2K x hxM
    obtain ⟨j, hj, hxj, hηj, -⟩ := hR W g S.completion.metric S.completion.inner_le S.rho
      S.rho_pos S.scale_spec.2.2.2.2 hΛ hμ hτ hσc hn hT hσs hσs1 hb hs hβ2 hσL hbη h3b hbH hLΛ
      hμΔ oM S.family i hi x hxi' hηi hti h35 hZ hS
    refine ⟨hxM, Bs.edge_entry x j hj (mem_ball.mp hxj) ?_ ?_ hxV⟩
    · rw [heta j hj]
      linarith
    · rw [hht]
      linarith
  obtain ⟨-, hcl⟩ := isClosed_of_finite_cover_BCF2K S.family.edgeB.finite_centres hM hV
    (fun i hi => S.family.toLocalPacketsOnB.isClosed_edgeOriginalDomain_BCF2K hi _ _) hbase hre
  have hK := isCompact_le_distanceToBoundary_BDRY1 W g (by norm_num : (0 : ℝ) < 35)
  have hPc : IsCompact (Subtype.val ⁻¹' Kc.edgePiece : Set (W.pieceInterior ⊤)) :=
    hK.of_isClosed_subset hcl fun x hx => Kc.M₂_subset_D35_BCF2K hx.1
  have himg : Subtype.val '' (Subtype.val ⁻¹' Kc.edgePiece : Set (W.pieceInterior ⊤)) =
      Kc.edgePiece := by
    refine Subset.antisymm (image_preimage_subset _ _) fun p hp => ?_
    have h35 := Kc.M₂_subset_D35_BCF2K hp.1
    have hpos : 0 < distanceToBoundary W g p :=
      lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (by norm_num)) h35
    have hpi := mem_interior_of_distanceToBoundary_pos_BDRY1 W g hpos
    rw [← coe_pieceInterior_top_BDRY1 W] at hpi
    exact ⟨⟨p, hpi⟩, hp, rfl⟩
  rw [← himg]
  exact hPc.image continuous_subtype_val

/-- **The compact pieces of `M₂`** (consumer of `isCompact_edgePiece_BCF2K`): under the same
premises, `M₂`, the edge piece `P_e`, the circle remainder `R_c = M₂ ∖ int_{M₂} P_e` and
`P_e ∩ R_c` are compact. -/
theorem isCompact_pieces_BCF2K (Kc : BoundaryCompactSlimChoice Bs ZC) (hΔ : 2 ≤ Δ)
    (hΛ : 0 ≤ Λ) (hμ : μ ≤ 1 / 10 ^ 8) (hτ : τ ≤ 1 / 10 ^ 8) (hσc : σc ≤ 1 / 1000)
    (hn : 1140 * Δ ≤ 35 * (n : ℝ)) (hT : 1000 * Δ ≤ T) (hσs : 0 ≤ σs) (hσs1 : σs ≤ 1 / 100)
    (hb : b < 1 / 1000000) (hs : s < 1 / 1000000) (hβ2 : β 2 < 1 / 1000000)
    (hσL : (bcf02Sigma_BCF2K Δ)⁻¹ ≤ Lmax) (hbη : b ≤ bcf02Eta_BCF2K Δ)
    (h3b : 3 * b ≤ bcf02Sigma_BCF2K Δ) (hbH : b * (2 * (20 * Δ + 1)) ≤ 1)
    (hLΛ : 1000000 * Δ * Λ < 1 / 100000) (hμΔ : μ * Δ < 1 / 10000) :
    IsCompact Kc.M₂ ∧ IsCompact Kc.edgePiece ∧ IsCompact Kc.remainder ∧
      IsCompact (Kc.edgePiece ∩ Kc.remainder) := by
  have hM₂ : IsCompact Kc.M₂ := Kc.isClosed_M₂_BCF2K.isCompact
  have hP := Kc.isCompact_edgePiece_BCF2K hΔ hΛ hμ hτ hσc hn hT hσs hσs1 hb hs hβ2 hσL hbη h3b
    hbH hLΛ hμΔ
  -- `R_c = M₂ ∖ int_{M₂} P_e` is closed
  have hRc : IsClosed Kc.remainder := by
    obtain ⟨O, hO, hOeq⟩ := isOpen_induced_iff.mp
      (isOpen_interior : IsOpen (interior (Subtype.val ⁻¹' Kc.edgePiece : Set Kc.M₂)))
    have heq : Kc.remainder = Kc.M₂ ∩ Oᶜ := by
      ext x
      constructor
      · rintro ⟨hx1, hx2⟩
        refine ⟨hx1, fun hxO => hx2 ⟨⟨x, hx1⟩, ?_, rfl⟩⟩
        rw [← hOeq]
        exact hxO
      · rintro ⟨hx1, hx2⟩
        refine ⟨hx1, ?_⟩
        rintro ⟨y, hy, hyx⟩
        rw [← hOeq] at hy
        apply hx2
        rw [← hyx]
        exact hy
    rw [heq]
    exact Kc.isClosed_M₂_BCF2K.inter hO.isClosed_compl
  exact ⟨hM₂, hP, hRc.isCompact, hP.inter_right hRc⟩

end BoundaryCompactSlimChoice

end DifferentialGeometry.Geometry.Collapse
