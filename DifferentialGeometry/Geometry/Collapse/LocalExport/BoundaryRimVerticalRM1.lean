import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRimCornerSectionRM1

/-!
# BCF02 rim clauses, G2: `hV` and `hF` as derived theorems (lane S-RIM81)

External review 81 (b), D81-4: from the existing interface (`face_complete`, `local_single`,
`face_smooth` at the zeros, `transverse`, the open edge parent with its rank clauses, the
closedness of `M₂`) and WITHOUT any two-sided description of `M₂` across the rim:

* **`BoundaryGaf02ChainE.verticalFace_subset_remainder_RM1`** (`hV : V_e ⊆ R_c`): a point `p` of
  `V_e` off `∂M₂` is an interior point of `M₂` with `dT ≠ 0` (rank two against rank one), so `M₂`
  has points with `T > 4Δ` near `p`; a point of `V_e` on `∂M₂` carries an active label, and the
  corner section (`exists_corner_section_RM1`) gives interior points of `M₂` with `u > 0`,
  `T = 4Δ`, hence (moving up in `T`) interior points of `M₂` with `T > 4Δ`;
* **`BoundaryGaf02ChainE.remainder_inter_frontier_subset_RM1`** (`hF : R_c ∩ ∂M₂ ⊆
  ∂M₂ ∖ int_{∂M₂} H_e`): at a corner point, the segment `u ∈ [-σ, σ]` at height `T = 4Δ + ε`
  joins an interior point of `M₂` (`u = σ`) to a point off `M₂` (`u = -σ`), so it meets `∂M₂` at a
  point with `T > 4Δ`, i.e. outside `H_e`.

The target of `hF` keeps `∂M₂ ∖ int_{∂M₂} H_e` (not `H_e`'s relative frontier).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter Topology
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

/-- A continuous section over `V` at the base point `(a, b)`: a neighbourhood of `s (a, b)` contains
`s (a, b + ε)` for all small `ε`. -/
theorem eventually_section_mem_RM1 {X : Type*} [TopologicalSpace X] {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) {s : ℝ × ℝ → X} (hsc : ContinuousOn s V) {a b : ℝ} (hab : (a, b) ∈ V)
    {G : Set X} (hG : G ∈ 𝓝 (s (a, b))) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), (a, b + ε) ∈ V ∧ s (a, b + ε) ∈ G := by
  have hι : Tendsto (fun ε : ℝ => (a, b + ε)) (𝓝 0) (𝓝 (a, b)) := by
    have h := (continuous_const.prodMk (continuous_const.add continuous_id) :
      Continuous fun ε : ℝ => (a, b + ε)).tendsto 0
    simpa using h
  exact (hι.eventually (hV.mem_nhds hab)).and
    (((hsc.continuousAt (hV.mem_nhds hab)).tendsto.comp hι).eventually_mem hG)

/-- A preconnected set meeting `M` and its complement meets the frontier of `M`. -/
theorem inter_frontier_nonempty_of_isPreconnected_RM1 {X : Type*} [TopologicalSpace X]
    {S M : Set X} (hS : IsPreconnected S) (h1 : (S ∩ M).Nonempty) (h2 : (S \ M).Nonempty) :
    (S ∩ frontier M).Nonempty := by
  by_contra hne
  have hne' : ∀ x, x ∈ S → x ∉ frontier M := fun x hx hf => hne ⟨x, hx, hf⟩
  have hsub : S ⊆ interior M ∪ (closure M)ᶜ := by
    intro x hx
    by_cases hxM : x ∈ M
    · exact Or.inl (by_contra fun hi => hne' x hx ⟨subset_closure hxM, hi⟩)
    · refine Or.inr fun hc => hne' x hx ⟨hc, fun hi => hxM (interior_subset hi)⟩
  obtain ⟨x, hxS, hxi⟩ : (S ∩ interior M).Nonempty := by
    obtain ⟨x, hxS, hxM⟩ := h1
    rcases hsub hxS with hi | hc
    · exact ⟨x, hxS, hi⟩
    · exact absurd (subset_closure hxM) hc
  obtain ⟨y, hyS, hyc⟩ : (S ∩ (closure M)ᶜ).Nonempty := by
    obtain ⟨y, hyS, hyM⟩ := h2
    rcases hsub hyS with hi | hc
    · exact absurd (interior_subset hi) hyM
    · exact ⟨y, hyS, hc⟩
  obtain ⟨z, -, hzi, hzc⟩ := hS _ _ isOpen_interior isClosed_closure.isOpen_compl hsub
    ⟨x, hxS, hxi⟩ ⟨y, hyS, hyc⟩
  exact hzc (subset_closure (interior_subset hzi))

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

/-- **`hV` (review 81 (b), D81-4): `V_e ⊆ R_c`** from the interface alone. -/
theorem verticalFace_subset_remainder_RM1 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (er : BoundaryRelativeEdgeRestrictionV2 Kc) : Kc.verticalFace ⊆ Kc.remainder := by
  rintro p ⟨⟨hpM, hpX⟩, hpT⟩
  have hpT : C.toChain.heightRatio p = 4 * Δ := hpT
  refine ⟨hpM, fun hrel => ?_⟩
  obtain ⟨-, O, hOo, hpO, hOsub⟩ := mem_relInterior_iff_BCF.mp hrel
  have hpU : p ∈ Bs.edgeParent := Bs.source_one_subset_edgeParent_BIFc hpX
  -- a point of `O ∩ M₂` above the rim contradicts `O ∩ M₂ ⊆ P_e ⊆ X₂ ⊆ {T ≤ 4Δ}`
  have key : ∀ q, q ∈ O → q ∈ Kc.M₂ → 4 * Δ < C.toChain.heightRatio q → False := by
    intro q hqO hqM hqT
    have hqX : q ∈ Bs.source 1 := (hOsub ⟨hqO, hqM⟩).2
    rw [Bs.parent.edgeParent_cut] at hqX
    exact absurd hqX.2 (not_le.mpr hqT)
  have hint : W.model.IsInteriorPoint p :=
    (W.model.isInteriorPoint_iff_not_isBoundaryPoint p).mpr
      (not_isBoundaryPoint_of_mem_source_G6C WF hpX)
  by_cases hpF : p ∈ frontier Kc.M₂
  · -- corner: a labelled face passes through `p`
    obtain ⟨V, hV, hV0, s, hsc, hs1, hs2, -⟩ :=
      C.exists_corner_section_RM1 WF er ⟨hpF, hpX⟩ hpT (hOo.mem_nhds hpO)
    have hσ : ∀ᶠ σ in 𝓝[>] (0 : ℝ), (σ, 4 * Δ) ∈ V := by
      have hc : Tendsto (fun σ : ℝ => (σ, 4 * Δ)) (𝓝 0) (𝓝 ((0 : ℝ), 4 * Δ)) := by
        simpa using (continuous_id.prodMk continuous_const :
          Continuous fun σ : ℝ => (σ, 4 * Δ)).tendsto 0
      exact (hc.eventually (hV.mem_nhds hV0)).filter_mono nhdsWithin_le_nhds
    obtain ⟨σ, hσV, hσ0⟩ := (hσ.and
      (eventually_mem_nhdsWithin : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioi (0 : ℝ))).exists
    have hqpos : s (σ, 4 * Δ) ∈ interior Kc.M₂ := hs2 _ hσV le_rfl hσ0
    have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
        ((σ, 4 * Δ + ε) ∈ V ∧ s (σ, 4 * Δ + ε) ∈ interior Kc.M₂) ∧ ε ∈ Ioi (0 : ℝ) :=
      ((eventually_section_mem_RM1 hV hsc hσV (isOpen_interior.mem_nhds hqpos)).filter_mono
        nhdsWithin_le_nhds).and
        (eventually_mem_nhdsWithin : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioi (0 : ℝ))
    obtain ⟨ε, ⟨hεV, hεint⟩, hε0⟩ := hev.exists
    obtain ⟨hqO, -, hqT⟩ := hs1 _ hεV
    refine key _ hqO (interior_subset hεint) ?_
    rw [hqT]
    change 4 * Δ < 4 * Δ + ε
    exact lt_add_of_pos_right _ hε0
  · -- off `∂M₂`: an interior point with `dT ≠ 0`
    have hpint : p ∈ interior Kc.M₂ := by
      by_contra h
      exact hpF ⟨subset_closure hpM, h⟩
    have hTs : ContMDiffAt W.model 𝓘(ℝ, ℝ) 1 C.toChain.heightRatio p :=
      (C.heightRatio_contMDiff_BAUGD p).of_le (by simp)
    have hN : O ∩ interior Kc.M₂ ∈ 𝓝 p :=
      inter_mem (hOo.mem_nhds hpO) (isOpen_interior.mem_nhds hpint)
    obtain ⟨V, hV, hVp, s, hsc, hs⟩ := exists_section_of_ne_zero_mvfderiv_RM1 hint hTs
      (C.mvfderiv_heightRatio_ne_zero_G6C hpU hpT) hN
    rw [hpT] at hVp
    have hVev : ∀ᶠ y in 𝓝 (4 * Δ), y ∈ V := hV.mem_nhds hVp
    have hev : ∀ᶠ y in 𝓝[>] (4 * Δ), y ∈ V ∧ y ∈ Ioi (4 * Δ) :=
      (hVev.filter_mono nhdsWithin_le_nhds).and
        (eventually_mem_nhdsWithin : ∀ᶠ x in 𝓝[>] (4 * Δ), x ∈ Ioi (4 * Δ))
    obtain ⟨y, hyV, hy⟩ := hev.exists
    obtain ⟨⟨hqO, hqint⟩, hqt⟩ := hs y hyV
    refine key _ hqO (interior_subset hqint) ?_
    rw [hqt]
    exact hy

/-- **`hF` (review 81 (b), D81-4): `R_c ∩ ∂M₂ ⊆ ∂M₂ ∖ int_{∂M₂} H_e`** from the interface alone.
A point of `R_c ∩ ∂M₂` that is relatively interior to `H_e` would lie on the rim
(`P_e ∩ R_c ⊆ V_e`); the corner section then gives, at height `T = 4Δ + ε`, a segment from an
interior point of `M₂` to a point off `M₂`, which meets `∂M₂` above the rim, i.e. outside `H_e`. -/
theorem remainder_inter_frontier_subset_RM1 {Bs : BoundaryGaf02BasesV2 C.toChain}
    (WF : BoundaryWholeFiberSpecV2b C.toChain Bs) (Kc : BoundaryCompactSlimChoiceV2 Bs)
    (er : BoundaryRelativeEdgeRestrictionV2 Kc) :
    Kc.remainder ∩ frontier Kc.M₂ ⊆
      frontier Kc.M₂ \ relInterior_BIF (frontier Kc.M₂) Kc.horizontalFace := by
  rintro p ⟨hpR, hpF⟩
  refine ⟨hpF, fun hrel => ?_⟩
  obtain ⟨-, O, hOo, hpO, hOsub⟩ := mem_relInterior_iff_BCF.mp hrel
  have hpH : p ∈ Kc.horizontalFace := hOsub ⟨hpO, hpF⟩
  have hpM : p ∈ Kc.M₂ := Kc.isClosed_M₂_BCF.frontier_subset hpF
  have hpV : p ∈ Kc.verticalFace :=
    Kc.edgePiece_inter_remainder_subset_BC2 ⟨⟨hpM, hpH.2⟩, hpR⟩
  have hpT : C.toChain.heightRatio p = 4 * Δ := hpV.2
  obtain ⟨V, hV, hV0, s, hsc, hs1, hs2, hs3⟩ :=
    C.exists_corner_section_RM1 WF er hpH hpT (hOo.mem_nhds hpO)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV _ hV0
  have hσ : 0 < r / 2 := half_pos hr
  -- the points `(τ, 4Δ + ε)` with `|τ| ≤ r / 2`, `|ε| < r / 2` lie in `V`
  have hmem : ∀ τ ε : ℝ, |τ| ≤ r / 2 → |ε| < r / 2 → (τ, 4 * Δ + ε) ∈ V := by
    intro τ ε hτ hε
    refine hball ?_
    rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
    simp only [Real.dist_eq, sub_zero, add_sub_cancel_left]
    exact ⟨by linarith, by linarith⟩
  have h0 : ∀ τ : ℝ, |τ| ≤ r / 2 → (τ, 4 * Δ + 0) ∈ V := fun τ hτ => hmem τ 0 hτ (by simpa using hσ)
  have hVσ : (r / 2, 4 * Δ) ∈ V := by simpa using h0 (r / 2) (by rw [abs_of_pos hσ])
  have hVσ' : (-(r / 2), 4 * Δ) ∈ V := by
    simpa using h0 (-(r / 2)) (by rw [abs_neg, abs_of_pos hσ])
  have hin : s (r / 2, 4 * Δ) ∈ interior Kc.M₂ := hs2 _ hVσ le_rfl hσ
  have hneg : (-(r / 2), 4 * Δ).1 < 0 := neg_neg_of_pos hσ
  have hout : s (-(r / 2), 4 * Δ) ∉ Kc.M₂ := hs3 _ hVσ' le_rfl hneg
  have hev₁ := eventually_section_mem_RM1 hV hsc hVσ (isOpen_interior.mem_nhds hin)
  have hev₂ := eventually_section_mem_RM1 hV hsc hVσ'
    (Kc.isClosed_M₂_BCF.isOpen_compl.mem_nhds hout)
  have hev₃ : ∀ᶠ ε in 𝓝 (0 : ℝ), |ε| < r / 2 := by
    have := Metric.ball_mem_nhds (0 : ℝ) hσ
    filter_upwards [this] with ε hε
    simpa [Real.dist_eq] using hε
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (((r / 2, 4 * Δ + ε) ∈ V ∧ s (r / 2, 4 * Δ + ε) ∈ interior Kc.M₂) ∧
        ((-(r / 2), 4 * Δ + ε) ∈ V ∧ s (-(r / 2), 4 * Δ + ε) ∈ Kc.M₂ᶜ) ∧ |ε| < r / 2) ∧
        ε ∈ Ioi (0 : ℝ) :=
    ((hev₁.and (hev₂.and hev₃)).filter_mono nhdsWithin_le_nhds).and
      (eventually_mem_nhdsWithin : ∀ᶠ x in 𝓝[>] (0 : ℝ), x ∈ Ioi (0 : ℝ))
  obtain ⟨ε, ⟨⟨-, hint₁⟩, ⟨-, hout₂⟩, hε⟩, hε0⟩ := hev.exists
  have hε0' : 0 < ε := hε0
  have hγ : ContinuousOn (fun τ : ℝ => s (τ, 4 * Δ + ε)) (Icc (-(r / 2)) (r / 2)) := by
    refine hsc.comp (continuous_id.prodMk continuous_const).continuousOn fun τ hτ => ?_
    exact hmem τ ε (abs_le.mpr ⟨hτ.1, hτ.2⟩) hε
  have hS : IsPreconnected ((fun τ : ℝ => s (τ, 4 * Δ + ε)) '' Icc (-(r / 2)) (r / 2)) :=
    isPreconnected_Icc.image _ hγ
  have hne : (((fun τ : ℝ => s (τ, 4 * Δ + ε)) '' Icc (-(r / 2)) (r / 2)) ∩ Kc.M₂).Nonempty :=
    ⟨s (r / 2, 4 * Δ + ε), ⟨r / 2, ⟨by linarith, le_rfl⟩, rfl⟩, interior_subset hint₁⟩
  have hnt : (((fun τ : ℝ => s (τ, 4 * Δ + ε)) '' Icc (-(r / 2)) (r / 2)) \ Kc.M₂).Nonempty :=
    ⟨s (-(r / 2), 4 * Δ + ε), ⟨-(r / 2), ⟨le_rfl, by linarith⟩, rfl⟩, hout₂⟩
  obtain ⟨x, ⟨τ, hτ, rfl⟩, hxF⟩ := inter_frontier_nonempty_of_isPreconnected_RM1 hS hne hnt
  obtain ⟨hxO, -, hxT⟩ := hs1 (τ, 4 * Δ + ε) (hmem τ ε (abs_le.mpr ⟨hτ.1, hτ.2⟩) hε)
  have hxX : s (τ, 4 * Δ + ε) ∈ Bs.source 1 := (hOsub ⟨hxO, hxF⟩).2
  rw [Bs.parent.edgeParent_cut] at hxX
  have hle : C.toChain.heightRatio (s (τ, 4 * Δ + ε)) ≤ 4 * Δ := hxX.2
  rw [hxT] at hle
  change 4 * Δ + ε ≤ 4 * Δ at hle
  linarith

end BoundaryGaf02ChainE

end DifferentialGeometry.Geometry.Collapse
