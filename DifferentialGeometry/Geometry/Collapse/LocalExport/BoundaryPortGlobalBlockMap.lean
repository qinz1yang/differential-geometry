import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryAugmentedInteriorKernels

/-!
# CGP01 on the boundary family: the `…On` global block map (lane B-PORT-A, G1)

GENERATED from `Geometry/Fibration/ActualGlobalBlockMap.lean` (sections `GlobalMap`, `Wrapper`) by
`build-logs/scratch/B-PORT-A/gen_g1.py` (substitution table `portlib.FAMILY_TABLE`); do not edit by
hand, re-run the script.

The closed CGP01 layer `cgpGlobalMap L Z` (`L : LocalChartFamily` on a compact carrier) on the
enriched boundary base family `L : LocalPacketsOnB X …` (complete σ-compact carrier, regional
families) and a regional zero family `Z : ZeroModelFamilyOn …`, with the ACTIVE edge family
`L.edgeB` (never the inherited `L.edge`):

* substitution table: `[CompactSpace X]` ↦ `[CompleteSpace X] [SigmaCompactSpace X]`;
  `LocalChartFamily …` ↦ `LocalPacketsOnB … Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂`;
  `ZeroModelFamily …` ↦ `ZeroModelFamilyOn … U₁ U₂`; `L.edge` ↦ `L.edgeB`; `EdgeFamily.cutoff /
  coord / contMDiffOn_coord / cutoff_eq_formula / contMDiffAt_height_of_collar /
  contMDiff_cutoff_of_margin / mem_of_cutoff_ne_zero` ↦ the `…_BAUGA` copies on `EdgeFamilyOn`
  (BAUG-A); `SlimFamily.cutoff` ↦ `SlimFamilyOn.cutoff_BCNT`; `SlimCentre.coord /
  contMDiffOn_coord` ↦ `SlimCentreOn.coord_BCG2 / contMDiffOn_coord_BAUGA`; every declaration
  `x` of the ported sections ↦ `x_BAUGP`;
* reused unchanged (generic): `planeAxis`, `cgpEdgeH` and their lemmas, `lc87EdgeTransition`, the
  edge profiles (`Transition` section of the closed file);
* proof patches: slim cutoff smoothness = `SlimFamilyOn.contMDiff_cutoff_BCNT`; slim support
  margin = `SlimFamilyOn.tsupport_cutoff_subset_BCNT` (`0.91·10⁶Δρ(j) < 10⁶Δρ(j)`), in place of
  the closed `fc18_slim_row`; the wrapper `cgpGlobalMap'_BAUGP W = cgpGlobalMap_BAUGP W W.zero`.

The bridge to BAUG-A's interior formula (`S.interiorMapOn_BAUGA = cgpGlobalMap_BAUGP
S.family.toLocalPacketsOnB S.family.zero`) and the margin-free smoothness are in
`BoundaryPortGlobalBlockMapBridge.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

section GlobalMap

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ vs : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δ εr e T V : ℝ}

/-- The tags of `𝓔⁰`: circle, slim, edge and zero centres, and the two special tags
(`false` = `ρ`, `true` = `E'`). -/
abbrev CGPTag_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) : Type :=
  L.circle.finite_centres.toFinset ⊕ L.slim.finite_centres.toFinset ⊕
    L.edgeB.finite_centres.toFinset ⊕ Z.finite_centres.toFinset ⊕ Bool

/-- The normalized edge height `t = F/ρ` of the ONE shared smoothing. -/
def cgpHeight_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (x : X) : ℝ :=
  L.edgeB.smoothing x / ρ x

/-- The sum `Σ_{i ∈ I_e} ζ_i` of the actual edge cutoffs. -/
def cgpEdgeSum_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (x : X) : ℝ :=
  ∑ j : L.edgeB.finite_centres.toFinset, L.edgeB.cutoff_BAUGA j x

/-- The `E'` marker `z₀ = h(t/Δ) χ_{1/2,1}(Σ_{I_e} ζ_i)` of CGP01. -/
def cgpEdgeMarker_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (x : X) : ℝ :=
  cgpEdgeH (cgpHeight_BAUGP L x / Δ) * cfsRamp lc87EdgeTransition (1 / 2) 1 (cgpEdgeSum_BAUGP L x)

/-- The block radii `R_i`. -/
def cgpRadius_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) : CGPTag_BAUGP L Z → X → ℝ
  | .inl j => fun _ => ρ j
  | .inr (.inl j) => fun _ => ρ j
  | .inr (.inr (.inl j)) => fun _ => ρ j
  | .inr (.inr (.inr (.inl i))) => fun _ =>
      (Z.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius
  | .inr (.inr (.inr (.inr _))) => ρ

/-- The block cutoffs `ζ_i` (LC87's actual cutoffs, LC31's annular cutoffs, `1`, `z₀`). -/
def cgpCutoff_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) : CGPTag_BAUGP L Z → X → ℝ
  | .inl j => L.circle.cutoff j
  | .inr (.inl j) => L.slim.cutoff_BCNT j
  | .inr (.inr (.inl j)) => L.edgeB.cutoff_BAUGA j
  | .inr (.inr (.inr (.inl i))) => fun x =>
      Calculus.annularCutoff Calculus.cutoffProfile ((Z.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radial x)
  | .inr (.inr (.inr (.inr false))) => fun _ => 1
  | .inr (.inr (.inr (.inr true))) => cgpEdgeMarker_BAUGP L

/-- The block coordinates `η_i` (scalar coordinates on the axis of `ℝ²`). -/
def cgpCoord_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) : CGPTag_BAUGP L Z → X → ℝ²
  | .inl j =>
      let c := L.circle.chart j.1 ((Set.Finite.mem_toFinset _).mp j.2)
      letI := mX.rescale (ρ j.1)⁻¹ (inv_pos.mpr (hρ j.1))
      c.coord
  | .inr (.inl j) => fun x =>
      planeAxis ((L.slim.centre j.1 ((Set.Finite.mem_toFinset _).mp j.2)).coord_BCG2 x)
  | .inr (.inr (.inl j)) => fun x => planeAxis (L.edgeB.coord_BAUGA j x)
  | .inr (.inr (.inr (.inl i))) => fun x =>
      planeAxis ((Z.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radial x)
  | .inr (.inr (.inr (.inr false))) => fun _ => 0
  | .inr (.inr (.inr (.inr true))) => fun x => planeAxis (cgpHeight_BAUGP L x)

/-- **CGP01: the actual original global block map `𝓔⁰ = F`** (FC01's block map on the actual LC87
families and the LC80 zero family, with the source profiles). Defined ONCE on the pair
`(L, Z)`; `cgpGlobalMap'_BAUGP` is the same map on `LocalChartFamilyWithZero`. -/
def cgpGlobalMap_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) :
    X → BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²) :=
  blockMap (cgpRadius_BAUGP L Z) (cgpCutoff_BAUGP L Z) (cgpCoord_BAUGP L Z)

section Domains

variable (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
  (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂)

/-- The open collar region where the `E'` height is smooth. -/
def cgpEdgeDomain_BAUGP : Set X :=
  {x | ∃ j ∈ L.edgeB.centres, x ∈ ball j (100 * Δ * ρ j) ∧ |L.edgeB.coord_BAUGA j x| < 10 * Δ ∧
    Δ / 10 < cgpHeight_BAUGP L x ∧ cgpHeight_BAUGP L x < 10 * Δ}

/-- The open smooth domains `U_i` of the blocks. -/
def cgpDomain_BAUGP : CGPTag_BAUGP L Z → Set X
  | .inl j => ball j.1 (200 * ρ j.1)
  | .inr (.inl j) => ball j.1 (10 ^ 6 * Δ * ρ j.1)
  | .inr (.inr (.inl j)) => ball j.1 (100 * Δ * ρ j.1)
  | .inr (.inr (.inr (.inl i))) =>
      Classical.choose (Z.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radial_spec.2.1
  | .inr (.inr (.inr (.inr false))) => univ
  | .inr (.inr (.inr (.inr true))) => cgpEdgeDomain_BAUGP L

theorem continuous_cgpHeight_BAUGP : Continuous (cgpHeight_BAUGP L) :=
  L.edgeB.lipschitz_smoothing.continuous.div L.contMDiff_scale.continuous fun x => (hρ x).ne'

theorem isOpen_cgpEdgeDomain_BAUGP : IsOpen (cgpEdgeDomain_BAUGP L) := by
  have h : cgpEdgeDomain_BAUGP L = ⋃ j ∈ L.edgeB.centres, (ball j (100 * Δ * ρ j) ∩
      L.edgeB.coord_BAUGA j ⁻¹' Ioo (-(10 * Δ)) (10 * Δ)) ∩
      cgpHeight_BAUGP L ⁻¹' Ioo (Δ / 10) (10 * Δ) := by
    ext x
    simp only [cgpEdgeDomain_BAUGP, mem_ofPred_eq, mem_iUnion, mem_inter_iff, mem_preimage, mem_Ioo,
      abs_lt, exists_prop]
    constructor
    · rintro ⟨j, hj, hx, ⟨h1, h2⟩, h3, h4⟩
      exact ⟨j, hj, ⟨hx, h1, h2⟩, h3, h4⟩
    · rintro ⟨j, hj, ⟨hx, h1, h2⟩, h3, h4⟩
      exact ⟨j, hj, hx, ⟨h1, h2⟩, h3, h4⟩
  rw [h]
  refine isOpen_biUnion fun j hj => IsOpen.inter ?_ (isOpen_Ioo.preimage (continuous_cgpHeight_BAUGP L))
  exact (L.edgeB.contMDiffOn_coord_BAUGA hj).continuousOn.isOpen_inter_preimage isOpen_ball isOpen_Ioo

end Domains

section Pieces

variable (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
  (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂)

theorem continuous_cgpEdgeSum_BAUGP (hΔ : 0 < Δ)
    (hmargin : ∀ j ∈ L.edgeB.centres, tsupport (L.edgeB.cutoff_BAUGA j) ⊆ ball j (100 * Δ * ρ j)) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (cgpEdgeSum_BAUGP L) := by
  unfold cgpEdgeSum_BAUGP
  refine contMDiff_finsetSum fun j _ => ?_
  exact L.edgeB.contMDiff_cutoff_of_margin_BAUGA hΔ L.contMDiff_scale.continuous
    (hmargin j.1 ((Set.Finite.mem_toFinset _).mp j.2))

/-- Where the edge sum is at least `1/2`, some actual edge cutoff is nonzero. -/
theorem exists_edge_cutoff_ne_zero_of_half_le_BAUGP {x : X} (hx : 1 / 2 ≤ cgpEdgeSum_BAUGP L x) :
    ∃ j ∈ L.edgeB.centres, L.edgeB.cutoff_BAUGA j x ≠ 0 := by
  have hne : cgpEdgeSum_BAUGP L x ≠ 0 := by linarith
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
  exact ⟨j.1, (Set.Finite.mem_toFinset _).mp j.2, hj⟩

/-- A point with an active edge cutoff and height in `[Δ/5, 9Δ]` lies in the collar domain. -/
theorem mem_cgpEdgeDomain_of_BAUGP (hΔ : 0 < Δ) {j x : X} (hjx : L.edgeB.cutoff_BAUGA j x ≠ 0)
    (h1 : Δ / 5 ≤ cgpHeight_BAUGP L x) (h2 : cgpHeight_BAUGP L x ≤ 9 * Δ) : x ∈ cgpEdgeDomain_BAUGP L := by
  obtain ⟨hj, hball, hcoord, -⟩ := L.edgeB.mem_of_cutoff_ne_zero_BAUGA hΔ hjx
  have hrj := hρ j
  refine ⟨j, hj, ?_, by linarith, by linarith, by linarith⟩
  have h := (inv_mul_lt_iff₀ hrj).mp hball
  rw [mem_ball]
  linarith

/-- The `E'` marker `z₀` is smooth on all of `X` and its closed support lies in the collar
domain. -/
theorem contMDiff_cgpEdgeMarker_BAUGP (hΔ : 0 < Δ)
    (hmargin : ∀ j ∈ L.edgeB.centres, tsupport (L.edgeB.cutoff_BAUGA j) ⊆ ball j (100 * Δ * ρ j)) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (cgpEdgeMarker_BAUGP L) := by
  have hsum := continuous_cgpEdgeSum_BAUGP L hΔ hmargin
  have hht := continuous_cgpHeight_BAUGP L
  intro x
  by_cases hx : cgpEdgeSum_BAUGP L x < 1 / 2
  · have h0 : cgpEdgeMarker_BAUGP L =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hsum.continuous.continuousAt.eventually (gt_mem_nhds hx)] with y hy
      rw [cgpEdgeMarker_BAUGP, cfsRamp_eq_zero (fun y hy => lc87EdgeTransition_eq_zero hy)
        (by norm_num) hy.le, mul_zero]
    exact contMDiffAt_const.congr_of_eventuallyEq h0
  rw [not_lt] at hx
  obtain ⟨j, -, hjx⟩ := exists_edge_cutoff_ne_zero_of_half_le_BAUGP L hx
  have hcont : Continuous fun y => cgpHeight_BAUGP L y / Δ := hht.div_const Δ
  by_cases hlow : cgpHeight_BAUGP L x / Δ < 1 / 5
  · have h0 : cgpEdgeMarker_BAUGP L =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hcont.continuousAt.eventually (gt_mem_nhds hlow)] with y hy
      rw [cgpEdgeMarker_BAUGP, cgpEdgeH_eq_zero_of_le hy.le, zero_mul]
    exact contMDiffAt_const.congr_of_eventuallyEq h0
  by_cases hhigh : 9 < cgpHeight_BAUGP L x / Δ
  · have h0 : cgpEdgeMarker_BAUGP L =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hcont.continuousAt.eventually (lt_mem_nhds hhigh)] with y hy
      rw [cgpEdgeMarker_BAUGP, cgpEdgeH_eq_zero_of_ge hy.le, zero_mul]
    exact contMDiffAt_const.congr_of_eventuallyEq h0
  rw [not_lt] at hlow hhigh
  have h1 : Δ / 5 ≤ cgpHeight_BAUGP L x := by
    rw [le_div_iff₀ hΔ] at hlow
    linarith
  have h2 : cgpHeight_BAUGP L x ≤ 9 * Δ := by
    rw [div_le_iff₀ hΔ] at hhigh
    linarith
  obtain ⟨k, hk, hxk, hck, hk1, hk2⟩ := mem_cgpEdgeDomain_of_BAUGP L hΔ hjx h1 h2
  have hH : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (cgpHeight_BAUGP L) x :=
    L.edgeB.contMDiffAt_height_of_collar_BAUGA hk hxk hck.le hk1.le hk2.le
  have hA : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (fun y => cgpEdgeH (cgpHeight_BAUGP L y / Δ)) x :=
    (cgpEdgeH_contDiff.comp (contDiff_id.div_const Δ)).contMDiff.contMDiffAt.comp x hH
  have hB : ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞
      (fun y => cfsRamp lc87EdgeTransition (1 / 2) 1 (cgpEdgeSum_BAUGP L y)) x :=
    (contDiff_cfsRamp lc87EdgeTransition_contDiff _ _).contMDiff.contMDiffAt.comp x (hsum x)
  exact hA.mul hB

theorem tsupport_cgpEdgeMarker_subset_BAUGP (hΔ : 0 < Δ)
    (hmargin : ∀ j ∈ L.edgeB.centres, tsupport (L.edgeB.cutoff_BAUGA j) ⊆ ball j (100 * Δ * ρ j)) :
    tsupport (cgpEdgeMarker_BAUGP L) ⊆ cgpEdgeDomain_BAUGP L := by
  have hsum := (continuous_cgpEdgeSum_BAUGP L hΔ hmargin).continuous
  have hht := continuous_cgpHeight_BAUGP L
  let S : Set X := {x | Δ / 5 ≤ cgpHeight_BAUGP L x ∧ cgpHeight_BAUGP L x ≤ 9 * Δ ∧ 1 / 2 ≤ cgpEdgeSum_BAUGP L x}
  have hS : IsClosed S :=
    (isClosed_le continuous_const hht).inter ((isClosed_le hht continuous_const).inter
      (isClosed_le continuous_const hsum))
  have hsupp : Function.support (cgpEdgeMarker_BAUGP L) ⊆ S := by
    intro x hx
    have hx' : cgpEdgeMarker_BAUGP L x ≠ 0 := hx
    rw [cgpEdgeMarker_BAUGP] at hx'
    have hH : cgpEdgeH (cgpHeight_BAUGP L x / Δ) ≠ 0 := left_ne_zero_of_mul hx'
    have hR : cfsRamp lc87EdgeTransition (1 / 2) 1 (cgpEdgeSum_BAUGP L x) ≠ 0 :=
      right_ne_zero_of_mul hx'
    refine ⟨?_, ?_, ?_⟩
    · by_contra hlt
      apply hH
      refine cgpEdgeH_eq_zero_of_le ?_
      rw [div_le_iff₀ hΔ]
      linarith [not_le.mp hlt]
    · by_contra hlt
      apply hH
      refine cgpEdgeH_eq_zero_of_ge ?_
      rw [le_div_iff₀ hΔ]
      linarith [not_le.mp hlt]
    · by_contra hlt
      exact hR (cfsRamp_eq_zero (fun y hy => lc87EdgeTransition_eq_zero hy) (by norm_num)
        (not_le.mp hlt).le)
  intro x hx
  obtain ⟨h1, h2, h3⟩ := closure_minimal hsupp hS hx
  obtain ⟨j, -, hjx⟩ := exists_edge_cutoff_ne_zero_of_half_le_BAUGP L h3
  exact mem_cgpEdgeDomain_of_BAUGP L hΔ hjx h1 h2

end Pieces

/-- **CGP01, smoothness**: with LC87's packet-(iv) margin `hmargin` (closed edge supports inside the
OPEN chart balls) and the zero-shell tolerance `e ≤ 1/8`, the actual global block map is smooth;
every block's closed support lies in its open smooth domain (FC01's construction check). -/
theorem contMDiff_cgpGlobalMap_BAUGP
    (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (hΔ : 0 < Δ) (he : e ≤ 1 / 8)
    (hmargin : ∀ j ∈ L.edgeB.centres, tsupport (L.edgeB.cutoff_BAUGA j) ⊆ ball j (100 * Δ * ρ j)) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²)) ∞ (cgpGlobalMap_BAUGP L Z) := by
  have hplane : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ²) ∞ planeAxis := planeAxis.contMDiff
  refine contMDiff_blockMap (U := cgpDomain_BAUGP L Z) (fun i => ?_) (fun i => ?_) (fun i => ?_)
    (fun i => ?_) (fun i => ?_)
  · -- open domains
    rcases i with j | j | j | i | bb
    · exact isOpen_ball
    · exact isOpen_ball
    · exact isOpen_ball
    · exact (Classical.choose_spec
        (Z.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radial_spec.2.1).1
    · cases bb
      · exact isOpen_univ
      · exact isOpen_cgpEdgeDomain_BAUGP L
  · -- smooth coordinates
    rcases i with j | j | j | i | bb
    · have hj := (Set.Finite.mem_toFinset _).mp j.2
      have hc := L.circle.chart_center j.1 hj
      have hrj := hρ j.1
      let c := L.circle.chart j.1 hj
      let mR : MetricSpace X := mX.rescale (ρ j.1)⁻¹ (inv_pos.mpr (hρ j.1))
      have hc' : c.center = j.1 := hc
      change ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ²) ∞ c.coord (@ball X mX.toPseudoMetricSpace j.1
        (200 * ρ j.1))
      refine c.contMDiffOn_coord.mono fun x hx => ?_
      have hd := @inv_mul_dist_lt_of_mem_ball_LC87 X mX ρ j.1 x 200 hrj hx
      change (ρ j.1)⁻¹ * @dist X mX.toDist x c.center < 200
      rw [hc']
      exact hd
    · have hj := (Set.Finite.mem_toFinset _).mp j.2
      exact hplane.comp_contMDiffOn (L.slim.centre j.1 hj).contMDiffOn_coord_BAUGA
    · have hj := (Set.Finite.mem_toFinset _).mp j.2
      exact hplane.comp_contMDiffOn (L.edgeB.contMDiffOn_coord_BAUGA hj)
    · have hO := Classical.choose_spec
        (Z.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radial_spec.2.1
      exact hplane.comp_contMDiffOn hO.2.2
    · cases bb
      · exact contMDiffOn_const
      · refine hplane.comp_contMDiffOn fun x hx => ?_
        obtain ⟨k, hk, hxk, hck, h1, h2⟩ := hx
        exact (L.edgeB.contMDiffAt_height_of_collar_BAUGA hk hxk hck.le h1.le h2.le).contMDiffWithinAt
  · -- smooth cutoffs
    rcases i with j | j | j | i | bb
    · exact L.circle.contMDiff_cutoff j.1 ((Set.Finite.mem_toFinset _).mp j.2)
    · exact L.slim.contMDiff_cutoff_BCNT j.1
    · exact L.edgeB.contMDiff_cutoff_of_margin_BAUGA hΔ L.contMDiff_scale.continuous
        (hmargin j.1 ((Set.Finite.mem_toFinset _).mp j.2))
    · have hspec :=
        (Z.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radial_spec.2.2.2.2.2.2.2.2.2.2.2
      exact hspec.choose_spec.2.2.1
    · cases bb
      · exact contMDiff_const
      · exact contMDiff_cgpEdgeMarker_BAUGP L hΔ hmargin
  · -- smooth radii
    rcases i with j | j | j | i | bb
    · exact contMDiff_const
    · exact contMDiff_const
    · exact contMDiff_const
    · exact contMDiff_const
    · cases bb
      · exact L.contMDiff_scale
      · exact L.contMDiff_scale
  · -- closed supports inside the domains
    rcases i with j | j | j | i | bb
    · exact L.circle.tsupport_subset_ball j.1 ((Set.Finite.mem_toFinset _).mp j.2)
    · have hpos := mul_pos hΔ (hρ j.1)
      exact (L.slim.tsupport_cutoff_subset_BCNT j.1).trans (closedBall_subset_ball (by nlinarith))
    · exact hmargin j.1 ((Set.Finite.mem_toFinset _).mp j.2)
    · have hO := Classical.choose_spec
        (Z.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radial_spec.2.1
      have hspec :=
        (Z.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radial_spec.2.2.2.2.2.2.2.2.2.2.2
      have hts := hspec.choose_spec.2.2.2.2.2.1
      refine hts.trans (fun x hx => hO.2.1 ⟨?_, ?_⟩)
      · linarith [hx.1]
      · linarith [hx.2]
    · cases bb
      · exact subset_univ _
      · exact tsupport_cgpEdgeMarker_subset_BAUGP L hΔ hmargin

section Identities

variable (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
  (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂)

/-- The tag of the scale block. -/
abbrev cgpScaleTag_BAUGP : CGPTag_BAUGP L Z := .inr (.inr (.inr (.inr false)))

/-- The tag of the `E'` block. -/
abbrev cgpEdgeTag_BAUGP : CGPTag_BAUGP L Z := .inr (.inr (.inr (.inr true)))

/-- The tag of the edge block at `j`. -/
abbrev cgpEdgeBlockTag_BAUGP (j : L.edgeB.finite_centres.toFinset) : CGPTag_BAUGP L Z := .inr (.inr (.inl j))

theorem cgpGlobalMap_scale_BAUGP (p : X) : (cgpGlobalMap_BAUGP L Z p (cgpScaleTag_BAUGP L Z)).snd = ρ p := by
  change ρ p * 1 = ρ p
  rw [mul_one]

theorem cgpGlobalMap_edgeMarker_BAUGP (p : X) :
    (cgpGlobalMap_BAUGP L Z p (cgpEdgeTag_BAUGP L Z)).snd = ρ p * cgpEdgeMarker_BAUGP L p :=
  rfl

theorem cgpGlobalMap_edgeCoord_BAUGP (p : X) :
    (cgpGlobalMap_BAUGP L Z p (cgpEdgeTag_BAUGP L Z)).fst =
      (ρ p * cgpEdgeMarker_BAUGP L p) • planeAxis (cgpHeight_BAUGP L p) :=
  rfl

theorem cgpGlobalMap_edgeBlock_BAUGP (j : L.edgeB.finite_centres.toFinset) (p : X) :
    (cgpGlobalMap_BAUGP L Z p (cgpEdgeBlockTag_BAUGP L Z j)).fst =
        (ρ j * L.edgeB.cutoff_BAUGA j p) • planeAxis (L.edgeB.coord_BAUGA j p) ∧
      (cgpGlobalMap_BAUGP L Z p (cgpEdgeBlockTag_BAUGP L Z j)).snd = ρ j * L.edgeB.cutoff_BAUGA j p :=
  ⟨rfl, rfl⟩

theorem cgpHeight_nonneg_BAUGP (p : X) : 0 ≤ cgpHeight_BAUGP L p :=
  div_nonneg (L.edgeB.smoothing_nonneg p) (hρ p).le

theorem cgpEdgeCutoff_mem_Icc_BAUGP (hΔ : 0 < Δ) (j x : X) : L.edgeB.cutoff_BAUGA j x ∈ Icc (0 : ℝ) 1 := by
  by_cases h : L.edgeB.cutoff_BAUGA j x = 0
  · rw [h]
    exact ⟨le_rfl, zero_le_one⟩
  obtain ⟨hj, hball, -, -⟩ := L.edgeB.mem_of_cutoff_ne_zero_BAUGA hΔ h
  have hx : x ∈ ball j (100 * Δ * ρ j) := by
    have hh := (inv_mul_lt_iff₀ (hρ j)).mp hball
    rw [mem_ball]
    linarith
  rw [L.edgeB.cutoff_eq_formula_BAUGA hj hx]
  have h1 := intervalPlateauProfile_mem_Icc (-9) (-8) 8 9 (L.edgeB.coord_BAUGA j x / Δ)
  have h2 := descendingIntervalProfile_mem_Icc 8 9 (L.edgeB.smoothing x / ρ x / Δ)
  change intervalPlateauProfile (-9) (-8) 8 9 (L.edgeB.coord_BAUGA j x / Δ) *
    descendingIntervalProfile 8 9 (L.edgeB.smoothing x / ρ x / Δ) ∈ Icc (0 : ℝ) 1
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

theorem cgpEdgeMarker_mem_Icc_BAUGP (p : X) : cgpEdgeMarker_BAUGP L p ∈ Icc (0 : ℝ) 1 := by
  have h1 := cgpEdgeH_mem_Icc (cgpHeight_BAUGP L p / Δ)
  have h2 := cfsRamp_mem_Icc lc87EdgeTransition_mem_Icc (1 / 2) 1 (cgpEdgeSum_BAUGP L p)
  rw [cgpEdgeMarker_BAUGP]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- The `E'` block of `𝓔⁰` is `(ρ t z₀, ρ z₀)` with `‖x'‖ = ρ t z₀` (CFS23's block identity). -/
theorem norm_cgpGlobalMap_edgeCoord_BAUGP (p : X) :
    ‖(cgpGlobalMap_BAUGP L Z p (cgpEdgeTag_BAUGP L Z)).fst‖ = ρ p * cgpHeight_BAUGP L p * cgpEdgeMarker_BAUGP L p := by
  rw [cgpGlobalMap_edgeCoord_BAUGP, norm_smul, norm_planeAxis, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (hρ p).le (cgpEdgeMarker_mem_Icc_BAUGP L p).1),
    abs_of_nonneg (cgpHeight_nonneg_BAUGP L p)]
  ring

/-- **CFS23's joint edge identity on the original domain**: on the chart ball, where
`|η_j| < 8Δ`, the actual edge cutoff is `g(t/Δ) = 1 − χ_{8,9}(t/Δ)`. -/
theorem cgp01_edge_identity_BAUGP {j : X} (hj : j ∈ L.edgeB.centres) {p : X}
    (hp : p ∈ ball j (100 * Δ * ρ j)) (hη : |L.edgeB.coord_BAUGA j p| < 8 * Δ) (hΔ : 0 < Δ) :
    L.edgeB.cutoff_BAUGA j p = 1 - cfsRamp lc87EdgeTransition 8 9 (cgpHeight_BAUGP L p / Δ) := by
  rw [L.edgeB.cutoff_eq_formula_BAUGA hj hp, edgeCoordinateProfile_eq_one_sub_cfsRamp_abs,
    edgeHeightProfile_eq_one_sub_cfsRamp]
  have h0 : cfsRamp lc87EdgeTransition 8 9 |L.edgeB.coord_BAUGA j p / Δ| = 0 := by
    refine cfsRamp_eq_zero (fun y hy => lc87EdgeTransition_eq_zero hy) (by norm_num) ?_
    rw [abs_div, abs_of_pos hΔ, div_le_iff₀ hΔ]
    linarith
  rw [h0, sub_zero, one_mul]
  rfl

/-- Outside the chart ball the actual edge cutoff vanishes (CFS23's `ζ_i = 0` off `U_i`). -/
theorem edgeCutoff_eq_zero_of_not_mem_BAUGP (hΔ : 0 < Δ) {j p : X}
    (hp : p ∉ ball j (100 * Δ * ρ j)) : L.edgeB.cutoff_BAUGA j p = 0 := by
  by_contra h
  obtain ⟨-, hball, -, -⟩ := L.edgeB.mem_of_cutoff_ne_zero_BAUGA hΔ h
  apply hp
  have hh := (inv_mul_lt_iff₀ (hρ j)).mp hball
  rw [mem_ball]
  linarith

end Identities

/-- **CGP01** (`prop:fibration-source-profile-binding`) on the actual LC87 families and LC80 zero
family: the global block map `𝓔⁰ = cgpGlobalMap_BAUGP L Z` (FC01 with the source profiles) is smooth,
its scale block is `ρ`, its `E'` block is `(ρ t z₀, ρ z₀)` with `t = F/ρ ≥ 0` and
`z₀ = h(t/Δ) χ_{1/2,1}(Σ_{I_e} ζ_i) ∈ [0, 1]`, `h ∈ [0, 1]`, `h = 1 − χ_{8,9}` on `[3/10, ∞)`,
every edge block is `(R_j ζ_j η_j, R_j ζ_j)` with `ζ_j ∈ [0, 1]` zero off its chart ball, and on the
chart ball where `|η_j| < 8Δ` the joint identity `ζ_j = 1 − χ_{8,9}(t/Δ)` holds (`χ = χ_E`, the
increasing profile of CFS22). Input beyond the families: the edge zero-extension margin `hmargin`
(LC87 packet (iv)) and the zero-shell tolerance `e ≤ 1/8`. -/
theorem cgp01_row_BAUGP (L : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X g ρ hρ β N C o δ εr e T V U₁ U₂) (hΔ : 0 < Δ) (he : e ≤ 1 / 8)
    (hmargin : ∀ j ∈ L.edgeB.centres, tsupport (L.edgeB.cutoff_BAUGA j) ⊆ ball j (100 * Δ * ρ j)) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²)) ∞ (cgpGlobalMap_BAUGP L Z) ∧
      (∀ p, (cgpGlobalMap_BAUGP L Z p (cgpScaleTag_BAUGP L Z)).snd = ρ p) ∧
      (∀ p, ‖(cgpGlobalMap_BAUGP L Z p (cgpEdgeTag_BAUGP L Z)).fst‖ =
          ρ p * cgpHeight_BAUGP L p * cgpEdgeMarker_BAUGP L p ∧
        (cgpGlobalMap_BAUGP L Z p (cgpEdgeTag_BAUGP L Z)).snd = ρ p * cgpEdgeMarker_BAUGP L p) ∧
      (∀ p, 0 ≤ cgpHeight_BAUGP L p) ∧
      (∀ p, cgpEdgeMarker_BAUGP L p = cgpEdgeH (cgpHeight_BAUGP L p / Δ) *
        cfsRamp lc87EdgeTransition (1 / 2) 1
          (∑ j : L.edgeB.finite_centres.toFinset, L.edgeB.cutoff_BAUGA j p)) ∧
      (∀ u, cgpEdgeH u ∈ Icc (0 : ℝ) 1) ∧
      (∀ u, 3 / 10 ≤ u → cgpEdgeH u = 1 - cfsRamp lc87EdgeTransition 8 9 u) ∧
      (∀ (j : L.edgeB.finite_centres.toFinset) p,
        (cgpGlobalMap_BAUGP L Z p (cgpEdgeBlockTag_BAUGP L Z j)).fst =
            (ρ j * L.edgeB.cutoff_BAUGA j p) • planeAxis (L.edgeB.coord_BAUGA j p) ∧
          (cgpGlobalMap_BAUGP L Z p (cgpEdgeBlockTag_BAUGP L Z j)).snd = ρ j * L.edgeB.cutoff_BAUGA j p) ∧
      (∀ j p, L.edgeB.cutoff_BAUGA j p ∈ Icc (0 : ℝ) 1) ∧
      (∀ j p, p ∉ ball j (100 * Δ * ρ j) → L.edgeB.cutoff_BAUGA j p = 0) ∧
      (∀ j ∈ L.edgeB.centres, ∀ p ∈ ball j (100 * Δ * ρ j), |L.edgeB.coord_BAUGA j p| < 8 * Δ →
        L.edgeB.cutoff_BAUGA j p = 1 - cfsRamp lc87EdgeTransition 8 9 (cgpHeight_BAUGP L p / Δ)) :=
  ⟨contMDiff_cgpGlobalMap_BAUGP L Z hΔ he hmargin, cgpGlobalMap_scale_BAUGP L Z,
    fun p => ⟨norm_cgpGlobalMap_edgeCoord_BAUGP L Z p, cgpGlobalMap_edgeMarker_BAUGP L Z p⟩,
    cgpHeight_nonneg_BAUGP L, fun _ => rfl, cgpEdgeH_mem_Icc, fun _ hu => cgpEdgeH_eq_of_le hu,
    cgpGlobalMap_edgeBlock_BAUGP L Z, fun j p => cgpEdgeCutoff_mem_Icc_BAUGP L hΔ j p,
    fun _ _ hp => edgeCutoff_eq_zero_of_not_mem_BAUGP L hΔ hp,
    fun _ hj _ hp hη => cgp01_edge_identity_BAUGP L hj hp hη hΔ⟩

end GlobalMap

section Wrapper

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {g : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf g a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {Λ : ℝ} {β : ℕ → ℝ} {Δ σs : ℝ} {K : ℕ}
  {σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- The model metrics of the zero kind, as a named local instance. -/
local instance instMetricN_C14KA_BAUGP
    (W : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (a : X) : MetricSpace (W.N a) :=
  W.instMetricN a

/-- The model charts of the zero kind, as a named local instance. -/
local instance instChartedN_C14KA_BAUGP
    (W : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (a : X) : ChartedSpace E3 (W.N a) :=
  W.instChartedN a

/-- The cone metrics of the zero kind, as a named local instance. -/
local instance instMetricC_C14KA_BAUGP
    (W : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (a : X) : MetricSpace (W.C a) :=
  W.instMetricC a

/-- The SAME map `𝓔⁰` on `LocalChartFamilyWithZero` (through its two projections). -/
abbrev cgpGlobalMap'_BAUGP
    (W : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂) :
    X → BlockSpace (fun _ : CGPTag_BAUGP W W.zero => ℝ²) :=
  cgpGlobalMap_BAUGP W W.zero

/-- CGP01's smoothness on `LocalChartFamilyWithZero`. -/
theorem contMDiff_cgpGlobalMap'_BAUGP
    (W : LocalPacketsOnB X g hmetric ρ hρ Λ β Δ σs K σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs U₁ U₂ Ue₁ Ue₂)
    (hΔ : 0 < Δ) (he : e ≤ 1 / 8)
    (hmargin : ∀ j ∈ W.edgeB.centres, tsupport (W.edgeB.cutoff_BAUGA j) ⊆ ball j (100 * Δ * ρ j)) :
    ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag_BAUGP W W.zero => ℝ²)) ∞
      (cgpGlobalMap'_BAUGP W) :=
  contMDiff_cgpGlobalMap_BAUGP W W.zero hΔ he hmargin

end Wrapper

end DifferentialGeometry.Geometry.Collapse
