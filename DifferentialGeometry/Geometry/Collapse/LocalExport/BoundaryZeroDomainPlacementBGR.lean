import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroDomainTransportBGR

/-!
# BCG07 F3, step Z6: placement of the actual zero domains of the boundary chain (lane B-BCG-ROWS)

Blueprint `master207B.tex`, ZSP02 (ZB) (B:6374–6479) and BCG07 (B:9518–9524): the actual zero
domain `Z_k` of `C.E` lies in the original zero ball, contains a smaller ball in its interior, is
compact, and distinct domains are disjoint. These clauses of the closed `zsp02_kernel_ZSP35` do NOT
use the derivative input; they are re-proved here on the boundary family (the generated kernel
port omits `zsp02_kernel_ZSP35`, whose diffeomorphism part needs a compact boundaryless carrier).

* generic on `(X, LocalPacketsOnB, ZeroModelFamilyOn)`: `zspDomain_subset_ball_BGR`
  (`Z_k ⊆ B(c_k, (.402 + e)R_k)`), `closedBall_subset_interior_zspDomain_BGR`
  (`B̄(c_k, (.381 − e)R_k) ⊆ int Z_k`), `isClosed_zspDomain_BGR`;
* on chains over the ACTUAL slot v2 (BIFACEc's fields of `BoundaryActualZeroDomains_BIFc`):
  **`actualZeroDomain_subset_ball_BGR`** (`domain_subset_ball`, original `g`-ball of radius `R_k`),
  **`actualZeroDomain_cover_BGR`** (`zero_cover` verbatim at `.38R_k`, with the register's
  `e ≤ 1/1000` — lead decision N76-6, the hypothesis of the closed `zsp02_ZB_ZSP35`),
  **`isCompact_actualZeroDomain_BGR`**
  (`isCompact_domain`), **`actualZeroDomain_pairwise_disjoint_BGR`** (`pairwise_disjoint`).
-/

set_option autoImplicit false

noncomputable section

open Set Function Metric Bundle Manifold Filter
open scoped ContDiff Manifold Topology ENNReal
open DifferentialGeometry.Topology.Ehresmann DifferentialGeometry.Topology.Manifold
open DifferentialGeometry.Geometry.Riemannian GC.MetricGeometry
open DifferentialGeometry GC.Endpoint DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Analysis

namespace DifferentialGeometry.Geometry.Collapse

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "ℝ²" => EuclideanSpace ℝ (Fin 2)

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

attribute [local instance] nezero_finrank_euclideanThree_LC87

section Generic

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {gX : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf gX a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {ΛX : ℝ} {βX : ℕ → ℝ} {ΔX σsX : ℝ} {KX : ℕ}
  {σcX μX bX sX b'X s'X εX γcX βcX : ℝ}
  {N C : X → Type} [∀ a, MetricSpace (N a)] [∀ a, ChartedSpace E3 (N a)]
  [∀ a, MetricSpace (C a)] {o : ∀ a, C a} {δX εrX eX TX VX : ℝ}
  {LmaxX τX γX vsX : ℝ} {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- **ZSP02 (ZB), outer half, on the boundary family**: with (ZE) (`δ₀ < 1/1000`) and `e < 1/40`,
`Z_k ⊆ B(c_k, (.402 + e)R_k)`. -/
theorem zspDomain_subset_ball_BGR
    (L : LocalPacketsOnB X gX hmetric ρ hρ ΛX βX ΔX σsX KX σcX μX bX sX b'X s'X εX γcX βcX LmaxX τX
      γX δX εrX eX TX VX vsX U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X gX ρ hρ βX N C o δX εrX eX TX VX U₁ U₂)
    (k : Z.finite_centres.toFinset) (f : X → BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²))
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1 / 1000)
    (hZE : ∀ p, ‖f p (.inr (.inr (.inr (.inl k)))) -
        cgpGlobalMap_BAUGP L Z p (.inr (.inr (.inr (.inl k))))‖ <
      δ₀ * (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius) :
    zspDomain_ZSP35_BGR L Z k f ⊆ ball (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center
      ((402 / 1000 + eX) * (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius) := by
  have hR := (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  obtain ⟨-, hcl, -⟩ := zsp_radial_facts_ZSP35_BGR Z k
  have he0 : 0 < eX := lt_of_le_of_lt (abs_nonneg _) (hcl (Z.zero k.1
    ((Set.Finite.mem_toFinset _).mp k.2)).center)
  have hrad := zsp02_original_radial_BGR L Z k f hδ₀ hZE
  have h45 : (4 / 10 : ℝ) = 2 / 5 := by norm_num
  rintro z (hz | ⟨hv, hu⟩)
  · refine ball_subset_ball ?_ hz
    nlinarith
  · have hη := (hrad z hv).2.1 (by rw [h45]; exact hu)
    have hd := abs_lt.mp (hcl z)
    rw [mem_ball]
    have h3 : ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ *
        dist z (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center < 402 / 1000 + eX := by
      linarith
    rw [inv_mul_lt_iff₀ hR] at h3
    linarith

/-- **ZSP02 (ZB), inner half, on the boundary family**: with (ZE) (`δ₀ < 1/1000`),
`B̄(c_k, (.381 − e)R_k) ⊆ int Z_k`. -/
theorem closedBall_subset_interior_zspDomain_BGR
    (L : LocalPacketsOnB X gX hmetric ρ hρ ΛX βX ΔX σsX KX σcX μX bX sX b'X s'X εX γcX βcX LmaxX τX
      γX δX εrX eX TX VX vsX U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X gX ρ hρ βX N C o δX εrX eX TX VX U₁ U₂)
    (k : Z.finite_centres.toFinset) (f : X → BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²))
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1 / 1000)
    (hZE : ∀ p, ‖f p (.inr (.inr (.inr (.inl k)))) -
        cgpGlobalMap_BAUGP L Z p (.inr (.inr (.inr (.inl k))))‖ <
      δ₀ * (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius) :
    closedBall (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center
        ((381 / 1000 - eX) * (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius) ⊆
      interior (zspDomain_ZSP35_BGR L Z k f) := by
  have hR := (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  obtain ⟨hηc, hcl, -⟩ := zsp_radial_facts_ZSP35_BGR Z k
  have hann := zsp02_original_annulus_BGR L Z k f hδ₀ hZE
  have h45 : (4 / 10 : ℝ) = 2 / 5 := by norm_num
  have hUo : IsOpen (ball (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center
      (35 / 100 * (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius) ∪
      {z | 3 / 10 < (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z ∧
        (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radial z < 381 / 1000}) :=
    isOpen_ball.union ((isOpen_lt continuous_const hηc).inter (isOpen_lt hηc continuous_const))
  refine Subset.trans ?_ (interior_maximal ?_ hUo)
  · intro z hz
    rw [mem_closedBall] at hz
    by_cases hb : dist z (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center <
        35 / 100 * (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius
    · exact Or.inl hb
    · push Not at hb
      have hd := abs_lt.mp (hcl z)
      have h1 : 35 / 100 ≤ ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ *
          dist z (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center := by
        rw [le_inv_mul_iff₀ hR]
        linarith
      have h2 : ((Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)⁻¹ *
          dist z (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center ≤ 381 / 1000 - eX := by
        rw [inv_mul_le_iff₀ hR]
        linarith
      exact Or.inr ⟨by linarith, by linarith⟩
  · rintro z (hz | ⟨h1, h2⟩)
    · exact Or.inl hz
    · obtain ⟨-, hv, hu⟩ := hann z h1.le h2
      rw [h45] at hu
      exact Or.inr ⟨by linarith, hu.le⟩

/-- **`Z_k` is closed** (the sublevel `{h₁ ≤ .4}` of the continuous (ZH) end `h₁`, ZSP02's sublevel
identity; `f` smooth, (ZE), `e < 1/40`). -/
theorem isClosed_zspDomain_BGR
    (L : LocalPacketsOnB X gX hmetric ρ hρ ΛX βX ΔX σsX KX σcX μX bX sX b'X s'X εX γcX βcX LmaxX τX
      γX δX εrX eX TX VX vsX U₁ U₂ Ue₁ Ue₂)
    (Z : ZeroModelFamilyOn 𝓘(ℝ, E3) X gX ρ hρ βX N C o δX εrX eX TX VX U₁ U₂)
    (k : Z.finite_centres.toFinset) (f : X → BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²))
    (hf : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : CGPTag_BAUGP L Z => ℝ²)) ∞ f)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1 / 1000)
    (hZE : ∀ p, ‖f p (.inr (.inr (.inr (.inl k)))) -
        cgpGlobalMap_BAUGP L Z p (.inr (.inr (.inr (.inl k))))‖ <
      δ₀ * (Z.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius) (he : eX < 1 / 40) :
    IsClosed (zspDomain_ZSP35_BGR L Z k f) := by
  obtain ⟨hsub, -⟩ := zsp_sublevel_eq_ZSP35_BGR L Z k f hδ₀ hZE he
  rw [← hsub]
  exact isClosed_le ((contMDiff_zspH0_ZSP35_BGR Z k).add
    (contMDiff_zspK_ZSP35_BGR L Z k f hf)).continuous continuous_const

end Generic

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
  {Ξ c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}

namespace BoundaryGaf02Chain

variable (C : BoundaryGaf02Chain DP.toBoundaryAugmentedData Kj Ξ Sg eg c cw bcut bder κ)

include C in
/-- ZSP01's `δ₀ = 200c₃/T < 1/1000` from the register (`1 ≤ Δ`, `1600·10⁶Δ ≤ T`) and the chain's
`c₃ ≤ 1/512`. -/
theorem delta_zero_lt_BGR (hΔ : 1 ≤ Δ) (hT : 1600 * (1000000 * Δ) ≤ T) :
    200 * c 2 / T < 1 / 1000 := by
  have hT0 : 0 < T := by nlinarith only [hT, hΔ]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hc2, -⟩ := C.numbers
  have hc20 : 0 ≤ c 2 := (C.c_pos_mono_V3_BGR.1.le.trans C.c_pos_mono_V3_BGR.2.1).trans
    C.c_pos_mono_V3_BGR.2.2
  rw [div_lt_iff₀ hT0]
  nlinarith only [hc2, hc20, hT, hΔ]

/-- **`domain_subset_ball`**: the actual zero domain of `C.E` lies in the ORIGINAL selected zero
ball `B_g(z_k, R_k)` of `W` (`Z_k ⊆ val '' B_ĝ(z_k, (.402 + e)R_k)` and `d_g ≤ d_ĝ`). -/
theorem actualZeroDomain_subset_ball_BGR (hΔ : 1 ≤ Δ) (hT : 1600 * (1000000 * Δ) ≤ T)
    (he : e < 1 / 40) (k : S.ZeroIdx_BAUGC) :
    C.actualZeroDomain_BIFc k ⊆ riemannianBallOf g k.1.val (S.zeroRadius_BAUGC k) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  have hT1 : 1 ≤ T := by nlinarith only [hT, hΔ]
  have hT0 : 0 < T := by linarith only [hT1]
  have hR := (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  have hc : (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center = k.1 :=
    S.family.zero.zero_center k.1 _
  rw [C.actualZeroDomain_eq_image_BGR hT1 he k]
  rintro _ ⟨x, hx, rfl⟩
  have hb := zspDomain_subset_ball_BGR S.family.toLocalPacketsOnB S.family.zero k C.zeroBindMap_BGR
    (C.delta_zero_lt_BGR hΔ hT) (C.zeroBind_ZE_BGR hT0 he k) hx
  rw [hc, mem_ball] at hb
  have hlt : dist x k.1 < S.zeroRadius_BAUGC k := by
    change dist x k.1 < (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius
    nlinarith
  have h1 := riemannianEDistOf_val_le_completion_BDRY1 W g S.completion.metric
    S.completion.inner_le k.1 x
  rw [inducedMetricSpace_hmetric S.completion.metric, dist_comm] at h1
  exact lt_of_le_of_lt h1 ((ENNReal.ofReal_lt_ofReal_iff (lt_of_le_of_lt dist_nonneg hlt)).mpr hlt)

/-- **`zero_cover`** (ZSP02 (ZB) at `a = 2/5`): every point of `W°` within `.38R_k` (in `d_ĝ`)
of the zero centre `z_k` lies in the interior of the actual zero domain of `C.E` (`e ≤ 1/1000`,
lead decision N76-6: the register's `e`-threshold of the closed `zsp02_ZB_ZSP35`). -/
theorem actualZeroDomain_cover_BGR (hΔ : 1 ≤ Δ) (hT : 1600 * (1000000 * Δ) ≤ T)
    (he : e ≤ 1 / 1000) (k : S.ZeroIdx_BAUGC) (q : W.pieceInterior ⊤)
    (hq : (letI := inducedMetricSpace S.completion.metric; dist q k.1) <
      38 / 100 * S.zeroRadius_BAUGC k) :
    q.val ∈ interior (C.actualZeroDomain_BIFc k) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  have he40 : e < 1 / 40 := by linarith only [he]
  have hT1 : 1 ≤ T := by nlinarith only [hT, hΔ]
  have hT0 : 0 < T := by linarith only [hT1]
  have hR := (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  have hc : (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center = k.1 :=
    S.family.zero.zero_center k.1 _
  have hin := closedBall_subset_interior_zspDomain_BGR S.family.toLocalPacketsOnB S.family.zero k
    C.zeroBindMap_BGR (C.delta_zero_lt_BGR hΔ hT) (C.zeroBind_ZE_BGR hT0 he40 k)
  rw [hc] at hin
  have hqin : q ∈ interior (zspDomain_ZSP35_BGR S.family.toLocalPacketsOnB S.family.zero k
      C.zeroBindMap_BGR) := by
    refine hin (mem_closedBall.mpr ?_)
    have h38 : (38 / 100 : ℝ) * S.zeroRadius_BAUGC k ≤ (381 / 1000 - e) *
        (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius := by
      change (38 / 100 : ℝ) * (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius
        ≤ _
      nlinarith
    exact (le_of_lt hq).trans h38
  rw [C.actualZeroDomain_eq_image_BGR hT1 he40 k]
  have hopen : IsOpenMap (Subtype.val : W.pieceInterior ⊤ → W.Carrier) :=
    (W.pieceInterior ⊤).isOpen.isOpenMap_subtype_val
  exact hopen.image_interior_subset _ ⟨q, hqin, rfl⟩

/-- **`isCompact_domain`**: the actual zero domain of `C.E` is compact (`val` of a closed subset of
a closed `ĝ`-ball of the proper `(W°, ĝ)`). -/
theorem isCompact_actualZeroDomain_BGR (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100)
    (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b)
    (he : e < 1 / 40) (hT : 1600 * (1000000 * Δ) ≤ T) (k : S.ZeroIdx_BAUGC) :
    IsCompact (C.actualZeroDomain_BIFc k) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  have hP : ProperSpace (W.pieceInterior ⊤) :=
    inducedMetricSpace_properSpace_of_riemannianMetricComplete
      ((riemannianMetricComplete_iff_completeSpace
        (inducedMetricSpace_hmetric S.completion.metric)).mpr S.completion.complete)
  have hT1 : 1 ≤ T := by nlinarith only [hT, hΔ]
  have hT0 : 0 < T := by linarith only [hT1]
  have hΔ0 : 0 < Δ := by linarith only [hΔ]
  have hcl := isClosed_zspDomain_BGR S.family.toLocalPacketsOnB S.family.zero k C.zeroBindMap_BGR
    (C.contMDiff_zeroBindMap_BGR hΛ hΔ0 hμ hτ hΔΛ hV hβ1 hb (by linarith only [he]))
    (C.delta_zero_lt_BGR hΔ hT) (C.zeroBind_ZE_BGR hT0 he k) he
  have hsub := zspDomain_subset_ball_BGR S.family.toLocalPacketsOnB S.family.zero k
    C.zeroBindMap_BGR (C.delta_zero_lt_BGR hΔ hT) (C.zeroBind_ZE_BGR hT0 he k)
  have hK : IsCompact (zspDomain_ZSP35_BGR S.family.toLocalPacketsOnB S.family.zero k
      C.zeroBindMap_BGR) :=
    (isCompact_closedBall _ _).of_isClosed_subset hcl (hsub.trans ball_subset_closedBall)
  rw [C.actualZeroDomain_eq_image_BGR hT1 he k]
  exact hK.image continuous_subtype_val

/-- **`pairwise_disjoint`**: distinct actual zero domains of `C.E` are disjoint (each lies in its
own selected zero ball; the selected balls are pairwise disjoint). -/
theorem actualZeroDomain_pairwise_disjoint_BGR (hΔ : 1 ≤ Δ) (hT : 1600 * (1000000 * Δ) ≤ T)
    (he : e < 1 / 40) : Pairwise (Disjoint on C.actualZeroDomain_BIFc) := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  have hT1 : 1 ≤ T := by nlinarith only [hT, hΔ]
  have hT0 : 0 < T := by linarith only [hT1]
  have hsub : ∀ k : S.ZeroIdx_BAUGC, C.actualZeroDomain_BIFc k ⊆ Subtype.val ''
      ball k.1 (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius := by
    intro k
    have hR := (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
    have hc : (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).center = k.1 :=
      S.family.zero.zero_center k.1 _
    rw [C.actualZeroDomain_eq_image_BGR hT1 he k]
    refine image_mono fun x hx => ?_
    have hb := zspDomain_subset_ball_BGR S.family.toLocalPacketsOnB S.family.zero k
      C.zeroBindMap_BGR (C.delta_zero_lt_BGR hΔ hT) (C.zeroBind_ZE_BGR hT0 he k) hx
    rw [hc, mem_ball] at hb
    rw [mem_ball]
    nlinarith
  intro i j hij
  have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
  have hd := S.family.zero.disjoint i.1 ((Set.Finite.mem_toFinset _).mp i.2) j.1
    ((Set.Finite.mem_toFinset _).mp j.2) hne
  refine Disjoint.mono (hsub i) (hsub j) ?_
  rw [disjoint_image_iff Subtype.val_injective]
  exact hd

end BoundaryGaf02Chain

end DifferentialGeometry.Geometry.Collapse
