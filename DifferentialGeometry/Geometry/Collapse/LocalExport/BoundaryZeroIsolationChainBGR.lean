import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryRigidityChainV3BGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryPortGlobalBlockMapBridge
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryWholeSupportCount

/-!
# ZSP01 on the boundary chain (slot v2, spec V3): zero blocks stay isolated (lane B-BCG-ROWS)

Blueprint `master207B.tex`, ZSP01 (B:6323) in the boundary setting (BCG07, B:9518–9524:
"ZSP01–ZSP02's zero-block isolation still uses the actual old support lists and retained blocks");
the input of the boundary zero-domain producer `BoundaryActualZeroDomains_BIFc` (BCG07 F3, lane
B-BCG-ROWS). For a zero index `k` (`J_k` = projection onto the WHOLE zero block of `H^∂`): (ZI)
`ρ(p) > 200R_k/T ⟹ J_k g_j(p) = 0` for `j = 0, …, 3` (`g₀ = F_∂`), and (ZE) `‖J_k(g_j − F_∂)(p)‖ <
δ₀R_k`, `δ₀ = 200c₃/T`, everywhere and on the segment `[F_∂ p, E p]`.

* `BoundaryInteriorSlots_BIF.orthogonal_stageQ_le_ker_tag_BGR`: a kept interior tag is killed by
  `(Q_j^∂)ᗮ`; `zeroTag_mem_stageTagsV2_BGR`: every zero tag is a tag of every v2 stage.
* `BoundarySupply.zeroBlock_original_eq_zero_BGR`: the original half (`20R_k/T < ρ(p) ⟹
  J_k F_∂(p) = 0`; boundary points: zero extension; interior points: LPA05's cutoff ratio on the
  boundary family, `zsp01_original_zero_block_BGR`, through `interiorMapOn_eq_cgpGlobalMap_BAUGP`).
* `BoundaryAugmentedDataPV3.contributor_zeroBlock_window_V3_BGR` (spec V3 field `zero_block`,
  (ZB*)).
* `BoundaryStageSlot_BIF.stage_zero_step_V3_BGR`: one stage keeps a zero block.
* **`BoundaryGaf02Chain.zsp01_ZI_V3_BGR`**, **`zsp01_ZE_V3_BGR`** (kernel form: any slot with the
  stage-core inclusion keeping the zero tags), **`zsp01_ZI_actualSlotsV2_BGR`**,
  **`zsp01_ZE_actualSlotsV2_BGR`** (every chain over the ACTUAL slot v2 with the V3 specs = the type
  of `BoundaryGaf02ChainE.toChain`).
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

attribute [local instance] interiorCharted_BDRY1 interiorManifold_BDRY1
  connectedSpace_interior_BDRY2

variable {K : ℕ} {A : ℝ → ℝ} {β : ℕ → ℝ}
  {βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ : ℝ}
  {W : CompactCarrier.{0}} [ConnectedSpace W.Carrier] {g : SmoothRiemannianMetric W.model W.Carrier}
  {δn : ℝ} {n : ℕ} {B : NearlyCuspidalBoundary W g K δn}
  {oM : ManifoldOrientation 𝓘(ℝ, E3) (W.pieceInterior ⊤) 3}

namespace BoundaryInteriorSlots_BIF

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} (Φ : BoundaryInteriorSlots_BIF S)

/-- **A kept interior tag is killed by `(Q_j^∂)ᗮ`**: if `t` is a tag of stage `st`, the whole
`t`-block of every `v ∈ (Q_j^∂)ᗮ` vanishes. -/
theorem orthogonal_stageQ_le_ker_tag_BGR {st : Fin 3} {t : S.IntTag_BAUGA}
    (ht : t ∈ Φ.stageTags st) :
    (Φ.stageQ st)ᗮ ≤ LinearMap.ker ((blockProjCLM_PLN
      (V := fun _ : S.IntTag_BAUGA ⊕ Fin S.packet.cusp.count => ℝ²) (Sum.inl t) :
        BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] WithLp 2 (ℝ² × ℝ)) :
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ]
            WithLp 2 (ℝ² × ℝ)) := fun v hv => by
  have h0 : Φ.stageProj st v = 0 :=
    (DFunLike.congr_fun (Φ.starProjection_stageQ_BGR st) v).symm.trans
      (((Φ.stageQ st).starProjection_apply_eq_zero_iff).mpr hv)
  have h1 : Φ.stageProj st v (Sum.inl t) = v (Sum.inl t) := by
    change blockRestrict (Φ.stageTagsAug st) v (Sum.inl t) = _
    rw [stageTagsAug, blockRestrict_disjSum_inl_BGR ht]
  rw [LinearMap.mem_ker]
  change v (Sum.inl t) = 0
  rw [← h1, h0]
  rfl

end BoundaryInteriorSlots_BIF

/-- **Every zero tag is a tag of every v2 stage** (`Q₁^∂` = all; `Q₂^∂`, `Q₃^∂` contain the zero
blocks). -/
theorem zeroTag_mem_stageTagsV2_BGR
    (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ
      W g δn n B oM) (st : Fin 3) (k : S.ZeroIdx_BAUGC) :
    S.zeroTag_BAUGC k ∈ (actualSlotsV2_BAUGD S).stageTags st := by
  rw [actualSlotsV2_stageTags_BAUGD]
  fin_cases st
  · exact Finset.mem_univ _
  · exact BoundarySupplyCore.mem_stageTagsV2_one_BAUGD.mpr rfl
  · exact BoundarySupplyCore.mem_stageTagsV2_two_BAUGD.mpr rfl

section ZeroFamily

variable {X : Type} [mX : MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X]
  [CompleteSpace X] [SigmaCompactSpace X] {gX : SmoothRiemannianMetric 𝓘(ℝ, E3) X}
  {hmetric : ∀ a b : X, riemannianEDistOf gX a b = ENNReal.ofReal (dist a b)}
  {ρ : X → ℝ} {hρ : ∀ p, 0 < ρ p} {ΛX : ℝ} {βX : ℕ → ℝ} {ΔX σsX : ℝ} {KX : ℕ}
  {σcX μX bX sX b'X s'X εX γcX βcX LmaxX τX γX δX εrX eX TX VX vsX ζX ΛzX : ℝ}
  {U₁ U₂ Ue₁ Ue₂ : Set X}

/-- The model metrics of `LocalPacketsOnBF`, as a named local instance. -/
local instance instMetricNBF_BGR
    (P : LocalPacketsOnBF X gX hmetric ρ hρ ΛX βX ΔX σsX KX σcX μX bX sX b'X s'X εX γcX βcX LmaxX τX
      γX δX εrX eX TX VX vsX ζX ΛzX U₁ U₂ Ue₁ Ue₂) (a : X) : MetricSpace (P.N a) :=
  P.instMetricN a

/-- The model charts of `LocalPacketsOnBF`, as a named local instance. -/
local instance instChartedNBF_BGR
    (P : LocalPacketsOnBF X gX hmetric ρ hρ ΛX βX ΔX σsX KX σcX μX bX sX b'X s'X εX γcX βcX LmaxX τX
      γX δX εrX eX TX VX vsX ζX ΛzX U₁ U₂ Ue₁ Ue₂) (a : X) : ChartedSpace E3 (P.N a) :=
  P.instChartedN a

/-- The cone metrics of `LocalPacketsOnBF`, as a named local instance. -/
local instance instMetricCBF_BGR
    (P : LocalPacketsOnBF X gX hmetric ρ hρ ΛX βX ΔX σsX KX σcX μX bX sX b'X s'X εX γcX βcX LmaxX τX
      γX δX εrX eX TX VX vsX ζX ΛzX U₁ U₂ Ue₁ Ue₂) (a : X) : MetricSpace (P.C a) :=
  P.instMetricC a

/-- **LPA05 on the zero supports** of the boundary family: on the closed support of LC31's annular
cutoff of the zero ball at `c`, `ρ(p) ≤ 20R_c/T` (`e < 1/40`). -/
theorem zero_cutoff_ratio_BGR
    (P : LocalPacketsOnBF X gX hmetric ρ hρ ΛX βX ΔX σsX KX σcX μX bX sX b'X s'X εX γcX βcX LmaxX τX
      γX δX εrX eX TX VX vsX ζX ΛzX U₁ U₂ Ue₁ Ue₂) (hT : 0 < TX) (he : eX < 1 / 40) {c : X}
    (hc : c ∈ P.zero.centres) {p : X}
    (hp : p ∈ tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
      ((P.zero.zero c hc).radial y))) :
    ρ p ≤ 20 * (P.zero.zero c hc).radius / TX := by
  have hband := zero_cutoff_tsupport_band_BCNT P.zero he hc hp
  have hcp : dist c p ≤ 10 * (P.zero.zero c hc).radius := by linarith [hband.2]
  have hratio := P.zero_local_comparison c hc p hcp
  rw [le_div_iff₀ (hρ p)] at hratio
  rw [le_div_iff₀ hT]
  linarith

/-- **ZSP01 (ZI), original half, on the boundary family**: if `20R_c/T < ρ(p)` the WHOLE zero block
of `𝓔⁰(p)` at the zero ball of `c` vanishes. -/
theorem zsp01_original_zero_block_BGR
    (P : LocalPacketsOnBF X gX hmetric ρ hρ ΛX βX ΔX σsX KX σcX μX bX sX b'X s'X εX γcX βcX LmaxX τX
      γX δX εrX eX TX VX vsX ζX ΛzX U₁ U₂ Ue₁ Ue₂) (hT : 0 < TX) (he : eX < 1 / 40)
    (i : P.zero.finite_centres.toFinset) {p : X}
    (hρp : 20 * (P.zero.zero i.1 ((Set.Finite.mem_toFinset _).mp i.2)).radius / TX < ρ p) :
    cgpGlobalMap_BAUGP P.toLocalPacketsOnB P.zero p (.inr (.inr (.inr (.inl i)))) = 0 := by
  have hi := (Set.Finite.mem_toFinset _).mp i.2
  have hcut :
      Calculus.annularCutoff Calculus.cutoffProfile ((P.zero.zero i.1 hi).radial p) = 0 := by
    by_contra h
    have hmem : p ∈ tsupport (fun y => Calculus.annularCutoff Calculus.cutoffProfile
        ((P.zero.zero i.1 hi).radial y)) := subset_tsupport _ h
    have := zero_cutoff_ratio_BGR P hT he hi hmem
    linarith
  change WithLp.toLp 2 ((cgpRadius_BAUGP P.toLocalPacketsOnB P.zero (.inr (.inr (.inr (.inl i))))
      p *
      Calculus.annularCutoff Calculus.cutoffProfile ((P.zero.zero i.1 hi).radial p)) •
      cgpCoord_BAUGP P.toLocalPacketsOnB P.zero (.inr (.inr (.inr (.inl i)))) p,
    cgpRadius_BAUGP P.toLocalPacketsOnB P.zero (.inr (.inr (.inr (.inl i)))) p *
      Calculus.annularCutoff Calculus.cutoffProfile ((P.zero.zero i.1 hi).radial p)) = 0
  rw [hcut, mul_zero, zero_smul]
  rfl

end ZeroFamily

namespace BoundarySupply

/-- **ZSP01 (ZI), original half, on `W`**: if `20R_k/T < ρ(y)` the WHOLE zero block of `F_∂(y)`
at the zero index `k` vanishes (interior points: LPA05's cutoff ratio; boundary points:
the zero extension of the interior slots). -/
theorem zeroBlock_original_eq_zero_BGR
    (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ
      W g δn n B oM) (hT : 0 < T) (he : e < 1 / 40) (k : S.ZeroIdx_BAUGC)
    {y : W.Carrier} (hy : 20 * S.zeroRadius_BAUGC k / T < S.rho y) :
    S.zeroBlockCLM_BAUGC k (S.boundaryOriginalMap y) = 0 := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  change S.intSlotW_BAUGA (S.zeroTag_BAUGC k) y = 0
  have hne : S.zeroTag_BAUGC k ≠ S.scaleTag_BAUGA := by
    intro h
    cases h
  unfold BoundarySupplyCore.intSlotW_BAUGA
  simp only [hne, ↓reduceIte]
  by_cases hyr : ∃ x : W.pieceInterior ⊤, x.val = y
  · obtain ⟨x, rfl⟩ := hyr
    rw [Subtype.val_injective.extend_apply]
    rw [S.interiorMapOn_eq_cgpGlobalMap_BAUGP]
    exact zsp01_original_zero_block_BGR S.family.toLocalPacketsOnBFR.toLocalPacketsOnBF hT he k hy
  · rw [Function.extend_apply' _ _ _ (fun ⟨x, hx⟩ => hyr ⟨x, hx⟩)]
    rfl

end BoundarySupply

namespace BoundaryAugmentedDataPV3

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {Γ Sg eg : Fin 3 → ℝ}
  (DP : BoundaryAugmentedDataPV3 S Φ Γ Sg eg)

/-- **ZSP01's contributor half on the three stored tables, spec V3** ((ZB*), field `zero_block`): a
window contributor `y` of the anchor `x = π_j F_∂ q` with `ρ(q) > 200R_k/T` has zero `k`-block and
`L_y ≤ ker J_k`. -/
theorem contributor_zeroBlock_window_V3_BGR {Ξs : ℝ} (hΞ : 0 < Ξs) (st : Fin 3)
    (hsgΞ : Sg st ≤ Ξs / 10000) (k : S.ZeroIdx_BAUGC) {q : W.pieceInterior ⊤}
    (hx : Φ.stageProj st (S.boundaryOriginalMap q.val) ∈ Φ.stageCloud st)
    (hρq : 200 * S.zeroRadius_BAUGC k / T < S.rho q)
    {y : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)} (hy : y ∈ Φ.stageCloud st)
    (hwin : (closedBall y (80 * Ξs⁻¹ * DP.stageRadius st (Sg st) y) ∩
      ball (Φ.stageProj st (S.boundaryOriginalMap q.val))
        (8 * Ξs⁻¹ * DP.stageRadius st (Sg st)
          (Φ.stageProj st (S.boundaryOriginalMap q.val)))).Nonempty) :
    S.zeroBlockCLM_BAUGC k y = 0 ∧
      DP.stagePlane st y ≤ LinearMap.ker ((S.zeroBlockCLM_BAUGC k :
        BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] WithLp 2 (ℝ² × ℝ)) :
          BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →ₗ[ℝ]
            WithLp 2 (ℝ² × ℝ)) := by
  fin_cases st
  · exact DP.circle_spec.zero_block _ _ hΞ hsgΞ _ k q hx hρq y hy hwin
  · exact DP.edge_spec.zero_block _ _ hΞ hsgΞ _ k q hx hρq y hy hwin
  · exact DP.slim_spec.zero_block _ _ hΞ hsgΞ _ k q hx hρq y hy hwin

end BoundaryAugmentedDataPV3

namespace BoundaryStageSlot_BIF

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S Φ Γ Sg eg} {Kj : ℕ}

/-- **The value step of one stage, spec V3** (A3b without any isolation input): for an input `z`
within `3Σ_jρ(p)/5` of `F_∂ p` whose cutoff support localizes `π_j F_∂ p` into the stage cloud
(with a preimage in `W°`), `‖Ψ_j z − z‖ ≤ ‖z − F_∂ p‖ + Ξ_j(5/3)Σ_jρ(p)`. -/
theorem stage_value_V3_BGR {st : Fin 3} {Ξs cws : ℝ}
    (sl : BoundaryStageSlot_BIF DP.toBoundaryAugmentedData st Kj Ξs (Sg st) cws)
    (hΞ : 0 < Ξs) (hsg : 0 < Sg st) (hψ : ∀ z, Φ.cutoff st z ∈ Icc (0 : ℝ) 1)
    (p : W.Carrier) (z : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
    (hloc : z ∈ tsupport (Φ.cutoff st) → ∃ q : W.pieceInterior ⊤, q.val = p ∧
      Φ.stageProj st (S.boundaryOriginalMap p) ∈ Φ.stageCloud st)
    (hz : ‖z - S.boundaryOriginalMap p‖ < 3 / 5 * (Sg st * S.rho p)) :
    ‖Φ.adjust st sl.map z - z‖ ≤
        ‖z - S.boundaryOriginalMap p‖ + Ξs * (5 / 3 * (Sg st * S.rho p)) := by
  cases sl with
  | inactive hcore henl =>
    have hid : Φ.adjust st (BoundaryStageSlot_BIF.map (.inactive hcore henl :
        BoundaryStageSlot_BIF DP.toBoundaryAugmentedData st Kj Ξs (Sg st) cws)) = id :=
      Φ.adjust_id st
    rw [hid]
    simp only [id, sub_self, norm_zero]
    have h1 : 0 ≤ Ξs * (5 / 3 * (Sg st * S.rho p)) := by
      have := S.rho_pos p
      positivity
    linarith [norm_nonneg (z - S.boundaryOriginalMap p)]
  | active O =>
    have hmap : Φ.adjust st (BoundaryStageSlot_BIF.map (.active O :
        BoundaryStageSlot_BIF DP.toBoundaryAugmentedData st Kj Ξs (Sg st) cws)) =
        adjustmentMap (Φ.stageQ st) (fun y => (Φ.stageQ st).starProjection (O.ambient y))
          (Φ.cutoff st) := rfl
    rw [hmap]
    have hπ := Φ.starProjection_stageQ_BGR st
    have hloc' : z ∈ tsupport (Φ.cutoff st) →
        Φ.stageProj st (S.boundaryOriginalMap p) ∈ Φ.stageCloud st := fun h => by
      obtain ⟨-, -, hx⟩ := hloc h
      exact hx
    have hrx : z ∈ tsupport (Φ.cutoff st) →
        3 / 5 * (Sg st * S.rho p) ≤
            DP.stageRadius st (Sg st) (Φ.stageProj st (S.boundaryOriginalMap p)) ∧
          DP.stageRadius st (Sg st) (Φ.stageProj st (S.boundaryOriginalMap p)) ≤
            5 / 3 * (Sg st * S.rho p) := fun h => by
      obtain ⟨q, hq, hx⟩ := hloc h
      have hc := DP.stageRadius_cmp_V3_BGR st hsg.le hx (q := q) (by rw [hq])
      rw [hq] at hc
      exact hc
    have h := Cfs15StageOutput.stage_step_cmp_generic_BGR
      (H := BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) O (Φ.stageQ st)
      (Φ.stageProj st) (fun v => DFunLike.congr_fun hπ v) (Φ.cutoff st) hψ
      (0 : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count) →L[ℝ] ℝ)
      (fun v _ => LinearMap.mem_ker.mpr rfl) (S.boundaryOriginalMap p) z 0 hloc' hrx hz
      (fun _ y _ _ => ⟨rfl, fun v _ => LinearMap.mem_ker.mpr rfl⟩)
    exact h.1

/-- **One stage keeps a zero block, spec V3** (ZSP01's stage step): if the zero tag of `k` is a
stage tag, `ρ(p) > 200R_k/T`, the input `z` is in the stage tube of `p` and `J_k z = 0`, then
`J_k(Ψ_j z) = 0` (every window contributor has zero `k`-block and `L_y ≤ ker J_k`). -/
theorem stage_zero_step_V3_BGR {st : Fin 3} {Ξs cws : ℝ}
    (sl : BoundaryStageSlot_BIF DP.toBoundaryAugmentedData st Kj Ξs (Sg st) cws)
    (hΞ : 0 < Ξs) (hsg : 0 < Sg st) (hSgΞ : Sg st ≤ Ξs / 10000)
    (hψ : ∀ z, Φ.cutoff st z ∈ Icc (0 : ℝ) 1) (k : S.ZeroIdx_BAUGC)
    (hzt : S.zeroTag_BAUGC k ∈ Φ.stageTags st) (p : W.Carrier)
    (z : BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count))
    (hloc : z ∈ tsupport (Φ.cutoff st) → ∃ q : W.pieceInterior ⊤, q.val = p ∧
      Φ.stageProj st (S.boundaryOriginalMap p) ∈ Φ.stageCloud st)
    (hz : ‖z - S.boundaryOriginalMap p‖ < 3 / 5 * (Sg st * S.rho p))
    (hρ : 200 * S.zeroRadius_BAUGC k / T < S.rho p) (hJ : S.zeroBlockCLM_BAUGC k z = 0) :
    S.zeroBlockCLM_BAUGC k (Φ.adjust st sl.map z) = 0 := by
  cases sl with
  | inactive hcore henl =>
    have hid : Φ.adjust st (BoundaryStageSlot_BIF.map (.inactive hcore henl :
        BoundaryStageSlot_BIF DP.toBoundaryAugmentedData st Kj Ξs (Sg st) cws)) = id :=
      Φ.adjust_id st
    rw [hid]
    exact hJ
  | active O =>
    have hmap : Φ.adjust st (BoundaryStageSlot_BIF.map (.active O :
        BoundaryStageSlot_BIF DP.toBoundaryAugmentedData st Kj Ξs (Sg st) cws)) =
        adjustmentMap (Φ.stageQ st) (fun y => (Φ.stageQ st).starProjection (O.ambient y))
          (Φ.cutoff st) := rfl
    rw [hmap]
    have hπ := Φ.starProjection_stageQ_BGR st
    have hloc' : z ∈ tsupport (Φ.cutoff st) →
        Φ.stageProj st (S.boundaryOriginalMap p) ∈ Φ.stageCloud st := fun h => by
      obtain ⟨-, -, hx⟩ := hloc h
      exact hx
    have hrx : z ∈ tsupport (Φ.cutoff st) →
        3 / 5 * (Sg st * S.rho p) ≤
            DP.stageRadius st (Sg st) (Φ.stageProj st (S.boundaryOriginalMap p)) ∧
          DP.stageRadius st (Sg st) (Φ.stageProj st (S.boundaryOriginalMap p)) ≤
            5 / 3 * (Sg st * S.rho p) := fun h => by
      obtain ⟨q, hq, hx⟩ := hloc h
      have hc := DP.stageRadius_cmp_V3_BGR st hsg.le hx (q := q) (by rw [hq])
      rw [hq] at hc
      exact hc
    have h := Cfs15StageOutput.stage_step_cmp_generic_BGR
      (H := BoundaryAmbient_BIF S.IntTag_BAUGA (Fin S.packet.cusp.count)) O (Φ.stageQ st)
      (Φ.stageProj st) (fun v => DFunLike.congr_fun hπ v) (Φ.cutoff st) hψ
      (S.zeroBlockCLM_BAUGC k) (Φ.orthogonal_stageQ_le_ker_tag_BGR hzt)
      (S.boundaryOriginalMap p) z 0 hloc' hrx hz
      (fun h0 y hyI hwin => by
        obtain ⟨q, rfl, hx⟩ := hloc h0
        exact DP.contributor_zeroBlock_window_V3_BGR hΞ st hSgΞ k hx hρ (O.I_subset hyI) hwin)
    exact h.2 hJ

end BoundaryStageSlot_BIF

namespace BoundaryGaf02Chain

variable {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ
  Λz θ W g δn n B oM} {Φ : BoundaryInteriorSlots_BIF S} {Γ Sg eg : Fin 3 → ℝ}
  {DP : BoundaryAugmentedDataPV3 S Φ Γ Sg eg} {Kj : ℕ} {Ξ c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
  (C : BoundaryGaf02Chain DP.toBoundaryAugmentedData Kj Ξ Sg eg c cw bcut bder κ)

include C in
/-- **A3b along the chain, spec V3, value part only**: `‖g_j − F_∂‖ < c_jρ` for `j = 1, 2, 3`, and
the stage tubes `‖g_j − F_∂‖ < 3Σ_{j+1}ρ/5` for `j = 0, 1, 2`. -/
theorem chain_values_V3_BGR
    (hcore : ∀ st, ⋃ m ∈ {m : S.MarkerIdx_BAUGC | S.markerStage_BAUGC m = st},
      S.markerCore7_BAUGC m ⊆ Φ.stageCore st) (p : W.Carrier) :
    ‖C.g₁ p - S.boundaryOriginalMap p‖ < c 0 * S.rho p ∧
      ‖C.g₂ p - S.boundaryOriginalMap p‖ < c 1 * S.rho p ∧
      ‖C.E p - S.boundaryOriginalMap p‖ < c 2 * S.rho p ∧
      ‖C.g₁ p - S.boundaryOriginalMap p‖ < 3 / 5 * (Sg 1 * S.rho p) ∧
      ‖C.g₂ p - S.boundaryOriginalMap p‖ < 3 / 5 * (Sg 2 * S.rho p) := by
  obtain ⟨hj, h0, -, -, -, hc01, h1, -, -, -, hc12, h2, -, -⟩ := C.numbers
  obtain ⟨hΞ0, hS0, -⟩ := hj 0
  obtain ⟨hΞ1, hS1, -⟩ := hj 1
  obtain ⟨hΞ2, hS2, -⟩ := hj 2
  have hc0 := C.c_pos_mono_V3_BGR.1
  have hψ0 := C.cutoff_bindings.1.2.1
  have hψ1 := C.cutoff_bindings.2.1.2.1
  have hψ2 := C.cutoff_bindings.2.2.2.1
  have hρ := S.rho_pos p
  have hz0 : ‖S.boundaryOriginalMap p - S.boundaryOriginalMap p‖ < 3 / 5 * (Sg 0 * S.rho p) := by
    rw [sub_self, norm_zero]; positivity
  have st0 := (C.slot 0).stage_value_V3_BGR hΞ0 hS0 hψ0 p (S.boundaryOriginalMap p)
    (C.stagePre_zero_BGR hcore p) hz0
  have hg1 : Φ.adjust 0 (C.slot 0).map (S.boundaryOriginalMap p) = C.g₁ p := rfl
  rw [hg1, sub_self, norm_zero, zero_add] at st0
  have he0 : ‖C.g₁ p - S.boundaryOriginalMap p‖ < c 0 * S.rho p := by
    have h3 : 5 / 3 * Ξ 0 * Sg 0 * S.rho p < c 0 * S.rho p := mul_lt_mul_of_pos_right h0 hρ
    have h4 : Ξ 0 * (5 / 3 * (Sg 0 * S.rho p)) = 5 / 3 * Ξ 0 * Sg 0 * S.rho p := by ring
    linarith only [st0, h3, h4]
  have hz1 : ‖C.g₁ p - S.boundaryOriginalMap p‖ < 3 / 5 * (Sg 1 * S.rho p) := by
    have h3 : c 0 * S.rho p ≤ 3 * Sg 1 / 10 * S.rho p := mul_le_mul_of_nonneg_right hc01 hρ.le
    have h4 : 0 < Sg 1 * S.rho p := mul_pos hS1 hρ
    linarith only [he0, h3, h4]
  have st1 := (C.slot 1).stage_value_V3_BGR hΞ1 hS1 hψ1 p (C.g₁ p) (C.stagePre_one_BGR hcore p) hz1
  have hg2 : Φ.adjust 1 (C.slot 1).map (C.g₁ p) = C.g₂ p := rfl
  rw [hg2] at st1
  have he1 : ‖C.g₂ p - S.boundaryOriginalMap p‖ < c 1 * S.rho p := by
    have htri := norm_sub_le_norm_sub_add_norm_sub (C.g₂ p) (C.g₁ p) (S.boundaryOriginalMap p)
    have hΞc0 : 0 ≤ Ξ 1 * c 0 := mul_nonneg hΞ1.le hc0.le
    have hb : (2 * c 0 + 5 / 3 * Ξ 1 * Sg 1) * S.rho p < c 1 * S.rho p :=
      mul_lt_mul_of_pos_right (by linarith only [h1, hΞc0]) hρ
    have h4 : Ξ 1 * (5 / 3 * (Sg 1 * S.rho p)) = 5 / 3 * Ξ 1 * Sg 1 * S.rho p := by ring
    linarith only [htri, st1, he0, hb, h4]
  have hc1 : 0 < c 1 := lt_of_lt_of_le hc0 C.c_pos_mono_V3_BGR.2.1
  have hz2 : ‖C.g₂ p - S.boundaryOriginalMap p‖ < 3 / 5 * (Sg 2 * S.rho p) := by
    have h3 : c 1 * S.rho p ≤ 3 * Sg 2 / 10 * S.rho p := mul_le_mul_of_nonneg_right hc12 hρ.le
    have h4 : 0 < Sg 2 * S.rho p := mul_pos hS2 hρ
    linarith only [he1, h3, h4]
  have st2 := (C.slot 2).stage_value_V3_BGR hΞ2 hS2 hψ2 p (C.g₂ p) (C.stagePre_two_BGR hcore p) hz2
  have hg3 : Φ.adjust 2 (C.slot 2).map (C.g₂ p) = C.E p := rfl
  rw [hg3] at st2
  have he2 : ‖C.E p - S.boundaryOriginalMap p‖ < c 2 * S.rho p := by
    have htri := norm_sub_le_norm_sub_add_norm_sub (C.E p) (C.g₂ p) (S.boundaryOriginalMap p)
    have hΞc1 : 0 ≤ Ξ 2 * c 1 := mul_nonneg hΞ2.le hc1.le
    have hb : (2 * c 1 + 5 / 3 * Ξ 2 * Sg 2) * S.rho p < c 2 * S.rho p :=
      mul_lt_mul_of_pos_right (by linarith only [h2, hΞc1]) hρ
    have h4 : Ξ 2 * (5 / 3 * (Sg 2 * S.rho p)) = 5 / 3 * Ξ 2 * Sg 2 * S.rho p := by ring
    linarith only [htri, st2, he1, hb, h4]
  exact ⟨he0, he1, he2, hz1, hz2⟩

include C in
/-- **ZSP01 (ZI) on the boundary chain, spec V3** (kernel form: any slot with the stage-core
inclusion whose stages keep the zero tag of `k`): `ρ(p) > 200R_k/T ⟹` the WHOLE `k`-block of
`F_∂(p)`, `g₁(p)`, `g₂(p)`, `E(p)` vanishes. -/
theorem zsp01_ZI_V3_BGR
    (hcore : ∀ st, ⋃ m ∈ {m : S.MarkerIdx_BAUGC | S.markerStage_BAUGC m = st},
      S.markerCore7_BAUGC m ⊆ Φ.stageCore st) (k : S.ZeroIdx_BAUGC)
    (hzt : ∀ st, S.zeroTag_BAUGC k ∈ Φ.stageTags st) (hT : 0 < T) (he : e < 1 / 40)
    {p : W.Carrier} (hρ : 200 * S.zeroRadius_BAUGC k / T < S.rho p) :
    S.zeroBlockCLM_BAUGC k (S.boundaryOriginalMap p) = 0 ∧
      S.zeroBlockCLM_BAUGC k (C.g₁ p) = 0 ∧ S.zeroBlockCLM_BAUGC k (C.g₂ p) = 0 ∧
      S.zeroBlockCLM_BAUGC k (C.E p) = 0 := by
  obtain ⟨hj, -⟩ := C.numbers
  obtain ⟨hΞ0, hS0, -, -, hSΞ0, -⟩ := hj 0
  obtain ⟨hΞ1, hS1, -, -, hSΞ1, -⟩ := hj 1
  obtain ⟨hΞ2, hS2, -, -, hSΞ2, -⟩ := hj 2
  have hψ0 := C.cutoff_bindings.1.2.1
  have hψ1 := C.cutoff_bindings.2.1.2.1
  have hψ2 := C.cutoff_bindings.2.2.2.1
  have hR : 0 < S.zeroRadius_BAUGC k := by
    let _ := inducedMetricSpace S.completion.metric
    let _ := S.completion.complete
    let _ := S.family.instMetricN
    let _ := S.family.instChartedN
    let _ := S.family.instMetricC
    exact (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  have h20 : 20 * S.zeroRadius_BAUGC k / T < S.rho p := by
    have : 20 * S.zeroRadius_BAUGC k / T ≤ 200 * S.zeroRadius_BAUGC k / T :=
      div_le_div_of_nonneg_right (by linarith only [hR]) hT.le
    linarith only [this, hρ]
  have h0 := S.zeroBlock_original_eq_zero_BGR hT he k h20
  obtain ⟨-, -, -, hz1, hz2⟩ := C.chain_values_V3_BGR hcore p
  have hz0 : ‖S.boundaryOriginalMap p - S.boundaryOriginalMap p‖ < 3 / 5 * (Sg 0 * S.rho p) := by
    rw [sub_self, norm_zero]
    have := S.rho_pos p
    positivity
  have h1 : S.zeroBlockCLM_BAUGC k (C.g₁ p) = 0 :=
    (C.slot 0).stage_zero_step_V3_BGR hΞ0 hS0 hSΞ0 hψ0 k (hzt 0) p (S.boundaryOriginalMap p)
      (C.stagePre_zero_BGR hcore p) hz0 hρ h0
  have h2 : S.zeroBlockCLM_BAUGC k (C.g₂ p) = 0 :=
    (C.slot 1).stage_zero_step_V3_BGR hΞ1 hS1 hSΞ1 hψ1 k (hzt 1) p (C.g₁ p)
      (C.stagePre_one_BGR hcore p) hz1 hρ h1
  have h3 : S.zeroBlockCLM_BAUGC k (C.E p) = 0 :=
    (C.slot 2).stage_zero_step_V3_BGR hΞ2 hS2 hSΞ2 hψ2 k (hzt 2) p (C.g₂ p)
      (C.stagePre_two_BGR hcore p) hz2 hρ h2
  exact ⟨h0, h1, h2, h3⟩

include C in
/-- **ZSP01 (ZE) on the boundary chain, spec V3**: with `δ₀ = 200c₃/T`,
`‖J_k(g_j(p) − F_∂(p))‖ < δ₀R_k` for `j = 0, …, 3` and for every point of the segment
`[F_∂ p, E p]`, at EVERY `p` (no global bound on `ρ/R_k`). -/
theorem zsp01_ZE_V3_BGR
    (hcore : ∀ st, ⋃ m ∈ {m : S.MarkerIdx_BAUGC | S.markerStage_BAUGC m = st},
      S.markerCore7_BAUGC m ⊆ Φ.stageCore st) (k : S.ZeroIdx_BAUGC)
    (hzt : ∀ st, S.zeroTag_BAUGC k ∈ Φ.stageTags st) (hT : 0 < T) (he : e < 1 / 40)
    (p : W.Carrier) :
    (∀ j : Fin 4, ‖S.zeroBlockCLM_BAUGC k (C.stage j p - S.boundaryOriginalMap p)‖ <
      200 * c 2 / T * S.zeroRadius_BAUGC k) ∧
    ∀ z ∈ segment ℝ (S.boundaryOriginalMap p) (C.E p),
      ‖S.zeroBlockCLM_BAUGC k (z - S.boundaryOriginalMap p)‖ <
        200 * c 2 / T * S.zeroRadius_BAUGC k := by
  obtain ⟨hc0, hc01, hc12⟩ := C.c_pos_mono_V3_BGR
  have hc2 : 0 < c 2 := by linarith only [hc0, hc01, hc12]
  have hR : 0 < S.zeroRadius_BAUGC k := by
    let _ := inducedMetricSpace S.completion.metric
    let _ := S.completion.complete
    let _ := S.family.instMetricN
    let _ := S.family.instChartedN
    let _ := S.family.instMetricC
    exact (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius_pos
  have hδ : 0 < 200 * c 2 / T * S.zeroRadius_BAUGC k := by positivity
  have hρp := S.rho_pos p
  have hstage : ∀ j : Fin 4, ‖S.zeroBlockCLM_BAUGC k (C.stage j p - S.boundaryOriginalMap p)‖ <
      200 * c 2 / T * S.zeroRadius_BAUGC k := by
    intro j
    by_cases hρ : 200 * S.zeroRadius_BAUGC k / T < S.rho p
    · obtain ⟨h0, h1, h2, h3⟩ := C.zsp01_ZI_V3_BGR hcore k hzt hT he hρ
      have hk : S.zeroBlockCLM_BAUGC k (C.stage j p) = 0 := by
        fin_cases j
        · exact h0
        · exact h1
        · exact h2
        · exact h3
      rw [map_sub, hk, h0, sub_zero, norm_zero]
      exact hδ
    · have hle : S.rho p ≤ 200 * S.zeroRadius_BAUGC k / T := not_lt.mp hρ
      have hm : c 2 * S.rho p ≤ 200 * c 2 / T * S.zeroRadius_BAUGC k := by
        have := mul_le_mul_of_nonneg_left hle hc2.le
        have e1 : c 2 * (200 * S.zeroRadius_BAUGC k / T) =
            200 * c 2 / T * S.zeroRadius_BAUGC k := by
          ring
        linarith only [this, e1]
      obtain ⟨he0, he1, he2, -, -⟩ := C.chain_values_V3_BGR hcore p
      have hm0 : c 0 * S.rho p ≤ c 2 * S.rho p :=
        mul_le_mul_of_nonneg_right (hc01.trans hc12) hρp.le
      have hm1 : c 1 * S.rho p ≤ c 2 * S.rho p := mul_le_mul_of_nonneg_right hc12 hρp.le
      have hd : ‖C.stage j p - S.boundaryOriginalMap p‖ < 200 * c 2 / T * S.zeroRadius_BAUGC k := by
        fin_cases j
        · change ‖S.boundaryOriginalMap p - S.boundaryOriginalMap p‖ <
            200 * c 2 / T * S.zeroRadius_BAUGC k
          rw [sub_self, norm_zero]
          exact hδ
        · change ‖C.g₁ p - S.boundaryOriginalMap p‖ < 200 * c 2 / T * S.zeroRadius_BAUGC k
          linarith only [he0, hm0, hm]
        · change ‖C.g₂ p - S.boundaryOriginalMap p‖ < 200 * c 2 / T * S.zeroRadius_BAUGC k
          linarith only [he1, hm1, hm]
        · change ‖C.E p - S.boundaryOriginalMap p‖ < 200 * c 2 / T * S.zeroRadius_BAUGC k
          linarith only [he2, hm]
      have hn := PiLp.norm_apply_le (C.stage j p - S.boundaryOriginalMap p)
        (Sum.inl (S.zeroTag_BAUGC k))
      exact lt_of_le_of_lt hn hd
  refine ⟨hstage, fun z hz => ?_⟩
  obtain ⟨a, bb, ha, hbb, hab, rfl⟩ := hz
  have h3 := hstage 3
  change ‖S.zeroBlockCLM_BAUGC k (C.E p - S.boundaryOriginalMap p)‖ <
    200 * c 2 / T * S.zeroRadius_BAUGC k at h3
  have hseg : a • S.boundaryOriginalMap p + bb • C.E p - S.boundaryOriginalMap p =
      bb • (C.E p - S.boundaryOriginalMap p) := by
    rw [show a = 1 - bb by linarith, sub_smul, one_smul, smul_sub]
    abel
  rw [hseg, map_smul, norm_smul, Real.norm_eq_abs, abs_of_nonneg hbb]
  have hb1 : bb ≤ 1 := by linarith
  calc bb * ‖S.zeroBlockCLM_BAUGC k (C.E p - S.boundaryOriginalMap p)‖ ≤
        1 * ‖S.zeroBlockCLM_BAUGC k (C.E p - S.boundaryOriginalMap p)‖ :=
        mul_le_mul_of_nonneg_right hb1 (norm_nonneg _)
    _ < 200 * c 2 / T * S.zeroRadius_BAUGC k := by rw [one_mul]; exact h3

end BoundaryGaf02Chain

/-- **ZSP01 (ZI) on every chain over the ACTUAL slot v2** with the V3 specs (= the type of
`BoundaryGaf02ChainE.toChain`; register: `0 < T` from `1600·10⁶Δ ≤ T`, `e < 1/40`). -/
theorem BoundaryGaf02Chain.zsp01_ZI_actualSlotsV2_BGR
    {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ
      W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
    {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
    {Ξ c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
    (C : BoundaryGaf02Chain DP.toBoundaryAugmentedData Kj Ξ Sg eg c cw bcut bder κ)
    (hT : 0 < T) (he : e < 1 / 40) (k : S.ZeroIdx_BAUGC) {p : W.Carrier}
    (hρ : 200 * S.zeroRadius_BAUGC k / T < S.rho p) :
    S.zeroBlockCLM_BAUGC k (S.boundaryOriginalMap p) = 0 ∧
      S.zeroBlockCLM_BAUGC k (C.g₁ p) = 0 ∧ S.zeroBlockCLM_BAUGC k (C.g₂ p) = 0 ∧
      S.zeroBlockCLM_BAUGC k (C.E p) = 0 :=
  C.zsp01_ZI_V3_BGR (fun st => (actualSlotsV2_stageCore_BAUGD S st).superset) k
    (fun st => zeroTag_mem_stageTagsV2_BGR S st k) hT he hρ

/-- **ZSP01 (ZE) on every chain over the ACTUAL slot v2** with the V3 specs. -/
theorem BoundaryGaf02Chain.zsp01_ZE_actualSlotsV2_BGR
    {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ
      W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
    {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
    {Ξ c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
    (C : BoundaryGaf02Chain DP.toBoundaryAugmentedData Kj Ξ Sg eg c cw bcut bder κ)
    (hT : 0 < T) (he : e < 1 / 40) (k : S.ZeroIdx_BAUGC) (p : W.Carrier) :
    (∀ j : Fin 4, ‖S.zeroBlockCLM_BAUGC k (C.stage j p - S.boundaryOriginalMap p)‖ <
      200 * c 2 / T * S.zeroRadius_BAUGC k) ∧
    ∀ z ∈ segment ℝ (S.boundaryOriginalMap p) (C.E p),
      ‖S.zeroBlockCLM_BAUGC k (z - S.boundaryOriginalMap p)‖ <
        200 * c 2 / T * S.zeroRadius_BAUGC k :=
  C.zsp01_ZE_V3_BGR (fun st => (actualSlotsV2_stageCore_BAUGD S st).superset) k
    (fun st => zeroTag_mem_stageTagsV2_BGR S st k) hT he p

end DifferentialGeometry.Geometry.Collapse
