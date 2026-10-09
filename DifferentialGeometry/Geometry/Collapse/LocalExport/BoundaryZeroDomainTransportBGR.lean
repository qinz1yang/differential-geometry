import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryZeroDomainBindingBGR
import DifferentialGeometry.Geometry.Collapse.LocalExport.BoundaryCuspCoreFlowW

/-!
# BCG07 F3, step Z3: the supported ZSP02 isotopy on the boundary carrier `W` (lane B-BCG-ROWS)

Blueprint `master207B.tex`, BCG07 (B:9518–9524): "Apply its ambient isotopy there and extend by
identity near `∂M`. Thus these are the actual `Z_i`, not separately chosen replacement cores."
The ported supported kernel `zsp02_supported_isotopy_kernel_ZSP35_BGR` gives a compactly supported
diffeomorphism of `(W°, ĝ)`; BCG6-Kb's `extendDiffeomorph_BCG6K` extends it by the identity to a
diffeomorphism of `W` (identity near `∂W`).

* **`BoundarySupply.zsp02_transport_W_BGR`** (kernel form, the analytic inputs of the closed
  ZSP02 kernel for an arbitrary smooth `f` on `W°`: (ZE) `δ₀ < 1/1000`, `‖df − d𝓔⁰‖ ≤ H|·|_ĝ`,
  `H < 1/100`): a diffeomorphism `Ψ` of `W`, the identity off `val '' K'` with `K'` compact in the
  thin annulus `{.39 < η_k < .41}`, carrying `val '' {η_k ≤ .4}` onto `val '' zspDomain(f)` and
  `val '' {η_k = .4}` onto `val '' zspFace(f)`.
* **`BoundaryGaf02Chain.zsp02_transport_chain_BGR`**: for `f = pr_int ∘ C.E ∘ val`, the same `Ψ`
  carries the ORIGINAL model sublevel / level of `η_k` onto BIFACEc's actual zero domain / face of
  `C.E` (G12's identities) — BIFACEc's `transport` field, given the derivative input of A3c.
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

/-- **ZSP02's supported isotopy on the boundary carrier** (kernel form): for every smooth `f` on
`W°` with ZSP01's (ZE) at the zero index `k` (`δ₀ < 1/1000`) and the derivative input
`‖df − d𝓔⁰‖ ≤ H|·|_ĝ` (`H < 1/100`), a diffeomorphism `Ψ` of `W`, the identity off `val '' K'`
(`K'` compact in `{.39 < η_k < .41}`), carries `val '' {η_k ≤ .4}` onto `val '' zspDomain(f)` and
`val '' {η_k = .4}` onto `val '' zspFace(f)`. Register: `0 ≤ Λ`, `0 < Δ`, `μ, τ ≤ 1/100`,
`100ΔΛ ≤ 1/100` (smoothness of `𝓔⁰`), `εr < 1/2`, `e < 1/40`. -/
theorem BoundarySupply.zsp02_transport_W_BGR
    (S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ
      W g δn n B oM) (k : S.ZeroIdx_BAUGC) (hΛ : 0 ≤ Λ) (hΔ : 0 < Δ) (hμ : μ ≤ 1 / 100)
    (hτ : τ ≤ 1 / 100) (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hεr : εr < 1 / 2) (he : e < 1 / 40)
    (f : W.pieceInterior ⊤ → BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²))
    (hf : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²)) ∞ f)
    {δ₀ : ℝ} (hδ₀ : δ₀ < 1 / 1000)
    (hZE : letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      letI := S.family.instMetricN
      letI := S.family.instChartedN
      letI := S.family.instMetricC
      ∀ p, ‖f p (.inr (.inr (.inr (.inl k)))) -
        cgpGlobalMap_BAUGP S.family.toLocalPacketsOnB S.family.zero p
          (.inr (.inr (.inr (.inl k))))‖ <
      δ₀ * (S.family.zero.zero k.1 ((Set.Finite.mem_toFinset _).mp k.2)).radius)
    {Hd : ℝ} (hHd : Hd < 1 / 100)
    (hder : letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      letI := S.family.instMetricN
      letI := S.family.instChartedN
      letI := S.family.instMetricC
      ∀ p (v : TangentSpace 𝓘(ℝ, E3) p),
      ‖mvfderiv 𝓘(ℝ, E3) f p v -
          mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap_BAUGP S.family.toLocalPacketsOnB S.family.zero) p v‖ ≤
        Hd * Real.sqrt (S.completion.metric.inner p v v)) :
    letI := inducedMetricSpace S.completion.metric
    letI := S.completion.complete
    letI := S.family.instMetricN
    letI := S.family.instChartedN
    letI := S.family.instMetricC
    ∃ (K' : Set (W.pieceInterior ⊤)) (Ψ : W.Carrier ≃ₘ⟮W.model, W.model⟯ W.Carrier),
      IsCompact K' ∧
      (∀ x ∈ K', 39 / 100 < S.zeroRadial_BIFc k x ∧ S.zeroRadial_BIFc k x < 41 / 100) ∧
      (∀ y, y ∉ Subtype.val '' K' → Ψ y = y) ∧
      Ψ '' (Subtype.val '' {q | S.zeroRadial_BIFc k q ≤ 2 / 5}) =
        Subtype.val '' zspDomain_ZSP35_BGR S.family.toLocalPacketsOnB S.family.zero k f ∧
      Ψ '' (Subtype.val '' {q | S.zeroRadial_BIFc k q = 2 / 5}) =
        Subtype.val '' zspFace_ZSP35_BGR S.family.toLocalPacketsOnB S.family.zero k f := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  have hF : ContMDiff 𝓘(ℝ, E3) 𝓘(ℝ, BlockSpace (fun _ : S.IntTag_BAUGA => ℝ²)) ∞
      (cgpGlobalMap_BAUGP S.family.toLocalPacketsOnB S.family.zero) := by
    rw [← S.interiorMapOn_eq_cgpGlobalMap_BAUGP]
    exact S.contMDiff_interiorMapOn_BAUGP hΛ hΔ hμ hτ hΔΛ (by linarith only [he])
  obtain ⟨K', Φ, hK', hK'a, -, -, hΦid, hdom, hface⟩ :=
    zsp02_supported_isotopy_kernel_ZSP35_BGR S.family.toLocalPacketsOnB S.family.zero k f hf hF
      hδ₀ hZE hHd hder hεr he (isCompact_zeroAnnulus_BGR S k)
  have hid : ∀ x, x ∉ K' → Φ 1 x = x := fun x hx => hΦid 1 x hx
  refine ⟨K', extendDiffeomorph_BCG6K (Φ 1) hK' hid, hK', hK'a, fun y hy => ?_, ?_, ?_⟩
  · rw [extendDiffeomorph_apply_BCG6K]
    exact extendInterior_eq_self_BCG6K hid hy
  · have himg : ∀ A : Set (W.pieceInterior ⊤),
        extendDiffeomorph_BCG6K (Φ 1) hK' hid '' (Subtype.val '' A) =
          Subtype.val '' (Φ 1 '' A) := fun A => by
      rw [image_image, image_image]
      refine image_congr fun x _ => ?_
      rw [extendDiffeomorph_apply_BCG6K, extendInterior_apply_val_BCG6K]
    rw [himg]
    exact congrArg (Subtype.val '' ·) hdom
  · have himg : ∀ A : Set (W.pieceInterior ⊤),
        extendDiffeomorph_BCG6K (Φ 1) hK' hid '' (Subtype.val '' A) =
          Subtype.val '' (Φ 1 '' A) := fun A => by
      rw [image_image, image_image]
      refine image_congr fun x _ => ?_
      rw [extendDiffeomorph_apply_BCG6K, extendInterior_apply_val_BCG6K]
    rw [himg]
    exact congrArg (Subtype.val '' ·) hface

/-- **ZSP02's transport onto the ACTUAL zero domain of the boundary chain** (BIFACEc's `transport`
field; the chain binding of `zsp02_transport_W_BGR` with `f = pr_int ∘ C.E ∘ val`: smoothness
from A3a, (ZE) from ZSP01 on the chain (G9) with `δ₀ = 200c₃/T < 1/1000`, the face / domain
identities of G12). The one remaining analytic input is the derivative estimate `hder` of A3c
(`‖d(pr_int C.E ∘ val) − d𝓔⁰‖ ≤ H|·|_ĝ`, `H < 1/100`). -/
theorem BoundaryGaf02Chain.zsp02_transport_chain_BGR
    {S : BoundarySupply K A β βd εN Λ w Δ σs σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V vs ζ Λz θ
      W g δn n B oM} {Γ Sg eg : Fin 3 → ℝ}
    {DP : BoundaryAugmentedDataPV3 S (actualSlotsV2_BAUGD S) Γ Sg eg} {Kj : ℕ}
    {Ξ c cw : Fin 3 → ℝ} {bcut bder κ : ℝ}
    (C : BoundaryGaf02Chain DP.toBoundaryAugmentedData Kj Ξ Sg eg c cw bcut bder κ)
    (hΛ : 0 ≤ Λ) (hΔ : 1 ≤ Δ) (hμ : μ ≤ 1 / 100) (hτ : τ ≤ 1 / 100)
    (hΔΛ : 100 * Δ * Λ ≤ 1 / 100) (hV : 0 ≤ V) (hβ1 : 0 < β 1) (hb : 0 < b) (he : e < 1 / 40)
    (hT : 1600 * (1000000 * Δ) ≤ T) (hεr : εr < 1 / 2) (k : S.ZeroIdx_BAUGC) {Hd : ℝ}
    (hHd : Hd < 1 / 100)
    (hder : letI := inducedMetricSpace S.completion.metric
      letI := S.completion.complete
      letI := S.family.instMetricN
      letI := S.family.instChartedN
      letI := S.family.instMetricC
      ∀ p (v : TangentSpace 𝓘(ℝ, E3) p),
      ‖mvfderiv 𝓘(ℝ, E3) C.zeroBindMap_BGR p v -
          mvfderiv 𝓘(ℝ, E3) (cgpGlobalMap_BAUGP S.family.toLocalPacketsOnB S.family.zero) p v‖ ≤
        Hd * Real.sqrt (S.completion.metric.inner p v v)) :
    ∃ Ψ : W.Carrier ≃ₘ⟮W.model, W.model⟯ W.Carrier,
      Ψ '' (Subtype.val '' {q | S.zeroRadial_BIFc k q ≤ 2 / 5}) = C.actualZeroDomain_BIFc k ∧
      Ψ '' (Subtype.val '' {q | S.zeroRadial_BIFc k q = 2 / 5}) = C.actualZeroFace_BIFc k := by
  let _ := inducedMetricSpace S.completion.metric
  let _ := S.completion.complete
  let _ := S.family.instMetricN
  let _ := S.family.instChartedN
  let _ := S.family.instMetricC
  have hΔ0 : 0 < Δ := by linarith only [hΔ]
  have hT1 : 1 ≤ T := by nlinarith only [hT, hΔ]
  have hT0 : 0 < T := by linarith only [hT1]
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hc2, -⟩ := C.numbers
  have hc20 : 0 ≤ c 2 := (C.c_pos_mono_V3_BGR.1.le.trans C.c_pos_mono_V3_BGR.2.1).trans
    C.c_pos_mono_V3_BGR.2.2
  have hδ₀ : 200 * c 2 / T < 1 / 1000 := by
    rw [div_lt_iff₀ hT0]
    nlinarith only [hc2, hc20, hT, hΔ]
  obtain ⟨-, Ψ, -, -, -, hdom, hface⟩ := S.zsp02_transport_W_BGR k hΛ hΔ0 hμ hτ hΔΛ hεr he
    C.zeroBindMap_BGR
    (C.contMDiff_zeroBindMap_BGR hΛ hΔ0 hμ hτ hΔΛ hV hβ1 hb (by linarith only [he]))
    hδ₀ (C.zeroBind_ZE_BGR hT0 he k) hHd hder
  refine ⟨Ψ, ?_, ?_⟩
  · rw [hdom, C.actualZeroDomain_eq_image_BGR hT1 he k]
  · rw [hface, C.actualZeroFace_eq_image_BGR hT1 he k]

end DifferentialGeometry.Geometry.Collapse
