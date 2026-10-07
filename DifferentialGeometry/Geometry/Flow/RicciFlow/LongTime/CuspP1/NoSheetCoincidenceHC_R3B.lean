import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.HMYOfHNT_MYN
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Embeddedness.NoSheetCoincidenceR3B

/-!
# O-MY-R3B G3：`_HC2` 实例——confined Morrey 盘的 coincident germ pairs 为空、无开 sheet 重合

在 `exists_eventual_confined_morrey_disk_HC2` 的 clause 上（与 `hMY_concl_of_hNT_MYN` 同一组 binder：
`hcvx`、smooth embedded `γU`、Morrey 盘 `q`、内部 `ρ < 0`、边界 `ρ = 0`）：

* 闭盘 smooth extension `Q` + 闭盘 rank：K16a/K16b `closed_rank_of_HC_clauses_KP`；
* `hseparate`：`hseparate_of_HC2_MYN`；
* 闭性：树里 `actual_morrey_coincident_germ_pairs_isClosed`；组装：`coincidentGermPairs_eq_empty_R3B`。

结论：`coincidentGermPairs q = ∅`，且 R3b 形式的 no-open-sheet-coincidence 成立。**不**声称 `q` 单射
（横截 collision 仍可能存在；那是 `hNT` / MY-G 的事）。

`no_open_sheet_coincidence_of_HC2_via_contract_R3B` 是第二个 consumer：同一 clause 上把 G2 合同
`no_open_sheet_coincidence_R3B`（无 minimality）的全部前提逐条供出——`hconf`/`hharm` 只取
`IsMorreyDisk` 的 `conformal`/`harmonic` field，`hbdry` 由 `boundary_fiber_eq` + `diskBoundary` 单射，
`hsep` 由 `hseparate_of_HC2_MYN` + weak trace——证明 G2 的前提形状在 `_HC2` 上可满足。
-/

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.LongTime
open DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff Topology

namespace GC.LongTime.CuspP1

universe u

/-- **G3 `_HC2` 实例。** confined Morrey 盘 `q` 的 coincident germ pairs 为空，并且没有两块不交
非空开 `V₁ V₂ ⊆ D°`（`diskExtension q` 在两边单射）有相同的像。 -/
theorem coincidentGermPairs_eq_empty_of_HC2_R3B
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} (t : ℝ)
    (a : ℝ) (ha : 0 < a)
    (ρ : (postStage F.observation t).Carrier → ℝ) (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ρ)
    (hcvx : ∀ x, 0 ≤ ρ x → ρ x < a →
      mfderiv (𝓡 3) 𝓘(ℝ) ρ x ≠ 0 ∧
        ∀ v : TangentSpace (𝓡 3) x, v ≠ 0 →
          0 < hessFun (postMetric F.observation t) ρ x v v) :
    let U : Opens (postStage F.observation t).Carrier :=
      ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
    let δ : (postStage F.observation t).Carrier → ℝ := fun x => cutoff_P2A a (ρ x)
    let hδ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ δ :=
      (cutoff_smooth_P2A a).contMDiff.comp hρ
    let hU : ∀ x : (postStage F.observation t).Carrier, x ∈ U ↔ 0 < δ x :=
      fun x => (cutoff_pos_iff_P2A ha (ρ x)).symm
    let G := canonicalPositiveDomainMetric_P2A (postMetric F.observation t) hδ U hU
    let ι : C(U, (postStage F.observation t).Carrier) :=
      ⟨Subtype.val, continuous_subtype_val⟩
    ∀ (γU : freeLoop U) (q : C(closedDisk, U)),
      IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γU →
      IsMorreyDisk G γU q →
      (∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ρ ((ι.comp q) z) < 0) →
      (∀ θ : loopCircle, ρ ((ι.comp q) (diskBoundary θ)) = 0) →
      coincidentGermPairs (q : closedDisk → U) = ∅ ∧
        ¬ ∃ V₁ V₂ : Set ℂ, IsOpen V₁ ∧ IsOpen V₂ ∧ V₁.Nonempty ∧ V₂.Nonempty ∧
          Disjoint V₁ V₂ ∧ V₁ ⊆ Metric.ball 0 1 ∧ V₂ ⊆ Metric.ball 0 1 ∧
          InjOn (diskExtension q) V₁ ∧ InjOn (diskExtension q) V₂ ∧
          diskExtension q '' V₁ = diskExtension q '' V₂ := by
  intro U δ hδ hU G ι γU q hsm hMor hneg hbd
  obtain ⟨⟨Q, hQ⟩, hall⟩ := closed_rank_of_HC_clauses_KP t a ha ρ hρ hcvx γU q hsm hMor hbd
  have hrank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) Q z) := fun z hz => ((hall Q hQ).2 z hz).1
  have hsep := hseparate_of_HC2_MYN (fun x : U => ρ (x : (postStage F.observation t).Carrier))
    hMor.trace hbd hneg
  have hd3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  have hcgp := coincidentGermPairs_eq_empty_R3B hMor hsm hd3 hQ hrank hsep
  exact ⟨hcgp, no_open_sheet_coincidence_of_coincidentGermPairs_eq_empty_R3B hcgp⟩

/-- `diskBoundary : loopCircle → closedDisk` 单射。 -/
theorem diskBoundary_injective_R3B :
    Function.Injective (diskBoundary : loopCircle → closedDisk) := by
  intro θ θ' h
  have hval : ((diskBoundary θ : closedDisk) : ℂ) = ((diskBoundary θ' : closedDisk) : ℂ) :=
    congrArg Subtype.val h
  apply AddCircle.injective_toCircle (T := (1 : ℝ)) one_ne_zero
  apply Circle.ext
  exact hval

/-- **G3 consumer 2：G2 合同在 `_HC2` 上的实例。** 只用 `IsMorreyDisk` 的 `conformal`/`harmonic`
field 与 trace（不用 `minimizes*`）供出 `no_open_sheet_coincidence_R3B` 的前提。 -/
theorem no_open_sheet_coincidence_of_HC2_via_contract_R3B
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} (t : ℝ)
    (a : ℝ) (ha : 0 < a)
    (ρ : (postStage F.observation t).Carrier → ℝ) (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ρ)
    (hcvx : ∀ x, 0 ≤ ρ x → ρ x < a →
      mfderiv (𝓡 3) 𝓘(ℝ) ρ x ≠ 0 ∧
        ∀ v : TangentSpace (𝓡 3) x, v ≠ 0 →
          0 < hessFun (postMetric F.observation t) ρ x v v) :
    let U : Opens (postStage F.observation t).Carrier :=
      ⟨{x | ρ x < a}, isOpen_lt hρ.continuous continuous_const⟩
    let δ : (postStage F.observation t).Carrier → ℝ := fun x => cutoff_P2A a (ρ x)
    let hδ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ δ :=
      (cutoff_smooth_P2A a).contMDiff.comp hρ
    let hU : ∀ x : (postStage F.observation t).Carrier, x ∈ U ↔ 0 < δ x :=
      fun x => (cutoff_pos_iff_P2A ha (ρ x)).symm
    let G := canonicalPositiveDomainMetric_P2A (postMetric F.observation t) hδ U hU
    let ι : C(U, (postStage F.observation t).Carrier) :=
      ⟨Subtype.val, continuous_subtype_val⟩
    ∀ (γU : freeLoop U) (q : C(closedDisk, U)),
      IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) γU →
      IsMorreyDisk G γU q →
      (∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ρ ((ι.comp q) z) < 0) →
      (∀ θ : loopCircle, ρ ((ι.comp q) (diskBoundary θ)) = 0) →
        ¬ ∃ V₁ V₂ : Set ℂ, IsOpen V₁ ∧ IsOpen V₂ ∧ V₁.Nonempty ∧ V₂.Nonempty ∧
          Disjoint V₁ V₂ ∧ V₁ ⊆ Metric.ball 0 1 ∧ V₂ ⊆ Metric.ball 0 1 ∧
          InjOn (diskExtension q) V₁ ∧ InjOn (diskExtension q) V₂ ∧
          diskExtension q '' V₁ = diskExtension q '' V₂ := by
  intro U δ hδ hU G ι γU q hsm hMor hneg hbd
  obtain ⟨⟨Q, hQ⟩, hall⟩ := closed_rank_of_HC_clauses_KP t a ha ρ hρ hcvx γU q hsm hMor hbd
  have hrank : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) Q z) := fun z hz => ((hall Q hQ).2 z hz).1
  have hsep := hseparate_of_HC2_MYN (fun x : U => ρ (x : (postStage F.observation t).Carrier))
    hMor.trace hbd hneg
  have hd3 : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := finrank_euclideanSpace_fin
  obtain ⟨σ, hσ, htrace⟩ := hMor.trace
  have hboundary := hQ.boundary_fiber_eq hsm hσ htrace
    (fun z hz => hrank z (Metric.sphere_subset_closedBall hz)) hsep
  have hbdry : ∀ θ θ' : loopCircle, q (diskBoundary θ) = q (diskBoundary θ') → θ = θ' :=
    fun θ θ' h => diskBoundary_injective_R3B (hboundary θ' (diskBoundary θ) h)
  have hsep' : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ∀ θ : loopCircle,
      q z ≠ q (diskBoundary θ) := by
    intro z hz θ h
    have hθ : q (diskBoundary θ) = γU (σ θ) := congrArg (fun η : freeLoop U => η θ) htrace
    exact hsep z hz (σ θ) (h.trans hθ)
  exact no_open_sheet_coincidence_R3B hd3 hQ hrank hMor.conformal hMor.harmonic hbdry hsep'

end GC.LongTime.CuspP1
