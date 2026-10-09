import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.NoSheetCoincidenceHC_R3B
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Uniqueness.TrimmedUniquenessR5

/-!
# O-MY-R5 G4（下）：R5 在 `_HC2` clause 上的实例

在 `exists_eventual_confined_morrey_disk_HC2` 的 clause 上（与 `coincidentGermPairs_eq_empty_of_HC2_R3B`
同一组 binder：`hcvx`、smooth embedded `γU`、Morrey 盘 `q`、内部 `ρ < 0`、边界 `ρ = 0`）：
* 闭盘 smooth extension `Q` + 闭盘 rank：K16a/K16b `closed_rank_of_HC_clauses_KP`；
* 边界 singleton fiber：`SmoothDiskExtension.boundary_fiber_eq` + `hseparate_of_HC2_MYN`；
* collar `ρ₀`：`trimmed_disk_MR1`；
* R5 本体：`trimmed_morrey_disk_unique_up_to_mobius_R5`（G4）。
结论：存在 `ρ₀ ∈ (0, 1)`，使任意 `r₂ ∈ (ρ₀, 1)` 与任意 `G`-Morrey 盘 `u`（trace = `diskTrace q_{r₂}`）都满足
`u = q_{r₂} ∘ mob ∨ u = q_{r₂} ∘ mob ∘ conj`，且三点归一 ⇒ `u = q_{r₂}`（R7 `huniq` 在 `_HC2` 上的形状）。
-/

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set TopologicalSpace ComplexConjugate
open DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Operator DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.MinimalSurface
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology GC.Endpoint GC.LongTime
open DifferentialGeometry.Geometry.Hyperbolic
open scoped Manifold ContDiff Topology

namespace GC.LongTime.CuspP1

universe u

/-- **R5 的 `_HC2` 实例**（`huniq` 形状）。 -/
theorem trimmed_morrey_disk_unique_of_HC2_R5
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
      ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ρ₀ < 1 ∧ ∀ r₂ : ℝ, ρ₀ < r₂ → r₂ < 1 →
        ∀ v : C(closedDisk, U), IsMorreyDisk G (diskTrace (affineSubdisk q 0 r₂)) v →
          (∃ a c : ℂ, ‖a‖ < 1 ∧ ‖c‖ = 1 ∧
            ((∀ z : closedDisk, v z = diskExtension (affineSubdisk q 0 r₂) (diskMobius_R5 a c z)) ∨
              (∀ z : closedDisk, v z =
                diskExtension (affineSubdisk q 0 r₂) (diskMobius_R5 a c (conj (z : ℂ)))))) ∧
          ∀ θ : Fin 3 → loopCircle, Function.Injective θ →
            (∀ j, diskTrace v (θ j) = diskTrace (affineSubdisk q 0 r₂) (θ j)) →
            v = affineSubdisk q 0 r₂ := by
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
  have hsingle : ∀ z : closedDisk, ‖(z : ℂ)‖ = 1 → ∀ w, q w = q z → w = z := by
    intro z hz w hw
    obtain ⟨θ, hθ⟩ := exists_diskBoundary_coe_eq_R5 hz
    have hzθ : z = diskBoundary θ := Subtype.ext hθ.symm
    rw [hzθ] at hw ⊢
    exact hboundary θ w hw
  obtain ⟨ρ₀, hρ₀, hρ₀1, hcol, -⟩ := trimmed_disk_MR1 hMor hQ hsingle hrank
  refine ⟨ρ₀, hρ₀, hρ₀1, fun r₂ hr hr1 v hv => ?_⟩
  exact trimmed_morrey_disk_unique_up_to_mobius_R5 hd3 hMor hQ hrank hρ₀ hcol hr hr1 hv

end GC.LongTime.CuspP1
