import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ConvexContainerHC_R6A
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.CanonicalMetricAgreeMY
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.OpenTargetAdaptersADP

/-!
# S-MY-ADAPT consumer（G1 + G3）：三个 carrier 在 `_HC2` confined Morrey disk 上的串联

`_HC2` 的数据：原 ambient carrier `M_amb = (postStage F.observation t).Carrier`（`hcpt` 在此成立）、
`U = {ρ < a}`（canonical positive-domain metric `G`，Morrey disk `q : C(closedDisk, U)` 在此）。

* R1（`trim_collar_of_HC_clauses_MR1`）给 collar `ρ₀`，`ρ₀ < r < 1` 时 `q_r := affineSubdisk q 0 r` 仍是
  `G`-Morrey disk；
* R6a 在**原 ambient carrier 与原度量 `g`** 上用 G1（`convex_container_carrier_U_ADP`）；`G = g.restrictOpen U`
  在 `K ⊆ {ρ ≤ 0}` 上逐点相等来自 `canonicalPositiveDomainMetric_inner_eq_of_nonpos_MY`（由 cutoff 定义，
  **不是**沿 `q` 的 local metric clause）；
* 搬到 `↥U`：`Kc := val ⁻¹' K` 在 `↥U` 中紧；`K° := interior Kc : Opens ↥U` 含 `range q_r`；
* G3：`q_r` 到 `K°` 的 lift 有闭盘 smooth extension（`smoothDiskExtension_trimmed_liftToOpen_ADP`）。

这就是 R6b（`hK`、`hconv`）、R7-E（`hKρ`、`hfr`）、K° glue G2、R15T-open 共同需要的 carrier 数据的陈述形。
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

/-- **三个 carrier 串联（`_HC2` 实例）**：binder 前缀 `t a ha ρ hρ hcvx` 与 `let U δ hδ hU G ι` 同
`convex_container_of_HC_clauses_R6A` 逐字相同，另带 `_HC2` 的紧性条款 `hcpt`。`ρ₀ < r < 1` 时：
`∃ b δ' > 0`、`↥U` 里的紧集 `Kc`（`= val ⁻¹' K`）与开集 `K° = interior Kc`，使 `range q_r ⊆ K°`、
`Kc ⊆ {ρ ≤ −b}`、`frontier Kc ⊆ {ρ = −b}`、`G = g.restrictOpen U` 在 `Kc` 上逐点成立、层
`[−b−δ', −b]` 对 `G` 与 `ρ ∘ val` 全 Hessian 严格凸 + `dρ ≠ 0`，并且 `q_r` 到 `K°` 的 lift 有闭盘
smooth extension。 -/
theorem carrier_chain_of_HC_clauses_ADP
    {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} (t : ℝ)
    (a : ℝ) (ha : 0 < a)
    (ρ : (postStage F.observation t).Carrier → ℝ) (hρ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ρ)
    (hcpt : IsCompact (closure {x | ρ x < a}))
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
      (∀ θ : loopCircle, ρ ((ι.comp q) (diskBoundary θ)) = 0) →
      (∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ρ ((ι.comp q) z) < 0) →
      ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ρ₀ < 1 ∧ ∀ r : ℝ, ρ₀ < r → r < 1 →
        ∃ (b δ' : ℝ) (Kc : Set U) (O : Opens U), 0 < b ∧ 0 < δ' ∧ IsCompact Kc ∧
          (O : Set U) = interior Kc ∧ Set.range (affineSubdisk q 0 r) ⊆ O ∧
          Kc ⊆ {x : U | ρ (x : (postStage F.observation t).Carrier) ≤ -b} ∧
          frontier Kc ⊆ {x : U | ρ (x : (postStage F.observation t).Carrier) = -b} ∧
          (∀ x ∈ Kc, G.inner x = ((postMetric F.observation t).restrictOpen U).inner x) ∧
          (∀ x : U, -b - δ' ≤ ρ (x : (postStage F.observation t).Carrier) →
            ρ (x : (postStage F.observation t).Carrier) ≤ -b →
            mfderiv (𝓡 3) 𝓘(ℝ)
              (fun y : U => ρ (y : (postStage F.observation t).Carrier)) x ≠ 0 ∧
              ∀ v : TangentSpace (𝓡 3) x, v ≠ 0 →
                0 < hessFun G (fun y : U => ρ (y : (postStage F.observation t).Carrier)) x v v) ∧
          ∃ hO : Set.range (affineSubdisk q 0 r) ⊆ O,
            ∃ V : ℂ → O, SmoothDiskExtension (E := EuclideanSpace ℝ (Fin 3))
              (liftToOpen_AT (affineSubdisk q 0 r) hO) V := by
  intro U δ hδ hU G ι γU q hsm hMor hbd hneg
  obtain ⟨⟨ρ₀, hρ₀, hρ₀1, -, htrim, -⟩, -⟩ :=
    trim_collar_of_HC_clauses_MR1 t a ha ρ hρ hcvx γU q hsm hMor hbd hneg
  refine ⟨ρ₀, hρ₀, hρ₀1, fun r hr hr1 => ?_⟩
  have hr0 : 0 ≤ r := (hρ₀.trans hr).le
  obtain ⟨hS, hSconn, hSneg⟩ := range_affineSubdisk_R6A (ρ := ρ) (q := ι.comp q) hneg hr0 hr1
  rw [affineSubdisk_comp_R6A ι q hr0 hr1.le] at hS hSconn hSneg
  obtain ⟨b, δ', hb, hδ', -, hlayer, hcomp⟩ :=
    convex_container_carrier_U_ADP (postMetric F.observation t) hρ ha hcpt hcvx (U := U) rfl G
      (canonicalPositiveDomainMetric_inner_eq_of_nonpos_MY (postMetric F.observation t) ha hρ)
      hS hSconn hSneg
  obtain ⟨hKc, hSK, hfr, hKb, hKG⟩ := hcomp _ ⟨0, rfl⟩
  have hO : Set.range (affineSubdisk q 0 r) ⊆
      (⟨interior (Subtype.val ⁻¹' connectedComponentIn {x | ρ x ≤ -b}
        (ι.comp (affineSubdisk q 0 r) 0) : Set U), isOpen_interior⟩ : Opens U) := by
    rintro _ ⟨z, rfl⟩
    exact hSK ⟨z, rfl⟩
  obtain ⟨V, hV⟩ := smoothDiskExtension_trimmed_liftToOpen_ADP hMor hr0 hr1 hO
  exact ⟨b, δ', _, _, hb, hδ', hKc, rfl, hO, hKb, hfr, hKG, hlayer, hO, V, hV⟩

end GC.LongTime.CuspP1
