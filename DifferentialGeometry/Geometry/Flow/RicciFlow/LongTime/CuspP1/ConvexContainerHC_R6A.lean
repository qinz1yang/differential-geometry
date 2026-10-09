import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.TrimCollarHC_MR1
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.ConvexContainerR6A

/-!
# S-MY-R6A consumer：外审 R6a 在 `_HC2` confined Morrey disk 上的实例化

`exists_eventual_confined_morrey_disk_HC2` 的 clause：`ρ` 光滑、`closure {ρ < a}` 紧、`hcvx`
（`{0 ≤ ρ < a}` 上 `dρ ≠ 0` + **全** Hessian 正定）、Morrey disk `q : C(closedDisk, U)`、
`ρ (ι q z) < 0`（`‖z‖ < 1`）、`ρ (ι q ∂) = 0`。

* `trim_collar_of_HC_clauses_MR1`（S-MY-R1）给 collar `ρ₀ ∈ (0,1)`：`ρ₀ < r < 1` 时
  `q_r = affineSubdisk q 0 r` 的 trace smooth embedded，且 `q_r` 仍是 Morrey disk。
* `strictly_convex_container_R6A` 以 `S := range (ι ∘ q_r)`（紧：闭盘紧 + 连续；预连通：闭盘连通；
  `ρ < 0`：`|r z| ≤ r < 1` + `hneg`）实例化，输出 design `strictly_convex_container_MYD2` 的结论：
  `b δ > 0`，`S ⊆ {ρ < −b−δ}`，层 `[−b−δ, −b]` 全 Hessian 严格凸 + `dρ ≠ 0`，
  `K_{x₀} := connectedComponentIn {ρ ≤ −b} x₀` 紧、`S ⊆ interior K_{x₀}`、`frontier ⊆ {ρ = −b}`。
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

/-- trimmed 盘 `q_r` 的像：紧、预连通，且在 `‖z‖ < 1` 上 `ρ ∘ q < 0` 时整个像 `ρ < 0`
（`‖r z‖ ≤ r < 1`）。 -/
theorem range_affineSubdisk_R6A {M : Type*} [TopologicalSpace M] {ρ : M → ℝ}
    {q : C(closedDisk, M)} (hneg : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ρ (q z) < 0)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    IsCompact (range (affineSubdisk q 0 r)) ∧ IsPreconnected (range (affineSubdisk q 0 r)) ∧
      ∀ x ∈ range (affineSubdisk q 0 r), ρ x < 0 := by
  refine ⟨isCompact_range (affineSubdisk q 0 r).continuous,
    isPreconnected_range (affineSubdisk q 0 r).continuous, ?_⟩
  rintro _ ⟨z, rfl⟩
  rw [affineSubdisk_zero_eq_MR1 hr0 hr1.le]
  refine hneg _ ?_
  have hz : ‖(z : ℂ)‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using z.property
  change ‖r • (z : ℂ)‖ < 1
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr0]
  nlinarith

/-- 复合 `f ∘ q` 的 trimmed 盘就是 `f ∘ q_r`（`ι ∘ q_r`：`U` 里的盘看成 ambient 里的盘）。 -/
theorem affineSubdisk_comp_R6A {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
    (f : C(M, N)) (q : C(closedDisk, M)) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    affineSubdisk (f.comp q) 0 r = f.comp (affineSubdisk q 0 r) := by
  ext z
  rw [ContinuousMap.comp_apply, affineSubdisk_zero_eq_MR1 hr0 hr1,
    affineSubdisk_zero_eq_MR1 hr0 hr1]
  rfl

/-- **R6a 在 `_HC2` 条款上的实例**：binder 前缀 `t a ha ρ hρ hcvx` 与 `let U δ hδ hU G ι`
同 `trim_collar_of_HC_clauses_MR1` 逐字相同，另带 `_HC2` 的紧性条款 `hcpt`。
`ρ₀` 是 R1 的 collar；`ρ₀ < r < 1` 时 (1) `q_r = affineSubdisk q 0 r` 是 `G`-Morrey disk 且 trace
smooth embedded（R2 / R7-E 的 `Γ`）；(2) `S := range (ι ∘ q_r)` 套 `strictly_convex_container_R6A`：
`∃ b δ > 0`，`S ⊆ {ρ < −b−δ}`（特别地 trace `Γ` 也是），层 `[−b−δ, −b]` 上 `dρ ≠ 0` + 全 Hessian
正定，每个 `x₀ ∈ S` 的 `K := connectedComponentIn {ρ ≤ −b} x₀` 紧、`S ⊆ interior K`、
`frontier K ⊆ {ρ = −b}`。 -/
theorem convex_container_of_HC_clauses_R6A
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
        (IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3)) (diskTrace (affineSubdisk q 0 r)) ∧
          IsMorreyDisk G (diskTrace (affineSubdisk q 0 r)) (affineSubdisk q 0 r)) ∧
        ∃ b δ' : ℝ, 0 < b ∧ 0 < δ' ∧
          (∀ z : closedDisk, ρ ((ι.comp (affineSubdisk q 0 r)) z) < -b - δ') ∧
          (∀ x, -b - δ' ≤ ρ x → ρ x ≤ -b →
            mfderiv (𝓡 3) 𝓘(ℝ) ρ x ≠ 0 ∧
              ∀ v : TangentSpace (𝓡 3) x, v ≠ 0 →
                0 < hessFun (postMetric F.observation t) ρ x v v) ∧
          ∀ x₀ ∈ range (ι.comp (affineSubdisk q 0 r)),
            IsCompact (connectedComponentIn {x | ρ x ≤ -b} x₀) ∧
            range (ι.comp (affineSubdisk q 0 r)) ⊆
              interior (connectedComponentIn {x | ρ x ≤ -b} x₀) ∧
            frontier (connectedComponentIn {x | ρ x ≤ -b} x₀) ⊆ {x | ρ x = -b} := by
  intro U δ hδ hU G ι γU q hsm hMor hbd hneg
  obtain ⟨⟨ρ₀, hρ₀, hρ₀1, -, htrim, -⟩, -⟩ :=
    trim_collar_of_HC_clauses_MR1 t a ha ρ hρ hcvx γU q hsm hMor hbd hneg
  refine ⟨ρ₀, hρ₀, hρ₀1, fun r hr hr1 => ?_⟩
  obtain ⟨hloop, hmor, -⟩ := htrim r hr hr1
  have hr0 : 0 ≤ r := (hρ₀.trans hr).le
  refine ⟨⟨hloop, hmor⟩, ?_⟩
  obtain ⟨hS, hSconn, hSneg⟩ := range_affineSubdisk_R6A (ρ := ρ) (q := ι.comp q) hneg hr0 hr1
  rw [affineSubdisk_comp_R6A ι q hr0 hr1.le] at hS hSconn hSneg
  obtain ⟨b, δ', hb, hδ', hSb, hlayer, hcomp⟩ :=
    strictly_convex_container_R6A (postMetric F.observation t) hρ ha hcpt hcvx hS hSconn hSneg
  exact ⟨b, δ', hb, hδ', fun z => hSb _ ⟨z, rfl⟩, hlayer, hcomp⟩

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- Consumer：对所有足够晚的 `T ≤ t`，`_HC2` 给出的 confined Morrey disk 经 R1 trim（`ρ₀ < r < 1`）
后，trimmed 盘的像 `S` 与 trace `Γ` 落在 `{ρ < −b−δ}`，`K := {ρ ≤ −b}` 里含 `S` 的连通分量紧、
`S ⊆ interior K`、`frontier K ⊆ {ρ = −b}`，层 `[−b−δ, −b]` 全 Hessian 严格凸 + `dρ ≠ 0`
——正是 design R7-E 的 `hb hδ hK hKρ hfr hΓρ` 与 R6b 的 `hconv` 的陈述形。 -/
example (M : PrescribedCuspMeridianTop_CPQ cores) (tmin : ℝ) :
    ∃ T₀ : ℝ, M.exterior.start ≤ T₀ ∧ ∀ (T : ℝ) (_ : T₀ ≤ T) (t : ℝ) (_ : T ≤ t),
      ∃ (ρ : (postStage F.observation t).Carrier → ℝ) (_ : ContMDiff (𝓡 3) 𝓘(ℝ, ℝ) ∞ ρ)
        (b δ : ℝ) (K : Set (postStage F.observation t).Carrier)
        (Γ : freeLoop (postStage F.observation t).Carrier),
        0 < b ∧ 0 < δ ∧ IsCompact K ∧ K ⊆ {x | ρ x ≤ -b} ∧ frontier K ⊆ {x | ρ x = -b} ∧
        (∀ θ : loopCircle, ρ (Γ θ) < -b - δ ∧ Γ θ ∈ interior K) ∧
        ∀ x, -b - δ ≤ ρ x → ρ x ≤ -b →
          mfderiv (𝓡 3) 𝓘(ℝ) ρ x ≠ 0 ∧
            ∀ v : TangentSpace (𝓡 3) x, v ≠ 0 →
              0 < hessFun (postMetric F.observation t) ρ x v v := by
  obtain ⟨a, ha, T₀, h₀, -, -, hH⟩ := M.exists_eventual_confined_morrey_disk_HC2 tmin
  refine ⟨T₀, h₀, fun T h t ht => ?_⟩
  obtain ⟨ρ, hρ, -, hcpt, hcvx, γU, q, -, hsm, hMor, -, -, hneg, hbd, -, -⟩ := hH T h t ht
  obtain ⟨ρ₀, hρ₀, hρ₀1, hr⟩ :=
    convex_container_of_HC_clauses_R6A t a ha ρ hρ hcpt hcvx γU q hsm hMor hbd hneg
  have hr1 : ρ₀ < (ρ₀ + 1) / 2 := by linarith
  have hr2 : (ρ₀ + 1) / 2 < 1 := by linarith
  obtain ⟨-, b, δ, hb, hδ, hSb, hlayer, hcomp⟩ := hr _ hr1 hr2
  obtain ⟨hKcpt, hSK, hfr⟩ := hcomp _ ⟨0, rfl⟩
  refine ⟨ρ, hρ, b, δ, _, diskTrace ((⟨Subtype.val, continuous_subtype_val⟩ :
    C(_, (postStage F.observation t).Carrier)).comp (affineSubdisk q 0 ((ρ₀ + 1) / 2))),
    hb, hδ, hKcpt, ?_, hfr, fun θ => ⟨hSb (diskBoundary θ), hSK ⟨diskBoundary θ, rfl⟩⟩, hlayer⟩
  exact connectedComponentIn_subset _ _

end GC.LongTime.CuspP1
