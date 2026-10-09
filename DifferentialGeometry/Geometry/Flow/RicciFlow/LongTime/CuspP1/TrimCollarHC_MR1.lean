import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ClosedRankHC_KP
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.TrimCollarMR1

/-!
# S-MY-R1 consumer：外审 Lemma R1（G1–G4）在 `_HC2` confined Morrey disk 上的实例化

`closed_rank_of_HC_clauses_KP`（K16a，ported）给出 `_HC2` 的 Morrey disk `q : C(closedDisk, U)` 的
任意 smooth extension `Q` 在整个闭盘上是浸入，且 `ι.comp q` 的 extension `Subtype.val ∘ Q` 同样
（K16b 内部浸入 + K16a 边界）。配合 `_HC2` 的两条 clause

* `hneg`：`ρ ((ι.comp q) z) < 0`（`‖z‖ < 1`），
* `hbd`：`ρ ((ι.comp q) (diskBoundary θ)) = 0`，

得 `hseparate`（内部不碰边界曲线 `γU`），于是通用版 `lemma_R1_MR1`（`Plateau/TrimCollarMR1`）适用：
G1 collar `ρ₀`、G2 trimmed disk、G3 collision 的统一 `ε` 分离、G4 一致 fiber 基数界。
`ι.comp q`（落在 ambient carrier 里的版本）的 G1 / G3 / G4 对 `Subtype.val ∘ Q` 直接适用。

只有 compact collision relation + 有限重数；**不**声称 collision 集是有限图。
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

/-- Lemma R1 on the clauses of `exists_eventual_confined_morrey_disk_HC2`：
(1) 对 `U` 值的 Morrey disk `q`：`∃ ρ₀ ∈ (0,1)`，G1 collar、G2 trimmed disk（边界 smooth
embedded、仍是 `G` 下的 Morrey disk、内部像与边界像不交）、G3 `ε`、G4 `m`；
(2) 对 ambient 值的 `ι.comp q`（即 `Subtype.val ∘ q`）：G1 collar、G3 `ε`、G4 `m`。 -/
theorem trim_collar_of_HC_clauses_MR1
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
      (∀ θ : loopCircle, ρ ((ι.comp q) (diskBoundary θ)) = 0) →
      (∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ρ ((ι.comp q) z) < 0) →
      (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ρ₀ < 1 ∧
        (∀ z w : closedDisk, ρ₀ < ‖(z : ℂ)‖ → q z = q w → z = w) ∧
        (∀ r : ℝ, ρ₀ < r → r < 1 →
          IsSmoothEmbeddedLoop (E := EuclideanSpace ℝ (Fin 3))
            (diskTrace (affineSubdisk q 0 r)) ∧
          IsMorreyDisk G (diskTrace (affineSubdisk q 0 r)) (affineSubdisk q 0 r) ∧
          Disjoint (affineSubdisk q 0 r '' {z : closedDisk | ‖(z : ℂ)‖ < 1})
            (affineSubdisk q 0 r '' {z : closedDisk | ‖(z : ℂ)‖ = 1})) ∧
        (∃ ε : ℝ, 0 < ε ∧
          ∀ x y : closedDisk, x ≠ y → q x = q y → ε ≤ dist (x : ℂ) (y : ℂ)) ∧
        ∃ m : ℕ, ∀ p : U, (q ⁻¹' {p}).Finite ∧ (q ⁻¹' {p}).ncard ≤ m) ∧
      (∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ρ₀ < 1 ∧
        (∀ z w : closedDisk, ρ₀ < ‖(z : ℂ)‖ → (ι.comp q) z = (ι.comp q) w → z = w) ∧
        (∃ ε : ℝ, 0 < ε ∧ ∀ x y : closedDisk, x ≠ y → (ι.comp q) x = (ι.comp q) y →
          ε ≤ dist (x : ℂ) (y : ℂ)) ∧
        ∃ m : ℕ, ∀ p : (postStage F.observation t).Carrier,
          ((ι.comp q) ⁻¹' {p}).Finite ∧ ((ι.comp q) ⁻¹' {p}).ncard ≤ m) := by
  intro U δ hδ hU G ι γU q hsm hMor hbd hneg
  obtain ⟨⟨Q, hQ⟩, hall⟩ := closed_rank_of_HC_clauses_KP t a ha ρ hρ hcvx γU q hsm hMor hbd
  obtain ⟨hQι, hrank⟩ := hall Q hQ
  have hγzero : ∀ θ : loopCircle, ρ (γU θ : (postStage F.observation t).Carrier) = 0 :=
    fun θ => boundary_zero_of_weak_trace_KP
      (fun x : U => ρ (x : (postStage F.observation t).Carrier)) hMor.trace hbd θ
  have hsep : ∀ z : closedDisk, ‖(z : ℂ)‖ < 1 → ∀ θ : loopCircle, q z ≠ γU θ := by
    intro z hz θ hqz
    have h1 := hneg z hz
    have h2 : ρ ((ι.comp q) z) = ρ (γU θ : (postStage F.observation t).Carrier) :=
      congrArg (fun x : U => ρ (x : (postStage F.observation t).Carrier)) hqz
    rw [hγzero θ] at h2
    exact absurd h2 (ne_of_lt h1)
  have hrankU : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) Q z) := fun z hz => (hrank z hz).1
  have hrankA : ∀ z ∈ Metric.closedBall (0 : ℂ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, ℂ) (𝓡 3) (Subtype.val ∘ Q) z) := fun z hz => (hrank z hz).2
  have hsingle := hQ.boundary_singleton_MR1 hsm hMor.trace
    (fun z hz => hrankU z (Metric.sphere_subset_closedBall hz)) hsep
  refine ⟨?_, ?_⟩
  · obtain ⟨ρ₀, hρ₀, hρ₀1, hcol, htrim, hε, hm⟩ :=
      lemma_R1_MR1 hMor hsm hQ hrankU hsep
    exact ⟨ρ₀, hρ₀, hρ₀1, hcol, htrim, hε, hm⟩
  · have hsingleA : ∀ z : closedDisk, ‖(z : ℂ)‖ = 1 → ∀ w, (ι.comp q) w = (ι.comp q) z → w = z :=
      fun z hz w hw => hsingle z hz w (Subtype.val_injective hw)
    obtain ⟨ρ₀, hρ₀, hρ₀1, hcol⟩ := hQι.exists_singleton_collar_MR1 hsingleA hrankA
    exact ⟨ρ₀, hρ₀, hρ₀1, hcol, hQι.collision_separation_MR1 hrankA,
      hQι.fiber_card_le_MR1 hrankA⟩

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g} {K : ℕ}
  {cores : PersistentHyperbolicCores F K}

/-- Consumer：对所有足够晚的 `T ≤ t`，`_HC2` 给出的 confined Morrey disk `q`（落在 exterior
region 里）满足 Lemma R1：`ρ₀ ∈ (0,1)` collar、`ε`-分离、一致 fiber 基数界 `m`。 -/
example (M : PrescribedCuspMeridianTop_CPQ cores) (tmin : ℝ) :
    ∃ T₀ : ℝ, M.exterior.start ≤ T₀ ∧ ∀ (T : ℝ) (_ : T₀ ≤ T) (t : ℝ) (_ : T ≤ t),
      ∃ (U : Opens (postStage F.observation t).Carrier) (q : C(closedDisk, U)),
        range (((⟨Subtype.val, continuous_subtype_val⟩ :
          C(U, (postStage F.observation t).Carrier))).comp q) ⊆ M.exterior.region t ∧
        ∃ (ρ₀ ε : ℝ) (m : ℕ), 0 < ρ₀ ∧ ρ₀ < 1 ∧
          (∀ z w : closedDisk, ρ₀ < ‖(z : ℂ)‖ → q z = q w → z = w) ∧
          0 < ε ∧ (∀ x y : closedDisk, x ≠ y → q x = q y → ε ≤ dist (x : ℂ) (y : ℂ)) ∧
          ∀ p : U, (q ⁻¹' {p}).Finite ∧ (q ⁻¹' {p}).ncard ≤ m := by
  obtain ⟨a, ha, T₀, h₀, -, -, hH⟩ := M.exists_eventual_confined_morrey_disk_HC2 tmin
  refine ⟨T₀, h₀, fun T h t ht => ?_⟩
  obtain ⟨ρ, hρ, -, -, hcvx, γU, q, -, hsm, hMor, hrange, -, hneg, hbd, -, -⟩ := hH T h t ht
  obtain ⟨⟨ρ₀, hρ₀, hρ₀1, hcol, -, ⟨ε, hε, hsep⟩, m, hm⟩, -⟩ :=
    trim_collar_of_HC_clauses_MR1 t a ha ρ hρ hcvx γU q hsm hMor hbd hneg
  exact ⟨_, q, hrange, ρ₀, ε, m, hρ₀, hρ₀1, hcol, hε, hsep, hm⟩

end GC.LongTime.CuspP1
