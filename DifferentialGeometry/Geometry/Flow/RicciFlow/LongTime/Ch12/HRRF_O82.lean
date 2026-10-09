import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.OpenImage_O82
import DifferentialGeometry.Geometry.Collapse.InducedVolumeComparison

set_option autoImplicit false

/-! # CH12-O82 G2: `hRRF_O82` — late right regularisation of a single old model

Statement = `[FROZEN] CH12-O75 hRRF` (binder of `hRRlate_of_hRRF_frozen_O75`,
`build-logs/ch12/scratch/FrozenO75v5.lean`), verbatim.  For `ρ ≤ 0` the ball is empty.  Otherwise
`T` is chosen with `α t < 1 / (ρ + 2)` (so `α t < 1` and `B(ρ + 1) ⊆ B(2 (α t)⁻¹)`); at a fixed
late time `t`, every `z₀` of the compact closed ball `B̄(ρ)` carries a persistent patch (8th
conjunct), whose spatial differential is injective (`patch_inj_S145` + `hlow_S145`), so
`patch_rr_O82` gives the claim near `(t, z₀)`; compactness of `B̄(ρ)` gives a uniform `δ`. -/

noncomputable section
open Set Filter Topology DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Collapse
open Manifold GC.LongTime
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12
universe u

/-- `[FROZEN] CH12-O75 hRRF`, proved (no binder). -/
theorem hRRF_O82 {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g) :
    ∀ (H₀ : FiniteVolumeHyperbolicModel.{u}) (s₀ : ℝ) (_hs₀ : 0 < s₀) (K : ℕ) (α : ℝ → ℝ)
      (Ω : TopologicalSpace.Opens (ℝ × H₀.Carrier))
      (m₀ : ∀ t : ℝ, s₀ ≤ t → H₀.Carrier → (postStage F.observation t).Carrier),
      ((∀ t, s₀ ≤ t → 0 < α t) ∧ AntitoneOn α (Ici s₀) ∧
      (∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → α t < ε) ∧
      (∀ t (ht : s₀ ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (m₀ t ht) (sourceSlice_CX5 Ω t)) ∧
      (∀ t (ht : s₀ ≤ t),
        IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : sourceSlice_CX5 Ω t => m₀ t ht x)) ∧
      (∀ t, s₀ ≤ t →
        riemannianBallOf H₀.metric H₀.basepoint (2 * (α t)⁻¹) ⊆ sourceSlice_CX5 Ω t) ∧
      (∀ t (ht : s₀ ≤ t), ∀ k : ℕ, k ≤ max K ⌈(α t)⁻¹⌉₊ →
        ∀ p ∈ riemannianBallOf H₀.metric H₀.basepoint (2 * (α t)⁻¹),
          ckErr_S45 H₀ (postMetric F.observation t) t⁻¹ (m₀ t ht) k p < α t) ∧
      (∀ t (_ht : s₀ ≤ t), ∀ x ∈ sourceSlice_CX5 Ω t,
        Nonempty (PersistentModelPatch F H₀ s₀ α (sourceSlice_CX5 Ω) m₀ t x))) →
      ∀ ρ : ℝ, ∃ T : ℝ, ∀ (t : ℝ) (hi : s₀ ≤ t), T ≤ t → ∃ δ : ℝ, 0 < δ ∧
        ∀ (s : ℝ) (hs : s₀ ≤ s), t ≤ s → s < t + δ →
        postStage F.observation t = postStage F.observation s →
        ∀ (x : (postStage F.observation t).Carrier) (y : (postStage F.observation s).Carrier),
          HEq x y →
          y ∈ m₀ s hs '' riemannianBallOf H₀.metric H₀.basepoint ρ →
          x ∈ m₀ t hi '' riemannianBallOf H₀.metric H₀.basepoint (ρ + 1) := by
  intro H₀ s₀ _ K α Ω m₀ hb ρ
  obtain ⟨hαpos, -, hαlim, -, -, hball, hck, hpat⟩ := hb
  by_cases hρ : ρ ≤ 0
  · refine ⟨0, fun t _ _ => ⟨1, one_pos, ?_⟩⟩
    intro s hs _ _ _ x y _ hy
    exfalso
    obtain ⟨z, hz, -⟩ := hy
    have hz' : riemannianEDistOf H₀.metric H₀.basepoint z < ENNReal.ofReal ρ := hz
    rw [ENNReal.ofReal_of_nonpos hρ] at hz'
    exact ENNReal.not_lt_zero hz'
  push Not at hρ
  obtain ⟨T, hT⟩ := hαlim (1 / (ρ + 2)) (by positivity)
  refine ⟨T, fun t hi hTt => ?_⟩
  have hαt := hT t hTt
  have hαp := hαpos t hi
  have hρ2 : 1 / (ρ + 2) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  have hα1 : α t < 1 := hαt.trans hρ2
  have hinv : ρ + 2 < (α t)⁻¹ := by
    rw [lt_inv_comm₀ (by linarith) hαp]
    simpa [one_div] using hαt
  have hrad : ρ + 1 ≤ 2 * (α t)⁻¹ := by linarith
  have hck0 : ∀ t' (ht' : s₀ ≤ t'), ∀ q ∈ riemannianBallOf H₀.metric H₀.basepoint (2 * (α t')⁻¹),
      ckErr_S45 H₀ (postMetric F.observation t') t'⁻¹ (m₀ t' ht') 0 q < α t' :=
    fun t' ht' q hq => hck t' ht' 0 (Nat.zero_le _) q hq
  have hKc : IsCompact (riemannianClosedBallOf H₀.metric H₀.basepoint ρ) :=
    isCompact_riemannianClosedBallOf H₀.complete _ ρ
  have hlt : ENNReal.ofReal ρ < ENNReal.ofReal (ρ + 1) :=
    (ENNReal.ofReal_lt_ofReal_iff (by linarith)).mpr (by linarith)
  have hKB : ∀ z ∈ riemannianClosedBallOf H₀.metric H₀.basepoint ρ,
      z ∈ riemannianBallOf H₀.metric H₀.basepoint (ρ + 1) := fun z hz =>
    lt_of_le_of_lt (show riemannianEDistOf H₀.metric H₀.basepoint z ≤ ENNReal.ofReal ρ from hz) hlt
  have hB2 : riemannianBallOf H₀.metric H₀.basepoint (ρ + 1) ⊆
      riemannianBallOf H₀.metric H₀.basepoint (2 * (α t)⁻¹) :=
    riemannianBallOf_mono _ _ hrad
  have hev : ∀ z₀ ∈ riemannianClosedBallOf H₀.metric H₀.basepoint ρ,
      ∀ᶠ q : ℝ × H₀.Carrier in 𝓝 (t, z₀), t ≤ q.1 → ∀ (hs : s₀ ≤ q.1)
        (x : (postStage F.observation t).Carrier), HEq x (m₀ q.1 hs q.2) →
          x ∈ m₀ t hi '' riemannianBallOf H₀.metric H₀.basepoint (ρ + 1) := by
    intro z₀ hz₀
    have hzB : z₀ ∈ riemannianBallOf H₀.metric H₀.basepoint (2 * (α t)⁻¹) := hB2 (hKB z₀ hz₀)
    obtain ⟨p⟩ := hpat t hi z₀ (hball t hi hzB)
    have hinj := patch_inj_S145 p ⟨t, p.a_nonneg.trans p.before.le, p.after.le.trans p.horizon⟩
      ⟨p.before, p.after⟩ hi p.mem_neighborhood hα1
      (fun w => hlow_S145 F H₀ s₀ m₀ α hck0 hi hzB w)
    exact patch_rr_O82 p hi hinj
      ((isOpen_riemannianBallOf_S61 H₀ (ρ + 1)).mem_nhds (hKB z₀ hz₀))
  have hall := hKc.eventually_forall_of_forall_eventually
    (P := fun s z => t ≤ s → ∀ (hs : s₀ ≤ s) (x : (postStage F.observation t).Carrier),
      HEq x (m₀ s hs z) → x ∈ m₀ t hi '' riemannianBallOf H₀.metric H₀.basepoint (ρ + 1)) hev
  obtain ⟨δ, hδ, hδall⟩ := Metric.eventually_nhds_iff.mp hall
  refine ⟨δ, hδ, fun s hs hts hsδ _ x y hxy hy => ?_⟩
  obtain ⟨z, hz, rfl⟩ := hy
  have hds : dist s t < δ := by
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  have hzK : z ∈ riemannianClosedBallOf H₀.metric H₀.basepoint ρ :=
    le_of_lt (show riemannianEDistOf H₀.metric H₀.basepoint z < ENNReal.ofReal ρ from hz)
  exact hδall hds z hzK hts hs x hxy

end GC.LongTime.Ch12
