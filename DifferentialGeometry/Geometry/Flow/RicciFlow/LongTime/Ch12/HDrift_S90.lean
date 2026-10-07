import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MemberOfDrift_S90
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PatchCore_S61
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.TimeSmoothingPatch_CX5

set_option autoImplicit false

/-! # CH12-S90 G3: `hD_S90` — membership half of the slow-patch drift `HDd`

For ONE old model `Hold` with the S4 block of `singleModelExplicit_S72` (accuracy `α ↓ 0`, `mold`
smooth embedding on `sourceSlice_CX5 Ω t`, `B(2/α t) ⊆` source, `ckErr_S45 … k < α t` there):
for every `Rold` and `L > 0` there is `T0` such that for all `r ≥ T0`, every point `y` of the stage
at time `r` that is `L/2`-close (in the rescaled metric `r⁻¹ g_r`) to `mold r q` for some
`q ∈ B(Rold - L)` lies in `mold r '' B(Rold)`.
Only the order-0 clause (`k = 0`) of the `ckErr` block is used. -/

noncomputable section
open Set Filter Topology DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open Manifold GC.LongTime
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12
universe u

theorem hD_S90 {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
    (Hold : FiniteVolumeHyperbolicModel.{u}) (K : ℕ) (start : ℝ) (hstart : 0 < start)
    (mold : (t : ℝ) → start ≤ t → Hold.Carrier → (postStage F.observation t).Carrier)
    (α : ℝ → ℝ) (Ω : TopologicalSpace.Opens (ℝ × Hold.Carrier))
    (hαpos : ∀ t, start ≤ t → 0 < α t)
    (hαlim : ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t, T ≤ t → α t < ε)
    (hsm : ∀ t (ht : start ≤ t), ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mold t ht) (sourceSlice_CX5 Ω t))
    (hemb : ∀ t (ht : start ≤ t),
      IsSmoothEmbedding (𝓡 3) (𝓡 3) ∞ (fun x : sourceSlice_CX5 Ω t => mold t ht x))
    (hball : ∀ t, start ≤ t →
      riemannianBallOf Hold.metric Hold.basepoint (2 * (α t)⁻¹) ⊆ sourceSlice_CX5 Ω t)
    (hck : ∀ t (ht : start ≤ t), ∀ k : ℕ, k ≤ max K ⌈(α t)⁻¹⌉₊ →
      ∀ p ∈ riemannianBallOf Hold.metric Hold.basepoint (2 * (α t)⁻¹),
        ckErr_S45 Hold (postMetric F.observation t) t⁻¹ (mold t ht) k p < α t)
    (Rold L : ℝ) (hL : 0 < L) :
    ∃ T0 : ℝ, ∀ r (hr : start ≤ r), T0 ≤ r → ∀ y : (postStage F.observation r).Carrier,
      (∃ q ∈ riemannianBallOf Hold.metric Hold.basepoint (Rold - L),
        riemannianEDistOf (scaleMetric r⁻¹ (inv_pos.mpr (hstart.trans_le hr))
          (postMetric F.observation r)) (mold r hr q) y < ENNReal.ofReal (L / 2)) →
      y ∈ mold r hr '' riemannianBallOf Hold.metric Hold.basepoint Rold := by
  obtain ⟨T1, hT1⟩ := hαlim (min (1 / 2) (1 / (|Rold| + 1)))
    (lt_min (by norm_num) (by positivity))
  refine ⟨max T1 start, fun r hr hrT y hy => ?_⟩
  have hr1 : T1 ≤ r := (le_max_left _ _).trans hrT
  have hαr := hT1 r hr1
  have hα0 := hαpos r hr
  have hαhalf : α r < 1 / 2 := lt_of_lt_of_le hαr (min_le_left _ _)
  have hαR : α r < 1 / (|Rold| + 1) := lt_of_lt_of_le hαr (min_le_right _ _)
  have hRlt : Rold < 2 * (α r)⁻¹ := by
    have h1 : |Rold| + 1 < (α r)⁻¹ := by
      rw [lt_inv_comm₀ (by positivity) hα0]
      simpa [one_div] using hαR
    have := le_abs_self Rold
    have hpos : 0 < (α r)⁻¹ := inv_pos.mpr hα0
    linarith
  have hrpos : 0 < r := hstart.trans_le hr
  let U : TopologicalSpace.Opens Hold.Carrier :=
    ⟨riemannianBallOf Hold.metric Hold.basepoint (2 * (α r)⁻¹), isOpen_riemannianBallOf_S61 Hold _⟩
  have hUs : (U : Set Hold.Carrier) ⊆ sourceSlice_CX5 Ω r := hball r hr
  have hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ (mold r hr) (U : Set Hold.Carrier) := (hsm r hr).mono hUs
  have hinj : Set.InjOn (mold r hr) (U : Set Hold.Carrier) := by
    intro a ha b hb hab
    have := (hemb r hr).isEmbedding.injective (a₁ := ⟨a, hUs ha⟩) (a₂ := ⟨b, hUs hb⟩) hab
    exact congrArg Subtype.val this
  have hRU : riemannianClosedBallOf Hold.metric Hold.basepoint Rold ⊆ (U : Set Hold.Carrier) := by
    intro x hx
    exact lt_of_le_of_lt hx ((ENNReal.ofReal_lt_ofReal_iff (by
      have : 0 < (α r)⁻¹ := inv_pos.mpr hα0
      have hq : 0 ≤ Rold := by
        by_contra hneg
        obtain ⟨q, hq, -⟩ := hy
        have : 0 < Rold - L := ENNReal.ofReal_pos.mp (lt_of_le_of_lt (by simp) hq)
        linarith
      linarith)).mpr hRlt)
  have hlow : ∀ p ∈ (U : Set Hold.Carrier), ∀ w : TangentSpace (𝓡 3) p,
      (1 - α r) * Hold.metric.inner p w w ≤
        (scaleMetric r⁻¹ (inv_pos.mpr hrpos) (postMetric F.observation r)).inner (mold r hr p)
          (mfderiv (𝓡 3) (𝓡 3) (mold r hr) p w) (mfderiv (𝓡 3) (𝓡 3) (mold r hr) p w) := by
    intro p hp w
    have h0 := hck r hr 0 (Nat.zero_le _) p hp
    have := pullback_inner_ge_of_ckErr_S90 Hold (postMetric F.observation r) r⁻¹ (mold r hr) p h0 w
    simpa using this
  have hsq : 1 / 2 < Real.sqrt (1 - α r) := by
    rw [Real.lt_sqrt (by norm_num)]
    nlinarith
  obtain ⟨q, hq, hd⟩ := hy
  refine member_of_drift_S90 Hold _ (mold r hr) U hf hinj (δ := α r) (by linarith) hlow hL hRU
    (A := L / 2) ?_ ⟨q, hq, hd⟩
  nlinarith

end GC.LongTime.Ch12
