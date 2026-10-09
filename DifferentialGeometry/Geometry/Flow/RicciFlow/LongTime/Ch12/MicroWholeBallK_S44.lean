import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.MicroWholeBallShi_O13

/-!
# CH12-S44, group 3: order-capped version of the pointwise glue (`T = T(K)`)

`microWholeBallK_of_pointwise_S44` is `microWholeBall_of_pointwise_O13` with an order cap `K`
(constants and the late time `T` may depend on `K`, the bound is for `k ≤ K`).  Reason: recent-cap
jets of order `k` need cap witnesses of order `≥ k+2`, available only after a time `T_k → ∞`; see
"[FROZEN v2] CH12-S44".  Same proof.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Collapse DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian Set
open scoped Manifold ContDiff ENNReal NNReal

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {δ : ℝ → ℝ}

/-- **`MicroWholeBallK_S44 Hp K`** (hypothesis shape, K-indexed variant of `MicroWholeBall_O2`,
authorised by the lead for CH12-S44): derivative orders `k ≤ K`, constants and `T` depending on `K`. -/
def MicroWholeBallK_S44 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ) (K : ℕ) : Prop :=
  ∀ w : ℝ, 0 < w → ∀ Λ : ℝ, 1 ≤ Λ → ∃ (b T : ℝ) (A : ℕ → ℝ), 0 < b ∧
    ∀ s : RegularSlice F.observation, T ≤ s.time →
    ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ → ρ ≤ b * Real.sqrt s.time →
      (∃ n, ∃ i : Fin (F.tower.history n).eventCount, ∃ h,
        (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time ∧
        ρ < Λ * (Hp.records n i).nominalRadius h) →
      (∃ z ∈ connectedComponent p, ¬ SectionalBoundedBelowAt s.metric z 0) →
      (∀ q ∈ riemannianBallOf s.metric p ρ,
        SectionalBoundedBelowAt s.metric q (-(ρ ^ 2)⁻¹)) →
      ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.metric p ρ →
      ∀ k : ℕ, k ≤ K → ∀ q ∈ riemannianBallOf s.metric p ρ,
        curvatureDerivativeNorm s.metric k q ≤ A k * (ρ ^ (k + 2))⁻¹

/-- **D (orders `k ≥ 0` on the whole ball), pointwise form.**  At every late micro test ball and
every `q ∈ B(p, ρ)`: a traced backward region about `q` at scale `aρ` (non-cap points), or a direct
all-order bound (recent-cap points) ⇒ `MicroWholeBall_O2 Hp`, with
`A k = max (shiTracedConst_O13 τ C k · a^{-(k+2)}) (B k)`. -/
theorem microWholeBallK_of_pointwise_S44 (Hp : GC.LongTime.AnalyticSurgeryProfile F δ)
    (hpt : ∀ w : ℝ, 0 < w → ∀ Λ : ℝ, 1 ≤ Λ → ∀ K : ℕ, ∃ (b T a τ C : ℝ) (B : ℕ → ℝ),
      0 < b ∧ 0 < a ∧ 0 < τ ∧ 0 < C ∧
      ∀ s : RegularSlice F.observation, T ≤ s.time →
      ∀ (p : s.stage.Carrier) (ρ : ℝ), 0 < ρ → ρ ≤ b * Real.sqrt s.time →
        (∃ n, ∃ i : Fin (F.tower.history n).eventCount, ∃ h,
          (F.tower.history n).time i.succ ∈ Icc (s.time / 2) s.time ∧
          ρ < Λ * (Hp.records n i).nominalRadius h) →
        (∃ z ∈ connectedComponent p, ¬ SectionalBoundedBelowAt s.metric z 0) →
        (∀ q ∈ riemannianBallOf s.metric p ρ,
          SectionalBoundedBelowAt s.metric q (-(ρ ^ 2)⁻¹)) →
        ENNReal.ofReal (w * ρ ^ 3) ≤ ballVolume s.metric p ρ →
        ∀ q ∈ riemannianBallOf s.metric p ρ,
          (∀ q' : (s.history.stageAt (sliceTop_S8 s)).Carrier, HEq q' q →
            s.history.isTracedRegion (sliceTop_S8 s) q' (2 * (a * ρ)) (τ * (a * ρ) ^ 2)
              (C / (a * ρ) ^ 2)) ∨
          ∀ k : ℕ, k ≤ K → curvatureDerivativeNorm s.metric k q ≤ B k * (ρ ^ (k + 2))⁻¹) :
    ∀ K : ℕ, MicroWholeBallK_S44 Hp K := by
  intro K
  unfold MicroWholeBallK_S44
  intro w hw Λ hΛ
  obtain ⟨b, T, a, τ, C, B, hb, ha, hτ, hC, hpt⟩ := hpt w hw Λ hΛ K
  refine ⟨b, T, fun k => max (shiTracedConst_O13 τ C k * (a ^ (k + 2))⁻¹) (B k), hb, ?_⟩
  intro s hs p ρ hρ hρb hmic hneg hsec hvol k hk q hq
  have hpos : (0 : ℝ) ≤ (ρ ^ (k + 2))⁻¹ := inv_nonneg.mpr (pow_nonneg hρ.le _)
  rcases hpt s hs p ρ hρ hρb hmic hneg hsec hvol q hq with htr | hcap
  · have haρ : 0 < a * ρ := mul_pos ha hρ
    have hqq : q ∈ riemannianBallOf s.metric q (a * ρ) :=
      mem_riemannianBallOf_self_O13 s.metric q haρ
    have h := wholeBall_of_traced_S8 s (Fin.last _) s.history.activeStage_at_horizon q hτ haρ hC
      htr k q hqq
    calc curvatureDerivativeNorm s.metric k q
        ≤ shiTracedConst_O13 τ C k * ((a * ρ) ^ (k + 2))⁻¹ := h
      _ = (shiTracedConst_O13 τ C k * (a ^ (k + 2))⁻¹) * (ρ ^ (k + 2))⁻¹ := by
          rw [mul_pow, mul_inv]; ring
      _ ≤ max (shiTracedConst_O13 τ C k * (a ^ (k + 2))⁻¹) (B k) * (ρ ^ (k + 2))⁻¹ :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
  · exact (hcap k hk).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hpos)

end GC.LongTime.Ch12
