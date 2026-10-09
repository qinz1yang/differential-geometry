import DifferentialGeometry.Geometry.Collapse.LocalExport.SlimPacket
import DifferentialGeometry.Geometry.Collapse.LocalExport.SlimChartApplications
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SlimFibreTypeSequence
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SurfaceOrientation

/-!
# LC85's producer in sequence form (LFR20 item 2 with the fibre type, modulo LFR14 data)

Dimension three. Data: LFR14's output for a sequence `(M i, p i)` with an oriented limit `N`
(`sec ≥ 0`, metric `G` of class `C^{k+1}`, `k ≥ 2`), an exact splitting `Φ : N ≃ᵢ ℓ²(ℝ × W)` with
compact `W` of diameter `≤ 10³Δ`, and slim charts `c i` (LFR19/LFR20 coordinates of the normalized
splittings `α i`) whose first coordinates converge to `t`.

* `exists_sphere_or_torus_eventually_slimChart_zeroLevel`: one compact connected oriented smooth
  surface `S`, diffeomorphic to `S²` or to `ℝ²/ℤ²` (LFR16 orientable factor + LFR17), such that
  eventually the ENTIRE zero fibre of `c i` in `B(p i, L)` is homeomorphic to `S`.
* `eventually_nonempty_slimPacket` (LC85's producer, sequence form): eventually each slim chart is
  an LC85 slim packet.
* consumer `SlimPacket.zeroLevel_compact_connected`.

The threshold form (∃ β₀ for LC85 with the fibre type) needs the compactness-contradiction frame:
LFR14 T1 for a sequence of counterexamples, the LFR16 product splitting `Φ` of the limit together
with the convergence of the splittings `u_i ∘ j_i → t`, and the orientation of the limit (see
`build-logs/worker-F7-LFR20b.md`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function Metric Bundle WithLp Manifold
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.ExactSplitting
open GC.MetricGeometry

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

local instance nezero_finrank_euclidean_three_F7LFR20b : NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

universe u

variable {N W : Type u} [MetricSpace N] [ChartedSpace E3 N] [IsManifold 𝓘(ℝ, E3) ∞ N]
  [ProperSpace N] [ConnectedSpace N] [RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x)]
  [IsRiemannianManifold 𝓘(ℝ, E3) N] [MetricSpace W] [CompactSpace W]
  {M : ℕ → Type*} [∀ i, MetricSpace (M i)] [∀ i, ChartedSpace E3 (M i)]
  [∀ i, IsManifold 𝓘(ℝ, E3) ∞ (M i)] [∀ i, SigmaCompactSpace (M i)]
  [∀ i, RiemannianBundle (fun x : M i => TangentSpace 𝓘(ℝ, E3) x)]
  [∀ i, IsRiemannianManifold 𝓘(ℝ, E3) (M i)] [∀ i, CompleteSpace (M i)]
  [∀ i, IsContinuousRiemannianBundle E3 (fun x : M i => TangentSpace 𝓘(ℝ, E3) x)]

/-- **LFR20 item 2 with the fibre type, sequence form.** One sphere-or-torus `S` is eventually
homeomorphic to the entire zero fibre of every slim chart. -/
theorem exists_sphere_or_torus_eventually_slimChart_zeroLevel {k : ℕ} (hk : 2 ≤ (k : ℕ∞))
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) (((k : ℕ∞) : ℕ∞ω) + 1) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace 𝓘(ℝ, E3) x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (hsec : ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, E3) x), 0 ≤ G.sectionalCurvature x v w)
    (oN : ManifoldOrientation (𝓡 3) N 3)
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E3) (M i)) (hEnorm : ∀ i, IsMetricNorm (g i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {K : ℕ} (hK : 2 ≤ K) (q : N) (j : ∀ i, PartialDiffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) N (M i) K)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hconv : ∀ (x : N) (L : Set E3), IsCompact L → L ⊆ (extChartAt 𝓘(ℝ, E3) x).target →
      MapCPConvergenceOn L 1
        (fun i => pullbackMetricCoefficients (g i)
          ((j i : N → M i) ∘ (extChartAt 𝓘(ℝ, E3) x).symm))
        (chartCoeff G x))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (j i x) (j i y) - dist x y| < ε)
    (hcover : ∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
      ball (j i q) a ⊆ (j i : N → M i) '' ball q b)
    (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) {Δ σ : ℝ} (hΔ : 1 ≤ Δ) (hσ : 0 < σ) (hσ1 : σ ≤ 1 / 100)
    (hD : ∀ a b : W, dist a b ≤ 10 ^ 3 * Δ)
    {Y : ℕ → Type*} [∀ i, MetricSpace (Y i)] {p : ∀ i, M i} {y₀ : ∀ i, Y i} {β : ℕ → ℝ}
    (α : ∀ i, KleinerLottApprox (p i) (WithLp.toLp 2 ((0 : ℝ), y₀ i)) (β i))
    (c : ∀ i, SlimChart (g i) (hEnorm i) Δ σ (α i)) (hpt : ∀ i, j i q = p i)
    (hU : ∀ C' : Set N, IsCompact C' →
      TendstoUniformlyOn (fun i x => ((α i).toFun (j i x)).fst) (fun x => (Φ x).fst) atTop C') :
    ∃ (S : Type u) (_ : MetricSpace S) (_ : ChartedSpace E2 S) (_ : IsManifold (𝓡 2) ∞ S),
      CompactSpace S ∧ ConnectedSpace S ∧ Nonempty (ManifoldOrientation (𝓡 2) S 2) ∧
      (Nonempty (S ≃ₘ⟮𝓡 2, 𝓡 2⟯ Metric.sphere (0 : E3) 1) ∨
        Nonempty (S ≃ₘ⟮𝓡 2, 𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)⟯ (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)))) ∧
      ∀ᶠ i in atTop, Nonempty ({y // y ∈ ball (p i) (10 ^ 6 * Δ) ∧ (c i).coord y = 0} ≃ₜ S) := by
  obtain ⟨S, mS, cS, iS, hc, hconn, ho, φ, -, -, κ, -, -, htype⟩ :=
    surfaceFactor_smoothCarrier_oriented G hk hGnorm hsec oN hD Φ
  refine ⟨S, mS, cS, iS, hc, hconn, ho, htype.imp id And.left, ?_⟩
  filter_upwards [eventually_nonempty_homeomorph_zeroLevel_slimChart hk G hGnorm g hEnorm hmetric
    hK q j hexh hconv hdist hcover Φ hΔ hσ hσ1 hD α c hpt hU] with i ⟨h⟩
  exact ⟨h.trans φ.symm⟩

/-- **LC85's producer, sequence form (modulo LFR14 data).** Eventually every slim chart is an LC85
slim packet: its entire zero fibre is connected and homeomorphic to `S²` or `T²`. -/
theorem eventually_nonempty_slimPacket {k : ℕ} (hk : 2 ≤ (k : ℕ∞))
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) (((k : ℕ∞) : ℕ∞ω) + 1) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace 𝓘(ℝ, E3) x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (hsec : ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, E3) x), 0 ≤ G.sectionalCurvature x v w)
    (oN : ManifoldOrientation (𝓡 3) N 3)
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E3) (M i)) (hEnorm : ∀ i, IsMetricNorm (g i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    {K : ℕ} (hK : 2 ≤ K) (q : N) (j : ∀ i, PartialDiffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) N (M i) K)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hconv : ∀ (x : N) (L : Set E3), IsCompact L → L ⊆ (extChartAt 𝓘(ℝ, E3) x).target →
      MapCPConvergenceOn L 1
        (fun i => pullbackMetricCoefficients (g i)
          ((j i : N → M i) ∘ (extChartAt 𝓘(ℝ, E3) x).symm))
        (chartCoeff G x))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (j i x) (j i y) - dist x y| < ε)
    (hcover : ∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
      ball (j i q) a ⊆ (j i : N → M i) '' ball q b)
    (Φ : N ≃ᵢ WithLp 2 (ℝ × W)) {Δ σ : ℝ} (hΔ : 1 ≤ Δ) (hσ : 0 < σ) (hσ1 : σ ≤ 1 / 100)
    (hD : ∀ a b : W, dist a b ≤ 10 ^ 3 * Δ)
    {Y : ℕ → Type*} [∀ i, MetricSpace (Y i)] {p : ∀ i, M i} {y₀ : ∀ i, Y i} {β : ℕ → ℝ}
    (α : ∀ i, KleinerLottApprox (p i) (WithLp.toLp 2 ((0 : ℝ), y₀ i)) (β i))
    (c : ∀ i, SlimChart (g i) (hEnorm i) Δ σ (α i)) (hpt : ∀ i, j i q = p i)
    (hU : ∀ C' : Set N, IsCompact C' →
      TendstoUniformlyOn (fun i x => ((α i).toFun (j i x)).fst) (fun x => (Φ x).fst) atTop C') :
    ∀ᶠ i in atTop, Nonempty (SlimPacket (g i) (hEnorm i) Δ σ (α i)) := by
  obtain ⟨S, mS, cS, iS, -, hconn, -, htype, hev⟩ :=
    exists_sphere_or_torus_eventually_slimChart_zeroLevel hk G hGnorm hsec oN g hEnorm hmetric hK q
      j hexh hconv hdist hcover Φ hΔ hσ hσ1 hD α c hpt hU
  filter_upwards [hev] with i ⟨ψ⟩
  refine ⟨{ c i with
    zeroLevel_connected := ψ.connectedSpace_iff.mpr hconn
    zeroLevel_type := ?_ }⟩
  rcases htype with hs | ht
  · obtain ⟨d⟩ := hs
    exact Or.inl ⟨ψ.trans d.toHomeomorph⟩
  · obtain ⟨d⟩ := ht
    exact Or.inr ⟨ψ.trans d.toHomeomorph⟩

section Consumer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : Type*} [MetricSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [SigmaCompactSpace X]
  [RiemannianBundle (fun x : X => TangentSpace I x)]
  [IsRiemannianManifold I X] [CompleteSpace X]
  [IsContinuousRiemannianBundle E (fun x : X => TangentSpace I x)]

/-- **Consumer.** The entire zero fibre of a slim packet is compact, nonempty and connected, and
it is a sphere or a torus. -/
theorem SlimPacket.zeroLevel_compact_connected {g : SmoothRiemannianMetric I X}
    {hEnorm : IsMetricNorm g} {Δ σ : ℝ} (hΔ : 0 < Δ) {Y : Type*} [MetricSpace Y] {p : X}
    {y₀ : Y} {β : ℝ} {α : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y₀)) β}
    (P : SlimPacket g hEnorm Δ σ α) :
    IsCompact {x | x ∈ ball p (10 ^ 6 * Δ) ∧ P.coord x = 0} ∧
      {x | x ∈ ball p (10 ^ 6 * Δ) ∧ P.coord x = 0}.Nonempty ∧
      ConnectedSpace {x // x ∈ ball p (10 ^ 6 * Δ) ∧ P.coord x = 0} ∧
      (Nonempty ({x // x ∈ ball p (10 ^ 6 * Δ) ∧ P.coord x = 0} ≃ₜ
          Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∨
        Nonempty ({x // x ∈ ball p (10 ^ 6 * Δ) ∧ P.coord x = 0} ≃ₜ
          (AddCircle (1 : ℝ) × AddCircle (1 : ℝ)))) := by
  obtain ⟨hcpt, hne, -, -⟩ := SlimChart.isCompact_zeroLevel hΔ P.toSlimChart
  exact ⟨hcpt, hne, P.zeroLevel_connected, P.zeroLevel_type⟩

end Consumer

end DifferentialGeometry.Geometry.Collapse
