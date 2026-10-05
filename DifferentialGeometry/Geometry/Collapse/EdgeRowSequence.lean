import DifferentialGeometry.Geometry.Collapse.EdgeRowSlabAssembly
import DifferentialGeometry.Geometry.Collapse.EdgeRowModelSurface
import DifferentialGeometry.Geometry.Collapse.EdgeSourceSlabEnclosure
import DifferentialGeometry.Geometry.Collapse.EdgeValueComparison
import DifferentialGeometry.Geometry.Collapse.EdgeQuotientModelDerivatives
import DifferentialGeometry.Geometry.Collapse.EdgeEndpointModel
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.VerticalDerivativeBridgeApplications
import DifferentialGeometry.Geometry.Exponential.FiniteMetric.SmoothAgreement

/-!
# LFR28 row, sequence form: the whole source edge disk bundle on a converging sequence

Blueprint 207A, LFR28 (`thm:collapse-finite-source-edge-packet`, A:27223), steps 1–4 of the proof
on ONE common tail of a sequence converging to a nonnegatively curved product limit (LFR14–LFR16
data, modulo the compactness that produces them; the threshold form is
`EdgeRowThreshold.lean`).

Data: the limit `N` with its `C^{k+1}` metric `G` (`sec ≥ 0`, oriented), the actual embeddings
`j i` of order `k + 2`, metric convergence, exact and approximate coverage, an exact splitting
`e : N ≃ᵢ ℓ²(ℝ × W)`; on each `M i` the coarse-border chart `Q i` of the closed set `A i`
(distortion `τΔ`), its first coordinate `U i` converging to `t`, LFR27's smoothing `F i` of `d_{A i}`
with its scale `ρ i` (value, gradient, quotient and smooth-core clauses), and LFR19's tangential
coordinate `f i` (smooth near `B̄(p, 100Δ)`, `(1+σ)`-Lipschitz, value error `μΔ`, the (LFR19.1)
test on `B(100Δ) × B(1000Δ)`). The height is `H = Δ ψ(F/(ρΔ))` (`edgeRowHeight`).

* `eventually_edgeSourceSlab_disk_bundle_of_model`: the same with the model data on the rescaled
  carrier given (the stage-2 output); the per-index assembly through
  `edgeRowSlab_disk_bundle_of_estimates`, fed by (LFR28.3)
  (`eventually_abs_mvfderiv_sub_inner_vertical_le_thousandth`), (LFR28.2) and (LFR28.4)
  (`eventually_abs_mvfderiv_edgeQuotient_comp_sub_model_le`), (LFR28.5)
  (`eventually_edgeValueComparison`) and B5 (`eventually_edgeSourceSlab_mem_image`).
* `eventually_edgeSourceSlab_disk_bundle` (**LFR28.1, sequence form**): stage 1
  (`edgeRowModelChart_of_carrier`), I7(a) (`exists_edgeEndpointModel`), stage 2
  (`edgeRowModelSurface`), LFR18 (`exists_vertical_field_eventually_inverse_directions_close`) and the
  previous theorem. Eventually there is an open `O ⊆ B(p_i, 20Δ)` containing the whole closed slab
  `{y ∈ B(p_i, 100Δ) : |f_i| ≤ 4Δ, H_i ≤ 4Δ}` on which, for every `-4Δ < a₀ < 0 < b₀ < 4Δ`, the
  conclusion of Row-A holds: the fibre `{f_i = 0, H_i ≤ 4Δ}` (regular sublevel, ModelProd charts) is
  diffeomorphic to `ClosedCell 2`, compact, connected, `f_i` is trivial over `(a₀, b₀)` with that
  fibre, and the boundary of the fibre is exactly `{H_i = 4Δ}`.

Universal constants (blueprint: `σ₀ = 10⁻¹⁰`, `ε₀ = μ₀ = λ₀ = 10⁻⁸`; our `τ₀ = 10⁻³⁰`, which meets
LFR24's endpoint threshold with gradient error `1/1000`, `h = 20√τ`, `40√(h + τ) < 10⁻⁵`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Function Filter Metric Manifold
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Analysis DifferentialGeometry.Topology
open DifferentialGeometry.Manifold DifferentialGeometry.Manifold.RegularLevel
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Operator
open GC.MetricGeometry

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

attribute [local instance] Handle.closedCellChartedSpaceSucc Handle.closedCellIsManifold

local instance nezero_finrank_euclidean_three_LFR28ROW2 : NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

/-- LFR27's height `H = Δ ψ((F/ρ)/Δ)` with the fixed sublevel profile `ψ`. -/
def edgeRowHeight {X : Type*} (Δ : ℝ) (F ρ : X → ℝ) : X → ℝ :=
  fun y => Δ * edgeSublevelProfile (F y / ρ y / Δ)

theorem edgeRowHeight_le_iff {X : Type*} {Δ : ℝ} (hΔ : 0 < Δ) {F ρ : X → ℝ} {y : X} :
    edgeRowHeight Δ F ρ y ≤ 4 * Δ ↔ F y / ρ y ≤ 4 * Δ := by
  unfold edgeRowHeight
  rw [mul_comm, ← le_div_iff₀ hΔ, mul_div_assoc, div_self hΔ.ne', mul_one,
    edgeSublevelProfile_le_iff (by norm_num), div_le_iff₀ hΔ, mul_comm]

/-- Near a point where `F/ρ > 2Δ` (and `F/ρ` is continuous) the height is `F/ρ`. -/
theorem edgeRowHeight_eventuallyEq {X : Type*} [TopologicalSpace X] {Δ : ℝ} (hΔ : 0 < Δ)
    {F ρ : X → ℝ} {x : X} (hc : ContinuousAt (fun y => F y / ρ y) x) (hx : 2 * Δ < F x / ρ x) :
    edgeRowHeight Δ F ρ =ᶠ[𝓝 x] fun y => F y / ρ y := by
  filter_upwards [hc.eventually (lt_mem_nhds hx)] with y hy
  unfold edgeRowHeight
  have h2 : 2 ≤ F y / ρ y / Δ := by
    rw [le_div_iff₀ hΔ]
    linarith
  rw [edgeSublevelProfile_eq_self h2]
  field_simp

/-- **LFR28.1 at one index from the limit estimates.** On one manifold `X` with an actual
embedding `jX : N ⇀ X` of the model limit: the per-index estimates of a late index of the sequence
((LFR28.3) on the cylinder, (LFR28.4) with the collar in LFR27's core, the values (LFR28.5) and
the enclosure B5) and the model data give the conclusion of Row-A on an open `O ⊆ B(jX q, 20Δ)`
containing the whole closed slab. -/
theorem edgeRowSlab_disk_bundle_of_limit_estimates
    {N : Type} [MetricSpace N] [ChartedSpace E3 N] [IsManifold 𝓘(ℝ, E3) ∞ N] [ProperSpace N]
    {k : ℕ} {n : ℕ∞ω}
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) n E3 (TangentSpace 𝓘(ℝ, E3) : N → Type _))
    {W : Type} [MetricSpace W] (e : N ≃ᵢ WithLp 2 (ℝ × W)) {w₀ : W} {q : N}
    (heq : e q = WithLp.toLp 2 ((0 : ℝ), w₀))
    {S : Type} [MetricSpace S] [ChartedSpace E2 S] [IsManifold (𝓡 2) ∞ S]
    [LocallyCompactSpace S] [SecondCountableTopology S]
    {s₀ : S} {FS h : S → ℝ} {Wh : Set S} {b : ClosedCell 2 → S} {Δ : ℝ} (hΔ : 0 < Δ)
    (hhdef : h = edgeModelCore FS) (hW : IsOpen Wh) (hW9 : closedBall s₀ 9 ⊆ Wh)
    (hh : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ h Wh)
    (h4 : ∀ x, dist x s₀ < 9 → h x = 4 → mvfderiv (𝓡 2) h x ≠ 0)
    (hb : IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ b)
    (hrange : range b = {x | dist x s₀ < 9 ∧ h x ≤ 4})
    (hQ : IsCompact (Icc (-(Δ / 100)) (Δ / 100) ×ˢ {s : S | dist s s₀ < 9 ∧ h s ≤ 401 / 100}))
    {n' : ℕ∞ω} (κ : ContMDiffRiemannianMetric (𝓡 2) n' E2 (TangentSpace (𝓡 2) : S → Type _))
    (hk : 1 ≤ k) (Θ : Diffeomorph (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) (ℝ × S) N ((k + 2 : ℕ) : ℕ∞ω))
    (hΘfst : ∀ p : ℝ × S, (e (Θ p)).fst = p.1)
    (hΘrad : ∀ p : ℝ × S, dist (e (Θ p)).snd w₀ = Δ * dist p.2 s₀)
    (hpull : ∀ (p : ℝ × S) (v w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 2)) p),
      G.inner (Θ p) (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p v)
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p w) = v.1 * w.1 + κ.inner p.2 v.2 w.2)
    (V : ∀ y : N, TangentSpace 𝓘(ℝ, E3) y)
    (hΘV : ∀ p : ℝ × S,
      mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p ((1 : ℝ), (0 : E2)) = V (Θ p))
    (hGN : ∀ s : S, dist s s₀ < 9 → 39 / 10 ≤ h s → h s ≤ 41 / 10 → ∀ (t a : ℝ) (Y : E2),
      mvfderiv 𝓘(ℝ, E3) (fun y => Δ * FS (Θ.symm y).2) (Θ (t, s))
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (t, s) (a, Y)) =
          Δ * mvfderiv (𝓡 2) h s Y)
    (hdir : ∀ s : S, dist s s₀ < 9 → 39 / 10 ≤ h s → h s ≤ 41 / 10 →
      ∃ Y : E2, κ.inner s Y Y ≤ 1 ∧ 1 / 2 ≤ Δ * mvfderiv (𝓡 2) h s Y)
    {μ : ℝ} (hμ1 : μ ≤ 1 / 100)
    (hGval : ∀ x : N, |Δ * FS (Θ.symm x).2 - dist (e x).snd w₀| < μ * Δ)
    {X : Type} [MetricSpace X] [ChartedSpace E3 X] [IsManifold 𝓘(ℝ, E3) ∞ X] [ProperSpace X]
    (jX : PartialDiffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) N X ((k + 2 : ℕ) : ℕ∞ω)) (A : Set X) (F f ρ : X → ℝ)
    (OF : Set X) (hOF : IsOpen OF) (hFs : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ F OF)
    (hHs : ∀ x ∈ ball (jX q) (20 * Δ), infDist x A < 41 / 4 * Δ →
      ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (edgeRowHeight Δ F ρ) x)
    (hρs : ∀ x ∈ ball (jX q) (100 * Δ), ContinuousAt ρ x)
    (Of : Set X) (hOf : IsOpen Of) (hOfb : closedBall (jX q) (100 * Δ) ⊆ Of)
    (hfs : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ f Of)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1 / 1000)
    (P1 : {x : N | |(e x).fst| ≤ 6 * Δ ∧ dist (e x).snd w₀ ≤ 9 * Δ} ⊆ jX.source)
    (P2 : ∀ x : N, |(e x).fst| ≤ 6 * Δ → dist (e x).snd w₀ ≤ 9 * Δ →
      ∀ Z : TangentSpace 𝓘(ℝ, E3) x,
        |mvfderiv 𝓘(ℝ, E3) (fun y => f (jX y)) x Z - G.inner x (V x) Z| ≤
          1 / 1000 * Real.sqrt (G.inner x Z Z))
    (P3 : ∀ x : N, |(e x).fst| ≤ 10 * Δ → 5 / 2 * Δ ≤ dist (e x).snd w₀ →
      dist (e x).snd w₀ ≤ 13 / 2 * Δ →
      jX x ∈ OF ∧ jX x ∈ ball (jX q) (100 * Δ) ∧ 0 < ρ (jX x) ∧
      ∀ Z : TangentSpace 𝓘(ℝ, E3) x,
        |mvfderiv 𝓘(ℝ, E3) (fun y => F (jX y) / ρ (jX y)) x Z -
          mvfderiv 𝓘(ℝ, E3) (fun y => Δ * FS (Θ.symm y).2) x Z| ≤
          c * Real.sqrt (G.inner x Z Z))
    (P5 : ∀ x ∈ edgeModelCylinder s₀ Δ,
      jX (Θ x) ∈ ball (jX q) (20 * Δ) ∧ infDist (jX (Θ x)) A < 41 / 4 * Δ ∧
      |F (jX (Θ x)) / ρ (jX (Θ x)) - Δ * FS x.2| < Δ / 1000 ∧
      |f (jX (Θ x)) - x.1| ≤ Δ / 100 ∧ |edgeRowHeight Δ F ρ (jX (Θ x)) - Δ * h x.2| ≤ Δ / 100)
    (P6 : ∀ y ∈ ball (jX q) (100 * Δ), |f y| ≤ 4 * Δ → F y / ρ y ≤ 4 * Δ →
      ∃ x, jX x = y ∧ |(e x).fst| < 5 * Δ ∧ dist (e x).snd w₀ < 5 * Δ) :
      ∃ O : TopologicalSpace.Opens X,
      (O : Set X) ⊆ ball (jX q) (20 * Δ) ∧
      (∀ y ∈ ball (jX q) (100 * Δ), |f y| ≤ 4 * Δ → edgeRowHeight Δ F ρ y ≤ 4 * Δ → y ∈ O) ∧
      ∀ (a₀ b₀ : ℝ), -(4 * Δ) < a₀ → ∀ (h0 : (0 : ℝ) ∈ Ioo a₀ b₀), b₀ < 4 * Δ →
      letI := chartedSpaceTransHomeomorph (M := O) euclideanThreeProdHomeomorph
      letI : IsManifold (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ O := edgeSource_isManifold
      ∃ (hΨ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ (fun y : O => f y))
        (hB : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
          (fun y : O => 4 * Δ - edgeRowHeight Δ F ρ y))
        (hreg : ∀ y : O, f y = 0 → 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y →
          Surjective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) (fun y : O => f y) y))
        (hregb : ∀ y : O, f y = 0 → 4 * Δ - edgeRowHeight Δ F ρ y = 0 →
          Surjective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
            (fun y : O => ((f y, 4 * Δ - edgeRowHeight Δ F ρ y) : ℝ × ℝ)) y)),
        letI := regularSublevelChartedSpace finrank_real_prod_euclideanTwo hΨ hB hreg hregb
        let Q₀ : TopologicalSpace.Opens ℝ := ⟨Ioo a₀ b₀, isOpen_Ioo⟩
        Nonempty (ClosedCell 2 ≃ₘ⟮𝓡∂ (1 + 1), 𝓡∂ (1 + 1)⟯
          {y : O // f y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y}) ∧
        CompactSpace {y : O // f y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y} ∧
        ConnectedSpace {y : O // f y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y} ∧
        (∃ Θ' : {y : O // f y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y} × Q₀ → O,
          ContMDiff ((𝓡∂ (1 + 1)).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ Θ' ∧
          (∀ p, f (Θ' p) = p.2 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ (Θ' p)) ∧
          (∀ x, Θ' (x, ⟨0, h0⟩) = x) ∧ Injective Θ' ∧
          ∃ O' : Set O, IsOpen O' ∧
            (∀ y : O, f y ∈ Ioo a₀ b₀ → 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y → y ∈ O') ∧
            ∃ R : O → O, ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ R O' ∧
              ∀ (y : O) (hy : f y ∈ Ioo a₀ b₀),
                0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y →
                ∃ hR : f (R y) = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ (R y),
                  Θ' (⟨R y, hR⟩, ⟨f y, hy⟩) = y) ∧
        ∀ y : {y : O // f y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ F ρ y},
          (𝓡∂ (1 + 1)).IsBoundaryPoint y ↔ edgeRowHeight Δ F ρ y = 4 * Δ := by
  set Cyl : Set N := {x | |(e x).fst| ≤ 6 * Δ ∧ dist (e x).snd w₀ ≤ 9 * Δ} with hCyldef
  set Cyl5 : Set N := {x | |(e x).fst| ≤ 5 * Δ ∧ dist (e x).snd w₀ ≤ 5 * Δ} with hCyl5def
  have hfstc : Continuous fun x : N => (e x).fst := (lipschitzWith_heightCoord e).continuous
  have hradc : Continuous fun x : N => dist (e x).snd w₀ := (lipschitzWith_axisDist e w₀).continuous
  have hCyl5sub : Cyl5 ⊆ Cyl := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hcylN : ∀ x ∈ edgeModelCylinder s₀ Δ, Θ x ∈ Cyl := by
    intro x hx
    refine ⟨?_, ?_⟩
    · rw [hΘfst]
      exact (abs_lt.mpr ⟨hx.1.1, hx.1.2⟩).le
    · rw [hΘrad]
      have := mul_lt_mul_of_pos_left hx.2 hΔ
      linarith
  have hcyl5 : ∀ x ∈ Cyl5, Θ.symm x ∈ edgeModelCylinder s₀ Δ := by
    intro x hx
    have hx' : x = Θ (Θ.symm x) := (Θ.apply_symm_apply x).symm
    have h1 := hx.1
    have h2 := hx.2
    rw [hx', hΘfst] at h1
    rw [hx', hΘrad] at h2
    refine ⟨⟨by linarith [(abs_le.mp h1).1], by linarith [(abs_le.mp h1).2]⟩, ?_⟩
    by_contra hcon
    push Not at hcon
    have := mul_le_mul_of_nonneg_left hcon hΔ.le
    linarith
  set H : X → ℝ := edgeRowHeight Δ F ρ with hHdef
  let O : TopologicalSpace.Opens X :=
    ⟨ball (jX q) (20 * Δ) ∩ {y | infDist y A < 41 / 4 * Δ} ∩ Of,
      (isOpen_ball.inter (isOpen_lt (continuous_infDist_pt _) continuous_const)).inter hOf⟩
  have hOsub : ∀ y : X, y ∈ ball (jX q) (20 * Δ) → infDist y A < 41 / 4 * Δ → y ∈ O := by
    intro y h1 h2
    refine ⟨⟨h1, h2⟩, hOfb ?_⟩
    have h1' := mem_ball.mp h1
    exact mem_closedBall.mpr (by linarith)
  have hcylO : ∀ x ∈ edgeModelCylinder s₀ Δ, jX (Θ x) ∈ O := fun x hx =>
    hOsub _ (P5 x hx).1 (P5 x hx).2.1
  -- the slab lies in `jX '' Cyl5`
  have hslab : ∀ y ∈ ball (jX q) (100 * Δ), |f y| ≤ 4 * Δ → H y ≤ 4 * Δ →
      ∃ x ∈ Cyl5, jX x = y := by
    intro y hy hfy hHy
    rw [hHdef, edgeRowHeight_le_iff hΔ] at hHy
    obtain ⟨x, hxy, ht, hr⟩ := P6 y hy hfy hHy
    exact ⟨x, ⟨ht.le, hr.le⟩, hxy⟩
  set C : Set X := (jX : N → X) '' Cyl5 with hCdef
  have hCO' : C ⊆ O := by
    rintro _ ⟨x, hx, rfl⟩
    have h := hcylO _ (hcyl5 x hx)
    rwa [Θ.apply_symm_apply] at h
  have hslabO : ∀ y ∈ ball (jX q) (100 * Δ), |f y| ≤ 4 * Δ → H y ≤ 4 * Δ → y ∈ O := by
    intro y hy hfy hHy
    obtain ⟨x, hx, rfl⟩ := hslab y hy hfy hHy
    exact hCO' ⟨x, hx, rfl⟩
  have hfO : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ f O := hfs.mono fun y hy => hy.2
  have hHO : ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ H O := fun y hy =>
    (hHs y hy.1.1 hy.1.2).contMDiffWithinAt
  refine ⟨O, fun y hy => hy.1.1, hslabO, fun a₀ b₀ ha₀ h0 hb₀ => ?_⟩
  have hU' : ∀ x ∈ edgeModelCylinder s₀ Δ, Θ x ∈ jX.source ∧ jX (Θ x) ∈ O := fun x hx =>
    ⟨P1 (hcylN x hx), hcylO x hx⟩
  have hval : ∀ x ∈ edgeModelCylinder s₀ Δ,
      |f (jX (Θ x)) - x.1| ≤ Δ / 100 ∧ |H (jX (Θ x)) - Δ * h x.2| ≤ Δ / 100 := fun x hx =>
    ⟨(P5 x hx).2.2.2.1, (P5 x hx).2.2.2.2⟩
  have h3 : ∀ x ∈ edgeModelCylinder s₀ Δ, |x.1| ≤ 41 / 10 * Δ → h x.2 ≤ 41 / 10 →
      ∀ Z : TangentSpace 𝓘(ℝ, E3) (Θ x),
        |mvfderiv 𝓘(ℝ, E3) (fun y => f (jX y)) (Θ x) Z - G.inner (Θ x) (V (Θ x)) Z| ≤
          1 / 1000 * Real.sqrt (G.inner (Θ x) Z Z) := fun x hx _ _ Z =>
    P2 (Θ x) (hcylN x hx).1 (hcylN x hx).2 Z
  have h4' : ∀ x ∈ edgeModelCylinder s₀ Δ, |x.1| ≤ 41 / 10 * Δ → 39 / 10 ≤ h x.2 →
      h x.2 ≤ 41 / 10 → ∀ Z : E3,
        |mvfderiv 𝓘(ℝ, E3) (fun y => H (jX y)) (Θ x) Z -
          mvfderiv 𝓘(ℝ, E3) (fun y => Δ * FS (Θ.symm y).2) (Θ x) Z| ≤
          c * Real.sqrt (G.inner (Θ x) Z Z) := by
    intro x hx ht hlo hhi Z
    rw [hhdef] at hlo hhi
    have hF39 : 39 / 10 ≤ FS x.2 := le_of_le_edgeModelCore (by norm_num) hlo
    have hFeq : edgeModelCore FS x.2 = FS x.2 := edgeSublevelProfile_eq_self (by linarith)
    rw [hFeq] at hhi
    have hgv := abs_lt.mp (hGval (Θ x))
    rw [Θ.symm_apply_apply] at hgv
    have hμΔ : μ * Δ ≤ Δ / 100 := by
      have := mul_le_mul_of_nonneg_right hμ1 hΔ.le
      linarith
    have hFΔ1 := mul_le_mul_of_nonneg_left hF39 hΔ.le
    have hFΔ2 := mul_le_mul_of_nonneg_left hhi hΔ.le
    have hr1 : 5 / 2 * Δ ≤ dist (e (Θ x)).snd w₀ := by linarith [hgv.2]
    have hr2' : dist (e (Θ x)).snd w₀ ≤ 13 / 2 * Δ := by linarith [hgv.1]
    have ht' : |(e (Θ x)).fst| ≤ 10 * Δ := by rw [hΘfst]; linarith
    obtain ⟨hjO, hj100, hρpos, hd⟩ := P3 (Θ x) ht' hr1 hr2'
    have hFc : ContinuousAt F (jX (Θ x)) :=
      ((hFs _ hjO).contMDiffAt (hOF.mem_nhds hjO)).continuousAt
    have hηc : ContinuousAt (fun y => F y / ρ y) (jX (Θ x)) :=
      hFc.div (hρs _ hj100) hρpos.ne'
    have hη := (abs_lt.mp (P5 x hx).2.2.1).1
    have hη2 : 2 * Δ < F (jX (Θ x)) / ρ (jX (Θ x)) := by linarith
    have hev := edgeRowHeight_eventuallyEq hΔ hηc hη2
    have hjc : ContinuousAt (jX : N → X) (Θ x) :=
      jX.contMDiffOn_toFun.continuousOn.continuousAt
        (jX.open_source.mem_nhds (P1 (hcylN x hx)))
    have hev' : (fun y => H (jX y)) =ᶠ[𝓝 (Θ x)] fun y => F (jX y) / ρ (jX y) :=
      hev.comp_tendsto hjc
    have hder : mvfderiv 𝓘(ℝ, E3) (fun y => H (jX y)) (Θ x) =
        mvfderiv 𝓘(ℝ, E3) (fun y => F (jX y) / ρ (jX y)) (Θ x) := by
      ext v
      simp only [mvfderiv, hev'.mfderiv_eq]
      rfl
    rw [hder]
    exact hd Z
  have henc : ∀ y ∈ O, |f y| < 4 * Δ → H y ≤ 4 * Δ →
      ∃ x ∈ edgeModelCylinder s₀ Δ, jX (Θ x) = y := by
    intro y hy hfy hHy
    have hy100 : y ∈ ball (jX q) (100 * Δ) := by
      have := mem_ball.mp hy.1.1
      exact mem_ball.mpr (by linarith)
    obtain ⟨x, hx, rfl⟩ := hslab y hy100 hfy.le hHy
    exact ⟨Θ.symm x, hcyl5 x hx, by rw [Θ.apply_symm_apply]⟩
  have hCyl5 : IsCompact Cyl5 := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_le (continuous_abs.comp hfstc) continuous_const).inter
        (isClosed_le hradc continuous_const)
    · exact (isBounded_closedBall (x := q) (r := 10 * Δ)).subset fun x hx =>
        mem_closedBall.mpr ((dist_le_abs_fst_add_axisDist e heq x).trans
          (by linarith [hx.1, hx.2]))
  have hjc5 : ContinuousOn (jX : N → X) Cyl5 :=
    jX.contMDiffOn_toFun.continuousOn.mono (hCyl5sub.trans P1)
  have hprop := isCompact_slab_preimage_of_subset_compact (O := O)
    (hCyl5.image_of_continuousOn hjc5) hCO' (hfO.continuousOn.mono hCO')
    (hHO.continuousOn.mono hCO') (β := 4 * Δ) (e := 4 * Δ)
    (fun y hy hfy hHy => by
      have hy100 : y ∈ ball (jX q) (100 * Δ) := by
        have := mem_ball.mp hy.1.1
        exact mem_ball.mpr (by linarith)
      obtain ⟨x, hx, rfl⟩ := hslab y hy100 hfy.le hHy
      exact ⟨x, hx, rfl⟩)
  exact edgeRowSlab_disk_bundle_of_estimates hW hW9 hh h4 hb hrange hΔ hQ
    (by omega : 3 ≤ k + 2) Θ G κ hpull V hΘV (fun y => Δ * FS (Θ.symm y).2) hGN hdir jX O hU'
    hfO hHO hval h3 hc0 hc1 h4' henc hprop ha₀ h0 hb₀

/-- **LFR28.1, sequence form, with the model data given.** See the module docstring. -/
theorem eventually_edgeSourceSlab_disk_bundle_of_model
    {N : Type} [MetricSpace N] [ChartedSpace E3 N] [IsManifold 𝓘(ℝ, E3) ∞ N] [ProperSpace N]
    [RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x)] [IsRiemannianManifold 𝓘(ℝ, E3) N]
    {M : ℕ → Type} [∀ i, MetricSpace (M i)] [∀ i, ChartedSpace E3 (M i)]
    [∀ i, IsManifold 𝓘(ℝ, E3) ∞ (M i)]
    [∀ i, SigmaCompactSpace (M i)]
    [∀ i, RiemannianBundle (fun x : M i => TangentSpace 𝓘(ℝ, E3) x)]
    [∀ i, IsRiemannianManifold 𝓘(ℝ, E3) (M i)] [∀ i, CompleteSpace (M i)]
    [∀ i, IsContinuousRiemannianBundle E3 (fun x : M i => TangentSpace 𝓘(ℝ, E3) x)]
    {k : ℕ} (hk : 3 ≤ k)
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) (((k : ℕ∞) : ℕ∞ω) + 1) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace 𝓘(ℝ, E3) x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (hGsec : ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, E3) x), 0 ≤ G.sectionalCurvature x v w)
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E3) (M i)) (hEnorm : ∀ i, IsMetricNorm (g i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (q : N) (j : ∀ i, PartialDiffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) N (M i) ((k + 2 : ℕ) : ℕ∞ω))
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
    {W : Type} [MetricSpace W] (e : N ≃ᵢ WithLp 2 (ℝ × W)) {w₀ : W}
    (heq : e q = WithLp.toLp 2 ((0 : ℝ), w₀))
    {S : Type} [MetricSpace S] [ChartedSpace E2 S] [IsManifold (𝓡 2) ∞ S]
    [LocallyCompactSpace S] [SecondCountableTopology S]
    {s₀ : S} {FS h : S → ℝ} {Wh : Set S} {b : ClosedCell 2 → S} {Δ : ℝ} (hΔ : 1 ≤ Δ)
    (hhdef : h = edgeModelCore FS) (hW : IsOpen Wh) (hW9 : closedBall s₀ 9 ⊆ Wh)
    (hh : ContMDiffOn (𝓡 2) 𝓘(ℝ, ℝ) ∞ h Wh)
    (h4 : ∀ x, dist x s₀ < 9 → h x = 4 → mvfderiv (𝓡 2) h x ≠ 0)
    (hb : IsSmoothEmbedding (𝓡∂ 2) (𝓡 2) ∞ b)
    (hrange : range b = {x | dist x s₀ < 9 ∧ h x ≤ 4})
    (hQ : IsCompact (Icc (-(Δ / 100)) (Δ / 100) ×ˢ {s : S | dist s s₀ < 9 ∧ h s ≤ 401 / 100}))
    {n' : ℕ∞ω} (κ : ContMDiffRiemannianMetric (𝓡 2) n' E2 (TangentSpace (𝓡 2) : S → Type _))
    (Θ : Diffeomorph (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) (ℝ × S) N ((k + 2 : ℕ) : ℕ∞ω))
    (hΘfst : ∀ p : ℝ × S, (e (Θ p)).fst = p.1)
    (hΘrad : ∀ p : ℝ × S, dist (e (Θ p)).snd w₀ = Δ * dist p.2 s₀)
    (hpull : ∀ (p : ℝ × S) (v w : TangentSpace (𝓘(ℝ, ℝ).prod (𝓡 2)) p),
      G.inner (Θ p) (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p v)
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p w) = v.1 * w.1 + κ.inner p.2 v.2 w.2)
    (V : ∀ y : N, TangentSpace 𝓘(ℝ, E3) y)
    (hVdir : ∀ y, G.finiteMinimizingDirectionsTo
      {e.symm (WithLp.toLp 2 ((e y).fst + 200 * Δ, (e y).snd))} y = {V y})
    (hVcont : Continuous (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E3) N)))
    (hΘV : ∀ p : ℝ × S,
      mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p ((1 : ℝ), (0 : E2)) = V (Θ p))
    (hGN : ∀ s : S, dist s s₀ < 9 → 39 / 10 ≤ h s → h s ≤ 41 / 10 → ∀ (t a : ℝ) (Y : E2),
      mvfderiv 𝓘(ℝ, E3) (fun y => Δ * FS (Θ.symm y).2) (Θ (t, s))
        (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ (t, s) (a, Y)) =
          Δ * mvfderiv (𝓡 2) h s Y)
    (hdir : ∀ s : S, dist s s₀ < 9 → 39 / 10 ≤ h s → h s ≤ 41 / 10 →
      ∃ Y : E2, κ.inner s Y Y ≤ 1 ∧ 1 / 2 ≤ Δ * mvfderiv (𝓡 2) h s Y)
    {σ ε εN μ τ κs : ℝ} {Λ : ℝ≥0} (hσ : 0 < σ) (hσ1 : σ ≤ 1 / 10 ^ 10) (hε : 0 ≤ ε)
    (hεN : 0 ≤ εN) (hbudget : ε + 100 * Δ * Λ + εN ≤ 1 / 2000) (hμ : 0 < μ)
    (hμ1 : μ ≤ 1 / 10 ^ 8) (hτ : 0 < τ) (hτ1 : τ ≤ 1 / 10 ^ 30) (hΛ : 100 * Δ * Λ ≤ 1 / 10 ^ 8)
    (hκs : 0 < κs) (hκsΔ : κs * Δ ≤ 1 / 100)
    (hGgrad : ∀ x : N, |(e x).fst| ≤ 10 * Δ → 5 / 2 * Δ ≤ dist (e x).snd w₀ →
      dist (e x).snd w₀ ≤ 13 / 2 * Δ →
      ∀ v ∈ G.finiteMinimizingDirectionsTo (e ⁻¹' {z | z.snd = w₀}) x,
        ∀ X : TangentSpace 𝓘(ℝ, E3) x,
          |mvfderiv 𝓘(ℝ, E3) (fun y => Δ * FS (Θ.symm y).2) x X + G.inner x v X| ≤
            εN * Real.sqrt (G.inner x X X))
    (hGval : ∀ x : N, |Δ * FS (Θ.symm x).2 - dist (e x).snd w₀| < μ * Δ)
    (Q : ∀ i, M i → WithLp 2 (ℝ × ℝ)) (A : ∀ i, Set (M i)) (U F f ρ : ∀ i, M i → ℝ)
    (hU : ∀ C : Set N, IsCompact C →
      TendstoUniformlyOn (fun i x => U i (j i x)) (fun x => (e x).fst) atTop C)
    (hQU : ∀ i z, (Q i z).fst = U i z)
    (hQp : ∀ i, Q i (j i q) = 0)
    (hQdist : ∀ i, ∀ x ∈ ball (j i q) (200 * Δ), ∀ y ∈ ball (j i q) (200 * Δ),
      |dist (Q i x) (Q i y) - dist x y| ≤ τ * Δ)
    (hheight : ∀ i, ∀ x ∈ ball (j i q) (200 * Δ), 0 ≤ (Q i x).snd)
    (hQcover : ∀ i, ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ → z.snd ∈ Icc 0 (100 * Δ) →
      ∃ x ∈ ball (j i q) (200 * Δ), dist (Q i x) z ≤ τ * Δ)
    (hAc : ∀ i, IsClosed (A i)) (hpA : ∀ i, j i q ∈ A i)
    (hborder : ∀ i, ∀ a ∈ A i ∩ ball (j i q) (190 * Δ), (Q i a).snd ≤ τ * Δ)
    (hbordercover : ∀ i, ∀ t : ℝ, |t| ≤ 100 * Δ →
      ∃ a ∈ A i ∩ ball (j i q) (190 * Δ), dist (Q i a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ)
    (hsec : ∀ i, ∀ z ∈ ball (j i q) (1000 * Δ), SectionalBoundedBelowAt (g i) z (-κs ^ 2))
    (hF : ∀ i x, |F i x - infDist x (A i)| < μ * Δ)
    (OF : ∀ i, Set (M i)) (hOF : ∀ i, IsOpen (OF i))
    (hCO : ∀ i, closedBall (j i q) (20 * Δ) ∩
      {y | 3 / 4 * Δ ≤ infDist y (A i) ∧ infDist y (A i) ≤ 21 / 2 * Δ} ⊆ OF i)
    (hFs : ∀ i, ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (F i) (OF i))
    (hFgrad : ∀ i, ∀ y ∈ closedBall (j i q) (20 * Δ) ∩
        {y | 3 / 4 * Δ ≤ infDist y (A i) ∧ infDist y (A i) ≤ 21 / 2 * Δ},
      ∀ v ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo (g i) (A i) y,
        Real.sqrt ((g i).inner y (gradFun (g i) (F i) y + v) (gradFun (g i) (F i) y + v)) < ε)
    (hquot : ∀ i, ∀ y ∈ closedBall (j i q) (20 * Δ) ∩
        {y | 3 / 4 * Δ ≤ infDist y (A i) ∧ infDist y (A i) ≤ 21 / 2 * Δ},
      Real.sqrt ((g i).inner y (gradFun (g i) (fun z => F i z / ρ i z) y - gradFun (g i) (F i) y)
        (gradFun (g i) (fun z => F i z / ρ i z) y - gradFun (g i) (F i) y)) ≤ 100 * Δ * Λ)
    (hHs : ∀ i, ∀ x ∈ ball (j i q) (20 * Δ), infDist x (A i) < 41 / 4 * Δ →
      ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (edgeRowHeight Δ (F i) (ρ i)) x)
    (hρ : ∀ i, LipschitzWith Λ (ρ i)) (hρp : ∀ i, ρ i (j i q) = 1)
    (hρs : ∀ i, ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (ρ i) (ball (j i q) (100 * Δ)))
    (Of : ∀ i, Set (M i)) (hOf : ∀ i, IsOpen (Of i))
    (hOfb : ∀ i, closedBall (j i q) (100 * Δ) ⊆ Of i)
    (hfs : ∀ i, ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (f i) (Of i))
    (hflip : ∀ i, LipschitzWith (Real.toNNReal (1 + σ)) (f i))
    (hfval : ∀ i, ∀ x ∈ ball (j i q) (100 * Δ), |f i x - U i x| < μ * Δ)
    (hftest : ∀ i, ∀ x ∈ ball (j i q) (100 * Δ), ∀ x' ∈ ball (j i q) (1000 * Δ),
      100 * Δ < dist x x' → ∀ w : TangentSpace 𝓘(ℝ, E3) x, (g i).inner x w w = 1 →
      intrinsicGeodesic (g i) (hEnorm i) x w (dist x x') = x' →
      |mvfderiv 𝓘(ℝ, E3) (f i) x w - (U i x' - U i x) / dist x x'| < σ) :
    ∀ᶠ i in atTop,
      ∃ O : TopologicalSpace.Opens (M i),
      (O : Set (M i)) ⊆ ball (j i q) (20 * Δ) ∧
      (∀ y ∈ ball (j i q) (100 * Δ), |f i y| ≤ 4 * Δ → edgeRowHeight Δ (F i) (ρ i) y ≤ 4 * Δ → y ∈ O) ∧
      ∀ (a₀ b₀ : ℝ), -(4 * Δ) < a₀ → ∀ (h0 : (0 : ℝ) ∈ Ioo a₀ b₀), b₀ < 4 * Δ →
      letI := chartedSpaceTransHomeomorph (M := O) euclideanThreeProdHomeomorph
      letI : IsManifold (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ O := edgeSource_isManifold
      ∃ (hΨ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ (fun y : O => f i y))
        (hB : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
          (fun y : O => 4 * Δ - edgeRowHeight Δ (F i) (ρ i) y))
        (hreg : ∀ y : O, f i y = 0 → 0 ≤ 4 * Δ - edgeRowHeight Δ (F i) (ρ i) y →
          Surjective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) (fun y : O => f i y) y))
        (hregb : ∀ y : O, f i y = 0 → 4 * Δ - edgeRowHeight Δ (F i) (ρ i) y = 0 →
          Surjective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
            (fun y : O => ((f i y, 4 * Δ - edgeRowHeight Δ (F i) (ρ i) y) : ℝ × ℝ)) y)),
        letI := regularSublevelChartedSpace finrank_real_prod_euclideanTwo hΨ hB hreg hregb
        let Q₀ : TopologicalSpace.Opens ℝ := ⟨Ioo a₀ b₀, isOpen_Ioo⟩
        Nonempty (ClosedCell 2 ≃ₘ⟮𝓡∂ (1 + 1), 𝓡∂ (1 + 1)⟯
          {y : O // f i y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ (F i) (ρ i) y}) ∧
        CompactSpace {y : O // f i y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ (F i) (ρ i) y} ∧
        ConnectedSpace {y : O // f i y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ (F i) (ρ i) y} ∧
        (∃ Θ' : {y : O // f i y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ (F i) (ρ i) y} × Q₀ → O,
          ContMDiff ((𝓡∂ (1 + 1)).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ Θ' ∧
          (∀ p, f i (Θ' p) = p.2 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ (F i) (ρ i) (Θ' p)) ∧
          (∀ x, Θ' (x, ⟨0, h0⟩) = x) ∧ Injective Θ' ∧
          ∃ O' : Set O, IsOpen O' ∧
            (∀ y : O, f i y ∈ Ioo a₀ b₀ → 0 ≤ 4 * Δ - edgeRowHeight Δ (F i) (ρ i) y → y ∈ O') ∧
            ∃ R : O → O, ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ R O' ∧
              ∀ (y : O) (hy : f i y ∈ Ioo a₀ b₀),
                0 ≤ 4 * Δ - edgeRowHeight Δ (F i) (ρ i) y →
                ∃ hR : f i (R y) = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ (F i) (ρ i) (R y),
                  Θ' (⟨R y, hR⟩, ⟨f i y, hy⟩) = y) ∧
        ∀ y : {y : O // f i y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ (F i) (ρ i) y},
          (𝓡∂ (1 + 1)).IsBoundaryPoint y ↔ edgeRowHeight Δ (F i) (ρ i) y = 4 * Δ := by
  have hΔ0 : 0 < Δ := by linarith
  have hr2 : (2 : ℕ∞) ≤ (k : ℕ∞) := by exact_mod_cast (show 2 ≤ k by omega)
  have hK2 : 2 ≤ k + 2 := by omega
  -- numerical facts
  have hsqτ : Real.sqrt τ ≤ 1 / 10 ^ 15 := by
    refine Real.sqrt_le_iff.mpr ⟨by norm_num, ?_⟩
    have h1 : (1 / 10 ^ 15 : ℝ) ^ 2 = 1 / 10 ^ 30 := by norm_num
    rw [h1]
    exact hτ1
  have hsqτ0 : 0 < Real.sqrt τ := Real.sqrt_pos.mpr hτ
  have hc : 40 * Real.sqrt (20 * Real.sqrt τ + τ) < 1 / 10 ^ 5 := by
    have h1 : Real.sqrt (20 * Real.sqrt τ + τ) < 1 / 4000000 := by
      rw [Real.sqrt_lt' (by norm_num)]
      have h2 : (1 / 4000000 : ℝ) ^ 2 = 1 / 16000000000000 := by norm_num
      rw [h2]
      have h3 : (1 / 10 ^ 30 : ℝ) ≤ 1 / 10 ^ 15 := by norm_num
      have h4 : (1 / 10 ^ 15 : ℝ) < 1 / 1000000000000000 + 1 := by norm_num
      have h5 : (20 : ℝ) / 10 ^ 15 + 1 / 10 ^ 30 < 1 / 16000000000000 := by norm_num
      have h6 : 20 * Real.sqrt τ ≤ 20 / 10 ^ 15 := by
        have := mul_le_mul_of_nonneg_left hsqτ (by norm_num : (0 : ℝ) ≤ 20)
        linarith [show (20 : ℝ) * (1 / 10 ^ 15) = 20 / 10 ^ 15 by ring]
      linarith
    linarith
  have hh21 : 20 * Real.sqrt τ < 21 * Real.sqrt τ := by linarith
  -- the model cylinders on `N`
  set Cyl : Set N := {x | |(e x).fst| ≤ 6 * Δ ∧ dist (e x).snd w₀ ≤ 9 * Δ} with hCyldef
  set Cyl5 : Set N := {x | |(e x).fst| ≤ 5 * Δ ∧ dist (e x).snd w₀ ≤ 5 * Δ} with hCyl5def
  have hfstc : Continuous fun x : N => (e x).fst := (lipschitzWith_heightCoord e).continuous
  have hradc : Continuous fun x : N => dist (e x).snd w₀ := (lipschitzWith_axisDist e w₀).continuous
  have hCylq : ∀ x ∈ Cyl, dist x q ≤ 15 * Δ := fun x hx =>
    (dist_le_abs_fst_add_axisDist e heq x).trans (by linarith [hx.1, hx.2])
  have hCyl : IsCompact Cyl := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ ?_
    · exact (isClosed_le (continuous_abs.comp hfstc) continuous_const).inter
        (isClosed_le hradc continuous_const)
    · exact (isBounded_closedBall (x := q) (r := 15 * Δ)).subset fun x hx =>
        mem_closedBall.mpr (hCylq x hx)
  have hCyl5sub : Cyl5 ⊆ Cyl := fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hCyl5 : IsCompact Cyl5 := by
    refine hCyl.of_isClosed_subset ?_ hCyl5sub
    exact (isClosed_le (continuous_abs.comp hfstc) continuous_const).inter
      (isClosed_le hradc continuous_const)
  have hcylN : ∀ x ∈ edgeModelCylinder s₀ Δ, Θ x ∈ Cyl := by
    intro x hx
    refine ⟨?_, ?_⟩
    · rw [hΘfst]
      exact (abs_lt.mpr ⟨hx.1.1, hx.1.2⟩).le
    · rw [hΘrad]
      have := mul_lt_mul_of_pos_left hx.2 hΔ0
      linarith
  have hcyl5 : ∀ x ∈ Cyl5, Θ.symm x ∈ edgeModelCylinder s₀ Δ := by
    intro x hx
    have hx' : x = Θ (Θ.symm x) := (Θ.apply_symm_apply x).symm
    have h1 := hx.1
    have h2 := hx.2
    rw [hx', hΘfst] at h1
    rw [hx', hΘrad] at h2
    refine ⟨⟨by linarith [(abs_le.mp h1).1], by linarith [(abs_le.mp h1).2]⟩, ?_⟩
    by_contra hcon
    push Not at hcon
    have := mul_le_mul_of_nonneg_left hcon hΔ0.le
    linarith
  -- the first coordinate of `Q` converges to `t`
  have hcoord : TendstoUniformlyOn (fun i x => (Q i (j i x)).fst) (fun x => (e x).fst) atTop
      (closedBall q (100 * Δ)) := by
    have h := hU _ (isCompact_closedBall q (100 * Δ))
    simp only [← hQU] at h
    exact h
  have hfQ : ∀ i, ∀ x ∈ ball (j i q) (100 * Δ), |f i x - (Q i x).fst| < μ * Δ := by
    intro i x hx
    rw [hQU]
    exact hfval i x hx
  ------------------------------------------------------------------ (LFR28.3)
  set ℓ : ℝ := 200 * Δ with hℓdef
  have hℓ : 0 < ℓ := by positivity
  have hball3 : ∀ᶠ i in atTop, ∀ x ∈ Cyl, j i x ∈ ball (j i q) (100 * Δ) ∧
      j i (e.symm (WithLp.toLp 2 ((e x).fst + ℓ, (e x).snd))) ∈ ball (j i q) (1000 * Δ) ∧
      100 * Δ < dist (j i x) (j i (e.symm (WithLp.toLp 2 ((e x).fst + ℓ, (e x).snd)))) := by
    filter_upwards [hdist (300 * Δ) Δ hΔ0] with i hi x hx
    set y := e.symm (WithLp.toLp 2 ((e x).fst + ℓ, (e x).snd)) with hydef
    have hey : e y = WithLp.toLp 2 ((e x).fst + ℓ, (e x).snd) := e.apply_symm_apply _
    have hyq : dist y q ≤ 215 * Δ := by
      have h := dist_le_abs_fst_add_axisDist e heq y
      rw [hey] at h
      have h1 : |(e x).fst + ℓ| ≤ 206 * Δ :=
        (abs_add_le _ _).trans (by rw [abs_of_pos hℓ]; linarith [hx.1])
      have h2 := hx.2
      change dist y q ≤ |(e x).fst + ℓ| + dist (e x).snd w₀ at h
      linarith
    have hxy : dist x y = ℓ := by
      rw [hydef, dist_vertical_shift e ℓ x, abs_of_pos hℓ]
    have hxq := hCylq x hx
    have hx3 : x ∈ ball q (300 * Δ) := mem_ball.mpr (by linarith)
    have hy3 : y ∈ ball q (300 * Δ) := mem_ball.mpr (by linarith)
    have hq3 : q ∈ ball q (300 * Δ) := mem_ball_self (by positivity)
    have h1 := abs_lt.mp (hi x hx3 q hq3)
    have h2 := abs_lt.mp (hi y hy3 q hq3)
    have h3 := abs_lt.mp (hi x hx3 y hy3)
    refine ⟨mem_ball.mpr (by linarith), mem_ball.mpr (by linarith), by linarith⟩
  have hfsm : ∀ᶠ i in atTop, ∀ x ∈ Cyl, MDifferentiableAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) (f i) (j i x) := by
    filter_upwards [hball3] with i hi x hx
    have hO := hOfb i (ball_subset_closedBall (hi x hx).1)
    exact ((hfs i _ hO).contMDiffAt ((hOf i).mem_nhds hO)).mdifferentiableAt (by simp)
  have h19 : ∀ᶠ i in atTop, ∀ x ∈ Cyl,
      ∀ w ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo (g i)
        {j i (e.symm (WithLp.toLp 2 ((e x).fst + ℓ, (e x).snd)))} (j i x),
        |mvfderiv 𝓘(ℝ, E3) (f i) (j i x) w -
          (U i (j i (e.symm (WithLp.toLp 2 ((e x).fst + ℓ, (e x).snd)))) - U i (j i x)) /
            dist (j i x) (j i (e.symm (WithLp.toLp 2 ((e x).fst + ℓ, (e x).snd))))| < σ := by
    filter_upwards [hball3] with i hi x hx w hw
    obtain ⟨hxb, hshb, hlt⟩ := hi x hx
    obtain ⟨hw1, hwend⟩ := hw
    rw [infDist_singleton, mem_singleton_iff,
      Bundle.ContMDiffRiemannianMetric.expMap_smul_eq_intrinsicGeodesic (g i) (hEnorm i)] at hwend
    exact hftest i (j i x) hxb _ hshb hlt w hw1 hwend
  have h283 := eventually_abs_mvfderiv_sub_inner_vertical_le_thousandth hr2 G hGnorm g hmetric hK2
    q j hexh hconv hdist hcover e hℓ hσ hCyl V hVdir hVcont f U hflip hfsm h19 hU hσ1
  ------------------------------------------------------------------ (LFR28.2), (LFR28.4)
  have hhgt := eventually_abs_height_sub_axisDist_le (fun i => (j i : N → M i)) q hdist e heq
    hΔ0 hτ.le (by linarith) Q hQp hQdist hheight hcoord
  have hh0 : 0 < 20 * Real.sqrt τ := by positivity
  have hh1 : 20 * Real.sqrt τ < 1 / 100 := by linarith
  have hlam : 100 * Δ * (Λ : ℝ) < 1 / 100 := by linarith
  have h284 := eventually_abs_mvfderiv_edgeQuotient_comp_sub_model_le hr2 G hGnorm hGsec g hmetric
    hK2 q j hexh hconv hdist hcover e heq hΔ0 hτ.le (by linarith) hκs hκsΔ hh0 hh1 Q A hQp
    hQdist hheight hQcover hpA hborder hbordercover hsec hhgt hAc F ρ hε hρ hρp hlam hρs OF hOF
    hCO hFs hFgrad hquot (fun y => Δ * FS (Θ.symm y).2) hGgrad (1 / 10 ^ 5) hc (1 / 10 ^ 5)
    (by norm_num)
  have hcore := eventually_mem_edgeSmoothingCore q j hdist e heq hΔ0 (by linarith : τ ≤ 1 / 4) hh1
    Q A hQp hQdist hheight hpA hborder hbordercover hhgt
  ------------------------------------------------------------------ (LFR28.5) and B5
  let Ω : TopologicalSpace.Opens N :=
    ⟨Θ '' edgeModelCylinder s₀ Δ, Θ.toHomeomorph.isOpenMap _ (edgeModelCylinder s₀ Δ).isOpen⟩
  have hΩ : ∀ x ∈ Ω, |(e x).fst| ≤ 6 * Δ ∧ dist (e x).snd w₀ ≤ 9 * Δ := by
    rintro _ ⟨x, hx, rfl⟩
    exact hcylN x hx
  have hI5 := eventually_edgeValueComparison (fun i => (j i : N → M i)) q hdist e heq hΔ0 hμ.le
    hτ.le (by linarith) (by norm_num : (0 : ℝ) ≤ 1 / 10 ^ 8) (by norm_num) hh21
    (by linarith) hΛ Q A F f ρ (fun y => Δ * FS (Θ.symm y).2) hQp hQdist hheight hcoord hpA
    hborder hbordercover hF hfQ hGval hρ hρp Ω hΩ
  have hB5 := eventually_edgeSourceSlab_mem_image (fun i => (j i : N → M i)) q hdist hcover e heq
    hΔ0 (by linarith : μ ≤ 1 / 1000) hτ.le (by linarith) (by norm_num : (1 / 10 ^ 8 : ℝ) ≤ 1 / 1000)
    hh21 (by linarith) hΛ Q A F f ρ hQp hQdist hheight hcoord hpA hborder hbordercover
    (fun i x => (hF i x).le) (fun i x hx => (hfQ i x hx).le) hρ hρp
  ------------------------------------------------------------------ one late index
  have hGNΘ : ∀ x : ℝ × S, edgeSublevelProfile (Δ * FS (Θ.symm (Θ x)).2 / Δ) = h x.2 := by
    intro x
    rw [Θ.symm_apply_apply, mul_div_cancel_left₀ _ hΔ0.ne', hhdef]
    rfl
  have hc0 : 0 ≤ ε + 100 * Δ * Λ + εN + 1 / 10 ^ 5 + 1 / 10 ^ 5 := by positivity
  have hc1 : ε + 100 * Δ * Λ + εN + 1 / 10 ^ 5 + 1 / 10 ^ 5 ≤ 1 / 1000 := by linarith
  filter_upwards [hexh Cyl hCyl, h283, h284, hcore, hI5, hB5] with i hsrc h3i h4i hci hvi hbi
  have _ : ProperSpace (M i) := Manifold.properSpace_of_isRiemannianManifold 𝓘(ℝ, E3)
  have hρpos : ∀ y ∈ ball (j i q) (100 * Δ), 0 < ρ i y := by
    intro y hy
    have h1 := (hρ i).dist_le_mul y (j i q)
    rw [Real.dist_eq, hρp i] at h1
    have h2 : (Λ : ℝ) * dist y (j i q) ≤ Λ * (100 * Δ) :=
      mul_le_mul_of_nonneg_left (mem_ball.mp hy).le Λ.coe_nonneg
    have h3 := (abs_le.mp h1).1
    linarith
  refine edgeRowSlab_disk_bundle_of_limit_estimates G e heq hΔ0 hhdef hW hW9 hh h4 hb hrange hQ κ
    (by omega) Θ hΘfst hΘrad hpull V hΘV hGN hdir (μ := μ) (by linarith) hGval (j i) (A i) (F i)
    (f i) (ρ i) (OF i) (hOF i) (hFs i) (hHs i)
    (fun x hx => ((hρs i x hx).contMDiffAt (isOpen_ball.mem_nhds hx)).continuousAt) (Of i)
    (hOf i) (hOfb i) (hfs i) hc0 hc1 hsrc (fun x h1 h2 Z => h3i x ⟨h1, h2⟩ Z)
    (fun x ht hr1 hr2 => ?_) (fun x hx => ?_) (fun y hy hfy hη => ?_)
  · have hcx := hci x ht hr1 hr2
    have hj100 : j i x ∈ ball (j i q) (100 * Δ) := by
      have := mem_closedBall.mp hcx.1
      exact mem_ball.mpr (by linarith)
    exact ⟨hCO i hcx, hj100, hρpos _ hj100, h4i x ht hr1 hr2⟩
  · obtain ⟨h1, h2, h3, -, h5, h6⟩ := hvi ⟨Θ x, x, hx, rfl⟩
    simp only [hΘfst] at h5 h6
    rw [hGNΘ] at h6
    rw [Θ.symm_apply_apply] at h3
    exact ⟨h1, by linarith, h3, h5, h6⟩
  · obtain ⟨x, -, hxy, ht, hr⟩ := hbi y hy hfy hη
    exact ⟨x, hxy, ht, hr⟩

/-- **LFR28.1 (the whole source edge disk bundle), sequence form.** See the module docstring. -/
theorem eventually_edgeSourceSlab_disk_bundle
    {N : Type} [MetricSpace N] [ChartedSpace E3 N] [IsManifold 𝓘(ℝ, E3) ∞ N] [ProperSpace N]
    [ConnectedSpace N]
    [RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x)] [IsRiemannianManifold 𝓘(ℝ, E3) N]
    {M : ℕ → Type} [∀ i, MetricSpace (M i)] [∀ i, ChartedSpace E3 (M i)]
    [∀ i, IsManifold 𝓘(ℝ, E3) ∞ (M i)]
    [∀ i, SigmaCompactSpace (M i)]
    [∀ i, RiemannianBundle (fun x : M i => TangentSpace 𝓘(ℝ, E3) x)]
    [∀ i, IsRiemannianManifold 𝓘(ℝ, E3) (M i)] [∀ i, CompleteSpace (M i)]
    [∀ i, IsContinuousRiemannianBundle E3 (fun x : M i => TangentSpace 𝓘(ℝ, E3) x)]
    {k : ℕ} (hk : 3 ≤ k)
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E3) (((k : ℕ∞) : ℕ∞ω) + 1) E3
      (TangentSpace 𝓘(ℝ, E3) : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace 𝓘(ℝ, E3) x),
      ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (hGsec : ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, E3) x), 0 ≤ G.sectionalCurvature x v w)
    (oN : ManifoldOrientation (𝓡 3) N 3)
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E3) (M i)) (hEnorm : ∀ i, IsMetricNorm (g i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (q : N) (j : ∀ i, PartialDiffeomorph 𝓘(ℝ, E3) 𝓘(ℝ, E3) N (M i) ((k + 2 : ℕ) : ℕ∞ω))
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
    (hcov : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ y ∈ ball (j i q) R,
      ∃ x ∈ ball q (R + 1), dist (j i x) y < ε)
    {W : Type} [MetricSpace W] (e : N ≃ᵢ WithLp 2 (ℝ × W)) {w₀ : W}
    (heq : e q = WithLp.toLp 2 ((0 : ℝ), w₀))
    {Δ σ ε μ τ κs : ℝ} {Λ : ℝ≥0} (hΔ : 1 ≤ Δ) (hσ : 0 < σ) (hσ1 : σ ≤ 1 / 10 ^ 10) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1 / 10 ^ 8) (hμ : 0 < μ)
    (hμ1 : μ ≤ 1 / 10 ^ 8) (hτ : 0 < τ) (hτ1 : τ ≤ 1 / 10 ^ 30) (hΛ : 100 * Δ * Λ ≤ 1 / 10 ^ 8)
    (hκs : 0 < κs) (hκsΔ : κs * Δ ≤ 1 / 100)
    (Q : ∀ i, M i → WithLp 2 (ℝ × ℝ)) (A : ∀ i, Set (M i)) (U F f ρ : ∀ i, M i → ℝ)
    (hU : ∀ C : Set N, IsCompact C →
      TendstoUniformlyOn (fun i x => U i (j i x)) (fun x => (e x).fst) atTop C)
    (hQU : ∀ i z, (Q i z).fst = U i z)
    (hQp : ∀ i, Q i (j i q) = 0)
    (hQdist : ∀ i, ∀ x ∈ ball (j i q) (200 * Δ), ∀ y ∈ ball (j i q) (200 * Δ),
      |dist (Q i x) (Q i y) - dist x y| ≤ τ * Δ)
    (hheight : ∀ i, ∀ x ∈ ball (j i q) (200 * Δ), 0 ≤ (Q i x).snd)
    (hQcover : ∀ i, ∀ z : WithLp 2 (ℝ × ℝ), |z.fst| ≤ 100 * Δ → z.snd ∈ Icc 0 (100 * Δ) →
      ∃ x ∈ ball (j i q) (200 * Δ), dist (Q i x) z ≤ τ * Δ)
    (hAc : ∀ i, IsClosed (A i)) (hpA : ∀ i, j i q ∈ A i)
    (hborder : ∀ i, ∀ a ∈ A i ∩ ball (j i q) (190 * Δ), (Q i a).snd ≤ τ * Δ)
    (hbordercover : ∀ i, ∀ t : ℝ, |t| ≤ 100 * Δ →
      ∃ a ∈ A i ∩ ball (j i q) (190 * Δ), dist (Q i a) (WithLp.toLp 2 (t, (0 : ℝ))) ≤ τ * Δ)
    (hsec : ∀ i, ∀ z ∈ ball (j i q) (1000 * Δ), SectionalBoundedBelowAt (g i) z (-κs ^ 2))
    (hF : ∀ i x, |F i x - infDist x (A i)| < μ * Δ)
    (OF : ∀ i, Set (M i)) (hOF : ∀ i, IsOpen (OF i))
    (hCO : ∀ i, closedBall (j i q) (20 * Δ) ∩
      {y | 3 / 4 * Δ ≤ infDist y (A i) ∧ infDist y (A i) ≤ 21 / 2 * Δ} ⊆ OF i)
    (hFs : ∀ i, ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (F i) (OF i))
    (hFgrad : ∀ i, ∀ y ∈ closedBall (j i q) (20 * Δ) ∩
        {y | 3 / 4 * Δ ≤ infDist y (A i) ∧ infDist y (A i) ≤ 21 / 2 * Δ},
      ∀ v ∈ ContMDiffRiemannianMetric.finiteMinimizingDirectionsTo (g i) (A i) y,
        Real.sqrt ((g i).inner y (gradFun (g i) (F i) y + v) (gradFun (g i) (F i) y + v)) < ε)
    (hquot : ∀ i, ∀ y ∈ closedBall (j i q) (20 * Δ) ∩
        {y | 3 / 4 * Δ ≤ infDist y (A i) ∧ infDist y (A i) ≤ 21 / 2 * Δ},
      Real.sqrt ((g i).inner y (gradFun (g i) (fun z => F i z / ρ i z) y - gradFun (g i) (F i) y)
        (gradFun (g i) (fun z => F i z / ρ i z) y - gradFun (g i) (F i) y)) ≤ 100 * Δ * Λ)
    (hHs : ∀ i, ∀ x ∈ ball (j i q) (20 * Δ), infDist x (A i) < 41 / 4 * Δ →
      ContMDiffAt 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (edgeRowHeight Δ (F i) (ρ i)) x)
    (hρ : ∀ i, LipschitzWith Λ (ρ i)) (hρp : ∀ i, ρ i (j i q) = 1)
    (hρs : ∀ i, ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (ρ i) (ball (j i q) (100 * Δ)))
    (Of : ∀ i, Set (M i)) (hOf : ∀ i, IsOpen (Of i))
    (hOfb : ∀ i, closedBall (j i q) (100 * Δ) ⊆ Of i)
    (hfs : ∀ i, ContMDiffOn 𝓘(ℝ, E3) 𝓘(ℝ, ℝ) ∞ (f i) (Of i))
    (hflip : ∀ i, LipschitzWith (Real.toNNReal (1 + σ)) (f i))
    (hfval : ∀ i, ∀ x ∈ ball (j i q) (100 * Δ), |f i x - U i x| < μ * Δ)
    (hftest : ∀ i, ∀ x ∈ ball (j i q) (100 * Δ), ∀ x' ∈ ball (j i q) (1000 * Δ),
      100 * Δ < dist x x' → ∀ w : TangentSpace 𝓘(ℝ, E3) x, (g i).inner x w w = 1 →
      intrinsicGeodesic (g i) (hEnorm i) x w (dist x x') = x' →
      |mvfderiv 𝓘(ℝ, E3) (f i) x w - (U i x' - U i x) / dist x x'| < σ) :
    ∀ᶠ i in atTop,
      ∃ O : TopologicalSpace.Opens (M i),
      (O : Set (M i)) ⊆ ball (j i q) (20 * Δ) ∧
      (∀ y ∈ ball (j i q) (100 * Δ), |f i y| ≤ 4 * Δ → edgeRowHeight Δ (F i) (ρ i) y ≤ 4 * Δ → y ∈ O) ∧
      ∀ (a₀ b₀ : ℝ), -(4 * Δ) < a₀ → ∀ (h0 : (0 : ℝ) ∈ Ioo a₀ b₀), b₀ < 4 * Δ →
      letI := chartedSpaceTransHomeomorph (M := O) euclideanThreeProdHomeomorph
      letI : IsManifold (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ O := edgeSource_isManifold
      ∃ (hΨ : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞ (fun y : O => f i y))
        (hB : ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) ∞
          (fun y : O => 4 * Δ - edgeRowHeight Δ (F i) (ρ i) y))
        (hreg : ∀ y : O, f i y = 0 → 0 ≤ 4 * Δ - edgeRowHeight Δ (F i) (ρ i) y →
          Surjective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ) (fun y : O => f i y) y))
        (hregb : ∀ y : O, f i y = 0 → 4 * Δ - edgeRowHeight Δ (F i) (ρ i) y = 0 →
          Surjective (mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, ℝ × ℝ)
            (fun y : O => ((f i y, 4 * Δ - edgeRowHeight Δ (F i) (ρ i) y) : ℝ × ℝ)) y)),
        letI := regularSublevelChartedSpace finrank_real_prod_euclideanTwo hΨ hB hreg hregb
        let Q₀ : TopologicalSpace.Opens ℝ := ⟨Ioo a₀ b₀, isOpen_Ioo⟩
        Nonempty (ClosedCell 2 ≃ₘ⟮𝓡∂ (1 + 1), 𝓡∂ (1 + 1)⟯
          {y : O // f i y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ (F i) (ρ i) y}) ∧
        CompactSpace {y : O // f i y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ (F i) (ρ i) y} ∧
        ConnectedSpace {y : O // f i y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ (F i) (ρ i) y} ∧
        (∃ Θ' : {y : O // f i y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ (F i) (ρ i) y} × Q₀ → O,
          ContMDiff ((𝓡∂ (1 + 1)).prod 𝓘(ℝ, ℝ)) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ Θ' ∧
          (∀ p, f i (Θ' p) = p.2 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ (F i) (ρ i) (Θ' p)) ∧
          (∀ x, Θ' (x, ⟨0, h0⟩) = x) ∧ Injective Θ' ∧
          ∃ O' : Set O, IsOpen O' ∧
            (∀ y : O, f i y ∈ Ioo a₀ b₀ → 0 ≤ 4 * Δ - edgeRowHeight Δ (F i) (ρ i) y → y ∈ O') ∧
            ∃ R : O → O, ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ R O' ∧
              ∀ (y : O) (hy : f i y ∈ Ioo a₀ b₀),
                0 ≤ 4 * Δ - edgeRowHeight Δ (F i) (ρ i) y →
                ∃ hR : f i (R y) = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ (F i) (ρ i) (R y),
                  Θ' (⟨R y, hR⟩, ⟨f i y, hy⟩) = y) ∧
        ∀ y : {y : O // f i y = 0 ∧ 0 ≤ 4 * Δ - edgeRowHeight Δ (F i) (ρ i) y},
          (𝓡∂ (1 + 1)).IsBoundaryPoint y ↔ edgeRowHeight Δ (F i) (ρ i) y = 4 * Δ := by
  have hΔ0 : 0 < Δ := by linarith
  have hΔi : 0 < Δ⁻¹ := inv_pos.mpr hΔ0
  have hk2 : (2 : ℕ∞) ≤ (k : ℕ∞) := by exact_mod_cast (show 2 ≤ k by omega)
  have _ : CompleteSpace N := complete_of_proper
  have _ : SecondCountableTopology N := secondCountable_of_proper
  -- stage 1: the vertical product chart on the oriented carrier
  obtain ⟨S, mS, cS, iS, ψ, κ0, Θ, hcS, hconnS, ⟨oS⟩, hsecS, hRS, he, hpull, hvert⟩ :=
    edgeRowModelChart_of_carrier G hk2 hGnorm hGsec oN e
  let _ := mS
  let _ := cS
  have _ := iS
  have _ := hcS
  have _ := hconnS
  let _ : RiemannianBundle (fun x : S => TangentSpace (𝓡 2) x) := ⟨κ0.toRiemannianMetric⟩
  obtain ⟨hRiemS, hκnorm⟩ := hRS
  have _ := hRiemS
  let κ : ContMDiffRiemannianMetric (𝓡 2) (((k : ℕ∞) : ℕ∞ω) + 1) E2
      (TangentSpace (𝓡 2) : S → Type _) :=
    { κ0 with contMDiff := by rw [withTop_natCast_add_one]; exact κ0.contMDiff }
  have _ : ProperSpace S := Manifold.properSpace_of_isRiemannianManifold (𝓡 2)
  -- I7(a): the endpoint model on the factor
  have hcoord : TendstoUniformlyOn (fun i x => (Q i (j i x)).fst) (fun x => (e x).fst) atTop
      (closedBall q (100 * Δ)) := by
    have h := hU _ (isCompact_closedBall q (100 * Δ))
    simp only [← hQU] at h
    exact h
  obtain ⟨eW, heW0, -, -, -, heWnn, heWdist, heWdense⟩ :=
    exists_edgeEndpointModel (fun i => (j i : N → M i)) q hdist hcov e heq hΔ hτ
      (by linarith) Q hQp hQdist hheight hQcover hcoord
  -- stage 2: the model surface data on the rescaled carrier
  have hδε : 20 * τ ≤ (1 / 1000 : ℝ) ^ 2 / 24000000 := by
    have h1 : (1 / 1000 : ℝ) ^ 2 / 24000000 = 1 / 24000000000000 := by norm_num
    rw [h1]
    have h2 : (20 : ℝ) / 10 ^ 30 ≤ 1 / 24000000000000 := by norm_num
    linarith
  have hm : (2 : WithTop ℕ∞) ≤ ((k + 2 : ℕ) : ℕ∞ω) := by exact_mod_cast (show 2 ≤ k + 2 by omega)
  obtain ⟨s₀, FS, h, Wh, b, hψs₀, hhdef, hmod, hGgrad, hGval⟩ :=
    edgeRowModelSurface hk G hGnorm κ (fun x w => hκnorm x w) (fun x v w => hsecS x v w) oS e ψ hm
      Θ he hpull hΔ0 w₀ eW (εm := 1 / 1000) (δ := 20 * τ) (μ := μ) (by norm_num) (by norm_num)
      (by positivity) hδε hμ (by linarith) heW0 heWnn heWdist heWdense
  obtain ⟨hW, hW9, hh, h4, hb, hrange, hQ, hGN, hdir⟩ := hmod
  -- LFR18: the vertical field
  have hℓ : (0 : ℝ) < 200 * Δ := by positivity
  obtain ⟨V, hVdir, hVcont, -⟩ := exists_vertical_field_eventually_inverse_directions_close hk2 G
    hGnorm g hmetric (by omega : 2 ≤ k + 2) q j hexh hconv hdist hcover e hℓ
    (isCompact_singleton (x := q))
  have hΘV : ∀ p : ℝ × S,
      mfderiv (𝓘(ℝ, ℝ).prod (𝓡 2)) 𝓘(ℝ, E3) Θ p ((1 : ℝ), (0 : E2)) = V (Θ p) := fun p =>
    mfderiv_edgeCylinder_eq_verticalField G e Θ (fun p => hvert p (200 * Δ) hℓ) V hVdir p
  have hΘfst : ∀ p : ℝ × S, (e (Θ p)).fst = p.1 := fun p => by
    rw [he]
    rfl
  have hΘrad : ∀ p : ℝ × S,
      dist (e (Θ p)).snd w₀ = Δ * @dist S (mS.rescale Δ⁻¹ hΔi).toDist p.2 s₀ := by
    intro p
    rw [MetricSpace.rescale_dist, he, ← hψs₀]
    change dist (ψ p.2) (ψ s₀) = _
    rw [ψ.dist_eq, ← mul_assoc, mul_inv_cancel₀ hΔ0.ne', one_mul]
  have hεN : (0 : ℝ) ≤ 1 / 1000 / 25 := by norm_num
  have hbudget : ε + 100 * Δ * Λ + 1 / 1000 / 25 ≤ 1 / 2000 := by linarith
  have hlcS : LocallyCompactSpace S := inferInstance
  have hscS : SecondCountableTopology S := inferInstance
  let _ : MetricSpace S := mS.rescale Δ⁻¹ hΔi
  have _ : LocallyCompactSpace S := hlcS
  have _ : SecondCountableTopology S := hscS
  exact eventually_edgeSourceSlab_disk_bundle_of_model hk G hGnorm hGsec g hEnorm hmetric q j hexh
    hconv hdist hcover e heq hΔ hhdef hW hW9 hh h4 hb hrange hQ κ Θ hΘfst hΘrad hpull V hVdir
    hVcont hΘV hGN hdir hσ hσ1 hε hεN hbudget hμ hμ1 hτ hτ1 hΛ hκs hκsΔ hGgrad hGval Q A U F f ρ
    hU hQU hQp hQdist hheight hQcover hAc hpA hborder hbordercover hsec hF OF hOF hCO hFs hFgrad
    hquot hHs hρ hρp hρs Of hOf hOfb hfs hflip hfval hftest

end DifferentialGeometry.Geometry.Collapse
