import DifferentialGeometry.Geometry.Collapse.EdgeRowSequence

/-!
# Consumers of the LFR28 row in sequence form

* `slabFibreHomeomorph`: the fibre `{f = 0, H ≤ c}` of an open `O ⊆ B` that contains every fibre
  point of `B`, read as a subtype of `O` (the regular-sublevel carrier of Row-A), is homeomorphic to
  the same fibre read as a subtype of the ambient space, cut by `B`.
* `eventually_edgeSourceSlab_fibre_homeomorph_closedCell` (**concrete consumer**): along the
  sequence of `eventually_edgeSourceSlab_disk_bundle`, eventually the ENTIRE source fibre
  `{y ∈ B(p_i, 100Δ) : f_i y = 0, H_i y ≤ 4Δ}` is homeomorphic to the closed disk `ClosedCell 2`,
  compact and connected (the topological `fibre_disk` clause of the intended edge disk packet).
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

local instance nezero_finrank_euclidean_three_app_LFR28ROW2 : NeZero (Module.finrank ℝ E3) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

/-- The fibre `{f = 0, H ≤ c}` of `O` (subtype of `O`) is the fibre of `B` (subtype of `X`) when
`O ⊆ B` and every fibre point of `B` lies in `O`. -/
def slabFibreHomeomorph {X : Type*} [TopologicalSpace X] (O : TopologicalSpace.Opens X)
    {B : Set X} {f H : X → ℝ} {c : ℝ} (hOB : (O : Set X) ⊆ B)
    (hBO : ∀ y ∈ B, f y = 0 → H y ≤ c → y ∈ O) :
    {y : O // f y = 0 ∧ 0 ≤ c - H y} ≃ₜ {y : X // y ∈ B ∧ f y = 0 ∧ H y ≤ c} where
  toFun y := ⟨y.1.1, hOB y.1.2, y.2.1, by linarith [y.2.2]⟩
  invFun y := ⟨⟨y.1, hBO y.1 y.2.1 y.2.2.1 y.2.2.2⟩, y.2.2.1, by linarith [y.2.2.2]⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _

/-- **Concrete consumer.** Eventually the entire source fibre `{f_i = 0, H_i ≤ 4Δ}` of
`B(p_i, 100Δ)` is homeomorphic to `ClosedCell 2`, compact and connected. -/
theorem eventually_edgeSourceSlab_fibre_homeomorph_closedCell
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
    ∀ᶠ i in atTop, Nonempty ({y : M i // y ∈ ball (j i q) (100 * Δ) ∧ f i y = 0 ∧
        edgeRowHeight Δ (F i) (ρ i) y ≤ 4 * Δ} ≃ₜ ClosedCell 2) ∧
      CompactSpace {y : M i // y ∈ ball (j i q) (100 * Δ) ∧ f i y = 0 ∧
        edgeRowHeight Δ (F i) (ρ i) y ≤ 4 * Δ} ∧
      ConnectedSpace {y : M i // y ∈ ball (j i q) (100 * Δ) ∧ f i y = 0 ∧
        edgeRowHeight Δ (F i) (ρ i) y ≤ 4 * Δ} := by
  have hΔ0 : 0 < Δ := by linarith
  filter_upwards [eventually_edgeSourceSlab_disk_bundle hk G hGnorm hGsec oN g hEnorm hmetric q j
    hexh hconv hdist hcover hcov e heq hΔ hσ hσ1 hε hε1 hμ hμ1 hτ hτ1 hΛ hκs hκsΔ Q A U F f ρ hU
    hQU hQp hQdist hheight hQcover hAc hpA hborder hbordercover hsec hF OF hOF hCO hFs hFgrad
    hquot hHs hρ hρp hρs Of hOf hOfb hfs hflip hfval hftest] with i hi
  obtain ⟨O, hOsub, hslab, hrow⟩ := hi
  have hr := hrow (-(2 * Δ)) (2 * Δ) (by linarith) ⟨by linarith, by linarith⟩ (by linarith)
  obtain ⟨hΨ, hB, hreg, hregb, hrest⟩ := hr
  let _ := chartedSpaceTransHomeomorph (M := O) euclideanThreeProdHomeomorph
  have _ : IsManifold (𝓘(ℝ, ℝ).prod (𝓡 2)) ∞ O := edgeSource_isManifold
  let _ := regularSublevelChartedSpace finrank_real_prod_euclideanTwo hΨ hB hreg hregb
  obtain ⟨hφ, hc, hconn, -⟩ := hrest
  obtain ⟨φ⟩ := hφ
  let T := slabFibreHomeomorph O (B := ball (j i q) (100 * Δ)) (f := f i)
    (H := edgeRowHeight Δ (F i) (ρ i)) (c := 4 * Δ)
    (fun y hy => ball_subset_ball (by linarith) (hOsub hy))
    (fun y hy hf hH => hslab y hy (by rw [hf, abs_zero]; positivity) hH)
  exact ⟨⟨((Diffeomorph.toHomeomorph φ).trans T).symm⟩, T.compactSpace,
    T.connectedSpace_iff.mp hconn⟩

end DifferentialGeometry.Geometry.Collapse
