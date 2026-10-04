import DifferentialGeometry.Geometry.Collapse.SublevelCore.FiniteCoreIsotopy
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.SmoothComparisonMaps

/-!
# Consumer: LC51′ on LFR14 data through LFR48's smooth comparison maps

`exists_smooth_core_isotopy_of_finite_limit`: T0-shaped data (a `C^{K-1}` limit metric `G`,
`4 ≤ K`, pointed `C^K` partial diffeomorphisms `j i`, exhaustion, chart convergence of order
`K - 1`, distortion) are first replaced by LFR48's SMOOTH comparison maps `jt i`
(`exists_smooth_comparison_maps_of_finite_limit`), `C⁰`-close to `j i`; LC51′ then carries the
model core `jt i (D)` onto every radial sublevel `{η i ≤ ρ}`, `ρ ∈ [1/5, 2]`, on one tail. This
is the collar step of LFR49 (A:29154–29170) on the finite carrier.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric
open scoped Manifold ContDiff Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Geometry.Operator

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]
  {X : ℕ → Type*} [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace E (X i)]
  [∀ i, IsManifold 𝓘(ℝ, E) ∞ (X i)] [∀ i, T2Space (TangentBundle 𝓘(ℝ, E) (X i))]
  [∀ i, SigmaCompactSpace (X i)] [∀ i, CompleteSpace (X i)]

/-- **LC51′ on LFR14 data via LFR48.** -/
theorem exists_smooth_core_isotopy_of_finite_limit {K : ℕ} (hK : 4 ≤ K)
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E) (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b)) (p : ∀ i, X i)
    {N : Type*} [MetricSpace N] [ProperSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N]
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E) ((K - 1 : ℕ) : ℕ∞ω) E
      (TangentSpace 𝓘(ℝ, E) : N → Type _))
    (hRiem : letI : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E) x) :=
        ⟨G.toRiemannianMetric⟩
      IsRiemannianManifold 𝓘(ℝ, E) N)
    (q : N) (j : ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) N (X i) K)
    (hpt : ∀ i, q ∈ (j i).source ∧ j i q = p i)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hcoef : ∀ (x : N) (L : Set E), IsCompact L → L ⊆ (extChartAt 𝓘(ℝ, E) x).target →
      MapCPConvergenceOn L (K - 1)
        (fun i => pullbackMetricCoefficients (g i)
          ((j i : N → X i) ∘ (extChartAt 𝓘(ℝ, E) x).symm))
        (chartCoeff G x))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (j i x) (j i y) - dist x y| < ε)
    (n : N) {D : Set N} (hDc : IsCompact D) (hin : closedBall n (1 / 2) ⊆ interior D)
    (hout : D ⊆ ball n 2) {O : Set N} (hO : IsOpen O) (hDO : frontier D ⊆ O)
    (V : (x : N) → TangentSpace 𝓘(ℝ, E) x)
    (hV : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, E).tangent ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, E) N)) O)
    (hdef : ∀ x ∈ frontier D, ∃ L : Set N, IsOpen L ∧ x ∈ L ∧ ∃ f : N → ℝ,
      ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f L ∧ D ∩ L = {y | f y ≤ 0} ∩ L ∧
        0 < mvfderiv (I := 𝓘(ℝ, E)) f x (V x))
    (hneg : ∀ x ∈ frontier D, ∀ v ∈ G.finiteMinimizingDirectionsTo {n} x,
      G.inner x (V x) v < 0) :
    ∃ jt : ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) N (X i) ∞,
      (∀ i, q ∈ (jt i).source ∧ jt i q = p i) ∧
      (∀ i, ∀ x ∈ (jt i).source, dist (jt i x) (j i x) < 1 / ((i : ℝ) + 1)) ∧
      ∃ α B : ℝ, 0 < α ∧ 0 < B ∧
      ∀ ε : ℝ≥0, (ε : ℝ) < 1 → (ε : ℝ) * (2 * B) < α →
      ∀ (η : ∀ i, X i → ℝ) (e : ℕ → ℝ),
      (∀ᶠ i in atTop, e i < 1 / 40 ∧ (∀ x, |η i x - dist (jt i n) x| < e i) ∧
        LipschitzWith ε (fun x => η i x - dist (jt i n) x) ∧
        ∃ Wi : Set (X i), IsOpen Wi ∧
          (∀ x, 1 / 10 ≤ dist (jt i n) x → dist (jt i n) x ≤ 10 → x ∈ Wi) ∧
          ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (η i) Wi ∧
          ∀ x, 1 / 10 ≤ dist (jt i n) x → dist (jt i n) x ≤ 10 →
            (1 - (ε : ℝ)) ^ 2 ≤ (g i).inner x (gradientFun (I := 𝓘(ℝ, E)) (g i) (η i) x)
              (gradientFun (I := 𝓘(ℝ, E)) (g i) (η i) x)) →
      ∀ᶠ i in atTop, ∀ ρ ∈ Icc (1 / 5 : ℝ) 2,
        ∃ Hs : ℝ → Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) (X i) (X i) ∞,
          Hs 0 = Diffeomorph.refl 𝓘(ℝ, E) (X i) ∞ ∧
          Hs 1 '' ((jt i : N → X i) '' D) = {x | η i x ≤ ρ} := by
  obtain ⟨jt, hjtpt, -, hclose, hjtexh, hjtcoef, hjtdist, hjtcov⟩ :=
    exists_smooth_comparison_maps_of_finite_limit (by omega) g hmetric p G q j hpt hexh hcoef
      hdist
  refine ⟨jt, hjtpt, hclose, ?_⟩
  obtain ⟨m, rfl⟩ : ∃ m, K = m + 4 := ⟨K - 4, by omega⟩
  let hRB : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E) x) := ⟨G.toRiemannianMetric⟩
  have hRM : IsRiemannianManifold 𝓘(ℝ, E) N := hRiem
  have hGnorm : ∀ (z : N) (u : TangentSpace 𝓘(ℝ, E) z),
      ‖u‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner z u u)) := by
    intro z u
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  have hr : (2 : ℕ∞) ≤ ((m + 2 : ℕ) : ℕ∞) := by exact_mod_cast Nat.le_add_left 2 m
  obtain ⟨α, B, hα, hB, -, -, -, -, -, -, hiso⟩ :=
    exists_finite_collar_constants_core_isotopy (M := X) (r := ((m + 2 : ℕ) : ℕ∞)) hr G hGnorm
      g hmetric q jt hjtexh (fun z L hL hLt => (hjtcoef z L hL hLt).mono_order (by omega))
      hjtdist
      (fun a b ha hab => by
        filter_upwards [hjtcov a b ha hab] with i hi
        rw [(hjtpt i).2]
        exact hi)
      n hDc hin hout hO hDO V hV hdef hneg
  refine ⟨α, B, hα, hB, fun ε hε1 hεB η e hη => ?_⟩
  filter_upwards [hiso ε hε1 hεB η e hη] with i hi ρ hρ
  obtain ⟨Hs, h0, -, -, -, h1⟩ := hi ρ hρ
  exact ⟨Hs, h0, h1⟩

end DifferentialGeometry.Geometry.Collapse
