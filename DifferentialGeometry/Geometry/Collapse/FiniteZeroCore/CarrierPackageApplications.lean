import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.CarrierPackage
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.IsometryTransport

/-!
# Consumers of the carrier package (lane LFR49-FIN, group G1)

* `lfr49A_carrier_package_pointedGHConverges`: if the comparison maps `jN` of the finite model
  `N` realize the pointed convergence `(X i, jN i q) → (N, q)`, the SMOOTH comparison maps `jt` of
  the carrier package realize `(X i, jt i (κ⁻¹ q)) → (N', κ⁻¹ q)` (the base points are the same,
  `jt i (κ⁻¹ q) = jN i q`, and the limit moves along the isometry `κ`).
* The frozen form of `lfr49A_carrier_package` (LFR49-A's `Targets.lean`, `6 ≤ r`, with the unused
  `hcover`, `[CompactSpace B]`, `[IsContMDiffRiemannianBundle …]`) is the `example` below.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Topology (TransportedCarrier)
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.MetricSmoothing
open GC.MetricGeometry

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))

section Package

variable {X : ℕ → Type} [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace E3 (X i)]
  [∀ i, IsManifold I3 ∞ (X i)] [∀ i, SigmaCompactSpace (X i)] [∀ i, CompleteSpace (X i)]

/-- **Consumer: pointed convergence of the carrier comparison maps.** -/
theorem lfr49A_carrier_package_pointedGHConverges
    {N : Type} [MetricSpace N] [ProperSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
    [RiemannianBundle (fun x : N => TangentSpace I3 x)] [IsRiemannianManifold I3 N]
    {r : ℕ∞} (hr : 6 ≤ r)
    (G : ContMDiffRiemannianMetric I3 ((r : ℕ∞ω) + 1) E3 (TangentSpace I3 : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace I3 x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (g : ∀ i, SmoothRiemannianMetric I3 (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (q : N) (jN : ∀ i, PartialDiffeomorph I3 I3 N (X i) ∞)
    (hexh : ∀ K : Set N, IsCompact K → ∀ᶠ i in atTop, K ⊆ (jN i).source)
    (hconv : ∀ (x : N) (L : Set E3), IsCompact L → L ⊆ (extChartAt I3 x).target →
      MapCPConvergenceOn L 1
        (fun i => pullbackMetricCoefficients (g i) ((jN i : N → X i) ∘ (extChartAt I3 x).symm))
        (chartCoeff G x))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (jN i x) (jN i y) - dist x y| < ε)
    {EB F : Type} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
    {B : Type} [TopologicalSpace B] [ChartedSpace EB B] [IsManifold 𝓘(ℝ, EB) ∞ B]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {V : B → Type} [TopologicalSpace (TotalSpace F V)] [∀ s, NormedAddCommGroup (V s)]
    [∀ s, InnerProductSpace ℝ (V s)] [FiberBundle F V] [VectorBundle ℝ F V]
    [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, EB)]
    (hdimP : Module.finrank ℝ EB + Module.finrank ℝ F = 3)
    (e : TotalSpace F V ≃ₘ^((r - 2 : ℕ∞) : ℕ∞ω)⟮𝓘(ℝ, EB).prod 𝓘(ℝ, F), I3⟯ N)
    (W : (y : TransportedCarrier e.toHomeomorph) → TangentSpace (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) y)
    (hW : ContMDiff (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (𝓘(ℝ, EB).prod 𝓘(ℝ, F)).tangent ∞
      (fun y => (⟨y, W y⟩ :
        TangentBundle (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (TransportedCarrier e.toHomeomorph))))
    {ℓ : ℝ}
    (hdu : ∀ y, ℓ < ‖((TransportedCarrier.diffeomorph (IX := 𝓘(ℝ, EB).prod 𝓘(ℝ, F))
        e.toHomeomorph).symm y).2‖ →
      mvfderiv (I := 𝓘(ℝ, EB).prod 𝓘(ℝ, F))
        (fun y' => ‖((TransportedCarrier.diffeomorph (IX := 𝓘(ℝ, EB).prod 𝓘(ℝ, F))
          e.toHomeomorph).symm y').2‖) y (W y) = 1)
    (hGH : PointedGHConverges (fun i => jN i q) q) :
    ∃ (N' : Type) (mN' : MetricSpace N') (cN' : ChartedSpace E3 N'),
      letI := mN'
      letI := cN'
      ∃ (_ : IsManifold I3 ∞ N') (κ : N' ≃ᵢ N) (jt : ∀ i, PartialDiffeomorph I3 I3 N' (X i) ∞),
        (∀ i, κ.symm q ∈ (jt i).source ∧ jt i (κ.symm q) = jN i q) ∧
        PointedGHConverges (fun i => jt i (κ.symm q)) (κ.symm q) := by
  obtain ⟨N', mN', cN', hMN', -, -, -, -, -, κ, -, -, jt, -, -, -, -, -, -, -, -, hjtpt, -, -, -,
      -⟩ := lfr49A_carrier_package hr G hGnorm g hmetric q jN hexh hconv hdist hdimP e W hW hdu
  refine ⟨N', mN', cN', hMN', κ, jt, hjtpt, ?_⟩
  have hfun : (fun i => jt i (κ.symm q)) = fun i => jN i q := funext fun i => (hjtpt i).2
  rw [hfun]
  exact pointedGHConverges_of_isometryEquiv κ hGH

-- The frozen form (LFR49-A's `Targets.lean`, `6 ≤ r`) follows from the stripped theorem.
example
    {N : Type} [MetricSpace N] [ProperSpace N] [ChartedSpace E3 N] [IsManifold I3 ∞ N]
    [RiemannianBundle (fun x : N => TangentSpace I3 x)] [IsRiemannianManifold I3 N]
    {r : ℕ∞} (hr : 6 ≤ r)
    (G : ContMDiffRiemannianMetric I3 ((r : ℕ∞ω) + 1) E3 (TangentSpace I3 : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace I3 x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (g : ∀ i, SmoothRiemannianMetric I3 (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (q : N) (jN : ∀ i, PartialDiffeomorph I3 I3 N (X i) ∞)
    (hexh : ∀ K : Set N, IsCompact K → ∀ᶠ i in atTop, K ⊆ (jN i).source)
    (hconv : ∀ (x : N) (L : Set E3), IsCompact L → L ⊆ (extChartAt I3 x).target →
      MapCPConvergenceOn L 1
        (fun i => pullbackMetricCoefficients (g i) ((jN i : N → X i) ∘ (extChartAt I3 x).symm))
        (chartCoeff G x))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (jN i x) (jN i y) - dist x y| < ε)
    (_hcover : ∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
      ball (jN i q) a ⊆ (jN i : N → X i) '' ball q b)
    {EB F : Type} [NormedAddCommGroup EB] [NormedSpace ℝ EB] [FiniteDimensional ℝ EB]
    {B : Type} [TopologicalSpace B] [ChartedSpace EB B] [IsManifold 𝓘(ℝ, EB) ∞ B] [CompactSpace B]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {V : B → Type} [TopologicalSpace (TotalSpace F V)] [∀ s, NormedAddCommGroup (V s)]
    [∀ s, InnerProductSpace ℝ (V s)] [FiberBundle F V] [VectorBundle ℝ F V]
    [ContMDiffVectorBundle ∞ F V 𝓘(ℝ, EB)] [IsContMDiffRiemannianBundle 𝓘(ℝ, EB) ∞ F V]
    (hdimP : Module.finrank ℝ EB + Module.finrank ℝ F = 3)
    (e : TotalSpace F V ≃ₘ^((r - 2 : ℕ∞) : ℕ∞ω)⟮𝓘(ℝ, EB).prod 𝓘(ℝ, F), I3⟯ N)
    (W : (y : TransportedCarrier e.toHomeomorph) → TangentSpace (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) y)
    (hW : ContMDiff (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (𝓘(ℝ, EB).prod 𝓘(ℝ, F)).tangent ∞
      (fun y => (⟨y, W y⟩ :
        TangentBundle (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) (TransportedCarrier e.toHomeomorph))))
    {ℓ : ℝ}
    (hdu : ∀ y, ℓ < ‖((TransportedCarrier.diffeomorph (IX := 𝓘(ℝ, EB).prod 𝓘(ℝ, F))
        e.toHomeomorph).symm y).2‖ →
      mvfderiv (I := 𝓘(ℝ, EB).prod 𝓘(ℝ, F))
        (fun y' => ‖((TransportedCarrier.diffeomorph (IX := 𝓘(ℝ, EB).prod 𝓘(ℝ, F))
          e.toHomeomorph).symm y').2‖) y (W y) = 1) :
    ∃ (N' : Type) (mN' : MetricSpace N') (cN' : ChartedSpace E3 N'),
      letI := mN'
      letI := cN'
      ∃ (_ : IsManifold I3 ∞ N') (_ : RiemannianBundle (fun y : N' => TangentSpace I3 y))
        (_ : IsRiemannianManifold I3 N') (r' : ℕ∞) (_ : 2 ≤ r')
        (G' : ContMDiffRiemannianMetric I3 ((r' : ℕ∞ω) + 1) E3 (TangentSpace I3 : N' → Type _))
        (κ : N' ≃ᵢ N) (D' : Diffeomorph (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) I3 (TotalSpace F V) N' ∞)
        (W' : (y : N') → TangentSpace I3 y) (jt : ∀ i, PartialDiffeomorph I3 I3 N' (X i) ∞),
        ProperSpace N' ∧
        (∀ (y : N') (w : TangentSpace I3 y),
          ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G'.inner y w w))) ∧
        ContMDiff I3 I3 1 (κ : N' → N) ∧
        (∀ (y : N') (v w : TangentSpace I3 y), G'.inner y v w =
          G.inner (κ y) (mfderiv I3 I3 (κ : N' → N) y v) (mfderiv I3 I3 (κ : N' → N) y w)) ∧
        (∀ z, κ (D' z) = e z) ∧
        ContMDiff I3 (ModelWithCorners.tangent I3) ∞ (fun y => (⟨y, W' y⟩ : TangentBundle I3 N')) ∧
        (∀ y : N', mfderiv I3 I3 (κ : N' → N) y (W' y) =
          mfderiv (𝓘(ℝ, EB).prod 𝓘(ℝ, F)) I3 (TransportedCarrier.identity e) ⟨κ y⟩
            (W ⟨κ y⟩)) ∧
        (∀ y : N', ℓ < ‖(D'.symm y).2‖ →
          mvfderiv (I := I3) (fun y' => ‖(D'.symm y').2‖) y (W' y) = 1) ∧
        (∀ i, κ.symm q ∈ (jt i).source ∧ jt i (κ.symm q) = jN i q) ∧
        (∀ K : Set N', IsCompact K → ∀ᶠ i in atTop, K ⊆ (jt i).source) ∧
        (∀ (x : N') (L : Set E3), IsCompact L → L ⊆ (extChartAt I3 x).target →
          MapCPConvergenceOn L 1
            (fun i => pullbackMetricCoefficients (g i) ((jt i : N' → X i) ∘ (extChartAt I3 x).symm))
            (chartCoeff G' x)) ∧
        (∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball (κ.symm q) R, ∀ y ∈ ball (κ.symm q) R,
          |dist (jt i x) (jt i y) - dist x y| < ε) ∧
        (∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
          ball (jt i (κ.symm q)) a ⊆ (jt i : N' → X i) '' ball (κ.symm q) b) :=
  lfr49A_carrier_package hr G hGnorm g hmetric q jN hexh hconv hdist hdimP e W hW hdu

end Package

end DifferentialGeometry.Geometry.Collapse
