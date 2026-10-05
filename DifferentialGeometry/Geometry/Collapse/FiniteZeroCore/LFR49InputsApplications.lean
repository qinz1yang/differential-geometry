import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.FiniteConePackage
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.FiniteCompactModelType
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.BundleDiscCore
import DifferentialGeometry.Geometry.Collapse.FiniteZeroCore.FiniteOpenBallModelType
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.SmoothComparisonMaps
import DifferentialGeometry.Topology.Manifold.TransportedCarrier

/-!
# Consumers of the LFR49 inputs (lane LFR49, group G2)

* `exists_finite_cone_package_of_limit` (T1 on LFR14's output): the `C^{K-1}` limit metric of LFR14
  with `sec ≥ 0` has its LC21 cone package.
* `exists_scale_eventually_compact_model_type_of_finite_limit` (LFR48 + T2): LFR14-shaped `C^K`
  maps from a COMPACT limit are replaced by LFR48's smooth maps, and every open ball
  `B(p_i, ρ R)` is eventually the whole source, diffeomorphic to the model.
* `transportedCarrier_disc_core_data` (T5 on LFR47's carrier): the fibre radius of the carrier
  map `TransportedCarrier.diffeomorph` is a core coordinate with open cores equal to the carrier.
* `exists_scale_eventually_open_ball_bundle_type_finite` (T4 + T5): for a finite model whose smooth
  structure carries a smooth bundle diffeomorphism `D : TotalSpace F V ≃ N` (LFR47's carrier) and a
  smooth field `W` with `|W| ≤ 2`, the finite point margin beyond `A₂` and `du(W) = 1` beyond `ℓ`
  (`exists_smooth_carrierFlow`), every open ball `B(p_i, ρ R)` is eventually diffeomorphic to the
  TOTAL SPACE of the bundle. This is the noncompact branch of LFR49 for a model presented in
  carrier coordinates.
* Verbatim frozen forms (G1) of T2 and T5 as `example`s.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle Metric
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Manifold
open GC.MetricGeometry
open DifferentialGeometry.Geometry.Comparison.Toponogov

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u

section LimitConsumers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NeZero (Module.finrank ℝ E)]

/-- **T1 on LFR14's output.** The `C^{K-1}` limit metric (`3 ≤ K`) of a proper limit, whose
distance is the Riemannian distance of `G`, with `sec_G ≥ 0`, has an LC21 cone package at `q`. -/
theorem exists_finite_cone_package_of_limit {K : ℕ} (hK : 3 ≤ K)
    {N : Type u} [MetricSpace N] [ProperSpace N] [ChartedSpace E N] [IsManifold 𝓘(ℝ, E) ∞ N]
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E) ((K - 1 : ℕ) : ℕ∞ω) E
      (TangentSpace 𝓘(ℝ, E) : N → Type _))
    (hRiem : letI : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E) x) :=
        ⟨G.toRiemannianMetric⟩
      IsRiemannianManifold 𝓘(ℝ, E) N)
    (hsec : ∀ (x : N) (v w : TangentSpace 𝓘(ℝ, E) x), 0 ≤ G.sectionalCurvature x v w) (q : N) :
    ∃ (C : Type u) (mC : MetricSpace C) (o : C), Nonempty (RadialConeData o) ∧
      ProperSpace C ∧ CompleteSpace C ∧ fourPointComparison 0 (univ : Set C) ∧
      ∀ τ : ℝ, 0 < τ → τ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
        Nonempty (@KleinerLottApprox N C ((inferInstance : MetricSpace N).rescale R⁻¹
          (inv_pos.mpr hR)) mC q o τ) := by
  let hRB : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E) x) := ⟨G.toRiemannianMetric⟩
  have hRM : IsRiemannianManifold 𝓘(ℝ, E) N := hRiem
  have hGnorm : ∀ (z : N) (u : TangentSpace 𝓘(ℝ, E) z),
      ‖u‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner z u u)) := by
    intro z u
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    rfl
  have hn : (2 : ℕ∞ω) ≤ ((K - 1 : ℕ) : ℕ∞ω) := by exact_mod_cast (show 2 ≤ K - 1 by omega)
  exact exists_finite_cone_package G hn hGnorm hsec q

variable {X : ℕ → Type*} [∀ i, MetricSpace (X i)] [∀ i, ChartedSpace E (X i)]
  [∀ i, IsManifold 𝓘(ℝ, E) ∞ (X i)] [∀ i, T2Space (TangentBundle 𝓘(ℝ, E) (X i))]
  [∀ i, SigmaCompactSpace (X i)] [∀ i, CompleteSpace (X i)]

/-- **Compact branch on LFR14's data (LFR48 + T2).** For LFR14-shaped data (`1 ≤ K`) with a
COMPACT limit and connected sources: there is `R₀ > 0` such that for every `R ≥ R₀` one tail has
every open ball `B(p_i, ρ R)`, `ρ ∈ [1/5, 2]`, diffeomorphic to the model. -/
theorem exists_scale_eventually_compact_model_type_of_finite_limit {K : ℕ} (hK : 1 ≤ K)
    [∀ i, ConnectedSpace (X i)]
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, E) (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b)) (p : ∀ i, X i)
    {N : Type*} [MetricSpace N] [ProperSpace N] [CompactSpace N] [ChartedSpace E N]
    [IsManifold 𝓘(ℝ, E) ∞ N]
    (G : ContMDiffRiemannianMetric 𝓘(ℝ, E) ((K - 1 : ℕ) : ℕ∞ω) E
      (TangentSpace 𝓘(ℝ, E) : N → Type _))
    (q : N) (j : ∀ i, PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) N (X i) K)
    (hpt : ∀ i, q ∈ (j i).source ∧ j i q = p i)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hcoef : ∀ (x : N) (L : Set E), IsCompact L → L ⊆ (extChartAt 𝓘(ℝ, E) x).target →
      MapCPConvergenceOn L (K - 1)
        (fun i => pullbackMetricCoefficients (g i)
          ((j i : N → X i) ∘ (extChartAt 𝓘(ℝ, E) x).symm))
        (chartCoeff G x))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
      |dist (j i x) (j i y) - dist x y| < ε) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ᶠ i in atTop, ∀ ρ ∈ Icc (1 / 5 : ℝ) 2,
      ∃ Ψ : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) (X i) N ∞,
        Ψ.source = Metric.ball (p i) (ρ * R) ∧ Ψ.target = univ := by
  obtain ⟨jt, hjtpt, -, -, hjtexh, -, hjtdist, -⟩ :=
    exists_smooth_comparison_maps_of_finite_limit hK g hmetric p G q j hpt hexh hcoef hdist
  obtain ⟨R₀, hR₀, h⟩ := exists_scale_eventually_compact_model_type_finite q jt hjtexh hjtdist
  refine ⟨R₀, hR₀, fun R hR => ?_⟩
  filter_upwards [h R hR] with i hi ρ hρ
  rw [← (hjtpt i).2]
  exact hi ρ hρ

end LimitConsumers

section Carrier

open DifferentialGeometry.Topology DifferentialGeometry.Topology.VectorBundle

variable {EB F : Type*} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {HB : Type*} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
  {B : Type*} [TopologicalSpace B] [ChartedSpace HB B] [CompactSpace B]
  {V : B → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ b, NormedAddCommGroup (V b)] [∀ b, InnerProductSpace ℝ (V b)]
  [FiberBundle F V] [VectorBundle ℝ F V] [IsContMDiffRiemannianBundle IB ∞ F V]

/-- **T5 on LFR47's carrier.** For any homeomorphism `e` from the total space of a smooth
Riemannian bundle over a compact base onto `N`, the fibre radius of the carrier map
`TransportedCarrier.diffeomorph e` is a core coordinate whose open cores are the whole carrier. -/
theorem transportedCarrier_disc_core_data [IsManifold (IB.prod 𝓘(ℝ, F)) ∞ (TotalSpace F V)]
    {N : Type*} [TopologicalSpace N] (e : TotalSpace F V ≃ₜ N) :
    let D := TransportedCarrier.diffeomorph (IX := IB.prod 𝓘(ℝ, F)) e
    Continuous (fun y => ‖(D.symm y).2‖) ∧ (∀ T, IsCompact {y | ‖(D.symm y).2‖ ≤ T}) ∧
      ContMDiffOn (IB.prod 𝓘(ℝ, F)) 𝓘(ℝ, ℝ) ∞ (fun y => ‖(D.symm y).2‖)
        {y | 0 < ‖(D.symm y).2‖} ∧
      ∀ T : ℝ, 0 < T → ∃ Ψ : PartialDiffeomorph (IB.prod 𝓘(ℝ, F)) (IB.prod 𝓘(ℝ, F))
          (TransportedCarrier e) (TransportedCarrier e) ∞,
        Ψ.source = interior {y | ‖(D.symm y).2‖ ≤ T} ∧ Ψ.target = univ := by
  intro D
  obtain ⟨h1, h2, -, h4, h5⟩ := bundle_disc_core_data D
  exact ⟨h1, h2, h4, h5⟩

/-- The frozen (G1) statement of T5. -/
example {EN : Type*} [NormedAddCommGroup EN]
    [NormedSpace ℝ EN] {HN : Type*} [TopologicalSpace HN] {IN : ModelWithCorners ℝ EN HN}
    {N : Type*} [TopologicalSpace N] [ChartedSpace HN N]
    (D : Diffeomorph (IB.prod 𝓘(ℝ, F)) IN (TotalSpace F V) N ∞) :
    Continuous (fun y => ‖(D.symm y).2‖) ∧ (∀ T, IsCompact {y | ‖(D.symm y).2‖ ≤ T}) ∧
      (∀ y, 0 ≤ ‖(D.symm y).2‖) ∧
      ContMDiffOn IN 𝓘(ℝ, ℝ) ∞ (fun y => ‖(D.symm y).2‖) {y | 0 < ‖(D.symm y).2‖} ∧
      ∀ T : ℝ, 0 < T → ∃ Ψ : PartialDiffeomorph IN IN N N ∞,
        Ψ.source = interior {y | ‖(D.symm y).2‖ ≤ T} ∧ Ψ.target = univ :=
  bundle_disc_core_data D

end Carrier

section Kernels

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : ℕ → Type} [mM : ∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)] [∀ i, SigmaCompactSpace (M i)]

/-- The frozen (G1) statement of T2 (with the unused instances of the scratch file). -/
example {N : Type} [MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [CompactSpace N]
    [∀ i, ConnectedSpace (M i)] (n : N) (j : ∀ i, PartialDiffeomorph I I N (M i) ∞)
    (hexh : ∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source)
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball n R, ∀ y ∈ ball n R,
      |dist (j i x) (j i y) - dist x y| < ε) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ᶠ i in atTop, ∀ ρ ∈ Icc (1 / 5 : ℝ) 2,
      ∃ Ψ : PartialDiffeomorph I I (M i) N ∞,
        Ψ.source = Metric.ball (j i n) (ρ * R) ∧ Ψ.target = univ :=
  exists_scale_eventually_compact_model_type_finite n j hexh hdist

variable [rbM : ∀ i, RiemannianBundle (fun x : M i => TangentSpace I x)]
  [rmM : ∀ i, IsRiemannianManifold I (M i)] [hMc : ∀ i, CompleteSpace (M i)]
  [crM : ∀ i, IsContinuousRiemannianBundle E (fun x : M i => TangentSpace I x)]

open DifferentialGeometry.Topology.VectorBundle in
/-- **LFR49 noncompact branch in carrier coordinates (T4 + T5).** A finite-order complete model
whose smooth structure carries a smooth diffeomorphism `D` from the total space of a smooth
Riemannian bundle over a compact base (LFR47's carrier), smooth comparison maps in LFR48's shape,
a supplied cone, the source curvature bounds, and a smooth field `W` with `|W| ≤ 2`, the finite
point margin `-1/4` beyond `A₂` and `du(W) = 1` beyond `ℓ` for `u = ‖(D⁻¹ ·).2‖`: there is `R₀ > 0`
such that for every `R ≥ R₀` one tail has every open ball `B(j_i n, ρ R)`, `ρ ∈ [1/5, 2]`,
diffeomorphic to the TOTAL SPACE of the bundle. -/
theorem exists_scale_eventually_open_ball_bundle_type_finite {mdim : ℕ}
    (hdim : Module.finrank ℝ E = mdim + 1)
    {N : Type} [mN : MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [pN : ProperSpace N]
    [RiemannianBundle (fun x : N => TangentSpace I x)] [IsRiemannianManifold I N]
    {r : ℕ∞} (hr : 1 ≤ r)
    (G : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : N → Type _))
    (hGnorm : ∀ (x : N) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (G.inner x w w)))
    (n : N) {C : Type} [MetricSpace C] {o : C} (Hc : RadialConeData o)
    (hcone : ∀ τ : ℝ, 0 < τ → τ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
      Nonempty (@KleinerLottApprox N C (mN.rescale R⁻¹ (inv_pos.mpr hR)) _ n o τ))
    (gSeq : ∀ i, SmoothRiemannianMetric I (M i)) (hSeqNorm : ∀ i, IsMetricNorm (gSeq i))
    (j : ∀ i, PartialDiffeomorph I I N (M i) ∞)
    (hexh : ∀ K : Set N, IsCompact K → ∀ᶠ i in atTop, K ⊆ (j i).source)
    (hconv : ∀ (x : N) (L : Set E), IsCompact L → L ⊆ (extChartAt I x).target →
      MapCPConvergenceOn L 1
        (fun i => pullbackMetricCoefficients (gSeq i) ((j i : N → M i) ∘ (extChartAt I x).symm))
        (chartCoeff G x))
    (hdist : ∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball n R, ∀ y ∈ ball n R,
      |dist (j i x) (j i y) - dist x y| < ε)
    (hcover : ∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
      ball (j i n) a ⊆ (j i : N → M i) '' ball n b)
    (hGH : PointedGHConverges (fun i => j i n) n)
    (Hb : ℕ → ℝ) (hHb : Tendsto Hb atTop atTop)
    (hsecM : ∀ i, ∀ y ∈ Metric.ball (j i n) (Hb i),
      SectionalBoundedBelowAt (gSeq i) y (-((Hb i)⁻¹ ^ 2)))
    {EB F : Type} [NormedAddCommGroup EB] [NormedSpace ℝ EB]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {HB : Type} [TopologicalSpace HB] {IB : ModelWithCorners ℝ EB HB}
    {B : Type} [TopologicalSpace B] [ChartedSpace HB B] [CompactSpace B]
    {Vb : B → Type} [TopologicalSpace (TotalSpace F Vb)]
    [∀ b, NormedAddCommGroup (Vb b)] [∀ b, InnerProductSpace ℝ (Vb b)]
    [FiberBundle F Vb] [VectorBundle ℝ F Vb] [IsContMDiffRiemannianBundle IB ∞ F Vb]
    (D : Diffeomorph (IB.prod 𝓘(ℝ, F)) I (TotalSpace F Vb) N ∞)
    (W : (x : N) → TangentSpace I x)
    (hW : ContMDiff I I.tangent ∞ (fun x => (⟨x, W x⟩ : TangentBundle I N)))
    {A₂ ℓ : ℝ} (hℓ : 0 ≤ ℓ)
    (hWB : ∀ x, G.inner x (W x) (W x) ≤ 4)
    (hWdir : ∀ x, A₂ ≤ dist n x → ∀ v ∈ G.finiteMinimizingDirectionsTo {n} x,
      G.inner x (W x) v ≤ -(1 / 4))
    (hdu : ∀ y, ℓ < ‖(D.symm y).2‖ →
      mvfderiv (I := I) (fun y' => ‖(D.symm y').2‖) y (W y) = 1) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ᶠ i in atTop, ∀ ρ ∈ Icc (1 / 5 : ℝ) 2,
      ∃ Ψ : PartialDiffeomorph I (IB.prod 𝓘(ℝ, F)) (M i) (TotalSpace F Vb) ∞,
        Ψ.source = Metric.ball (j i n) (ρ * R) ∧ Ψ.target = univ := by
  obtain ⟨hu, hucpt, -, huW, hcore⟩ := bundle_disc_core_data D
  set u : N → ℝ := fun y => ‖(D.symm y).2‖ with hudef
  have hWu : IsOpen {y : N | 0 < u y} := isOpen_lt continuous_const hu
  obtain ⟨R₀, hR₀, h⟩ := exists_scale_eventually_open_ball_model_type_finite hdim hr G hGnorm n
    Hc hcone gSeq hSeqNorm j hexh hconv hdist hcover hGH Hb hHb hsecM W hWB hWdir hu hucpt
    (T₀ := ℓ + 1) hWu (fun y hy => by
      have hy' : ℓ + 1 ≤ u y := hy
      change 0 < u y
      linarith) huW hW.contMDiffOn
    (fun y hy => by
      have hy' : ℓ + 1 ≤ u y := hy
      rw [hdu y (by linarith)]
      exact one_pos)
    (fun T hT => hcore T (by linarith))
  refine ⟨R₀, hR₀, fun R hR => ?_⟩
  filter_upwards [h R hR] with i hi ρ hρ
  obtain ⟨Ψ, hΨs, hΨt⟩ := hi ρ hρ
  refine ⟨Ψ.trans D.symm.toPartialDiffeomorph, ?_, ?_⟩
  · rw [PartialDiffeomorph.trans_source, hΨs]
    exact inter_eq_left.mpr fun x _ => mem_univ _
  · apply eq_univ_of_forall
    intro z
    refine ⟨mem_univ z, ?_⟩
    change D z ∈ Ψ.target
    rw [hΨt]
    exact mem_univ _

end Kernels

end DifferentialGeometry.Geometry.Collapse
