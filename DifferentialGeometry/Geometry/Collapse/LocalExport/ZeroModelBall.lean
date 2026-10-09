import DifferentialGeometry.Geometry.Collapse.SelectedZeroModelBallsApplications
import DifferentialGeometry.Geometry.Collapse.RankStrata

/-!
# LC87 item 1: the LC80 zero-model balls as data

Blueprint row LC87 (`def:collapse-local-export-certificate`, master207A, A:31053), item 1: "LC80
zero-model balls and cores, with original radial functions"; every item records "the witness
metric and scale, map domain and image buffer, regularity, error tolerance, core/fiber
identification". The fields below are exactly the output clauses of LC80 as proved in
`exists_selected_zero_packets_with_model_balls` (LCP04 with the LC58 model balls).

* `ZeroModelBall I M g N C o δ ε e`: one zero-model ball: center, radius, the model index, an
  actual Kleiner–Lott `δ`-map of `(M, radius⁻¹ d, center)` to the model's cone, the ORIGINAL radial
  function (LC67's choice: all LC30 clauses at the scale `radius`, smooth near the buffered shell
  `{3/40 ≤ d ≤ 11}`, with LC31's cutoff `Φ ∘ radial`), and the core/interior identification: for
  every `ρ' ∈ [1/5, 2]` a diffeomorphism of `B(center, ρ' radius)` onto the model.
* `ZeroModelFamily I M g ρ hρ β N C o δ ε e T V`: the LC80 export at one selection: finitely
  many zero-model balls centred at their indices, radii in `[T ρ, V ρ]`, pairwise disjoint, each
  meeting the zero stratum `scaledSplittingStratum ρ hρ β 0`, the tenth-radius balls covering that
  stratum, and every attached model with at most one end.
* `eventually_nonempty_zeroModelFamily`: the producer, from LC58's sequential hypothesis on a
  sequence of closed connected Riemannian three-manifolds (the metric `inducedMetricSpace (g α)`).

LC80 item 3 (shell splittings and adapted coordinates) is part of the consumer theorem's conclusion
and is not stored here.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Real Filter Metric
open scoped Topology ContDiff Manifold NNReal
open GC.MetricGeometry
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Data

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type) [mM : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- **One LC80 zero-model ball** (LC87 item 1). DATA with proofs of its fields: center, radius,
model index, an actual cone map at the scale `radius`, the original radial function with every
LC30 clause, the buffered smooth window and LC31's cutoff, and the core/interior identification of
`B(center, ρ' radius)`, `ρ' ∈ [1/5, 2]`, with the model. -/
structure ZeroModelBall (g : SmoothRiemannianMetric I M) {ι : Type} (N C : ι → Type)
    [∀ b, MetricSpace (N b)] [∀ b, ChartedSpace H (N b)] [mC : ∀ b, MetricSpace (C b)]
    (o : ∀ b, C b) (δ ε e : ℝ) where
  center : M
  radius : ℝ
  radius_pos : 0 < radius
  /-- The index of the selected nonnegatively curved model. -/
  model : ι
  /-- An actual Kleiner–Lott `δ`-map of `(M, radius⁻¹ d, center)` to the model's cone. -/
  coneMap : @KleinerLottApprox M (C model) (mM.rescale radius⁻¹ (inv_pos.mpr radius_pos))
    (mC model) center (o model) δ
  /-- The original radial function at the scale `radius`. -/
  radial : M → ℝ
  radial_spec :
    letI := mM.rescale radius⁻¹ (inv_pos.mpr radius_pos)
    let gR := scaleMetric (radius⁻¹ ^ 2) (pow_pos (inv_pos.mpr radius_pos) 2) g
    LipschitzWith (Real.toNNReal (1 + ε)) radial ∧
      (∃ O : Set M, IsOpen O ∧ {x : M | 3 / 40 ≤ dist x center ∧ dist x center ≤ 11} ⊆ O ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ radial O) ∧
      (∀ x, |radial x - Metric.infDist x {center}| < e) ∧
      (∀ x, x ∉ {x : M | 1 / 20 < dist x center ∧ dist x center < 20} →
        radial x = Metric.infDist x {center}) ∧
      (∀ x y, |(radial x - Metric.infDist x {center}) -
          (radial y - Metric.infDist y {center})| ≤ ε * dist x y) ∧
      (∀ x, 0 ≤ radial x) ∧ radial center = 0 ∧
      (∀ q ∈ {x : M | 1 / 10 ≤ dist x center ∧ dist x center ≤ 10},
        1 - ε ≤ Real.sqrt (gR.inner q (gradFun gR radial q) (gradFun gR radial q)) ∧
          Real.sqrt (gR.inner q (gradFun gR radial q) (gradFun gR radial q)) ≤ 1 + ε) ∧
      (∀ x, radial x ∈ Icc (1 / 5 : ℝ) 2 →
        1 / 5 - e < dist x center ∧ dist x center < 2 + e) ∧
      radial ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ {x : M | 1 / 10 ≤ dist x center ∧ dist x center ≤ 10} ∧
      (∃ O' : Set M, IsOpen O' ∧ radial ⁻¹' Icc (1 / 5 : ℝ) 2 ⊆ O' ∧
        ContMDiffOn I 𝓘(ℝ, ℝ) ∞ radial O' ∧ ∀ q ∈ O', gradFun gR radial q ≠ 0) ∧
      ∃ L : ℝ, 0 ≤ L ∧ (∀ t, |deriv (annularCutoff cutoffProfile) t| ≤ L) ∧
        ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => annularCutoff cutoffProfile (radial x)) ∧
        (∀ x, annularCutoff cutoffProfile (radial x) ∈ Icc (0 : ℝ) 1) ∧
        (∀ x, radial x ∈ Icc (3 / 10 : ℝ) (4 / 5) →
          annularCutoff cutoffProfile (radial x) = 1) ∧
        tsupport (fun x => annularCutoff cutoffProfile (radial x)) ⊆
          {x : M | 1 / 5 - e < dist x center ∧ dist x center < 9 / 10 + e} ∧
        ∀ q, Real.sqrt (gR.inner q
          (gradFun gR (fun x => annularCutoff cutoffProfile (radial x)) q)
          (gradFun gR (fun x => annularCutoff cutoffProfile (radial x)) q)) ≤ L * (1 + ε)
  /-- The core/interior identification with the model. -/
  modelChart : (ρ' : ℝ) → ρ' ∈ Icc (1 / 5 : ℝ) 2 → PartialDiffeomorph I I M (N model) ∞
  modelChart_source : ∀ ρ' (h : ρ' ∈ Icc (1 / 5 : ℝ) 2),
    (modelChart ρ' h).source = ball center (ρ' * radius)
  modelChart_target : ∀ ρ' (h : ρ' ∈ Icc (1 / 5 : ℝ) 2), (modelChart ρ' h).target = univ

/-- **The LC80 export at one selection** (LC87 item 1 as a family). DATA with proofs of its fields:
finitely many zero-model balls centred at their indices, radii in `[T ρ, V ρ]`, pairwise disjoint,
each meeting the zero stratum, whose tenth-radius balls cover that stratum, and whose models have
at most one end. -/
structure ZeroModelFamily (g : SmoothRiemannianMetric I M) (ρ : M → ℝ) (hρ : ∀ p, 0 < ρ p)
    (β : ℕ → ℝ) {ι : Type} (N C : ι → Type) [∀ b, MetricSpace (N b)] [∀ b, ChartedSpace H (N b)]
    [∀ b, MetricSpace (C b)] (o : ∀ b, C b) (δ ε e T V : ℝ) where
  centres : Set M
  finite_centres : centres.Finite
  zero : (i : M) → i ∈ centres → ZeroModelBall I M g N C o δ ε e
  zero_center : ∀ i (hi : i ∈ centres), (zero i hi).center = i
  radius_mem : ∀ i (hi : i ∈ centres),
    T * ρ i ≤ (zero i hi).radius ∧ (zero i hi).radius ≤ V * ρ i
  disjoint : ∀ i (hi : i ∈ centres) j (hj : j ∈ centres), i ≠ j →
    Disjoint (ball i (zero i hi).radius) (ball j (zero j hj).radius)
  meets_stratum : ∀ i (hi : i ∈ centres),
    (ball i (zero i hi).radius ∩ scaledSplittingStratum.{0, 0} ρ hρ β 0).Nonempty
  covers_stratum : scaledSplittingStratum.{0, 0} ρ hρ β 0 ⊆
    ⋃ i, ⋃ (hi : i ∈ centres), ball i ((zero i hi).radius / 10)
  one_end : ∀ i (hi : i ∈ centres), ∀ K : Set (N (zero i hi).model), IsCompact K →
    ∀ a₁ a₂ : N (zero i hi).model,
      ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a₁) →
      ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a₂) →
      connectedComponentIn Kᶜ a₁ = connectedComponentIn Kᶜ a₂

end Data

section Producer

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **The producer of the LC80 zero-model family.** Under LC58's sequential hypothesis for closed
connected Riemannian three-manifolds `(M^α, g^α)` (as in
`exists_selected_zero_packets_with_model_balls`), there are `ε`, a cone error `δ`, ratios
`0 < T ≤ V` and `α₀` such that for `α > α₀` the manifold `(M^α, g^α)` carries a zero-model
family at the scale `ρ_α`. -/
theorem eventually_nonempty_zeroModelFamily (hE : Module.finrank ℝ E = 3)
    {β : ℕ → ℝ} (hβ : 0 < β 1) (hβone : β 1 < 1) {ζ : ℝ} (hβζ : β 1 < ζ) (hζone : ζ < 1)
    {M : ℕ → Type} [∀ α, TopologicalSpace (M α)] [∀ α, ChartedSpace H (M α)]
    [∀ α, IsManifold I ∞ (M α)] [∀ α, T3Space (M α)] [∀ α, SigmaCompactSpace (M α)]
    [∀ α, ConnectedSpace (M α)] [∀ α, CompactSpace (M α)]
    (g : ∀ α, SmoothRiemannianMetric I (M α))
    (ρ : ∀ α, M α → ℝ) (hρc : ∀ α, Continuous (ρ α)) (hρ : ∀ α x, 0 < ρ α x)
    {ι : Type} {N C : ι → Type} [mN : ∀ b, MetricSpace (N b)] [∀ b, ChartedSpace H (N b)]
    [∀ b, IsManifold I ∞ (N b)] [∀ b, SigmaCompactSpace (N b)] [∀ b, ConnectedSpace (N b)]
    [∀ b, RiemannianBundle (fun x : N b => TangentSpace I x)] [∀ b, IsRiemannianManifold I (N b)]
    [∀ b, CompleteSpace (N b)]
    [∀ b, IsContinuousRiemannianBundle E (fun x : N b => TangentSpace I x)]
    [∀ b, T2Space (TangentBundle I (N b))] [mC : ∀ b, MetricSpace (C b)]
    [∀ b, ProperSpace (C b)]
    (gN : ∀ b, SmoothRiemannianMetric I (N b)) (hgN : ∀ b, IsMetricNorm (I := I) (gN b))
    (hsecN : ∀ b x, SectionalBoundedBelowAt (gN b) x 0)
    (n : ∀ b, N b) (o : ∀ b, C b) (Hc : ∀ b, RadialConeData (o b))
    (hcone : ∀ b : ι, ∀ τ : ℝ, 0 < τ → τ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
      Nonempty (@KleinerLottApprox (N b) (C b) ((mN b).rescale R⁻¹ (inv_pos.mpr hR)) (mC b)
        (n b) (o b) τ))
    (hmodel : ∀ a : ℕ → ℕ, Tendsto a atTop atTop → ∀ z : ∀ j, M (a j),
      ∃ b : ι, ∃ k : ℕ → ℕ, StrictMono k ∧
        @PointedGHConverges (fun j => M (a (k j)))
          (fun j => (inducedMetricSpace (g (a (k j)))).rescale (ρ (a (k j)) (z (k j)))⁻¹
            (inv_pos.mpr (hρ _ _)))
          (N b) (mN b) (fun j => z (k j)) (n b) ∧
        (∃ jm : ∀ j, PartialDiffeomorph I I (N b) (M (a (k j))) ∞, (∀ j, jm j (n b) = z (k j)) ∧
          ∀ r : ℝ, 0 < r → ∃ i₀ : ℕ, ∃ hsub : ∀ l,
            ((⟨Metric.ball (n b) r, Metric.isOpen_ball⟩ : TopologicalSpace.Opens (N b)) :
              Set (N b)) ⊆ (jm (l + i₀)).source,
            ∀ K : Set (⟨Metric.ball (n b) r, Metric.isOpen_ball⟩ : TopologicalSpace.Opens (N b)),
              IsCompact K → MetricCPConvergenceOn K 1
                (fun l => PartialDiffeomorph.pullbackMetricOn (jm (l + i₀)) _ (hsub l)
                  (scaleMetric ((ρ (a (k (l + i₀))) (z (k (l + i₀))))⁻¹ ^ 2)
                    (pow_pos (inv_pos.mpr (hρ _ _)) 2) (g (a (k (l + i₀))))))
                ((gN b).restrictOpen _) ((gN b).restrictOpen _)) ∧
        ∃ Hb : ℕ → ℝ, Tendsto Hb atTop atTop ∧ ∀ j,
          ∀ y ∈ @Metric.ball (M (a (k j)))
            ((inducedMetricSpace (g (a (k j)))).rescale (ρ (a (k j)) (z (k j)))⁻¹
              (inv_pos.mpr (hρ _ _))).toPseudoMetricSpace (z (k j)) (Hb j),
            SectionalBoundedBelowAt (scaleMetric ((ρ (a (k j)) (z (k j)))⁻¹ ^ 2)
              (pow_pos (inv_pos.mpr (hρ _ _)) 2) (g (a (k j)))) y (-((Hb j)⁻¹ ^ 2)))
    {e : ℝ} (he : 0 < e) (he1 : e < 1 / 40) :
    ∃ ε δ T V : ℝ, 0 < ε ∧ ε < 1 / 4 ∧ 0 < δ ∧ 0 < T ∧ T ≤ V ∧ ∃ α₀ : ℕ, ∀ α : ℕ, α₀ < α →
      letI := inducedMetricSpace (g α)
      Nonempty (ZeroModelFamily I (M α) (g α) (ρ α) (hρ α) β N C o δ ε e T V) := by
  obtain ⟨ε, δ, Λ', T, V, hε, hεq, hδ, -, hT, -, hTV, α₀, h⟩ :=
    exists_selected_zero_packets_with_model_balls hE hβ hβone hβζ hζone g ρ hρc hρ gN hgN hsecN n
      o Hc hcone hmodel he he1
  refine ⟨ε, δ, T, V, hε, hεq, hδ, hT, hTV, α₀, fun α hα => ?_⟩
  obtain ⟨r, hr, b, η, hrange, J, hfin, hdisj, hmeet, -, -, hcover, -, -, hend, hitem⟩ := h α hα
  let _ : MetricSpace (M α) := inducedMetricSpace (g α)
  exact ⟨{ centres := J
           finite_centres := hfin
           zero := fun i hi =>
             { center := i
               radius := r i
               radius_pos := hr i
               model := b i
               coneMap := (hitem i hi).1.some
               radial := η i
               radial_spec := (hitem i hi).2.1
               modelChart := fun ρ' h => ((hitem i hi).2.2 ρ' h).choose
               modelChart_source := fun ρ' h => ((hitem i hi).2.2 ρ' h).choose_spec.1
               modelChart_target := fun ρ' h => ((hitem i hi).2.2 ρ' h).choose_spec.2 }
           zero_center := fun _ _ => rfl
           radius_mem := fun i _ => hrange i
           disjoint := fun _ hi _ hj hij => hdisj hi hj hij
           meets_stratum := fun i hi => hmeet i hi
           covers_stratum := fun _ hq => hcover hq
           one_end := fun i hi => hend i hi }⟩

end Producer

end DifferentialGeometry.Geometry.Collapse
