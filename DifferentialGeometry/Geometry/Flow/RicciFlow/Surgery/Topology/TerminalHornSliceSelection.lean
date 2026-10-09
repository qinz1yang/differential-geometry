import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HornPointSliceGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HornTerminalScalarBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalHornCanonicalNeckUniform
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.FineCutNeckSupplyTolerances
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalFineNeckOfSpatialNecks
import DifferentialGeometry.Topology.Sequences.DiagonalChoice

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
  (SpatialCanonicalWitness SpatialCanonicalAlternative SpatialNeck SpatialLocalNeck)
open scoped Manifold ContDiff Topology NNReal ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

universe u

theorem exists_slices_of_deep_horn_presentation_sequence :
    ∃ eta etaC : ℝ, 0 < eta ∧ 0 < etaC ∧
    ∀ {κ ε ε₁ C1 C2 qcan εc a : ℝ} {Ctime Cgrad : ℝ≥0}
      {phi : ℝ → ℝ}, 0 < κ → 0 < qcan → 0 < ε → ε ≤ etaC → 0 < εc → εc < 1 / 2 → 0 < a →
      Perelman.AdmissiblePinchingFunction phi →
    ∀ (H : ℕ → RetainedCoreHistory.{u})
      (hend : ∀ n, (H n).time (Fin.last (H n).eventCount) = (H n).horizon),
      (∀ n, (H n).EventSlabsDerivative Ctime qcan (Fin.last (H n).eventCount)) →
      (∀ n, (H n).EventSlabsPinched phi) →
    ∀ {s : ℕ → ℝ} (G : ∀ n, ((H n).stage (Fin.last (H n).eventCount)).IncomingSlab
        ((H n).time (Fin.last (H n).eventCount)) (s n))
      (L : ∀ n, (G n).TerminalLimitMetric) (hsing : ∀ n, (G n).SingularEndpoint)
      (parameters : ℕ → CutoffParameters)
      (hG : ∀ n, (G n).flow.base.metric ((H n).time (Fin.last (H n).eventCount)) =
        (H n).initialMetric (Fin.last (H n).eventCount)),
      (∀ n, a ≤ s n) →
      (∀ n, (G n).DerivativeBoundBefore Ctime qcan (s n)) →
      (∀ n, (G n).GradientBoundBefore Cgrad qcan (s n)) →
      (∀ n, (H n).StronglyCanonicalBefore (Fin.last (H n).eventCount) (G n) ε ε₁ C1 C2 qcan
        (s n)) →
      (∀ n, Perelman.PhiAlmostNonnegative (G n).flow
        (Ico ((H n).time (Fin.last (H n).eventCount)) (s n)) phi) →
      (∀ n, ∀ t₀ ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (s n),
        (H n).TerminalNoncollapsedBefore (hend n) (G n) (hG n) κ ε t₀) →
    ∀ {εP Λ : ℕ → ℝ} (P : ∀ n, TerminalCorePresentation
        { stage := (H n).stage (Fin.last (H n).eventCount)
          startTime := (H n).time (Fin.last (H n).eventCount)
          endTime := s n
          startTime_nonneg := (H n).toHistory.time_nonneg (Fin.last (H n).eventCount)
          startTime_lt_endTime := (G n).lt
          slab := G n
          terminal := L n
          singular := hsing n
          parameters := parameters n } (εP n) (Λ n)), (∀ n, εP n ≤ eta) →
    ∀ (c : ∀ n, ConnectedComponents (G n).terminalRegularOpen) (e : ∀ n, (P n).hornIndex (c n))
      (x : ∀ n, (G n).terminalRegularOpen),
      (∀ n, x n ∈ interior (range fun p : HalfNeckCylinder => (P n).horn (c n) (e n) p.1)) →
      (∀ n : ℕ, ((n : ℝ) + 1) * max (Λ n * ((P n).coreRadius ^ 2)⁻¹) (max qcan 1) ≤
        metricScalarAt (L n).metric (x n)) →
      (∀ n, ¬ ∃ N : NormalizedNeck (L n).metric εc (⌊εc⁻¹⌋₊ + 1), N.center = x n) →
    ∃ (τ : ℕ → ℝ) (Q : ℕ → ℝ)
      (S V W : ∀ n, Set ((H n).stage (Fin.last (H n).eventCount)).Carrier),
      (∀ n, τ n ∈ Ioo ((H n).time (Fin.last (H n).eventCount)) (s n)) ∧
      (∀ m, 1 ≤ Q m) ∧
      (∀ n, ¬ Nonempty (SpatialNeck ((G n).flow.base.metric (τ n)) (min (εc / (1 + εc)) (1 / 12))
        (x n).val)) ∧
      (∀ n, |(G n).flow.scalar (τ n) (x n).val - metricScalarAt (L n).metric (x n)| ≤
        metricScalarAt (L n).metric (x n) / 2) ∧
      (∀ n, (s n - τ n) * metricScalarAt (L n).metric (x n) ≤ 1 / ((n : ℝ) + 1)) ∧
      (∀ n, IsOpen (V n)) ∧ (∀ n, IsOpen (W n)) ∧ (∀ n, Disjoint (V n) (W n)) ∧
      (∀ n, ∀ z ∈ S n, riemannianEDistOf ((G n).flow.base.metric (τ n)) (x n).val z ≤
        ENNReal.ofReal (7 / Real.sqrt ((G n).flow.scalar (τ n) (x n).val))) ∧
      (∀ m : ℕ, ∀ᶠ n in atTop,
        riemannianClosedBallOf ((G n).flow.base.metric (τ n)) (x n).val
            (3 * ((m : ℝ) + 1) / Real.sqrt ((G n).flow.scalar (τ n) (x n).val)) \ S n ⊆
          V n ∪ W n ∧
        ∃ p ∈ V n, ∃ q ∈ W n,
          ENNReal.ofReal (((m : ℝ) + 1) / Real.sqrt ((G n).flow.scalar (τ n) (x n).val)) ≤
            riemannianEDistOf ((G n).flow.base.metric (τ n)) (x n).val p ∧
          riemannianEDistOf ((G n).flow.base.metric (τ n)) (x n).val p <
            ENNReal.ofReal (3 * ((m : ℝ) + 1) / Real.sqrt ((G n).flow.scalar (τ n) (x n).val)) ∧
          ENNReal.ofReal (((m : ℝ) + 1) / Real.sqrt ((G n).flow.scalar (τ n) (x n).val)) ≤
            riemannianEDistOf ((G n).flow.base.metric (τ n)) (x n).val q ∧
          riemannianEDistOf ((G n).flow.base.metric (τ n)) (x n).val q <
            ENNReal.ofReal (3 * ((m : ℝ) + 1) /
              Real.sqrt ((G n).flow.scalar (τ n) (x n).val))) ∧
      (∀ m : ℕ, ∀ᶠ n in atTop,
        (∀ w : (G n).terminalRegularOpen, riemannianEDistOf (L n).metric (x n) w <
          ENNReal.ofReal (8 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n))) →
          metricScalarAt (L n).metric w ≤ Q m * metricScalarAt (L n).metric (x n)) ∧
        riemannianBallOf ((G n).flow.base.metric (τ n)) (x n).val
            (16 * (3 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n))) / 17) ⊆
          Subtype.val '' riemannianClosedBallOf (L n).metric (x n)
            (3 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n))) ∧
        ∀ w ∈ riemannianClosedBallOf (L n).metric (x n)
            (3 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n))),
          |metricScalarAt ((G n).flow.base.metric (τ n)) w.val - metricScalarAt (L n).metric w| <
            metricScalarAt (L n).metric (x n)) ∧
      (∀ m : ℕ, ∀ᶠ n in atTop, ∀ w ∈ riemannianClosedBallOf (L n).metric (x n)
          (3 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n))),
        ∀ W : SpatialCanonicalWitness ((G n).flow.base.metric (τ n)) ε C1 C2 w.val,
          W.capTubeHasNeckChart ε →
            ∃ neck : SpatialLocalNeck ((G n).flow.base.metric (τ n)) ε w.val W.domain.carrier,
              W.alternative = SpatialCanonicalAlternative.neck neck) := by
  obtain ⟨eta₀, -, heta₀, -, -, -, -, -, hSC4c⟩ := exists_fineCutNeckSupplyStrong_tolerances.{u}
  obtain ⟨eta₇, heta₇, hSC7⟩ :=
    exists_eventually_terminal_scalar_bound_at_distance_of_mem_hornHalfRange.{u}
  obtain ⟨eta₂, heta₂, hSC2b⟩ :=
    TerminalCorePresentation.eventually_forall_neck_alternative_of_subset_hornHalfRange.{u}
  refine ⟨min eta₀ (min eta₇ eta₂), min eta₂ eta₇, lt_min heta₀ (lt_min heta₇ heta₂),
    lt_min heta₂ heta₇, ?_⟩
  intro κ ε ε₁ C1 C2 qcan εc a Ctime Cgrad phi hκ hq hε hεC hεc hεc12 ha hphi H hend hderiv
    hpinch s G L hsing parameters hG hs hderG hgradG hcanG hpinchG hncG εP Λ P hεP c e x hxint hRl
    hnoN
  have hεη₂ : ε ≤ eta₂ := hεC.trans (min_le_left _ _)
  have hεη₇ : ε ≤ eta₇ := hεC.trans (min_le_right _ _)
  have hεPη₀ : ∀ n, εP n ≤ eta₀ := fun n => (hεP n).trans (min_le_left _ _)
  have hεPη₇ : ∀ n, εP n ≤ eta₇ := fun n =>
    (hεP n).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hεPη₂ : ∀ n, εP n ≤ eta₂ := fun n =>
    (hεP n).trans ((min_le_right _ _).trans (min_le_right _ _))
  have heps : 0 < min (εc / (1 + εc)) (1 / 12) := lt_min (div_pos hεc (by linarith)) (by norm_num)
  have hfit : εc⁻¹ + 1 ≤ (min (εc / (1 + εc)) (1 / 12))⁻¹ :=
    inv_add_one_le_inv_of_le_div_one_add hεc heps (min_le_left _ _)
  have hhorn : ∀ n, x n ∈ (P n).hornHalfRange (c n) (e n) := fun n => interior_subset (hxint n)
  have hcomp : ∀ n, c n ∈ (P n).component := fun n => by
    by_contra hnot
    exact ((P n).hornIndex_empty (c n) hnot).elim (e n)
  have hμpos : ∀ n, 0 < max (Λ n * ((P n).coreRadius ^ 2)⁻¹) qcan := fun n =>
    hq.trans_le (le_max_right _ _)
  have hμle : ∀ n, max (Λ n * ((P n).coreRadius ^ 2)⁻¹) qcan ≤
      max (Λ n * ((P n).coreRadius ^ 2)⁻¹) (max qcan 1) := fun n =>
    max_le_max_left _ (le_max_left _ _)
  have hone : ∀ n, 1 ≤ max (Λ n * ((P n).coreRadius ^ 2)⁻¹) (max qcan 1) := fun n =>
    (le_max_right _ _).trans (le_max_right _ _)
  have hRl1 : ∀ n : ℕ, (n : ℝ) + 1 ≤ metricScalarAt (L n).metric (x n) := fun n =>
    (le_mul_of_one_le_right (by positivity) (hone n)).trans (hRl n)
  have hRlpos : ∀ n, 0 < metricScalarAt (L n).metric (x n) := fun n =>
    (by positivity : (0 : ℝ) < n + 1).trans_le (hRl1 n)
  have hnat : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun n => by linarith) tendsto_natCast_atTop_atTop
  have hgrow : Tendsto (fun n => metricScalarAt (L n).metric (x n) /
      max (Λ n * ((P n).coreRadius ^ 2)⁻¹) qcan) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) hnat
    rw [le_div_iff₀ (hμpos n)]
    exact (mul_le_mul_of_nonneg_left (hμle n) (by positivity)).trans (hRl n)
  have hmu : ∀ K : ℝ, ∀ᶠ n in atTop,
      K * max (Λ n * ((P n).coreRadius ^ 2)⁻¹) qcan < metricScalarAt (L n).metric (x n) :=
    fun K => (hgrow.eventually_gt_atTop K).mono fun n hn => by
      rwa [lt_div_iff₀ (hμpos n)] at hn
  have hRs : Tendsto (fun n => metricScalarAt (L n).metric (x n) * s n) atTop atTop := by
    refine tendsto_atTop_mono (fun n => ?_) (hnat.atTop_mul_const ha)
    exact mul_le_mul (hRl1 n) (hs n) ha.le (hRlpos n).le
  have hno : ∀ n, ∀ᶠ τ in 𝓝[<] s n,
      ¬ Nonempty (SpatialNeck ((G n).flow.base.metric τ) (min (εc / (1 + εc)) (1 / 12))
        (x n).val) := by
    intro n
    rw [← Filter.not_frequently]
    intro hfreq
    exact hnoN n ((L n).exists_normalizedNeck_of_frequently_spatialNeck (x n) (hRlpos n) hεc
      (by linarith) hfit hfreq)
  have hSC7' := hSC7 hε hεη₇ hκ hq hε hphi H hend s G hG L hsing parameters εP Λ P
    hεPη₇ c hcomp e x hhorn hcanG hderiv hderG hgradG hpinch hpinchG hncG hgrow hRs
  choose Q hQ1 hQev using fun m : ℕ => hSC7' (8 * ((m : ℝ) + 1)) (by positivity)
  have hfar : ∀ m : ℕ, ∀ᶠ n in atTop, ∀ w ∈ frontier ((P n).core (c n)),
      ENNReal.ofReal (2 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n))) <
        riemannianEDistOf (L n).metric (x n) w := by
    intro m
    filter_upwards [hmu (2 * (1 + Cgrad * (2 * ((m : ℝ) + 1))) ^ 2)] with n hn
    refine (P n).ofReal_lt_riemannianEDistOf_frontier_of_gradientBoundBefore (c n) (hcomp n)
      (hgradG n) hq (by positivity) (x n) ?_
    calc 2 * max (Λ n * ((P n).coreRadius ^ 2)⁻¹) qcan * (1 + Cgrad * (2 * ((m : ℝ) + 1))) ^ 2
        = 2 * (1 + Cgrad * (2 * ((m : ℝ) + 1))) ^ 2 *
          max (Λ n * ((P n).coreRadius ^ 2)⁻¹) qcan := by ring
      _ < metricScalarAt (L n).metric (x n) := hn
  have hlowL : ∀ m : ℕ, ∀ᶠ n in atTop, ∀ w : (G n).terminalRegularOpen,
      riemannianEDistOf (L n).metric (x n) w <
        ENNReal.ofReal (4 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n))) →
      max (4 * C2) 1 * max (Λ n * ((P n).coreRadius ^ 2)⁻¹) qcan <
        metricScalarAt (L n).metric w := by
    intro m
    filter_upwards [hmu (4 * (1 + Cgrad * (4 * ((m : ℝ) + 1))) ^ 2 * max (4 * C2) 1)] with n hn
    have hκ2 : 0 < 4 * (1 + Cgrad * (4 * ((m : ℝ) + 1))) ^ 2 := by positivity
    have hbig : max (4 * C2) 1 * max (Λ n * ((P n).coreRadius ^ 2)⁻¹) qcan <
        metricScalarAt (L n).metric (x n) / (4 * (1 + Cgrad * (4 * ((m : ℝ) + 1))) ^ 2) := by
      rw [lt_div_iff₀ hκ2]
      calc max (4 * C2) 1 * max (Λ n * ((P n).coreRadius ^ 2)⁻¹) qcan *
            (4 * (1 + Cgrad * (4 * ((m : ℝ) + 1))) ^ 2)
          = 4 * (1 + Cgrad * (4 * ((m : ℝ) + 1))) ^ 2 * max (4 * C2) 1 *
            max (Λ n * ((P n).coreRadius ^ 2)⁻¹) qcan := by ring
        _ < metricScalarAt (L n).metric (x n) := hn
    have hq' : qcan < metricScalarAt (L n).metric (x n) /
        (4 * (1 + Cgrad * (4 * ((m : ℝ) + 1))) ^ 2) :=
      ((le_max_right _ _).trans (le_mul_of_one_le_left (hμpos n).le (le_max_right _ _))).trans_lt
        hbig
    intro w hw
    exact hbig.trans_le ((L n).quarter_scalar_le_on_ball_of_gradientBoundBefore (hgradG n) hq
      (by positivity) (x n) hq' w hw)
  have hΛnn : ∀ n, 0 ≤ Λ n * ((P n).coreRadius ^ 2)⁻¹ := fun n =>
    mul_nonneg (zero_le_one.trans (P n).Lambda_ge_one) (by positivity)
  have hhorn4 : ∀ m : ℕ, ∀ᶠ n in atTop, riemannianBallOf (L n).metric (x n)
      (4 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n))) ⊆
        (P n).hornHalfRange (c n) (e n) := by
    intro m
    filter_upwards [hlowL m] with n hn
    refine (P n).riemannianBallOf_subset_hornHalfRange (hcomp n) (hhorn n)
      (div_pos (by positivity) (Real.sqrt_pos.mpr (hRlpos n))) fun w hw => ?_
    calc Λ n * ((P n).coreRadius ^ 2)⁻¹ ≤ max (Λ n * ((P n).coreRadius ^ 2)⁻¹) qcan :=
          le_max_left _ _
      _ ≤ max (4 * C2) 1 * max (Λ n * ((P n).coreRadius ^ 2)⁻¹) qcan :=
          le_mul_of_one_le_left (hμpos n).le (le_max_right _ _)
      _ < metricScalarAt (L n).metric w := hn w hw
  choose δN kN N hNc hNδ hNk using fun n => (P n).horn_spatial_neck (c n) (e n) (x n) (hxint n)
  have hLfix : ∀ᶠ n in atTop, ∀ w ∈ frontier ((P n).core (c n)),
      2 * metricScalarAt (L n).metric w < (N n).scale := by
    filter_upwards [hmu 2] with n hn w hw
    rw [(N n).scale_scalar, hNc n]
    have hfr : metricScalarAt (L n).metric w ≤ Λ n * ((P n).coreRadius ^ 2)⁻¹ :=
      (P n).frontier_scalar_le (c n) (hcomp n) hw
    calc 2 * metricScalarAt (L n).metric w ≤ 2 * max (Λ n * ((P n).coreRadius ^ 2)⁻¹) qcan := by
          linarith [le_max_left (Λ n * ((P n).coreRadius ^ 2)⁻¹) qcan]
      _ < metricScalarAt (L n).metric (x n) := hn
  have hsepC : ∀ n, ∃ S V W : Set ((H n).stage (Fin.last (H n).eventCount)).Carrier,
      IsOpen V ∧ IsOpen W ∧ Disjoint V W ∧
      (∀ᶠ τ in 𝓝[<] s n, ∀ z ∈ S,
        riemannianEDistOf ((G n).flow.base.metric τ) (x n).val z ≤
          ENNReal.ofReal (7 / Real.sqrt ((G n).flow.scalar τ (x n).val))) ∧
      ((∀ w ∈ frontier ((P n).core (c n)), 2 * metricScalarAt (L n).metric w < (N n).scale) →
        ∀ A : ℝ, 0 < A →
          IsCompact (riemannianClosedBallOf (L n).metric (x n)
            (4 * A / Real.sqrt (metricScalarAt (L n).metric (x n)))) →
          (∀ w ∈ frontier ((P n).core (c n)),
            ENNReal.ofReal (2 * A / Real.sqrt (metricScalarAt (L n).metric (x n))) <
              riemannianEDistOf (L n).metric (x n) w) →
          ∀ᶠ τ in 𝓝[<] s n,
            riemannianClosedBallOf ((G n).flow.base.metric τ) (x n).val
                (3 * A / Real.sqrt ((G n).flow.scalar τ (x n).val)) \ S ⊆ V ∪ W ∧
            ∃ p ∈ V, ∃ q ∈ W,
              ENNReal.ofReal (A / Real.sqrt ((G n).flow.scalar τ (x n).val)) ≤
                riemannianEDistOf ((G n).flow.base.metric τ) (x n).val p ∧
              riemannianEDistOf ((G n).flow.base.metric τ) (x n).val p <
                ENNReal.ofReal (3 * A / Real.sqrt ((G n).flow.scalar τ (x n).val)) ∧
              ENNReal.ofReal (A / Real.sqrt ((G n).flow.scalar τ (x n).val)) ≤
                riemannianEDistOf ((G n).flow.base.metric τ) (x n).val q ∧
              riemannianEDistOf ((G n).flow.base.metric τ) (x n).val q <
                ENNReal.ofReal (3 * A / Real.sqrt ((G n).flow.scalar τ (x n).val))) := by
    intro n
    by_cases hL : ∀ w ∈ frontier ((P n).core (c n)),
      2 * metricScalarAt (L n).metric w < (N n).scale
    · obtain ⟨S, V, W, hV, hW, hVW, hSb, hcl⟩ := hSC4c (P n) (hεPη₀ n) (c n) (hcomp n) (e n)
        (N n) (hNδ n) (hNk n) (by rw [hNc n]; exact hhorn n) hL
      rw [hNc n] at hSb hcl
      exact ⟨S, V, W, hV, hW, hVW, hSb, fun _ A hA hc hf => hcl hA hc hf⟩
    · exact ⟨∅, ∅, ∅, isOpen_empty, isOpen_empty, disjoint_empty _,
        Eventually.of_forall fun τ z hz => absurd hz (Set.notMem_empty z), fun h => absurd h hL⟩
  choose S V W hV hW hVW hsep using hsepC
  have hdiag : ∀ n (m : ℕ), ∀ᶠ τ in 𝓝[<] s n,
      (¬ Nonempty (SpatialNeck ((G n).flow.base.metric τ) (min (εc / (1 + εc)) (1 / 12))
        (x n).val)) ∧
      |(G n).flow.scalar τ (x n).val - metricScalarAt (L n).metric (x n)| ≤
        metricScalarAt (L n).metric (x n) / 2 ∧
      (s n - τ) * metricScalarAt (L n).metric (x n) ≤ 1 / ((n : ℝ) + 1) ∧
      (∀ z ∈ S n, riemannianEDistOf ((G n).flow.base.metric τ) (x n).val z ≤
        ENNReal.ofReal (7 / Real.sqrt ((G n).flow.scalar τ (x n).val))) ∧
      ((∀ w ∈ frontier ((P n).core (c n)), 2 * metricScalarAt (L n).metric w < (N n).scale) →
        IsCompact (riemannianClosedBallOf (L n).metric (x n)
          (4 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n)))) →
        (∀ w ∈ frontier ((P n).core (c n)),
          ENNReal.ofReal (2 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n))) <
            riemannianEDistOf (L n).metric (x n) w) →
        riemannianClosedBallOf ((G n).flow.base.metric τ) (x n).val
            (3 * ((m : ℝ) + 1) / Real.sqrt ((G n).flow.scalar τ (x n).val)) \ S n ⊆ V n ∪ W n ∧
        ∃ p ∈ V n, ∃ q ∈ W n,
          ENNReal.ofReal (((m : ℝ) + 1) / Real.sqrt ((G n).flow.scalar τ (x n).val)) ≤
            riemannianEDistOf ((G n).flow.base.metric τ) (x n).val p ∧
          riemannianEDistOf ((G n).flow.base.metric τ) (x n).val p <
            ENNReal.ofReal (3 * ((m : ℝ) + 1) / Real.sqrt ((G n).flow.scalar τ (x n).val)) ∧
          ENNReal.ofReal (((m : ℝ) + 1) / Real.sqrt ((G n).flow.scalar τ (x n).val)) ≤
            riemannianEDistOf ((G n).flow.base.metric τ) (x n).val q ∧
          riemannianEDistOf ((G n).flow.base.metric τ) (x n).val q <
            ENNReal.ofReal (3 * ((m : ℝ) + 1) / Real.sqrt ((G n).flow.scalar τ (x n).val))) ∧
      (IsCompact (riemannianClosedBallOf (L n).metric (x n)
          (3 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n)))) →
        riemannianBallOf ((G n).flow.base.metric τ) (x n).val
            (16 * (3 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n))) / 17) ⊆
          Subtype.val '' riemannianClosedBallOf (L n).metric (x n)
            (3 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n))) ∧
        ∀ w ∈ riemannianClosedBallOf (L n).metric (x n)
            (3 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n))),
          |metricScalarAt ((G n).flow.base.metric τ) w.val - metricScalarAt (L n).metric w| <
            metricScalarAt (L n).metric (x n)) ∧
      (IsCompact (riemannianClosedBallOf (L n).metric (x n)
          (3 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n)))) →
        riemannianClosedBallOf (L n).metric (x n)
            (3 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n))) ⊆
          (P n).hornHalfRange (c n) (e n) →
        (∀ w ∈ riemannianClosedBallOf (L n).metric (x n)
            (3 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n))),
          4 * C2 * (Λ n * ((P n).coreRadius ^ 2)⁻¹) < metricScalarAt (L n).metric w) →
        ∀ w ∈ riemannianClosedBallOf (L n).metric (x n)
            (3 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n))),
          ∀ W : SpatialCanonicalWitness ((G n).flow.base.metric τ) ε C1 C2 w.val,
            W.capTubeHasNeckChart ε →
              ∃ neck : SpatialLocalNeck ((G n).flow.base.metric τ) ε w.val W.domain.carrier,
                W.alternative = SpatialCanonicalAlternative.neck neck) := by
    intro n m
    have h2 : ∀ᶠ τ in 𝓝[<] s n,
        |(G n).flow.scalar τ (x n).val - metricScalarAt (L n).metric (x n)| ≤
          metricScalarAt (L n).metric (x n) / 2 := by
      filter_upwards [((L n).tendsto_metricScalarAt (x n)).eventually
        (Metric.ball_mem_nhds _ (half_pos (hRlpos n)))] with τ hτ
      rw [Real.dist_eq] at hτ
      exact hτ.le
    have h3 : ∀ᶠ τ in 𝓝[<] s n,
        (s n - τ) * metricScalarAt (L n).metric (x n) ≤ 1 / ((n : ℝ) + 1) := by
      have hpos : 0 < ((n : ℝ) + 1) * metricScalarAt (L n).metric (x n) :=
        mul_pos (by positivity) (hRlpos n)
      filter_upwards [Ioo_mem_nhdsLT
        (show s n - 1 / (((n : ℝ) + 1) * metricScalarAt (L n).metric (x n)) < s n by
          linarith [one_div_pos.mpr hpos])] with τ hτ
      have h' : s n - τ < 1 / (((n : ℝ) + 1) * metricScalarAt (L n).metric (x n)) := by
        linarith [hτ.1]
      calc (s n - τ) * metricScalarAt (L n).metric (x n)
          ≤ 1 / (((n : ℝ) + 1) * metricScalarAt (L n).metric (x n)) *
            metricScalarAt (L n).metric (x n) :=
            mul_le_mul_of_nonneg_right h'.le (hRlpos n).le
        _ = 1 / ((n : ℝ) + 1) := by
            rw [one_div, one_div, mul_inv, mul_assoc, inv_mul_cancel₀ (hRlpos n).ne', mul_one]
    have h5 : ∀ᶠ τ in 𝓝[<] s n,
        (∀ w ∈ frontier ((P n).core (c n)), 2 * metricScalarAt (L n).metric w < (N n).scale) →
        IsCompact (riemannianClosedBallOf (L n).metric (x n)
          (4 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n)))) →
        (∀ w ∈ frontier ((P n).core (c n)),
          ENNReal.ofReal (2 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n))) <
            riemannianEDistOf (L n).metric (x n) w) →
        riemannianClosedBallOf ((G n).flow.base.metric τ) (x n).val
            (3 * ((m : ℝ) + 1) / Real.sqrt ((G n).flow.scalar τ (x n).val)) \ S n ⊆ V n ∪ W n ∧
        ∃ p ∈ V n, ∃ q ∈ W n,
          ENNReal.ofReal (((m : ℝ) + 1) / Real.sqrt ((G n).flow.scalar τ (x n).val)) ≤
            riemannianEDistOf ((G n).flow.base.metric τ) (x n).val p ∧
          riemannianEDistOf ((G n).flow.base.metric τ) (x n).val p <
            ENNReal.ofReal (3 * ((m : ℝ) + 1) / Real.sqrt ((G n).flow.scalar τ (x n).val)) ∧
          ENNReal.ofReal (((m : ℝ) + 1) / Real.sqrt ((G n).flow.scalar τ (x n).val)) ≤
            riemannianEDistOf ((G n).flow.base.metric τ) (x n).val q ∧
          riemannianEDistOf ((G n).flow.base.metric τ) (x n).val q <
            ENNReal.ofReal (3 * ((m : ℝ) + 1) / Real.sqrt ((G n).flow.scalar τ (x n).val)) :=
      eventually_imp_distrib_left.mpr fun hL => eventually_imp_distrib_left.mpr fun hc =>
        eventually_imp_distrib_left.mpr fun hf => (hsep n).2 hL _ (by positivity) hc hf
    have h6 : ∀ᶠ τ in 𝓝[<] s n,
        IsCompact (riemannianClosedBallOf (L n).metric (x n)
          (3 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n)))) →
        riemannianBallOf ((G n).flow.base.metric τ) (x n).val
            (16 * (3 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n))) / 17) ⊆
          Subtype.val '' riemannianClosedBallOf (L n).metric (x n)
            (3 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n))) ∧
        ∀ w ∈ riemannianClosedBallOf (L n).metric (x n)
            (3 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n))),
          |metricScalarAt ((G n).flow.base.metric τ) w.val - metricScalarAt (L n).metric w| <
            metricScalarAt (L n).metric (x n) :=
      eventually_imp_distrib_left.mpr fun hc =>
        ((L n).eventually_riemannianBallOf_subset_image_closedBall (x n)
          (div_pos (by positivity) (Real.sqrt_pos.mpr (hRlpos n))) hc).and
          ((L n).eventually_scalar_close_on_compact hc (hRlpos n))
    have h7 : ∀ᶠ τ in 𝓝[<] s n,
        IsCompact (riemannianClosedBallOf (L n).metric (x n)
          (3 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n)))) →
        riemannianClosedBallOf (L n).metric (x n)
            (3 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n))) ⊆
          (P n).hornHalfRange (c n) (e n) →
        (∀ w ∈ riemannianClosedBallOf (L n).metric (x n)
            (3 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n))),
          4 * C2 * (Λ n * ((P n).coreRadius ^ 2)⁻¹) < metricScalarAt (L n).metric w) →
        ∀ w ∈ riemannianClosedBallOf (L n).metric (x n)
            (3 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n))),
          ∀ W : SpatialCanonicalWitness ((G n).flow.base.metric τ) ε C1 C2 w.val,
            W.capTubeHasNeckChart ε →
              ∃ neck : SpatialLocalNeck ((G n).flow.base.metric τ) ε w.val W.domain.carrier,
                W.alternative = SpatialCanonicalAlternative.neck neck :=
      eventually_imp_distrib_left.mpr fun hc => eventually_imp_distrib_left.mpr fun hsub =>
        eventually_imp_distrib_left.mpr fun hsc =>
          hSC2b (P n) (hεPη₂ n) (c n) (e n) hc hsub (epsCan := ε) (C1 := C1) (C2 := C2) hε hεη₂
            hsc
    exact (hno n).and (h2.and (h3.and ((hsep n).1.and (h5.and (h6.and h7)))))
  obtain ⟨τ, hτmem, hτp⟩ := Filter.exists_seq_mem_Ioo_forall_of_eventually_nhdsLT
    (b := fun n => (H n).time (Fin.last (H n).eventCount)) (fun n => (G n).lt)
    (ι := fun n => Fin (n + 1)) (fun n i => hdiag n i)
  have hc3of : ∀ (m : ℕ) (n : ℕ), IsCompact (riemannianClosedBallOf (L n).metric (x n)
      (8 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n)))) →
      IsCompact (riemannianClosedBallOf (L n).metric (x n)
        (3 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n)))) := fun m n h =>
    h.of_isClosed_subset (Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _)
      (riemannianClosedBallOf_mono _ _ (div_le_div_of_nonneg_right (by linarith) (by positivity)))
  refine ⟨τ, Q, S, V, W, hτmem, hQ1, fun n => (hτp n 0).1, fun n => (hτp n 0).2.1,
    fun n => (hτp n 0).2.2.1, hV, hW, hVW, fun n => (hτp n 0).2.2.2.1, ?_, ?_, ?_⟩
  · intro m
    filter_upwards [eventually_ge_atTop m, hLfix, hQev m, hfar m] with n hmn hL hQn hf
    have hc4 : IsCompact (riemannianClosedBallOf (L n).metric (x n)
        (4 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n)))) :=
      hQn.2.of_isClosed_subset (Geometry.Metric.isClosed_riemannianClosedBallOf _ _ _)
        (riemannianClosedBallOf_mono _ _
          (div_le_div_of_nonneg_right (by linarith) (by positivity)))
    exact (hτp n ⟨m, Nat.lt_succ_of_le hmn⟩).2.2.2.2.1 hL hc4 hf
  · intro m
    filter_upwards [eventually_ge_atTop m, hQev m] with n hmn hQn
    exact ⟨hQn.1, (hτp n ⟨m, Nat.lt_succ_of_le hmn⟩).2.2.2.2.2.1 (hc3of m n hQn.2)⟩
  · intro m
    filter_upwards [eventually_ge_atTop m, hQev m, hhorn4 m, hlowL m] with n hmn hQn hhn hln
    have h34 : 3 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n)) <
        4 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n)) :=
      div_lt_div_of_pos_right (by linarith) (Real.sqrt_pos.mpr (hRlpos n))
    have h4pos : 0 < 4 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n)) :=
      div_pos (by positivity) (Real.sqrt_pos.mpr (hRlpos n))
    have hsub3 : riemannianClosedBallOf (L n).metric (x n)
        (3 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n))) ⊆
          (P n).hornHalfRange (c n) (e n) := fun w hw =>
      hhn (lt_of_le_of_lt hw ((ENNReal.ofReal_lt_ofReal_iff h4pos).mpr h34))
    have hsc : ∀ w ∈ riemannianClosedBallOf (L n).metric (x n)
        (3 * ((m : ℝ) + 1) / Real.sqrt (metricScalarAt (L n).metric (x n))),
        4 * C2 * (Λ n * ((P n).coreRadius ^ 2)⁻¹) < metricScalarAt (L n).metric w := by
      intro w hw
      calc 4 * C2 * (Λ n * ((P n).coreRadius ^ 2)⁻¹)
          ≤ max (4 * C2) 1 * max (Λ n * ((P n).coreRadius ^ 2)⁻¹) qcan :=
            mul_le_mul (le_max_left _ _) (le_max_left _ _) (hΛnn n)
              (zero_le_one.trans (le_max_right _ _))
        _ < metricScalarAt (L n).metric w :=
            hln w (lt_of_le_of_lt hw ((ENNReal.ofReal_lt_ofReal_iff h4pos).mpr h34))
    exact (hτp n ⟨m, Nat.lt_succ_of_le hmn⟩).2.2.2.2.2.2 (hc3of m n hQn.2) hsub3 hsc

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.RetainedCoreHistory

end
