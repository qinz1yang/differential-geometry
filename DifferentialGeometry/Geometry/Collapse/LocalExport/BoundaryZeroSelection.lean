import DifferentialGeometry.Geometry.Collapse.ZeroStratumRiemannian
import DifferentialGeometry.Geometry.Collapse.InducedVolumeComparison

/-!
# LC88 / BCP04, packet P3c: the zero selection on a compact candidate envelope (BDRY-3)

Review 45 §3.3 (one shared regionalised kernel): LC64 / LC66 / LC77 without `CompactSpace`. The
closed kernels use compactness only for (a) total boundedness of the candidate centres and the
two-sided bounds of the radii (LC64), (b) completeness and properness of the carrier (segments,
four-point comparison) and (c) finite volume (Hausdorff dimension). Here:
* `exists_finite_maximal_ball_cover_of_envelope_BDRY3`: LC64 with the candidate centres (every `v`
  whose ball meets `Z`) inside a totally bounded envelope `S` and global radius bounds;
* `exists_zero_stratum_small_core_cover_envelope_BDRY3`: LC66 (metric) for any subset `Z` of the
  zero stratum with a totally bounded candidate envelope;
* complete-carrier inputs for `inducedMetricSpace g`: segments, Hausdorff dimension (σ-compact
  carrier) and four-point comparison levels;
* `exists_selected_zero_family_envelope_BDRY3` (consumer): LC66 + LC77 on a complete connected
  Riemannian three-manifold — one selection `J` (finite, disjoint, balls meeting `Z`) such that the
  original buffer, the models and the Kleiner–Lott maps at the selected centres give the tenth-ball
  cover of `Z` and at most one end of every model.
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric MeasureTheory
open scoped Manifold ContDiff ENNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Comparison.Toponogov
open GC.MetricGeometry

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.Geometry.Metric

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u v

/-! ### Metric kernels with a candidate envelope -/

/-- **LC64 on a candidate envelope.** The maximal-candidate selection of
`Metric.exists_finite_maximal_ball_cover_of_bounded_radii` when only the candidate centres (every
`v` whose `r(v)`-ball meets `Z`) lie in a totally bounded set `S`. -/
theorem exists_finite_maximal_ball_cover_of_envelope_BDRY3 {X : Type*} [MetricSpace X]
    {S : Set X} (htot : TotallyBounded S) (Z : Set X) (r : X → ℝ)
    (hS : ∀ v, (ball v (r v) ∩ Z).Nonempty → v ∈ S)
    {rmin R : ℝ} (hmin : 0 < rmin) (hlower : ∀ p, rmin ≤ r p) (hupper : ∀ p, r p ≤ R) :
    ∃ I : Set X, I.Finite ∧
      (∀ i ∈ I, (ball i (r i) ∩ Z).Nonempty ∧
        ∀ q, (ball q (r q) ∩ Z).Nonempty → ball i (r i) ⊆ ball q (r q) → r q ≤ 2 * r i) ∧
      I.PairwiseDisjoint (fun i => ball i (r i)) ∧
      (∀ i ∈ I, ∀ q, dist i q ≤ 10 * r i → r q ≤ 20 * r i) ∧
      Z ⊆ ⋃ i ∈ I, ball i (5 * r i) := by
  let V : Set X := {v | (ball v (r v) ∩ Z).Nonempty ∧
    ∀ q, (ball q (r q) ∩ Z).Nonempty →
      ball v (r v) ⊆ ball q (r q) → r q ≤ 2 * r v}
  have hpos : ∀ p, 0 < r p := fun p => hmin.trans_le (hlower p)
  obtain ⟨I, hIV, hfin, hdisj, hcover⟩ := exists_finite_disjoint_ball_selection
    (htot.subset fun v (hv : v ∈ V) => hS v hv.1) r hmin (fun p _ => hlower p) (fun p _ => hupper p)
  refine ⟨I, hfin, fun i hi => hIV hi, hdisj, ?_, ?_⟩
  · intro i hi q hq
    exact radius_le_of_maximal_doubling_ball r Z (hIV hi).1 (hpos i) (hIV hi).2 hq
  · intro z hz
    obtain ⟨v, hvZ, hzv, hmax⟩ := exists_maximal_doubling_ball r Z hpos hupper
      (show (ball z (r z) ∩ Z).Nonempty from ⟨z, mem_ball_self (hpos z), hz⟩)
    have hzball : z ∈ ball v (r v) := by
      rcases hzv with rfl | ⟨_, hsub⟩
      · exact mem_ball_self (hpos z)
      · exact hsub (mem_ball_self (hpos z))
    obtain ⟨i, hi, _, _, _, hsub⟩ := hcover v ⟨hvZ, hmax⟩
    exact mem_iUnion₂.mpr ⟨i, hi, hsub hzball⟩

/-- **LC66 (metric kernel) on a candidate envelope.** For ANY subset `Z` of the LC16 zero stratum
whose candidate centres lie in a totally bounded set: one LC64 selection `I` (finite, disjoint
balls meeting `Z`, LC62's scale ratio on the ten-radius balls) such that the LC65 data at the
selected centres give the tenth-radius cover of `Z`. -/
theorem exists_zero_stratum_small_core_cover_envelope_BDRY3 {β : ℕ → ℝ} (hβ : 0 < β 1)
    (hβone : β 1 < 1) :
    ∃ δ' Λ' : ℝ, 0 < δ' ∧ 0 < Λ' ∧
      ∀ (X : Type u) [m : MetricSpace X] [CompleteSpace X],
      (∀ x y : X, ∃ f : Icc (0 : ℝ) 1 → X,
        Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
          ∀ s t, dist (f s) (f t) = dist x y * dist s t) →
      dimH (univ : Set X) ≤ 3 →
      ∀ (r ρ : X → ℝ) (hρpos : ∀ p, 0 < ρ p) {T rmin R : ℝ} (hT : 0 < T),
      20 * Λ' ≤ T → ∀ (hlower : ∀ p, T * ρ p ≤ r p), 0 < rmin → (∀ p, rmin ≤ r p) →
      (∀ p, r p ≤ R) →
      ∀ (Z S : Set X), TotallyBounded S →
      Z ⊆ {q | @splittingRank.{u, 0} X (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 = 0} →
      (∀ w, (ball w (r w) ∩ Z).Nonempty → w ∈ S) →
      ∃ I : Set X, I.Finite ∧ (∀ i ∈ I, (ball i (r i) ∩ Z).Nonempty) ∧
        I.PairwiseDisjoint (fun i => ball i (r i)) ∧
        (∀ i ∈ I, ∀ q, dist i q ≤ 10 * r i → T / 20 ≤ r i / ρ q) ∧
        ((∀ i ∈ I, fourPointComparison ((1 / 60) ^ 2 * (r i)⁻¹ ^ 2) (ball i (21 * r i)) ∧
            ∃ (C : Type v) (mC : MetricSpace C) (o : C), Nonempty (RadialConeData o) ∧ ∃ δ : ℝ,
              δ < δ' ∧ Nonempty (@KleinerLottApprox X C
                (m.rescale (r i)⁻¹ (inv_pos.mpr ((mul_pos hT (hρpos i)).trans_le (hlower i))))
                mC i o δ)) →
          Z ⊆ ⋃ i ∈ I, ball i (r i / 10)) := by
  obtain ⟨σ, hσ, hσone, hAC55⟩ :=
    exists_prescribed_splitting_parameter.{u} (n := 3) (by norm_num) hβ hβone
  obtain ⟨θ, δσ, Λσ, -, -, hδσ, hΛσ, hLC65⟩ :=
    exists_annular_exact_scale_strainer.{u, v} hσ hσone
  refine ⟨δσ, max Λσ σ⁻¹, hδσ, lt_max_of_lt_left hΛσ, ?_⟩
  intro X m _ hsegments hdim r ρ hρpos T rmin R hT hTΛ hlower hrmin hrlow hrup Z S hS hZ hSZ
  have hrpos (p : X) : 0 < r p := (mul_pos hT (hρpos p)).trans_le (hlower p)
  obtain ⟨I, hfin, hmax, hdisj, hloc20, hcover⟩ :=
    exists_finite_maximal_ball_cover_of_envelope_BDRY3 hS Z r hSZ hrmin hrlow hrup
  have hlocal : ∀ i ∈ I, ∀ q, dist i q ≤ 10 * r i → T / 20 ≤ r i / ρ q := by
    intro i hi q hq
    refine (le_div_iff₀ (hρpos q)).mpr ?_
    linarith [hlower q, hloc20 i hi q hq]
  refine ⟨I, hfin, fun i hi => (hmax i hi).1, hdisj, hlocal, fun hdata => ?_⟩
  have hcurves := arbitrarily_short_curves_of_metric_segments hsegments
  have hshell : ∀ i ∈ I, ∀ q, r i / 10 ≤ dist i q → dist i q ≤ 10 * r i →
      @HasEuclideanSplitting.{u, 0} X (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q 1 (β 1) := by
    intro i hi q hq1 hq2
    obtain ⟨hcomp1, C, mC, o, ⟨H⟩, δ, hδ, ⟨φ⟩⟩ := hdata i hi
    have hcomp := hcomp1.forall_ge (by positivity)
    have hri := hrpos i
    have hri' : 0 < (r i)⁻¹ := inv_pos.mpr hri
    have hρq := hρpos q
    have hlampos : 0 < r i / ρ q := div_pos hri hρq
    have hlamT : T / 20 ≤ r i / ρ q := hlocal i hi q hq2
    have hlamΛ : max Λσ σ⁻¹ ≤ r i / ρ q := by linarith
    have hlamΛσ : Λσ ≤ r i / ρ q := (le_max_left _ _).trans hlamΛ
    have hlamσ : σ⁻¹ ≤ r i / ρ q := (le_max_right _ _).trans hlamΛ
    have hcomp21 : @fourPointComparison X (m.rescale (r i)⁻¹ hri') ((1 / 60) ^ 2)
        (@ball X (m.rescale (r i)⁻¹ hri').toPseudoMetricSpace i 21) := by
      have hb := MetricSpace.rescale_ball m (r i)⁻¹ hri' i (21 * r i)
      have hc : (r i)⁻¹ * (21 * r i) = 21 := by field_simp
      rw [hc] at hb
      rw [hb, fourPointComparison_rescale_iff (m := m) hri' (by positivity)]
      exact hcomp _ le_rfl
    have hd1 : 1 / 10 ≤ @dist X (m.rescale (r i)⁻¹ hri').toDist i q := by
      rw [MetricSpace.rescale_dist, le_inv_mul_iff₀ hri]
      linarith
    have hd2 : @dist X (m.rescale (r i)⁻¹ hri').toDist i q ≤ 10 := by
      rw [MetricSpace.rescale_dist, inv_mul_le_iff₀ hri]
      linarith
    obtain ⟨a, b, -, -, -, -, hqa, hqb, -, -, hangle⟩ :=
      @hLC65 X C (m.rescale (r i)⁻¹ hri') mC (rescale_segments m hri' hsegments) i o H δ φ hδ
        hcomp21 q hd1 hd2 (r i / ρ q) hlamΛσ
    simp only [MetricSpace.rescale_dist] at hqa hqb hangle
    have hconv (x y : X) : r i / ρ q * ((r i)⁻¹ * dist x y) = (ρ q)⁻¹ * dist x y := by
      field_simp
    rw [hconv, hconv, hconv] at hangle
    have hρq' : 0 < (ρ q)⁻¹ := inv_pos.mpr hρq
    have hσρ : σ⁻¹ / (ρ q)⁻¹ ≤ r i := by
      rw [div_inv_eq_mul]
      have := (le_div_iff₀ hρq).mp hlamσ
      linarith
    have hK : (1 / 60) ^ 2 * (r i)⁻¹ ^ 2 ≤ σ * (ρ q)⁻¹ ^ 2 := by
      have hρr : (ρ q)⁻¹ = r i / ρ q * (r i)⁻¹ := by field_simp
      have h1 : 1 ≤ σ * (r i / ρ q) := by
        have := mul_le_mul_of_nonneg_left hlamσ hσ.le
        rwa [mul_inv_cancel₀ hσ.ne'] at this
      have h2 : 1 ≤ σ * (r i / ρ q) ^ 2 := by nlinarith
      rw [hρr, mul_pow, ← mul_assoc]
      have h3 : 0 ≤ (r i)⁻¹ ^ 2 := by positivity
      nlinarith
    refine hasEuclideanSplitting_one_of_rescaled_strainer hσ hAC55 (by norm_num) hcurves hρq'
      ((dimH_mono (subset_univ _)).trans (by exact_mod_cast hdim)) isOpen_ball
      (fun w hw => ?_) (hcomp _ hK) ?_ ?_ hangle
    · have hw' : dist w q < σ⁻¹ / (ρ q)⁻¹ := hw
      change dist w i < 21 * r i
      have ht := dist_triangle w q i
      rw [dist_comm q i] at ht
      linarith
    · rw [mul_comm, ← div_eq_mul_inv, div_eq_iff hρq.ne']
      have := (eq_div_iff hlampos.ne').mp hqa
      field_simp at this ⊢
      linarith
    · rw [mul_comm, ← div_eq_mul_inv, div_eq_iff hρq.ne']
      have := (eq_div_iff hlampos.ne').mp hqb
      field_simp at this ⊢
      linarith
  have hrank : ∀ i ∈ I, ∀ q, r i / 10 ≤ dist i q → dist i q ≤ 10 * r i →
      @splittingRank.{u, 0} X (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 ≠ 0 := by
    intro i hi q hq1 hq2
    have h := @le_splittingRank.{u, 0} X (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 1
      (by norm_num) (hshell i hi q hq1 hq2)
    omega
  apply subset_small_balls_of_annular_exclusion Z I r hcover
  intro i hi z hz hshellz
  exact hrank i hi z hshellz.1 hshellz.2 (hZ hz)

/-! ### Complete-carrier inputs for `inducedMetricSpace g` -/

section Inputs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T3Space M]
  [SigmaCompactSpace M] [ConnectedSpace M]

/-- Minimizing segments for the distance of a complete metric `g`. -/
theorem inducedMetricSpace_segments_of_complete_BDRY3 {g : SmoothRiemannianMetric I M}
    (hg : RiemannianMetricComplete (I := I) g) :
    letI := inducedMetricSpace g
    ∀ x y : M, ∃ f : Icc (0 : ℝ) 1 → M,
      Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
        ∀ s t, dist (f s) (f t) = dist x y * dist s t := by
  let := inducedMetricSpace g
  have : ProperSpace M := inducedMetricSpace_properSpace_of_riemannianMetricComplete hg
  intro x y
  exact Metric.exists_metric_segment_of_approximate_midpoints
    (Metric.approximate_midpoints_of_arbitrarily_short_curves
      (fun a b η hη => exists_arbitrarily_short_riemannian_curve
        g (inducedMetricSpace_hmetric g) a b hη)) x y

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- A σ-compact connected smooth Riemannian manifold, with the distance of its metric, has
Hausdorff dimension at most the dimension of its model (compact pieces have finite volume). -/
theorem dimH_univ_le_finrank_of_sigmaCompact_BDRY3 (g : SmoothRiemannianMetric I M) :
    letI := inducedMetricSpace g
    dimH (univ : Set M) ≤ Module.finrank ℝ E := by
  let _ := inducedMetricSpace g
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  obtain ⟨hRM, hEnorm, hcont⟩ := inducedMetricSpace_riemannian g
  let _ : MeasurableSpace M := borel M
  have _ : BorelSpace M := ⟨rfl⟩
  have h := normalizedHausdorffMeasure_eq_riemannianVolumeMeasure g hEnorm
  have _ := DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_isFiniteMeasureOnCompacts
    (I := I) g
  have hK : ∀ k, dimH (compactCovering M k) ≤ Module.finrank ℝ E := by
    intro k
    have hne : (normalizedHausdorffMeasure (Module.finrank ℝ E) : Measure M)
        (compactCovering M k) ≠ ⊤ := by
      rw [h]
      exact (isCompact_compactCovering M k).measure_lt_top.ne
    have hμ : μH[(Module.finrank ℝ E : ℝ)] (compactCovering M k) ≠ ⊤ := by
      intro htop
      apply hne
      simp only [normalizedHausdorffMeasure, Measure.smul_apply]
      rw [htop]
      exact ENNReal.mul_top (by exact_mod_cast (euclideanHausdorffFactor_pos _).ne')
    have hd := dimH_le_of_hausdorffMeasure_ne_top (d := (Module.finrank ℝ E : NNReal))
      (s := compactCovering M k) (by simpa only [NNReal.coe_natCast] using hμ)
    simpa only [ENNReal.coe_natCast] using hd
  rw [← iUnion_compactCovering M, dimH_iUnion]
  exact iSup_le hK

omit [SigmaCompactSpace M] in
/-- Four-point comparison at every curvature `-K`, `K ≥ κ`, on the ball of radius `R` of a complete
metric, from `sec ≥ -κ` on the ball of radius `8R`. -/
theorem inducedMetricSpace_fourPointComparison_levels_of_complete_BDRY3
    [SigmaCompactSpace M] {g : SmoothRiemannianMetric I M}
    (hg : RiemannianMetricComplete (I := I) g) (o : M) {κ R : ℝ} (hκ : 0 ≤ κ)
    (hsec : ∀ y ∈ riemannianBallOf g o (8 * R), SectionalBoundedBelowAt g y (-κ)) :
    letI := inducedMetricSpace g
    ∀ K : ℝ, κ ≤ K → fourPointComparison K (ball o R) := by
  let := inducedMetricSpace g
  let : CompleteSpace M := riemannianMetricComplete_iff_inducedMetricSpace.mp hg
  intro K hK
  apply fourPointComparison_of_sectional_lower_bound_on_eight_ball g (inducedMetricSpace_hmetric g)
    o (hκ.trans hK)
  intro y hy
  rw [inducedMetricSpace_ball g o (8 * R)] at hy
  exact (hsec y hy).mono (by linarith)

end Inputs

/-! ### LC66 + LC77 on a complete carrier -/

section Selection

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **The zero selection on a complete carrier (consumer).** On a complete connected Riemannian
three-manifold, for a subset `Z` of the zero stratum with a totally bounded candidate envelope:
one LC64 selection `J` (finite, disjoint balls meeting `Z`) such that the ORIGINAL buffer
`sec_g ≥ -(1/60)² r(i)⁻²` on `B_g(i, 400 r(i))`, the models (four-point comparison `0`, segments,
cone maps from every blow-down) and the actual Kleiner–Lott maps at the selected centres give
LC66's tenth-radius cover of `Z` and LC77's end count of the SAME models. -/
theorem exists_selected_zero_family_envelope_BDRY3 (hE : Module.finrank ℝ E = 3)
    {β : ℕ → ℝ} (hβ : 0 < β 1) (hβone : β 1 < 1) :
    ∃ δ' Λ' : ℝ, 0 < δ' ∧ 0 < Λ' ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T3Space M]
        [SigmaCompactSpace M] [ConnectedSpace M] (g : SmoothRiemannianMetric I M),
      RiemannianMetricComplete (I := I) g →
      letI m := inducedMetricSpace g
      ∀ (N C : M → Type v) [mN : ∀ i, MetricSpace (N i)] [∀ i, ProperSpace (N i)]
        [mC : ∀ i, MetricSpace (C i)] [∀ i, ProperSpace (C i)]
        (n₀ : ∀ i, N i) (o : ∀ i, C i), (∀ i, RadialConeData (o i)) →
      ∀ (δ : M → ℝ) (r ρ : M → ℝ) (hρpos : ∀ p, 0 < ρ p) {T rmin R : ℝ} (hT : 0 < T),
      20 * Λ' ≤ T → ∀ (hlower : ∀ p, T * ρ p ≤ r p), 0 < rmin → (∀ p, rmin ≤ r p) →
      (∀ p, r p ≤ R) →
      ∀ (Z S : Set M), TotallyBounded S →
      Z ⊆ {q | @splittingRank.{u, 0} M (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 = 0} →
      (∀ w, (ball w (r w) ∩ Z).Nonempty → w ∈ S) →
      ∃ J : Set M, J.Finite ∧ J.PairwiseDisjoint (fun i => ball i (r i)) ∧
        (∀ i ∈ J, (ball i (r i) ∩ Z).Nonempty) ∧
        ((∀ i ∈ J,
            (∀ y ∈ riemannianBallOf g i (400 * r i),
              SectionalBoundedBelowAt g y (-((1 / 60) ^ 2 * (r i)⁻¹ ^ 2))) ∧
            fourPointComparison 0 (univ : Set (N i)) ∧
            (∀ x y : N i, ∃ f : Icc (0 : ℝ) 1 → N i,
              Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
              ∀ s t, dist (f s) (f t) = dist x y * dist s t) ∧
            (∀ δ₁ : ℝ, 0 < δ₁ → δ₁ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ,
              R₀ ≤ R → ∀ hR : 0 < R, Nonempty (@KleinerLottApprox (N i) (C i)
                ((mN i).rescale R⁻¹ (inv_pos.mpr hR)) (mC i) (n₀ i) (o i) δ₁)) ∧
            δ i < δ' ∧
            Nonempty (@KleinerLottApprox M (C i)
              (m.rescale (r i)⁻¹ (inv_pos.mpr ((mul_pos hT (hρpos i)).trans_le (hlower i))))
              (mC i) i (o i) (δ i))) →
          Z ⊆ ⋃ i ∈ J, ball i (r i / 10) ∧
          ∀ i ∈ J, ∀ K : Set (N i), IsCompact K → ∀ a b : N i,
            ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a) →
            ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b) →
            connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ b) := by
  obtain ⟨δ₁, Λ₁, hδ₁, hΛ₁, h66⟩ :=
    exists_zero_stratum_small_core_cover_envelope_BDRY3.{u, v} hβ hβone
  obtain ⟨δ₂, Λ₂, hδ₂, hΛ₂, h77⟩ :=
    exists_selected_model_one_end_parameter.{u, v, v} hβ hβone
  refine ⟨min δ₁ δ₂, max Λ₁ Λ₂, lt_min hδ₁ hδ₂, lt_max_of_lt_left hΛ₁, ?_⟩
  intro M _ _ _ _ _ _ g hg
  let m := inducedMetricSpace g
  have hcomplete : CompleteSpace M := riemannianMetricComplete_iff_inducedMetricSpace.mp hg
  intro N C mN _ mC _ n₀ o H δ r ρ hρpos T rmin R hT hTΛ hlower hrmin hrlow hrup Z S hS hZ hSZ
  have hdim : dimH (univ : Set M) ≤ 3 := by
    have h := dimH_univ_le_finrank_of_sigmaCompact_BDRY3 (I := I) g
    rw [hE] at h
    exact_mod_cast h
  have hseg := inducedMetricSpace_segments_of_complete_BDRY3 hg
  have hr : ∀ p, 0 < r p := fun p => (mul_pos hT (hρpos p)).trans_le (hlower p)
  obtain ⟨J, hfin, hmeet, hdisj, hloc, hcond⟩ :=
    h66 M hseg hdim r ρ hρpos hT ((mul_le_mul_of_nonneg_left (le_max_left _ _)
      (by norm_num)).trans hTΛ) hlower hrmin hrlow hrup Z S hS hZ hSZ
  refine ⟨J, hfin, hdisj, hmeet, fun hdata => ?_⟩
  have hscale : ∀ i ∈ J, ∀ q, dist i q ≤ 10 * r i → max Λ₁ Λ₂ ≤ r i / ρ q := fun i hi q hq => by
    have := hloc i hi q hq
    linarith
  have hsec8 : ∀ i ∈ J, ∀ y ∈ riemannianBallOf g i (8 * (21 * r i)),
      SectionalBoundedBelowAt g y (-((1 / 60) ^ 2 * (r i)⁻¹ ^ 2)) := by
    intro i hi y hy
    apply (hdata i hi).1 y
    have hsub : riemannianBallOf g i (8 * (21 * r i)) ⊆ riemannianBallOf g i (400 * r i) := by
      rw [← inducedMetricSpace_ball g, ← inducedMetricSpace_ball g]
      exact ball_subset_ball (by nlinarith [hr i])
    exact hsub hy
  have hcomp : ∀ i ∈ J, fourPointComparison ((1 / 60) ^ 2 * (r i)⁻¹ ^ 2) (ball i (21 * r i)) :=
    fun i hi => inducedMetricSpace_fourPointComparison_levels_of_complete_BDRY3 hg i
      (by positivity) (hsec8 i hi) _ le_rfl
  refine ⟨hcond fun i hi => ⟨hcomp i hi, C i, mC i, o i, ⟨H i⟩, δ i,
    ((hdata i hi).2.2.2.2.1).trans_le (min_le_left _ _), (hdata i hi).2.2.2.2.2⟩, ?_⟩
  intro i hi
  obtain ⟨-, hNcomp, hNseg, hcone, hδ, ⟨F⟩⟩ := hdata i hi
  exact h77 M hseg ρ hρpos i (hr i) ((dimH_mono (subset_univ _)).trans hdim) (hcomp i hi)
    (fun q hq => (le_max_right _ _).trans (hscale i hi q (by linarith [hr i]))) (hmeet i hi |>
      fun ⟨z, hz1, hz2⟩ => ⟨z, hz1, hZ hz2⟩)
    (N i) (n₀ i) (C i) (o i) hNcomp hNseg hcone (hδ.trans_le (min_le_right _ _)) ⟨F⟩

end Selection

end DifferentialGeometry.Geometry.Collapse
