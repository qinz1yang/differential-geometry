import DifferentialGeometry.Geometry.Collapse.CurvatureScaleBalls
import DifferentialGeometry.Geometry.Metric.Distance.InducedMetricSpaceApplications
import DifferentialGeometry.Topology.MetricSpace.VariableRadiusCover

/-!
# Selection and the LC86 cover at the curvature scale

The proved selection and multiplicity kernels are bound to the actual curvature scale
`R_p = curvatureRadius g p` (`Geometry/Collapse/CurvatureScale.lean`) of a smooth metric `g` on a
compact connected manifold, with the distance induced by `g` (`inducedMetricSpace g`,
`Geometry/Metric/Distance/InducedMetricSpace.lean`). The scale is `ρ p = c R_p` for a constant
`c > 0`; nothing about the cover is assumed.

* T1 (the scale): `ρ` is positive (`toReal_curvatureRadius_pos`), `c`-Lipschitz for `g`
  (`abs_curvatureScale_sub_le`, `lipschitzWith_curvatureScale`) and pinched between two positive
  constants on a compact manifold (`exists_toReal_curvatureRadius_bounds`).
* T2 (Ricci at the curvature scale): below `R_p` the Ricci curvature on the `g`-ball of radius `a`
  is at least `(n - 1)(-a⁻²)` (`ricciBoundedBelowOn_of_lt_curvatureRadius`); on the enlarged
  ball of radius `D ρ p` with `D c < 1` this is the bound `(n - 1)(-(D⁻¹ / ρ p)²)` consumed by LC86
  (`ricciBoundedBelowOn_curvatureScale`).
* T3 (LC63 at the curvature scale): `exists_finite_disjoint_curvatureScale_selection`, from
  `Metric.exists_finite_disjoint_ball_selection` (`Topology/MetricSpace/VariableRadiusCover.lean`).
* T4 (LC86 at the curvature scale): `exists_finite_curvatureScale_cover_of_subset` (centres in an
  arbitrary set `S`), `exists_finite_curvatureScale_cover` (all of `M`) and
  `exists_finite_curvatureScale_cover_riemannianBallOf` (every ball a `g`-ball), from the LC86
  Riemannian adapter `exists_finite_scale_cover_of_ricci_bound`
  (`Geometry/Comparison/Volume/RicciScaleMultiplicity.lean`) through its installation on the
  induced metric (`exists_finite_scale_cover_of_ricci_bound_induced`). The multiplicity constant
  `V_{-q²}(3C + 2Δ/3) / V_{-q²}(Δ/3)` with `q = (3C + 2Δ/3)⁻¹` depends only on `C`, `Δ` and the
  dimension.

Paper proof of T4: `ρ` is `c`-Lipschitz (A1 T5), so `Λ = c`. Since `c Δ ≤ 1/100` and
`c C ≤ 1/4`, `D c ≤ 3/4 + 1/150 < 1` for `D = 3C + 2Δ/3`, hence the ball of radius `a = D ρ p`
lies below the curvature scale `R_p`; A1 T1 gives `sec ≥ -a⁻²` on it, and the trace over an
orthonormal complement gives `Ric ≥ (n - 1)(-a⁻²) = (n - 1)(-(q / ρ p)²)`.

The finiteness hypothesis `∀ p, curvatureRadius g p ≠ ⊤` concerns `g` only; on a connected
manifold it is equivalent to `¬ SectionalBoundedBelow g 0` (`curvatureRadius_eq_top_iff`,
`curvatureRadius_ne_top_of_not_sectionalBoundedBelow`).
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open Bundle Filter Set
open scoped Manifold ContDiff ENNReal NNReal Topology
namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

section Normed

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-! ### T1: the curvature scale `ρ = c R` -/

omit [CompleteSpace E] in
/-- Finiteness of every curvature scale from a point of somewhere-negative sectional curvature
(the converse direction of `curvatureRadius_eq_top_iff`). -/
theorem curvatureRadius_ne_top_of_not_sectionalBoundedBelow [ConnectedSpace M]
    {g : SmoothRiemannianMetric I M} (hneg : ¬ SectionalBoundedBelow g 0) (p : M) :
    curvatureRadius g p ≠ ⊤ :=
  fun htop => hneg ((curvatureRadius_eq_top_iff p).mp htop)

/-- A finite curvature scale is a positive real number. -/
theorem toReal_curvatureRadius_pos [T2Space M] (g : SmoothRiemannianMetric I M) {p : M}
    (hfin : curvatureRadius g p ≠ ⊤) : 0 < (curvatureRadius g p).toReal :=
  ENNReal.toReal_pos (curvatureRadius_pos g p).ne' hfin

omit [CompleteSpace E] in
/-- The scale `c R` is `c`-Lipschitz for the distance of `g` (A1 T5). -/
theorem abs_curvatureScale_sub_le [ConnectedSpace M] (g : SmoothRiemannianMetric I M)
    (hfin : ∀ p, curvatureRadius g p ≠ ⊤) {c : ℝ} (hc : 0 ≤ c) (p q : M) :
    |c * (curvatureRadius g p).toReal - c * (curvatureRadius g q).toReal| ≤
      c * (riemannianEDistOf (I := I) g p q).toReal := by
  rw [← mul_sub, abs_mul, abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (abs_toReal_curvatureRadius_sub_le g hfin p q) hc

omit [CompleteSpace E] in
/-- The scale `c R` is `c`-Lipschitz for the metric induced by `g`. -/
theorem lipschitzWith_curvatureScale [T3Space M] [ConnectedSpace M]
    (g : SmoothRiemannianMetric I M) (hfin : ∀ p, curvatureRadius g p ≠ ⊤) (c : ℝ≥0) :
    letI := inducedMetricSpace g
    LipschitzWith c (fun p => (c : ℝ) * (curvatureRadius g p).toReal) :=
  inducedMetricSpace_lipschitzWith_iff.2
    (abs_curvatureScale_sub_le g hfin c.coe_nonneg)

/-- On a compact connected manifold with finite curvature scales, the real curvature scale is
pinched between two positive constants. -/
theorem exists_toReal_curvatureRadius_bounds [T3Space M] [ConnectedSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (hfin : ∀ p, curvatureRadius g p ≠ ⊤) :
    ∃ a b : ℝ, 0 < a ∧ ∀ p : M,
      a ≤ (curvatureRadius g p).toReal ∧ (curvatureRadius g p).toReal ≤ b := by
  obtain ⟨a, ha, hfloor⟩ := exists_pos_le_curvatureRadius g
  let := inducedMetricSpace g
  have hLip := lipschitzWith_curvatureScale g hfin 1
  obtain ⟨b, hb⟩ := isCompact_univ.bddAbove_image hLip.continuous.continuousOn
  refine ⟨a, b, ha, fun p => ⟨?_, ?_⟩⟩
  · have h := ENNReal.toReal_mono (hfin p) (hfloor p)
    rwa [ENNReal.toReal_ofReal ha.le] at h
  · have h := hb (mem_image_of_mem _ (mem_univ p))
    simpa using h

/-! ### T2: Ricci curvature below the curvature scale -/

omit [CompleteSpace E] in
/-- T2. Below the curvature scale, the `g`-ball of radius `a` has Ricci curvature at least
`(n - 1)(-a⁻²)` (A1 T1 traced over an orthonormal complement). -/
theorem ricciBoundedBelowOn_of_lt_curvatureRadius [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) {p : M} {a : ℝ}
    (hR : ENNReal.ofReal a < curvatureRadius g p) :
    ricciBoundedBelowOn (I := I) g (riemannianBallOf g p a)
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) * (-(a ^ 2)⁻¹)) := by
  intro x hx v
  exact ricci_lower_of_sectionalBoundedBelowAt g x
    (sectionalBoundedBelowAt_of_lt_curvatureRadius g hR hx) v

/-- T2 at the curvature scale. If `D c < 1`, then on the `g`-ball of radius `D ρ p`, where
`ρ p = c R_p`, the Ricci curvature is at least `(n - 1)(-(D⁻¹ / ρ p)²)`: the Ricci hypothesis of
the LC86 adapter with `q = D⁻¹`. -/
theorem ricciBoundedBelowOn_curvatureScale [I.Boundaryless] [T2Space M]
    (g : SmoothRiemannianMetric I M) {p : M} (hfin : curvatureRadius g p ≠ ⊤)
    {c D : ℝ} (hc : 0 < c) (hD : 0 < D) (hDc : D * c < 1) :
    ricciBoundedBelowOn (I := I) g
      (riemannianBallOf g p (D * (c * (curvatureRadius g p).toReal)))
      (((Module.finrank ℝ E - 1 : ℕ) : ℝ) *
        (-((D⁻¹ / (c * (curvatureRadius g p).toReal)) ^ 2))) := by
  have hR := toReal_curvatureRadius_pos g hfin
  set R := (curvatureRadius g p).toReal with hRdef
  have hlt : D * (c * R) < R := by
    have h : D * (c * R) = (D * c) * R := by ring
    rw [h]
    exact mul_lt_of_lt_one_left hR hDc
  have hRlt : ENNReal.ofReal (D * (c * R)) < curvatureRadius g p := by
    rw [← ENNReal.ofReal_toReal hfin]
    exact (ENNReal.ofReal_lt_ofReal_iff hR).mpr hlt
  have hκ : (D⁻¹ / (c * R)) ^ 2 = ((D * (c * R)) ^ 2)⁻¹ := by
    field_simp
  rw [hκ]
  exact ricciBoundedBelowOn_of_lt_curvatureRadius g hRlt

/-! ### T3: LC63 at the curvature scale -/

/-- T3. LC63 for the radii `r p = c R_p` of the metric induced by `g`: a finite subfamily of
centres in an arbitrary set `P` with disjoint balls, such that every ball centred in `P` meets a
selected ball of at least half its radius, whose centre lies within three selected radii and whose
quintuple contains it. -/
theorem exists_finite_disjoint_curvatureScale_selection [T3Space M] [ConnectedSpace M]
    [CompactSpace M] (g : SmoothRiemannianMetric I M) (hfin : ∀ p : M, curvatureRadius g p ≠ ⊤)
    (P : Set M) {c : ℝ} (hc : 0 < c) :
    letI := inducedMetricSpace g
    let r : M → ℝ := fun p => c * (curvatureRadius g p).toReal
    ∃ J : Set M, J ⊆ P ∧ J.Finite ∧ J.PairwiseDisjoint (fun p => Metric.ball p (r p)) ∧
      ∀ p ∈ P, ∃ i ∈ J, (Metric.ball p (r p) ∩ Metric.ball i (r i)).Nonempty ∧
        r p ≤ 2 * r i ∧ dist p i < 3 * r i ∧ Metric.ball p (r p) ⊆ Metric.ball i (5 * r i) := by
  let := inducedMetricSpace g
  intro r
  obtain ⟨a, b, ha, hab⟩ := exists_toReal_curvatureRadius_bounds g hfin
  exact Metric.exists_finite_disjoint_ball_selection
    (isCompact_univ.totallyBounded.subset (subset_univ P)) r (mul_pos hc ha)
    (fun p _ => mul_le_mul_of_nonneg_left (hab p).1 hc.le)
    (fun p _ => mul_le_mul_of_nonneg_left (hab p).2 hc.le)

/-- T3 with every ball a `g`-ball and the distance of `g`: no metric structure occurs in the
statement. -/
theorem exists_finite_disjoint_curvatureScale_selection_riemannianBallOf [T3Space M]
    [ConnectedSpace M] [CompactSpace M] (g : SmoothRiemannianMetric I M)
    (hfin : ∀ p : M, curvatureRadius g p ≠ ⊤) (P : Set M) {c : ℝ} (hc : 0 < c) :
    let r : M → ℝ := fun p => c * (curvatureRadius g p).toReal
    ∃ J : Set M, J ⊆ P ∧ J.Finite ∧ J.PairwiseDisjoint (fun p => riemannianBallOf g p (r p)) ∧
      ∀ p ∈ P, ∃ i ∈ J, (riemannianBallOf g p (r p) ∩ riemannianBallOf g i (r i)).Nonempty ∧
        r p ≤ 2 * r i ∧ (riemannianEDistOf (I := I) g p i).toReal < 3 * r i ∧
          riemannianBallOf g p (r p) ⊆ riemannianBallOf g i (5 * r i) := by
  intro r
  have h := exists_finite_disjoint_curvatureScale_selection g hfin P hc
  simp only [inducedMetricSpace_ball g, inducedMetricSpace_dist g] at h
  exact h

end Normed

/-! ### T4: LC86 at the curvature scale -/

section Inner

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space (TangentBundle I M)]
  [T3Space M] [ConnectedSpace M] [CompactSpace M]

/-- The early constants force the enlarged LC86 ball below the curvature scale:
`c Δ ≤ 1/100` and `c C ≤ 1/4` give `(3C + 2Δ/3) c < 1`. -/
theorem curvatureScale_enlargement_lt_one {c Δ C : ℝ}
    (hsel : c * Δ ≤ 1 / 100) (hover : c * C ≤ 1 / 4) :
    (3 * C + 2 * (Δ / 3)) * c < 1 := by
  have h : (3 * C + 2 * (Δ / 3)) * c = 3 * (c * C) + 2 / 3 * (c * Δ) := by ring
  rw [h]
  linarith

/-- T4 (LC86 at the curvature scale, centres in an arbitrary set `S`). For the scale
`ρ p = c R_p` and the metric induced by `g`, with `c Δ ≤ 1/100` and `c C ≤ 1/4`: finitely many
centres in `S` whose `Δρ/3`-balls are disjoint, whose `2Δρ`-balls contain every `Δρ`-ball centred
in `S`, and such that every point lies in at most
`V_{-q²}(3C + 2Δ/3) / V_{-q²}(Δ/3)` of the `Cρ`-balls, `q = (3C + 2Δ/3)⁻¹`. -/
theorem exists_finite_curvatureScale_cover_of_subset
    (g : SmoothRiemannianMetric I M) (hfin : ∀ p : M, curvatureRadius g p ≠ ⊤) (S : Set M)
    {c Δ C : ℝ} (hc : 0 < c) (hΔ : 0 < Δ) (hC : 0 ≤ C)
    (hsel : c * Δ ≤ 1 / 100) (hover : c * C ≤ 1 / 4) :
    letI := inducedMetricSpace g
    let ρ : M → ℝ := fun p => c * (curvatureRadius g p).toReal
    let q : ℝ := (3 * C + 2 * (Δ / 3))⁻¹
    ∃ J : Set M, J ⊆ S ∧ J.Finite ∧ J.PairwiseDisjoint (fun p => Metric.ball p (Δ * ρ p / 3)) ∧
      (∀ p ∈ S, ∃ i ∈ J, Metric.ball p (Δ * ρ p) ⊆ Metric.ball i (2 * Δ * ρ i)) ∧
      ∀ x : M, ((J ∩ {i | x ∈ Metric.ball i (C * ρ i)}).ncard : ℝ) ≤
        modelVolume (-(q ^ 2)) (Module.finrank ℝ E) (3 * C + 2 * (Δ / 3)) /
          modelVolume (-(q ^ 2)) (Module.finrank ℝ E) (Δ / 3) := by
  intro ρ q
  have hD : 0 < 3 * C + 2 * (Δ / 3) := by positivity
  have hDc := curvatureScale_enlargement_lt_one hsel hover
  exact exists_finite_scale_cover_of_ricci_bound_induced (Λ := ⟨c, hc.le⟩) g S
    (abs_curvatureScale_sub_le g hfin hc.le)
    (fun p => mul_pos hc (toReal_curvatureRadius_pos g (hfin p)))
    hΔ hC (inv_nonneg.mpr hD.le) hsel hover
    (fun p _ => ricciBoundedBelowOn_curvatureScale g (hfin p) hc hD hDc)

/-- T4, the plan's form (`A5 SEL`): the LC86 cover of the whole manifold at the curvature scale. -/
theorem exists_finite_curvatureScale_cover
    (g : SmoothRiemannianMetric I M) (hfin : ∀ p : M, curvatureRadius g p ≠ ⊤)
    {c Δ C : ℝ} (hc : 0 < c) (hΔ : 0 < Δ) (hC : 0 ≤ C)
    (hsel : c * Δ ≤ 1 / 100) (hover : c * C ≤ 1 / 4) :
    letI := inducedMetricSpace g
    let ρ : M → ℝ := fun p => c * (curvatureRadius g p).toReal
    let q : ℝ := (3 * C + 2 * (Δ / 3))⁻¹
    ∃ J : Set M, J.Finite ∧ J.PairwiseDisjoint (fun p => Metric.ball p (Δ * ρ p / 3)) ∧
      (∀ p : M, ∃ i ∈ J, Metric.ball p (Δ * ρ p) ⊆ Metric.ball i (2 * Δ * ρ i)) ∧
      ∀ x : M, ((J ∩ {i | x ∈ Metric.ball i (C * ρ i)}).ncard : ℝ) ≤
        modelVolume (-(q ^ 2)) (Module.finrank ℝ E) (3 * C + 2 * (Δ / 3)) /
          modelVolume (-(q ^ 2)) (Module.finrank ℝ E) (Δ / 3) := by
  obtain ⟨J, -, hJ, hdisj, hcover, hmult⟩ :=
    exists_finite_curvatureScale_cover_of_subset g hfin univ hc hΔ hC hsel hover
  exact ⟨J, hJ, hdisj, fun p => hcover p (mem_univ p), hmult⟩

/-- T4 with every ball a `g`-ball: no metric structure occurs in the statement. -/
theorem exists_finite_curvatureScale_cover_riemannianBallOf
    (g : SmoothRiemannianMetric I M) (hfin : ∀ p : M, curvatureRadius g p ≠ ⊤) (S : Set M)
    {c Δ C : ℝ} (hc : 0 < c) (hΔ : 0 < Δ) (hC : 0 ≤ C)
    (hsel : c * Δ ≤ 1 / 100) (hover : c * C ≤ 1 / 4) :
    let ρ : M → ℝ := fun p => c * (curvatureRadius g p).toReal
    let q : ℝ := (3 * C + 2 * (Δ / 3))⁻¹
    ∃ J : Set M, J ⊆ S ∧ J.Finite ∧
      J.PairwiseDisjoint (fun p => riemannianBallOf g p (Δ * ρ p / 3)) ∧
      (∀ p ∈ S, ∃ i ∈ J, riemannianBallOf g p (Δ * ρ p) ⊆ riemannianBallOf g i (2 * Δ * ρ i)) ∧
      ∀ x : M, ((J ∩ {i | x ∈ riemannianBallOf g i (C * ρ i)}).ncard : ℝ) ≤
        modelVolume (-(q ^ 2)) (Module.finrank ℝ E) (3 * C + 2 * (Δ / 3)) /
          modelVolume (-(q ^ 2)) (Module.finrank ℝ E) (Δ / 3) := by
  intro ρ q
  have h := exists_finite_curvatureScale_cover_of_subset g hfin S hc hΔ hC hsel hover
  simp only [inducedMetricSpace_ball g] at h
  exact h

end Inner

end DifferentialGeometry.Geometry.Collapse
