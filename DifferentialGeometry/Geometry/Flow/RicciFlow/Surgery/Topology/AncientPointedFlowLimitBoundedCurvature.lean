import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.AncientPointedFlowLimitCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialNeckScalarBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SpatialCanonicalWitness
import DifferentialGeometry.Geometry.Flow.RicciFlow.HamiltonHarnack.TerminalScalar
import DifferentialGeometry.Geometry.Curvature.ScalarControlsRm
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Nonnegative

set_option autoImplicit false

noncomputable section
open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

theorem le_two_mul_of_abs_deriv_le_mul_sq_of_right_le {u : ℝ → ℝ} {B K a b : ℝ}
    (hB : 0 < B) (hK : 0 ≤ K) (hdiff : ∀ s ∈ Icc a b, DifferentiableAt ℝ u s)
    (hder : ∀ s ∈ Icc a b, B < u s → |deriv u s| ≤ K * u s ^ 2) (hb : u b ≤ B)
    (hlen : K * (b - a) ≤ 1 / (2 * B)) : ∀ s ∈ Icc a b, u s ≤ 2 * B := by
  intro s₁ hs₁
  by_contra hlt
  push Not at hlt
  have hcont : ContinuousOn u (Icc a b) := fun s hs => (hdiff s hs).continuousAt.continuousWithinAt
  let S := {s ∈ Icc s₁ b | u s ≤ B}
  have hsub : Icc s₁ b ⊆ Icc a b := Icc_subset_Icc_left hs₁.1
  have hSclosed : IsClosed S :=
    (hcont.mono hsub).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hbS : b ∈ S := ⟨⟨hs₁.2, le_rfl⟩, hb⟩
  have hSne : S.Nonempty := ⟨b, hbS⟩
  have hSbdd : BddBelow S := ⟨s₁, fun s hs => hs.1.1⟩
  set c := sInf S with hc
  have hcS : c ∈ S := hSclosed.csInf_mem hSne hSbdd
  have hs₁c : s₁ < c := by
    rcases hcS.1.1.eq_or_lt with h | h
    · rw [← h] at hcS
      linarith [hcS.2]
    · exact h
  have hgt : ∀ s ∈ Ico s₁ c, B < u s := by
    intro s hs
    by_contra hle
    push Not at hle
    have hsS : s ∈ S := ⟨⟨hs.1, hs.2.le.trans hcS.1.2⟩, hle⟩
    exact absurd (csInf_le hSbdd hsS) (not_le.mpr hs.2)
  have hsc : Icc s₁ c ⊆ Icc a b := fun s hs => hsub ⟨hs.1, hs.2.trans hcS.1.2⟩
  have hge : ∀ s ∈ Icc s₁ c, B ≤ u s := by
    have hclosed : IsClosed {s ∈ Icc s₁ c | B ≤ u s} :=
      (hcont.mono hsc).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
    have hIco : Ico s₁ c ⊆ {s ∈ Icc s₁ c | B ≤ u s} :=
      fun s hs => ⟨Ico_subset_Icc_self hs, (hgt s hs).le⟩
    have hcl := hclosed.closure_subset_iff.mpr hIco
    rw [closure_Ico hs₁c.ne] at hcl
    exact fun s hs => (hcl hs).2
  have hpos : ∀ s ∈ Icc s₁ c, 0 < u s := fun s hs => hB.trans_le (hge s hs)
  have hfc : ContinuousOn (fun s => (u s)⁻¹) (Icc s₁ c) :=
    (hcont.mono hsc).inv₀ fun s hs => (hpos s hs).ne'
  have hfd : ∀ s ∈ Ioo s₁ c, HasDerivAt (fun s => (u s)⁻¹)
      (-(deriv u s) / (u s) ^ 2) s := by
    intro s hs
    exact (hdiff s (hsc (Ioo_subset_Icc_self hs))).hasDerivAt.inv
      (hpos s (Ioo_subset_Icc_self hs)).ne'
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope (fun s => (u s)⁻¹)
    (fun s => -(deriv u s) / (u s) ^ 2) hs₁c hfc hfd
  have hξpos : 0 < u ξ := hpos ξ (Ioo_subset_Icc_self hξ)
  have hbound : |-(deriv u ξ) / (u ξ) ^ 2| ≤ K := by
    rw [abs_div, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < u ξ ^ 2),
      div_le_iff₀ (by positivity)]
    exact hder ξ (hsc (Ioo_subset_Icc_self hξ)) (hgt ξ (Ioo_subset_Ico_self hξ))
  have hcb : c - s₁ ≤ b - a := by linarith [hcS.1.2, hs₁.1]
  have hdiffle : (u s₁)⁻¹ ≥ (u c)⁻¹ - K * (c - s₁) := by
    have hlen' : 0 < c - s₁ := sub_pos.mpr hs₁c
    have h1 : (u c)⁻¹ - (u s₁)⁻¹ = (-(deriv u ξ) / (u ξ) ^ 2) * (c - s₁) := by
      rw [hslope]
      field_simp
    have h2 := (abs_le.mp hbound).2
    nlinarith
  have hinvc : (1 : ℝ) / B ≤ (u c)⁻¹ := by
    rw [one_div]
    exact inv_anti₀ (hpos c ⟨hs₁c.le, le_rfl⟩) hcS.2
  have hKlen : K * (c - s₁) ≤ 1 / (2 * B) :=
    (mul_le_mul_of_nonneg_left hcb hK).trans hlen
  have hfinal : 1 / (2 * B) ≤ (u s₁)⁻¹ := by
    have : 1 / B - 1 / (2 * B) = 1 / (2 * B) := by field_simp; ring
    linarith
  have hu1 : 0 < u s₁ := by linarith
  rw [one_div, inv_le_inv₀ (by positivity) hu1] at hfinal
  linarith

theorem le_two_mul_of_abs_deriv_le_mul_sq_of_left_le {u : ℝ → ℝ} {B K a b : ℝ}
    (hB : 0 < B) (hK : 0 ≤ K) (hdiff : ∀ s ∈ Icc a b, DifferentiableAt ℝ u s)
    (hder : ∀ s ∈ Icc a b, B < u s → |deriv u s| ≤ K * u s ^ 2) (ha : u a ≤ B)
    (hlen : K * (b - a) ≤ 1 / (2 * B)) : ∀ s ∈ Icc a b, u s ≤ 2 * B := by
  have hmem : ∀ s ∈ Icc (-b) (-a), -s ∈ Icc a b :=
    fun s hs => ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hv := le_two_mul_of_abs_deriv_le_mul_sq_of_right_le (u := fun s => u (-s)) (a := -b)
    (b := -a) hB hK
    (fun s hs => (hdiff (-s) (hmem s hs)).comp s (differentiableAt_neg_iff.mpr
      (differentiableAt_id)))
    (fun s hs hlt => by
      rw [deriv_comp_neg, abs_neg]
      exact hder (-s) (hmem s hs) hlt)
    (by simpa only [neg_neg] using ha) (by linarith)
  intro s hs
  simpa only [neg_neg] using hv (-s) ⟨by linarith [hs.2], by linarith [hs.1]⟩

universe u

theorem exists_scalar_bound_of_curvatureOperator_nonnegative_of_spatialCanonicalWitness :
    ∃ eps₀ : ℝ, 0 < eps₀ ∧ ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
      (g : SmoothRiemannianMetric I3 M), RiemannianMetricComplete g →
      (∀ x : M, metricAlgebraicCurvatureTensorAt g x ∈ algebraicCurvatureOperatorNonnegativeCone) →
      ∀ {eps C1 C2 q : ℝ}, eps ≤ eps₀ →
      (∀ x : M, q < metricScalarAt g x →
        ∃ W : SpatialCanonicalWitness g eps C1 C2 x, W.capTubeHasNeckChart eps) →
      ∃ C : ℝ, ∀ x : M, metricScalarAt g x ≤ C := by
  obtain ⟨eta₀, heta₀, hneck⟩ := exists_spatialNeck_scalar_upper_bound.{u}
  refine ⟨eta₀, heta₀, ?_⟩
  intro M _ _ _ _ _ _ g hg hcone eps C1 C2 q heps hW
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have hsec : DifferentialGeometry.Geometry.HasNonnegativeSectionalCurvature g :=
    (DifferentialGeometry.Geometry.hasNonnegativeSectionalCurvature_iff g).mpr fun x v w =>
      (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff_sectional
        g x hdim).mp (hcone x) v w
  obtain ⟨Cn, hCn⟩ := hneck M g hg hsec
  by_cases hcpt : CompactSpace M
  · obtain ⟨C, hC⟩ := (isCompact_univ.image (metricScalar_smooth g).continuous).bddAbove
    exact ⟨C, fun x => hC ⟨x, mem_univ x, rfl⟩⟩
  refine ⟨max q (max Cn (C2 * Cn)), fun x => ?_⟩
  by_cases hx : metricScalarAt g x ≤ q
  · exact hx.trans (le_max_left _ _)
  obtain ⟨W, hWc⟩ := hW x (lt_of_not_ge hx)
  have hwhole : W.domain.carrier = connectedComponent x → False := by
    intro hwhole
    apply hcpt
    have huniv : W.domain.carrier = univ := by
      rw [hwhole, PreconnectedSpace.connectedComponent_eq_univ]
    exact ⟨huniv ▸ W.domain.compact⟩
  cases halt : W.alternative with
  | neck data =>
    exact (hCn x eps heps data.neck).trans ((le_max_left _ _).trans (le_max_right _ _))
  | cap data deep =>
    obtain ⟨v, nk, hmap⟩ := hWc data deep halt
    have hvtube : v ∈ data.tube := by
      rw [← data.tube_eq]
      refine ⟨(nk.center, 0), ⟨mem_univ _, by norm_num⟩, ?_⟩
      rw [hmap]
      exact nk.center_eq
    have hv : v ∈ W.domain.carrier := by
      rw [data.union_eq]
      exact Or.inr hvtube
    have hRv := hCn v eps heps nk
    have hlow := (W.scalar_bounds v hv).1
    have hC2 : 1 ≤ C2 := W.one_le_comparison_constant
    have hx' : metricScalarAt g x ≤ C2 * metricScalarAt g v := by
      have h1 := mul_le_mul_of_nonneg_left hlow (by linarith : (0 : ℝ) ≤ C2)
      rwa [← mul_assoc, mul_inv_cancel₀ (by linarith : C2 ≠ 0), one_mul] at h1
    exact hx'.trans ((mul_le_mul_of_nonneg_left hRv (by linarith)).trans
      ((le_max_right _ _).trans (le_max_right _ _)))
  | positive whole data sec => exact (hwhole whole).elim
  | round whole data => exact (hwhole whole).elim

theorem exists_scalar_bound_of_ancient_curvatureOperator_nonnegative_of_slice_bounds
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] {G : ℝ → SmoothRiemannianMetric I3 M}
    (hS : IsSolutionOn ({ base.metric := G } : SolutionOn (I := I3) (M := M) ancientTimeInterval))
    (hcomplete : ∀ t ≤ 0, RiemannianMetricComplete (G t))
    (hcone : ∀ t ≤ 0, ∀ x : M,
      metricAlgebraicCurvatureTensorAt (G t) x ∈ algebraicCurvatureOperatorNonnegativeCone)
    (hCs : ∀ t ≤ 0, ∃ C : ℝ, ∀ x : M, metricScalarAt (G t) x ≤ C) {q Ctime : ℝ}
    (hderiv : ∀ t < 0, ∀ x : M, q < metricScalarAt (G t) x →
      |derivWithin (fun v => metricScalarAt (G v) x) (Iic t) t| ≤
        Ctime * metricScalarAt (G t) x ^ 2) :
    ∃ C : ℝ, ∀ t ≤ 0, ∀ x : M, metricScalarAt (G t) x ≤ C := by
  let _ : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  let S : SolutionOn (I := I3) (M := M) ancientTimeInterval := { base.metric := G }
  have hdiff : ∀ t < 0, ∀ x : M,
      DifferentiableAt ℝ (fun v => metricScalarAt (G v) x) t := by
    intro t ht x
    have h := hS.scalarTime (K := Iio 0) (t := t) ht (fun s hs => by
      rw [ancientTimeInterval_carrier]
      exact mem_Iic.mpr hs.le) x
    exact h.differentiableAt (Iio_mem_nhds ht)
  have hder : ∀ t < 0, ∀ x : M, q < metricScalarAt (G t) x →
      |deriv (fun v => metricScalarAt (G v) x) t| ≤ max Ctime 0 * metricScalarAt (G t) x ^ 2 := by
    intro t ht x hq
    have h := hderiv t ht x hq
    rw [(hdiff t ht x).derivWithin (uniqueDiffWithinAt_Iic t)] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _))
  have hwin : ∀ c d : ℝ, Icc c d ⊆ Iio 0 →
      ∃ C : ℝ, ∀ t ∈ Icc c d, ∀ x : M, metricScalarAt (G t) x ≤ C := by
    intro c d hcd
    refine isCompact_Icc.induction_on
      (p := fun T => ∃ C : ℝ, ∀ t ∈ T, ∀ x : M, metricScalarAt (G t) x ≤ C)
      ⟨0, fun t ht => ht.elim⟩ (fun T T' hTT' ⟨C, hC⟩ => ⟨C, fun t ht => hC t (hTT' ht)⟩)
      (fun T T' ⟨C, hC⟩ ⟨C', hC'⟩ => ⟨max C C', fun t ht x => ht.elim
        (fun h => (hC t h x).trans (le_max_left _ _))
        (fun h => (hC' t h x).trans (le_max_right _ _))⟩) ?_
    intro s hs
    have hs0 : s < 0 := hcd hs
    obtain ⟨Cs, hCs'⟩ := hCs s hs0.le
    set B := max (max Cs q) 1 with hBdef
    set K := max Ctime 0 with hKdef
    have hB : 0 < B := lt_of_lt_of_le one_pos (le_max_right _ _)
    have hK : 0 ≤ K := le_max_right _ _
    set δ := 1 / (2 * (K + 1) * B) with hδdef
    have hδ : 0 < δ := by positivity
    refine ⟨Icc c d ∩ Ioo (s - δ) (s + δ),
      inter_mem_nhdsWithin _ (Ioo_mem_nhds (by linarith) (by linarith)), 2 * B, ?_⟩
    rintro t ⟨htcd, htδ⟩ x
    have hKδ : ∀ w : ℝ, 0 ≤ w → w ≤ δ → K * w ≤ 1 / (2 * B) := by
      intro w hw0 hw
      have h1 : K * w ≤ (K + 1) * δ :=
        mul_le_mul (by linarith) hw hw0 (by linarith)
      have h2 : (K + 1) * δ = 1 / (2 * B) := by
        rw [hδdef]
        field_simp
      linarith
    have hderB : ∀ v < 0, B < metricScalarAt (G v) x →
        |deriv (fun v => metricScalarAt (G v) x) v| ≤ K * metricScalarAt (G v) x ^ 2 := by
      intro v hv hBv
      exact hder v hv x (lt_of_le_of_lt ((le_max_right _ _).trans (le_max_left _ _)) hBv)
    have hsB : metricScalarAt (G s) x ≤ B := (hCs' x).trans ((le_max_left _ _).trans
      (le_max_left _ _))
    rcases le_total t s with hts | hst
    · exact le_two_mul_of_abs_deriv_le_mul_sq_of_right_le (u := fun v => metricScalarAt (G v) x)
        hB hK (fun v hv => hdiff v (lt_of_le_of_lt hv.2 hs0) x)
        (fun v hv hBv => hderB v (lt_of_le_of_lt hv.2 hs0) hBv) hsB
        (hKδ _ (by linarith) (by linarith [htδ.1])) t ⟨le_rfl, hts⟩
    · have ht0 : t < 0 := hcd htcd
      exact le_two_mul_of_abs_deriv_le_mul_sq_of_left_le (u := fun v => metricScalarAt (G v) x)
        hB hK (fun v hv => hdiff v (lt_of_le_of_lt hv.2 ht0) x)
        (fun v hv hBv => hderB v (lt_of_le_of_lt hv.2 ht0) hBv) hsB
        (hKδ _ (by linarith) (by linarith [htδ.2])) t ⟨hst, le_rfl⟩
  have hcompleteR : ∀ t ∈ ancientTimeInterval.regular, RiemannianMetricComplete (S.base.metric t) :=
    fun t ht => hcomplete t (le_of_lt ht)
  have hRR : ∀ t ∈ ancientTimeInterval.regular, ∀ x : M,
      metricAlgebraicCurvatureTensorAt (S.base.metric t) x ∈
        algebraicCurvatureOperatorNonnegativeCone := fun t ht => hcone t (le_of_lt ht)
  have hcurv : ∀ c d : ℝ, Icc c d ⊆ ancientTimeInterval.regular →
      ∃ C : ℝ, ∀ t ∈ Icc c d, ∀ x : M,
        Tensor0SBundle.normSq0S (S.base.metric t) x 4 (S.base.rm04 t x) ≤ C := by
    intro c d hcd
    obtain ⟨C, hC⟩ := hwin c d hcd
    refine ⟨100 ^ 2 * C ^ 2, fun t ht x => ?_⟩
    have htneg : t < 0 := hcd ht
    have hbound := normSq_metricRm04_le_scalar_sq_of_curvatureOperator_nonnegative
      (G t) x hdim (hcone t htneg.le x)
    have h0 := metricScalarAt_nonnegative_of_curvatureOperator_nonnegative (G t) x
      (hcone t htneg.le x)
    change Tensor0SBundle.normSq0S (G t) x 4 (metricRm04 (G t) x) ≤ 100 ^ 2 * C ^ 2
    exact hbound.trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 (hC t ht x) 2)
      (by norm_num))
  obtain ⟨C₀, hC₀⟩ := hCs 0 le_rfl
  refine ⟨C₀, fun t ht x => ?_⟩
  have hH := hamilton_ancient_scalar_le_terminal S hS hcompleteR hcurv hRR (b := 0) ht
    (by rw [ancientTimeInterval_carrier]; exact mem_Iic.mpr le_rfl)
    (by rw [ancientTimeInterval_regular]) x
  exact hH.trans (hC₀ x)


theorem exists_scalar_bound_of_ancient_curvatureOperator_nonnegative_of_spatialCanonicalWitness :
    ∃ eps₀ : ℝ, 0 < eps₀ ∧ ∀ {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
      [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]
      {G : ℝ → SmoothRiemannianMetric I3 M},
      IsSolutionOn ({ base.metric := G } : SolutionOn (I := I3) (M := M) ancientTimeInterval) →
      (∀ t ≤ 0, RiemannianMetricComplete (G t)) →
      (∀ t ≤ 0, ∀ x : M,
        metricAlgebraicCurvatureTensorAt (G t) x ∈ algebraicCurvatureOperatorNonnegativeCone) →
      ∀ {eps C1 C2 q Ctime : ℝ}, eps ≤ eps₀ →
      (∀ t ≤ 0, ∀ x : M, q < metricScalarAt (G t) x →
        ∃ W : SpatialCanonicalWitness (G t) eps C1 C2 x, W.capTubeHasNeckChart eps) →
      (∀ t < 0, ∀ x : M, q < metricScalarAt (G t) x →
        |derivWithin (fun v => metricScalarAt (G v) x) (Iic t) t| ≤
          Ctime * metricScalarAt (G t) x ^ 2) →
      ∃ C : ℝ, ∀ t ≤ 0, ∀ x : M, metricScalarAt (G t) x ≤ C := by
  obtain ⟨eps₀, heps₀, hslice⟩ :=
    exists_scalar_bound_of_curvatureOperator_nonnegative_of_spatialCanonicalWitness.{u}
  refine ⟨eps₀, heps₀, ?_⟩
  intro M _ _ _ _ _ _ G hS hcomplete hcone eps C1 C2 q Ctime heps hW hderiv
  exact exists_scalar_bound_of_ancient_curvatureOperator_nonnegative_of_slice_bounds hS
    hcomplete hcone (fun t ht => hslice (G t) (hcomplete t ht) (hcone t ht) heps (hW t ht)) hderiv

section PointedLimit

open TopologicalSpace DifferentialGeometry.CheegerGromovCompactness

attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

theorem exists_scalar_bound_of_ancient_pointed_flow_limit :
    ∃ eps₀ : ℝ, 0 < eps₀ ∧ ∀ {X : PointedRiemannianSeq.{u, 0, 0} I3}
      {P : PointedRiemannianManifold.{u, 0, 0} I3} {W : ∀ (_ : ℕ) (n : ℕ), Opens (X.obj n).M}
      {h : ∀ k n, ℝ → SmoothRiemannianMetric I3 (W k n)} {f : ℕ → ℕ}, StrictMono f →
      MetricComplete P → ConnectedSpace P.M → ∀ {V : ℕ → Opens P.M},
      (∀ k, (V k : Set P.M) = riemannianBallOf P.metric P.basepoint (((k + 1 : ℕ) : ℝ) / 2)) →
      ∀ {N : ℕ → ℕ} {φ : ∀ k j, N k ≤ j → V k → W k (f j)}
        {hφ : ∀ k j (hj : N k ≤ j), IsLocalDiffeomorph I3 I3 ∞ (φ k j hj)}
        {G : ℝ → SmoothRiemannianMetric I3 P.M}, G 0 = P.metric →
      IsSolutionOn ({ base.metric := G } : SolutionOn (I := I3) (M := P.M)
        ancientTimeInterval) →
      ∀ {ψ : ℕ → ℕ}, StrictMono ψ →
      (∀ k (K : Set (V k)), IsCompact K → ∀ p : ℕ, ∀ η : ℝ, 0 < η →
        ∃ j₀ : ℕ, ∀ i ≥ j₀, ∃ hi : N k ≤ ψ i, ∀ t ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0,
          metricDerivNormSupOn K p
            (localPullMetric (h k (f (ψ i)) t) (φ k (ψ i) hi) (hφ k (ψ i) hi))
            ((G t).restrictOpen (V k)) (P.metric.restrictOpen (V k)) < η) →
      ∀ {Q : ℕ → ℝ}, Tendsto Q atTop atTop → ∀ {Phi : ℝ → ℝ}, AdmissiblePinchingFunction Phi →
      (∀ k : ℕ, ∀ᶠ n in atTop, ∀ t ∈ Icc (-((k + 1 : ℕ) : ℝ)) 0, ∀ x : W k n,
        curvatureOperatorLowerBoundAt (h k n t) x (metricAlgebraicCurvatureTensorAt (h k n t) x)
          (rescalePinchingFunction (Q n) Phi (metricScalarAt (h k n t) x))) →
      ∀ {eps C1 C2 q Ctime : ℝ}, eps ≤ eps₀ →
      (∀ t ≤ 0, ∀ x : P.M, q < metricScalarAt (G t) x →
        ∃ W : SpatialCanonicalWitness (G t) eps C1 C2 x, W.capTubeHasNeckChart eps) →
      (∀ t < 0, ∀ x : P.M, q < metricScalarAt (G t) x →
        |derivWithin (fun v => metricScalarAt (G v) x) (Iic t) t| ≤
          Ctime * metricScalarAt (G t) x ^ 2) →
      ∃ C : ℝ, ∀ t ≤ 0, ∀ x : P.M, metricScalarAt (G t) x ≤ C := by
  obtain ⟨eps₀, heps₀, hmain⟩ :=
    exists_scalar_bound_of_ancient_curvatureOperator_nonnegative_of_spatialCanonicalWitness.{u}
  refine ⟨eps₀, heps₀, ?_⟩
  intro X P W h f hf hPc hconn V hV N φ hφ G hG0 hGsol ψ hψ hconv Q hQ Phi hPhi hpinch
    eps C1 C2 q Ctime heps hW hderiv
  obtain ⟨hcone, hcomplete⟩ := ancient_pointed_flow_limit_curvatureOperator_nonnegative_and_complete
    hf hPc hconn hV hG0 hGsol hψ hconv hQ hPhi hpinch
  exact hmain hGsol hcomplete hcone heps hW hderiv

end PointedLimit

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
