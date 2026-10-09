import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckScaleStability
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonScalarCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ComparisonParabolicScaling

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

variable {P : Type u} [TopologicalSpace P] [ChartedSpace ThreeSpace P]
  [IsManifold I3 ∞ P] [T2Space P] [SigmaCompactSpace P]

private local instance neckLimitC1 : IsManifold I3 1 P :=
  IsManifold.of_le (n := ∞) (by decide)

theorem StrongNeck.eventually_transport_of_comparisons
    {Sm : SolutionOn (I := I3) (M := P) ancientTimeInterval} (hSm : IsSolutionOn Sm)
    {alpha : ℝ} {p : P} (nk : StrongNeck Sm (neckModelTolerance alpha) p 0)
    (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11)
    (U : TopologicalSpace.Opens P) (hUcompact : IsCompact (closure (U : Set P)))
    {K : Set P} (hK : IsCompact K) (hKU : K ⊆ U)
    (houter : ∀ y ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹, nk.map y ∈ K)
    {M : ℕ → Type u} [∀ i, TopologicalSpace (M i)] [∀ i, ChartedSpace ThreeSpace (M i)]
    [∀ i, IsManifold I3 ∞ (M i)] [∀ i, T2Space (M i)] [∀ i, SigmaCompactSpace (M i)]
    {D : ℕ → RealTimeInterval} (S : ∀ i, SolutionOn (I := I3) (M := M i) (D i))
    (hS : ∀ i, IsSolutionOn (S i)) (F : ∀ i, PartialDiffeomorph I3 I3 P (M i) ∞)
    (hsource : ∀ᶠ i in atTop, (U : Set P) ⊆ (F i).source)
    (htimes : ∀ A : ℝ, 0 < A → ∀ᶠ i in atTop,
      Icc (-A) 0 ⊆ (D i).carrier ∧ Ioo (-A) 0 ⊆ (D i).regular)
    (hcompare : ∀ A : ℝ, 0 < A → ∀ order : ℕ, ∀ delta : ℝ, 0 < delta → ∀ᶠ i in atTop,
      Nonempty (MetricComparisonOn Sm.base.metric (S i).base.metric
        (F i) U (Icc (-A) 0) order delta)) :
    ∀ᶠ i in atTop, ∃ nk' : StrongNeck (S i) (2 * alpha) (F i p) 0,
      nk'.map = partialDiffeomorphTransMixed nk.map (F i) := by
  have hp : p ∈ U := by
    rw [← nk.center_eq]
    apply hKU
    exact houter (nk.center, 0) ⟨mem_univ _, neg_neg_of_pos (inv_pos.mpr ha), inv_pos.mpr ha⟩
  let r := Sm.scalar 0 p
  have hr : 0 < r := nk.Q_pos
  let q (i : ℕ) := (S i).scalar 0 (F i p)
  have hqlim : Tendsto q atTop (𝓝 r) := by
    have hh := tendsto_metricScalarAt_of_comparisons Sm.base.metric
      (fun i => (S i).base.metric) F U
      (show (0 : ℝ) ∈ Icc (-1 : ℝ) 0 by norm_num) (by norm_num : 2 ≤ 2) hp hsource
      (hcompare 1 zero_lt_one 2)
    exact hh
  obtain ⟨eta, beta, heta, hbeta, htransfer⟩ :=
    nk.exists_rescaled_transport_tolerances_of_ancient hSm ha hsmall U hUcompact hK hKU houter
  let order := ⌈(2 * alpha)⁻¹⌉₊
  let L := (max 1 (Real.sqrt (r / 2))⁻¹) ^ order
  have hL : 0 < L := pow_pos (lt_max_of_lt_left zero_lt_one) _
  let delta := beta / L
  have hd : 0 < delta := div_pos hbeta hL
  let A := 4 / r
  have hA : 0 < A := div_pos (by norm_num) hr
  have hqnear : ∀ᶠ i in atTop, |q i - r| < eta := by
    simpa only [Real.dist_eq] using (Metric.tendsto_nhds.mp hqlim) eta heta
  have hqlower : ∀ᶠ i in atTop, r / 2 < q i := hqlim.eventually (eventually_gt_nhds (by linarith : r / 2 < r))
  filter_upwards [hsource, hqnear, hqlower, htimes (A + 1) (by positivity),
    hcompare A hA order delta hd] with i hi hnear hlow htime hcmp
  have hq : 0 < q i := (div_pos hr (by norm_num)).trans hlow
  have hAq : 2 ≤ A * q i := by
    have hh := mul_le_mul_of_nonneg_left hlow.le hA.le
    have heq : A * (r / 2) = 2 := by dsimp only [A]; field_simp; ring
    rwa [heq] at hh
  have hmap : MapsTo (parabolicTime 0 (q i)) (Icc (-2 : ℝ) 0) (Icc (-A) 0) := by
    intro s hs
    simp only [parabolicTime, zero_add]
    constructor
    · apply (le_div_iff₀ hq).mpr
      nlinarith [hs.1]
    · exact div_nonpos_of_nonpos_of_nonneg hs.2 hq.le
  have hmapOne : MapsTo (parabolicTime 0 (q i)) (Icc (-1 : ℝ) 0) (Icc (-A) 0) := by
    intro s hs
    exact hmap ⟨by linarith [hs.1], hs.2⟩
  have hdomain : Icc (-A - 1) 0 ⊆ (D i).carrier := by
    simpa only [neg_add, sub_eq_add_neg] using htime.1
  have hregular : Ioo (-A - 1) 0 ⊆ (D i).regular := by
    simpa only [neg_add, sub_eq_add_neg] using htime.2
  obtain ⟨C⟩ := hcmp
  let C' := C.parabolicRescale 0 (q i) hq order le_rfl (Icc (-1 : ℝ) 0)
    (uniqueDiffOn_Icc (by norm_num : (-1 : ℝ) < 0)) hmapOne (by
      intro b s hs y hy v
      exact (C.jet_contDiffOn_of_solutions Sm hSm (S i) (hS i)
        (show -A - 1 < -A by linarith) (show -A - 1 < -A by linarith)
        (neg_lt_zero.mpr hA) (fun _ ht => ht.2) (fun _ ht => ht.2) hdomain hregular
        b y hy v _ (hmapOne hs)).differentiableWithinAt (by simp))
  have hweight : (max 1 (Real.sqrt (q i))⁻¹) ^ order ≤ L := by
    apply pow_le_pow_left₀ (zero_le_one.trans (le_max_left _ _))
    apply max_le_max_left
    exact inv_anti₀ (Real.sqrt_pos.mpr (div_pos hr (by norm_num)))
      (Real.sqrt_le_sqrt hlow.le)
  have hloss : (max 1 (Real.sqrt (q i))⁻¹) ^ order * delta ≤ beta := by
    calc
      _ ≤ L * delta := mul_le_mul_of_nonneg_right hweight hd.le
      _ = beta := by dsimp only [delta]; field_simp
  have Cnorm : MetricComparisonOn (rescaledMetric Sm 0 (q i) hq)
      (rescaledMetric (S i) 0 (q i) hq) (F i) U (Icc (-1 : ℝ) 0) order beta :=
    C'.mono (subset_refl _) le_rfl hloss
  apply htransfer (q i) hq hnear (M i) (S i) (hS i)
    hq (b := -2) (by norm_num) ?_ ?_ (F i) hi rfl Cnorm
  · intro s hs
    apply hdomain
    have hh := hmap hs
    exact ⟨by linarith [hh.1], hh.2⟩
  · intro s hs
    apply hregular
    have hh := hmap ⟨hs.1.le, hs.2.le⟩
    refine ⟨by linarith [hh.1], ?_⟩
    change 0 + s / q i < 0
    simpa only [zero_add] using div_neg_of_neg_of_pos hs.2 hq

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
