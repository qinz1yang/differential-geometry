import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.Families.Preparation

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Surgery.Topology Width

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

theorem polygonVertex_edist_le_of_lipschitz (g : SmoothRiemannianMetric I Q)
    (γ : Surgery.Topology.Circle → Q) (L : ℝ≥0)
    (hL : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (L : ℝ≥0∞) * edist x y)
    {N : ℕ} (hN : 0 < N) (i : ℤ) :
    riemannianEDistOf g (polygonVertex γ N i) (polygonVertex γ N (i + 1)) ≤
      ENNReal.ofReal ((L : ℝ) / N) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  apply (hL _ _).trans
  apply le_trans (mul_le_mul' le_rfl (edist_proj_le ((i : ℝ) / N) (((i + 1 : ℤ) : ℝ) / N)))
  rw [edist_dist, Real.dist_eq]
  have hd : |(i : ℝ) / N - ((i + 1 : ℤ) : ℝ) / N| = 1 / (N : ℝ) := by
    push_cast
    rw [← sub_div]
    ring_nf
    rw [abs_neg, abs_inv, abs_of_pos hNR]
  rw [hd, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul L.coe_nonneg]
  apply le_of_eq
  congr 1
  ring

theorem exists_uniform_short_polygon_edges {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (g : SmoothRiemannianMetric I Q) (Γ : RegularFamily (I := I) (Q := Q) K)
    {radius : ℝ} (hradius : 0 < radius) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ n : ℕ, N ≤ n → ∀ k (i : ℤ),
      riemannianEDistOf g (polygonVertex (Γ k).1 n i)
        (polygonVertex (Γ k).1 n (i + 1)) < ENNReal.ofReal radius := by
  obtain ⟨L, hL, _⟩ := regularFamily_uniform_bounds g Γ
  obtain ⟨N, hN⟩ := exists_nat_gt ((L : ℝ) / radius)
  refine ⟨max 2 N, le_max_left _ _, fun n hn k i => ?_⟩
  have hn2 : 2 ≤ n := (le_max_left 2 N).trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast ((le_max_right 2 N).trans hn)
  apply (polygonVertex_edist_le_of_lipschitz g (Γ k).1 L (hL k) (by omega) i).trans_lt
  apply (ENNReal.ofReal_lt_ofReal_iff hradius).mpr
  apply (div_lt_iff₀ hnpos).mpr
  have h := (div_lt_iff₀ hradius).mp (hN.trans_le hNn)
  nlinarith

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families

end

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.Families

open Surgery.Topology Width

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {Q : Type*} [TopologicalSpace Q] [ChartedSpace H Q] [IsManifold I ∞ Q]

private theorem flatPolygon_edist_le_of_mem_Ico (g : SmoothRiemannianMetric I Q)
    (P : FlatteningProfile) (γ : Surgery.Topology.Circle → Q) (L : ℝ≥0)
    (hL : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (L : ℝ≥0∞) * edist x y)
    {N : ℕ} (hN : 0 < N) {i : ℤ} (hi : 0 ≤ i) (hiN : i < N) {x : ℝ}
    (hx : x ∈ Ico ((i : ℝ) / N) (((i : ℝ) + 1) / N))
    (hseg : IsShortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1))
      (shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1)))) :
    riemannianEDistOf g (flatPolygon g P N γ (x : Surgery.Topology.Circle))
      (γ (x : Surgery.Topology.Circle)) ≤ ENNReal.ofReal (2 * (L : ℝ) / N) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let p := polygonVertex γ N i
  let q := polygonVertex γ N (i + 1)
  let c := shortSegment g p q
  have hy : (N : ℝ) * x - (i : ℝ) ∈ Icc (0 : ℝ) 1 := by
    have h0 := (div_le_iff₀ hNR).mp hx.1
    have h1 := (lt_div_iff₀ hNR).mp hx.2
    constructor <;> nlinarith
  have hb := P.beta_mem_Icc hy
  have hcp : riemannianEDistOf g (c (P.beta ((N : ℝ) * x - i))) p ≤
      ENNReal.ofReal ((L : ℝ) / N) := by
    calc
      _ = ENNReal.ofReal |P.beta ((N : ℝ) * x - i) - 0| * riemannianEDistOf g p q := by
        have h := hseg.2.2.2.2 _ hb 0 (by norm_num)
        rw [hseg.2.2.1] at h
        exact h
      _ ≤ riemannianEDistOf g p q := by
        apply mul_le_of_le_one_left'
        apply ENNReal.ofReal_le_one.mpr
        simpa only [sub_zero, abs_of_nonneg hb.1] using hb.2
      _ ≤ _ := polygonVertex_edist_le_of_lipschitz g γ L hL hN i
  have hpx : riemannianEDistOf g p (γ (x : Surgery.Topology.Circle)) ≤
      ENNReal.ofReal ((L : ℝ) / N) := by
    apply (hL _ _).trans
    apply (mul_le_mul' le_rfl (edist_proj_le ((i : ℝ) / N) x)).trans
    rw [edist_dist, Real.dist_eq]
    have hdist : |(i : ℝ) / N - x| ≤ 1 / (N : ℝ) := by
      rw [abs_of_nonpos (sub_nonpos.mpr hx.1)]
      have h1 : x < (i : ℝ) / N + 1 / N := by
        simpa only [add_div] using hx.2
      linarith
    apply (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal hdist)).trans
    rw [← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul L.coe_nonneg]
    apply le_of_eq
    congr 1
    ring
  rw [flatPolygon_apply_of_mem_Ico g P N γ hN hi hiN hx]
  apply (DifferentialGeometry.riemannianEDistOf_triangle g _ p _).trans
  apply (add_le_add hcp hpx).trans
  rw [← ENNReal.ofReal_add (div_nonneg L.coe_nonneg hNR.le)
    (div_nonneg L.coe_nonneg hNR.le)]
  apply le_of_eq
  congr 1
  ring

theorem flatPolygon_edist_le_of_lipschitz (g : SmoothRiemannianMetric I Q)
    (P : FlatteningProfile) (γ : Surgery.Topology.Circle → Q) (L : ℝ≥0)
    (hL : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (L : ℝ≥0∞) * edist x y)
    {N : ℕ} (hN : 0 < N)
    (hseg : ∀ i : ℤ, 0 ≤ i → i < N → IsShortSegment g (polygonVertex γ N i)
      (polygonVertex γ N (i + 1))
      (shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1))))
    (z : Surgery.Topology.Circle) :
    riemannianEDistOf g (flatPolygon g P N γ z) (γ z) ≤
      ENNReal.ofReal (2 * (L : ℝ) / N) := by
  let x := AddCircle.equivIco (1 : ℝ) 0 z
  have hx : (x : ℝ) ∈ Ico (0 : ℝ) 1 := by simpa only [zero_add] using x.2
  have hz : ((x : ℝ) : Surgery.Topology.Circle) = z := AddCircle.coe_equivIco
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  let i : ℤ := ⌊(N : ℝ) * (x : ℝ)⌋
  have hi : 0 ≤ i := Int.floor_nonneg.mpr (mul_nonneg hNR.le hx.1)
  have hiN : i < N := Int.floor_lt.mpr (by exact_mod_cast (mul_lt_of_lt_one_right hNR hx.2))
  have hic : (x : ℝ) ∈ Ico ((i : ℝ) / N) (((i : ℝ) + 1) / N) := by
    refine ⟨(div_le_iff₀ hNR).mpr ?_, (lt_div_iff₀ hNR).mpr ?_⟩
    · simpa only [mul_comm] using Int.floor_le ((N : ℝ) * (x : ℝ))
    · simpa only [mul_comm] using Int.lt_floor_add_one ((N : ℝ) * (x : ℝ))
  rw [← hz]
  exact flatPolygon_edist_le_of_mem_Ico g P γ L hL hN hi hiN hic (hseg i hi hiN)


theorem flatPolygon_loopUniformDistance_le (g : SmoothRiemannianMetric I Q)
    (P : FlatteningProfile) (γ c : RegularLoop I Q) (L : ℝ≥0)
    (hL : ∀ x y, riemannianEDistOf g (γ x) (γ y) ≤ (L : ℝ≥0∞) * edist x y)
    {N : ℕ} (hN : 0 < N) (hc : ∀ z, c z = flatPolygon g P N γ z)
    (hseg : ∀ i : ℤ, 0 ≤ i → i < N → IsShortSegment g (polygonVertex γ N i)
      (polygonVertex γ N (i + 1))
      (shortSegment g (polygonVertex γ N i) (polygonVertex γ N (i + 1)))) :
    loopUniformDistance g c.toContinuousLoop γ.toContinuousLoop ≤ 2 * (L : ℝ) / N := by
  apply csSup_le (Set.range_nonempty _)
  rintro r ⟨z, rfl⟩
  have h := flatPolygon_edist_le_of_lipschitz g P γ L hL hN hseg z
  rw [← hc z] at h
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq
    (ENNReal.toReal_ofReal (by positivity))

end DifferentialGeometry.PDE.RicciFlow.Extinction.Families
