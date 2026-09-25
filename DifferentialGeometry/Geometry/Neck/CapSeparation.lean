import DifferentialGeometry.Geometry.Neck.ProductCapExclusion
import DifferentialGeometry.Geometry.Neck.SpatialOverlap
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckRegionBall

noncomputable section
open Set Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M]
  {g : SmoothRiemannianMetric I3 M} {p : M} {eps : ℝ}

theorem SpatialNeck.set_subset_image_slab_of_intersects_unit_slab
    (nk : SpatialNeck g eps p) {K : Set M} {q C D : ℝ}
    (hq : 0 < q) (hC : 0 < C) (hD : 0 ≤ D)
    (heps : 4323 * eps ≤ 1 / 2)
    (hscalar : ∀ x ∈ K, metricScalarAt g x ≤ C * q)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K,
      riemannianEDistOf (DifferentialGeometry.scaleMetric q hq g) x y ≤ ENNReal.ofReal D)
    (hcontact : (K ∩ nk.map '' (univ ×ˢ Icc (-1 : ℝ) 1)).Nonempty)
    (hfit : 2 * (15 + Real.sqrt (2 * C) * D) < eps⁻¹) :
    metricScalarAt g p ≤ 2 * C * q ∧
      K ⊆ nk.map '' (univ ×ˢ
        Icc (-(2 * (15 + Real.sqrt (2 * C) * D))) (2 * (15 + Real.sqrt (2 * C) * D))) := by
  obtain ⟨x, hxK, hx⟩ := hcontact
  have hunit : (1 : ℝ) < eps⁻¹ := (one_lt_inv₀ nk.eps_pos).mpr
    (nk.eps_small.trans (by norm_num))
  have hwindow : x ∈ nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) := by
    apply image_mono _ hx
    intro z hz
    exact ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  have hlow := (nk.scalar_bounds_on_image_window hwindow).1
  have hupper := hscalar x hxK
  have hQ : metricScalarAt g p ≤ 2 * C * q := by
    nlinarith [nk.Q_pos]
  refine ⟨hQ, ?_⟩
  have hratio : 0 < metricScalarAt g p / q := div_pos nk.Q_pos hq
  have hratioC : metricScalarAt g p / q ≤ 2 * C := by
    exact (div_le_iff₀ hq).mpr (by nlinarith [hQ])
  let gq := DifferentialGeometry.scaleMetric q hq g
  let gQ := DifferentialGeometry.scaleMetric (metricScalarAt g p) nk.Q_pos g
  have hg : gQ = DifferentialGeometry.scaleMetric (metricScalarAt g p / q) hratio gq := by
    apply SmoothRiemannianMetric.ext_inner
    intro z v w
    simp only [gQ, gq, scaleMetric_inner]
    field_simp
  have hcontactdist : riemannianEDistOf gQ p x ≤ ENNReal.ofReal 14 := by
    have hb := nk.image_slab_subset_closedBall (by norm_num : (0 : ℝ) ≤ 1) hunit hx
    have hsqrt : Real.sqrt (1 + eps) ≤ 2 := by
      apply (Real.sqrt_le_iff).mpr
      constructor
      · norm_num
      · linarith [nk.eps_small]
    have hball : x ∈ riemannianClosedBallOf g p (14 / Real.sqrt (metricScalarAt g p)) :=
      hb.trans (ENNReal.ofReal_le_ofReal (by
        apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
        nlinarith))
    have hscale := riemannianClosedBallOf_scaleMetric (metricScalarAt g p) nk.Q_pos g p
      (14 / Real.sqrt (metricScalarAt g p))
    rw [mul_div_cancel₀ _ (Real.sqrt_pos.mpr nk.Q_pos).ne'] at hscale
    change x ∈ riemannianClosedBallOf gQ p 14
    rw [hscale]
    exact hball
  intro y hy
  have hxy : riemannianEDistOf gQ x y ≤ ENNReal.ofReal (Real.sqrt (2 * C) * D) := by
    rw [hg, edistOf_scale]
    calc
      _ ≤ ENNReal.ofReal (Real.sqrt (metricScalarAt g p / q)) * ENNReal.ofReal D :=
        mul_le_mul' le_rfl (hdiam x hxK y hy)
      _ ≤ ENNReal.ofReal (Real.sqrt (2 * C)) * ENNReal.ofReal D :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt hratioC)) le_rfl
      _ = _ := (ENNReal.ofReal_mul (Real.sqrt_nonneg _)).symm
  have hbound : riemannianEDistOf gQ p y ≤ ENNReal.ofReal (14 + Real.sqrt (2 * C) * D) := by
    have ht := (riemannianEDistOf_triangle gQ p x y).trans (add_le_add hcontactdist hxy)
    rwa [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 14)
      (mul_nonneg (Real.sqrt_nonneg _) hD)] at ht
  apply nk.ball_subset_closed_slab (by positivity) hfit
  change riemannianEDistOf gQ p y < ENNReal.ofReal (2 * (15 + Real.sqrt (2 * C) * D) / 2)
  apply hbound.trans_lt
  apply (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr
  linarith

private local instance : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩
private local instance : ConnectedSpace (Sphere 2) :=
  isConnected_iff_connectedSpace.mp
    (isConnected_sphere (by rw [← Module.finrank_eq_rank]; norm_num)
      (0 : ThreeSpace) (by norm_num : (0 : ℝ) ≤ 1))

theorem SpatialNeck.interior_eq_empty_of_frontier_neck_in_neck_chart
    (cut : SpatialNeck g eps p) {epsb : ℝ} {pb : M}
    (boundary : SpatialNeck g epsb pb) (hb : epsb ≤ 1 / 1000)
    {s : ℝ} (hs : s ∈ Ioo (-epsb⁻¹) epsb⁻¹)
    {K : Set M} (hK : IsCompact K)
    (hcapture : K ⊆ cut.cylindricalChart.target)
    (hfront : frontier K = range (fun z : Sphere 2 => boundary.map (z, s)))
    (hsmall : 720 * eps < (metricScalarAt g pb / metricScalarAt g p) / 16) :
    interior K = ∅ := by
  let h := DifferentialGeometry.scaleMetric 2 (by norm_num)
    (Geometry.roundMetric (E := ThreeSpace) (n := 2))
  have hprod : Geometry.Metric.roundCylinderMetric (E := ThreeSpace) (n := 2) =
      h.prod (euclideanMetric (E := ℝ)) := rfl
  let gQ := DifferentialGeometry.scaleMetric (metricScalarAt g p) cut.Q_pos g
  have heps : eps ≤ 1 / 4 := cut.eps_small.le.trans (by norm_num)
  have hratio : metricScalarAt gQ pb = metricScalarAt g pb / metricScalarAt g p := by
    rw [metricScalarAt_scaleMetric]
    ring
  apply (boundary.scaleMetric (metricScalarAt g p) cut.Q_pos).interior_eq_empty_of_frontier_in_product_chart
    hb hs h (by simp) cut.cylindricalChart.domain cut.cylindricalChart.target
      cut.cylindricalChart.chart hK hcapture hfront heps
      (by rw [hratio]; exact hsmall)
  intro y _ m hm
  have hh := cut.cylindricalChart_metricCloseOn
    (cut.cylindricalChart.chart.symm y) (mem_univ _) m hm
  rw [hprod] at hh
  exact hh

theorem SpatialNeck.disjoint_unit_slab_of_frontier_neck_of_subset
    (cut : SpatialNeck g eps p) {epsb : ℝ} {pb : M}
    (boundary : SpatialNeck g epsb pb) (hb : epsb ≤ 1 / 1000)
    {s : ℝ} (hs : s ∈ Ioo (-epsb⁻¹) epsb⁻¹)
    {L K : Set M} (hLK : L ⊆ K) (hL : IsCompact L) (hinterior : (interior L).Nonempty)
    (hfront : frontier L = range (fun z : Sphere 2 => boundary.map (z, s)))
    {q C D c : ℝ} (hq : 0 < q) (hC : 0 < C) (hD : 0 ≤ D)
    (heps : 4323 * eps ≤ 1 / 2)
    (hscalar : ∀ x ∈ K, metricScalarAt g x ≤ C * q)
    (hboundary : c * q ≤ metricScalarAt g pb)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K,
      riemannianEDistOf (DifferentialGeometry.scaleMetric q hq g) x y ≤ ENNReal.ofReal D)
    (hfit : 2 * (15 + Real.sqrt (2 * C) * D) < eps⁻¹)
    (hsmall : 23040 * C * eps < c) :
    Disjoint K (cut.map '' (univ ×ˢ Icc (-1 : ℝ) 1)) := by
  apply disjoint_iff_inter_eq_empty.mpr
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hQ, hcapture⟩ := cut.set_subset_image_slab_of_intersects_unit_slab
    hq hC hD heps hscalar hdiam ⟨x, hx⟩ hfit
  have htarget : K ⊆ cut.cylindricalChart.target := by
    apply hcapture.trans
    change cut.map '' _ ⊆ cut.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹)
    apply image_mono
    intro z hz
    exact ⟨hz.1, by constructor <;> linarith [hz.2.1, hz.2.2]⟩
  have hratio : 720 * eps < (metricScalarAt g pb / metricScalarAt g p) / 16 := by
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 16)).mpr
    apply (lt_div_iff₀ cut.Q_pos).mpr
    have hmul := mul_le_mul_of_nonneg_left hQ
      (by have := cut.eps_pos; positivity : 0 ≤ 720 * eps * 16)
    have hstrict := mul_lt_mul_of_pos_right hsmall hq
    nlinarith
  have hempty := cut.interior_eq_empty_of_frontier_neck_in_neck_chart boundary hb hs
    hL (hLK.trans htarget) hfront hratio
  exact Set.not_nonempty_empty (hempty ▸ hinterior)

omit [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M] in
theorem exists_neck_cap_separation_tolerance_of_subset
    {C D c : ℝ} (hC : 0 < C) (hD : 0 ≤ D) (hc : 0 < c) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ (M : Type*) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] (g : SmoothRiemannianMetric I3 M)
      (eps epsb : ℝ) (p pb : M), eps ≤ eta →
      ∀ (cut : SpatialNeck g eps p) (boundary : SpatialNeck g epsb pb),
        epsb ≤ 1 / 1000 → ∀ s ∈ Ioo (-epsb⁻¹) epsb⁻¹,
        ∀ (L K : Set M), L ⊆ K → IsCompact L → (interior L).Nonempty →
          frontier L = range (fun z : Sphere 2 => boundary.map (z, s)) →
          ∀ (q : ℝ) (hq : 0 < q),
            (∀ x ∈ K, metricScalarAt g x ≤ C * q) →
            c * q ≤ metricScalarAt g pb →
            (∀ x ∈ K, ∀ y ∈ K,
              riemannianEDistOf (DifferentialGeometry.scaleMetric q hq g) x y ≤ ENNReal.ofReal D) →
            Disjoint K (cut.map '' (univ ×ˢ Icc (-1 : ℝ) 1)) := by
  let R := 2 * (15 + Real.sqrt (2 * C) * D)
  have hR : 0 < R := by dsimp [R]; positivity
  let eta := min (1 / 10000) (min ((2 * R)⁻¹) (c / (46080 * C)))
  have heta : 0 < eta := by dsimp [eta]; positivity
  refine ⟨eta, heta, ?_⟩
  intro M _ _ _ _ g eps epsb p pb heps cut boundary hb s hs L K hLK hL hLi hfront q hq hscalar hboundary hdiam
  have hepsbound : eps ≤ 1 / 10000 := heps.trans (min_le_left _ _)
  have hepsR : eps ≤ (2 * R)⁻¹ := heps.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hepsc : eps ≤ c / (46080 * C) := heps.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hfit : R < eps⁻¹ := by
    have hh := inv_anti₀ cut.eps_pos hepsR
    rw [inv_inv] at hh
    linarith
  have hsmall : 23040 * C * eps < c := by
    have hh := (le_div_iff₀ (by positivity : 0 < 46080 * C)).mp hepsc
    nlinarith
  exact cut.disjoint_unit_slab_of_frontier_neck_of_subset boundary hb hs hLK hL hLi hfront
    hq hC hD (by linarith) hscalar hboundary hdiam hfit hsmall

theorem SpatialNeck.disjoint_unit_slab_of_frontier_neck
    (cut : SpatialNeck g eps p) {epsb : ℝ} {pb : M}
    (boundary : SpatialNeck g epsb pb) (hb : epsb ≤ 1 / 1000)
    {s : ℝ} (hs : s ∈ Ioo (-epsb⁻¹) epsb⁻¹)
    {K : Set M} (hK : IsCompact K) (hinterior : (interior K).Nonempty)
    (hfront : frontier K = range (fun z : Sphere 2 => boundary.map (z, s)))
    {q C D c : ℝ} (hq : 0 < q) (hC : 0 < C) (hD : 0 ≤ D)
    (heps : 4323 * eps ≤ 1 / 2)
    (hscalar : ∀ x ∈ K, metricScalarAt g x ≤ C * q)
    (hboundary : c * q ≤ metricScalarAt g pb)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K,
      riemannianEDistOf (DifferentialGeometry.scaleMetric q hq g) x y ≤ ENNReal.ofReal D)
    (hfit : 2 * (15 + Real.sqrt (2 * C) * D) < eps⁻¹)
    (hsmall : 23040 * C * eps < c) :
    Disjoint K (cut.map '' (univ ×ˢ Icc (-1 : ℝ) 1)) := by
  exact cut.disjoint_unit_slab_of_frontier_neck_of_subset boundary hb hs Subset.rfl hK hinterior hfront
    hq hC hD heps hscalar hboundary hdiam hfit hsmall


omit [TopologicalSpace M] [ChartedSpace ThreeSpace M] [IsManifold I3 ∞ M] [T2Space M] in
theorem exists_neck_cap_separation_tolerance
    {C D c : ℝ} (hC : 0 < C) (hD : 0 ≤ D) (hc : 0 < c) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ (M : Type*) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] (g : SmoothRiemannianMetric I3 M)
      (eps epsb : ℝ) (p pb : M), eps ≤ eta →
      ∀ (cut : SpatialNeck g eps p) (boundary : SpatialNeck g epsb pb),
        epsb ≤ 1 / 1000 → ∀ s ∈ Ioo (-epsb⁻¹) epsb⁻¹,
        ∀ (K : Set M), IsCompact K → (interior K).Nonempty →
          frontier K = range (fun z : Sphere 2 => boundary.map (z, s)) →
          ∀ (q : ℝ) (hq : 0 < q),
            (∀ x ∈ K, metricScalarAt g x ≤ C * q) →
            c * q ≤ metricScalarAt g pb →
            (∀ x ∈ K, ∀ y ∈ K,
              riemannianEDistOf (DifferentialGeometry.scaleMetric q hq g) x y ≤ ENNReal.ofReal D) →
            Disjoint K (cut.map '' (univ ×ˢ Icc (-1 : ℝ) 1)) := by
  obtain ⟨eta, heta, hsep⟩ := exists_neck_cap_separation_tolerance_of_subset hC hD hc
  refine ⟨eta, heta, ?_⟩
  intro M _ _ _ _ g eps epsb p pb heps cut boundary hb s hs K hK hKi hfront q hq hscalar hboundary hdiam
  exact hsep M g eps epsb p pb heps cut boundary hb s hs K K Subset.rfl hK hKi hfront q hq
    hscalar hboundary hdiam

theorem SpatialNeck.disjoint_unit_slab_of_ricci_lower_bound
    (nk : SpatialNeck g eps p) {K : Set M} {q C D κ : ℝ} {z : M}
    (hq : 0 < q) (hC : 0 < C) (hD : 0 ≤ D)
    (heps : 4323 * eps ≤ 1 / 2)
    (hscalar : ∀ x ∈ K, metricScalarAt g x ≤ C * q)
    (hdiam : ∀ x ∈ K, ∀ y ∈ K,
      riemannianEDistOf (DifferentialGeometry.scaleMetric q hq g) x y ≤ ENNReal.ofReal D)
    (hz : z ∈ K)
    (hRic : ∀ v : TangentSpace I3 z, κ * q * g.inner z v v ≤ ricciTensor g z v v)
    (hfit : 2 * (15 + Real.sqrt (2 * C) * D) < eps⁻¹)
    (hκ : 11544 * C * eps < κ) :
    Disjoint K (nk.map '' (univ ×ˢ Icc (-1 : ℝ) 1)) := by
  apply Set.disjoint_iff_inter_eq_empty.mpr
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨hQ, hcapture⟩ := nk.set_subset_image_slab_of_intersects_unit_slab hq hC hD
    heps hscalar hdiam ⟨x, hx⟩ hfit
  have hzwindow : z ∈ nk.map '' (univ ×ˢ Ioo (-eps⁻¹) eps⁻¹) := by
    apply image_mono _ (hcapture hz)
    intro y hy
    exact ⟨hy.1, by constructor <;> linarith [hy.2.1, hy.2.2]⟩
  apply nk.not_mem_image_window_of_ricci_lower_bound hRic _ hzwindow
  have hmul := mul_le_mul_of_nonneg_right hQ nk.eps_pos.le
  have hstrict := mul_lt_mul_of_pos_right hκ hq
  nlinarith

theorem exists_neck_separation_tolerance_of_ricci_lower_bound
    {C D κ : ℝ} (hC : 0 < C) (hD : 0 ≤ D) (hκ : 0 < κ) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ (M : Type*) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] (g : SmoothRiemannianMetric I3 M)
        (eps : ℝ) (p : M), eps ≤ eta → ∀ (cut : SpatialNeck g eps p)
        (K : Set M) (q : ℝ) (hq : 0 < q),
        (∀ x ∈ K, metricScalarAt g x ≤ C * q) →
        (∀ x ∈ K, ∀ y ∈ K,
          riemannianEDistOf (DifferentialGeometry.scaleMetric q hq g) x y ≤ ENNReal.ofReal D) →
        ∀ z ∈ K, (∀ v : TangentSpace I3 z,
          κ * q * g.inner z v v ≤ ricciTensor g z v v) →
        Disjoint K (cut.map '' (univ ×ˢ Icc (-1 : ℝ) 1)) := by
  let R := 2 * (15 + Real.sqrt (2 * C) * D)
  have hR : 0 < R := by dsimp [R]; positivity
  let eta := min (1 / 10000) (min ((2 * R)⁻¹) (κ / (23088 * C)))
  have heta : 0 < eta := by dsimp [eta]; positivity
  refine ⟨eta, heta, ?_⟩
  intro M _ _ _ _ g eps p heps cut K q hq hscalar hdiam z hz hRic
  have hepsbound : eps ≤ 1 / 10000 := heps.trans (min_le_left _ _)
  have hepsR : eps ≤ (2 * R)⁻¹ := heps.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hepsc : eps ≤ κ / (23088 * C) := heps.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hfit : R < eps⁻¹ := by
    have hh := inv_anti₀ cut.eps_pos hepsR
    rw [inv_inv] at hh
    linarith
  have hsmall : 11544 * C * eps < κ := by
    have hh := (le_div_iff₀ (by positivity : 0 < 23088 * C)).mp hepsc
    nlinarith
  exact cut.disjoint_unit_slab_of_ricci_lower_bound hq hC hD (by linarith)
    hscalar hdiam hz hRic hfit hsmall

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
