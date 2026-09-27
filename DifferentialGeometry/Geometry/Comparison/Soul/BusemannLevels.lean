import DifferentialGeometry.Geometry.Comparison.Soul.SoulShaving
import Mathlib.Analysis.Convex.Slope

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.HopfRinow
open DifferentialGeometry.Geometry.Comparison.Toponogov

namespace DifferentialGeometry.Geometry.Topology

section Metric

variable {X : Type*} [MetricSpace X]

private def rayValues (p x : X) : Set ℝ :=
  {a | a = 0 ∨ ∃ c : ℝ≥0 → X, Isometry c ∧ c 0 = p ∧ busemann c x = a}

private theorem rayValues_nonempty (p x : X) : (rayValues p x).Nonempty := ⟨0, Or.inl rfl⟩

private theorem rayValues_le_dist (p x : X) : ∀ a ∈ rayValues p x, a ≤ dist x p := by
  rintro a (rfl | ⟨c, hc, hc0, rfl⟩)
  · exact dist_nonneg
  · simpa only [hc0] using (le_abs_self (busemann c x)).trans (abs_busemann_le hc x)

private theorem rayValues_bddAbove (p x : X) : BddAbove (rayValues p x) :=
  ⟨dist x p, rayValues_le_dist p x⟩

def rayExhaustion (p x : X) : ℝ := sSup (rayValues p x)


theorem rayExhaustion_nonneg (p x : X) : 0 ≤ rayExhaustion p x :=
  le_csSup (rayValues_bddAbove p x) (Or.inl rfl)


theorem rayExhaustion_le_dist (p x : X) : rayExhaustion p x ≤ dist x p :=
  csSup_le (rayValues_nonempty p x) (rayValues_le_dist p x)


theorem busemann_le_rayExhaustion {c : ℝ≥0 → X} (hc : Isometry c) {p : X} (hc0 : c 0 = p)
    (x : X) : busemann c x ≤ rayExhaustion p x :=
  le_csSup (rayValues_bddAbove p x) (Or.inr ⟨c, hc, hc0, rfl⟩)


@[simp] theorem rayExhaustion_self (p : X) : rayExhaustion p p = 0 :=
  le_antisymm (by simpa only [dist_self] using rayExhaustion_le_dist p p) (rayExhaustion_nonneg p p)


theorem rayExhaustion_le_iff {p x : X} {t : ℝ} (ht : 0 ≤ t) :
    rayExhaustion p x ≤ t ↔ x ∈ rayBusemannSublevel p t := by
  constructor
  · intro hx c hc hc0
    exact (busemann_le_rayExhaustion hc hc0 x).trans hx
  · intro hx
    apply csSup_le (rayValues_nonempty p x)
    rintro a (rfl | ⟨c, hc, hc0, rfl⟩)
    · exact ht
    · exact hx c hc hc0

private theorem rayExhaustion_le_add_dist (p x y : X) :
    rayExhaustion p x ≤ rayExhaustion p y + dist x y := by
  apply csSup_le (rayValues_nonempty p x)
  rintro a (rfl | ⟨c, hc, hc0, rfl⟩)
  · exact add_nonneg (rayExhaustion_nonneg p y) dist_nonneg
  · have hdist := (lipschitzWith_busemann hc).dist_le_mul x y
    rw [Real.dist_eq, NNReal.coe_one, one_mul] at hdist
    have hsub := (le_abs_self (busemann c x - busemann c y)).trans hdist
    have hbound := busemann_le_rayExhaustion hc hc0 y
    linarith only [hsub, hbound]

theorem lipschitzWith_rayExhaustion (p : X) : LipschitzWith 1 (rayExhaustion p) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  simp only [Real.dist_eq, NNReal.coe_one, one_mul, abs_le]
  constructor
  · have h := rayExhaustion_le_add_dist p y x
    rw [dist_comm y x] at h
    linarith
  · exact sub_le_iff_le_add.2 (by simpa only [add_comm] using rayExhaustion_le_add_dist p x y)

end Metric

private theorem convex_strictly_above_of_one_lt {f : ℝ → ℝ}
    (hf : ConvexOn ℝ univ f) (hzero : f 0 = 0) (hone : 0 < f 1)
    {t : ℝ} (ht : 1 < t) : f 1 < f t := by
  have htpos : 0 < t := zero_lt_one.trans ht
  have hs := hf.secant_mono (mem_univ 0) (mem_univ 1) (mem_univ t)
    one_ne_zero htpos.ne' ht.le
  simp only [hzero, sub_zero, div_one] at hs
  have hmul : f 1 * t ≤ f t := (le_div_iff₀ htpos).1 hs
  exact (lt_mul_of_one_lt_right hone ht).trans_le hmul

section Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [ConnectedSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem convexOn_rayExhaustion_intrinsicGeodesic
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ z : M, metricRm04At (I := I) g z ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (p q : M) (v : TangentSpace I q) {D : Set ℝ} (hD : Convex ℝ D) :
    ConvexOn ℝ D (fun t => rayExhaustion p (intrinsicGeodesic (I := I) g hEnorm q v t)) := by
  refine ⟨hD, ?_⟩
  intro x hx y hy a b ha hb hab
  apply csSup_le (rayValues_nonempty p _)
  rintro z (rfl | ⟨c, hc, hc0, rfl⟩)
  · exact add_nonneg (smul_nonneg ha (rayExhaustion_nonneg p _))
      (smul_nonneg hb (rayExhaustion_nonneg p _))
  · exact ((convexOn_busemann_intrinsicGeodesic g hEnorm hsec hc q v hD).2 hx hy ha hb hab).trans
      (add_le_add (smul_le_smul_of_nonneg_left (busemann_le_rayExhaustion hc hc0 _) ha)
        (smul_le_smul_of_nonneg_left (busemann_le_rayExhaustion hc hc0 _) hb))

variable [T2Space (TangentBundle I M)]

theorem mem_relBoundary_rayExhaustion_level
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ z : M, metricRm04At (I := I) g z ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (p r : M) (hr : 0 < rayExhaustion p r) :
    r ∈ relBoundary I (rayBusemannSublevel p (rayExhaustion p r)) := by
  let C := rayBusemannSublevel p (rayExhaustion p r)
  have hconv : IsTotallyConvex (I := I) g C := isTotallyConvex_rayBusemannSublevel g hEnorm hsec p _
  refine ⟨(rayExhaustion_le_iff hr.le).1 le_rfl, ?_⟩
  intro hrN
  have hslice : IsEmbeddedSlice I (Module.finrank ℝ E) (maxSliceLocus I C) := by
    have h := isEmbeddedSlice_maxSliceLocus hEnorm hconv
    rwa [maxSliceDim_rayBusemannSublevel (I := I) p hr] at h
  have hopen : IsOpen (maxSliceLocus I C) := hslice.isOpen
  let γ := minJoin (I := I) g hEnorm p r
  have hcont : Continuous γ := minJoin_cont g hEnorm p r
  have hγone : γ 1 = r := minJoin_one g hEnorm p r
  have hnear : ∀ᶠ t in 𝓝 (1 : ℝ), γ t ∈ maxSliceLocus I C := by
    apply hcont.continuousAt
    rw [hγone]
    exact hopen.mem_nhds hrN
  have hnear' : ∀ᶠ t : ℝ in 𝓝[>] (1 : ℝ), γ t ∈ maxSliceLocus I C :=
    hnear.filter_mono nhdsWithin_le_nhds
  obtain ⟨t, htN, ht⟩ := (hnear'.and self_mem_nhdsWithin).exists
  have hgrowth : rayExhaustion p (γ 1) < rayExhaustion p (γ t) :=
    convex_strictly_above_of_one_lt
      (convexOn_rayExhaustion_intrinsicGeodesic g hEnorm hsec p p
        (minimizingVec g hEnorm p r) convex_univ)
      (by simp) (show 0 < rayExhaustion p (γ 1) by rwa [hγone]) ht
  rw [hγone] at hgrowth
  exact (not_le_of_gt hgrowth) ((rayExhaustion_le_iff hr.le).2 (maxSliceLocus_subset htN))

theorem rayExhaustion_separator
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm (I := I) g)
    (hsec : ∀ z : M, metricRm04At (I := I) g z ∈
      tensor04SectionalNonnegativeCone (I := I) (M := M))
    (p r : M) (hr : r ∉ rayBusemannSublevel p 1) :
    let C := rayBusemannSublevel p (rayExhaustion p r)
    IsCompact C ∧ IsTotallyConvex (I := I) g C ∧ r ∈ relBoundary I C ∧
      rayBusemannSublevel p 1 ⊆ maxSliceLocus I C := by
  have hlevel : 1 < rayExhaustion p r := lt_of_not_ge fun h => hr ((rayExhaustion_le_iff zero_le_one).1 h)
  have hpos := zero_lt_one.trans hlevel
  refine ⟨isCompact_rayBusemannSublevel g hEnorm hsec p _,
    isTotallyConvex_rayBusemannSublevel g hEnorm hsec p _,
    mem_relBoundary_rayExhaustion_level g hEnorm hsec p r hpos, ?_⟩
  intro x hx
  refine ⟨interior (rayBusemannSublevel p (rayExhaustion p r)),
    rayBusemannSublevel_subset_interior p hlevel hx, interior_subset, ?_⟩
  rw [maxSliceDim_rayBusemannSublevel (I := I) p hpos]
  exact IsEmbeddedSlice.of_isOpen isOpen_interior

end Geometry

end DifferentialGeometry.Geometry.Topology
