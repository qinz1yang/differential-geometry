import DifferentialGeometry.Geometry.Metric.Comparison.Inverse

noncomputable section

open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PartialDiffeomorph

universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M N : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem edist_bounds_of_metric_bounds_on_buffered_ball
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric I N)
    (Φ : PartialDiffeomorph I I M N ∞) (o : M)
    {r R L : ℝ} (hr : 0 ≤ r) (hL : 1 ≤ L) (hbuffer : 3 * L ^ 2 * r < R)
    (hcompact : IsCompact (riemannianClosedBallOf g o R))
    (hsource : riemannianClosedBallOf g o R ⊆ Φ.source)
    (hquad : ∀ x ∈ riemannianClosedBallOf g o R, ∀ v : TangentSpace I x,
      g.inner x v v ≤ L ^ 2 * h.inner (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x v) ∧
      h.inner (Φ x) (mfderiv I I Φ x v) (mfderiv I I Φ x v) ≤ L ^ 2 * g.inner x v v)
    {x y : M} (hx : x ∈ riemannianClosedBallOf g o r)
    (hy : y ∈ riemannianClosedBallOf g o r) :
    riemannianEDistOf h (Φ x) (Φ y) ≤ ENNReal.ofReal L * riemannianEDistOf g x y ∧
    riemannianEDistOf g x y ≤ ENNReal.ofReal L * riemannianEDistOf h (Φ x) (Φ y) := by
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hLsq : 1 ≤ L ^ 2 := by nlinarith
  have hrR : r < R := by nlinarith [mul_nonneg (sub_nonneg.mpr hLsq) hr]
  have hRpos : 0 < R := hr.trans_lt hrR
  have hupper := fun x hx v => (hquad x hx v).2
  have hlower := fun x hx v => (hquad x hx v).1
  have hbase (z : M) (hz : z ∈ riemannianClosedBallOf g o r) :
      Φ z ∈ riemannianClosedBallOf h (Φ o) (L * r) := by
    have hzR : riemannianEDistOf g o z < ENNReal.ofReal R :=
      hz.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hRpos).mpr hrR)
    have hd := PDE.RicciFlow.Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_ball
      g h Φ o z hRpos hLpos hsource hupper hzR
    change riemannianEDistOf h (Φ o) (Φ z) ≤ ENNReal.ofReal (L * r)
    rw [ENNReal.ofReal_mul hLpos.le]
    exact hd.trans (mul_le_mul' le_rfl hz)
  have hmargin : 3 * (L * r) < R / L := by
    apply (lt_div_iff₀ hLpos).mpr
    nlinarith
  obtain ⟨s, hslo, hshi⟩ := exists_between hmargin
  constructor
  · exact PDE.RicciFlow.Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_buffered_ball
      g h Φ o x y hr (by nlinarith [mul_nonneg (sub_nonneg.mpr hLsq) hr])
      hLpos hsource hupper hx hy
  · have hd := PDE.RicciFlow.Perelman.KappaSolutions.edistOf_symm_pair_le_of_metric_lower_on_compact_ball
      g h Φ o hRpos hLpos (mul_nonneg hLpos.le hr) hslo hshi hcompact hsource hlower
      (Φ x) (Φ y) (hbase x hx) (hbase y hy)
    have hxS := hsource ((riemannianClosedBallOf_mono g o hrR.le) hx)
    have hyS := hsource ((riemannianClosedBallOf_mono g o hrR.le) hy)
    have hleftx : Φ.symm (Φ x) = x := Φ.left_inv' hxS
    have hlefty : Φ.symm (Φ y) = y := Φ.left_inv' hyS
    rw [hleftx, hlefty] at hd
    exact hd

end DifferentialGeometry.PartialDiffeomorph
