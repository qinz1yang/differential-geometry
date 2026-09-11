import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedMetricTimeControl


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance fixedReferenceTopology {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : TopologicalSpace F.M := F.topology
private local instance fixedReferenceCharted {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : ChartedSpace H F.M := F.charted
private local instance fixedReferenceSmooth {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I ∞ F.M := F.smooth
private local instance fixedReferenceC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance fixedReferenceT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space F.M := F.t2

private local instance fixedReferenceMetricTopology
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : TopologicalSpace P.M := P.topology
private local instance fixedReferenceMetricCharted
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : ChartedSpace H P.M := P.charted
private local instance fixedReferenceMetricSmooth
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) : IsManifold I ∞ P.M := P.smooth


theorem exists_pointed_fixed_reference_equivalence
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi)
    {kappa : ℝ} (hsource : ∀ i, KLim (I := I) kappa (X.term i))
    {a : ℝ} (ha : a ≤ 0) (K : Set L.M) (hK : IsCompact K)
    (C0 : MetricConvergenceData (I := I) (Phi.atTime (L := L) 0))
    (hc0 : ∀ i, C0.domain i = CanonicalMetricCompactness.canonicalSourceData
      (I := I) (Phi.atTime (L := L) 0) i)
    (Ca : MetricConvergenceData (I := I) (Phi.atTime (L := L) a))
    (hca : ∀ i, Ca.domain i = CanonicalMetricCompactness.canonicalSourceData
      (I := I) (Phi.atTime (L := L) a) i) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ᶠ i in atTop, K ⊆ Phi.source i ∧
      ∀ t ∈ Icc a 0, ∀ x ∈ K, ∀ v : TangentSpace I x,
        B⁻¹ * (L.S.base.metric a).inner x v v ≤
          ((X.term (phi i)).S.base.metric t).inner (Phi.map i x)
            (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x v) ∧
        ((X.term (phi i)).S.base.metric t).inner (Phi.map i x)
            (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x v) ≤
          B * (L.S.base.metric a).inner x v v := by
  let _ : NeZero (Module.finrank ℝ E) := ⟨by
    have hd := (hsource 0).dimension_ge_two
    omega⟩
  obtain ⟨C, hC, hscalar⟩ := exists_pointed_scalar_bound_on_compact C0 hc0 K hK
  have href (i : ℕ) : (Ca.domain i).referenceMetric = (Ca.domain i).limitMetric := by
    rw [hca i]
    rfl
  obtain ⟨N, hN⟩ := exists_pointed_full_ambient_quadratic_control Ca href K hK
    (1 / 2) (by norm_num)
  let H0 : ℝ := Real.exp (C * (-a))
  have hH0 : 0 < H0 := Real.exp_pos _
  have hH1 : 1 ≤ H0 := Real.one_le_exp (mul_nonneg hC.le (neg_nonneg.mpr ha))
  let B : ℝ := 2 * H0
  have hB : 1 ≤ B := by dsimp only [B]; linarith
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  refine ⟨B, hB, ?_⟩
  filter_upwards [hscalar, Filter.eventually_ge_atTop N] with i hi hNi
  refine ⟨hi.1, ?_⟩
  intro t ht x hx v
  have hQ := (hN i hNi).2 (x : L.M) hx v
  change |((X.term (phi i)).S.base.metric a).inner (Phi.map i (x : L.M))
      (mfderiv I I (Phi.map i) (x : L.M) v) (mfderiv I I (Phi.map i) (x : L.M) v) -
      (L.S.base.metric a).inner x v v| ≤ (1 / 2 : ℝ) * (L.S.base.metric a).inner x v v at hQ
  have hQlo := (abs_le.mp hQ).1
  have hQhi := (abs_le.mp hQ).2
  have hscalarBound : (X.term (phi i)).S.scalar 0 (Phi.map i x) ≤ C :=
    (le_abs_self _).trans (hi.2 x hx)
  have htimeUpper := (hsource (phi i)).metric_inner_le ht.1 ht.2
    (Phi.map i x) (mfderiv I I (Phi.map i) x v)
  have htimeLower := (hsource (phi i)).metric_inner_le ht.2 (le_refl (0 : ℝ))
    (Phi.map i x) (mfderiv I I (Phi.map i) x v)
  have hexp := (hsource (phi i)).metric_inner_le_exp_terminal_bound ha
    (Phi.map i x) hscalarBound (mfderiv I I (Phi.map i) x v)
  have hweighted := mul_le_mul_of_nonneg_left htimeLower hH0.le
  have hnonneg : 0 ≤ (L.S.base.metric a).inner x v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact ((L.S.base.metric a).pos x v hv).le
  have hmul : (L.S.base.metric a).inner x v v ≤
      B * ((X.term (phi i)).S.base.metric t).inner (Phi.map i x)
        (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x v) := by
    change _ ≤ (2 * H0) * _
    change _ ≤ H0 * _ at hexp
    nlinarith
  refine ⟨?_, ?_⟩
  · calc
      B⁻¹ * (L.S.base.metric a).inner x v v ≤
          B⁻¹ * (B * ((X.term (phi i)).S.base.metric t).inner (Phi.map i x)
            (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x v)) :=
        mul_le_mul_of_nonneg_left hmul (inv_nonneg.mpr hBpos.le)
      _ = _ := by rw [← mul_assoc, inv_mul_cancel₀ hBpos.ne', one_mul]
  · change _ ≤ (2 * H0) * _
    nlinarith

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
