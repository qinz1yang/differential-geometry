import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedMetricTimeControl
import DifferentialGeometry.Analysis.Calculus.MapConvergence.WeightedCompactTime


set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

private local instance uniformTimeTopology {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : TopologicalSpace F.M := F.topology
private local instance uniformTimeCharted {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : ChartedSpace H F.M := F.charted
private local instance uniformTimeSmooth {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I ∞ F.M := F.smooth
private local instance uniformTimeC1 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance uniformTimeT2 {D : RealTimeInterval}
    (F : PointedFlowData.{u, uE, uH} (I := I) D) : T2Space F.M := F.t2

private local instance uniformTimeMetricTopology
    (F : PointedRiemannianManifold.{u, uE, uH} (I := I)) : TopologicalSpace F.M := F.topology
private local instance uniformTimeMetricCharted
    (F : PointedRiemannianManifold.{u, uE, uH} (I := I)) : ChartedSpace H F.M := F.charted
private local instance uniformTimeMetricSmooth
    (F : PointedRiemannianManifold.{u, uE, uH} (I := I)) : IsManifold I ∞ F.M := F.smooth
private local instance uniformTimeMetricC1
    (F : PointedRiemannianManifold.{u, uE, uH} (I := I)) : IsManifold I 1 F.M :=
  IsManifold.of_le (n := ∞) (by decide)
private local instance uniformTimeMetricT2
    (F : PointedRiemannianManifold.{u, uE, uH} (I := I)) : T2Space F.M := F.t2


theorem pointed_metric_quadratic_uniform_on_closed_time
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D} {phi : ℕ → ℕ}
    (Phi : PointedCGHMaps (I := I) X (L.atTime (I := I) 0) phi)
    {kappa : ℝ} (hsource : ∀ i, KLim (I := I) kappa (X.term i))
    {a : ℝ} (ha : a ≤ 0) (K : Set L.M) (hK : IsCompact K)
    (hconv : ∀ t ∈ Icc a 0,
      ∃ C : MetricConvergenceData (I := I) (Phi.atTime (L := L) t),
        ∀ k, C.domain k = CanonicalMetricCompactness.canonicalSourceData
          (I := I) (Phi.atTime (L := L) t) k) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, K ⊆ Phi.source i ∧
      ∀ t ∈ Icc a 0, ∀ x ∈ K, ∀ v : TangentSpace I x,
        |((X.term (phi i)).S.base.metric t).inner (Phi.map i x)
            (mfderiv I I (Phi.map i) x v) (mfderiv I I (Phi.map i) x v) -
          (L.S.base.metric t).inner x v v| ≤ ε * (L.S.base.metric 0).inner x v v := by
  classical
  let _ : NeZero (Module.finrank ℝ E) := ⟨by
    have hn := (hsource 0).dimension_ge_two
    omega⟩
  have hzero : (0 : ℝ) ∈ Icc a 0 := ⟨ha, le_rfl⟩
  obtain ⟨C0, hC0⟩ := hconv 0 hzero
  obtain ⟨B, hB, hmod⟩ :=
    exists_pointed_metric_time_modulus_on_compact Phi hsource C0 hC0 K hK a
  let Z := Σ x : K, TangentSpace I (x : L.M)
  let w : Z → ℝ := fun z => (L.S.base.metric 0).inner (z.1 : L.M) z.2 z.2
  let Q : ℕ → ℝ → Z → ℝ := fun i t z =>
    ((X.term (phi i)).S.base.metric t).inner (Phi.map i (z.1 : L.M))
      (mfderiv I I (Phi.map i) (z.1 : L.M) z.2) (mfderiv I I (Phi.map i) (z.1 : L.M) z.2)
  let Q0 : ℝ → Z → ℝ := fun t z => (L.S.base.metric t).inner (z.1 : L.M) z.2 z.2
  have hw (z : Z) : 0 ≤ w z := by
    by_cases hz : z.2 = 0
    · simp [w, hz]
    · exact ((L.S.base.metric 0).pos (z.1 : L.M) z.2 hz).le
  have hLip : ∀ᶠ i in atTop, ∀ s ∈ Icc a 0, ∀ t ∈ Icc a 0, ∀ z : Z,
      |Q i t z - Q i s z| ≤ B * w z * |t - s| :=
    hmod.mono fun i hi s hs t ht z => hi.2 s hs t ht (z.1 : L.M) z.1.property z.2
  have hrelative (t : ℝ) (ht : t ∈ Icc a 0) (ε : ℝ) (hε : 0 < ε) :
      ∃ N : ℕ, ∀ i ≥ N, ∀ z : Z, |Q i t z - Q0 t z| ≤ ε * Q0 t z := by
    obtain ⟨Ct, hCt⟩ := hconv t ht
    have href (k : ℕ) : (Ct.domain k).referenceMetric = (Ct.domain k).limitMetric := by
      rw [hCt k]
      rfl
    obtain ⟨N, hN⟩ := exists_pointed_full_ambient_quadratic_control Ct href K hK ε hε
    exact ⟨N, fun i hi z => (hN i hi).2 (z.1 : L.M) z.1.property z.2⟩
  obtain ⟨N0, hN0⟩ := hrelative 0 hzero 1 zero_lt_one
  have hbase : ∀ᶠ i in atTop, ∀ z : Z, |Q i 0 z - w z| ≤ w z := by
    filter_upwards [Filter.eventually_ge_atTop N0] with i hi
    intro z
    simpa only [one_mul] using hN0 i hi z
  let H0 : ℝ := 2 * (2 + B * (-a))
  have hamin : 0 ≤ -a := neg_nonneg.mpr ha
  have hH0 : 0 < H0 := by dsimp only [H0]; positivity
  have hlimit (t : ℝ) (ht : t ∈ Icc a 0) (z : Z) : Q0 t z ≤ H0 * w z := by
    obtain ⟨Nt, hNt⟩ := hrelative t ht (1 / 2) (by norm_num)
    obtain ⟨i, hi, hi0, hit⟩ :=
      (hLip.and (hbase.and (Filter.eventually_ge_atTop Nt))).exists
    have hterminal := (abs_le.mp (hi0 z)).2
    have htime := (abs_le.mp (hi 0 hzero t ht z)).2
    have htlength : |t - 0| ≤ -a := by
      rw [sub_zero, abs_of_nonpos ht.2]
      linarith [ht.1]
    have htime' := htime.trans
      (mul_le_mul_of_nonneg_left htlength (mul_nonneg hB.le (hw z)))
    have hlower := (abs_le.mp (hNt i hit z)).1
    dsimp only [H0]
    nlinarith
  have hslice (t : ℝ) (ht : t ∈ Icc a 0) (ε : ℝ) (hε : 0 < ε) :
      ∀ᶠ i in atTop, ∀ z : Z, |Q i t z - Q0 t z| ≤ ε * w z := by
    obtain ⟨N, hN⟩ := hrelative t ht (ε / H0) (div_pos hε hH0)
    filter_upwards [Filter.eventually_ge_atTop N] with i hi
    intro z
    calc
      |Q i t z - Q0 t z| ≤ (ε / H0) * Q0 t z := hN i hi z
      _ ≤ (ε / H0) * (H0 * w z) :=
        mul_le_mul_of_nonneg_left (hlimit t ht z) (div_pos hε hH0).le
      _ = ε * w z := by field_simp
  intro ε hε
  have huniform := IsCompact.eventually_uniform_of_weighted_lipschitz
    Q Q0 w hw isCompact_Icc hB.le hLip hslice ε hε
  filter_upwards [huniform, hmod] with i hi hmi
  exact ⟨hmi.1, fun t ht x hx v => hi t ht ⟨⟨x, hx⟩, v⟩⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
