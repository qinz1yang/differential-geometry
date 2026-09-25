import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.InverseCapture
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.MetricAgreement
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Exhaustion
import DifferentialGeometry.Analysis.Calculus.Compactness.DiagonalSubsequence

noncomputable section
open Set Filter Manifold
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.CheegerGromovCompactness

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [I.Boundaryless] in
private theorem radial_balls_exhaust
    (L : PointedRiemannianManifold.{u, uE, uH} I) {rho : ℝ}
    (hradial : ∀ x : L.M, riemannianEDistOf L.metric L.basepoint x < ENNReal.ofReal rho)
    (r : ℕ → ℝ) (hr : Monotone r) (hrlim : Tendsto r atTop (𝓝 rho)) :
    ExhaustsByOpen (fun n => riemannianBallOf L.metric L.basepoint (r n)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact isOpen_lt (by
      unfold riemannianEDistOf
      exact Geometry.Riemannian.continuous_riemannianEDist L.metric L.basepoint) continuous_const
  · intro n x hx
    exact hx.trans_le (ENNReal.ofReal_le_ofReal (hr (Nat.le_succ n)))
  · intro K hK
    have hcover : K ⊆ ⋃ n, riemannianBallOf L.metric L.basepoint (r n) := by
      intro x _
      have hfinite := ne_top_of_lt (hradial x)
      have hx := ENNReal.toReal_lt_of_lt_ofReal (hradial x)
      obtain ⟨n, hn⟩ := (hrlim.eventually (eventually_gt_nhds hx)).exists
      exact mem_iUnion.mpr ⟨n, (ENNReal.lt_ofReal_iff_toReal_lt hfinite).mpr hn⟩
    have hopen : ∀ n, IsOpen (riemannianBallOf L.metric L.basepoint (r n)) := by
      intro n
      exact isOpen_lt (by unfold riemannianEDistOf; exact Geometry.Riemannian.continuous_riemannianEDist _ _) continuous_const
    have hmono : Monotone (fun n => riemannianBallOf L.metric L.basepoint (r n)) := by
      intro n m hnm x hx
      exact hx.trans_le (ENNReal.ofReal_le_ofReal (hr hnm))
    obtain ⟨n, hn⟩ := hK.elim_directed_cover _ hopen hcover hmono.directed_le
    exact ⟨n, fun m hm => hn.trans (hmono hm)⟩



omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
private theorem canonicalSourceData_derivNormSupOn_eq_of_same_map
    {X : PointedRiemannianSeq.{u, uE, uH} I}
    {L : PointedRiemannianManifold.{u, uE, uH} I} {f : ℕ → ℕ}
    (F G : PointedRiemannianConvergenceMaps X L f) (k : ℕ)
    (hmap : G.map k = F.map k)
    (U : TopologicalSpace.Opens L.M) (hUsrc : (U : Set L.M) ⊆ F.source k)
    (hUG : (U : Set L.M) ⊆ G.source k) (K : Set L.M) (hKU : K ⊆ U) (p : ℕ) :
    (CanonicalMetricCompactness.canonicalSourceData G k).derivNormSupOn K p =
      (CanonicalMetricCompactness.canonicalSourceData F k).derivNormSupOn K p := by
  let D := CanonicalMetricCompactness.canonicalSourceData F k
  let V : TopologicalSpace.Opens L.M := metricSourceOpenSubset F k
  let A := D.pullbackMetric.restrictOpenOfSubset hUsrc
  have hA : ∀ (x : U) (v w : TangentSpace I x),
      A.inner x v w = (X.obj (f k)).metric.inner (F.map k x)
        (mfderiv I I (F.map k) x v) (mfderiv I I (F.map k) x w) := by
    intro x v w
    have hpull := D.pullback_inner (⟨x, hUsrc x.property⟩ : V) v w
    have hval := (hasMFDerivAt_subtype_val (I := I) V (⟨x, hUsrc x.property⟩ : V)).mdifferentiableAt
    have hF := (F.partialDiffeomorph k).mdifferentiableAt (by simp) (hUsrc x.property)
    have hderiv (v : TangentSpace I x) :
        mfderiv I I (fun y : V => F.map k (y : L.M)) (⟨x, hUsrc x.property⟩ : V) v =
          mfderiv I I (F.map k) (x : L.M) v := by
      exact (mfderiv_comp_apply (⟨x, hUsrc x.property⟩ : V) hF hval v).trans
        (congrArg (mfderiv I I (F.map k) (x : L.M)) (mfderiv_subtype_val_apply V _ v))
    exact hpull.trans (congrArg₂ (fun a b => (X.obj (f k)).metric.inner (F.map k x) a b)
      (hderiv v) (hderiv w))
  rw [canonicalSourceData_derivNormSupOn_eq_of_open_pullback G k U hUG A K hKU p
    (fun x v w => by rw [hmap]; exact hA x v w),
    canonicalSourceData_derivNormSupOn_eq_of_open_pullback F k U hUsrc A K hKU p hA]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem PointedRiemannianConvergenceMaps.exists_restriction_with_uniform_metric_bounds
    {X : PointedRiemannianSeq.{u, uE, uH} I}
    {L : PointedRiemannianManifold.{u, uE, uH} I} {f : ℕ → ℕ}
    (F : PointedRiemannianConvergenceMaps X L f) (C : MetricConvergenceData F)
    (hcanonical : ∀ n, C.domain n = CanonicalMetricCompactness.canonicalSourceData F n)
    {rho : ℝ} (hrho : 0 < rho)
    (hradial : ∀ x : L.M, riemannianEDistOf L.metric L.basepoint x < ENNReal.ofReal rho)
    (hcompact : ∀ R : ℝ, 0 ≤ R → R < rho → IsCompact (riemannianClosedBallOf L.metric L.basepoint R)) :
    ∃ (phi : ℕ → ℕ), StrictMono phi ∧
      ∃ (r : ℕ → ℝ), (∀ n, 0 < r n ∧ r n < rho) ∧ Tendsto r atTop (𝓝 rho) ∧
      ∃ F' : PointedRiemannianConvergenceMaps X L (f ∘ phi),
        (∀ n, F'.map n = F.map (phi n)) ∧
        (∀ n, (F'.partialDiffeomorph n).symm.toFun = (F.partialDiffeomorph (phi n)).symm.toFun) ∧
        (∀ n, F'.source n ⊆ F.source (phi n)) ∧
        (∀ n, riemannianClosedBallOf (X.obj (f (phi n))).metric (X.obj (f (phi n))).basepoint (r n) ⊆ F'.target n) ∧
        (∀ eps : ℝ, 0 < eps → ∀ᶠ n in atTop, ∀ x ∈ F'.source n, ∀ v : TangentSpace I x,
          (1 - eps) * L.metric.inner x v v ≤
            (X.obj (f (phi n))).metric.inner (F'.map n x)
              (mfderiv I I (F'.map n) x v) (mfderiv I I (F'.map n) x v) ∧
          (X.obj (f (phi n))).metric.inner (F'.map n x)
              (mfderiv I I (F'.map n) x v) (mfderiv I I (F'.map n) x v) ≤
            (1 + eps) * L.metric.inner x v v) ∧
        ∃ C' : MetricConvergenceData F',
          ∀ n, C'.domain n = CanonicalMetricCompactness.canonicalSourceData F' n := by
  classical
  let r : ℕ → ℝ := fun n => rho - rho / ((n : ℝ) + 2)
  let R : ℕ → ℝ := fun n => (r n + rho) / 2
  let B : ℕ → ℝ := fun n => (r n + R n) / 2
  let factor : ℕ → ℝ := fun n => B n / r n
  let eps : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hr (n) : 0 < r n ∧ r n < rho := by
    constructor
    · apply sub_pos.mpr
      exact div_lt_self hrho (by linarith [Nat.cast_nonneg (α := ℝ) n])
    · exact sub_lt_self _ (by positivity)
  have hR (n) : r n < R n ∧ R n < rho := by dsimp [R]; constructor <;> linarith [(hr n).2]
  have hB (n) : r n < B n ∧ B n < R n := by dsimp [B]; constructor <;> linarith [(hR n).1]
  have hfactor (n) : 1 < factor n := (one_lt_div (hr n).1).mpr (hB n).1
  have hbuffer (n) : factor n * r n < R n := by
    dsimp [factor]
    rw [div_mul_cancel₀ _ (hr n).1.ne']
    exact (hB n).2
  have heps (n) : 0 < eps n := by dsimp [eps]; positivity
  have hrlim : Tendsto r atTop (𝓝 rho) := by
    have hd : Tendsto (fun n : ℕ => (n : ℝ) + 2) atTop atTop :=
      tendsto_atTop_mono (fun _ => le_add_of_nonneg_right (by norm_num)) tendsto_natCast_atTop_atTop
    simpa only [sub_zero] using tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hd)
  have hRlim : Tendsto R atTop (𝓝 rho) := by
    have hh := (hrlim.add (tendsto_const_nhds (x := rho))).div_const (2 : ℝ)
    convert hh using 1; congr 1; ring
  have hRmono : Monotone R := by
    intro n m hnm
    have hd : (n : ℝ) + 2 ≤ (m : ℝ) + 2 := by exact_mod_cast Nat.add_le_add_right hnm 2
    have hdiv := div_le_div_of_nonneg_left hrho.le (by positivity : (0 : ℝ) < (n : ℝ) + 2) hd
    dsimp [R, r]
    linarith
  have hexhaust := radial_balls_exhaust L hradial R hRmono hRlim
  have hconv (n) : metricSourceConvergesOn F (CanonicalMetricCompactness.canonicalSourceData F)
      (riemannianClosedBallOf L.metric L.basepoint (R n)) 0 := by
    have hc := C.converges _ (hcompact _ ((hr n).1.trans (hR n).1).le (hR n).2) 0
    have heq : C.domain = CanonicalMetricCompactness.canonicalSourceData F := funext hcanonical
    simpa only [heq] using hc
  have hready (n) : ∀ᶠ k in atTop,
      riemannianClosedBallOf L.metric L.basepoint (R n) ⊆ F.source k ∧
      (∀ x ∈ riemannianClosedBallOf L.metric L.basepoint (R n), ∀ v : TangentSpace I x,
        (1 - eps n) * L.metric.inner x v v ≤
          (X.obj (f k)).metric.inner (F.map k x) (mfderiv I I (F.map k) x v) (mfderiv I I (F.map k) x v) ∧
        (X.obj (f k)).metric.inner (F.map k x) (mfderiv I I (F.map k) x v) (mfderiv I I (F.map k) x v) ≤
          (1 + eps n) * L.metric.inner x v v) ∧
      ∀ y ∈ riemannianClosedBallOf (X.obj (f k)).metric (X.obj (f k)).basepoint (r n),
        y ∈ (F.partialDiffeomorph k).target ∧
        (F.partialDiffeomorph k).symm y ∈ riemannianClosedBallOf L.metric L.basepoint (B n) := by
    have hcpt := hcompact _ ((hr n).1.trans (hR n).1).le (hR n).2
    filter_upwards [pointed_metric_eventually_quadratic_bounds hcpt (hconv n) (heps n),
      pointed_metric_eventually_inverse_ball_capture L.basepoint (hr n).1.le (hfactor n) (hbuffer n) hcpt (hconv n)]
      with k hk hcap
    refine ⟨hk.1, hk.2, ?_⟩
    intro y hy
    have hpoint := hcap.2 y (by
      change y ∈ riemannianClosedBallOf (X.obj (f k)).metric ((F.partialDiffeomorph k) L.basepoint) (r n)
      rw [F.basepoint_map]; exact hy)
    refine ⟨hpoint.1, ?_⟩
    simpa only [factor, div_mul_cancel₀ _ (hr n).1.ne'] using hpoint.2.2.1
  choose N hN using fun n => eventually_atTop.mp (hready n)
  obtain ⟨phi, hphi, hphiN⟩ := exists_strictMono_ge N
  let Ψ := fun n => Topology.PartialDiffeomorph.restrict (F.partialDiffeomorph (phi n))
    (riemannianBallOf L.metric L.basepoint (R n)) (hexhaust.isOpen n)
  have hsource (n) : (Ψ n).source = riemannianBallOf L.metric L.basepoint (R n) := by
    apply inter_eq_right.mpr
    exact (fun x hx => (hN n (phi n) (hphiN n)).1 (show riemannianEDistOf L.metric L.basepoint x ≤ ENNReal.ofReal (R n) from le_of_lt hx))
  let F' : PointedRiemannianConvergenceMaps X L (f ∘ phi) := {
    partialDiffeomorph := Ψ
    source_exhausts := by simpa only [hsource] using hexhaust
    base_mem := fun n => by
      rw [hsource]
      change riemannianEDistOf L.metric L.basepoint L.basepoint < ENNReal.ofReal (R n)
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr ((hr n).1.trans (hR n).1)
    basepoint_map := fun n => F.basepoint_map (phi n) }
  have hmap (n) : F'.map n = F.map (phi n) := rfl
  have hcapture (n) : riemannianClosedBallOf (X.obj (f (phi n))).metric
      (X.obj (f (phi n))).basepoint (r n) ⊆ F'.target n := by
    intro y hy
    have hpoint := (hN n (phi n) (hphiN n)).2.2 y hy
    change y ∈ (F.partialDiffeomorph (phi n)).target ∩
      (F.partialDiffeomorph (phi n)).symm ⁻¹' riemannianBallOf L.metric L.basepoint (R n)
    exact ⟨hpoint.1, hpoint.2.trans_lt ((ENNReal.ofReal_lt_ofReal_iff
      ((hr n).1.trans (hR n).1)).mpr (hB n).2)⟩
  have hbounds : ∀ eta : ℝ, 0 < eta → ∀ᶠ n in atTop, ∀ x ∈ F'.source n, ∀ v : TangentSpace I x,
      (1 - eta) * L.metric.inner x v v ≤
        (X.obj (f (phi n))).metric.inner (F'.map n x) (mfderiv I I (F'.map n) x v) (mfderiv I I (F'.map n) x v) ∧
      (X.obj (f (phi n))).metric.inner (F'.map n x) (mfderiv I I (F'.map n) x v) (mfderiv I I (F'.map n) x v) ≤
        (1 + eta) * L.metric.inner x v v := by
    intro eta heta
    have hepslim : Tendsto eps atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
    filter_upwards [hepslim.eventually_lt_const heta] with n hn x hx v
    have hxR : x ∈ riemannianClosedBallOf L.metric L.basepoint (R n) := by
      change x ∈ (Ψ n).source at hx
      rw [hsource] at hx
      exact (show riemannianEDistOf L.metric L.basepoint x < ENNReal.ofReal (R n) from hx).le
    have hb := (hN n (phi n) (hphiN n)).2.1 x hxR v
    have hv := DifferentialGeometry.metric_inner_self_nonneg L.metric x v
    rw [hmap n]
    constructor <;> nlinarith [hb.1, hb.2]
  let hCseq := C.compSubseq phi hphi
  obtain ⟨C', hC', _⟩ := exists_metricConvergenceData_canonicalSourceData F' (by
    intro K hK p epsilon hepsilon
    obtain ⟨N, hN⟩ := hCseq.converges K hK p epsilon hepsilon
    obtain ⟨J, hJ⟩ := F'.source_exhausts.subset K hK
    refine ⟨max N J, fun n hn => ?_⟩
    have hsourceK := hJ n ((le_max_right N J).trans hn)
    have hold := hN n ((le_max_left N J).trans hn)
    let V : TopologicalSpace.Opens L.M := ⟨F'.source n, (F'.partialDiffeomorph n).open_source⟩
    have hsrcOld : (V : Set L.M) ⊆ (F.compSubseq phi hphi).source n := by
      exact inter_subset_left
    have hmapSame : F'.map n = (F.compSubseq phi hphi).map n := hmap n
    rw [canonicalSourceData_derivNormSupOn_eq_of_same_map (F.compSubseq phi hphi) F' n
      hmapSame V hsrcOld Subset.rfl K hsourceK p]
    have hcan : hCseq.domain n = CanonicalMetricCompactness.canonicalSourceData (F.compSubseq phi hphi) n := by
      change MetricSourceData.compSubseq phi hphi n (C.domain (phi n)) = _
      rw [hcanonical (phi n)]
      rfl
    simpa only [hcan] using hold.2)
  exact ⟨phi, hphi, r, hr, hrlim, F', hmap, fun _ => rfl, fun _ => inter_subset_left,
    hcapture, hbounds, C', hC'⟩

end DifferentialGeometry.CheegerGromovCompactness
