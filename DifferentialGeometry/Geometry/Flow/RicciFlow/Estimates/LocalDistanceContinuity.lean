import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.CurvatureMetricComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.CurvatureContinuity
import DifferentialGeometry.Geometry.Metric.Pullback.LocalDistance

set_option autoImplicit false
noncomputable section
open Set Filter TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {D : RealTimeInterval}

omit [I.Boundaryless] in
private theorem min_restrictOpen_edist_eq
    (g : SmoothRiemannianMetric I M) (V : Opens M) (p x : V) (R : ℝ)
    (hball : riemannianBallOf g p.val R ⊆ V) :
    min (riemannianEDistOf (g.restrictOpen V) p x) (ENNReal.ofReal R) =
      min (riemannianEDistOf g p.val x.val) (ENNReal.ofReal R) := by
  by_cases hx : riemannianEDistOf g p.val x.val < ENNReal.ofReal R
  · have hball' : riemannianBallOf g p.val R ⊆ range (Subtype.val : V → M) := by
      intro y hy
      exact ⟨⟨y, hball hy⟩, rfl⟩
    obtain ⟨z, hz, heq⟩ := exists_riemannianEDistOf_localPullMetric_eq_of_ball_subset_range
      g (isLocalDiffeomorph_subtype_val V) Subtype.val_injective p hball' hx
    have hzx : z = x := Subtype.ext hz
    subst z
    rw [localPullMetric_subtype_val] at heq
    rw [heq]
  · have hlow : ENNReal.ofReal R ≤ riemannianEDistOf g p.val x.val := not_lt.mp hx
    rw [min_eq_right (hlow.trans (riemannianEDistOf_le_restrictOpen g V p x)),
      min_eq_right hlow]

private theorem min_le_mul_min {d e R A : ℝ≥0∞} (hde : d ≤ A * e) (hA : 1 ≤ A) :
    min d R ≤ A * min e R := by
  by_cases he : e ≤ R
  · rw [min_eq_left he]
    exact (min_le_left _ _).trans hde
  · rw [min_eq_right (le_of_not_ge he)]
    exact (min_le_right _ _).trans (by
      simpa only [one_mul] using mul_le_mul' hA (le_refl R))

/-- A fixed compact protective set gives joint continuity of the original
ambient distance clipped at the protected radius, including both time endpoints.
The radius may be nonpositive, in which case the clipped function is zero. -/
theorem continuousOn_min_edist_of_compact_protected_domain
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hcarrier : Icc a b ⊆ D.carrier)
    (hregular : Ioo a b ⊆ D.regular)
    (V : Opens M) (C : Set M) (hC : IsCompact C)
    (hVC : (V : Set M) ⊆ C) (p : V) (R : ℝ)
    (hball : ∀ t ∈ Icc a b, riemannianBallOf (S.base.metric t) p.val R ⊆ V) :
    ContinuousOn (fun q : ℝ × M =>
      min (riemannianEDistOf (S.base.metric q.1) p.val q.2) (ENNReal.ofReal R))
      (Icc a b ×ˢ (univ : Set M)) := by
  obtain ⟨K, hK⟩ := (isCompact_Icc.prod hC).bddAbove_image
    (hS.continuousOn_rmNormSq.mono (fun q hq => ⟨hcarrier hq.1, mem_univ q.2⟩))
  have hRm (v : ℝ) (hv : v ∈ Icc a b) (x : V) :
      normSq0S (S.base.metric v) x.val 4 (S.base.rm04 v x.val) ≤ K :=
    hK ⟨(v, x.val), ⟨hv, hVC x.property⟩, rfl⟩
  let c : ℝ := (Module.finrank ℝ E : ℝ)^2 * Real.sqrt K
  have hc : 0 ≤ c := mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
  have hlocal (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (x : V) :
      riemannianEDistOf ((S.base.metric s).restrictOpen V) p x ≤
        ENNReal.ofReal (Real.exp (c * |s-t|)) *
          riemannianEDistOf ((S.base.metric t).restrictOpen V) p x := by
    have hquad (z : V) (w : TangentSpace I z) :
        ((S.base.metric s).restrictOpen V).inner z w w ≤
          Real.exp (2*(Module.finrank ℝ E : ℝ)^2 * Real.sqrt K * |s-t|) *
            ((S.base.metric t).restrictOpen V).inner z w w := by
      exact (metric_inner_exp_bounds_of_curvature_bound S hS hcarrier hregular z.val
        (fun v hv => hRm v hv z) hs ht w).2
    have hh := edistOf_le_of_quad ((S.base.metric t).restrictOpen V)
      ((S.base.metric s).restrictOpen V) (Real.exp_pos _) hquad p x
    rw [← Real.exp_half] at hh
    have he : 2*(Module.finrank ℝ E : ℝ)^2 * Real.sqrt K * |s-t| / 2 = c*|s-t| := by
      dsimp only [c]
      ring
    simpa only [he] using hh
  let d : ℝ → M → ℝ≥0∞ := fun t x =>
    min (riemannianEDistOf (S.base.metric t) p.val x) (ENNReal.ofReal R)
  have hupper (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (x : M) :
      d s x ≤ ENNReal.ofReal (Real.exp (c*|s-t|)) * d t x := by
    have hA : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (Real.exp (c*|s-t|)) := by
      simpa only [ENNReal.ofReal_one] using
        ENNReal.ofReal_le_ofReal (Real.one_le_exp (mul_nonneg hc (abs_nonneg _)))
    by_cases hx : x ∈ V
    · let z : V := ⟨x, hx⟩
      have hs' := min_restrictOpen_edist_eq (S.base.metric s) V p z R (hball s hs)
      have ht' := min_restrictOpen_edist_eq (S.base.metric t) V p z R (hball t ht)
      change min (riemannianEDistOf (S.base.metric s) p.val z.val) (ENNReal.ofReal R) ≤
        ENNReal.ofReal (Real.exp (c*|s-t|)) *
          min (riemannianEDistOf (S.base.metric t) p.val z.val) (ENNReal.ofReal R)
      rw [← hs', ← ht']
      exact min_le_mul_min (hlocal s t hs ht z) hA
    · have hlarge (v : ℝ) (hv : v ∈ Icc a b) :
          ENNReal.ofReal R ≤ riemannianEDistOf (S.base.metric v) p.val x := by
        apply le_of_not_gt
        intro hh
        exact hx (hball v hv hh)
      dsimp only [d]
      rw [min_eq_right (hlarge s hs), min_eq_right (hlarge t ht)]
      simpa only [one_mul] using mul_le_mul' hA (le_refl (ENNReal.ofReal R))
  have hlower (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (x : M) :
      ENNReal.ofReal (Real.exp (-(c*|s-t|))) * d t x ≤ d s x := by
    have hh := hupper t s ht hs x
    rw [abs_sub_comm t s] at hh
    calc
      _ ≤ ENNReal.ofReal (Real.exp (-(c*|s-t|))) *
          (ENNReal.ofReal (Real.exp (c*|s-t|)) * d s x) := mul_le_mul' le_rfl hh
      _ = d s x := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add,
          neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one, one_mul]
  intro q hq
  let A : ℝ × M → ℝ := fun z => c * |z.1-q.1|
  let d₀ : ℝ × M → ℝ≥0∞ := fun z => d q.1 z.2
  have hA : Continuous A := continuous_const.mul (continuous_fst.sub continuous_const).abs
  have hd₀ : Continuous d₀ :=
    ((Geometry.Riemannian.continuous_riemannianEDist (S.base.metric q.1) p.val).comp
      continuous_snd).min continuous_const
  have hlo : Continuous (fun z => ENNReal.ofReal (Real.exp (-A z)) * d₀ z) :=
    (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp hA.neg)).ennreal_mul hd₀
      (fun _ => Or.inl (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne')
      (fun _ => Or.inr ENNReal.ofReal_ne_top)
  have hhi : Continuous (fun z => ENNReal.ofReal (Real.exp (A z)) * d₀ z) :=
    (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp hA)).ennreal_mul hd₀
      (fun _ => Or.inl (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne')
      (fun _ => Or.inr ENNReal.ofReal_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun z => ENNReal.ofReal (Real.exp (-A z)) * d₀ z)
    (h := fun z => ENNReal.ofReal (Real.exp (A z)) * d₀ z) ?_ ?_ ?_ ?_
  · change Tendsto _ (𝓝 q ⊓ principal (Icc a b ×ˢ univ)) _
    simpa only [A, d₀, d, sub_self, abs_zero, mul_zero, neg_zero,
      Real.exp_zero, ENNReal.ofReal_one, one_mul] using (hlo.tendsto q).mono_left inf_le_left
  · change Tendsto _ (𝓝 q ⊓ principal (Icc a b ×ˢ univ)) _
    simpa only [A, d₀, d, sub_self, abs_zero, mul_zero,
      Real.exp_zero, ENNReal.ofReal_one, one_mul] using (hhi.tendsto q).mono_left inf_le_left
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact hlower z.1 q.1 hz.1 hq.1 z.2
  · filter_upwards [self_mem_nhdsWithin] with z hz
    exact hupper z.1 q.1 hz.1 hq.1 z.2

theorem continuousOn_min_edist_toReal_of_compact_protected_domain
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {a b : ℝ} (hcarrier : Icc a b ⊆ D.carrier)
    (hregular : Ioo a b ⊆ D.regular)
    (V : Opens M) (C : Set M) (hC : IsCompact C)
    (hVC : (V : Set M) ⊆ C) (p : V) (R : ℝ)
    (hball : ∀ t ∈ Icc a b, riemannianBallOf (S.base.metric t) p.val R ⊆ V) :
    ContinuousOn (fun q : ℝ × M =>
      (min (riemannianEDistOf (S.base.metric q.1) p.val q.2) (ENNReal.ofReal R)).toReal)
      (Icc a b ×ˢ (univ : Set M)) := by
  apply ENNReal.continuousOn_toReal.comp'
    (continuousOn_min_edist_of_compact_protected_domain S hS hcarrier hregular V C hC hVC p R hball)
  intro q _
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_right _ _)

end DifferentialGeometry.PDE.RicciFlow
