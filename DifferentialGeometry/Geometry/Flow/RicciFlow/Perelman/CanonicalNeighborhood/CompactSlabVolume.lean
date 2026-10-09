import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.EarlySlabVolume


set_option autoImplicit false
noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Tensor.Coordinates
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.VolumeComparison
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Integral.Measure
open Bundle Manifold Matrix MeasureTheory Metric Set
open scoped Manifold ContDiff Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M] [I.Boundaryless]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [CompleteSpace E] [T2Space M] [CompactSpace M] [I.Boundaryless] in
private theorem paramDensity_cont_compact
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    {K : Set Real} (hK : K ⊆ D.carrier)
    (Ψ : PartialDiffeomorph 𝓘(Real, E) I E M 1)
    {B : Set E} (hB : B ⊆ Ψ.source) :
    Continuous (fun q : {t : Real // t ∈ K} × B =>
      paramDensity (I := I) (g_fam q.1.1) Ψ q.2.1) := by
  classical
  let P := {t : Real // t ∈ K} × B
  let b : P → M := fun q => Ψ q.2.1
  have hb : Continuous b :=
    Ψ.contMDiffOn_toFun.continuousOn.comp_continuous
      (continuous_subtype_val.comp continuous_snd)
      (fun q => hB q.2.2)
  have hslot : ∀ i : Fin (Module.finrank Real E),
      Continuous (fun q : P =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) (b q)
          (mfderiv 𝓘(Real, E) I Ψ q.2.1 ((chartModelBasis E) i))) := by
    intro i
    let lift : P → TangentBundle 𝓘(Real, E) E :=
      fun q => ⟨q.2.1, (chartModelBasis E) i⟩
    have hlift : Continuous lift :=
      (tangentBundleModelSpaceHomeomorph 𝓘(Real, E)).symm.continuous.comp
        ((continuous_subtype_val.comp continuous_snd).prodMk continuous_const)
    simpa [b, lift] using
      (PartialDiffeomorph.continuous_mfderiv_apply Ψ (by norm_num) lift hlift
        (fun q => hB q.2.2))
  have hentry : ∀ i j : Fin (Module.finrank Real E),
      Continuous (fun q : P =>
        paramGramMatrix (I := I) (g_fam q.1.1) Ψ q.2.1 i j) := by
    intro i j
    let v : Fin 2 → (q : P) → TangentSpace I (b q) :=
      fun k q => mfderiv 𝓘(Real, E) I Ψ q.2.1
        ((chartModelBasis E) (if k = 0 then i else j))
    have hv : ∀ k : Fin 2, Continuous (fun q : P =>
        TotalSpace.mk' E (E := fun x : M => TangentSpace I x) (b q) (v k q)) := by
      intro k
      exact hslot (if k = 0 then i else j)
    have heval :=
      (metricTensor_cont_restrict_of_metricFamilySmoothOn
        (I := I) (M := M) g_fam hG hK).eval_continuous
        (P := P) (τ := fun q => q.1.1) (b := b)
        (continuous_subtype_val.comp continuous_fst)
        (fun q => q.1.2) hb hv
    refine heval.congr (fun q => ?_)
    rw [Tensor0SBundle.metricTensorField_apply]
    simp [b, v, paramGramMatrix_apply]
  have hmatrix : Continuous (fun q : P =>
      paramGramMatrix (I := I) (g_fam q.1.1) Ψ q.2.1) := by
    apply continuous_matrix
    exact hentry
  exact Real.continuous_sqrt.comp
    ((continuous_id.matrix_det).comp hmatrix)

omit [CompactSpace M] in
private theorem exists_param_ctrl_compact
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    {K : Set ℝ} (hKc : IsCompact K) (hK : K ⊆ D.carrier) (hKne : K.Nonempty)
    (a : M) :
    let Ψ := NormalCoordinates.expMapDiffeo (I := I) (g_fam 0) a
    ∃ R c L : ℝ, 0 < R ∧ 0 < c ∧ 1 ≤ L ∧
      Metric.closedBall (0 : E) (2 * R) ⊆ Ψ.source ∧
      ∀ t ∈ K, ∀ w ∈ Metric.closedBall (0 : E) (2 * R),
        c ≤ paramDensity (I := I) (g_fam t) Ψ w ∧
        ∀ v : E, Real.sqrt
          ((g_fam t).inner (Ψ w)
            (mfderiv 𝓘(Real, E) I Ψ w v) (mfderiv 𝓘(Real, E) I Ψ w v)) ≤ L * ‖v‖ := by
  classical
  dsimp only
  let Ψ := NormalCoordinates.expMapDiffeo (I := I) (g_fam 0) a
  let R : Real := expMapC2Radius (I := I) (g_fam 0) a / 4
  let B : Set E := Metric.closedBall (0 : E) (2 * R)
  have hR_pos : 0 < R := by
    dsimp [R]
    exact div_pos (expMapC2Radius_pos (I := I) (g_fam 0) a) (by norm_num)
  have hB : B ⊆ Ψ.source := by
    intro w hw
    apply mem_expMapDiffeo_source_of_norm_lt_radius
      (I := I) (g_fam 0) a
    have hw_le : ‖w‖ ≤ 2 * R := by
      simpa [B, Metric.mem_closedBall, dist_zero_right] using hw
    have h2R_lt : 2 * R < expMapC2Radius (I := I) (g_fam 0) a := by
      dsimp [R]
      nlinarith [expMapC2Radius_pos (I := I) (g_fam 0) a]
    exact lt_of_le_of_lt hw_le h2R_lt
  let T := {t : Real // t ∈ K}
  let P := T × B
  let dens : P → Real := fun q =>
    paramDensity (I := I) (g_fam q.1.1) Ψ q.2.1
  have hdens : Continuous dens :=
    paramDensity_cont_compact (I := I) g_fam hG hK Ψ hB
  let : CompactSpace T := isCompact_iff_compactSpace.mp hKc
  let : CompactSpace B :=
    isCompact_iff_compactSpace.mp (by
      simpa [B] using isCompact_closedBall (0 : E) (2 * R))
  have hPne : (Set.univ : Set P).Nonempty := by
    let q : P :=
      (⟨hKne.choose, hKne.choose_spec⟩,
        ⟨0, by simp [B, hR_pos.le]⟩)
    exact ⟨q, Set.mem_univ q⟩
  obtain ⟨qmin, _hqmin, hmin⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set P)).exists_isMinOn
      hPne hdens.continuousOn
  let c : Real := dens qmin
  have hc_pos : 0 < c := by
    dsimp [c, dens]
    exact paramDensity_pos (I := I) (g_fam qmin.1.1) Ψ
      (hB qmin.2.2)
  let U : Set E := Metric.closedBall (0 : E) 1
  let Q := P × U
  let speed : Q → Real := fun q =>
    Real.sqrt
      ((g_fam q.1.1.1).inner (Ψ q.1.2.1)
        (mfderiv 𝓘(Real, E) I Ψ q.1.2.1 q.2.1)
        (mfderiv 𝓘(Real, E) I Ψ q.1.2.1 q.2.1))
  have htangent : Continuous (fun q : Q =>
      TotalSpace.mk' E (E := fun x : M => TangentSpace I x) (Ψ q.1.2.1)
        (mfderiv 𝓘(Real, E) I Ψ q.1.2.1 q.2.1)) := by
    let lift : Q → TangentBundle 𝓘(Real, E) E :=
      fun q => ⟨q.1.2.1, q.2.1⟩
    have hlift : Continuous lift :=
      (tangentBundleModelSpaceHomeomorph 𝓘(Real, E)).symm.continuous.comp
        ((continuous_subtype_val.comp (continuous_snd.comp continuous_fst)).prodMk
          (continuous_subtype_val.comp continuous_snd))
    simpa [lift] using
      (PartialDiffeomorph.continuous_mfderiv_apply Ψ (by norm_num) lift hlift
        (fun q => hB q.1.2.2))
  have hspeed : Continuous speed := by
    have hquad :=
      metricTimeBundleQuad_cont_of_metricFamilySmoothOn
        (I := I) (M := M) g_fam hG hK
    have hpull : Continuous (fun q : Q =>
        (q.1.1,
          TotalSpace.mk' E (E := fun x : M => TangentSpace I x) (Ψ q.1.2.1)
            (mfderiv 𝓘(Real, E) I Ψ q.1.2.1 q.2.1))) :=
      (continuous_fst.comp continuous_fst).prodMk htangent
    exact Real.continuous_sqrt.comp (hquad.comp hpull)
  let : CompactSpace U :=
    isCompact_iff_compactSpace.mp (by
      simpa [U] using isCompact_closedBall (0 : E) 1)
  have hQne : (Set.univ : Set Q).Nonempty := by
    obtain ⟨p0, _⟩ := hPne
    let q : Q := (p0, ⟨0, by simp [U]⟩)
    exact ⟨q, Set.mem_univ q⟩
  obtain ⟨qmax, _hqmax, hmax⟩ :=
    (isCompact_univ : IsCompact (Set.univ : Set Q)).exists_isMaxOn
      hQne hspeed.continuousOn
  let L : Real := max 1 (speed qmax)
  have hL_one : 1 ≤ L := le_max_left _ _
  have hL_pos : 0 < L := lt_of_lt_of_le zero_lt_one hL_one
  refine ⟨R, c, L, hR_pos, hc_pos, hL_one, hB, ?_⟩
  intro t htK w hw
  let p : P := (⟨(t : Real), htK⟩, ⟨w, hw⟩)
  have hc_le : c ≤ paramDensity (I := I) (g_fam (t : Real)) Ψ w := by
    have hp := (isMinOn_iff.mp hmin) p (Set.mem_univ p)
    simpa [c, dens, p] using hp
  refine ⟨hc_le, ?_⟩
  intro v
  by_cases hv : v = 0
  · subst v
    have hd0 :
        mfderiv 𝓘(Real, E) I Ψ w (0 : E) =
          (0 : TangentSpace I (Ψ w)) := by
      exact map_zero _
    rw [hd0]
    simp
  · have hvnorm_pos : 0 < ‖v‖ := norm_pos_iff.mpr hv
    let u : E := ‖v‖⁻¹ • v
    have hu_norm : ‖u‖ = 1 := by
      dsimp [u]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm]
      exact inv_mul_cancel₀ (ne_of_gt hvnorm_pos)
    have hu_mem : u ∈ U := by
      simp [U, Metric.mem_closedBall, dist_zero_right, hu_norm]
    let q : Q := (p, ⟨u, hu_mem⟩)
    have hspeed_le : speed q ≤ L := by
      exact le_trans ((isMaxOn_iff.mp hmax) q (Set.mem_univ q))
        (le_max_right _ _)
    have hv_from_u : ‖v‖ • u = v := by
      dsimp [u]
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hvnorm_pos), one_smul]
    have hscale :
        (g_fam (t : Real)).inner (Ψ w)
            (mfderiv 𝓘(Real, E) I Ψ w v)
            (mfderiv 𝓘(Real, E) I Ψ w v) =
          ‖v‖ ^ 2 *
            (g_fam (t : Real)).inner (Ψ w)
              (mfderiv 𝓘(Real, E) I Ψ w u)
              (mfderiv 𝓘(Real, E) I Ψ w u) := by
      conv_lhs => rw [← hv_from_u]
      have hdscale :
          mfderiv 𝓘(Real, E) I Ψ w (‖v‖ • u) =
            ‖v‖ • mfderiv 𝓘(Real, E) I Ψ w u := by
        exact map_smul _ _ _
      rw [hdscale, metric_smul2]
      ring
    rw [hscale, Real.sqrt_mul (sq_nonneg ‖v‖), Real.sqrt_sq_eq_abs,
      abs_of_nonneg (norm_nonneg v)]
    have hspeed_le' :
        Real.sqrt
            ((g_fam (t : Real)).inner (Ψ w)
              (mfderiv 𝓘(Real, E) I Ψ w u)
              (mfderiv 𝓘(Real, E) I Ψ w u)) ≤ L := by
      simpa [speed, q, p] using hspeed_le
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_left hspeed_le' (norm_nonneg v))

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem family_compact_small_ball_lower
    [T2Space (TangentBundle I M)]
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    {K : Set ℝ} (hKc : IsCompact K) (hK : K ⊆ D.carrier) (hKne : K.Nonempty) :
    ∃ kappa delta : ℝ, 0 < kappa ∧ 0 < delta ∧
      ∀ t ∈ K, ∀ p : M, ∀ r : ℝ, 0 < r → r ≤ delta →
        ENNReal.ofReal kappa * ENNReal.ofReal r ^ Module.finrank ℝ E ≤
          riemannianVolumeMeasure I M (g_fam t)
            {x : M | riemannianEDistOf (I := I) (g_fam t) p x < ENNReal.ofReal r} := by
  classical
  by_cases hM : IsEmpty M
  · refine ⟨1, 1, one_pos, one_pos, ?_⟩
    intro _t _ht p
    exact (hM.false p).elim
  rw [not_isEmpty_iff] at hM
  let Ψ : M → PartialDiffeomorph 𝓘(Real, E) I E M 1 :=
    fun a => NormalCoordinates.expMapDiffeo (I := I) (g_fam 0) a
  have hlocal : ∀ a : M, ∃ R c L : Real,
      0 < R ∧ 0 < c ∧ 1 ≤ L ∧
      Metric.closedBall (0 : E) (2 * R) ⊆ (Ψ a).source ∧
      ∀ t ∈ K,
        ∀ w ∈ Metric.closedBall (0 : E) (2 * R),
          c ≤ paramDensity (I := I) (g_fam (t : Real)) (Ψ a) w ∧
          ∀ v : E,
            Real.sqrt
              ((g_fam (t : Real)).inner ((Ψ a) w)
                (mfderiv 𝓘(Real, E) I (Ψ a) w v)
                (mfderiv 𝓘(Real, E) I (Ψ a) w v)) ≤ L * ‖v‖ := by
    intro a
    simpa only [Ψ] using exists_param_ctrl_compact g_fam hG hKc hK hKne a
  choose RLoc cLoc LLoc hR_pos hc_pos hL_one hsource hctrl
    using hlocal
  let U : M → Set M := fun a => (Ψ a) '' Metric.ball (0 : E) (RLoc a)
  have hball_source : ∀ a : M,
      Metric.ball (0 : E) (RLoc a) ⊆ (Ψ a).source := by
    intro a w hw
    apply hsource a
    have hwR : ‖w‖ < RLoc a := by
      simpa only [Metric.mem_ball, dist_zero_right] using hw
    simp only [Metric.mem_closedBall, dist_zero_right]
    linarith [hR_pos a]
  have hU_open : ∀ a : M, IsOpen (U a) := by
    intro a
    exact (Ψ a).toOpenPartialHomeomorph.isOpen_image_of_subset_source
      Metric.isOpen_ball (hball_source a)
  have haU : ∀ a : M, a ∈ U a := by
    intro a
    refine ⟨0, ?_, ?_⟩
    · simpa only [Metric.mem_ball, dist_self] using hR_pos a
    · simpa only [Ψ] using
        NormalCoordinates.expMapDiffeo_zero (I := I) (g_fam 0) a
  have hcover : (Set.univ : Set M) ⊆ ⋃ a : M, U a := by
    intro a _ha
    exact Set.mem_iUnion.mpr ⟨a, haU a⟩
  obtain ⟨s, hs_cover⟩ :=
    (isCompact_univ (X := M)).elim_finite_subcover U hU_open hcover
  have hs_ne : s.Nonempty := by
    obtain ⟨a⟩ := hM
    have ha : a ∈ ⋃ i ∈ s, U i := hs_cover (Set.mem_univ a)
    rw [Set.mem_iUnion₂] at ha
    obtain ⟨i, hi, _⟩ := ha
    exact ⟨i, hi⟩
  let unitVol : Real :=
    ((modelHaar (E := E)) (Metric.ball (0 : E) 1)).toReal
  have hunit_pos : 0 < unitVol := by
    dsimp only [unitVol]
    exact ENNReal.toReal_pos
      (Metric.measure_ball_pos (modelHaar (E := E)) (0 : E) one_pos).ne'
      measure_ball_lt_top.ne
  let kLoc : M → Real :=
    fun a => cLoc a * (LLoc a)⁻¹ ^ Module.finrank Real E * unitVol
  have hkLoc_pos : ∀ a : M, 0 < kLoc a := by
    intro a
    dsimp only [kLoc]
    exact mul_pos
      (mul_pos (hc_pos a) (pow_pos (inv_pos.mpr (zero_lt_one.trans_le (hL_one a))) _))
      hunit_pos
  let delta : Real := s.inf' hs_ne RLoc
  let kappa : Real := s.inf' hs_ne kLoc
  have hdelta_pos : 0 < delta := by
    rw [show delta = s.inf' hs_ne RLoc from rfl, Finset.lt_inf'_iff]
    intro a _ha
    exact hR_pos a
  have hdelta_le : ∀ a ∈ s, delta ≤ RLoc a := by
    intro a ha
    exact Finset.inf'_le _ ha
  have hkappa_pos : 0 < kappa := by
    rw [show kappa = s.inf' hs_ne kLoc from rfl, Finset.lt_inf'_iff]
    intro a _ha
    exact hkLoc_pos a
  have hkappa_le : ∀ a ∈ s, kappa ≤ kLoc a := by
    intro a ha
    exact Finset.inf'_le _ ha
  refine ⟨kappa, delta, hkappa_pos, hdelta_pos, ?_⟩
  intro t ht p r hr hrdelta
  have hp : p ∈ ⋃ i ∈ s, U i := hs_cover (Set.mem_univ p)
  rw [Set.mem_iUnion₂] at hp
  obtain ⟨a, ha, w, hw, hwp⟩ := hp
  have hrR : r ≤ RLoc a := hrdelta.trans (hdelta_le a ha)
  let B : Set E := Metric.ball w (r / LLoc a)
  have hL_pos : 0 < LLoc a := zero_lt_one.trans_le (hL_one a)
  have hrad_pos : 0 < r / LLoc a := div_pos hr hL_pos
  have hw_norm : ‖w‖ < RLoc a := by
    simpa only [Metric.mem_ball, dist_zero_right] using hw
  have hB_closed : B ⊆ Metric.closedBall (0 : E) (2 * RLoc a) := by
    intro z hz
    have hzw : dist z w < r / LLoc a := by
      simpa only [B, Metric.mem_ball] using hz
    have hdiv_le : r / LLoc a ≤ r := by
      exact (div_le_iff₀ hL_pos).2 <| by nlinarith [hL_one a, hr]
    simp only [Metric.mem_closedBall, dist_zero_right]
    calc
      ‖z‖ ≤ ‖w‖ + ‖z - w‖ := norm_le_norm_add_norm_sub' z w
      _ = ‖w‖ + dist z w := by rw [dist_eq_norm]
      _ ≤ 2 * RLoc a := by linarith
  have hB_source : B ⊆ (Ψ a).source :=
    hB_closed.trans (hsource a)
  have hseg : ∀ z ∈ B,
      segment Real w z ⊆ Metric.closedBall (0 : E) (2 * RLoc a) := by
    intro z hz
    apply (convex_closedBall (0 : E) (2 * RLoc a)).segment_subset
    · simp only [Metric.mem_closedBall, dist_zero_right]
      linarith [hw_norm, hR_pos a]
    · exact hB_closed hz
  have hctrl_t := hctrl a t ht
  let : Bundle.RiemannianBundle (fun x : M => TangentSpace I x) :=
    ⟨(g_fam (t : Real)).toRiemannianMetric⟩
  have hspd : ∀ q ∈ Metric.closedBall (0 : E) (2 * RLoc a), ∀ ξ : E,
      ‖mfderiv 𝓘(Real, E) I (Ψ a) q ξ‖ₑ ≤
        ENNReal.ofReal (LLoc a * ‖ξ‖) := by
    intro q hq ξ
    rw [← ofReal_norm, norm_eq_sqrt_real_inner]
    change ENNReal.ofReal
      (Real.sqrt
        ((g_fam (t : Real)).inner ((Ψ a) q)
          (mfderiv 𝓘(Real, E) I (Ψ a) q ξ)
          (mfderiv 𝓘(Real, E) I (Ψ a) q ξ))) ≤
        ENNReal.ofReal (LLoc a * ‖ξ‖)
    exact ENNReal.ofReal_le_ofReal ((hctrl_t q hq).2 ξ)
  have himage : (Ψ a) '' B ⊆
      {x : M | riemannianEDistOf (I := I) (g_fam (t : Real)) p x <
        ENNReal.ofReal r} := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := hx
    have hdist := param_edist_le (I := I) (Ψ a)
      (hsource a) hspd (hseg z hz)
    rw [← hwp]
    refine lt_of_le_of_lt hdist ?_
    have hzw : dist w z < r / LLoc a := by
      simpa only [B, Metric.mem_ball, dist_comm] using hz
    have hmul : LLoc a * dist w z < r := by
      calc
        LLoc a * dist w z < LLoc a * (r / LLoc a) :=
          mul_lt_mul_of_pos_left hzw hL_pos
        _ = r := by field_simp
    exact (ENNReal.ofReal_lt_ofReal_iff hr).2 hmul
  have hparam :
      ENNReal.ofReal (cLoc a) * (modelHaar (E := E)) B ≤
        riemannianVolumeMeasure (I := I) (M := M) (g_fam (t : Real))
          ((Ψ a) '' B) := by
    apply param_vol_ge (I := I) (g_fam (t : Real)) (Ψ a)
      measurableSet_ball hB_source
    intro z hz
    exact (hctrl_t z (hB_closed hz)).1
  have hmono :
      riemannianVolumeMeasure (I := I) (M := M) (g_fam (t : Real))
          ((Ψ a) '' B) ≤
        riemannianVolumeMeasure (I := I) (M := M) (g_fam (t : Real))
          {x : M | riemannianEDistOf (I := I) (g_fam (t : Real)) p x <
            ENNReal.ofReal r} :=
    measure_mono himage
  have hball :
      (modelHaar (E := E)) B =
        ENNReal.ofReal ((r / LLoc a) ^ Module.finrank Real E) *
          (modelHaar (E := E)) (Metric.ball (0 : E) 1) := by
    simpa only [B] using
      (MeasureTheory.Measure.addHaar_ball_of_pos
        (μ := modelHaar (E := E)) (x := w) hrad_pos)
  have hkappa_ofReal :
      ENNReal.ofReal kappa ≤ ENNReal.ofReal (kLoc a) :=
    ENNReal.ofReal_le_ofReal (hkappa_le a ha)
  calc
    ENNReal.ofReal kappa * ENNReal.ofReal r ^ Module.finrank Real E
        ≤ ENNReal.ofReal (kLoc a) *
            ENNReal.ofReal r ^ Module.finrank Real E := by gcongr
    _ = ENNReal.ofReal (cLoc a) * (modelHaar (E := E)) B := by
      rw [hball]
      dsimp only [kLoc, unitVol]
      rw [ENNReal.ofReal_mul (mul_nonneg (hc_pos a).le
          (pow_nonneg (inv_nonneg.mpr hL_pos.le) _)),
        ENNReal.ofReal_mul (hc_pos a).le,
        ENNReal.ofReal_pow (inv_nonneg.mpr hL_pos.le),
        ENNReal.ofReal_inv_of_pos hL_pos,
        ENNReal.ofReal_toReal measure_ball_lt_top.ne]
      conv_rhs =>
        rw [ENNReal.ofReal_pow (div_nonneg hr.le hL_pos.le),
          ENNReal.ofReal_div_of_pos hL_pos]
      simp only [div_eq_mul_inv, mul_pow]
      ac_rfl
    _ ≤ riemannianVolumeMeasure (I := I) (M := M) (g_fam (t : Real))
          ((Ψ a) '' B) := hparam
    _ ≤ riemannianVolumeMeasure (I := I) (M := M) (g_fam (t : Real))
          {x : M | riemannianEDistOf (I := I) (g_fam (t : Real)) p x <
            ENNReal.ofReal r} := hmono


theorem family_compact_slab_volume
    [T2Space (TangentBundle I M)]
    {D : RealTimeInterval}
    (g_fam : ℝ → SmoothRiemannianMetric I M)
    (hG : MetricFamilySmoothOn (I := I) (M := M) D g_fam)
    {K : Set ℝ} (hKc : IsCompact K) (hK : K ⊆ D.carrier)
    {rho : ℝ} (hrho : 0 < rho) :
    ∃ kappa : ℝ, 0 < kappa ∧
      ∀ t ∈ K, ∀ p : M, ∀ r : ℝ, 0 < r → r ≤ rho →
        ENNReal.ofReal kappa * ENNReal.ofReal r ^ Module.finrank ℝ E ≤
          riemannianVolumeMeasure I M (g_fam t)
            {x : M | riemannianEDistOf (I := I) (g_fam t) p x < ENNReal.ofReal r} := by
  by_cases hKne : K.Nonempty
  swap
  · refine ⟨1, one_pos, ?_⟩
    intro t ht
    exact (hKne ⟨t, ht⟩).elim
  obtain ⟨kappa0, delta, hkappa0, hdelta, hsmall⟩ :=
    family_compact_small_ball_lower g_fam hG hKc hK hKne
  let c : ℝ := min 1 (delta / rho)
  have hc : 0 < c := lt_min zero_lt_one (div_pos hdelta hrho)
  have hc1 : c ≤ 1 := min_le_left _ _
  have hcrho : c * rho ≤ delta :=
    (le_div_iff₀ hrho).1 (min_le_right _ _)
  refine ⟨kappa0 * c ^ Module.finrank ℝ E,
    mul_pos hkappa0 (pow_pos hc _), ?_⟩
  intro t ht p r hr hrrho
  have hcr : 0 < c * r := mul_pos hc hr
  have hcrdelta : c * r ≤ delta :=
    (mul_le_mul_of_nonneg_left hrrho hc.le).trans hcrho
  have hcrr : c * r ≤ r := mul_le_of_le_one_left hr.le hc1
  calc
    ENNReal.ofReal (kappa0 * c ^ Module.finrank ℝ E) *
        ENNReal.ofReal r ^ Module.finrank ℝ E =
      ENNReal.ofReal kappa0 * ENNReal.ofReal (c * r) ^ Module.finrank ℝ E := by
        rw [ENNReal.ofReal_mul hkappa0.le, ENNReal.ofReal_pow hc.le,
          ENNReal.ofReal_mul hc.le, mul_pow]
        ac_rfl
    _ ≤ riemannianVolumeMeasure (I := I) (M := M) (g_fam (t : Real))
        {x : M | riemannianEDistOf (I := I) (g_fam (t : Real)) p x <
          ENNReal.ofReal (c * r)} := hsmall t ht p (c * r) hcr hcrdelta
    _ ≤ riemannianVolumeMeasure (I := I) (M := M) (g_fam (t : Real))
        {x : M | riemannianEDistOf (I := I) (g_fam (t : Real)) p x <
          ENNReal.ofReal r} := by
      apply measure_mono
      intro x hx
      exact hx.trans_le (ENNReal.ofReal_le_ofReal hcrr)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
