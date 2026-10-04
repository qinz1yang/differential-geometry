import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.Finite.LocalApproximation

/-!
# Partition-of-unity assembly for a metric of finite order (LFR02, tier T2)

Finite-order re-run of LC28's `DistanceSmoothing/Assembly.lean` (whose statement takes a
`SmoothRiemannianMetric`). Properness, connectedness and the local-to-global Lipschitz bound come
from the metric Hopf–Rinow of lane CM-H (`Geometry/Metric/Path/RiemannianHopfRinow.lean`, any
regularity) and LC28's metric kernel `lipschitzWith_of_locally_of_segments`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set Metric
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian Bundle.ContMDiffRiemannianMetric

namespace DifferentialGeometry.Geometry.Collapse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)] [IsRiemannianManifold I M]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M] in
variable (I) in
include I in
/-- On a complete Riemannian manifold of any regularity, any two points are joined by a segment
parametrized on `[0, 1]` proportionally to arc length (the form consumed by
`lipschitzWith_of_locally_of_segments`). -/
theorem exists_riemannian_segment_of_isRiemannianManifold [CompleteSpace M] (x y : M) :
    ∃ c : ℝ → M, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
      ∀ s t, s ≤ t → dist (c s) (c t) ≤ dist x y * (t - s) := by
  obtain ⟨c₀, hc0, hc1, hseg⟩ := Manifold.exists_unit_speed_segment_of_isRiemannianManifold I x y
  set D := dist x y with hD
  have hD0 : 0 ≤ D := dist_nonneg
  set cl : ℝ → ℝ := fun t => D * max 0 (min 1 t) with hcl
  have hclmem : ∀ t, cl t ∈ Icc 0 D := fun t => by
    refine ⟨mul_nonneg hD0 (le_max_left _ _), ?_⟩
    have : max 0 (min 1 t) ≤ 1 := max_le zero_le_one (min_le_left _ _)
    nlinarith
  have hc₀cont : ContinuousOn c₀ (Icc 0 D) := by
    refine (LipschitzOnWith.of_dist_le_mul (K := 1) fun s hs t ht => ?_).continuousOn
    rw [hseg s hs t ht, NNReal.coe_one, one_mul, Real.dist_eq]
  have hclc : Continuous cl := continuous_const.mul
    (continuous_const.max (continuous_const.min continuous_id))
  refine ⟨fun t => c₀ (cl t), hc₀cont.comp_continuous hclc hclmem, ?_, ?_, fun s t hst => ?_⟩
  · simp only [hcl, min_eq_right zero_le_one, max_self, mul_zero]; exact hc0
  · simp only [hcl, min_self, max_eq_right zero_le_one, mul_one]; exact hc1
  · rw [hseg _ (hclmem s) _ (hclmem t)]
    have hmono : max 0 (min 1 s) ≤ max 0 (min 1 t) :=
      max_le_max le_rfl (min_le_min le_rfl hst)
    have hlip : max 0 (min 1 t) - max 0 (min 1 s) ≤ t - s := by
      rcases le_total t 0 with ht0 | ht0 <;> rcases le_total t 1 with ht1 | ht1 <;>
        rcases le_total s 0 with hs0 | hs0 <;> rcases le_total s 1 with hs1 | hs1 <;>
        simp [ht0, ht1, hs0, hs1] <;>
        linarith
    rw [abs_sub_comm, abs_of_nonneg (by simp only [hcl]; nlinarith)]
    simp only [hcl]
    nlinarith

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [IsManifold I ∞ M] in
variable (I) in
include I in
/-- A complete Riemannian manifold (any regularity) with a nonempty carrier is connected. -/
theorem connectedSpace_of_isRiemannianManifold_complete [CompleteSpace M] [Nonempty M] :
    ConnectedSpace M := by
  obtain ⟨x₀⟩ := ‹Nonempty M›
  refine { isPreconnected_univ := ?_, toNonempty := ‹Nonempty M› }
  refine isPreconnected_of_forall x₀ fun y _ => ?_
  obtain ⟨c, hc, hc0, hc1, -⟩ := exists_riemannian_segment_of_isRiemannianManifold I x₀ y
  refine ⟨c '' Icc 0 1, subset_univ _, ⟨0, ⟨le_rfl, zero_le_one⟩, hc0⟩,
    ⟨1, ⟨zero_le_one, le_rfl⟩, hc1⟩, ?_⟩
  exact (isPreconnected_Icc).image c hc.continuousOn

/-- A smooth compactly supported function is Lipschitz for the distance of a complete metric of
finite order. -/
theorem exists_lipschitzWith_of_contMDiff_hasCompactSupport_finite [CompleteSpace M] {r : ℕ∞}
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {ψ : M → ℝ} (hψ : ContMDiff I 𝓘(ℝ, ℝ) ∞ ψ) (hcs : HasCompactSupport ψ) :
    ∃ K : ℝ≥0, LipschitzWith K ψ := by
  -- local Lipschitz bounds near every point
  have hloc : ∀ b : M, ∃ W : Set M, IsOpen W ∧ b ∈ W ∧ ∃ K : ℝ≥0,
      ∀ x ∈ W, ∀ x' ∈ W, |ψ x - ψ x'| ≤ K * dist x x' := by
    intro b
    set φ := extChartAt I b with hφ
    have hcd : ContDiffAt ℝ 1 (ψ ∘ φ.symm) (φ b) := by
      have h : ContMDiffAt I 𝓘(ℝ, ℝ) 1 ψ b := (hψ b).of_le (by simp)
      rw [contMDiffAt_iff] at h
      have h2 := h.2
      rw [ModelWithCorners.Boundaryless.range_eq_univ, contDiffWithinAt_univ] at h2
      simpa [writtenInExtChartAt, extChartAt_model_space_eq_id, hφ, extChartAt_coe,
        extChartAt_coe_symm] using h2
    obtain ⟨K₁, t, ht, hlip⟩ := hcd.exists_lipschitzOnWith
    obtain ⟨c₀, hc₀, hc₀N⟩ := exists_mul_norm_le_finiteMetricSeminormAt g b
    obtain ⟨r₁, hr₁, hr₁src, hchart⟩ :=
      exists_ball_finiteSeminormAt_chart_sub_le g hr hnorm b (κ := 2) one_lt_two
    have hpre : φ ⁻¹' t ∈ 𝓝 b := (continuousAt_extChartAt b).preimage_mem_nhds ht
    obtain ⟨W, hWsub, hWo, hbW⟩ := _root_.mem_nhds_iff.mp (inter_mem hpre (Metric.ball_mem_nhds b hr₁))
    refine ⟨W, hWo, hbW, ⟨K₁ * (2 / c₀), by positivity⟩, fun x hx x' hx' => ?_⟩
    have hxs : x ∈ φ.source := by rw [hφ, extChartAt_source]; exact hr₁src (hWsub hx).2
    have hx's : x' ∈ φ.source := by rw [hφ, extChartAt_source]; exact hr₁src (hWsub hx').2
    have h1 := hlip.dist_le_mul (φ x) (hWsub hx).1 (φ x') (hWsub hx').1
    simp only [Function.comp_apply, φ.left_inv hxs, φ.left_inv hx's, dist_eq_norm] at h1
    have h2 := hchart x' (hWsub hx').2 x (hWsub hx).2
    have h3 : c₀ * ‖φ x - φ x'‖ ≤ 2 * dist x x' := by
      rw [dist_comm x' x] at h2
      exact (hc₀N _).trans h2
    have h4 : ‖φ x - φ x'‖ ≤ 2 / c₀ * dist x x' := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hc₀]; linarith
    calc |ψ x - ψ x'| ≤ K₁ * ‖φ x - φ x'‖ := h1
      _ ≤ K₁ * (2 / c₀ * dist x x') := mul_le_mul_of_nonneg_left h4 K₁.coe_nonneg
      _ = (K₁ * (2 / c₀)) * dist x x' := by ring
  choose W hWo hbW K hK using hloc
  obtain ⟨t, -, ht⟩ := hcs.isCompact.elim_nhds_subcover W (fun b _ => (hWo b).mem_nhds (hbW b))
  set L : ℝ≥0 := t.sup K with hL
  refine ⟨L, lipschitzWith_of_locally_of_segments
    (exists_riemannian_segment_of_isRiemannianManifold I) fun x => ?_⟩
  by_cases hx : x ∈ tsupport ψ
  · obtain ⟨b, hb, hxb⟩ := mem_iUnion₂.mp (ht hx)
    refine ⟨W b, (hWo b).mem_nhds hxb, fun y hy y' hy' => ?_⟩
    have hKL : (K b : ℝ) ≤ L := by exact_mod_cast Finset.le_sup hb
    exact (hK b y hy y' hy').trans (mul_le_mul_of_nonneg_right hKL dist_nonneg)
  · refine ⟨(tsupport ψ)ᶜ, (isClosed_tsupport ψ).isOpen_compl.mem_nhds hx, fun y hy y' hy' => ?_⟩
    rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hy', sub_zero,
      abs_zero]
    positivity

/-- Partition-of-unity assembly of local smoothings with Lipschitz control, for a complete metric
of finite order (finite-order form of LC28's `exists_smoothing_of_local_approximations`). -/
theorem exists_smoothing_of_local_approximations_finite [CompleteSpace M] {r : ℕ∞}
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r)
    (hnorm : ∀ (x : M) (w : TangentSpace I x), ‖w‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x w w)))
    {f : M → ℝ} {K : ℝ≥0} (hf : LipschitzWith K f)
    {U C : Set M} (hU : IsOpen U) (hC : IsCompact C) (hCU : C ⊆ U) {Ld La : ℝ}
    (hLd : 0 ≤ Ld)
    (hloc : ∀ b ∈ U, ∃ W : Set M, IsOpen W ∧ b ∈ W ∧ W ⊆ U ∧ IsCompact (closure W) ∧
      ∀ η > 0, ∃ f' : M → ℝ, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f' W ∧ (∀ x ∈ W, |f' x - f x| ≤ η) ∧
        (∀ x ∈ W, ∀ x' ∈ W, |(f' x - f x) - (f' x' - f x')| ≤ Ld * dist x x') ∧
        (∀ x ∈ W, ∀ x' ∈ W, |f' x - f' x'| ≤ La * dist x x'))
    {e ε' : ℝ} (he : 0 < e) (hε' : 0 < ε') :
    ∃ F : M → ℝ, ∃ O : Set M, IsOpen O ∧ C ⊆ O ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F O ∧
      (∀ x, |F x - f x| < e) ∧ (∀ x, x ∉ U → F x = f x) ∧
      (∀ x y, |(F x - f x) - (F y - f y)| ≤ (Ld + ε') * dist x y) ∧
      (∀ x y, |F x - F y| ≤ (max (K : ℝ) La + ε') * dist x y) := by
  classical
  rcases isEmpty_or_nonempty M with hM | hM
  · exact ⟨f, univ, isOpen_univ, subset_univ _, fun x => (IsEmpty.false x).elim,
      fun x => (IsEmpty.false x).elim, fun x _ => rfl, fun x => (IsEmpty.false x).elim,
      fun x => (IsEmpty.false x).elim⟩
  have : ConnectedSpace M := connectedSpace_of_isRiemannianManifold_complete I
  have : ProperSpace M := Manifold.properSpace_of_isRiemannianManifold I
  choose! W hWo hbW hWU hWc happ using hloc
  obtain ⟨C', hC'c, hCC', hC'U⟩ := exists_compact_between hC hU hCU
  obtain ⟨t, ht⟩ := hC'c.elim_finite_subcover (fun b : U => W b) (fun b => hWo b b.2)
    (fun x hx => mem_iUnion.2 ⟨⟨x, hC'U hx⟩, hbW x (hC'U hx)⟩)
  let ι := {i : U // i ∈ t}
  let V : ι → Set M := fun i => W i.1.1
  have hVo : ∀ i, IsOpen (V i) := fun i => hWo _ i.1.2
  obtain ⟨ψ, hψ⟩ := SmoothPartitionOfUnity.exists_isSubordinate I hC'c.isClosed V hVo (by
    intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.1 (ht hx)
    exact mem_iUnion.2 ⟨⟨i, hi⟩, hxi⟩)
  have hKψ : ∀ i : ι, ∃ Kψ : ℝ≥0, LipschitzWith Kψ (ψ i) := by
    intro i
    have hcs : HasCompactSupport (ψ i) :=
      (hWc _ i.1.2).of_isClosed_subset (isClosed_tsupport _) ((hψ i).trans subset_closure)
    exact exists_lipschitzWith_of_contMDiff_hasCompactSupport_finite g hr hnorm (ψ i).contMDiff hcs
  choose Kψ hKψ using hKψ
  set Ks : ℝ := ∑ i, (Kψ i : ℝ) with hKs
  have hKs0 : 0 ≤ Ks := Finset.sum_nonneg fun i _ => (Kψ i).coe_nonneg
  set η : ℝ := min (e / 2) (ε' / (Ks + 1)) with hηdef
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hηKs : η * Ks ≤ ε' := by
    have h1 : η ≤ ε' / (Ks + 1) := min_le_right _ _
    have h2 : η * Ks ≤ ε' / (Ks + 1) * Ks := mul_le_mul_of_nonneg_right h1 hKs0
    have h3 : ε' / (Ks + 1) * Ks ≤ ε' := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    linarith
  have happ' : ∀ i : ι, ∃ f' : M → ℝ, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f' (V i) ∧
      (∀ x ∈ V i, |f' x - f x| ≤ η) ∧
      (∀ x ∈ V i, ∀ x' ∈ V i, |(f' x - f x) - (f' x' - f x')| ≤ Ld * dist x x') ∧
      (∀ x ∈ V i, ∀ x' ∈ V i, |f' x - f' x'| ≤ La * dist x x') :=
    fun i => happ i.1.1 i.1.2 η hη
  choose fi hfism hficl hfid hfia using happ'
  have hsum1 : ∀ x ∈ C', ∑ i, ψ i x = 1 := fun x hx => by
    rw [← finsum_eq_sum_of_fintype]; exact ψ.sum_eq_one hx
  have hsumle : ∀ x, ∑ i, ψ i x ≤ 1 := fun x => by
    rw [← finsum_eq_sum_of_fintype]; exact ψ.sum_le_one x
  have hzero : ∀ i x, x ∉ V i → ψ i x = 0 := fun i x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hψ i h))
  have hmemV : ∀ i x, ψ i x ≠ 0 → x ∈ V i := fun i x hx =>
    hψ i (subset_tsupport _ hx)
  let F : M → ℝ := fun x => f x + ∑ i, ψ i x * (fi i x - f x)
  -- the adapted neighbourhood, with both cases recorded
  have hnbhd' : ∀ x, ∃ Vx ∈ 𝓝 x, ∀ i, ∀ y ∈ Vx,
      (x ∈ tsupport (ψ i) → y ∈ V i) ∧ (x ∉ tsupport (ψ i) → ψ i y = 0) := by
    intro x
    refine ⟨⋂ i, (if x ∈ tsupport (ψ i) then V i else (tsupport (ψ i))ᶜ),
      Filter.iInter_mem.mpr fun i => ?_, fun i y hy => ⟨fun hi => ?_, fun hi => ?_⟩⟩
    · split_ifs with h
      · exact (hVo i).mem_nhds (hψ i h)
      · exact (isClosed_tsupport _).isOpen_compl.mem_nhds h
    · have := mem_iInter.1 hy i
      simpa only [hi, ite_true] using this
    · have := mem_iInter.1 hy i
      simp only [hi, ite_false] at this
      exact image_eq_zero_of_notMem_tsupport this
  -- the per-index two-point estimates
  have hterm : ∀ x, ∃ Vx ∈ 𝓝 x, ∀ y ∈ Vx, ∀ y' ∈ Vx, ∀ i,
      |ψ i y * (fi i y - f y) - ψ i y' * (fi i y' - f y')| ≤
        ψ i y * (Ld * dist y y') + Kψ i * dist y y' * η ∧
      ψ i y * |fi i y - fi i y'| ≤ ψ i y * (La * dist y y') ∧
      |(ψ i y - ψ i y') * (fi i y' - f y')| ≤ Kψ i * dist y y' * η := by
    intro x
    obtain ⟨Vx, hVx, hcase⟩ := hnbhd' x
    refine ⟨Vx, hVx, fun y hy y' hy' i => ?_⟩
    have hd := dist_nonneg (x := y) (y := y')
    have hψy := ψ.nonneg i y
    have hKd : |ψ i y - ψ i y'| ≤ Kψ i * dist y y' := by
      rw [← Real.dist_eq]; exact (hKψ i).dist_le_mul y y'
    by_cases hx : x ∈ tsupport (ψ i)
    · have hyV := (hcase i y hy).1 hx
      have hy'V := (hcase i y' hy').1 hx
      have h1 := hfid i y hyV y' hy'V
      have h2 := hficl i y' hy'V
      have h3 := hfia i y hyV y' hy'V
      have hsplit : ψ i y * (fi i y - f y) - ψ i y' * (fi i y' - f y') =
          ψ i y * ((fi i y - f y) - (fi i y' - f y')) + (ψ i y - ψ i y') * (fi i y' - f y') := by
        ring
      have hprod : |(ψ i y - ψ i y') * (fi i y' - f y')| ≤ Kψ i * dist y y' * η := by
        rw [abs_mul]
        exact mul_le_mul hKd h2 (abs_nonneg _) (by positivity)
      refine ⟨?_, mul_le_mul_of_nonneg_left h3 hψy, hprod⟩
      rw [hsplit]
      refine (abs_add_le _ _).trans (add_le_add ?_ hprod)
      rw [abs_mul, abs_of_nonneg hψy]
      exact mul_le_mul_of_nonneg_left h1 hψy
    · have hz := (hcase i y hy).2 hx
      have hz' := (hcase i y' hy').2 hx
      refine ⟨?_, ?_, ?_⟩
      · rw [hz, hz']; simp only [zero_mul, sub_zero, abs_zero]; positivity
      · rw [hz]; simp
      · rw [hz, hz']; simp only [sub_zero, zero_mul, abs_zero]; positivity
  refine ⟨F, interior C', isOpen_interior, hCC', ?_, ?_, ?_, ?_, ?_⟩
  · -- smoothness where the partition sums to one
    have hG : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => ∑ᶠ i, ψ i x • fi i x) :=
      ψ.contMDiff_finsum_smul fun i x hx =>
        (hfism i).contMDiffAt ((hVo i).mem_nhds (hψ i hx))
    refine hG.contMDiffOn.congr fun x hx => ?_
    have h1 := hsum1 x (interior_subset hx)
    simp only [F, finsum_eq_sum_of_fintype, smul_eq_mul, mul_sub, Finset.sum_sub_distrib,
      ← Finset.sum_mul, h1, one_mul]
    ring
  · intro x
    have hle : |∑ i, ψ i x * (fi i x - f x)| ≤ ∑ i, ψ i x * η := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [abs_mul, abs_of_nonneg (ψ.nonneg i x)]
      by_cases h : ψ i x = 0
      · rw [h]; simp
      · exact mul_le_mul_of_nonneg_left (hficl i x (hmemV i x h)) (ψ.nonneg i x)
    have hle2 : ∑ i, ψ i x * η ≤ η := by
      rw [← Finset.sum_mul]
      nlinarith [hsumle x]
    have hηe : η < e := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    simp only [F, add_sub_cancel_left]
    linarith
  · intro x hx
    have : ∀ i, ψ i x = 0 := fun i => hzero i x (fun h => hx (hWU _ i.1.2 h))
    simp only [F, this, zero_mul, Finset.sum_const_zero, add_zero]
  · -- the Lipschitz difference
    have hL : LipschitzWith (Real.toNNReal (Ld + ε')) (fun x => F x - f x) := by
      refine lipschitzWith_of_locally_of_segments
        (exists_riemannian_segment_of_isRiemannianManifold I) fun x => ?_
      obtain ⟨Vx, hVx, hest⟩ := hterm x
      refine ⟨Vx, hVx, fun y hy y' hy' => ?_⟩
      rw [Real.coe_toNNReal _ (by positivity)]
      have hd := dist_nonneg (x := y) (y := y')
      simp only [F, add_sub_cancel_left]
      rw [← Finset.sum_sub_distrib]
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      refine (Finset.sum_le_sum fun i _ => (hest y hy y' hy' i).1).trans ?_
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
      have h1 := hsumle y
      have h2 : (∑ i, ψ i y) * (Ld * dist y y') ≤ Ld * dist y y' := by
        have := mul_le_mul_of_nonneg_right h1 (mul_nonneg hLd hd)
        linarith
      have h3 : (∑ i, (Kψ i : ℝ)) * dist y y' * η ≤ ε' * dist y y' := by
        rw [← hKs]
        nlinarith
      nlinarith
    intro x y
    have := hL.dist_le_mul x y
    rwa [Real.dist_eq, Real.coe_toNNReal _ (by positivity)] at this
  · -- the Lipschitz bound of `F`
    have hL : LipschitzWith (Real.toNNReal (max (K : ℝ) La + ε')) F := by
      refine lipschitzWith_of_locally_of_segments
        (exists_riemannian_segment_of_isRiemannianManifold I) fun x => ?_
      obtain ⟨Vx, hVx, hest⟩ := hterm x
      refine ⟨Vx, hVx, fun y hy y' hy' => ?_⟩
      have hmax : 0 ≤ max (K : ℝ) La := le_max_of_le_left K.coe_nonneg
      rw [Real.coe_toNNReal _ (by positivity)]
      have hd := dist_nonneg (x := y) (y := y')
      have hS := hsumle y
      have hS0 : 0 ≤ ∑ i, ψ i y := Finset.sum_nonneg fun i _ => ψ.nonneg i y
      have hfy : |f y - f y'| ≤ K * dist y y' := by
        rw [← Real.dist_eq]; exact hf.dist_le_mul y y'
      have hexp : F y - F y' = (1 - ∑ i, ψ i y) * (f y - f y') +
          ∑ i, ψ i y * (fi i y - fi i y') + ∑ i, (ψ i y - ψ i y') * (fi i y' - f y') := by
        simp only [F, mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
        ring
      have hA : |(1 - ∑ i, ψ i y) * (f y - f y')| ≤ (1 - ∑ i, ψ i y) * (max (K : ℝ) La * dist y y') := by
        rw [abs_mul, abs_of_nonneg (by linarith)]
        exact mul_le_mul_of_nonneg_left (hfy.trans (mul_le_mul_of_nonneg_right
          (le_max_left _ _) hd)) (by linarith)
      have hB : |∑ i, ψ i y * (fi i y - fi i y')| ≤ (∑ i, ψ i y) * (max (K : ℝ) La * dist y y') := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        rw [Finset.sum_mul]
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_of_nonneg (ψ.nonneg i y)]
        exact ((hest y hy y' hy' i).2.1).trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (le_max_right _ _) hd) (ψ.nonneg i y))
      have hC3 : |∑ i, (ψ i y - ψ i y') * (fi i y' - f y')| ≤ ε' * dist y y' := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        refine (Finset.sum_le_sum fun i _ => (hest y hy y' hy' i).2.2).trans ?_
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← hKs]
        nlinarith
      rw [hexp]
      calc |(1 - ∑ i, ψ i y) * (f y - f y') + ∑ i, ψ i y * (fi i y - fi i y') +
            ∑ i, (ψ i y - ψ i y') * (fi i y' - f y')|
          ≤ |(1 - ∑ i, ψ i y) * (f y - f y')| + |∑ i, ψ i y * (fi i y - fi i y')| +
            |∑ i, (ψ i y - ψ i y') * (fi i y' - f y')| := abs_add_three _ _ _
        _ ≤ (1 - ∑ i, ψ i y) * (max (K : ℝ) La * dist y y') +
            (∑ i, ψ i y) * (max (K : ℝ) La * dist y y') + ε' * dist y y' := by linarith
        _ = (max (K : ℝ) La + ε') * dist y y' := by ring
    intro x y
    have := hL.dist_le_mul x y
    rwa [Real.dist_eq, Real.coe_toNNReal _ (by positivity)] at this

end DifferentialGeometry.Geometry.Collapse
