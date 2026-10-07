import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Uniqueness.SheetCoverR5
import DifferentialGeometry.Geometry.Measure.Area.Positivity
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.ConformalHarmonic
import DifferentialGeometry.Analysis.Elliptic.ComplexPlane.HarmonicConformalOrientation
import DifferentialGeometry.Analysis.Complex.StrictRadius

/-!
# O-MY-R5 G3：R5-B(i) proper-sheet continuation（`proper_sheet_continuation_R5`）

`U := diskExtension u`（`u` 是 trace `Γ` 的 Morrey 盘，可有孤立 branch points），`V := diskExtension q`
（`q` Morrey、开盘 rank 2、`coincidentGermPairs q = ∅`（R3b）、`q⁻¹(Γ) ⊆ rS¹`、fiber 有限），
面积 `A(U, D°) ≤ A(V, D_r)`（R2 等面积），以及一个 seed：`U z₀ = V W₀`、`‖W₀‖ < r`、germ `≤`。
结论：存在 `φ`，全纯 ∨ 反全纯于 `D°`，`φ(D°) ⊆ D_r`，`U = V ∘ φ` on `D°`。

D-3 四个缺口的处理（design-R5-uniqueness §2）：
1. germ continuation：`exists_morrey_local_factor_R5`（局部一步）+ `exists_partner_of_mem_closure_R5`（闭性）；
2. monodromy：partner 全局唯一（R3b），`sheetPartner_R5` 单值——不做路径延拓；
3. no escape：partner 限在 `closedBall 0 r ⊆ D°`；crossing `rS¹` 由**面积**排除：
   `A(V, D_r) ≤ A(V, φ(Ω_in)) ≤ A(U, Ω_in)`（`riemannianArea_image_le_R5`）⇒
   `A(U, D° \ Ω_in) ≤ 0`，而 crossing
   点外侧给出 `D° \ Ω_in` 中正面积的闭球；
4. single-valued removability：`exists_differentiableOn_extension_R5`（此时 `φ` 已单值有界）。
副产品：`u(D°) ∩ Γ = ∅`（`φ(D°) ⊆ D_r` 且 `q⁻¹(Γ) ⊆ rS¹`），即 D-3 要求"在调用处生产"的前提。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Function Metric Manifold DifferentialGeometry MeasureTheory
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Topology ContDiff Manifold NNReal ENNReal

namespace DifferentialGeometry.Geometry

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T3Space M]

/-- 全局 Lipschitz ⇒ 面积密度在有界集上可积。 -/
theorem integrableOn_density_of_bounded_R5 (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {U : ℂ → M} {C : ℝ≥0}
    (hU : ∀ x y, riemannianEDistOf g (U x) (U y) ≤ (C : ℝ≥0∞) * edist x y)
    {s : Set ℂ} (hs : Bornology.IsBounded s) : IntegrableOn (riemannianAreaDensity g U) s := by
  have : IsFiniteMeasure (volume.restrict s) :=
    isFiniteMeasure_restrict.mpr hs.measure_lt_top.ne
  exact integrableOn_riemannianAreaDensity_of_lipschitz g hU s

/-- **G3（R5-B(i) proper-sheet continuation）**。 -/
theorem proper_sheet_continuation_R5 {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hd3 : Module.finrank ℝ E = 3) {γ : freeLoop M} {q : C(closedDisk, M)}
    (hq : IsMorreyDisk g γ q)
    (hVrank : ∀ W ∈ ball (0 : ℂ) 1,
      Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) W))
    (hcoin : coincidentGermPairs (q : closedDisk → M) = ∅)
    (hfin : ∀ p : M, ((q : closedDisk → M) ⁻¹' {p}).Finite)
    {CV : ℝ≥0} (hVLip : ∀ x y, riemannianEDistOf g (diskExtension q x) (diskExtension q y) ≤
      (CV : ℝ≥0∞) * edist x y)
    {r : ℝ} (hr1 : r < 1) {Γ : freeLoop M}
    (hfiber : ∀ w ∈ closedBall (0 : ℂ) 1, diskExtension q w ∈ range Γ → ‖w‖ = r)
    {u : C(closedDisk, M)} (hu : IsMorreyDisk g Γ u) (hΓ : IsSmoothEmbeddedLoop (E := E) Γ)
    {CU : ℝ≥0} (hULip : ∀ x y, riemannianEDistOf g (diskExtension u x) (diskExtension u y) ≤
      (CU : ℝ≥0∞) * edist x y)
    (hArea : riemannianArea g (diskExtension u) (ball 0 1) ≤
      riemannianArea g (diskExtension q) (ball 0 r))
    {z₀ W₀ : ℂ} (hz₀ : z₀ ∈ ball (0 : ℂ) 1) (hW₀ : ‖W₀‖ < r)
    (hval₀ : diskExtension u z₀ = diskExtension q W₀)
    (hgerm₀ : Filter.map (diskExtension u) (𝓝 z₀) ≤ Filter.map (diskExtension q) (𝓝 W₀)) :
    ∃ φ : ℂ → ℂ, (AnalyticOnNhd ℂ φ (ball 0 1) ∨
        AnalyticOnNhd ℂ (fun z => Complex.conjCLE (φ z)) (ball 0 1)) ∧
      MapsTo φ (ball 0 1) (ball 0 r) ∧
      ∀ z ∈ ball (0 : ℂ) 1, diskExtension u z = diskExtension q (φ z) := by
  classical
  set U : ℂ → M := diskExtension u with hUdef
  set V : ℂ → M := diskExtension q with hVdef
  set R : Set ℂ := {z : ℂ | z ∈ ball (0 : ℂ) 1 ∧
      Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)} with hR
  set Ω : Set ℂ := {z : ℂ | z ∈ ball (0 : ℂ) 1 ∧
      Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z) ∧
      ∃ W : ℂ, ‖W‖ < r ∧ U z = V W ∧ Filter.map U (𝓝 z) = Filter.map V (𝓝 W)} with hΩ
  set φ := sheetPartner_R5 u q with hφ
  have hr0 : 0 < r := lt_of_le_of_lt (norm_nonneg _) hW₀
  have hr1' : r ≤ 1 := hr1.le
  have hRo : IsOpen R := isOpen_morrey_regular_R5 hu hΓ
  have hBc : (ball (0 : ℂ) 1 \ R).Countable := countable_morrey_branch_R5 hu hΓ
  have hRc : IsPreconnected R := isPreconnected_morrey_regular_R5 hu hΓ
  have hUc : Continuous U := u.continuous.comp diskRetraction_lipschitz.continuous
  have hVc : Continuous V := q.continuous.comp diskRetraction_lipschitz.continuous
  have hprops := fun z (hz : z ∈ Ω) =>
    sheetInside_props_R5 hu hq hVrank hcoin hr1' hRo hz
  have hφΩ : ∀ z ∈ Ω, ‖φ z‖ < r ∧ U z = V (φ z) ∧
      Filter.map U (𝓝 z) = Filter.map V (𝓝 (φ z)) := by
    intro z hz
    obtain ⟨hzB, hzi, W, hWr, hval, hgerm⟩ := hz
    have hWB : W ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (lt_of_lt_of_le hWr hr1')
    have hpW : φ z = W := sheetPartner_eq_R5 hcoin hWB hval hgerm
    rw [hpW]
    exact ⟨hWr, hval, hgerm⟩
  have hΩR : Ω ⊆ R := fun z hz => ⟨hz.1, hz.2.1⟩
  have hΩB : Ω ⊆ ball (0 : ℂ) 1 := fun z hz => hz.1
  have hΩo : IsOpen Ω := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨N, hN, hNΩ, -⟩ := hprops z hz
    exact Filter.mem_of_superset hN hNΩ
  -- 正则 seed
  have hW₀B : W₀ ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (lt_of_lt_of_le hW₀ hr1')
  have hΩne : Ω.Nonempty := by
    obtain ⟨N, Φ, hNo, hz₀N, hNB, -, -, hΦmaps, hfac, hreg⟩ :=
      sheetPartner_local_R5 hu hq hVrank hcoin hz₀ hW₀B hval₀ hgerm₀
        (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hW₀) : ball (0 : ℂ) r ∈ 𝓝 W₀)
    obtain ⟨z₁, hz₁N, hz₁R⟩ := nonempty_inter_morrey_regular_R5 hu hΓ hNo ⟨z₀, hz₀N⟩ hNB
    obtain ⟨-, hg, -, -⟩ := hreg z₁ hz₁N hz₁R.2
    exact ⟨z₁, hz₁R.1, hz₁R.2, Φ z₁, mem_ball_zero_iff.mp (hΦmaps hz₁N).1, hfac z₁ hz₁N, hg⟩
  -- 例外集 `C` 可数
  set C : Set ℂ := closedBall (0 : ℂ) 1 ∩ V ⁻¹' (U '' (ball (0 : ℂ) 1 \ R)) with hC
  have hCc : C.Countable := by
    have h1 : (U '' (ball (0 : ℂ) 1 \ R)).Countable := hBc.image U
    have h2 : C ⊆ ⋃ p ∈ U '' (ball (0 : ℂ) 1 \ R),
        (Subtype.val '' ((q : closedDisk → M) ⁻¹' {p})) := by
      rintro w ⟨hwK, hwV⟩
      refine mem_iUnion₂.mpr ⟨V w, hwV, ⟨w, hwK⟩, ?_, rfl⟩
      change q ⟨w, hwK⟩ = V w
      exact (diskExtension_coe (q : closedDisk → M) ⟨w, hwK⟩).symm
    exact (h1.biUnion fun p _ => ((hfin p).image _).countable).mono h2
  have hcover : ball (0 : ℂ) r \ C ⊆ φ '' Ω :=
    sheetPartner_image_cover_R5 hu hq hd3 hVrank hcoin hr1 hfiber hRo hCc hΩne
  -- 面积
  have hUint : ∀ s : Set ℂ, Bornology.IsBounded s → IntegrableOn (riemannianAreaDensity g U) s :=
    fun s hs => integrableOn_density_of_bounded_R5 g hULip hs
  have hVint : ∀ s : Set ℂ, Bornology.IsBounded s → IntegrableOn (riemannianAreaDensity g V) s :=
    fun s hs => integrableOn_density_of_bounded_R5 g hVLip hs
  have hφr : φ '' Ω ⊆ ball (0 : ℂ) r := by
    rintro _ ⟨z, hz, rfl⟩
    exact mem_ball_zero_iff.mpr (hφΩ z hz).1
  have hdens : ∀ z ∈ Ω, riemannianAreaDensity g (V ∘ φ) z = riemannianAreaDensity g U z := by
    intro z hz
    apply riemannianAreaDensity_congr g
    filter_upwards [hΩo.mem_nhds hz] with z' hz'
    exact (hφΩ z' hz').2.1.symm
  have hAreaΩ : riemannianArea g V (ball 0 r) ≤ riemannianArea g U Ω := by
    have h1 : riemannianArea g V (ball 0 r) ≤ riemannianArea g V (φ '' Ω) := by
      unfold riemannianArea
      apply setIntegral_mono_set (hVint _ (isBounded_ball.subset hφr))
      · exact Filter.Eventually.of_forall fun z => riemannianAreaDensity_nonneg g _ z
      · have hnull : ∀ᵐ x ∂(volume : Measure ℂ), x ∉ C :=
          measure_eq_zero_iff_ae_notMem.mp (hCc.measure_zero _)
        filter_upwards [hnull] with x hx hxB
        exact hcover ⟨hxB, hx⟩
    have hint : IntegrableOn (riemannianAreaDensity g (V ∘ φ)) Ω :=
      (hUint Ω (isBounded_ball.subset hΩB)).congr_fun (fun z hz => (hdens z hz).symm)
        hΩo.measurableSet
    have hcont : ContinuousOn φ Ω := by
      intro z hz
      obtain ⟨N, hN, -, Φ, hΦ, -, -, hφΦ, -, -⟩ := hprops z hz
      have heq : φ =ᶠ[𝓝 z] Φ := Filter.eventually_of_mem hN hφΦ
      exact (hΦ.continuousAt.congr heq.symm).continuousWithinAt
    have hloc : ∀ x ∈ Ω, ∃ W ∈ 𝓝 x, ∃ K L : ℝ≥0, LipschitzOnWith K φ W ∧
        ∀ y ∈ W, ∀ z ∈ W, edist y z ≤ (L : ℝ≥0∞) * edist (φ y) (φ z) := by
      intro x hx
      obtain ⟨N, hN, -, Φ, hΦ, -, hΦi, hφΦ, -, -⟩ := hprops x hx
      obtain ⟨W, hW, K, L, hlip, hlow⟩ := exists_localBiLip_of_contDiffAt_R5 hΦ hΦi
      have hφΦ' : ∀ z' ∈ N, φ z' = Φ z' := hφΦ
      refine ⟨W ∩ N, Filter.inter_mem hW hN, K, L, ?_, ?_⟩
      · intro y hy z hz
        rw [hφΦ' y hy.2, hφΦ' z hz.2]
        exact hlip hy.1 hz.1
      · intro y hy z hz
        rw [hφΦ' y hy.2, hφΦ' z hz.2]
        exact hlow y hy.1 z hz.1
    have h2 := riemannianArea_image_le_R5 g hVLip hΩo (isBounded_ball.subset hφr) hint hcont hloc
    have h3 : riemannianArea g (V ∘ φ) Ω = riemannianArea g U Ω := by
      unfold riemannianArea
      exact setIntegral_congr_fun hΩo.measurableSet hdens
    linarith
  have hAreaOut : riemannianArea g U (ball 0 1 \ Ω) ≤ 0 := by
    have h := setIntegral_sdiff (μ := volume) hΩo.measurableSet (hUint _ isBounded_ball) hΩB
    change riemannianArea g U (ball 0 1 \ Ω) =
      riemannianArea g U (ball 0 1) - riemannianArea g U Ω at h
    linarith
  -- 无 crossing：`closure Ω ∩ R ⊆ Ω`
  have hcl : closure Ω ∩ R ⊆ Ω := by
    rintro z ⟨hzcl, hzR⟩
    obtain ⟨W, hWK, hval, hgerm⟩ :=
      exists_partner_of_mem_closure_R5 hu hq hd3 hVrank hr1 hzR.1 hzR.2 hzcl
    rcases lt_or_eq_of_le (mem_closedBall_zero_iff.mp hWK) with hlt | heq
    · exact ⟨hzR.1, hzR.2, W, hlt, hval, hgerm⟩
    exfalso
    have hWB : W ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr (by rw [heq]; exact hr1)
    obtain ⟨N, Φ, hNo, hzN, hNB, hΦ, hΦz, -, hfac, hreg⟩ :=
      sheetPartner_local_R5 hu hq hVrank hcoin hzR.1 hWB hval hgerm.le Filter.univ_mem
    obtain ⟨-, -, hdi, -⟩ := hreg z hzN hzR.2
    have him := image_mem_nhds_of_contDiffAt_R5 ((hΦ z hzN).contDiffAt (hNo.mem_nhds hzN)) hdi
      (Filter.inter_mem (hNo.mem_nhds hzN) (hRo.mem_nhds hzR))
    rw [hΦz] at him
    obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp him
    set w' : ℂ := ((1 + δ / (2 * r) : ℝ) : ℂ) * W with hw'
    have hδr : 0 < δ / (2 * r) := by positivity
    have hw'B : w' ∈ ball W δ := by
      rw [mem_ball, dist_eq_norm]
      have : w' - W = ((δ / (2 * r) : ℝ) : ℂ) * W := by
        rw [hw']
        push_cast
        ring
      rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδr, heq]
      field_simp
      linarith
    have hw'n : r < ‖w'‖ := by
      rw [hw', norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity), heq]
      nlinarith
    obtain ⟨z', ⟨hz'N, hz'R⟩, hz'eq⟩ := hδsub hw'B
    have hOut : IsOpen ((N ∩ R) ∩ Φ ⁻¹' {w : ℂ | r < ‖w‖}) :=
      (hΦ.continuousOn.mono inter_subset_left).isOpen_inter_preimage (hNo.inter hRo)
        (isOpen_lt continuous_const continuous_norm)
    have hz'out : z' ∈ (N ∩ R) ∩ Φ ⁻¹' {w : ℂ | r < ‖w‖} := by
      refine ⟨⟨hz'N, hz'R⟩, ?_⟩
      change r < ‖Φ z'‖
      rw [hz'eq]
      exact hw'n
    obtain ⟨ε, hε, hεsub⟩ := Metric.isOpen_iff.mp hOut z' hz'out
    have hKsub : closedBall z' (ε / 2) ⊆ ball (0 : ℂ) 1 \ Ω := by
      intro x hx
      have hxo := hεsub (closedBall_subset_ball (half_lt_self hε) hx)
      refine ⟨hNB hxo.1.1, fun hxΩ => ?_⟩
      have h1 := (hφΩ x hxΩ).1
      have h2 : φ x = Φ x := (hreg x hxo.1.1 hxo.1.2.2).1
      have h3 : r < ‖Φ x‖ := hxo.2
      rw [h2] at h1
      linarith
    have hpos : 0 < riemannianArea g U (closedBall z' (ε / 2)) :=
      riemannianArea_pos_of_injective_mfderiv g isOpen_ball (hu.smoothInterior.of_le (by simp))
        (isCompact_closedBall _ _) (fun x hx => (hKsub hx).1)
        (by
          rw [interior_closedBall _ (half_pos hε).ne']
          exact mem_ball_self (half_pos hε))
        hz'R.2
    have hle : riemannianArea g U (closedBall z' (ε / 2)) ≤
        riemannianArea g U (ball 0 1 \ Ω) := by
      unfold riemannianArea
      apply setIntegral_mono_set (hUint _ (isBounded_ball.subset sdiff_subset))
      · exact Filter.Eventually.of_forall fun z => riemannianAreaDensity_nonneg g _ z
      · exact Filter.Eventually.of_forall hKsub
    linarith
  have hRΩ : R ⊆ Ω := by
    obtain ⟨z, hz⟩ := hΩne
    exact hRc.subset_of_closure_inter_subset hΩo ⟨z, hΩR hz, hz⟩ hcl
  -- `φ` 在 `R` 上光滑、共形、有界
  have hφloc : ∀ z ∈ R, ContDiffAt ℝ ∞ φ z ∧ ConformalAt φ z := by
    intro z hz
    obtain ⟨N, hN, -, Φ, hΦ, hΦc, -, hφΦ, -, -⟩ := hprops z (hRΩ hz)
    have heq : φ =ᶠ[𝓝 z] Φ := Filter.eventually_of_mem hN hφΦ
    refine ⟨hΦ.congr_of_eventuallyEq heq, ?_⟩
    exact hΦc.congr (mem_interior_iff_mem_nhds.mpr hN) isOpen_interior
      (fun x hx => hφΦ x (interior_subset hx))
  have hφcd : ContDiffOn ℝ 2 φ R := fun z hz =>
    ((hφloc z hz).1.of_le (by simp)).contDiffWithinAt
  have hharm : InnerProductSpace.HarmonicOnNhd φ R :=
    harmonicOnNhd_of_contDiffOn_of_dense_conformalAt hRo hRo subset_rfl subset_closure hφcd
      (fun z hz => (hφloc z hz).2)
  obtain ⟨z₁, hz₁⟩ := hΩne
  have hz₁R : z₁ ∈ R := hΩR hz₁
  have hor := analyticOnNhd_or_conj_of_harmonicOnNhd_of_eventually_conformalAt hRo hRc hharm hz₁R
    (Filter.eventually_of_mem (hRo.mem_nhds hz₁R) fun z hz => (hφloc z hz).2)
  have hbound : ∀ z ∈ R, ‖φ z‖ ≤ r := fun z hz => (hφΩ z (hRΩ hz)).1.le
  have hdisc : ∀ b ∈ ball (0 : ℂ) 1, ∃ ε > 0, ball b ε ⊆ ball (0 : ℂ) 1 ∧
      ∀ z ∈ ball b ε, z ≠ b → z ∈ R := fun b hb =>
    punctured_subset_morrey_regular_R5 hu hΓ hb
  -- 去掉 branch points（可去）
  obtain ⟨φ', hφ'an, hφ'R⟩ : ∃ φ' : ℂ → ℂ, (AnalyticOnNhd ℂ φ' (ball 0 1) ∨
      AnalyticOnNhd ℂ (fun z => Complex.conjCLE (φ' z)) (ball 0 1)) ∧ ∀ z ∈ R, φ' z = φ z := by
    rcases hor with han | han
    · obtain ⟨f, hf, hfR⟩ := exists_differentiableOn_extension_R5 hRo hdisc han.differentiableOn
        hbound
      exact ⟨f, Or.inl (hf.analyticOnNhd isOpen_ball), hfR⟩
    · obtain ⟨f, hf, hfR⟩ := exists_differentiableOn_extension_R5 hRo hdisc han.differentiableOn
        (C := r) (fun z hz => by
          rw [Complex.conjCLE_apply, Complex.norm_conj]
          exact hbound z hz)
      refine ⟨fun z => Complex.conjCLE (f z), Or.inr ?_, fun z hz => ?_⟩
      · have : (fun z => Complex.conjCLE (Complex.conjCLE (f z))) = f := by
          funext z
          simp
        rw [this]
        exact hf.analyticOnNhd isOpen_ball
      · change Complex.conjCLE (f z) = φ z
        rw [hfR z hz]
        simp
  have hφ'cont : ContinuousOn φ' (ball 0 1) := by
    rcases hφ'an with h | h
    · exact h.continuousOn
    · have h2 := (Complex.conjCLE.continuous.comp_continuousOn h.continuousOn)
      refine h2.congr fun z _ => ?_
      simp
  have hpunct : ∀ b ∈ ball (0 : ℂ) 1, ∀ᶠ z in 𝓝[≠] b, z ∈ R := by
    intro b hb
    obtain ⟨ε, hε, -, hsub⟩ := hdisc b hb
    filter_upwards [nhdsWithin_le_nhds (isOpen_ball.mem_nhds (mem_ball_self hε)),
      self_mem_nhdsWithin] with z hz hzb
    exact hsub z hz hzb
  have hle : ∀ z ∈ ball (0 : ℂ) 1, ‖φ' z‖ ≤ r := by
    intro z hz
    have hcz : ContinuousAt φ' z := hφ'cont.continuousAt (isOpen_ball.mem_nhds hz)
    have hne : (𝓝[≠] z).NeBot := NormedField.nhdsNE_neBot z
    have ht : Tendsto (fun w => ‖φ' w‖) (𝓝[≠] z) (𝓝 ‖φ' z‖) :=
      (hcz.tendsto.mono_left nhdsWithin_le_nhds).norm
    apply le_of_tendsto ht
    filter_upwards [hpunct z hz] with w hw
    rw [hφ'R w hw]
    exact hbound w hw
  have hconf₁ : ConformalAt φ' z₁ :=
    (hφloc z₁ hz₁R).2.congr hz₁R hRo (fun x hx => hφ'R x hx)
  have hlt := norm_lt_of_analyticOnNhd_or_conj_of_conformalAt_of_norm_le isOpen_ball
    (convex_ball (0 : ℂ) 1).isPreconnected hφ'an hz₁R.1 hconf₁ hle
  refine ⟨φ', hφ'an, fun z hz => mem_ball_zero_iff.mpr (hlt z hz), fun z hz => ?_⟩
  by_cases hzR : z ∈ R
  · rw [hφ'R z hzR]
    exact (hφΩ z (hRΩ hzR)).2.1
  · have hcz : ContinuousAt φ' z := hφ'cont.continuousAt (isOpen_ball.mem_nhds hz)
    have h1 : Tendsto U (𝓝[≠] z) (𝓝 (U z)) := (hUc.tendsto z).mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (V ∘ φ') (𝓝[≠] z) (𝓝 (V (φ' z))) :=
      ((hVc.tendsto _).comp hcz.tendsto).mono_left nhdsWithin_le_nhds
    have hne : (𝓝[≠] z).NeBot := NormedField.nhdsNE_neBot z
    have h3 : U =ᶠ[𝓝[≠] z] V ∘ φ' := by
      filter_upwards [hpunct z hz] with w hw
      change U w = V (φ' w)
      rw [hφ'R w hw]
      exact (hφΩ w (hRΩ hw)).2.1
    exact tendsto_nhds_unique (h1.congr' h3) h2

/-- **consumer（D-3 要求在调用处生产的前提）**：G3 的输出给出 `u(D°) ∩ Γ = ∅`——`U z = V (φ z)`、
`‖φ z‖ < r`，而 `q⁻¹(Γ) ⊆ rS¹`。 -/
theorem morrey_interior_avoids_trace_R5 {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    (hd3 : Module.finrank ℝ E = 3) {γ : freeLoop M} {q : C(closedDisk, M)}
    (hq : IsMorreyDisk g γ q)
    (hVrank : ∀ W ∈ ball (0 : ℂ) 1,
      Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) W))
    (hcoin : coincidentGermPairs (q : closedDisk → M) = ∅)
    (hfin : ∀ p : M, ((q : closedDisk → M) ⁻¹' {p}).Finite)
    {CV : ℝ≥0} (hVLip : ∀ x y, riemannianEDistOf g (diskExtension q x) (diskExtension q y) ≤
      (CV : ℝ≥0∞) * edist x y)
    {r : ℝ} (hr1 : r < 1) {Γ : freeLoop M}
    (hfiber : ∀ w ∈ closedBall (0 : ℂ) 1, diskExtension q w ∈ range Γ → ‖w‖ = r)
    {u : C(closedDisk, M)} (hu : IsMorreyDisk g Γ u) (hΓ : IsSmoothEmbeddedLoop (E := E) Γ)
    {CU : ℝ≥0} (hULip : ∀ x y, riemannianEDistOf g (diskExtension u x) (diskExtension u y) ≤
      (CU : ℝ≥0∞) * edist x y)
    (hArea : riemannianArea g (diskExtension u) (ball 0 1) ≤
      riemannianArea g (diskExtension q) (ball 0 r))
    {z₀ W₀ : ℂ} (hz₀ : z₀ ∈ ball (0 : ℂ) 1) (hW₀ : ‖W₀‖ < r)
    (hval₀ : diskExtension u z₀ = diskExtension q W₀)
    (hgerm₀ : Filter.map (diskExtension u) (𝓝 z₀) ≤ Filter.map (diskExtension q) (𝓝 W₀)) :
    ∀ z ∈ ball (0 : ℂ) 1, diskExtension u z ∉ range Γ := by
  obtain ⟨φ, -, hmaps, hfac⟩ := proper_sheet_continuation_R5 hd3 hq hVrank hcoin hfin hVLip hr1
    hfiber hu hΓ hULip hArea hz₀ hW₀ hval₀ hgerm₀
  intro z hz hmem
  have hφ : ‖φ z‖ < r := mem_ball_zero_iff.mp (hmaps hz)
  rw [hfac z hz] at hmem
  have := hfiber (φ z) (mem_closedBall_zero_iff.mpr (hφ.le.trans hr1.le)) hmem
  linarith

end DifferentialGeometry.Geometry
