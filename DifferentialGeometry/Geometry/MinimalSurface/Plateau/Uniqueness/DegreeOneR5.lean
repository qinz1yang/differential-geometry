import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Uniqueness.SheetContinuationR5
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.Uniqueness.DiskAutomorphismR5
import Mathlib.MeasureTheory.Function.Jacobian

/-!
# O-MY-R5 G2：R5-B(ii) degree-one factor rigidity

输入是 G3 的输出形状：`φ` 在 `D°` 上全纯 ∨ 反全纯，`φ(D°) ⊆ D_r`，`U = V ∘ φ`，外加 R2 等面积
`A(U, D°) ≤ A(V, D_r)` 与 properness（`u(∂D) ⊆ Γ`、`q⁻¹(Γ) ⊆ rS¹`）。
* `surjOn_of_proper_R5`：开映射 + properness ⇒ `φ(D°) = D_r`；
* `injOn_of_area_R5`（**degree one**）：若 `φ z₁ = φ z₂`（`z₁ ≠ z₂`），两块不交开集的像在 `w` 附近重叠，
  面积重数给 `A(U, D°) ≥ A(V, D_r) + A(V, O) > A(V, D_r)`——与 R2 矛盾。用的是 D-3 "边界次数 1"的面积版
  （设计文档 §3 的偏差说明），不需要 Blaschke 理论或边界正则性；
* `degree_one_factor_rigidity_R5`：再接 G2a（盘自同构 ⇒ Möbius），得 `φ = r · mob(a, c)` 或
  `φ = r · mob(a, c) ∘ conj`。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Function Metric Manifold DifferentialGeometry MeasureTheory ComplexConjugate
open DifferentialGeometry.Topology DifferentialGeometry.Analysis
open scoped Topology ContDiff Manifold NNReal ENNReal

namespace DifferentialGeometry.Geometry

/-- 全纯 ∨ 反全纯 ⇒ `C^∞`（实意义）。 -/
theorem contDiffOn_of_analytic_or_conj_R5 {φ : ℂ → ℂ} {D : Set ℂ}
    (han : AnalyticOnNhd ℂ φ D ∨ AnalyticOnNhd ℂ (fun z => Complex.conjCLE (φ z)) D) :
    ContDiffOn ℝ ∞ φ D := by
  rcases han with h | h
  · exact ((h.contDiffOn_of_completeSpace (n := ∞)).restrict_scalars ℝ)
  · have h1 : ContDiffOn ℝ ∞ (fun z => Complex.conjCLE (φ z)) D :=
      (h.contDiffOn_of_completeSpace (n := ∞)).restrict_scalars ℝ
    have h2 := (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).contDiff.comp_contDiffOn h1
    refine h2.congr fun z _ => ?_
    simp

/-- 全纯 ∨ 反全纯且非常值 ⇒ 开映射。 -/
theorem isOpen_image_of_analytic_or_conj_R5 {φ : ℂ → ℂ} {D : Set ℂ} (hDc : IsPreconnected D)
    (han : AnalyticOnNhd ℂ φ D ∨ AnalyticOnNhd ℂ (fun z => Complex.conjCLE (φ z)) D)
    {z₁ z₂ : ℂ} (hz₁ : z₁ ∈ D) (hz₂ : z₂ ∈ D) (hne : φ z₁ ≠ φ z₂) :
    ∀ s ⊆ D, IsOpen s → IsOpen (φ '' s) := by
  rcases han with h | h
  · rcases h.is_constant_or_isOpen hDc with ⟨w, hw⟩ | hop
    · exact absurd ((hw z₁ hz₁).trans (hw z₂ hz₂).symm) hne
    · exact hop
  · rcases h.is_constant_or_isOpen hDc with ⟨w, hw⟩ | hop
    · exfalso
      apply hne
      have := (hw z₁ hz₁).trans (hw z₂ hz₂).symm
      exact (starRingEnd ℂ).injective (by simpa using this)
    · intro s hs hso
      have h1 := hop s hs hso
      have himg : φ '' s =
          (Complex.conjCLE : ℂ ≃L[ℝ] ℂ) '' ((fun z => Complex.conjCLE (φ z)) '' s) := by
        rw [image_image]
        apply image_congr
        intro z _
        simp
      rw [himg]
      exact (Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toHomeomorph.isOpenMap _ h1

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M]

/-- **满射（properness）**：`φ` 开映射到 `D_r`，且 `∂D` 处极限满足 `V w ∈ Γ ⇒ ‖w‖ = r` ⇒ `φ(D°) ⊇ D_r`。 -/
theorem surjOn_of_proper_R5 [T2Space M] {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {Γ : freeLoop M} {u q : C(closedDisk, M)} (hu : IsMorreyDisk g Γ u) {r : ℝ} (hr1 : r < 1)
    (hfiber : ∀ w ∈ closedBall (0 : ℂ) 1, diskExtension q w ∈ range Γ → ‖w‖ = r)
    {φ : ℂ → ℂ} (hcont : ContinuousOn φ (ball 0 1))
    (hopen : ∀ s ⊆ ball (0 : ℂ) 1, IsOpen s → IsOpen (φ '' s))
    (hmaps : MapsTo φ (ball 0 1) (ball 0 r))
    (hfac : ∀ z ∈ ball (0 : ℂ) 1, diskExtension u z = diskExtension q (φ z)) :
    SurjOn φ (ball 0 1) (ball 0 r) := by
  have hSo : IsOpen (φ '' ball 0 1) := hopen _ subset_rfl isOpen_ball
  have hne : (ball (0 : ℂ) r ∩ φ '' ball 0 1).Nonempty :=
    ⟨φ 0, hmaps (mem_ball_self one_pos), 0, mem_ball_self one_pos, rfl⟩
  refine (convex_ball (0 : ℂ) r).isPreconnected.subset_of_closure_inter_subset hSo hne ?_
  rintro w ⟨hwcl, hwr⟩
  have hwB : w ∈ closedBall (0 : ℂ) 1 :=
    mem_closedBall_zero_iff.mpr (le_of_lt (lt_trans (mem_ball_zero_iff.mp hwr) hr1))
  obtain ⟨y, hyS, hylim⟩ := mem_closure_iff_seq_limit.mp hwcl
  choose x hxB hxy using hyS
  obtain ⟨z, hzK, k, hk, hxlim⟩ := (isCompact_closedBall (0 : ℂ) 1).tendsto_subseq
    (fun n => ball_subset_closedBall (hxB n))
  have hylim' : Tendsto (fun n => φ (x (k n))) atTop (𝓝 w) :=
    (hylim.comp hk.tendsto_atTop).congr fun n => (hxy (k n)).symm
  rcases eq_or_lt_of_le (mem_closedBall_zero_iff.mp hzK) with hz1 | hz1
  · exfalso
    have hUc : Continuous (diskExtension u) :=
      u.continuous.comp diskRetraction_lipschitz.continuous
    have hVc : Continuous (diskExtension q) :=
      q.continuous.comp diskRetraction_lipschitz.continuous
    have hval : diskExtension u z = diskExtension q w :=
      tendsto_nhds_unique (((hUc.tendsto z).comp hxlim).congr fun n => hfac _ (hxB (k n)))
        ((hVc.tendsto w).comp hylim')
    have hmem := diskExtension_mem_range_of_norm_eq_one_R5 hu hz1
    rw [hval] at hmem
    exact (ne_of_lt (mem_ball_zero_iff.mp hwr)) (hfiber w hwB hmem)
  · have hzB : z ∈ ball (0 : ℂ) 1 := mem_ball_zero_iff.mpr hz1
    have hcz : ContinuousAt φ z := hcont.continuousAt (isOpen_ball.mem_nhds hzB)
    have : φ z = w := tendsto_nhds_unique ((hcz.tendsto).comp hxlim) hylim'
    exact ⟨z, hzB, this⟩

omit [FiniteDimensional ℝ E] in
/-- 面积的容斥不等式：开集 `T₁ T₂`、可积 ⇒ `A(T₁ ∪ T₂) + A(T₁ ∩ T₂) = A(T₁) + A(T₂)`。 -/
theorem riemannianArea_union_add_inter_R5 (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {V : ℂ → M}
    {T₁ T₂ : Set ℂ} (h₁ : MeasurableSet T₁) (h₂ : MeasurableSet T₂)
    (hi₁ : IntegrableOn (riemannianAreaDensity g V) T₁)
    (hi₂ : IntegrableOn (riemannianAreaDensity g V) T₂) :
    riemannianArea g V (T₁ ∪ T₂) + riemannianArea g V (T₁ ∩ T₂) =
      riemannianArea g V T₁ + riemannianArea g V T₂ := by
  unfold riemannianArea
  have hU : T₁ ∪ T₂ = T₁ ∪ (T₂ \ T₁) := union_sdiff_self.symm
  rw [hU, setIntegral_union disjoint_sdiff_right (h₂.diff h₁) hi₁ (hi₂.mono_set sdiff_subset)]
  have h := integral_inter_add_sdiff (μ := volume) (f := riemannianAreaDensity g V) h₁ hi₂
  rw [inter_comm] at h
  linarith

/-- **degree one（面积重数）**：`φ` 全纯 ∨ 反全纯、`φ(D°) ⊆ D_r`、`U = V ∘ φ`、`A(U, D°) ≤ A(V, D_r)`
⇒ `φ` 在 `D°` 上单射。 -/
theorem injOn_of_area_R5 [T3Space M] {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {γ Γ : freeLoop M} {q u : C(closedDisk, M)} (hq : IsMorreyDisk g γ q)
    (hVrank : ∀ W ∈ ball (0 : ℂ) 1,
      Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) W))
    {CV : ℝ≥0} (hVLip : ∀ x y, riemannianEDistOf g (diskExtension q x) (diskExtension q y) ≤
      (CV : ℝ≥0∞) * edist x y)
    {r : ℝ} (hr1 : r < 1) (hu : IsMorreyDisk g Γ u) (hΓ : IsSmoothEmbeddedLoop (E := E) Γ)
    {CU : ℝ≥0} (hULip : ∀ x y, riemannianEDistOf g (diskExtension u x) (diskExtension u y) ≤
      (CU : ℝ≥0∞) * edist x y)
    (hArea : riemannianArea g (diskExtension u) (ball 0 1) ≤
      riemannianArea g (diskExtension q) (ball 0 r))
    {φ : ℂ → ℂ}
    (han : AnalyticOnNhd ℂ φ (ball 0 1) ∨
      AnalyticOnNhd ℂ (fun z => Complex.conjCLE (φ z)) (ball 0 1))
    (hmaps : MapsTo φ (ball 0 1) (ball 0 r))
    (hsurj : SurjOn φ (ball 0 1) (ball 0 r))
    (hopen : ∀ s ⊆ ball (0 : ℂ) 1, IsOpen s → IsOpen (φ '' s))
    (hfac : ∀ z ∈ ball (0 : ℂ) 1, diskExtension u z = diskExtension q (φ z)) :
    InjOn φ (ball 0 1) := by
  classical
  set U : ℂ → M := diskExtension u with hUdef
  set V : ℂ → M := diskExtension q with hVdef
  set D : Set ℂ := ball (0 : ℂ) 1 with hD
  set R : Set ℂ := {z : ℂ | z ∈ ball (0 : ℂ) 1 ∧
      Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z)} with hR
  have hRo : IsOpen R := isOpen_morrey_regular_R5 hu hΓ
  have hBc : (ball (0 : ℂ) 1 \ R).Countable := countable_morrey_branch_R5 hu hΓ
  have hφcd : ContDiffOn ℝ ∞ φ D := contDiffOn_of_analytic_or_conj_R5 han
  have hUint : ∀ s : Set ℂ, Bornology.IsBounded s → IntegrableOn (riemannianAreaDensity g U) s :=
    fun s hs => integrableOn_density_of_bounded_R5 g hULip hs
  have hVint : ∀ s : Set ℂ, Bornology.IsBounded s → IntegrableOn (riemannianAreaDensity g V) s :=
    fun s hs => integrableOn_density_of_bounded_R5 g hVLip hs
  -- 正则点处 `dφ` 单射
  have hdφ : ∀ z ∈ R, Injective (fderiv ℝ φ z) := by
    intro z hz
    have hVd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) V (φ z) :=
      (hq.smoothInterior.contMDiffAt (isOpen_ball.mem_nhds
        (ball_subset_ball hr1.le (hmaps hz.1)))).mdifferentiableAt (by simp)
    exact injective_fderiv_of_local_factor_R5 isOpen_ball hz.1 hφcd hfac hVd hz.2
  -- 开集上的面积下界
  have hAreaLB : ∀ A : Set ℂ, IsOpen A → A ⊆ R →
      riemannianArea g V (φ '' A) ≤ riemannianArea g U A := by
    intro A hAo hAR
    have hAB : A ⊆ D := fun z hz => (hAR hz).1
    have hdens : ∀ z ∈ A, riemannianAreaDensity g (V ∘ φ) z = riemannianAreaDensity g U z := by
      intro z hz
      apply riemannianAreaDensity_congr g
      filter_upwards [isOpen_ball.mem_nhds (hAB hz)] with z' hz'
      exact (hfac z' hz').symm
    have hint : IntegrableOn (riemannianAreaDensity g (V ∘ φ)) A :=
      (hUint A (isBounded_ball.subset hAB)).congr_fun (fun z hz => (hdens z hz).symm)
        hAo.measurableSet
    have hloc : ∀ x ∈ A, ∃ W ∈ 𝓝 x, ∃ K L : ℝ≥0, LipschitzOnWith K φ W ∧
        ∀ y ∈ W, ∀ z ∈ W, edist y z ≤ (L : ℝ≥0∞) * edist (φ y) (φ z) := fun x hx =>
      exists_localBiLip_of_contDiffAt_R5 ((hφcd x (hAB hx)).contDiffAt
        (isOpen_ball.mem_nhds (hAB hx))) (hdφ x (hAR hx))
    have hbd : Bornology.IsBounded (φ '' A) :=
      isBounded_ball.subset ((image_mono hAB).trans (mapsTo_iff_image_subset.mp hmaps))
    have h2 := riemannianArea_image_le_R5 g hVLip hAo hbd hint
      (hφcd.continuousOn.mono hAB) hloc
    have h3 : riemannianArea g (V ∘ φ) A = riemannianArea g U A := by
      unfold riemannianArea
      exact setIntegral_congr_fun hAo.measurableSet hdens
    linarith
  intro z₁ hz₁ z₂ hz₂ heq
  by_contra hne
  have hd : 0 < ‖z₁ - z₂‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hne)
  -- 小球
  obtain ⟨ε₁, hε₁, hε₁sub⟩ := Metric.isOpen_iff.mp isOpen_ball z₁ hz₁
  obtain ⟨ε₂, hε₂, hε₂sub⟩ := Metric.isOpen_iff.mp isOpen_ball z₂ hz₂
  set ε : ℝ := min (min (ε₁ / 2) (ε₂ / 2)) (‖z₁ - z₂‖ / 3) with hε
  have hεpos : 0 < ε := lt_min (lt_min (half_pos hε₁) (half_pos hε₂)) (by positivity)
  have hεd : ε ≤ ‖z₁ - z₂‖ / 3 := min_le_right _ _
  have hε1 : ε < ε₁ := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _))
    (half_lt_self hε₁)
  have hε2 : ε < ε₂ := lt_of_le_of_lt ((min_le_left _ _).trans (min_le_right _ _))
    (half_lt_self hε₂)
  have hB₁ : ball z₁ ε ⊆ D := (ball_subset_ball hε1.le).trans hε₁sub
  have hB₂ : closedBall z₂ ε ⊆ D := (closedBall_subset_ball hε2).trans hε₂sub
  set A₁ : Set ℂ := (D \ closedBall z₂ ε) ∩ R with hA₁
  set A₂ : Set ℂ := ball z₂ ε ∩ R with hA₂
  have hA₁o : IsOpen A₁ := (isOpen_ball.sdiff isClosed_closedBall).inter hRo
  have hA₂o : IsOpen A₂ := isOpen_ball.inter hRo
  have hA₁R : A₁ ⊆ R := inter_subset_right
  have hA₂R : A₂ ⊆ R := inter_subset_right
  have hA₁D : A₁ ⊆ D := fun x hx => hx.1.1
  have hA₂D : A₂ ⊆ D := fun x hx => hB₂ (ball_subset_closedBall hx.1)
  have hdisj : Disjoint A₁ A₂ := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    exact hx1.1.2 (ball_subset_closedBall hx2.1)
  have hB₁A : ∀ x ∈ ball z₁ ε, x ∈ R → x ∈ A₁ := by
    intro x hx hxR
    refine ⟨⟨hB₁ hx, fun hx2 => ?_⟩, hxR⟩
    rw [mem_ball, dist_eq_norm] at hx
    rw [mem_closedBall, dist_eq_norm] at hx2
    have : ‖z₁ - z₂‖ ≤ ‖z₁ - x‖ + ‖x - z₂‖ := by
      calc ‖z₁ - z₂‖ = ‖(z₁ - x) + (x - z₂)‖ := by ring_nf
        _ ≤ _ := norm_add_le _ _
    have h1 : ‖z₁ - x‖ = ‖x - z₁‖ := norm_sub_rev _ _
    linarith
  -- 源面积
  have hsrc : riemannianArea g U A₁ + riemannianArea g U A₂ ≤ riemannianArea g U D := by
    unfold riemannianArea
    rw [← setIntegral_union hdisj hA₂o.measurableSet (hUint _ (isBounded_ball.subset hA₁D))
      (hUint _ (isBounded_ball.subset hA₂D))]
    apply setIntegral_mono_set (hUint _ isBounded_ball)
    · exact Filter.Eventually.of_forall fun z => riemannianAreaDensity_nonneg g _ z
    · exact Filter.Eventually.of_forall (union_subset hA₁D hA₂D)
  -- 像
  have hT₁o : IsOpen (φ '' A₁) := hopen _ hA₁D hA₁o
  have hT₂o : IsOpen (φ '' A₂) := hopen _ hA₂D hA₂o
  have hTr : ∀ A ⊆ D, φ '' A ⊆ ball (0 : ℂ) r := fun A hA =>
    (image_mono hA).trans (mapsTo_iff_image_subset.mp hmaps)
  have hN₀ : volume (φ '' (D \ R)) = 0 := (hBc.image φ).measure_zero volume
  have hsph : sphere z₂ ε ⊆ D := sphere_subset_closedBall.trans hB₂
  have hN₁ : volume (φ '' sphere z₂ ε) = 0 :=
    addHaar_image_eq_zero_of_differentiableOn_of_addHaar_eq_zero volume
      ((hφcd.differentiableOn (by simp)).mono hsph) (Measure.addHaar_sphere volume z₂ ε)
  have hcov : ∀ y ∈ ball (0 : ℂ) r, y ∉ φ '' (D \ R) → y ∉ φ '' sphere z₂ ε →
      y ∈ φ '' A₁ ∪ φ '' A₂ := by
    intro y hy hy0 hy1
    obtain ⟨z, hzD, rfl⟩ := hsurj hy
    have hzR : z ∈ R := by
      by_contra hzR
      exact hy0 ⟨z, ⟨hzD, hzR⟩, rfl⟩
    by_cases hzc : z ∈ closedBall z₂ ε
    · rcases lt_or_eq_of_le (mem_closedBall.mp hzc) with hlt | heq'
      · exact Or.inr ⟨z, ⟨mem_ball.mpr hlt, hzR⟩, rfl⟩
      · exact absurd ⟨z, mem_sphere.mpr heq', rfl⟩ hy1
    · exact Or.inl ⟨z, ⟨⟨hzD, hzc⟩, hzR⟩, rfl⟩
  set O : Set ℂ := φ '' ball z₁ ε ∩ φ '' ball z₂ ε with hO
  have hOo : IsOpen O := (hopen _ hB₁ isOpen_ball).inter
    (hopen _ (ball_subset_closedBall.trans hB₂) isOpen_ball)
  have hwO : φ z₁ ∈ O := ⟨⟨z₁, mem_ball_self hεpos, rfl⟩, ⟨z₂, mem_ball_self hεpos, heq.symm⟩⟩
  have hOI : ∀ y ∈ O, y ∉ φ '' (D \ R) → y ∈ φ '' A₁ ∩ φ '' A₂ := by
    rintro y ⟨⟨x₁, hx₁, rfl⟩, ⟨x₂, hx₂, hx₂eq⟩⟩ hy0
    have hx₁R : x₁ ∈ R := by
      by_contra h
      exact hy0 ⟨x₁, ⟨hB₁ hx₁, h⟩, rfl⟩
    have hx₂R : x₂ ∈ R := by
      by_contra h
      exact hy0 ⟨x₂, ⟨hB₂ (ball_subset_closedBall hx₂), h⟩, hx₂eq⟩
    exact ⟨⟨x₁, hB₁A x₁ hx₁ hx₁R, rfl⟩, ⟨x₂, ⟨hx₂, hx₂R⟩, hx₂eq⟩⟩
  -- 目标面积
  have hT₁b : Bornology.IsBounded (φ '' A₁) := isBounded_ball.subset (hTr _ hA₁D)
  have hT₂b : Bornology.IsBounded (φ '' A₂) := isBounded_ball.subset (hTr _ hA₂D)
  have hTU : riemannianArea g V (ball 0 r) ≤ riemannianArea g V (φ '' A₁ ∪ φ '' A₂) := by
    unfold riemannianArea
    apply setIntegral_mono_set (hVint _ (hT₁b.union hT₂b))
    · exact Filter.Eventually.of_forall fun z => riemannianAreaDensity_nonneg g _ z
    · filter_upwards [measure_eq_zero_iff_ae_notMem.mp hN₀,
        measure_eq_zero_iff_ae_notMem.mp hN₁] with y hy0 hy1 hy
      exact hcov y hy hy0 hy1
  have hTI : riemannianArea g V O ≤ riemannianArea g V (φ '' A₁ ∩ φ '' A₂) := by
    unfold riemannianArea
    apply setIntegral_mono_set (hVint _ (hT₁b.subset inter_subset_left))
    · exact Filter.Eventually.of_forall fun z => riemannianAreaDensity_nonneg g _ z
    · filter_upwards [measure_eq_zero_iff_ae_notMem.mp hN₀] with y hy0 hy
      exact hOI y hy hy0
  have hOB : O ⊆ D := fun y hy => ball_subset_ball hr1.le (hTr _ hB₁ hy.1)
  have hOpos : 0 < riemannianArea g V O := by
    obtain ⟨δ, hδ, hδsub⟩ := Metric.isOpen_iff.mp hOo _ hwO
    have hK : closedBall (φ z₁) (δ / 2) ⊆ O :=
      (closedBall_subset_ball (half_lt_self hδ)).trans hδsub
    have hpos : 0 < riemannianArea g V (closedBall (φ z₁) (δ / 2)) :=
      riemannianArea_pos_of_injective_mfderiv g isOpen_ball (hq.smoothInterior.of_le (by simp))
        (isCompact_closedBall _ _) (hK.trans hOB)
        (by
          rw [interior_closedBall _ (half_pos hδ).ne']
          exact mem_ball_self (half_pos hδ))
        (hVrank _ (hOB hwO))
    have hle : riemannianArea g V (closedBall (φ z₁) (δ / 2)) ≤ riemannianArea g V O := by
      unfold riemannianArea
      apply setIntegral_mono_set (hVint _ (isBounded_ball.subset hOB))
      · exact Filter.Eventually.of_forall fun z => riemannianAreaDensity_nonneg g _ z
      · exact Filter.Eventually.of_forall hK
    linarith
  have hIE := riemannianArea_union_add_inter_R5 g hT₁o.measurableSet hT₂o.measurableSet
    (hVint _ hT₁b) (hVint _ hT₂b)
  have hLB₁ := hAreaLB A₁ hA₁o hA₁R
  have hLB₂ := hAreaLB A₂ hA₂o hA₂R
  linarith

/-- Möbius 的共轭：`conj (mob(a, c)(z)) = mob(ā, c̄)(z̄)`。 -/
theorem conj_diskMobius_R5 (a c z : ℂ) :
    conj (diskMobius_R5 a c z) = diskMobius_R5 (conj a) (conj c) (conj z) := by
  simp [diskMobius_R5, map_div₀, map_mul, map_sub]

/-- **G2（R5-B(ii) degree-one factor rigidity）**：G3 输出形状的因子 `φ`（全纯 ∨ 反全纯，`φ(D°) ⊆ D_r`，
`U = V ∘ φ`）在 R2 等面积与 properness 下是 `r · mob(a, c)` 或 `r · mob(a, c) ∘ conj`。 -/
theorem degree_one_factor_rigidity_R5 [T3Space M] {g : SmoothRiemannianMetric 𝓘(ℝ, E) M}
    {γ Γ : freeLoop M} {q u : C(closedDisk, M)} (hq : IsMorreyDisk g γ q)
    (hVrank : ∀ W ∈ ball (0 : ℂ) 1,
      Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) W))
    {CV : ℝ≥0} (hVLip : ∀ x y, riemannianEDistOf g (diskExtension q x) (diskExtension q y) ≤
      (CV : ℝ≥0∞) * edist x y)
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1)
    (hfiber : ∀ w ∈ closedBall (0 : ℂ) 1, diskExtension q w ∈ range Γ → ‖w‖ = r)
    (hu : IsMorreyDisk g Γ u) (hΓ : IsSmoothEmbeddedLoop (E := E) Γ)
    {CU : ℝ≥0} (hULip : ∀ x y, riemannianEDistOf g (diskExtension u x) (diskExtension u y) ≤
      (CU : ℝ≥0∞) * edist x y)
    (hArea : riemannianArea g (diskExtension u) (ball 0 1) ≤
      riemannianArea g (diskExtension q) (ball 0 r))
    {φ : ℂ → ℂ}
    (han : AnalyticOnNhd ℂ φ (ball 0 1) ∨
      AnalyticOnNhd ℂ (fun z => Complex.conjCLE (φ z)) (ball 0 1))
    (hmaps : MapsTo φ (ball 0 1) (ball 0 r))
    (hfac : ∀ z ∈ ball (0 : ℂ) 1, diskExtension u z = diskExtension q (φ z)) :
    ∃ a c : ℂ, ‖a‖ < 1 ∧ ‖c‖ = 1 ∧
      ((∀ z ∈ ball (0 : ℂ) 1, φ z = (r : ℂ) * diskMobius_R5 a c z) ∨
        (∀ z ∈ ball (0 : ℂ) 1, φ z = (r : ℂ) * diskMobius_R5 a c (conj z))) := by
  have hφcd : ContDiffOn ℝ ∞ φ (ball 0 1) := contDiffOn_of_analytic_or_conj_R5 han
  -- 非常值：正则点处 `dφ` 单射
  obtain ⟨z, hzD, hzR⟩ := nonempty_inter_morrey_regular_R5 hu hΓ isOpen_ball
    ⟨0, mem_ball_self one_pos⟩ subset_rfl
  have hVd : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (diskExtension q) (φ z) :=
    (hq.smoothInterior.contMDiffAt (isOpen_ball.mem_nhds
      (ball_subset_ball hr1.le (hmaps hzD)))).mdifferentiableAt (by simp)
  have hdz := injective_fderiv_of_local_factor_R5 isOpen_ball hzD hφcd hfac hVd hzR.2
  have hnc : ∃ z' ∈ ball (0 : ℂ) 1, φ z' ≠ φ z := by
    by_contra hcon
    push Not at hcon
    have hloc : φ =ᶠ[𝓝 z] fun _ => φ z :=
      Filter.eventually_of_mem (isOpen_ball.mem_nhds hzD) hcon
    have h0 : fderiv ℝ φ z = 0 := by
      rw [hloc.fderiv_eq]
      exact fderiv_const_apply _
    have := hdz (a₁ := 1) (a₂ := 0) (by rw [h0]; simp)
    exact one_ne_zero this
  obtain ⟨z', hz'D, hz'ne⟩ := hnc
  have hopen := isOpen_image_of_analytic_or_conj_R5 (convex_ball (0 : ℂ) 1).isPreconnected han
    hz'D hzD hz'ne
  have hsurj := surjOn_of_proper_R5 hu hr1 hfiber hφcd.continuousOn hopen hmaps hfac
  have hinj := injOn_of_area_R5 hq hVrank hVLip hr1 hu hΓ hULip hArea han hmaps hsurj hopen hfac
  have hr0' : (r : ℂ) ≠ 0 := by exact_mod_cast hr0.ne'
  have hscale : ∀ w : ℂ, w ∈ ball (0 : ℂ) r ↔ (r : ℂ)⁻¹ * w ∈ ball (0 : ℂ) 1 := by
    intro w
    rw [mem_ball_zero_iff, mem_ball_zero_iff, norm_mul, norm_inv, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hr0, inv_mul_lt_iff₀ hr0, mul_one]
  rcases han with h | h
  · let ψ : ℂ → ℂ := fun z => (r : ℂ)⁻¹ * φ z
    have hψd : DifferentiableOn ℂ ψ (ball 0 1) :=
      (h.differentiableOn).const_mul _
    have hψm : MapsTo ψ (ball 0 1) (ball 0 1) := fun z hz => (hscale _).mp (hmaps hz)
    have hψi : InjOn ψ (ball 0 1) := by
      intro x hx y hy hxy
      apply hinj hx hy
      have := congrArg (fun w => (r : ℂ) * w) hxy
      simpa [ψ, ← mul_assoc, mul_inv_cancel₀ hr0'] using this
    have hψs : SurjOn ψ (ball 0 1) (ball 0 1) := by
      intro w hw
      have hw' : (r : ℂ) * w ∈ ball (0 : ℂ) r := by
        rw [hscale]
        simpa [← mul_assoc, inv_mul_cancel₀ hr0'] using hw
      obtain ⟨x, hx, hxw⟩ := hsurj hw'
      exact ⟨x, hx, by simp [ψ, hxw, ← mul_assoc, inv_mul_cancel₀ hr0']⟩
    obtain ⟨a, c, ha, hc, heq⟩ := diskMobius_of_bijOn_ball_R5 hψd hψm hψi hψs
    refine ⟨a, c, ha, hc, Or.inl fun z hz => ?_⟩
    have := heq hz
    simp only [ψ] at this
    rw [← this, ← mul_assoc, mul_inv_cancel₀ hr0', one_mul]
  · let ψ : ℂ → ℂ := fun z => (r : ℂ)⁻¹ * Complex.conjCLE (φ z)
    have hψd : DifferentiableOn ℂ ψ (ball 0 1) :=
      (h.differentiableOn).const_mul _
    have hnorm : ∀ w : ℂ, ‖Complex.conjCLE w‖ = ‖w‖ := fun w => by simp
    have hψm : MapsTo ψ (ball 0 1) (ball 0 1) := by
      intro z hz
      apply (hscale _).mp
      rw [mem_ball_zero_iff, hnorm]
      exact mem_ball_zero_iff.mp (hmaps hz)
    have hψi : InjOn ψ (ball 0 1) := by
      intro x hx y hy hxy
      apply hinj hx hy
      have h1 := congrArg (fun w => (r : ℂ) * w) hxy
      simp only [ψ, ← mul_assoc, mul_inv_cancel₀ hr0', one_mul] at h1
      exact Complex.conjCLE.injective h1
    have hψs : SurjOn ψ (ball 0 1) (ball 0 1) := by
      intro w hw
      have hw' : conj ((r : ℂ) * w) ∈ ball (0 : ℂ) r := by
        rw [mem_ball_zero_iff, Complex.norm_conj, ← mem_ball_zero_iff, hscale]
        simpa [← mul_assoc, inv_mul_cancel₀ hr0'] using hw
      obtain ⟨x, hx, hxw⟩ := hsurj hw'
      refine ⟨x, hx, ?_⟩
      simp only [ψ, hxw, Complex.conjCLE_apply, Complex.conj_conj, ← mul_assoc,
        inv_mul_cancel₀ hr0', one_mul]
    obtain ⟨a, c, ha, hc, heq⟩ := diskMobius_of_bijOn_ball_R5 hψd hψm hψi hψs
    refine ⟨conj a, conj c, by simpa using ha, by simpa using hc, Or.inr fun z hz => ?_⟩
    have h1 := heq hz
    simp only [ψ] at h1
    have h2 : Complex.conjCLE (φ z) = (r : ℂ) * diskMobius_R5 a c z := by
      rw [← h1, ← mul_assoc, mul_inv_cancel₀ hr0', one_mul]
    have h3 : φ z = conj ((r : ℂ) * diskMobius_R5 a c z) := by
      rw [← h2, Complex.conjCLE_apply, Complex.conj_conj]
    rw [h3, map_mul, Complex.conj_ofReal, conj_diskMobius_R5]

end DifferentialGeometry.Geometry
