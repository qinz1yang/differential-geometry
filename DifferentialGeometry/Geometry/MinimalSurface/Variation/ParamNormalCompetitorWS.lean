import DifferentialGeometry.Geometry.MinimalSurface.Plateau.MorreyDisk
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.SmoothExtension
import DifferentialGeometry.Geometry.MinimalSurface.Plateau.DiskDifferential
import DifferentialGeometry.Geometry.Measure.Area.Manifold
import DifferentialGeometry.Geometry.Measure.Area.Positivity
import DifferentialGeometry.Geometry.Connection.SourceSectionPairing
import DifferentialGeometry.Geometry.Metric.SourceTangentSmooth
import DifferentialGeometry.Geometry.Metric.ParameterTangentMap
import DifferentialGeometry.Geometry.MinimalSurface.Variation.ParamAreaCalculusWS
import DifferentialGeometry.Geometry.MinimalSurface.Variation.ParamNormalFamilyWS

/-!
# S-W-STAB G1：Morrey attainer 沿 parametrized 法向变分的 `area_variation_nonneg_WS`

`u`（Morrey disk 的光滑到边界延拓 `U`）在光滑竞争者类
`{v | DiskSmoothUpToBoundary v ∧ DiskWeakJordanTrace γ v ∧ range v ⊆ W}` 里面积极小（显式参数 `hmin`）。
`F : ℝ × ℂ → M` 是 `U` 在 regular part `N`（`⊆` 开单位盘）里 `K = tsupport φ` 上的光滑变分、`K` 外不动：

* `exists_competitor_WS`：`v_t := (z ↦ if z ∈ K then F(t, z) else U z)` 在闭盘上光滑、弱 Jordan trace 不变、
  range 仍在 `W` 内，且 `Area(v_t) = ∫_{D̄ ∖ K} dens(U) + ∫_K dens(F_t)`；
* `area_variation_nonneg_of_family_WS`：generic family 版；`a(t)` 在 `0` 局部极小 ⇒
  `∫_K ∂_t dens(F_t) = 0`、`0 ≤ ∫_K ∂_t² dens(F_t)`（`ParamAreaCalculusWS`）；
* `area_variation_nonneg_WS`：`F` 取 `ParamNormalFamilyWS` 的 geodesic 变分 `exp_{U z}(t φ ν)`。

没有 embedding / injectivity / `mfderiv` 全盘单射假设：`hi` 只在 `N` 上（immersion on regular part）。
-/

set_option autoImplicit false
noncomputable section

open Bundle Filter Manifold Set MeasureTheory DifferentialGeometry DifferentialGeometry.Topology
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
theorem riemannianArea_split_WS (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {Ut : ℂ → M} {s : Set ℂ}
    (hs : IsOpen s) (hUt : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ Ut s)
    (hDs : Metric.closedBall (0 : ℂ) 1 ⊆ s) {K : Set ℂ} (hK : IsCompact K)
    (hKcb : K ⊆ Metric.closedBall (0 : ℂ) 1) :
    riemannianArea g Ut (Metric.closedBall (0 : ℂ) 1) =
      (∫ z in Metric.closedBall (0 : ℂ) 1 \ K, riemannianAreaDensity g Ut z) +
        ∫ z in K, riemannianAreaDensity g Ut z := by
  have hint : IntegrableOn (riemannianAreaDensity g Ut) (Metric.closedBall (0 : ℂ) 1) :=
    ((continuousOn_riemannianAreaDensity g hs (hUt.of_le (by simp))).mono hDs).integrableOn_compact
      (isCompact_closedBall 0 1)
  unfold riemannianArea
  rw [setIntegral_sdiff hK.measurableSet hint hKcb]
  ring

omit [FiniteDimensional ℝ E] in
theorem exists_competitor_WS (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (W : Set M) (γ : freeLoop M)
    {u : C(closedDisk, M)} {U : ℂ → M} (hExt : SmoothDiskExtension (E := E) u U)
    (hW : Set.range u ⊆ W) (htr : DiskWeakJordanTrace γ u)
    (N : TopologicalSpace.Opens ℂ) (hNball : (N : Set ℂ) ⊆ Metric.ball 0 1)
    {F : ℝ × ℂ → M} {V : Set (ℝ × ℂ)}
    (hF : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, E) ∞ F V)
    {K : Set ℂ} (hKN : K ⊆ N)
    (htriv : ∀ z ∈ N, z ∉ K → ∀ t : ℝ, (t, z) ∈ V ∧ F (t, z) = U z)
    {t : ℝ} (htV : ∀ z ∈ K, (t, z) ∈ V) (htW : ∀ z ∈ K, F (t, z) ∈ W)
    (hK : IsCompact K) :
    ∃ v : C(closedDisk, M), DiskSmoothUpToBoundary (E := E) v ∧ DiskWeakJordanTrace γ v ∧
      Set.range v ⊆ W ∧
      riemannianDiskArea g v =
        (∫ z in Metric.closedBall (0 : ℂ) 1 \ K, riemannianAreaDensity g U z) +
          ∫ z in K, riemannianAreaDensity g (fun y => F (t, y)) z := by
  classical
  obtain ⟨heq, s, hs, hDs, hUs⟩ := hExt
  let Ut : ℂ → M := fun z => if z ∈ K then F (t, z) else U z
  have htN (z : ℂ) (hz : z ∈ N) : (t, z) ∈ V := by
    by_cases hzK : z ∈ K
    · exact htV z hzK
    · exact (htriv z hz hzK t).1
  have hUtN (z : ℂ) (hz : z ∈ N) : Ut z = F (t, z) := by
    by_cases hzK : z ∈ K
    · simp only [Ut, hzK, ↓reduceIte]
    · simp only [Ut, hzK, ↓reduceIte]
      exact ((htriv z hz hzK t).2).symm
  have hUtK (z : ℂ) (hz : z ∉ K) : Ut z = U z := by
    simp only [Ut, hz, ↓reduceIte]
  have hslice : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ (fun y : ℂ => F (t, y)) (N : Set ℂ) :=
    hF.comp (contMDiff_const.prodMk contMDiff_id).contMDiffOn (fun z hz => htN z hz)
  have hUtN' : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ Ut (N : Set ℂ) :=
    hslice.congr (fun z hz => hUtN z hz)
  have hUts : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ Ut s := by
    apply contMDiffOn_of_locally_contMDiffOn
    intro z hz
    by_cases hzK : z ∈ K
    · exact ⟨N, N.isOpen, hKN hzK, hUtN'.mono inter_subset_right⟩
    · refine ⟨Kᶜ, hK.isClosed.isOpen_compl, hzK, ?_⟩
      exact (hUs.mono inter_subset_left).congr (fun y hy => hUtK y hy.2)
  have hcont : Continuous (fun z : closedDisk => Ut z) :=
    (hUts.continuousOn.mono hDs).comp_continuous continuous_subtype_val
      (fun z => z.property)
  let v : C(closedDisk, M) := ⟨fun z => Ut z, hcont⟩
  have hvext (z : ℂ) (hz : z ∈ Metric.closedBall (0 : ℂ) 1) : diskExtension v z = Ut z :=
    diskExtension_coe v ⟨z, hz⟩
  refine ⟨v, ?_, ?_, ?_, ?_⟩
  · exact (hUts.mono hDs).congr (fun z hz => hvext z hz)
  · obtain ⟨σ, hσ, htr'⟩ := htr
    refine ⟨σ, hσ, ?_⟩
    rw [← htr']
    ext θ
    have hnorm : ‖((diskBoundary θ : closedDisk) : ℂ)‖ = 1 := by simp [diskBoundary]
    have hbd : ((diskBoundary θ : closedDisk) : ℂ) ∉ K := by
      intro hmem
      have h := Metric.mem_ball.mp (hNball (hKN hmem))
      rw [dist_zero_right, hnorm] at h
      exact lt_irrefl _ h
    change Ut (diskBoundary θ : ℂ) = u (diskBoundary θ)
    rw [hUtK _ hbd]
    exact heq (diskBoundary θ)
  · rintro _ ⟨z, rfl⟩
    by_cases hzK : (z : ℂ) ∈ K
    · change Ut z ∈ W
      rw [hUtN z (hKN hzK)]
      exact htW z hzK
    · change Ut z ∈ W
      rw [hUtK z hzK, heq z]
      exact hW (mem_range_self z)
  · have hKcb : K ⊆ Metric.closedBall (0 : ℂ) 1 :=
      hKN.trans (hNball.trans Metric.ball_subset_closedBall)
    rw [riemannianDiskArea_eq_of_extension g v Ut (fun z => rfl),
      riemannianArea_split_WS g hs hUts hDs hK hKcb]
    congr 1
    · apply setIntegral_congr_fun (measurableSet_closedBall.diff hK.measurableSet)
      intro z hz
      exact riemannianAreaDensity_congr g
        (Filter.eventually_of_mem (hK.isClosed.isOpen_compl.mem_nhds hz.2)
          (fun y hy => hUtK y hy))
    · apply setIntegral_congr_fun hK.measurableSet
      intro z hz
      exact riemannianAreaDensity_congr g
        (Filter.eventually_of_mem (N.isOpen.mem_nhds (hKN hz)) (fun y hy => hUtN y hy))

omit [FiniteDimensional ℝ E] in
/-- **G1（generic family 版）.**  `q = u` 在光滑竞争者类里面积极小，`F` 是 `U` 的紧支撑光滑变分族
（`K` 外不动）⇒ `a(t) = Area(v_t)` 在 `0` 局部极小 ⇒ 密度的一阶导积分为 `0`、二阶导积分 `≥ 0`。 -/
theorem area_variation_nonneg_of_family_WS (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (W : Set M)
    (γ : freeLoop M) {u : C(closedDisk, M)} {U : ℂ → M}
    (hExt : SmoothDiskExtension (E := E) u U)
    (hW : Set.range u ⊆ W) (htr : DiskWeakJordanTrace γ u)
    (hmin : ∀ v : C(closedDisk, M), DiskSmoothUpToBoundary (E := E) v →
      DiskWeakJordanTrace γ v → Set.range v ⊆ W → riemannianDiskArea g u ≤ riemannianDiskArea g v)
    (N : TopologicalSpace.Opens ℂ) (hNball : (N : Set ℂ) ⊆ Metric.ball 0 1)
    (hi : ∀ z ∈ N, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z))
    {F : ℝ × ℂ → M} {V : Set (ℝ × ℂ)} (hV : IsOpen V)
    (h0V : ∀ z ∈ N, ((0 : ℝ), z) ∈ V) (hF : ContMDiffOn 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) ∞ F V)
    (hF0 : ∀ z ∈ N, F (0, z) = U z)
    {K : Set ℂ} (hK : IsCompact K) (hKN : K ⊆ N) (hint : ∀ z ∈ K, U z ∈ interior W)
    (htriv : ∀ z ∈ N, z ∉ K → ∀ t : ℝ, (t, z) ∈ V ∧ F (t, z) = U z) :
    IntegrableOn
        (fun z => deriv (deriv (fun t => riemannianAreaDensity g (fun y => F (t, y)) z)) 0) K ∧
      IntegrableOn (fun z => deriv (fun t => riemannianAreaDensity g (fun y => F (t, y)) z) 0) K ∧
      (∫ z in K, deriv (fun t => riemannianAreaDensity g (fun y => F (t, y)) z) 0 = 0) ∧
      0 ≤ ∫ z in K, deriv (deriv (fun t => riemannianAreaDensity g (fun y => F (t, y)) z)) 0 := by
  classical
  have hExt' := hExt
  obtain ⟨heq, s, hs, hDs, hUs⟩ := hExt
  have hFprod : ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, E) ∞ F V := by
    have h := hF
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at h
    exact h
  let P : ℂ → ℝ × ℂ → E := fun a p => (mfderiv 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) F p (0, a) : E)
  have hPreg (a : ℂ) : ContMDiffOn 𝓘(ℝ, ℝ × ℂ) (𝓘(ℝ, E).prod 𝓘(ℝ, E)) ∞
      (fun p => TotalSpace.mk' E (F p) (mfderiv 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) F p (0, a))) V :=
    contMDiffOn_source_partial hV hF (m := ∞) (by simp) (0, a)
  let G : ℝ × ℂ → ℝ := fun p =>
    g.inner (F p) (P 1 p) (P 1 p) * g.inner (F p) (P Complex.I p) (P Complex.I p) -
      g.inner (F p) (P 1 p) (P Complex.I p) ^ 2
  have hpair (a b : ℂ) : ContDiffOn ℝ ∞ (fun p => g.inner (F p) (P a p) (P b p)) V :=
    contDiffOn_sourceSectionPairing g hF (hPreg a) (hPreg b)
  have hG : ContDiffOn ℝ ∞ G V :=
    ((hpair 1 1).mul (hpair Complex.I Complex.I)).sub ((hpair 1 Complex.I).pow 2)
  have hFd (p : ℝ × ℂ) (hp : p ∈ V) :
      MDifferentiableAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℂ)) 𝓘(ℝ, E) F p :=
    ((hFprod p hp).contMDiffAt (hV.mem_nhds hp)).mdifferentiableAt (by simp)
  have hspace (t : ℝ) (q : ℂ) (hp : (t, q) ∈ V) (a : ℂ) :
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) (fun y => F (t, y)) q a : E) = P a (t, q) := by
    have h := mfderiv_parameter_slice (hFd (t, q) hp) a
    rwa [← modelWithCornersSelf_prod, chartedSpaceSelf_prod] at h
  have hdens (p : ℝ × ℂ) (hp : p ∈ V) :
      riemannianAreaDensity g (fun y => F (p.1, y)) p.2 = Real.sqrt (G p) := by
    unfold riemannianAreaDensity tangentTwoJacobian
    rw [hspace p.1 p.2 hp 1, hspace p.1 p.2 hp Complex.I]
  have hG0 (z : ℂ) (hz : z ∈ N) : 0 < G (0, z) := by
    have h1 : 0 < riemannianAreaDensity g U z :=
      riemannianAreaDensity_pos_of_injective_mfderiv g (hi z hz)
    have h2 : riemannianAreaDensity g (fun y => F (0, y)) z = riemannianAreaDensity g U z :=
      riemannianAreaDensity_congr g
        (Filter.eventually_of_mem (N.isOpen.mem_nhds hz) (fun y hy => hF0 y hy))
    have h3 := hdens (0, z) (h0V z hz)
    have h4 : 0 < Real.sqrt (G (0, z)) := by
      rw [← h3]
      exact h2 ▸ h1
    exact Real.sqrt_pos.mp h4
  let Ω₁ : Set (ℝ × ℂ) := V ∩ G ⁻¹' Ioi 0
  have hΩ₁ : IsOpen Ω₁ := hG.continuousOn.isOpen_inter_preimage hV isOpen_Ioi
  let Ω₂ : Set (ℝ × ℂ) := V ∩ F ⁻¹' interior W
  have hΩ₂ : IsOpen Ω₂ := hF.continuousOn.isOpen_inter_preimage hV isOpen_interior
  have hΩ : IsOpen (Ω₁ ∩ Ω₂) := hΩ₁.inter hΩ₂
  have h0Ω : ({0} : Set ℝ) ×ˢ K ⊆ Ω₁ ∩ Ω₂ := by
    rintro ⟨t, z⟩ ⟨ht, hz⟩
    have ht0 : t = 0 := ht
    subst ht0
    refine ⟨⟨h0V z (hKN hz), hG0 z (hKN hz)⟩, h0V z (hKN hz), ?_⟩
    change F (0, z) ∈ interior W
    rw [hF0 z (hKN hz)]
    exact hint z hz
  obtain ⟨T, v, hTo, hvo, h0T, hKv, hTv⟩ :=
    generalized_tube_lemma isCompact_singleton hK hΩ h0Ω
  have h0T' : (0 : ℝ) ∈ T := h0T (mem_singleton 0)
  have hTK (t : ℝ) (ht : t ∈ T) (z : ℂ) (hz : z ∈ K) : (t, z) ∈ Ω₁ ∩ Ω₂ :=
    hTv ⟨ht, hKv hz⟩
  let f : ℝ × ℂ → ℝ := fun p => riemannianAreaDensity g (fun y => F (p.1, y)) p.2
  have hf : ContDiffOn ℝ ∞ f Ω₁ :=
    ((hG.mono inter_subset_left).sqrt (fun p hp => ne_of_gt hp.2)).congr
      (fun p hp => hdens p hp.1)
  have hsub : T ×ˢ K ⊆ Ω₁ := fun p hp => (hTK p.1 hp.1 p.2 hp.2).1
  have hKcb : K ⊆ Metric.closedBall (0 : ℂ) 1 :=
    hKN.trans (hNball.trans Metric.ball_subset_closedBall)
  let C : ℝ := ∫ z in Metric.closedBall (0 : ℂ) 1 \ K, riemannianAreaDensity g U z
  have harea0 : riemannianDiskArea g u = C + ∫ z in K, f (0, z) := by
    rw [riemannianDiskArea_eq_of_extension g u U heq,
      riemannianArea_split_WS g hs hUs hDs hK hKcb]
    congr 1
    apply setIntegral_congr_fun hK.measurableSet
    intro z hz
    exact (riemannianAreaDensity_congr g
      (Filter.eventually_of_mem (N.isOpen.mem_nhds (hKN hz)) (fun y hy => hF0 y hy))).symm
  have hlocmin : IsLocalMin (fun t => C + ∫ z in K, f (t, z)) 0 := by
    refine Filter.eventually_of_mem (hTo.mem_nhds h0T') (fun t ht => ?_)
    have htV : ∀ z ∈ K, (t, z) ∈ V := fun z hz => (hTK t ht z hz).1.1
    have htW : ∀ z ∈ K, F (t, z) ∈ W := fun z hz => interior_subset (hTK t ht z hz).2.2
    obtain ⟨vt, hvs, hvt, hvW, hvarea⟩ :=
      exists_competitor_WS g W γ hExt' hW htr N hNball hFprod hKN htriv htV htW hK
    have hle := hmin vt hvs hvt hvW
    rw [hvarea] at hle
    change C + ∫ z in K, f (0, z) ≤ C + ∫ z in K, f (t, z)
    rw [← harea0]
    exact hle
  exact integral_second_nonneg_of_isLocalMin_WS hK hTo hΩ₁ hsub hf h0T' C hlocmin

open Riemannian.CovariantDerivativeAlong in
/-- **G1 `area_variation_nonneg_WS`.**  Morrey attainer `u` 在光滑竞争者类
`{v | DiskSmoothUpToBoundary v ∧ DiskWeakJordanTrace γ v ∧ range v ⊆ W}` 里面积极小（显式参数 `hmin`），
`N ⊆` 开单位盘是 `U` 的 regular part（immersion），`φ ∈ C_c^∞(N)`：存在 geodesic 变分
`F(t, z) = exp_{U z}(t φ ν)`（`ParamNormalFamilyWS`）使得面积函数 `a(t) = Area(v_t)` 在 `0` 局部极小，
从而 `∫_K ∂_t dens = 0`、`0 ≤ ∫_K ∂_t² dens`（`K = tsupport φ`）。 -/
theorem area_variation_nonneg_WS [T2Space M] (hdim : Module.finrank ℝ E = 3)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (W : Set M) (γ : freeLoop M)
    {u : C(closedDisk, M)} {U : ℂ → M} (hExt : SmoothDiskExtension (E := E) u U)
    (hW : Set.range u ⊆ W) (htr : DiskWeakJordanTrace γ u)
    (hmin : ∀ v : C(closedDisk, M), DiskSmoothUpToBoundary (E := E) v →
      DiskWeakJordanTrace γ v → Set.range v ⊆ W → riemannianDiskArea g u ≤ riemannianDiskArea g v)
    (N : TopologicalSpace.Opens ℂ) (hNball : (N : Set ℂ) ⊆ Metric.ball 0 1)
    (hi : ∀ z ∈ N, Function.Injective (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U z))
    (hint : ∀ z ∈ N, U z ∈ interior W)
    (ν : ∀ q : N, TangentSpace 𝓘(ℝ, E) (U q))
    (hν : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, E).tangent) ∞
      (fun q : N => (⟨U q, ν q⟩ : TangentBundle 𝓘(ℝ, E) M)))
    (φ : N → ℝ) (hφ : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞ φ) (hφc : HasCompactSupport φ) :
    ∃ (F : ℝ × ℂ → M) (V : Set (ℝ × ℂ)), IsOpen V ∧ (∀ z ∈ N, ((0 : ℝ), z) ∈ V) ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) ∞ F V ∧ (∀ z ∈ N, F (0, z) = U z) ∧
      (∀ (z : ℂ) (hz : z ∈ N),
        (mfderiv 𝓘(ℝ, ℝ × ℂ) 𝓘(ℝ, E) F (0, z) (1, 0) : E) =
          φ ⟨z, hz⟩ • (ν ⟨z, hz⟩ : E)) ∧
      (∀ z ∈ N, covDerivAlong g (fun s : ℝ => F (s, z))
        (fun s => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) (fun r : ℝ => F (r, z)) s (1 : ℝ)) 0 = 0) ∧
      (∀ (z : ℂ) (hz : z ∈ N), φ ⟨z, hz⟩ = 0 → ∀ t : ℝ, (t, z) ∈ V ∧ F (t, z) = U z) ∧
      IntegrableOn
        (fun z => deriv (deriv (fun t => riemannianAreaDensity g (fun y => F (t, y)) z)) 0)
          (Subtype.val '' tsupport φ) ∧
      IntegrableOn (fun z => deriv (fun t => riemannianAreaDensity g (fun y => F (t, y)) z) 0)
          (Subtype.val '' tsupport φ) ∧
      (∫ z in Subtype.val '' tsupport φ,
        deriv (fun t => riemannianAreaDensity g (fun y => F (t, y)) z) 0 = 0) ∧
      0 ≤ ∫ z in Subtype.val '' tsupport φ,
        deriv (deriv (fun t => riemannianAreaDensity g (fun y => F (t, y)) z)) 0 := by
  obtain ⟨F, V, hV, hVN, h0V, hFsm, hF0, hvel, hacc, htriv⟩ :=
    exists_normalGeodesicFamily_WS hdim g N U ν hν φ hφ
  have hK : IsCompact (Subtype.val '' tsupport φ) := hφc.image continuous_subtype_val
  have hKN : (Subtype.val '' tsupport φ) ⊆ (N : Set ℂ) := by
    rintro _ ⟨q, _, rfl⟩
    exact q.property
  have htriv' : ∀ z ∈ N, z ∉ (Subtype.val '' tsupport φ) → ∀ t : ℝ,
      (t, z) ∈ V ∧ F (t, z) = U z := by
    intro z hz hzK t
    refine htriv z hz ?_ t
    by_contra hne
    exact hzK ⟨⟨z, hz⟩, subset_tsupport _ (Function.mem_support.mpr hne), rfl⟩
  obtain ⟨h1, h2, h3, h4⟩ := area_variation_nonneg_of_family_WS g W γ hExt hW htr hmin N hNball hi
    hV h0V hFsm hF0 hK hKN (fun z hz => hint z (hKN hz)) htriv'
  exact ⟨F, V, hV, h0V, hFsm, hF0, hvel, hacc, htriv, h1, h2, h3, h4⟩

end DifferentialGeometry.Geometry
