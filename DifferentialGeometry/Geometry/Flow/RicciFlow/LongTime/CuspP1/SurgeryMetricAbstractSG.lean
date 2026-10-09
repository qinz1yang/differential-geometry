import DifferentialGeometry.Geometry.Metric.QuadraticBounds.Unit
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# 度量比较的抽象引理（G4a，S-A14-SURGERY）

hmetric（`P^* g_t ≤ e^ε g_s` on 紧集）的三个一般性分析零件，在任意 `C^∞` 流形 `M` 上：

* `continuous_tangentMap_family_SG`：`f : ℝ × M → M` 联合光滑 ⇒ `(σ, v) ↦ (f_σ x, d f_σ v)` 在
  `ℝ × TM` 上连续（`ContMDiff.continuous_tangentMap` + `equivTangentBundleProd.symm`）；
* `exists_near_id_quadratic_SG`（"M0"）：`f_{σ₀} = id`、紧 `K` ⇒ `σ → σ₀` 时
  `h(d f_σ u, d f_σ u) ≤ e^ε h(u, u)` 在 `K` 上一致（`MetricUnitTangent` 紧 + tube lemma）；
* `exists_quadratic_close_SG`（"C-cont"）：度量族 `G` 的二次型在 `A ×ˢ univ` 上联合连续，
  `τ₀ ∈ A` ⇒ 紧集上与 `G τ₀` 双向 `e^ε` 接近（`t ∈ A`，`|t - τ₀| < δ`）。
-/

set_option autoImplicit false
noncomputable section
open Set Manifold Bundle DifferentialGeometry
open scoped Manifold ContDiff
namespace GC.LongTime.CuspP1
universe u

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- 联合光滑的参数族的切映射在 `(σ, v)` 上联合连续。 -/
theorem continuous_tangentMap_family_SG [IsManifold I ∞ M] (f : ℝ × M → M)
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ f) :
    Continuous (fun p : ℝ × TangentBundle I M =>
      (TotalSpace.mk' E (f (p.1, p.2.proj))
        (mfderiv I I (fun x => f (p.1, x)) p.2.proj p.2.2) : TangentBundle I M)) := by
  have h1 : Continuous (fun p : ℝ × TangentBundle I M =>
      (equivTangentBundleProd 𝓘(ℝ, ℝ) ℝ I M).symm
        ((TotalSpace.mk' ℝ p.1 (0 : ℝ) : TangentBundle 𝓘(ℝ, ℝ) ℝ), p.2)) := by
    have hσ : Continuous (fun σ : ℝ =>
        (TotalSpace.mk' ℝ σ (0 : ℝ) : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
        (continuous_id.prodMk continuous_const)
    exact (contMDiff_equivTangentBundleProd_symm (n := 0)).continuous.comp
      ((hσ.comp continuous_fst).prodMk continuous_snd)
  have h2 := hf.continuous_tangentMap (by simp)
  refine (h2.comp h1).congr ?_
  rintro ⟨σ, ⟨x, u⟩⟩
  have hd : MDifferentiableAt (𝓘(ℝ, ℝ).prod I) I f (σ, x) := hf.mdifferentiable (by simp) (σ, x)
  have hcomp : mfderiv I I (fun y => f (σ, y)) x =
      (mfderiv (𝓘(ℝ, ℝ).prod I) I f (σ, x)).comp
        (mfderiv I (𝓘(ℝ, ℝ).prod I) (fun y => (σ, y)) x) :=
    mfderiv_comp x hd (mdifferentiableAt_const.prodMk mdifferentiableAt_id)
  rw [mfderiv_prod_right] at hcomp
  change _ = TotalSpace.mk' E (f (σ, x)) (mfderiv I I (fun y => f (σ, y)) x u)
  rw [hcomp]
  rfl

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I 1 M] [T2Space M]

/-- "M0"：`f_{σ₀} = id` 的联合光滑族在紧集上 `σ → σ₀` 时关于固定度量 `h` 的二次型一致地
`≤ e^ε`。 -/
theorem exists_near_id_quadratic_SG (h : SmoothRiemannianMetric I M) (f : ℝ × M → M)
    (hf : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ f) (σ₀ : ℝ) (hid : ∀ x, f (σ₀, x) = x)
    {K : Set M} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ σ, |σ - σ₀| < δ → ∀ x ∈ K, ∀ u : TangentSpace I x,
      h.inner (f (σ, x)) (mfderiv I I (fun y => f (σ, y)) x u)
          (mfderiv I I (fun y => f (σ, y)) x u) ≤ Real.exp ε * h.inner x u u := by
  have hS : IsCompact {p : MetricUnitTangent (I := I) (M := M) h |
      MetricUnitTangent.base (I := I) (M := M) p ∈ K} := metricUnitOn_compact h hK
  have hΨ : Continuous (fun p : ℝ × TangentBundle I M =>
      h.inner (f (p.1, p.2.proj)) (mfderiv I I (fun x => f (p.1, x)) p.2.proj p.2.2)
        (mfderiv I I (fun x => f (p.1, x)) p.2.proj p.2.2)) :=
    (metricQuad_cont h).comp (continuous_tangentMap_family_SG f hf)
  let W : Set (ℝ × MetricUnitTangent (I := I) (M := M) h) :=
    {q | h.inner (f (q.1, q.2.1.proj)) (mfderiv I I (fun x => f (q.1, x)) q.2.1.proj q.2.1.2)
        (mfderiv I I (fun x => f (q.1, x)) q.2.1.proj q.2.1.2) < Real.exp ε}
  have hWo : IsOpen W :=
    isOpen_lt (hΨ.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)))
      continuous_const
  have hsub : ({σ₀} : Set ℝ) ×ˢ {p : MetricUnitTangent (I := I) (M := M) h |
      MetricUnitTangent.base (I := I) (M := M) p ∈ K} ⊆ W := by
    rintro ⟨σ, p⟩ ⟨hσ, -⟩
    rw [mem_singleton_iff] at hσ
    subst hσ
    have hfun : (fun x => f (σ, x)) = id := funext hid
    change h.inner (f (σ, p.1.proj)) (mfderiv I I (fun x => f (σ, x)) p.1.proj p.1.2)
        (mfderiv I I (fun x => f (σ, x)) p.1.proj p.1.2) < Real.exp ε
    rw [hfun, mfderiv_id, hid]
    have h1 : h.inner p.1.proj p.1.2 p.1.2 = 1 := p.2
    simp only [ContinuousLinearMap.id_apply]
    rw [h1]
    exact Real.one_lt_exp_iff.mpr hε
  obtain ⟨u, v, hu, hv, hσu, hSv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton hS hWo hsub
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hu σ₀ (hσu rfl)
  refine ⟨δ, hδ, fun σ hσ x hx w => ?_⟩
  have hσu' : σ ∈ u := hball (by simpa [Real.dist_eq] using hσ)
  by_cases hw : w = 0
  · subst hw
    simp
  have hpos : 0 < h.inner x w w := h.pos x w hw
  set s : ℝ := Real.sqrt (h.inner x w w) with hs_def
  have hs : 0 < s := Real.sqrt_pos.mpr hpos
  have hss : s * s = h.inner x w w := by
    simpa only [hs_def, sq] using Real.sq_sqrt hpos.le
  have hunit : h.inner x (s⁻¹ • w) (s⁻¹ • w) = 1 := by
    rw [metric_smul2]
    field_simp [hs.ne']
    linarith [hss]
  let p : MetricUnitTangent (I := I) (M := M) h := ⟨(TotalSpace.mk' E x (s⁻¹ • w)), hunit⟩
  have hp : MetricUnitTangent.base (I := I) (M := M) p ∈ K := hx
  have hlt : ((σ, p) : ℝ × MetricUnitTangent (I := I) (M := M) h) ∈ W :=
    huv (show ((σ, p) : ℝ × MetricUnitTangent (I := I) (M := M) h) ∈ u ×ˢ v from
      ⟨hσu', hSv hp⟩)
  change h.inner (f (σ, x)) (mfderiv I I (fun y => f (σ, y)) x (s⁻¹ • w))
      (mfderiv I I (fun y => f (σ, y)) x (s⁻¹ • w)) < Real.exp ε at hlt
  rw [map_smul, metric_smul2] at hlt
  have hm := mul_lt_mul_of_pos_right hlt (mul_pos hs hs)
  have hleft : s⁻¹ * s⁻¹ * h.inner (f (σ, x)) (mfderiv I I (fun y => f (σ, y)) x w)
      (mfderiv I I (fun y => f (σ, y)) x w) * (s * s) =
      h.inner (f (σ, x)) (mfderiv I I (fun y => f (σ, y)) x w)
        (mfderiv I I (fun y => f (σ, y)) x w) := by field_simp
  rw [hleft, hss] at hm
  exact hm.le

/-- "C-cont"：度量族 `G` 的二次型在 `A ×ˢ univ` 上联合连续、`τ₀ ∈ A` ⇒ 紧集 `K` 上
`t ∈ A`、`|t - τ₀| < δ` 时与 `G τ₀` 双向 `e^ε` 接近（`δ` 与 `K`、`ε` 有关，对 `x ∈ K`、`v` 一致）。 -/
theorem exists_quadratic_close_SG (G : ℝ → SmoothRiemannianMetric I M) (A : Set ℝ) (τ₀ : ℝ)
    (hτ : τ₀ ∈ A)
    (hcont : ContinuousOn (fun p : ℝ × TangentBundle I M =>
      (G p.1).inner p.2.proj p.2.2 p.2.2) (A ×ˢ univ))
    {K : Set M} (hK : IsCompact K) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ t ∈ A, |t - τ₀| < δ → ∀ x ∈ K, ∀ v : TangentSpace I x,
      (G t).inner x v v ≤ Real.exp ε * (G τ₀).inner x v v ∧
        (G τ₀).inner x v v ≤ Real.exp ε * (G t).inner x v v := by
  have hS : IsCompact {p : MetricUnitTangent (I := I) (M := M) (G τ₀) |
      MetricUnitTangent.base (I := I) (M := M) p ∈ K} := metricUnitOn_compact (G τ₀) hK
  have hΨ : Continuous (fun q : A × MetricUnitTangent (I := I) (M := M) (G τ₀) =>
      (G q.1.1).inner q.2.1.proj q.2.1.2 q.2.1.2) :=
    hcont.comp_continuous (f := fun q : A × MetricUnitTangent (I := I) (M := M) (G τ₀) =>
      ((q.1.1, q.2.1) : ℝ × TangentBundle I M))
      (continuous_subtype_val.comp continuous_fst |>.prodMk
        (continuous_subtype_val.comp continuous_snd)) (fun q => ⟨q.1.2, mem_univ _⟩)
  let W : Set (A × MetricUnitTangent (I := I) (M := M) (G τ₀)) :=
    {q | Real.exp (-ε) < (G q.1.1).inner q.2.1.proj q.2.1.2 q.2.1.2 ∧
      (G q.1.1).inner q.2.1.proj q.2.1.2 q.2.1.2 < Real.exp ε}
  have hWo : IsOpen W :=
    (isOpen_lt continuous_const hΨ).inter (isOpen_lt hΨ continuous_const)
  have hsub : ({⟨τ₀, hτ⟩} : Set A) ×ˢ {p : MetricUnitTangent (I := I) (M := M) (G τ₀) |
      MetricUnitTangent.base (I := I) (M := M) p ∈ K} ⊆ W := by
    rintro ⟨a, p⟩ ⟨ha, -⟩
    rw [mem_singleton_iff] at ha
    subst ha
    have h1 : (G τ₀).inner p.1.proj p.1.2 p.1.2 = 1 := p.2
    refine ⟨?_, ?_⟩
    · change Real.exp (-ε) < (G τ₀).inner p.1.proj p.1.2 p.1.2
      rw [h1]
      have := Real.exp_lt_exp.mpr (show -ε < 0 by linarith)
      simpa using this
    · change (G τ₀).inner p.1.proj p.1.2 p.1.2 < Real.exp ε
      rw [h1]
      exact Real.one_lt_exp_iff.mpr hε
  obtain ⟨u, v, hu, hv, hσu, hSv, huv⟩ :=
    generalized_tube_lemma isCompact_singleton hS hWo hsub
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hu ⟨τ₀, hτ⟩ (hσu rfl)
  refine ⟨δ, hδ, fun t ht hdt x hx w => ?_⟩
  have hσu' : (⟨t, ht⟩ : A) ∈ u := hball (by
    rw [Metric.mem_ball, Subtype.dist_eq, Real.dist_eq]
    exact hdt)
  by_cases hw : w = 0
  · subst hw
    simp
  have hpos : 0 < (G τ₀).inner x w w := (G τ₀).pos x w hw
  set s : ℝ := Real.sqrt ((G τ₀).inner x w w) with hs_def
  have hs : 0 < s := Real.sqrt_pos.mpr hpos
  have hss : s * s = (G τ₀).inner x w w := by
    simpa only [hs_def, sq] using Real.sq_sqrt hpos.le
  have hunit : (G τ₀).inner x (s⁻¹ • w) (s⁻¹ • w) = 1 := by
    rw [metric_smul2]
    field_simp [hs.ne']
    linarith [hss]
  let p : MetricUnitTangent (I := I) (M := M) (G τ₀) :=
    ⟨(TotalSpace.mk' E x (s⁻¹ • w)), hunit⟩
  have hp : MetricUnitTangent.base (I := I) (M := M) p ∈ K := hx
  have hlt : ((⟨t, ht⟩, p) : A × MetricUnitTangent (I := I) (M := M) (G τ₀)) ∈ W :=
    huv (show ((⟨t, ht⟩, p) : A × MetricUnitTangent (I := I) (M := M) (G τ₀)) ∈ u ×ˢ v from
      ⟨hσu', hSv hp⟩)
  obtain ⟨hl, hr⟩ := hlt
  change Real.exp (-ε) < (G t).inner x (s⁻¹ • w) (s⁻¹ • w) at hl
  change (G t).inner x (s⁻¹ • w) (s⁻¹ • w) < Real.exp ε at hr
  rw [metric_smul2] at hl hr
  have hss' : 0 < s * s := mul_pos hs hs
  set a : ℝ := (G t).inner x w w with ha_def
  set c : ℝ := s⁻¹ * s⁻¹ * a with hc_def
  have hac : a = s * s * c := by
    rw [hc_def]
    field_simp
  have h3 : Real.exp ε * Real.exp (-ε) = 1 := by rw [← Real.exp_add]; simp
  rw [← hss]
  constructor
  · have := mul_lt_mul_of_pos_left hr hss'
    rw [hac]
    nlinarith [this]
  · have h2 := mul_lt_mul_of_pos_left hl hss'
    have h4 : s * s * Real.exp (-ε) * Real.exp ε < s * s * c * Real.exp ε :=
      mul_lt_mul_of_pos_right h2 (Real.exp_pos ε)
    have h5 : s * s * Real.exp (-ε) * Real.exp ε = s * s := by
      calc s * s * Real.exp (-ε) * Real.exp ε = s * s * (Real.exp ε * Real.exp (-ε)) := by ring
        _ = s * s := by rw [h3, mul_one]
    rw [h5] at h4
    rw [hac]
    nlinarith [h4]

end GC.LongTime.CuspP1
