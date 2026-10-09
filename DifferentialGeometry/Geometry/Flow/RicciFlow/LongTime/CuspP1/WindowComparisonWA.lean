import DifferentialGeometry.Geometry.Metric.Family.LocalEquivalence
import DifferentialGeometry.Geometry.Metric.QuadraticBounds.Unit
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

/-!
# window 上的一致 `e^ε` 比较（O-W-ASSEMBLY G3，剩余义务 c1，后缀 `_WA`）

紧流形 `M` 上的连续度量族 `G`（`MetricFamilySmoothOn D G`）与参数族 `f : ℝ × M → M`
（在 `J ×ˢ univ` 上 joint `C^∞`，`J` 有 unique differentiability，`f (t₀, ·) = id`）：
`s → t₀`（在 `J` 内）时
`e^{-ε} G t₀ (w, w) ≤ G s (d f_s w, d f_s w) ≤ e^ε G t₀ (w, w)`，对所有 `p`、`w` 一致。

* `continuousOn_tangentMap_family_WA`：`(σ, v) ↦ (f_σ x, d f_σ v)` 在 `J ×ˢ univ` 上连续——
  `ContMDiffOn.continuousOn_tangentMapWithin` + `equivTangentBundleProd.symm` + 链式法则
  （同 S-A14-SURGERY `continuous_tangentMap_family_SG` 的思路，这里只要 `ContMDiffOn`，允许
  `J = Ico t₀ b` 这类半开区间）。
* `eventually_comparison_of_window_WA`：上述两侧比较，`∀ᶠ s in 𝓝[J] t₀`；证明 = 单位切丛
  `MetricUnitTangent (G t₀)` 紧（`metricUnitOn_compact`）+ tube lemma，与
  `eventually_metric_comparison_on_compact`（tracked）同一模式。

用途：`J = I ∩ D.regular`（regular 时刻 window，开）给 `hcmp`；`J = Ico t₀ b`（STATIC G7 的右侧
window）给 event 时刻 HT-R 的度量字段。
-/

set_option autoImplicit false
noncomputable section

open Set Filter Manifold Bundle DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

namespace GC.LongTime.CuspP1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- `ContMDiffOn` 的参数族的切映射在 `J ×ˢ univ` 上联合连续。 -/
theorem continuousOn_tangentMap_family_WA [IsManifold I ∞ M] (f : ℝ × M → M) {J : Set ℝ}
    (hJ : UniqueDiffOn ℝ J) (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ f (J ×ˢ univ)) :
    ContinuousOn (fun p : ℝ × TangentBundle I M =>
      (TotalSpace.mk' E (f (p.1, p.2.proj))
        (mfderiv I I (fun x => f (p.1, x)) p.2.proj p.2.2) : TangentBundle I M))
      (J ×ˢ univ) := by
  have hU : UniqueMDiffOn (𝓘(ℝ, ℝ).prod I) (J ×ˢ (univ : Set M)) :=
    hJ.uniqueMDiffOn.prod uniqueMDiffOn_univ
  have h1 : Continuous (fun p : ℝ × TangentBundle I M =>
      (equivTangentBundleProd 𝓘(ℝ, ℝ) ℝ I M).symm
        ((TotalSpace.mk' ℝ p.1 (0 : ℝ) : TangentBundle 𝓘(ℝ, ℝ) ℝ), p.2)) := by
    have hσ : Continuous (fun σ : ℝ =>
        (TotalSpace.mk' ℝ σ (0 : ℝ) : TangentBundle 𝓘(ℝ, ℝ) ℝ)) :=
      (tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ)).symm.continuous.comp
        (continuous_id.prodMk continuous_const)
    exact (contMDiff_equivTangentBundleProd_symm (n := 0)).continuous.comp
      ((hσ.comp continuous_fst).prodMk continuous_snd)
  have h2 := hf.continuousOn_tangentMapWithin (by simp) hU
  refine (h2.comp h1.continuousOn ?_).congr ?_
  · rintro ⟨σ, v⟩ ⟨hσ, -⟩
    exact ⟨hσ, mem_univ _⟩
  · rintro ⟨σ, ⟨x, u⟩⟩ ⟨hσ, -⟩
    have hsl : MDifferentiableWithinAt I (𝓘(ℝ, ℝ).prod I) (fun y : M => (σ, y)) univ x :=
      (mdifferentiableAt_const.prodMk mdifferentiableAt_id).mdifferentiableWithinAt
    have hdw : MDifferentiableWithinAt (𝓘(ℝ, ℝ).prod I) I f (J ×ˢ univ) (σ, x) :=
      (hf (σ, x) ⟨hσ, mem_univ _⟩).mdifferentiableWithinAt (by simp)
    have hcomp : mfderivWithin I I (f ∘ fun y : M => (σ, y)) univ x =
        (mfderivWithin (𝓘(ℝ, ℝ).prod I) I f (J ×ˢ univ) (σ, x)).comp
          (mfderivWithin I (𝓘(ℝ, ℝ).prod I) (fun y : M => (σ, y)) univ x) :=
      mfderivWithin_comp x hdw hsl (fun y _ => ⟨hσ, mem_univ _⟩) (uniqueMDiffWithinAt_univ I)
    rw [mfderivWithin_univ, mfderivWithin_univ, mfderiv_prod_right] at hcomp
    change TotalSpace.mk' E (f (σ, x)) (mfderiv I I (fun y => f (σ, y)) x u) = _
    change mfderiv I I (fun y => f (σ, y)) x = _ at hcomp
    rw [hcomp]
    rfl

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M] [IsManifold I 1 M] [T2Space M]

/-- **c1**：紧流形上，连续度量族 + joint `C^∞`、`f (t₀, ·) = id` 的参数族 ⇒ `s → t₀`（在 `J` 内）时
`f_s^* G s` 与 `G t₀` 双向 `e^ε` 一致接近。 -/
theorem eventually_comparison_of_window_WA [CompactSpace M]
    (G : ℝ → SmoothRiemannianMetric I M) (D : RealTimeInterval) (hG : MetricFamilySmoothOn D G)
    {J : Set ℝ} (hJ : UniqueDiffOn ℝ J) (hJD : J ⊆ D.carrier) {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (f : ℝ × M → M) (hf : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I ∞ f (J ×ˢ univ))
    (hid : ∀ x, f (t₀, x) = x) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ s in 𝓝[J] t₀, ∀ (p : M) (w : TangentSpace I p),
      (G t₀).inner p w w ≤ Real.exp ε *
          (G s).inner (f (s, p)) (mfderiv I I (fun x => f (s, x)) p w)
            (mfderiv I I (fun x => f (s, x)) p w) ∧
      (G s).inner (f (s, p)) (mfderiv I I (fun x => f (s, x)) p w)
          (mfderiv I I (fun x => f (s, x)) p w) ≤ Real.exp ε * (G t₀).inner p w w := by
  have hQ : Continuous (fun q : {t : ℝ // t ∈ D.carrier} × TangentBundle I M =>
      (G q.1.1).inner q.2.proj q.2.2 q.2.2) := by
    have hq := tensor0SFamily_quadCont (I := I) (M := M) hG.metricTensor_cont
    simpa only [quad02, Tensor0SBundle.metricTensorField_apply] using hq
  have hTF := continuousOn_tangentMap_family_WA f hJ hf
  let U := MetricUnitTangent (I := I) (M := M) (G t₀)
  have hS : IsCompact {p : U | MetricUnitTangent.base (I := I) (M := M) p ∈ (univ : Set M)} :=
    metricUnitOn_compact (G t₀) isCompact_univ
  let Ψ : J × U → ℝ := fun q =>
    (G q.1.1).inner (f (q.1.1, q.2.1.proj)) (mfderiv I I (fun x => f (q.1.1, x)) q.2.1.proj q.2.1.2)
      (mfderiv I I (fun x => f (q.1.1, x)) q.2.1.proj q.2.1.2)
  have hΨ : Continuous Ψ := by
    have hr : Continuous (fun q : J × U => ((q.1.1, q.2.1) : ℝ × TangentBundle I M)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd)
    have hT : Continuous (fun q : J × U =>
        (TotalSpace.mk' E (f (q.1.1, q.2.1.proj))
          (mfderiv I I (fun x => f (q.1.1, x)) q.2.1.proj q.2.1.2) : TangentBundle I M)) :=
      hTF.comp_continuous hr (fun q => ⟨q.1.2, mem_univ _⟩)
    have hs : Continuous (fun q : J × U => (⟨q.1.1, hJD q.1.2⟩ : {t : ℝ // t ∈ D.carrier})) :=
      (continuous_subtype_val.comp continuous_fst).subtype_mk _
    exact hQ.comp (hs.prodMk hT)
  let W : Set (J × U) := {q | Real.exp (-ε) < Ψ q ∧ Ψ q < Real.exp ε}
  have hWo : IsOpen W := (isOpen_lt continuous_const hΨ).inter (isOpen_lt hΨ continuous_const)
  have hsub : ({⟨t₀, ht₀⟩} : Set J) ×ˢ
      {p : U | MetricUnitTangent.base (I := I) (M := M) p ∈ (univ : Set M)} ⊆ W := by
    rintro ⟨a, p⟩ ⟨ha, -⟩
    rw [mem_singleton_iff] at ha
    subst ha
    have hfun : (fun x => f (t₀, x)) = id := funext hid
    have h1 : (G t₀).inner p.1.proj p.1.2 p.1.2 = 1 := p.2
    have hval : Ψ (⟨t₀, ht₀⟩, p) = 1 := by
      change (G t₀).inner (f (t₀, p.1.proj)) (mfderiv I I (fun x => f (t₀, x)) p.1.proj p.1.2)
        (mfderiv I I (fun x => f (t₀, x)) p.1.proj p.1.2) = 1
      rw [hfun, mfderiv_id, hid]
      simpa only [ContinuousLinearMap.id_apply] using h1
    refine ⟨?_, ?_⟩
    · rw [hval]
      have := Real.exp_lt_exp.mpr (show -ε < 0 by linarith)
      simpa using this
    · rw [hval]
      exact Real.one_lt_exp_iff.mpr hε
  obtain ⟨u, v, hu, -, hσu, hSv, huv⟩ := generalized_tube_lemma isCompact_singleton hS hWo hsub
  rw [nhdsWithin_eq_map_subtype_coe ht₀, Filter.eventually_map]
  filter_upwards [hu.mem_nhds (hσu rfl)] with s hs p w
  by_cases hw : w = 0
  · subst hw
    simp
  have hpos : 0 < (G t₀).inner p w w := (G t₀).pos p w hw
  set r : ℝ := Real.sqrt ((G t₀).inner p w w) with hr_def
  have hr : 0 < r := Real.sqrt_pos.mpr hpos
  have hrr : r * r = (G t₀).inner p w w := by
    simpa only [hr_def, sq] using Real.sq_sqrt hpos.le
  have hunit : (G t₀).inner p (r⁻¹ • w) (r⁻¹ • w) = 1 := by
    rw [metric_smul2]
    field_simp [hr.ne']
    linarith [hrr]
  let q : U := ⟨(TotalSpace.mk' E p (r⁻¹ • w)), hunit⟩
  have hW : ((s, q) : J × U) ∈ W := huv ⟨hs, hSv (mem_univ _)⟩
  obtain ⟨hlo, hhi⟩ := hW
  change Real.exp (-ε) < (G s.1).inner (f (s.1, p)) (mfderiv I I (fun x => f (s.1, x)) p (r⁻¹ • w))
    (mfderiv I I (fun x => f (s.1, x)) p (r⁻¹ • w)) at hlo
  change (G s.1).inner (f (s.1, p)) (mfderiv I I (fun x => f (s.1, x)) p (r⁻¹ • w))
    (mfderiv I I (fun x => f (s.1, x)) p (r⁻¹ • w)) < Real.exp ε at hhi
  rw [map_smul, metric_smul2] at hlo hhi
  set Qw := (G s.1).inner (f (s.1, p)) (mfderiv I I (fun x => f (s.1, x)) p w)
    (mfderiv I I (fun x => f (s.1, x)) p w) with hQw
  have hrinv : r⁻¹ * r⁻¹ * (r * r) = 1 := by field_simp
  have hlo' : Real.exp (-ε) * (r * r) < Qw := by
    have := mul_lt_mul_of_pos_right hlo (mul_pos hr hr)
    calc Real.exp (-ε) * (r * r) < r⁻¹ * r⁻¹ * Qw * (r * r) := this
      _ = Qw := by rw [mul_right_comm, hrinv, one_mul]
  have hhi' : Qw < Real.exp ε * (r * r) := by
    have := mul_lt_mul_of_pos_right hhi (mul_pos hr hr)
    calc Qw = r⁻¹ * r⁻¹ * Qw * (r * r) := by rw [mul_right_comm, hrinv, one_mul]
      _ < Real.exp ε * (r * r) := this
  rw [hrr] at hlo' hhi'
  refine ⟨?_, hhi'.le⟩
  have hexp : Real.exp ε * Real.exp (-ε) = 1 := by rw [← Real.exp_add]; simp
  have := mul_lt_mul_of_pos_left hlo' (Real.exp_pos ε)
  rw [← mul_assoc, hexp, one_mul] at this
  exact this.le

end GC.LongTime.CuspP1
