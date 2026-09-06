import DifferentialGeometry.Analysis.Sobolev.WithBoundary.Intrinsic.Algebra
import DifferentialGeometry.Analysis.Sobolev.Manifold.MeasureBridgeUniform
import DifferentialGeometry.Analysis.Sobolev.Intrinsic.EquivalenceReverseGradientProductBound
import DifferentialGeometry.Geometry.Operator.WithBoundary.GradientContinuity
import DifferentialGeometry.Geometry.Metric.InnerExpansion

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace WithBoundary
namespace EquivalenceReverse

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "I_hs" => modelWithCornersEuclideanHalfSpace n
local notation "EuN'" => EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))

private local instance : MeasurableSpace EuN :=
  WithLp.measurableSpace 2 (Fin n → ℝ)
private local instance : MeasurableSpace EuN' :=
  WithLp.measurableSpace 2 (Fin (Module.finrank ℝ EuN) → ℝ)
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [IsManifold I_hs ∞ M] [T2Space M] [CompactSpace M] in
private lemma chartPushedRaw_eq_chartSmoothExt_comp_toEuclidean_symm
    (α : M) (f : M → ℝ) :
    DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw
        (I := I_hs) (M := M) α f =
      fun y => chartSmoothExt (n := n) (M := M) α f
        ((toEuclidean (E := EuN)).symm y) := by
  classical
  funext y
  have hy_iff : y ∈ DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I_hs) (M := M) α ↔
      (toEuclidean (E := EuN)).symm y ∈ (extChartAt I_hs α).target := by
    unfold DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa using hz
    · intro hy
      exact ⟨(toEuclidean (E := EuN)).symm y, hy,
        (toEuclidean (E := EuN)).apply_symm_apply y⟩
  by_cases hy : (toEuclidean (E := EuN)).symm y ∈ (extChartAt I_hs α).target
  · rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_mem
      (I := I_hs) (M := M) α f (hy_iff.mpr hy)]
    unfold chartSmoothExt
    rw [if_pos hy]
  · rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_notMem
      (I := I_hs) (M := M) α f (hy_iff.not.mpr hy)]
    unfold chartSmoothExt
    rw [if_neg hy]

omit [IsManifold I_hs ∞ M] [T2Space M] [CompactSpace M] in
private lemma exists_eLpNorm_chartSmoothExt_le_const_mul_chartPushedRaw
    (α : M) :
    ∃ A : ℝ, 0 < A ∧ ∀ f : M → ℝ,
      eLpNorm (chartSmoothExt (n := n) (M := M) α f) 2
          (volume.restrict
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
              (chartTargetEuclid (n := n) (M := M) α))) ≤
        ENNReal.ofReal A *
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw
              (I := I_hs) (M := M) α f)
            2
            ((volume : Measure EuN').restrict
              (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
                (I := I_hs) (M := M) α)) := by
  classical
  let e : EuN ≃L[ℝ] EuN' := toEuclidean (E := EuN)
  let μe : Measure EuN := Measure.map (e.symm : EuN' → EuN) (volume : Measure EuN')
  let c : ℝ≥0 := Measure.addHaarScalarFactor μe (volume : Measure EuN)
  let a : ℝ≥0 := c ^ (2 : ℝ≥0∞).toReal⁻¹
  have hc : c ≠ 0 :=
    Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
      μe (volume : Measure EuN) |>.ne'
  have ha_pos : 0 < a := by
    simp only [a]
    positivity
  refine ⟨((a : ℝ)⁻¹), inv_pos.mpr (by exact_mod_cast ha_pos), ?_⟩
  intro f
  let raw : EuN' → ℝ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw
      (I := I_hs) (M := M) α f
  let ext : EuN → ℝ := chartSmoothExt (n := n) (M := M) α f
  have hraw : raw = fun y => ext (e.symm y) :=
    chartPushedRaw_eq_chartSmoothExt_comp_toEuclidean_symm
      (n := n) (M := M) α f
  have he : MeasurableEmbedding (e.symm : EuN' → EuN) :=
    e.symm.toHomeomorph.measurableEmbedding
  have hfull : eLpNorm raw 2 (volume : Measure EuN') = eLpNorm ext 2 μe := by
    rw [hraw]
    change eLpNorm (ext ∘ (e.symm : EuN' → EuN)) 2 (volume : Measure EuN') =
      eLpNorm ext 2 (Measure.map (e.symm : EuN' → EuN) (volume : Measure EuN'))
    exact (MeasurableEmbedding.eLpNorm_map_measure
      (μ := (volume : Measure EuN')) (f := (e.symm : EuN' → EuN))
      (g := ext) (p := (2 : ℝ≥0∞)) he).symm
  have hμe : μe = c • (volume : Measure EuN) :=
    Measure.isAddLeftInvariant_eq_smul μe (volume : Measure EuN)
  have hraw_support : Function.support raw ⊆
      DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
        (I := I_hs) (M := M) α := by
    intro y hy
    by_contra hyt
    apply hy
    exact DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw_apply_of_notMem
      (I := I_hs) (M := M) α f hyt
  have hraw_restrict : eLpNorm raw 2 (volume : Measure EuN') =
      eLpNorm raw 2
        ((volume : Measure EuN').restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I_hs) (M := M) α)) := by
    exact (eLpNorm_restrict_eq_of_support_subset hraw_support).symm
  have hext_le : eLpNorm ext 2
      (volume.restrict
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) α))) ≤
      eLpNorm ext 2 (volume : Measure EuN) :=
    eLpNorm_mono_measure ext Measure.restrict_le_self
  have ha_ne_zero : (a : ℝ≥0∞) ≠ 0 := by exact_mod_cast ha_pos.ne'
  have ha_ne_top : (a : ℝ≥0∞) ≠ ⊤ := by simp
  have hscale : eLpNorm raw 2 (volume : Measure EuN') =
      (a : ℝ≥0∞) * eLpNorm ext 2 (volume : Measure EuN) := by
    rw [hfull, hμe, eLpNorm_smul_measure_of_ne_zero' hc]
    rfl
  refine hext_le.trans_eq ?_
  rw [ENNReal.ofReal_inv_of_pos (by exact_mod_cast ha_pos), ENNReal.ofReal_coe_nnreal]
  calc
    eLpNorm ext 2 volume =
        (a : ℝ≥0∞)⁻¹ * ((a : ℝ≥0∞) * eLpNorm ext 2 volume) :=
      (ENNReal.inv_mul_cancel_left ha_ne_zero ha_ne_top).symm
    _ = (a : ℝ≥0∞)⁻¹ * eLpNorm raw 2 volume := by rw [hscale]
    _ = (a : ℝ≥0∞)⁻¹ * eLpNorm raw 2
        (volume.restrict
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
            (I := I_hs) (M := M) α)) := by rw [hraw_restrict]

private noncomputable def chartTargetUnitFiber
    (α : M) (i : Fin n) (x : M) : TangentSpace I_hs x :=
  (trivializationAt EuN (TangentSpace I_hs) α).symm x
    (EuclideanSpace.single i (1 : ℝ))

omit [T2Space M] [CompactSpace M] in
private lemma chartTargetUnitFiber_smoothOn
    (α : M) (i : Fin n) :
    ContMDiffOn I_hs ((modelWithCornersEuclideanHalfSpace n).prod 𝓘(ℝ, EuN)) ∞
      (fun x : M => TotalSpace.mk' EuN x
        (chartTargetUnitFiber (n := n) (M := M) α i x))
      (trivializationAt EuN (TangentSpace I_hs) α).baseSet := by
  set v : EuN := EuclideanSpace.single i (1 : ℝ) with hv_def
  have hiff :=
    (trivializationAt EuN (TangentSpace I_hs) α).contMDiffOn_section_baseSet_iff
      (IB := I_hs) (n := ∞)
      (s := fun x : M => (trivializationAt EuN (TangentSpace I_hs) α).symm x v)
  refine hiff.mpr ?_
  have hc : ContMDiffOn I_hs 𝓘(ℝ, EuN) ∞ (fun _ : M => v)
      (trivializationAt EuN (TangentSpace I_hs) α).baseSet :=
    contMDiffOn_const
  refine hc.congr ?_
  intro x hx
  exact congrArg Prod.snd
    ((trivializationAt EuN (TangentSpace I_hs) α).apply_mk_symm hx v)

omit [T2Space M] [CompactSpace M] in
private lemma g_inner_chartTargetUnitFiber_continuousOn
    (g : DifferentialGeometry.SmoothRiemannianMetric I_hs M)
    (α : M) (i : Fin n) :
    ContinuousOn
      (fun x : M => g.inner x
        (chartTargetUnitFiber (n := n) (M := M) α i x)
        (chartTargetUnitFiber (n := n) (M := M) α i x))
      (trivializationAt EuN (TangentSpace I_hs) α).baseSet := by
  have hg : ContMDiffOn I_hs
      ((modelWithCornersEuclideanHalfSpace n).prod 𝓘(ℝ, EuN →L[ℝ] EuN →L[ℝ] ℝ)) ∞
      (fun b : M => TotalSpace.mk' (EuN →L[ℝ] EuN →L[ℝ] ℝ)
        (E := fun y => TangentSpace I_hs y →L[ℝ] TangentSpace I_hs y →L[ℝ] ℝ)
        b (g.inner b))
      (trivializationAt EuN (TangentSpace I_hs) α).baseSet :=
    g.contMDiff.contMDiffOn
  have hv := chartTargetUnitFiber_smoothOn (n := n) (M := M) α i
  have happ : ContMDiffOn I_hs
      ((modelWithCornersEuclideanHalfSpace n).prod 𝓘(ℝ, ℝ)) ∞
      (fun x : M =>
        (⟨x, g.inner x
          (chartTargetUnitFiber (n := n) (M := M) α i x)
          (chartTargetUnitFiber (n := n) (M := M) α i x)⟩ :
          TotalSpace ℝ (Bundle.Trivial M ℝ)))
      (trivializationAt EuN (TangentSpace I_hs) α).baseSet :=
    ContMDiffOn.clm_bundle_apply₂ (F₁ := EuN) (F₂ := EuN) (F₃ := ℝ)
      (b := fun x : M => x) hg hv hv
  intro x hx
  have hpx := happ x hx
  rw [Bundle.contMDiffWithinAt_totalSpace] at hpx
  exact hpx.2.continuousWithinAt

private lemma exists_chartTargetUnitFiber_sq_bound
    (g : DifferentialGeometry.SmoothRiemannianMetric I_hs M) (α : M) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x ∈ tsupport
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ),
      ∀ i : Fin n,
        g.inner x
          (chartTargetUnitFiber (n := n) (M := M) α i x)
          (chartTargetUnitFiber (n := n) (M := M) α i x) ≤ B := by
  classical
  set K : Set M := tsupport
    ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) with hK_def
  let F : M → ℝ := fun x => ∑ i : Fin n,
    g.inner x
      (chartTargetUnitFiber (n := n) (M := M) α i x)
      (chartTargetUnitFiber (n := n) (M := M) α i x)
  have hK_compact : IsCompact K := (isClosed_tsupport _).isCompact
  have hK_base : K ⊆ (trivializationAt EuN (TangentSpace I_hs) α).baseSet := by
    intro x hx
    rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source]
    exact DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M α hx
  have hF_cont : ContinuousOn F K := by
    apply continuousOn_finsetSum
    intro i _
    exact (g_inner_chartTargetUnitFiber_continuousOn
      (n := n) (M := M) g α i).mono hK_base
  by_cases hK_ne : K.Nonempty
  · obtain ⟨B, hB⟩ := (hK_compact.image_of_continuousOn hF_cont).bddAbove
    obtain ⟨x₀, hx₀⟩ := hK_ne
    have hF_nonneg : ∀ x : M, 0 ≤ F x := by
      intro x
      exact Finset.sum_nonneg (fun i _ => by
        by_cases hi : chartTargetUnitFiber (n := n) (M := M) α i x = 0
        · rw [hi, (g.inner x).map_zero]
          change (0 : ℝ) ≤ (0 : TangentSpace I_hs x →L[ℝ] ℝ) 0
          simp
        · exact (g.pos x _ hi).le)
    have hB_nonneg : 0 ≤ B := (hF_nonneg x₀).trans (hB ⟨x₀, hx₀, rfl⟩)
    refine ⟨B, hB_nonneg, ?_⟩
    intro x hx i
    have hterm_nonneg : ∀ j : Fin n, 0 ≤ g.inner x
        (chartTargetUnitFiber (n := n) (M := M) α j x)
        (chartTargetUnitFiber (n := n) (M := M) α j x) := by
      intro j
      by_cases hj : chartTargetUnitFiber (n := n) (M := M) α j x = 0
      · rw [hj, (g.inner x).map_zero]
        change (0 : ℝ) ≤ (0 : TangentSpace I_hs x →L[ℝ] ℝ) 0
        simp
      · exact (g.pos x _ hj).le
    refine (Finset.single_le_sum
      (s := Finset.univ) (f := fun j : Fin n => g.inner x
        (chartTargetUnitFiber (n := n) (M := M) α j x)
        (chartTargetUnitFiber (n := n) (M := M) α j x))
      (fun j _ => hterm_nonneg j) (Finset.mem_univ i)).trans ?_
    exact hB ⟨x, hx, rfl⟩
  · rw [Set.not_nonempty_iff_eq_empty] at hK_ne
    refine ⟨0, le_rfl, ?_⟩
    intro x hx
    rw [hK_ne] at hx
    exact (Set.notMem_empty x hx).elim

private lemma exists_sqrt_g_inner_gradFun_pou_mul_le_uniform
    (g : DifferentialGeometry.SmoothRiemannianMetric I_hs M) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {u : M → ℝ}, ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u →
      ∀ x : M,
        Real.sqrt
            (g.inner x
              (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g
                (fun y : M =>
                  (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
                    : C^∞⟮I_hs, M; ℝ⟯) y * u y) x)
              (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g
                (fun y : M =>
                  (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
                    : C^∞⟮I_hs, M; ℝ⟯) y * u y) x)) ≤
          K *
            (|u x| + Real.sqrt
              (g.inner x
                (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g u x)
                (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g u x))) := by
  classical
  set ρ : C^∞⟮I_hs, M; ℝ⟯ :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α with hρ_def
  have hρ_norm_cont : Continuous (fun x : M => Real.sqrt
      (g.inner x
        (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g
          ((ρ : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) x)
        (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g
          ((ρ : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) x))) :=
    Real.continuous_sqrt.comp
      (DifferentialGeometry.Geometry.Operator.WithBoundary.continuous_g_inner_gradFun_gradFun
        (n := n) (M := M) g ρ.contMDiff ρ.contMDiff)
  obtain ⟨Kρ, hKρ_nonneg, hKρ_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.exists_continuous_sup_of_compactSpace
      (M := M) hρ_norm_cont (fun _ => Real.sqrt_nonneg _)
  set K : ℝ := max 1 Kρ with hK_def
  have hK_nonneg : 0 ≤ K := zero_le_one.trans (le_max_left _ _)
  refine ⟨K, hK_nonneg, ?_⟩
  intro u hu x
  have hρ_diff : MDifferentiableAt I_hs 𝓘(ℝ, ℝ)
      ((ρ : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) x :=
    ρ.contMDiff.mdifferentiableAt (by simp)
  have hu_diff : MDifferentiableAt I_hs 𝓘(ℝ, ℝ) u x :=
    hu.mdifferentiableAt (by simp)
  have hgrad :=
    DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.gradFun_mul_pointwise
      (I := I_hs) g (ρ := (ρ : M → ℝ)) (u := u) hρ_diff hu_diff
  rw [hgrad]
  set gu : TangentSpace I_hs x :=
    DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g u x
  set gρ : TangentSpace I_hs x :=
    DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g
      ((ρ : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) x
  have hρ_abs : |((ρ : M → ℝ) x)| ≤ 1 :=
    DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.abs_chartAtlasPOU_le_one
      (I := I_hs) (M := M) α x
  have hgu_nonneg : 0 ≤ Real.sqrt (g.inner x gu gu) := Real.sqrt_nonneg _
  have hu_abs_nonneg : 0 ≤ |u x| := abs_nonneg _
  have hterm_u : |((ρ : M → ℝ) x)| * Real.sqrt (g.inner x gu gu) ≤
      Real.sqrt (g.inner x gu gu) := by
    calc
      |((ρ : M → ℝ) x)| * Real.sqrt (g.inner x gu gu) ≤
          1 * Real.sqrt (g.inner x gu gu) :=
        mul_le_mul_of_nonneg_right hρ_abs hgu_nonneg
      _ = Real.sqrt (g.inner x gu gu) := one_mul _
  have hterm_ρ : |u x| * Real.sqrt (g.inner x gρ gρ) ≤ |u x| * Kρ :=
    mul_le_mul_of_nonneg_left (hKρ_bound x) hu_abs_nonneg
  have hgu_scale : Real.sqrt (g.inner x gu gu) ≤
      K * Real.sqrt (g.inner x gu gu) := by
    simpa [K] using mul_le_mul_of_nonneg_right (le_max_left (1 : ℝ) Kρ) hgu_nonneg
  have hu_scale : Kρ * |u x| ≤ K * |u x| :=
    mul_le_mul_of_nonneg_right (le_max_right (1 : ℝ) Kρ) hu_abs_nonneg
  calc
    Real.sqrt
        (g.inner x
          (((ρ : M → ℝ) x) • gu + u x • gρ)
          (((ρ : M → ℝ) x) • gu + u x • gρ)) ≤
      Real.sqrt (g.inner x (((ρ : M → ℝ) x) • gu) (((ρ : M → ℝ) x) • gu)) +
        Real.sqrt (g.inner x (u x • gρ) (u x • gρ)) :=
      DifferentialGeometry.Geometry.Riemannian.sqrt_inner_add_le
        (I := I_hs) g x _ _
    _ = |((ρ : M → ℝ) x)| * Real.sqrt (g.inner x gu gu) +
        |u x| * Real.sqrt (g.inner x gρ gρ) := by
      rw [DifferentialGeometry.Geometry.Riemannian.sqrt_inner_smul,
        DifferentialGeometry.Geometry.Riemannian.sqrt_inner_smul]
    _ ≤ Real.sqrt (g.inner x gu gu) + |u x| * Kρ :=
      add_le_add hterm_u hterm_ρ
    _ = Real.sqrt (g.inner x gu gu) + Kρ * |u x| := by ring
    _ ≤ K * Real.sqrt (g.inner x gu gu) + K * |u x| :=
      add_le_add hgu_scale hu_scale
    _ = K * (|u x| + Real.sqrt (g.inner x gu gu)) := by ring

omit [T2Space M] [CompactSpace M] in
private lemma mfderiv_extChartAt_apply_triv_symm
    (α : M) {x : M} (hx : x ∈ (chartAt (EuclideanHalfSpace n) α).source)
    (v : EuN) :
    mfderiv I_hs 𝓘(ℝ, EuN) (extChartAt I_hs α) x
      ((trivializationAt EuN (TangentSpace I_hs) α).symm x v) = v := by
  have hbase : x ∈ (trivializationAt EuN (TangentSpace I_hs) α).baseSet := by
    rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source]
    exact hx
  rw [← TangentBundle.continuousLinearMapAt_trivializationAt
    (𝕜 := ℝ) (I := I_hs) (x₀ := α) (x := x) hx]
  have hsymm : (trivializationAt EuN (TangentSpace I_hs) α).symm x v =
      ((trivializationAt EuN (TangentSpace I_hs) α).symmL ℝ x :
        EuN →L[ℝ] TangentSpace I_hs x) v :=
    (Trivialization.symmL_apply
      (trivializationAt EuN (TangentSpace I_hs) α) hbase v).symm
  rw [hsymm]
  exact Trivialization.continuousLinearMapAt_symmL
    (R := ℝ) (trivializationAt EuN (TangentSpace I_hs) α) hbase v

omit [T2Space M] [CompactSpace M] in
private lemma mfderiv_triv_symm_const_eq_fderiv_scalarOnE
    (α : M) {f : M → ℝ} {x : M}
    (hf : MDifferentiableAt I_hs 𝓘(ℝ, ℝ) f x)
    (hx_chart : x ∈ (chartAt (EuclideanHalfSpace n) α).source)
    (hx_int : extChartAt I_hs α x ∈ interior (extChartAt I_hs α).target)
    (v : EuN) :
    mfderiv I_hs 𝓘(ℝ, ℝ) f x
        ((trivializationAt EuN (TangentSpace I_hs) α).symm x v) =
      fderiv ℝ
        (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
          (I := I_hs) α f) (extChartAt I_hs α x) v := by
  classical
  set φ := extChartAt I_hs α
  have hx_source : x ∈ φ.source := by
    rw [DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
      (I := I_hs)]
    exact hx_chart
  have hcomp_eq : ∀ᶠ y in 𝓝 x, f y =
      (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
        (I := I_hs) α f) (φ y) := by
    have hsource_nhd : φ.source ∈ 𝓝 x :=
      (isOpen_extChartAt_source (I := I_hs) α).mem_nhds hx_source
    filter_upwards [hsource_nhd] with y hy
    rw [DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE_def,
      φ.left_inv hy]
  have hcongr : f =ᶠ[𝓝 x]
      (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
        (I := I_hs) α f) ∘ φ := hcomp_eq
  have hmfderiv_congr : mfderiv I_hs 𝓘(ℝ, ℝ) f x =
      mfderiv I_hs 𝓘(ℝ, ℝ)
        ((DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
          (I := I_hs) α f) ∘ φ) x :=
    Filter.EventuallyEq.mfderiv_eq hcongr
  rw [hmfderiv_congr]
  have hφ_mdiff : MDifferentiableAt I_hs 𝓘(ℝ, EuN) φ x :=
    mdifferentiableAt_extChartAt (I := I_hs) (x := α) hx_chart
  have hφ_symm_mdiff : MDifferentiableAt 𝓘(ℝ, EuN) I_hs φ.symm (φ x) := by
    have hsmooth : ContMDiffOn 𝓘(ℝ, EuN) I_hs ∞ φ.symm φ.target :=
      contMDiffOn_extChartAt_symm (I := I_hs) α
    have htarget_nhd : φ.target ∈ 𝓝 (φ x) :=
      mem_of_superset (isOpen_interior.mem_nhds hx_int) interior_subset
    exact (hsmooth (φ x) (interior_subset hx_int)).contMDiffAt htarget_nhd
      |>.mdifferentiableAt (by simp)
  have hsymm : φ.symm (φ x) = x := φ.left_inv hx_source
  have hf_symm : MDifferentiableAt I_hs 𝓘(ℝ, ℝ) f (φ.symm (φ x)) := by
    rw [hsymm]
    exact hf
  have hf_comp_symm : MDifferentiableAt 𝓘(ℝ, EuN) 𝓘(ℝ, ℝ)
      (f ∘ φ.symm) (φ x) :=
    hf_symm.comp (φ x) hφ_symm_mdiff
  have hscalar_eq :
      DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
        (I := I_hs) α f = f ∘ φ.symm := by
    funext y
    rfl
  have hscalar_mdiff : MDifferentiableAt 𝓘(ℝ, EuN) 𝓘(ℝ, ℝ)
      (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
        (I := I_hs) α f) (φ x) := by
    rw [hscalar_eq]
    exact hf_comp_symm
  have hchain :
      mfderiv I_hs 𝓘(ℝ, ℝ)
          ((DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
            (I := I_hs) α f) ∘ φ) x =
        (mfderiv 𝓘(ℝ, EuN) 𝓘(ℝ, ℝ)
          (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
            (I := I_hs) α f) (φ x)).comp
          (mfderiv I_hs 𝓘(ℝ, EuN) φ x) :=
    mfderiv_comp x hscalar_mdiff hφ_mdiff
  rw [hchain]
  rw [show mfderiv 𝓘(ℝ, EuN) 𝓘(ℝ, ℝ)
      (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
        (I := I_hs) α f) (φ x) =
      fderiv ℝ
        (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
          (I := I_hs) α f) (φ x) from
    mfderiv_eq_fderiv (𝕜 := ℝ)
      (f := DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
        (I := I_hs) α f)]
  change (fderiv ℝ
      (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
        (I := I_hs) α f) (φ x))
      ((mfderiv I_hs 𝓘(ℝ, EuN) φ x)
        ((trivializationAt EuN (TangentSpace I_hs) α).symm x v)) =
    (fderiv ℝ
      (DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
        (I := I_hs) α f) (φ x)) v
  rw [mfderiv_extChartAt_apply_triv_symm
    (n := n) (M := M) α hx_chart v]

omit [T2Space M] [CompactSpace M] in
private lemma fderiv_chartSmoothExt_apply_eq_inner_gradFun
    (g : DifferentialGeometry.SmoothRiemannianMetric I_hs M)
    (α : M) {f : M → ℝ} (hf : ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ f)
    {y : EuN} (hy : y ∈ interior (extChartAt I_hs α).target) (i : Fin n) :
    let x := (extChartAt I_hs α).symm y
    (fderiv ℝ (chartSmoothExt (n := n) (M := M) α f) y)
        (EuclideanSpace.single i 1) =
      g.inner x (DifferentialGeometry.Geometry.Operator.gradFun
        (I := I_hs) g f x)
        (chartTargetUnitFiber (n := n) (M := M) α i x) := by
  classical
  intro x
  have hy_target : y ∈ (extChartAt I_hs α).target := interior_subset hy
  have hx_source : x ∈ (extChartAt I_hs α).source :=
    (extChartAt I_hs α).map_target hy_target
  have hx_chart : x ∈ (chartAt (EuclideanHalfSpace n) α).source := by
    rw [← DifferentialGeometry.Integral.Measure.extChartAt_source_eq_chartAt_source
      (I := I_hs) (M := M)]
    exact hx_source
  have hxy : extChartAt I_hs α x = y :=
    (extChartAt I_hs α).right_inv hy_target
  have heq : chartSmoothExt (n := n) (M := M) α f =ᶠ[𝓝 y]
      DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
        (I := I_hs) α f := by
    filter_upwards [isOpen_interior.mem_nhds hy] with z hz
    unfold chartSmoothExt DifferentialGeometry.Integral.DivergenceTheorem.scalarOnE
    rw [if_pos (interior_subset hz)]
  rw [heq.fderiv_eq]
  rw [DifferentialGeometry.Geometry.Operator.inner_gradFun
    (I := I_hs) g f x
      (chartTargetUnitFiber (n := n) (M := M) α i x)]
  have hfactor := mfderiv_triv_symm_const_eq_fderiv_scalarOnE
    (n := n) (M := M) α (hf.mdifferentiableAt (by simp)) hx_chart
      (by rw [hxy]; exact hy) (EuclideanSpace.single i 1)
  rw [hxy] at hfactor
  exact hfactor.symm

private lemma exists_abs_fderiv_chartSmoothExt_pou_mul_le_indicator
    (g : DifferentialGeometry.SmoothRiemannianMetric I_hs M) (α : M) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {u : M → ℝ}, ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u →
      ∀ (i : Fin n) {y : EuN}, y ∈ interior (extChartAt I_hs α).target →
        |(fderiv ℝ
          (chartSmoothExt (n := n) (M := M) α
            (fun z : M =>
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
                : C^∞⟮I_hs, M; ℝ⟯) z * u z)) y)
          (EuclideanSpace.single i 1)| ≤
        K * chartSmoothExt (n := n) (M := M) α
          (Set.indicator
            (tsupport
              ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
                : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ))
            (fun x : M => |u x| + Real.sqrt
              (g.inner x
                (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g u x)
                (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g u x)))) y := by
  classical
  obtain ⟨B, hB_nonneg, hB_bound⟩ :=
    exists_chartTargetUnitFiber_sq_bound (n := n) (M := M) g α
  obtain ⟨Kgrad, hKgrad_nonneg, hKgrad_bound⟩ :=
    exists_sqrt_g_inner_gradFun_pou_mul_le_uniform (n := n) (M := M) g α
  refine ⟨Kgrad * Real.sqrt B,
    mul_nonneg hKgrad_nonneg (Real.sqrt_nonneg _), ?_⟩
  intro u hu i y hy
  set ρ : C^∞⟮I_hs, M; ℝ⟯ :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α with hρ_def
  set Kα : Set M := tsupport ((ρ : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) with hKα_def
  set v : M → ℝ := fun x : M => |u x| + Real.sqrt
    (g.inner x
      (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g u x)
      (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g u x)) with hv_def
  set f : M → ℝ := fun z : M => (ρ : M → ℝ) z * u z with hf_def
  set x : M := (extChartAt I_hs α).symm y with hx_def
  have hf_smooth : ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ f := ρ.contMDiff.mul hu
  have hderiv := fderiv_chartSmoothExt_apply_eq_inner_gradFun
    (n := n) (M := M) g α hf_smooth hy i
  dsimp only at hderiv
  change |(fderiv ℝ (chartSmoothExt (n := n) (M := M) α f) y)
      (EuclideanSpace.single i 1)| ≤
    Kgrad * Real.sqrt B * chartSmoothExt (n := n) (M := M) α
      (Set.indicator Kα v) y
  rw [hderiv]
  by_cases hxK : x ∈ Kα
  · have hCS :=
      DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.abs_g_inner_le_sqrt_mul_sqrt
        (I := I_hs) g x
          (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g f x)
          (chartTargetUnitFiber (n := n) (M := M) α i x)
    have hgrad : Real.sqrt
        (g.inner x
          (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g f x)
          (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g f x)) ≤
        Kgrad * v x := by
      simpa [f, v, ρ] using hKgrad_bound hu x
    have hframe : Real.sqrt
        (g.inner x
          (chartTargetUnitFiber (n := n) (M := M) α i x)
          (chartTargetUnitFiber (n := n) (M := M) α i x)) ≤ Real.sqrt B :=
      Real.sqrt_le_sqrt (hB_bound x hxK i)
    have hv_nonneg : 0 ≤ v x := add_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
    calc
      |g.inner x
          (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g f x)
          (chartTargetUnitFiber (n := n) (M := M) α i x)| ≤
          Real.sqrt
              (g.inner x
                (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g f x)
                (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g f x)) *
            Real.sqrt
              (g.inner x
                (chartTargetUnitFiber (n := n) (M := M) α i x)
                (chartTargetUnitFiber (n := n) (M := M) α i x)) := hCS
      _ ≤ (Kgrad * v x) *
            Real.sqrt
              (g.inner x
                (chartTargetUnitFiber (n := n) (M := M) α i x)
                (chartTargetUnitFiber (n := n) (M := M) α i x)) :=
        mul_le_mul_of_nonneg_right hgrad (Real.sqrt_nonneg _)
      _ ≤ (Kgrad * v x) * Real.sqrt B :=
        mul_le_mul_of_nonneg_left hframe (mul_nonneg hKgrad_nonneg hv_nonneg)
      _ = Kgrad * Real.sqrt B *
          chartSmoothExt (n := n) (M := M) α (Set.indicator Kα v) y := by
        simp only [chartSmoothExt, if_pos (interior_subset hy),
          Set.indicator_of_mem hxK, x]
        ring
  · have hf_supp : tsupport f ⊆ Kα := by
      have heq : f = fun z : M => (ρ : M → ℝ) z • u z := by
        funext z
        simp [f, smul_eq_mul]
      rw [heq]
      exact tsupport_smul_subset_left
        (f := fun z : M => (ρ : M → ℝ) z) (g := u)
    have hx_off : x ∉ tsupport f := fun hx => hxK (hf_supp hx)
    have heqz : f =ᶠ[𝓝 x] (fun _ : M => (0 : ℝ)) := by
      filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hx_off] with z hz
      exact image_eq_zero_of_notMem_tsupport hz
    have hmfd : mfderiv I_hs 𝓘(ℝ, ℝ) f x = 0 := by
      rw [heqz.mfderiv_eq]
      exact mfderiv_const
    have hgrad_zero : DifferentialGeometry.Geometry.Operator.gradFun
        (I := I_hs) g f x = 0 :=
      DifferentialGeometry.Geometry.Operator.gradFun_eq_zero_of_mfderiv_eq_zero
        g f hmfd
    rw [hgrad_zero, (g.inner x).map_zero]
    rw [zero_apply, abs_zero]
    refine mul_nonneg (mul_nonneg hKgrad_nonneg (Real.sqrt_nonneg _)) ?_
    rw [chartSmoothExt, if_pos (interior_subset hy), Set.indicator_of_notMem hxK]

private lemma exists_eLpNorm_fderiv_chartSmoothExt_apply_le_const_mul
    (g : DifferentialGeometry.SmoothRiemannianMetric I_hs M) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : M → ℝ}, ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u →
      ∀ i : Fin n,
        eLpNorm
            (fun y : EuN =>
              (fderiv ℝ
                (chartSmoothExt (n := n) (M := M) α
                  (fun z : M =>
                    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
                      : C^∞⟮I_hs, M; ℝ⟯) z * u z)) y)
                (EuclideanSpace.single i 1))
            2
            (volume.restrict
              (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
                (chartTargetEuclid (n := n) (M := M) α))) ≤
          ENNReal.ofReal C *
            (eLpNorm u 2
                (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I_hs M g) +
              eLpNorm
                (fun x : M => Real.sqrt
                  (g.inner x
                    (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g u x)
                    (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g u x)))
                2
                (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
                  I_hs M g)) := by
  classical
  set ρ : C^∞⟮I_hs, M; ℝ⟯ :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α with hρ_def
  set Kα : Set M := tsupport ((ρ : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) with hKα_def
  have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
  have hKα_sub : Kα ⊆ (chartAt (EuclideanHalfSpace n) α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M α
  obtain ⟨K, hK_nonneg, hK_bound⟩ :=
    exists_abs_fderiv_chartSmoothExt_pou_mul_le_indicator
      (n := n) (M := M) g α
  obtain ⟨A, hA_pos, hA_bound⟩ :=
    exists_eLpNorm_chartSmoothExt_le_const_mul_chartPushedRaw
      (n := n) (M := M) α
  obtain ⟨D, hD_pos, hD_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.eLpNorm_chartPushedRaw_le_const_mul_eLpNorm_riemannianMeasure_uniform_of_subset
        (I := I_hs) (M := M) g α hKα_compact hKα_sub (p := (2 : ℝ≥0∞))
          (by norm_num) (by norm_num)
  refine ⟨K * A * D,
    mul_nonneg (mul_nonneg hK_nonneg hA_pos.le) hD_pos.le, ?_⟩
  intro u hu i
  set v : M → ℝ := fun x : M => |u x| + Real.sqrt
    (g.inner x
      (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g u x)
      (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g u x)) with hv_def
  set vα : M → ℝ := Set.indicator Kα v with hvα_def
  set IntΩ : Set EuN :=
    DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
      (chartTargetEuclid (n := n) (M := M) α) with hIntΩ_def
  have hIntΩ_open : IsOpen IntΩ :=
    interiorHalfSpace_chartTargetEuclid_isOpen (n := n) (M := M) α
  have hIntΩ_sub : IntΩ ⊆ interior (extChartAt I_hs α).target := by
    apply interior_maximal _ hIntΩ_open
    intro y hy
    rw [hIntΩ_def, interiorHalfSpace_chartTargetEuclid_eq
      (n := n) (M := M)] at hy
    exact hy.1
  have hv_meas : Measurable v := by
    have hu_abs : Measurable (fun x : M => |u x|) := hu.continuous.measurable.abs
    have hgrad_cont : Continuous (fun x : M => Real.sqrt
        (g.inner x
          (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g u x)
          (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g u x))) :=
      Real.continuous_sqrt.comp
        (DifferentialGeometry.Geometry.Operator.WithBoundary.continuous_g_inner_gradFun_gradFun
          (n := n) (M := M) g hu hu)
    exact hu_abs.add hgrad_cont.measurable
  have hvα_meas : Measurable vα :=
    Measurable.indicator hv_meas (isClosed_tsupport _).measurableSet
  have hvα_supp : tsupport vα ⊆ Kα := by
    apply closure_minimal _ (isClosed_tsupport _)
    intro x hx
    by_contra hxK
    apply hx
    change (Set.indicator Kα v) x = 0
    rw [Set.indicator_of_notMem hxK]
  have hpoint : ∀ᵐ y ∂(volume.restrict IntΩ),
      ‖(fderiv ℝ
          (chartSmoothExt (n := n) (M := M) α
            (fun z : M => (ρ : M → ℝ) z * u z)) y)
          (EuclideanSpace.single i 1)‖ ≤
        K * chartSmoothExt (n := n) (M := M) α vα y := by
    filter_upwards [ae_restrict_mem hIntΩ_open.measurableSet] with y hy
    have hraw := hK_bound hu i (hIntΩ_sub hy)
    rw [Real.norm_eq_abs]
    simpa [ρ, Kα, v, vα, IntΩ] using hraw
  have hmono :
      eLpNorm
          (fun y : EuN =>
            (fderiv ℝ
              (chartSmoothExt (n := n) (M := M) α
                (fun z : M => (ρ : M → ℝ) z * u z)) y)
              (EuclideanSpace.single i 1))
          2 (volume.restrict IntΩ) ≤
        eLpNorm
          (fun y : EuN => K * chartSmoothExt (n := n) (M := M) α vα y)
          2 (volume.restrict IntΩ) :=
    eLpNorm_mono_ae_real hpoint
  refine hmono.trans ?_
  have hpull :
      eLpNorm
          (fun y : EuN => K * chartSmoothExt (n := n) (M := M) α vα y)
          2 (volume.restrict IntΩ) =
        ENNReal.ofReal K *
          eLpNorm (chartSmoothExt (n := n) (M := M) α vα)
            2 (volume.restrict IntΩ) := by
    have heq : (fun y : EuN => K * chartSmoothExt (n := n) (M := M) α vα y) =
        K • chartSmoothExt (n := n) (M := M) α vα := by
      funext y
      change K * _ = K • chartSmoothExt (n := n) (M := M) α vα y
      rw [smul_eq_mul]
    rw [heq, eLpNorm_const_smul]
    rw [Real.enorm_eq_ofReal hK_nonneg]
  rw [hpull]
  have hext := hA_bound vα
  have hraw := hD_bound hvα_meas hvα_supp
  rw [← DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_def
    (I := I_hs) (M := M) g] at hraw
  have hvα_point : ∀ x : M, ‖vα x‖ ≤ |u x| + Real.sqrt
      (g.inner x
        (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g u x)
        (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g u x)) := by
    intro x
    rw [Real.norm_eq_abs]
    by_cases hxK : x ∈ Kα
    · rw [hvα_def, Set.indicator_of_mem hxK, hv_def, abs_of_nonneg
        (add_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))]
    · rw [hvα_def, Set.indicator_of_notMem hxK, abs_zero]
      exact add_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hvα_Lp : eLpNorm vα 2
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I_hs M g) ≤
      eLpNorm u 2
          (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I_hs M g) +
        eLpNorm
          (fun x : M => Real.sqrt
            (g.inner x
              (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g u x)
              (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g u x)))
          2
          (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I_hs M g) := by
    refine (eLpNorm_mono_real hvα_point).trans ?_
    have hu_abs_aesm : AEStronglyMeasurable (fun x : M => |u x|)
        (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I_hs M g) :=
      hu.continuous.measurable.abs.aestronglyMeasurable
    have hgrad_aesm : AEStronglyMeasurable
        (fun x : M => Real.sqrt
          (g.inner x
            (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g u x)
            (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g u x)))
        (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I_hs M g) :=
      (Real.continuous_sqrt.comp
        (DifferentialGeometry.Geometry.Operator.WithBoundary.continuous_g_inner_gradFun_gradFun
          (n := n) (M := M) g hu hu)).aestronglyMeasurable
    refine (eLpNorm_add_le hu_abs_aesm hgrad_aesm (by norm_num)).trans ?_
    have habs : eLpNorm (fun x : M => |u x|) 2
        (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I_hs M g) =
        eLpNorm u 2
          (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I_hs M g) := by
      rw [show (fun x : M => |u x|) = fun x : M => ‖u x‖ from by
        funext x
        exact (Real.norm_eq_abs _).symm]
      exact eLpNorm_norm u
    rw [habs]
  calc
    ENNReal.ofReal K *
        eLpNorm (chartSmoothExt (n := n) (M := M) α vα)
          2 (volume.restrict IntΩ) ≤
      ENNReal.ofReal K *
        (ENNReal.ofReal A *
          eLpNorm
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw
              (I := I_hs) (M := M) α vα)
            2
            ((volume : Measure EuN').restrict
              (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
                (I := I_hs) (M := M) α))) := by
      gcongr
    _ ≤ ENNReal.ofReal K *
        (ENNReal.ofReal A *
          (ENNReal.ofReal D * eLpNorm vα 2
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
              I_hs M g))) := by
      gcongr
    _ ≤ ENNReal.ofReal K *
        (ENNReal.ofReal A *
          (ENNReal.ofReal D *
            (eLpNorm u 2
                (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I_hs M g) +
              eLpNorm
                (fun x : M => Real.sqrt
                  (g.inner x
                    (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g u x)
                    (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g u x)))
                2
                (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
                  I_hs M g)))) := by
      gcongr
    _ = ENNReal.ofReal (K * A * D) *
        (eLpNorm u 2
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I_hs M g) +
          eLpNorm
            (fun x : M => Real.sqrt
              (g.inner x
                (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g u x)
                (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g u x)))
            2
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I_hs M g)) := by
      rw [ENNReal.ofReal_mul (mul_nonneg hK_nonneg hA_pos.le),
        ENNReal.ofReal_mul hK_nonneg]
      ring

private lemma exists_eLpNorm_chartSmoothExt_pou_mul_le_const_mul
    (g : DifferentialGeometry.SmoothRiemannianMetric I_hs M) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : M → ℝ}, ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u →
      eLpNorm
          (chartSmoothExt (n := n) (M := M) α
            (fun z : M =>
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
                : C^∞⟮I_hs, M; ℝ⟯) z * u z))
          2
          (volume.restrict
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
              (chartTargetEuclid (n := n) (M := M) α))) ≤
        ENNReal.ofReal C *
          eLpNorm u 2
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I_hs M g) := by
  classical
  set ρ : C^∞⟮I_hs, M; ℝ⟯ :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α with hρ_def
  set Kα : Set M := tsupport ((ρ : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) with hKα_def
  have hKα_compact : IsCompact Kα := (isClosed_tsupport _).isCompact
  have hKα_sub : Kα ⊆ (chartAt (EuclideanHalfSpace n) α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M α
  obtain ⟨A, hA_pos, hA_bound⟩ :=
    exists_eLpNorm_chartSmoothExt_le_const_mul_chartPushedRaw
      (n := n) (M := M) α
  obtain ⟨D, hD_pos, hD_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.eLpNorm_chartPushedRaw_le_const_mul_eLpNorm_riemannianMeasure_uniform_of_subset
      (I := I_hs) (M := M) g α hKα_compact hKα_sub (p := (2 : ℝ≥0∞))
        (by norm_num) (by norm_num)
  refine ⟨A * D, mul_nonneg hA_pos.le hD_pos.le, ?_⟩
  intro u hu
  set f : M → ℝ := fun z : M => (ρ : M → ℝ) z * u z with hf_def
  have hf_meas : Measurable f := ρ.contMDiff.continuous.measurable.mul hu.continuous.measurable
  have hf_supp : tsupport f ⊆ Kα := by
    have heq : f = fun z : M => (ρ : M → ℝ) z • u z := by
      funext z
      simp [f, smul_eq_mul]
    rw [heq]
    exact tsupport_smul_subset_left
      (f := fun z : M => (ρ : M → ℝ) z) (g := u)
  have hext := hA_bound f
  have hraw := hD_bound hf_meas hf_supp
  rw [← DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_def
    (I := I_hs) (M := M) g] at hraw
  have hf_Lp : eLpNorm f 2
      (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I_hs M g) ≤
      eLpNorm u 2
        (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I_hs M g) := by
    apply eLpNorm_mono
    intro x
    rw [Real.norm_eq_abs, Real.norm_eq_abs, hf_def, abs_mul]
    calc
      |(ρ : M → ℝ) x| * |u x| ≤ 1 * |u x| := by
        gcongr
        exact DifferentialGeometry.Analysis.Sobolev.EquivalenceReverse.abs_chartAtlasPOU_le_one
          (I := I_hs) (M := M) α x
      _ = |u x| := one_mul _
  calc
    eLpNorm (chartSmoothExt (n := n) (M := M) α f) 2
        (volume.restrict
          (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
            (chartTargetEuclid (n := n) (M := M) α))) ≤
      ENNReal.ofReal A *
        eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw
            (I := I_hs) (M := M) α f)
          2
          ((volume : Measure EuN').restrict
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
              (I := I_hs) (M := M) α)) := hext
    _ ≤ ENNReal.ofReal A *
        (ENNReal.ofReal D * eLpNorm f 2
          (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I_hs M g)) := by
      gcongr
    _ ≤ ENNReal.ofReal A *
        (ENNReal.ofReal D * eLpNorm u 2
          (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I_hs M g)) := by
      gcongr
    _ = ENNReal.ofReal (A * D) *
        eLpNorm u 2
          (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I_hs M g) := by
      rw [ENNReal.ofReal_mul hA_pos.le]
      ring

private lemma exists_wkpNormHalfSpace_chartPushed_le_const_mul_intrinsic
    (g : DifferentialGeometry.SmoothRiemannianMetric I_hs M) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {u : M → ℝ}, ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u →
      AllChartsInteriorSupport (n := n) (M := M) u →
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
          (d := n) 1 2
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u)
          (chartTargetEuclid (n := n) (M := M) α) ≤
        ENNReal.ofReal C *
          (eLpNorm u 2
              (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I_hs M g) +
            eLpNorm
              (fun x : M => Real.sqrt
                (g.inner x
                  (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g u x)
                  (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g u x)))
              2
              (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I_hs M g)) := by
  classical
  obtain ⟨C₀, hC₀_nonneg, hC₀_bound⟩ :=
    exists_eLpNorm_chartSmoothExt_pou_mul_le_const_mul
      (n := n) (M := M) g α
  obtain ⟨C₁, hC₁_nonneg, hC₁_bound⟩ :=
    exists_eLpNorm_fderiv_chartSmoothExt_apply_le_const_mul
      (n := n) (M := M) g α
  refine ⟨C₀ + (n : ℝ) * C₁,
    add_nonneg hC₀_nonneg (mul_nonneg (Nat.cast_nonneg _) hC₁_nonneg), ?_⟩
  intro u hu h_int
  rw [wkpNormHalfSpace_chartPushed_eq_smooth_extension
    (n := n) (M := M) (by norm_num) hu h_int α]
  set S : ℝ≥0∞ :=
    eLpNorm u 2
        (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I_hs M g) +
      eLpNorm
        (fun x : M => Real.sqrt
          (g.inner x
            (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g u x)
            (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g u x)))
        2
        (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I_hs M g)
      with hS_def
  have hzero : eLpNorm
      (chartSmoothExt (n := n) (M := M) α
        (fun x : M =>
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
            : C^∞⟮I_hs, M; ℝ⟯) x * u x))
      2
      (volume.restrict
        (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
          (chartTargetEuclid (n := n) (M := M) α))) ≤
      ENNReal.ofReal C₀ * S := by
    rw [hS_def]
    refine (hC₀_bound hu).trans ?_
    gcongr
    exact le_self_add
  have hone : ∀ i : Fin n,
      eLpNorm
          (fun z : EuN =>
            (fderiv ℝ
              (chartSmoothExt (n := n) (M := M) α
                (fun x : M =>
                  (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
                    : C^∞⟮I_hs, M; ℝ⟯) x * u x)) z)
              (EuclideanSpace.single i 1))
          2
          (volume.restrict
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
              (chartTargetEuclid (n := n) (M := M) α))) ≤
        ENNReal.ofReal C₁ * S := by
    intro i
    rw [hS_def]
    exact hC₁_bound hu i
  have hsum := Finset.sum_le_sum
    (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hone i)
  have hconst :
      (∑ _ : Fin n, ENNReal.ofReal C₁ * S) =
        ENNReal.ofReal ((n : ℝ) * C₁) * S := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    rw [nsmul_eq_mul, ← mul_assoc]
    congr 1
    rw [show ((n : ℕ) : ℝ≥0∞) = ENNReal.ofReal (n : ℝ) by
      rw [ENNReal.ofReal_natCast]]
    rw [← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
  have hderiv :
      (∑ i : Fin n,
        eLpNorm
          (fun z : EuN =>
            (fderiv ℝ
              (chartSmoothExt (n := n) (M := M) α
                (fun x : M =>
                  (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
                    : C^∞⟮I_hs, M; ℝ⟯) x * u x)) z)
              (EuclideanSpace.single i 1))
          2
          (volume.restrict
            (DifferentialGeometry.Analysis.Sobolev.Euclidean.interiorHalfSpace
              (chartTargetEuclid (n := n) (M := M) α)))) ≤
        ENNReal.ofReal ((n : ℝ) * C₁) * S :=
    hsum.trans_eq hconst
  refine (add_le_add hzero hderiv).trans ?_
  rw [← add_mul]
  rw [ENNReal.ofReal_add hC₀_nonneg (mul_nonneg (Nat.cast_nonneg _) hC₁_nonneg)]

theorem wkpNormChart_le_const_mul_intrinsicLpComponents_smooth_uniform
    (g : DifferentialGeometry.SmoothRiemannianMetric I_hs M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {u : M → ℝ}, ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ u →
        AllChartsInteriorSupport (n := n) (M := M) u →
        wkpNormChart (n := n) (M := M) 1 2 u ≤
          ENNReal.ofReal C *
            (eLpNorm u 2
                (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I_hs M g) +
              eLpNorm
                (fun x : M => Real.sqrt
                  (g.inner x
                    (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g u x)
                    (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g u x)))
                2
                (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I_hs M g)) := by
  classical
  set S : Finset M :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOUFinset (I := I_hs) (M := M)
  set Cα : M → ℝ := fun α => Classical.choose
    (exists_wkpNormHalfSpace_chartPushed_le_const_mul_intrinsic
      (n := n) (M := M) g α)
  have hCα_nonneg : ∀ α : M, 0 ≤ Cα α := fun α =>
    (Classical.choose_spec
      (exists_wkpNormHalfSpace_chartPushed_le_const_mul_intrinsic
        (n := n) (M := M) g α)).1
  refine ⟨∑ α ∈ S, Cα α, Finset.sum_nonneg (fun α _ => hCα_nonneg α), ?_⟩
  intro u hu h_int
  rw [DifferentialGeometry.Analysis.Sobolev.WithBoundary.wkpNormChart_eq_finset_sum_withBoundary
    (n := n) (M := M) 1 (by norm_num) u]
  have h_per_chart : ∀ α ∈ S,
      DifferentialGeometry.Analysis.Sobolev.Euclidean.wkpNormHalfSpace
          (d := n) 1 2
          (chartPushed (n := n) (M := M)
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M) α u)
          (chartTargetEuclid (n := n) (M := M) α) ≤
        ENNReal.ofReal (Cα α) *
          (eLpNorm u 2
              (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I_hs M g) +
            eLpNorm
              (fun x : M => Real.sqrt
                (g.inner x
                  (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g u x)
                  (DifferentialGeometry.Geometry.Operator.gradFun (I := I_hs) g u x)))
              2
              (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure I_hs M g)) :=
    fun α _ => (Classical.choose_spec
      (exists_wkpNormHalfSpace_chartPushed_le_const_mul_intrinsic
        (n := n) (M := M) g α)).2 hu h_int
  refine (Finset.sum_le_sum h_per_chart).trans ?_
  rw [← Finset.sum_mul]
  gcongr
  rw [show (∑ α ∈ S, ENNReal.ofReal (Cα α)) = ENNReal.ofReal (∑ α ∈ S, Cα α) from
    (ENNReal.ofReal_sum_of_nonneg (fun α _ => hCα_nonneg α)).symm]

end EquivalenceReverse
end WithBoundary
end Sobolev
end Analysis
end DifferentialGeometry

end
