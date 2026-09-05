import DifferentialGeometry.Analysis.Sobolev.WithBoundary.Embedding.MorreyManifold
import DifferentialGeometry.Analysis.Sobolev.Euclidean.Embedding.RellichHigher
import DifferentialGeometry.Analysis.Sobolev.Manifold.MeasureBridgeUniform
import DifferentialGeometry.Analysis.Integration.Measure.Rellich
import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.WithBoundary.Divergence.LocalFormula
import DifferentialGeometry.External.DeGiorgi.LpFunctionToolkit

noncomputable section

open MeasureTheory Set Filter Topology Bundle Manifold Function
open scoped Manifold ContDiff ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace WithBoundary

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "EuN" => EuclideanSpace ℝ (Fin n)
local notation "I_hs" => modelWithCornersEuclideanHalfSpace n

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private lemma allChartsInteriorSupport_of_tsupport_subset_interior
    {u : M → ℝ}
    (hu : tsupport u ⊆ (modelWithCornersEuclideanHalfSpace n).interior M) :
    AllChartsInteriorSupport (n := n) (M := M) u := by
  intro α
  unfold chartSmoothExtInteriorSupport
  rintro y ⟨x, hx, rfl⟩
  have hx_pou : x ∈ tsupport
      ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) :=
    tsupport_mul_subset_left hx
  have hx_src : x ∈ (chartAt (EuclideanHalfSpace n) α).source :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M α hx_pou
  have hx_u : x ∈ tsupport u := tsupport_mul_subset_right hx
  have hy_int : extChartAt I_hs α x ∈ interior (extChartAt I_hs α).target :=
    DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary.extChartAt_mem_interior_target_of_isInteriorPoint
      α hx_src (hu hx_u)
  have hy_range : extChartAt I_hs α x ∈ interior (Set.range I_hs) :=
    interior_mono (extChartAt_target_subset_range α) hy_int
  rwa [interior_range_modelWithCornersEuclideanHalfSpace] at hy_range

private lemma exists_chart_rellich_subseq
    (g : DifferentialGeometry.SmoothRiemannianMetric I_hs M)
    {u : ℕ → M → ℝ}
    (hu_smooth : ∀ k, ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ (u k))
    (hu_int : ∀ k,
      tsupport (u k) ⊆ (modelWithCornersEuclideanHalfSpace n).interior M)
    {C : ℝ}
    (hu_bdd : ∀ k, wkpNormChart (n := n) (M := M) 1 2 (u k) ≤ ENNReal.ofReal C)
    (α : M) (ψ : ℕ → ℕ) :
    ∃ σ : ℕ → ℕ, StrictMono σ ∧
      ∃ R : ℝ, 0 < R ∧
        (∀ k, tsupport
          (chartSmoothExt (n := n) (M := M) α
            (fun x : M =>
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
                : C^∞⟮I_hs, M; ℝ⟯) x * u (ψ (σ k)) x)) ⊆
          Metric.ball (0 : EuN) R) ∧
        ∃ w : EuN → ℝ,
          MemLp w 2 (volume.restrict (Metric.ball (0 : EuN) R)) ∧
          Tendsto
            (fun k => eLpNorm
              (fun z => chartSmoothExt (n := n) (M := M) α
                  (fun x : M =>
                    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
                      : C^∞⟮I_hs, M; ℝ⟯) x * u (ψ (σ k)) x) z - w z)
              2 (volume.restrict (Metric.ball (0 : EuN) R)))
            atTop (𝓝 0) := by
  classical
  obtain ⟨R, hR, hcontrol⟩ :=
    exists_chart_smooth_extension_sobolev_control (n := n) (M := M) g α
  let v : ℕ → EuN → ℝ := fun k =>
    chartSmoothExt (n := n) (M := M) α
      (fun x : M =>
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u (ψ k) x)
  have hv_control : ∀ k,
      ContDiff ℝ ∞ (v k) ∧ HasCompactSupport (v k) ∧
        tsupport (v k) ⊆ Metric.ball (0 : EuN) R ∧
        eLpNorm (v k) 2 (volume.restrict (Metric.ball (0 : EuN) R)) ≤
          wkpNormChart (n := n) (M := M) 1 2 (u (ψ k)) ∧
        (∑ i : Fin n,
          eLpNorm (fun z : EuN =>
              (fderiv ℝ (v k) z) (EuclideanSpace.single i 1)) 2
            (volume.restrict (Metric.ball (0 : EuN) R))) ≤
          wkpNormChart (n := n) (M := M) 1 2 (u (ψ k)) := by
    intro k
    have h := hcontrol (q := 2) (by norm_num)
      (hu_smooth (ψ k))
      (allChartsInteriorSupport_of_tsupport_subset_interior
        (n := n) (M := M) (hu_int (ψ k)))
    dsimp only at h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩
  have hv_smooth : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (v k) := fun k => (hv_control k).1
  have hv_supp : ∀ k, HasCompactSupport (v k) := fun k => (hv_control k).2.1
  have hv_sub : ∀ k, tsupport (v k) ⊆ Metric.ball (0 : EuN) R :=
    fun k => (hv_control k).2.2.1
  have hv_fun : ∀ k,
      eLpNorm (v k) 2 (volume.restrict (Metric.ball (0 : EuN) R)) ≤
        ENNReal.ofReal C := fun k =>
    (hv_control k).2.2.2.1.trans (hu_bdd (ψ k))
  have hv_grad : ∀ k,
      (∑ i : Fin n,
        eLpNorm (fun z : EuN =>
            (fderiv ℝ (v k) z) (EuclideanSpace.single i 1)) 2
          (volume.restrict (Metric.ball (0 : EuN) R))) ≤
        ENNReal.ofReal C := fun k =>
    (hv_control k).2.2.2.2.trans (hu_bdd (ψ k))
  rcases DifferentialGeometry.Analysis.Sobolev.Euclidean.rellich_kondrachov_W01p_seq_smooth
    (d := n) Metric.isOpen_ball Metric.isBounded_ball hv_smooth hv_supp hv_sub hv_fun hv_grad
    with ⟨σ, hσ, w, hw, hconv⟩
  exact ⟨σ, hσ, R, hR, fun k => hv_sub (σ k), w, hw, hconv⟩

private lemma exists_diagonal_chart_rellich_subseq
    (g : DifferentialGeometry.SmoothRiemannianMetric I_hs M)
    {u : ℕ → M → ℝ}
    (hu_smooth : ∀ k, ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ (u k))
    (hu_int : ∀ k,
      tsupport (u k) ⊆ (modelWithCornersEuclideanHalfSpace n).interior M)
    {C : ℝ}
    (hu_bdd : ∀ k, wkpNormChart (n := n) (M := M) 1 2 (u k) ≤ ENNReal.ofReal C)
    (S : Finset M) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ α ∈ S,
        ∃ R : ℝ, 0 < R ∧
          (∀ k, tsupport
            (chartSmoothExt (n := n) (M := M) α
              (fun x : M =>
                (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
                  : C^∞⟮I_hs, M; ℝ⟯) x * u (φ k) x)) ⊆
            Metric.ball (0 : EuN) R) ∧
          ∃ w : EuN → ℝ,
            MemLp w 2 (volume.restrict (Metric.ball (0 : EuN) R)) ∧
            Tendsto
              (fun k => eLpNorm
                (fun z => chartSmoothExt (n := n) (M := M) α
                    (fun x : M =>
                      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
                        : C^∞⟮I_hs, M; ℝ⟯) x * u (φ k) x) z - w z)
                2 (volume.restrict (Metric.ball (0 : EuN) R)))
              atTop (𝓝 0) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      exact ⟨id, strictMono_id, fun α hα => absurd hα (Finset.notMem_empty α)⟩
  | insert a S ha ih =>
      rcases ih with ⟨φ, hφ, hprev⟩
      rcases exists_chart_rellich_subseq (n := n) (M := M) g hu_smooth hu_int hu_bdd a φ with
        ⟨σ, hσ, R, hR, hsupp, w, hw, hconv⟩
      refine ⟨φ ∘ σ, hφ.comp hσ, ?_⟩
      intro α hα
      rcases Finset.mem_insert.mp hα with rfl | hα
      · exact ⟨R, hR, hsupp, w, hw, hconv⟩
      · rcases hprev α hα with ⟨Rα, hRα, hsuppα, wα, hwα, hconvα⟩
        refine ⟨Rα, hRα, fun k => hsuppα (σ k), wα, hwα, ?_⟩
        exact hconvα.comp
          (tendsto_atTop_atTop_of_monotone hσ.monotone
            (fun k => ⟨k, hσ.id_le k⟩))

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
private lemma exists_eLpNorm_chartPushedRaw_le_const_mul_chartSmoothExt
    (α : M) :
    ∃ A : ℝ≥0∞, 0 < A ∧ A ≠ ⊤ ∧
      ∀ (f : M → ℝ) {R : ℝ},
        tsupport (chartSmoothExt (n := n) (M := M) α f) ⊆
            Metric.ball (0 : EuN) R →
          eLpNorm
              (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw
                (I := I_hs) (M := M) α f)
              2
              ((volume : Measure
                (EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN)))).restrict
                (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
                  (I := I_hs) (M := M) α)) ≤
            A * eLpNorm (chartSmoothExt (n := n) (M := M) α f) 2
              (volume.restrict (Metric.ball (0 : EuN) R)) := by
  classical
  let e : EuN ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN)) :=
    toEuclidean (E := EuN)
  let μe : Measure EuN := Measure.map
    (e.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN)) → EuN)
    (volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN))))
  let c : ℝ≥0 := Measure.addHaarScalarFactor μe (volume : Measure EuN)
  let A : ℝ≥0∞ := ↑(c ^ (2 : ℝ≥0∞).toReal⁻¹)
  have hc : c ≠ 0 := by
    exact (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure
      μe (volume : Measure EuN)).ne'
  have hc_pos : 0 < c := bot_lt_iff_ne_bot.mpr hc
  have hμe : μe = c • (volume : Measure EuN) :=
    Measure.isAddLeftInvariant_eq_smul μe (volume : Measure EuN)
  refine ⟨A, ?_, by simp [A], ?_⟩
  · simp only [A, ENNReal.coe_pos]
    positivity
  intro f R hsupp
  let raw : EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN)) → ℝ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw
      (I := I_hs) (M := M) α f
  let ext : EuN → ℝ := chartSmoothExt (n := n) (M := M) α f
  have hraw : raw = fun y => ext (e.symm y) := by
    exact chartPushedRaw_eq_chartSmoothExt_comp_toEuclidean_symm
      (n := n) (M := M) α f
  have he : MeasurableEmbedding (e.symm :
      EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN)) → EuN) :=
    e.symm.toHomeomorph.measurableEmbedding
  have hfull : eLpNorm raw 2
        (volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN)))) =
      eLpNorm ext 2 μe := by
    rw [hraw]
    change eLpNorm (ext ∘ (e.symm :
          EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN)) → EuN)) 2
        (volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN)))) =
      eLpNorm ext 2 (Measure.map
        (e.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN)) → EuN)
        (volume : Measure (EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN)))))
    exact (MeasurableEmbedding.eLpNorm_map_measure
        (μ := (volume : Measure
          (EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN)))))
        (f := (e.symm :
          EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN)) → EuN))
        (g := ext) (p := (2 : ℝ≥0∞)) he).symm
  have hrestrict : eLpNorm ext 2 (volume : Measure EuN) =
      eLpNorm ext 2 (volume.restrict (Metric.ball (0 : EuN) R)) := by
    have heq : ext = (Metric.ball (0 : EuN) R).indicator ext := by
      funext z
      by_cases hz : z ∈ Metric.ball (0 : EuN) R
      · rw [Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz]
        exact image_eq_zero_of_notMem_tsupport (fun hzs => hz (hsupp hzs))
    calc
      eLpNorm ext 2 volume =
          eLpNorm ((Metric.ball (0 : EuN) R).indicator ext) 2 volume := by
        rw [← heq]
      _ = eLpNorm ext 2 (volume.restrict (Metric.ball (0 : EuN) R)) :=
        eLpNorm_indicator_eq_eLpNorm_restrict measurableSet_ball
  refine (eLpNorm_mono_measure raw Measure.restrict_le_self).trans ?_
  rw [hfull, hμe, eLpNorm_smul_measure_of_ne_zero' hc, hrestrict]
  rfl

omit [IsManifold I_hs ∞ M] [T2Space M] [CompactSpace M] in
private lemma chartSmoothExt_sub (α : M) (f h : M → ℝ) :
    chartSmoothExt (n := n) (M := M) α (fun x => f x - h x) =
      fun z => chartSmoothExt (n := n) (M := M) α f z -
        chartSmoothExt (n := n) (M := M) α h z := by
  classical
  funext z
  unfold chartSmoothExt
  split_ifs <;> ring

private lemma tsupport_sub_subset_union
    {X : Type*} [TopologicalSpace X] (f h : X → ℝ) :
    tsupport (fun x => f x - h x) ⊆ tsupport f ∪ tsupport h := by
  rw [tsupport]
  refine ((isClosed_tsupport f).union (isClosed_tsupport h)).closure_subset_iff.mpr ?_
  intro x hx
  by_contra hx_union
  rw [Set.mem_union, not_or] at hx_union
  apply hx
  change f x - h x = 0
  rw [image_eq_zero_of_notMem_tsupport hx_union.1,
    image_eq_zero_of_notMem_tsupport hx_union.2, sub_zero]

private lemma tsupport_pou_mul_sub_subset_tsupport_pou
    (α : M) (f h : M → ℝ) :
    tsupport (fun x =>
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * f x -
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * h x) ⊆
      tsupport
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ) := by
  refine (tsupport_sub_subset_union
    (fun x =>
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * f x)
    (fun x =>
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) x * h x)).trans ?_
  exact union_subset
    (tsupport_mul_subset_left (f :=
      ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ)) (g := f))
    (tsupport_mul_subset_left (f :=
      ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
        : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ)) (g := h))

private lemma eLpNorm_sub_cauchy_of_tendsto_zero
    {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {v : ℕ → X → ℝ} {w : X → ℝ}
    (hv : ∀ k, AEStronglyMeasurable (v k) μ)
    (hw : AEStronglyMeasurable w μ)
    (hconv : Tendsto
      (fun k => eLpNorm (fun x => v k x - w x) 2 μ) atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N,
        eLpNorm (fun x => v j x - v k x) 2 μ ≤ ENNReal.ofReal ε := by
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero] at hconv
  rcases hconv (ENNReal.ofReal (ε / 2))
      (ENNReal.ofReal_pos.mpr (by linarith)) with ⟨N, hN⟩
  refine ⟨N, fun j hj k hk => ?_⟩
  have htriangle : eLpNorm (fun x => v j x - v k x) 2 μ ≤
      eLpNorm (fun x => v j x - w x) 2 μ +
        eLpNorm (fun x => w x - v k x) 2 μ := by
    have hfun : (fun x => v j x - v k x) =
        fun x => (v j x - w x) + (w x - v k x) := by
      funext x
      ring
    rw [hfun]
    exact eLpNorm_add_le
      ((hv j).sub hw) (hw.sub (hv k)) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hswap : eLpNorm (fun x => w x - v k x) 2 μ =
      eLpNorm (fun x => v k x - w x) 2 μ := by
    have hfun : (fun x => w x - v k x) = -(fun x => v k x - w x) := by
      funext x
      simp
    rw [hfun, eLpNorm_neg]
  rw [hswap] at htriangle
  refine htriangle.trans ?_
  have hj' := hN j hj
  have hk' := hN k hk
  calc
    eLpNorm (fun x => v j x - w x) 2 μ +
        eLpNorm (fun x => v k x - w x) 2 μ ≤
      ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
        add_le_add hj' hk'
    _ = ENNReal.ofReal ε := by
      rw [← ENNReal.ofReal_add (by linarith : (0 : ℝ) ≤ ε / 2)
        (by linarith : (0 : ℝ) ≤ ε / 2)]
      congr 1
      ring

private lemma eLpNorm_pou_mul_sub_cauchy_of_chart_tendsto
    (g : DifferentialGeometry.SmoothRiemannianMetric I_hs M)
    {u : ℕ → M → ℝ}
    (hu_smooth : ∀ k, ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ (u k))
    (hu_int : ∀ k,
      tsupport (u k) ⊆ (modelWithCornersEuclideanHalfSpace n).interior M)
    (α : M) {φ : ℕ → ℕ} {R : ℝ}
    (hsupp : ∀ k, tsupport
      (chartSmoothExt (n := n) (M := M) α
        (fun x : M =>
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
            : C^∞⟮I_hs, M; ℝ⟯) x * u (φ k) x)) ⊆
      Metric.ball (0 : EuN) R)
    {w : EuN → ℝ}
    (hw : MemLp w 2 (volume.restrict (Metric.ball (0 : EuN) R)))
    (hconv : Tendsto
      (fun k => eLpNorm
        (fun z => chartSmoothExt (n := n) (M := M) α
            (fun x : M =>
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
                : C^∞⟮I_hs, M; ℝ⟯) x * u (φ k) x) z - w z)
        2 (volume.restrict (Metric.ball (0 : EuN) R)))
      atTop (𝓝 0)) :
    ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N,
        eLpNorm
          (fun x : M =>
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
                : C^∞⟮I_hs, M; ℝ⟯) x * u (φ j) x -
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
                : C^∞⟮I_hs, M; ℝ⟯) x * u (φ k) x)
          2
          (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I_hs) g
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)) ≤
          ENNReal.ofReal ε := by
  classical
  let v : ℕ → EuN → ℝ := fun k =>
    chartSmoothExt (n := n) (M := M) α
      (fun x : M =>
        (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) x * u (φ k) x)
  have hv : ∀ k,
      AEStronglyMeasurable (v k)
        (volume.restrict (Metric.ball (0 : EuN) R)) := by
    intro k
    obtain ⟨R', hR', hcontrol⟩ :=
      exists_chart_smooth_extension_sobolev_control (n := n) (M := M) g α
    have hsmooth := (hcontrol (q := 2) (by norm_num)
      (hu_smooth (φ k))
      (allChartsInteriorSupport_of_tsupport_subset_interior
        (n := n) (M := M) (hu_int (φ k)))).1
    exact hsmooth.continuous.measurable.aestronglyMeasurable
  obtain ⟨C, hC_pos, hC_bound⟩ :=
    DifferentialGeometry.Analysis.Sobolev.Chart.eLpNorm_riemannianMeasure_le_const_mul_eLpNorm_chartPushedRaw_uniform_of_subset
      (I := I_hs) (M := M) g α
      (isClosed_tsupport
        ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
          : C^∞⟮I_hs, M; ℝ⟯) : M → ℝ)).isCompact
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M α)
      (p := 2) (by norm_num) (by norm_num)
  obtain ⟨A, hA_pos, hA_top, hA_bound⟩ :=
    exists_eLpNorm_chartPushedRaw_le_const_mul_chartSmoothExt
      (n := n) (M := M) α
  let D : ℝ := C * A.toReal
  have hA_toReal_pos : 0 < A.toReal := ENNReal.toReal_pos hA_pos.ne' hA_top
  have hD_pos : 0 < D := mul_pos hC_pos hA_toReal_pos
  intro ε hε
  rcases eLpNorm_sub_cauchy_of_tendsto_zero hv hw.1 hconv
      (ε / D) (div_pos hε hD_pos) with ⟨N, hN⟩
  refine ⟨N, fun j hj k hk => ?_⟩
  let f : M → ℝ := fun x =>
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) x * u (φ j) x
  let h : M → ℝ := fun x =>
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯) x * u (φ k) x
  have hf_meas : Measurable f :=
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯).contMDiff.continuous.measurable.mul
      (hu_smooth (φ j)).continuous.measurable
  have hh_meas : Measurable h :=
    (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
      : C^∞⟮I_hs, M; ℝ⟯).contMDiff.continuous.measurable.mul
      (hu_smooth (φ k)).continuous.measurable
  have hglobal := hC_bound (hf_meas.sub hh_meas)
    (tsupport_pou_mul_sub_subset_tsupport_pou
      (n := n) (M := M) α (u (φ j)) (u (φ k)))
  have hext_supp : tsupport
      (chartSmoothExt (n := n) (M := M) α (fun x => f x - h x)) ⊆
        Metric.ball (0 : EuN) R := by
    rw [chartSmoothExt_sub (n := n) (M := M)]
    exact (tsupport_sub_subset_union (v j) (v k)).trans
      (union_subset (hsupp j) (hsupp k))
  have hraw := hA_bound (fun x => f x - h x) hext_supp
  rw [chartSmoothExt_sub (n := n) (M := M)] at hraw
  have hlocal := hN j hj k hk
  have hD_eq : ENNReal.ofReal D = ENNReal.ofReal C * A := by
    change ENNReal.ofReal (C * A.toReal) = ENNReal.ofReal C * A
    rw [ENNReal.ofReal_mul hC_pos.le, ENNReal.ofReal_toReal hA_top]
  calc
    eLpNorm (fun x => f x - h x) 2
        (DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I_hs) g
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)) ≤
      ENNReal.ofReal C *
        eLpNorm
          (DifferentialGeometry.Analysis.Sobolev.Chart.chartPushedRaw
            (I := I_hs) (M := M) α (fun x => f x - h x))
          2
          ((volume : Measure
            (EuclideanSpace ℝ (Fin (Module.finrank ℝ EuN)))).restrict
            (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid
              (I := I_hs) (M := M) α)) := hglobal
    _ ≤ ENNReal.ofReal C *
        (A * eLpNorm (fun z => v j z - v k z) 2
          (volume.restrict (Metric.ball (0 : EuN) R))) :=
      by gcongr
    _ ≤ ENNReal.ofReal C * (A * ENNReal.ofReal (ε / D)) :=
      by gcongr
    _ = (ENNReal.ofReal C * A) * ENNReal.ofReal (ε / D) := by
      rw [mul_assoc]
    _ = ENNReal.ofReal D * ENNReal.ofReal (ε / D) := by rw [hD_eq]
    _ = ENNReal.ofReal (D * (ε / D)) :=
      (ENNReal.ofReal_mul hD_pos.le).symm
    _ = ENNReal.ofReal ε := by
      congr 1
      field_simp

theorem rellich_kondrachov_chart_seq_of_tsupport_subset_interior
    (g : DifferentialGeometry.SmoothRiemannianMetric I_hs M)
    {u : ℕ → M → ℝ}
    (hu_smooth : ∀ k, ContMDiff I_hs 𝓘(ℝ, ℝ) ∞ (u k))
    (hu_int : ∀ k,
      tsupport (u k) ⊆ (modelWithCornersEuclideanHalfSpace n).interior M)
    {C : ℝ}
    (hu_bdd : ∀ k, wkpNormChart (n := n) (M := M) 1 2 (u k) ≤ ENNReal.ofReal C) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ u_lim : M → ℝ,
        MemLp u_lim 2
          (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
            (I := I_hs) (M := M) g) ∧
        Tendsto
          (fun k => eLpNorm (fun x => u (φ k) x - u_lim x) 2
            (DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure
              (I := I_hs) (M := M) g))
          atTop (𝓝 0) := by
  classical
  let μg : Measure M :=
    DifferentialGeometry.Integral.Measure.riemannianMeasure (I := I_hs) g
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
  let _ : IsFiniteMeasure μg :=
    DifferentialGeometry.Integral.Measure.riemannianMeasure_isFiniteMeasure_of_compactSpace
      (I := I_hs) (M := M) g
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M)
      (DifferentialGeometry.Integral.Measure.chartAtlasPOU_isSubordinate I_hs M)
  let S : Finset M :=
    DifferentialGeometry.Integral.Measure.chartAtlasPOUFinset (I := I_hs) (M := M)
  rcases exists_diagonal_chart_rellich_subseq
      (n := n) (M := M) g hu_smooth hu_int hu_bdd S with
    ⟨φ, hφ, hcharts⟩
  let fSeq : ℕ → M → ℝ := fun k => u (φ k)
  have hf_memLp : ∀ k, MemLp (fSeq k) 2 μg := by
    intro k
    exact (hu_smooth (φ k)).continuous.memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hf_cauchy : Tendsto
      (fun jk : ℕ × ℕ => eLpNorm (fSeq jk.1 - fSeq jk.2) 2 μg)
      atTop (𝓝 0) := by
    rw [ENNReal.tendsto_atTop_zero]
    intro ε hε
    by_cases hε_top : ε = ⊤
    · subst ε
      exact ⟨(0, 0), fun _ _ => le_top⟩
    let d : ℕ := S.attach.card + 1
    have hd_pos : 0 < d := Nat.zero_lt_succ _
    have hd_ne : (d : ℝ≥0∞) ≠ 0 := by exact_mod_cast hd_pos.ne'
    have hquot_pos : 0 < ε / (d : ℝ≥0∞) :=
      ENNReal.div_pos hε.ne' (ENNReal.natCast_ne_top d)
    have hquot_top : ε / (d : ℝ≥0∞) ≠ ⊤ :=
      ENNReal.div_ne_top hε_top hd_ne
    let δ : ℝ := (ε / (d : ℝ≥0∞)).toReal
    have hδ_pos : 0 < δ := ENNReal.toReal_pos hquot_pos.ne' hquot_top
    have hN_exists : ∀ α : {x : M // x ∈ S},
        ∃ N : ℕ, ∀ j ≥ N, ∀ k ≥ N,
          eLpNorm
            (fun x : M =>
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α.1
                  : C^∞⟮I_hs, M; ℝ⟯) x * u (φ j) x -
                (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α.1
                  : C^∞⟮I_hs, M; ℝ⟯) x * u (φ k) x)
            2 μg ≤ ENNReal.ofReal δ := by
      intro α
      rcases hcharts α.1 α.2 with ⟨R, hR, hsupp, w, hw, hconv⟩
      exact eLpNorm_pou_mul_sub_cauchy_of_chart_tendsto
        (n := n) (M := M) g hu_smooth hu_int α.1 hsupp hw hconv δ hδ_pos
    choose N hN using hN_exists
    let Nmax : ℕ := S.attach.sup N
    refine ⟨(Nmax, Nmax), ?_⟩
    rintro ⟨j, k⟩ hjk
    have hj_ge : ∀ α ∈ S.attach, j ≥ N α := fun α hα =>
      le_trans (Finset.le_sup (f := N) hα) hjk.1
    have hk_ge : ∀ α ∈ S.attach, k ≥ N α := fun α hα =>
      le_trans (Finset.le_sup (f := N) hα) hjk.2
    have hdiff_eq : (fun x : M => u (φ j) x - u (φ k) x) =
        fun x => ∑ α ∈ S.attach,
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α.1
              : C^∞⟮I_hs, M; ℝ⟯) x * u (φ j) x -
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α.1
              : C^∞⟮I_hs, M; ℝ⟯) x * u (φ k) x) := by
      funext x
      rw [Finset.sum_sub_distrib]
      have hsum_j :
          ∑ α ∈ S.attach,
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α.1
                : C^∞⟮I_hs, M; ℝ⟯) x * u (φ j) x = u (φ j) x := by
        have h_attach := Finset.sum_attach S
          (f := fun α : M =>
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
              : C^∞⟮I_hs, M; ℝ⟯) x * u (φ j) x)
        rw [h_attach, ← Finset.sum_mul]
        change (∑ α ∈ S,
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
            : M → ℝ) x) * u (φ j) x = u (φ j) x
        rw [show S =
          DifferentialGeometry.Integral.Measure.chartAtlasPOUFinset
            (I := I_hs) (M := M) from rfl]
        rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartAtlasPOU_finset_sum_eq_one,
          one_mul]
      have hsum_k :
          ∑ α ∈ S.attach,
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α.1
                : C^∞⟮I_hs, M; ℝ⟯) x * u (φ k) x = u (φ k) x := by
        have h_attach := Finset.sum_attach S
          (f := fun α : M =>
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
              : C^∞⟮I_hs, M; ℝ⟯) x * u (φ k) x)
        rw [h_attach, ← Finset.sum_mul]
        change (∑ α ∈ S,
          (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α
            : M → ℝ) x) * u (φ k) x = u (φ k) x
        rw [show S =
          DifferentialGeometry.Integral.Measure.chartAtlasPOUFinset
            (I := I_hs) (M := M) from rfl]
        rw [DifferentialGeometry.Analysis.Sobolev.Chart.chartAtlasPOU_finset_sum_eq_one,
          one_mul]
      rw [hsum_j, hsum_k]
    have hsum_fun : (fun x : M => ∑ α ∈ S.attach,
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α.1
              : C^∞⟮I_hs, M; ℝ⟯) x * u (φ j) x -
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α.1
              : C^∞⟮I_hs, M; ℝ⟯) x * u (φ k) x)) =
        ∑ α ∈ S.attach, fun x : M =>
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α.1
              : C^∞⟮I_hs, M; ℝ⟯) x * u (φ j) x -
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α.1
              : C^∞⟮I_hs, M; ℝ⟯) x * u (φ k) x) := by
      funext x
      rw [Finset.sum_apply]
    rw [show fSeq j - fSeq k = fun x => u (φ j) x - u (φ k) x from rfl,
      hdiff_eq, hsum_fun]
    have hmeas : ∀ α ∈ S.attach,
        AEStronglyMeasurable
          (fun x : M =>
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α.1
                : C^∞⟮I_hs, M; ℝ⟯) x * u (φ j) x -
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α.1
                : C^∞⟮I_hs, M; ℝ⟯) x * u (φ k) x)
          μg := by
      intro α _
      exact (((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α.1
          : C^∞⟮I_hs, M; ℝ⟯).contMDiff.continuous.measurable.mul
            (hu_smooth (φ j)).continuous.measurable).sub
          ((DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α.1
          : C^∞⟮I_hs, M; ℝ⟯).contMDiff.continuous.measurable.mul
            (hu_smooth (φ k)).continuous.measurable)).aestronglyMeasurable
    refine (eLpNorm_sum_le hmeas (by norm_num)).trans ?_
    have hterm : ∀ α ∈ S.attach,
        eLpNorm
          (fun x : M =>
            (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α.1
                : C^∞⟮I_hs, M; ℝ⟯) x * u (φ j) x -
              (DifferentialGeometry.Integral.Measure.chartAtlasPOU I_hs M α.1
                : C^∞⟮I_hs, M; ℝ⟯) x * u (φ k) x)
          2 μg ≤ ENNReal.ofReal δ := fun α _ =>
      hN α j (hj_ge α (Finset.mem_attach S α)) k
        (hk_ge α (Finset.mem_attach S α))
    refine (Finset.sum_le_sum hterm).trans ?_
    have hδ_eq : ENNReal.ofReal δ = ε / (d : ℝ≥0∞) :=
      ENNReal.ofReal_toReal hquot_top
    rw [Finset.sum_const, nsmul_eq_mul, hδ_eq]
    calc
      (S.attach.card : ℝ≥0∞) * (ε / (d : ℝ≥0∞)) ≤
          (d : ℝ≥0∞) * (ε / (d : ℝ≥0∞)) := by
        gcongr
        exact_mod_cast Nat.le_succ S.attach.card
      _ = ε := ENNReal.mul_div_cancel hd_ne (ENNReal.natCast_ne_top d)
  rcases BareFunction.scalar_cauchy_to_limit
      (μ := μg) (p := 2) (by norm_num) (by norm_num) hf_memLp hf_cauchy with
    ⟨u_lim, hu_lim, hlim⟩
  refine ⟨φ, hφ, u_lim, ?_, ?_⟩
  · simpa [μg, DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_def]
      using hu_lim
  · rw [DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure_def]
    change Tendsto
      (fun k => eLpNorm (fun x => u (φ k) x - u_lim x) 2 μg) atTop (𝓝 0)
    have heq : (fun k => eLpNorm (fSeq k - u_lim) 2 μg) =
        fun k => eLpNorm (fun x => u (φ k) x - u_lim x) 2 μg := by
      funext k
      apply eLpNorm_congr_ae
      exact Filter.Eventually.of_forall fun x => rfl
    rw [← heq]
    exact hlim

end WithBoundary
end Sobolev
end Analysis
end DifferentialGeometry

end
