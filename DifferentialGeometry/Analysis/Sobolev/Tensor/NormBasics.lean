import DifferentialGeometry.Analysis.Sobolev.Tensor.Defs

/-!
# Finiteness and the real-valued normed structure on the tensor `W^{2k, 2}` space

For a closed Riemannian manifold `(M, g)` modelled on a finite-dimensional real
inner product space `E` and fixed ranks `(r, s)`, the companion file
`Analysis/Sobolev/Tensor/Defs.lean` introduces the tensor Sobolev space
`W^{2k, 2}` as a `Submodule ℝ (SmoothCcTensor g r s)`, together with the
`ℝ≥0∞`-valued chart-aggregated norm `wtwokTwoNorm g k T` and its basic
algebraic inequalities.

This file completes the analytic side:

* **Finiteness.** For a smooth compactly-supported `(r, s)`-tensor section in
  `W^{2k, 2}`, the chart-aggregated norm `wtwokTwoNorm g k T` is finite. The
  argument mirrors the scalar precedent `wkpNormChart_lt_top_of_memWkpChart`:
  the canonical chart-atlas partition of unity has locally finite supports, so
  on a compact manifold only finitely many chart base points contribute, and
  each per-chart contribution is a finite sum of finite Euclidean Sobolev norms.

* **The real-valued norm.** `wtwokTwoNormReal g k T := (wtwokTwoNorm g k T).toReal`,
  with the non-negativity, vanishing-on-zero, triangle and homogeneity
  inequalities transported from the `ℝ≥0∞` versions using finiteness.

* **Separation and the normed structure.** A smooth compactly-supported tensor
  section all of whose chart components have vanishing scalar `W^{2k, 2}` norm
  is the zero section: the order-zero summand of the scalar `W^{2k, 2}` norm
  controls the `L²` norm of the (continuous) chart component on the open chart
  target, hence the chart component vanishes there; reassembling against the
  chart frame and using that the partition of unity sums to one recovers the
  section pointwise. Consequently `WtwokTwo g r s k` carries a genuine
  `NormedAddCommGroup` and `NormedSpace ℝ` structure (not merely a seminormed
  one).

Banach completeness of `WtwokTwo g r s k` is **not** developed here; it is
deferred to a later file.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Sobolev
namespace Tensor

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Sobolev.Euclidean
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- The tensor Sobolev norm is finite for any `W^{2k, 2}`-tensor section on a
closed manifold.

This mirrors the scalar chart-Sobolev precedent
`wkpNormChart_lt_top_of_memWkpChart`. The canonical chart-atlas partition of
unity has locally finite supports, so on a compact manifold only finitely many
chart base points `α` have a nonempty partition-of-unity support. For every
other `α` the chart component of any section is the zero function (the
partition-of-unity weight vanishes identically), hence its scalar Sobolev norm
is `0`. The chart-aggregating `tsum` therefore has finitely many nonzero terms,
each of which is a finite sum, over the `n ^ (r + s)` component multi-indices,
of finite Euclidean iterated Sobolev norms `wkpNorm (2 * k) 2`. -/
theorem wtwokTwoNorm_lt_top
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    {T : SmoothCcTensor g r s}
    (hT : MemWtwokTwo (I := I) (M := M) g k T) :
    wtwokTwoNorm (I := I) (M := M) g k T < ⊤ := by
  classical
  unfold wtwokTwoNorm
  set f : M → ℝ≥0∞ := fun α =>
    ∑ Idx : Fin r → Fin (Module.finrank ℝ E),
      ∑ Jdx : Fin s → Fin (Module.finrank ℝ E),
        wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
          (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
          (chartTargetEuclid (I := I) (M := M) α) with hf_def
  have hPOU_locFin : LocallyFinite
      (fun α : M => Function.support (chartAtlasPOU I M α : M → ℝ)) :=
    (chartAtlasPOU I M).locallyFinite
  have hSupport_finite :
      {α : M | (Function.support (chartAtlasPOU I M α : M → ℝ)).Nonempty}.Finite :=
    hPOU_locFin.finite_nonempty_of_compact
  set S : Set M :=
    {α : M | (Function.support (chartAtlasPOU I M α : M → ℝ)).Nonempty} with hS_def
  have hS_finite : S.Finite := hSupport_finite
  have hf_zero_off : ∀ α : M,
      (Function.support (chartAtlasPOU I M α : M → ℝ)) = ∅ → f α = 0 := by
    intro α hα
    have hρ_zero : ∀ x : M, (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x = 0 := by
      intro x
      have hx : x ∉ Function.support (chartAtlasPOU I M α : M → ℝ) := by
        rw [hα]; exact Set.notMem_empty x
      simpa [Function.mem_support] using hx
    rw [hf_def]
    refine Finset.sum_eq_zero ?_
    intro Idx _
    refine Finset.sum_eq_zero ?_
    intro Jdx _
    have hcomp_zero :
        tensorChartComp (I := I) (M := M) g r s T α Idx Jdx = (fun _ => (0 : ℝ)) := by
      funext y
      by_cases hy : y ∈ chartTargetEuclid (I := I) (M := M) α
      · rw [tensorChartComp_apply_of_mem (I := I) (M := M) g r s T α Idx Jdx hy]
        unfold tensorChartComponentPou
        rw [hρ_zero]
        ring
      · exact tensorChartComp_apply_of_notMem (I := I) (M := M) g r s T α Idx Jdx hy
    rw [hcomp_zero]
    exact wkpNorm_zero_fun_zero (d := Module.finrank ℝ E) (by norm_num)
      (chartTargetEuclid_isOpen (I := I) (M := M) α)
  have htsum_eq : ∑' α : M, f α = ∑ α ∈ hS_finite.toFinset, f α := by
    rw [tsum_eq_sum]
    intro α hα
    have hαS : α ∉ S := fun hαS => hα ((Set.Finite.mem_toFinset _).mpr hαS)
    have hempty : (Function.support (chartAtlasPOU I M α : M → ℝ)) = ∅ :=
      Set.not_nonempty_iff_eq_empty.mp (fun hne => hαS hne)
    exact hf_zero_off α hempty
  rw [htsum_eq]
  refine ENNReal.sum_lt_top.mpr ?_
  intro α _
  rw [hf_def]
  refine ENNReal.sum_lt_top.mpr ?_
  intro Idx _
  refine ENNReal.sum_lt_top.mpr ?_
  intro Jdx _
  exact wkpNorm_lt_top_of_memWkp (d := Module.finrank ℝ E) (hT α Idx Jdx)

/-- The tensor Sobolev norm of a `W^{2k, 2}`-tensor section is not `⊤`. -/
theorem wtwokTwoNorm_ne_top
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    {T : SmoothCcTensor g r s}
    (hT : MemWtwokTwo (I := I) (M := M) g k T) :
    wtwokTwoNorm (I := I) (M := M) g k T ≠ ⊤ :=
  (wtwokTwoNorm_lt_top (I := I) (M := M) g hT).ne

/-- If the tensor Sobolev norm of a section vanishes, then every scalar chart
component vanishes identically on its chart target.

The chart-aggregating `tsum` is a sum of non-negative `ℝ≥0∞` terms, so a zero
total forces every per-chart double sum — and hence every individual scalar
Euclidean Sobolev norm `wkpNorm (2 * k) 2 (tensorChartComp …)` — to vanish. The
order-zero summand of `wkpNorm` is the `L²` norm (`eLpNorm`) of the chart
component itself; its vanishing makes the component a.e.-zero on the open chart
target, and a continuous a.e.-zero function on an open set (for the
open-positive Lebesgue measure) vanishes identically there. -/
theorem tensorChartComp_eqOn_zero_of_wtwokTwoNorm_zero
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    {T : SmoothCcTensor g r s}
    (hnorm : wtwokTwoNorm (I := I) (M := M) g k T = 0)
    (α : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    Set.EqOn (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
      (fun _ => (0 : ℝ)) (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hchart_zero :
      ∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
        ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
          wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
            (tensorChartComp (I := I) (M := M) g r s T α Idx' Jdx')
            (chartTargetEuclid (I := I) (M := M) α) = 0 := by
    have hsumm : Summable
        (fun β : M =>
          ∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
              wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
                (tensorChartComp (I := I) (M := M) g r s T β Idx' Jdx')
                (chartTargetEuclid (I := I) (M := M) β)) := ENNReal.summable
    have htsum0 :
        (∑' β : M,
          ∑ Idx' : Fin r → Fin (Module.finrank ℝ E),
            ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
              wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
                (tensorChartComp (I := I) (M := M) g r s T β Idx' Jdx')
                (chartTargetEuclid (I := I) (M := M) β)) = 0 := by
      rw [← wtwokTwoNorm_eq_tsum (I := I) (M := M) g k T]; exact hnorm
    exact (ENNReal.tsum_eq_zero.mp htsum0) α
  have hwkp_zero :
      wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
        (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
        (chartTargetEuclid (I := I) (M := M) α) = 0 := by
    have hJ :
        ∑ Jdx' : Fin s → Fin (Module.finrank ℝ E),
          wkpNorm (d := Module.finrank ℝ E) (2 * k) 2
            (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx')
            (chartTargetEuclid (I := I) (M := M) α) = 0 :=
      (Finset.sum_eq_zero_iff.mp hchart_zero) Idx (Finset.mem_univ Idx)
    exact (Finset.sum_eq_zero_iff.mp hJ) Jdx (Finset.mem_univ Jdx)
  set u : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
    tensorChartComp (I := I) (M := M) g r s T α Idx Jdx with hu_def
  set Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :=
    chartTargetEuclid (I := I) (M := M) α with hΩ_def
  have hΩ_open : IsOpen Ω := chartTargetEuclid_isOpen (I := I) (M := M) α
  have hu_cont : Continuous u :=
    tensorChartComp_continuous (I := I) (M := M) g r s T α Idx Jdx
  have heLp_zero : eLpNorm u 2 (volume.restrict Ω) = 0 := by
    have hsum :
        wkpNorm (d := Module.finrank ℝ E) (2 * k) 2 u Ω =
          ∑ j ∈ Finset.range (2 * k + 1),
            ∑ a : Fin j → Fin (Module.finrank ℝ E),
              eLpNorm (iterWeakPartial (d := Module.finrank ℝ E) 2 j a u Ω) 2
                (volume.restrict Ω) :=
      wkpNorm_eq_sum (d := Module.finrank ℝ E) (2 * k) 2 u Ω
    have hj0 :
        ∑ a : Fin 0 → Fin (Module.finrank ℝ E),
          eLpNorm (iterWeakPartial (d := Module.finrank ℝ E) 2 0 a u Ω) 2
            (volume.restrict Ω) = 0 := by
      have hzero := hwkp_zero
      rw [hsum] at hzero
      have h0mem : (0 : ℕ) ∈ Finset.range (2 * k + 1) := by
        rw [Finset.mem_range]; omega
      exact (Finset.sum_eq_zero_iff.mp hzero) 0 h0mem
    have hUniq : ∀ a : Fin 0 → Fin (Module.finrank ℝ E),
        a = (fun i : Fin 0 => i.elim0) := fun a => by funext i; exact i.elim0
    haveI : Unique (Fin 0 → Fin (Module.finrank ℝ E)) :=
      { default := fun i : Fin 0 => i.elim0
        uniq := fun a => (hUniq a).symm ▸ rfl }
    rw [Fintype.sum_unique
        (f := fun a : Fin 0 → Fin (Module.finrank ℝ E) =>
          eLpNorm (iterWeakPartial (d := Module.finrank ℝ E) 2 0 a u Ω) 2
            (volume.restrict Ω))] at hj0
    rwa [iterWeakPartial_zero] at hj0
  have hu_aem : AEStronglyMeasurable u (volume.restrict Ω) :=
    hu_cont.aestronglyMeasurable
  have hu_ae : u =ᵐ[volume.restrict Ω] (fun _ => (0 : ℝ)) := by
    have := (eLpNorm_eq_zero_iff hu_aem (by norm_num)).mp heLp_zero
    simpa [Pi.zero_def] using this
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq hu_ae hΩ_open
    hu_cont.continuousOn continuousOn_const

/-- The base set of the `TensorRSModel`-trivialization at `α` is the chart
source at `α`. (The product trivialization of a `(0, r)`- and a
`(0, s)`-tensor bundle, each in turn a tensor power of the tangent bundle,
shares the tangent-bundle base set, namely the chart source.) -/
private lemma tensorRS_baseSet_eq_chart_source
    (α : M) (r s : ℕ) :
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun x : M => TensorRSSpace r s I x) α).baseSet =
      (chartAt H α).source := by
  change ((trivializationAt (Tensor0SModel r ℝ E)
        (fun x : M => Tensor0SSpace r I x) α).baseSet) ∩
      ((trivializationAt (Tensor0SModel s ℝ E)
        (fun x : M => Tensor0SSpace s I x) α).baseSet) =
        (chartAt H α).source
  change (trivializationAt E (TangentSpace I) α).baseSet ∩
        (trivializationAt E (TangentSpace I) α).baseSet = (chartAt H α).source
  rw [Set.inter_self]
  rfl

/-- If the trivialization-projected fibre value of a tensor section vanishes at
a point of the chart source, then the section itself vanishes there.

The trivialization of the `(r, s)`-tensor bundle is fibrewise a linear equiv on
the base set, so its fibrewise component `continuousLinearMapAt` is injective
there; applying the fibrewise inverse `symmL` (a continuous linear map, hence
zero-preserving) recovers the section value. -/
private lemma toSection_eq_zero_of_tensorTrivProj_eq_zero
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) {x : M}
    (hx : x ∈ (chartAt H α).source)
    (hzero : tensorTrivProj (I := I) (M := M) g r s S α x = 0) :
    S.toSection x = 0 := by
  set e := trivializationAt (TensorRSModel r s ℝ E)
    (fun y : M => TensorRSSpace r s I y) α with he_def
  have hx_base : x ∈ e.baseSet := by
    rw [he_def, tensorRS_baseSet_eq_chart_source (I := I) (M := M) α r s]
    exact hx
  have hproj : e.continuousLinearMapAt ℝ x (S.toSection x) = 0 := by
    rw [← hzero]; rfl
  have hrecover : e.symmL ℝ x (e.continuousLinearMapAt ℝ x (S.toSection x)) =
      S.toSection x :=
    Bundle.Trivialization.symmL_continuousLinearMapAt e hx_base (S.toSection x)
  rw [hproj, map_zero] at hrecover
  exact hrecover.symm

/-- **Separation.** A smooth compactly-supported `(r, s)`-tensor section whose
tensor Sobolev norm vanishes is the zero section.

By `tensorChartComp_eqOn_zero_of_wtwokTwoNorm_zero`, every scalar chart
component vanishes on its chart target. Reassembling the chart components
against the chart frame (`tensorChartPushed_eq_sum_tensorChartComp`) shows the
partition-of-unity-weighted chart-pushed tensor vanishes on each chart target;
on the chart source this reads `ρ_α(x) • tensorTrivProj S α x = 0`. Since the
partition of unity sums to one, for every point `x` some chart base point `α`
has `ρ_α(x) > 0`, forcing `tensorTrivProj S α x = 0` and hence — by
`toSection_eq_zero_of_tensorTrivProj_eq_zero` — `S.toSection x = 0`. As `x` was
arbitrary, the section is zero. -/
theorem eq_zero_of_wtwokTwoNorm_zero
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    {T : SmoothCcTensor g r s}
    (hnorm : wtwokTwoNorm (I := I) (M := M) g k T = 0) :
    T = 0 := by
  classical
  refine SmoothCcTensor.ext ?_
  refine ContMDiffSection.ext (fun x => ?_)
  obtain ⟨α, hα_pos⟩ :=
    (chartAtlasPOU I M).exists_pos_of_mem (Set.mem_univ x)
  have hx_supp : x ∈ Function.support (chartAtlasPOU I M α : M → ℝ) := by
    rw [Function.mem_support]; exact ne_of_gt hα_pos
  have hx_chart : x ∈ (chartAt H α).source :=
    tsupport_subset_chartAt_source (chartAtlasPOU I M)
      (chartAtlasPOU_isSubordinate I M) α (subset_tsupport _ hx_supp)
  have hx_ext : x ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]; exact hx_chart
  set y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) :=
    toEuclidean (E := E) ((extChartAt I α) x) with hy_def
  have hy_mem : y ∈ chartTargetEuclid (I := I) (M := M) α := by
    refine ⟨(extChartAt I α) x, ?_, rfl⟩
    exact (extChartAt I α).map_source hx_ext
  have hround : (extChartAt I α).symm ((toEuclidean (E := E)).symm y) = x := by
    rw [hy_def]
    rw [ContinuousLinearEquiv.symm_apply_apply]
    exact (extChartAt I α).left_inv hx_ext
  have hcomp_zero :
      ∀ (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        tensorChartComp (I := I) (M := M) g r s T α Idx Jdx y = 0 := by
    intro Idx Jdx
    have := tensorChartComp_eqOn_zero_of_wtwokTwoNorm_zero
      (I := I) (M := M) g hnorm α Idx Jdx hy_mem
    simpa using this
  have hpushed_zero :
      tensorChartPushed (I := I) (M := M) g r s T α y = 0 := by
    rw [tensorChartPushed_eq_sum_tensorChartComp (I := I) (M := M) g r s T α y]
    refine Finset.sum_eq_zero ?_
    intro Idx _
    refine Finset.sum_eq_zero ?_
    intro Jdx _
    rw [hcomp_zero Idx Jdx, zero_smul]
  have hpushed_eq :
      tensorChartPushed (I := I) (M := M) g r s T α y =
        (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x •
          tensorTrivProj (I := I) (M := M) g r s T α x := by
    rw [tensorChartPushed_def (I := I) (M := M) g r s T α y]
    rw [tensorChartPushedRawModel_apply_of_mem (I := I) (M := M) g r s T α hy_mem]
    rw [hround]
  have hweighted_zero :
      (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x •
        tensorTrivProj (I := I) (M := M) g r s T α x = 0 := by
    rw [← hpushed_eq]; exact hpushed_zero
  have hproj_zero : tensorTrivProj (I := I) (M := M) g r s T α x = 0 := by
    have hρ_ne : (chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) x ≠ 0 := ne_of_gt hα_pos
    exact (smul_eq_zero.mp hweighted_zero).resolve_left hρ_ne
  have hsection : T.toSection x = 0 :=
    toSection_eq_zero_of_tensorTrivProj_eq_zero
      (I := I) (M := M) g r s T α hx_chart hproj_zero
  rw [SmoothCcTensor.toSection_zero, hsection]
  rw [ContMDiffSection.coe_zero]
  rfl

/-- The real-valued (`ℝ≥0∞.toReal`) tensor Sobolev norm. -/
def wtwokTwoNormReal
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) : ℝ :=
  (wtwokTwoNorm (I := I) (M := M) g k T).toReal

@[simp] lemma wtwokTwoNormReal_def
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    wtwokTwoNormReal (I := I) (M := M) g k T =
      (wtwokTwoNorm (I := I) (M := M) g k T).toReal := rfl

/-- The real-valued tensor Sobolev norm is non-negative. -/
theorem wtwokTwoNormReal_nonneg
    (g : SmoothRiemannianMetric I M) {r s : ℕ}
    (k : ℕ) (T : SmoothCcTensor g r s) :
    0 ≤ wtwokTwoNormReal (I := I) (M := M) g k T :=
  ENNReal.toReal_nonneg

/-- The real-valued tensor Sobolev norm of the zero section is zero. -/
theorem wtwokTwoNormReal_zero_section
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (k : ℕ) :
    wtwokTwoNormReal (I := I) (M := M) g k (0 : SmoothCcTensor g r s) = 0 := by
  unfold wtwokTwoNormReal
  rw [wtwokTwoNorm_zero_section (I := I) (M := M) g k]
  simp

/-- The triangle inequality for the real-valued tensor Sobolev norm. -/
theorem wtwokTwoNormReal_add_le
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    {T₁ T₂ : SmoothCcTensor g r s}
    (h₁ : MemWtwokTwo (I := I) (M := M) g k T₁)
    (h₂ : MemWtwokTwo (I := I) (M := M) g k T₂) :
    wtwokTwoNormReal (I := I) (M := M) g k (T₁ + T₂) ≤
      wtwokTwoNormReal (I := I) (M := M) g k T₁ +
        wtwokTwoNormReal (I := I) (M := M) g k T₂ := by
  unfold wtwokTwoNormReal
  have h₁_ne : wtwokTwoNorm (I := I) (M := M) g k T₁ ≠ ⊤ :=
    wtwokTwoNorm_ne_top (I := I) (M := M) g h₁
  have h₂_ne : wtwokTwoNorm (I := I) (M := M) g k T₂ ≠ ⊤ :=
    wtwokTwoNorm_ne_top (I := I) (M := M) g h₂
  have hsum_le := wtwokTwoNorm_add_le (I := I) (M := M) g h₁ h₂
  have hRHS_ne : wtwokTwoNorm (I := I) (M := M) g k T₁ +
      wtwokTwoNorm (I := I) (M := M) g k T₂ ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨h₁_ne, h₂_ne⟩
  have hToReal := ENNReal.toReal_mono hRHS_ne hsum_le
  rwa [ENNReal.toReal_add h₁_ne h₂_ne] at hToReal

/-- The scalar-homogeneity identity for the real-valued tensor Sobolev norm. -/
theorem wtwokTwoNormReal_smul
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    (c : ℝ) {T : SmoothCcTensor g r s}
    (h : MemWtwokTwo (I := I) (M := M) g k T) :
    wtwokTwoNormReal (I := I) (M := M) g k (c • T) =
      ‖c‖ * wtwokTwoNormReal (I := I) (M := M) g k T := by
  unfold wtwokTwoNormReal
  rw [wtwokTwoNorm_smul (I := I) (M := M) g c h]
  rw [ENNReal.toReal_mul, toReal_enorm]

/-- Each per-chart term of the tensor Sobolev norm is monotone in the regularity
order `k`: the Euclidean iterated Sobolev norm `wkpNorm` is monotone in its
order, applied componentwise. -/
private lemma wtwokTwoNorm_le_succ_aux
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (k : ℕ)
    (T : SmoothCcTensor g r s) :
    wtwokTwoNorm (I := I) (M := M) g k T ≤
      wtwokTwoNorm (I := I) (M := M) g (k + 1) T := by
  unfold wtwokTwoNorm
  refine ENNReal.tsum_le_tsum ?_
  intro α
  refine Finset.sum_le_sum ?_
  intro Idx _
  refine Finset.sum_le_sum ?_
  intro Jdx _
  have hle : 2 * k ≤ 2 * (k + 1) := by omega
  exact wkpNorm_mono_order (d := Module.finrank ℝ E) hle
    (tensorChartComp (I := I) (M := M) g r s T α Idx Jdx)
    (chartTargetEuclid (I := I) (M := M) α)

/-- The tensor Sobolev norm is monotone in the regularity order `k`: a
lower-order norm is bounded by a higher-order one. -/
theorem wtwokTwoNorm_le_succ
    (g : SmoothRiemannianMetric I M) {r s : ℕ} (k : ℕ)
    (T : SmoothCcTensor g r s) :
    wtwokTwoNorm (I := I) (M := M) g k T ≤
      wtwokTwoNorm (I := I) (M := M) g (k + 1) T :=
  wtwokTwoNorm_le_succ_aux (I := I) (M := M) g k T

/-- The real-valued tensor Sobolev norm is monotone in the regularity order
`k`, for any `W^{2(k+1), 2}`-tensor section. -/
theorem wtwokTwoNormReal_le_succ
    (g : SmoothRiemannianMetric I M) {r s : ℕ} {k : ℕ}
    {T : SmoothCcTensor g r s}
    (hT : MemWtwokTwo (I := I) (M := M) g (k + 1) T) :
    wtwokTwoNormReal (I := I) (M := M) g k T ≤
      wtwokTwoNormReal (I := I) (M := M) g (k + 1) T := by
  unfold wtwokTwoNormReal
  have hk_ne : wtwokTwoNorm (I := I) (M := M) g (k + 1) T ≠ ⊤ :=
    wtwokTwoNorm_ne_top (I := I) (M := M) g hT
  exact ENNReal.toReal_mono hk_ne (wtwokTwoNorm_le_succ (I := I) (M := M) g k T)

/-- The underlying smooth compactly-supported tensor section of an element of
`WtwokTwo g r s k`. -/
def wtwokTwoFun
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {k : ℕ}
    (T : WtwokTwo (I := I) (M := M) g r s k) : SmoothCcTensor g r s :=
  Subtype.val (α := SmoothCcTensor g r s)
    (p := fun T => T ∈ wtwokTwoSubmodule (I := I) (M := M) g r s k) T

/-- The membership property of the underlying section of an element of
`WtwokTwo g r s k`. -/
lemma wtwokTwoFun_memWtwokTwo
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {k : ℕ}
    (T : WtwokTwo (I := I) (M := M) g r s k) :
    MemWtwokTwo (I := I) (M := M) g k (wtwokTwoFun T) :=
  Subtype.property
    (α := SmoothCcTensor g r s)
    (p := fun T => T ∈ wtwokTwoSubmodule (I := I) (M := M) g r s k) T

@[simp] lemma wtwokTwoFun_zero
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {k : ℕ} :
    wtwokTwoFun (0 : WtwokTwo (I := I) (M := M) g r s k) =
      (0 : SmoothCcTensor g r s) := rfl

@[simp] lemma wtwokTwoFun_add
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {k : ℕ}
    (T₁ T₂ : WtwokTwo (I := I) (M := M) g r s k) :
    wtwokTwoFun (T₁ + T₂) = wtwokTwoFun T₁ + wtwokTwoFun T₂ := rfl

@[simp] lemma wtwokTwoFun_smul
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {k : ℕ}
    (c : ℝ) (T : WtwokTwo (I := I) (M := M) g r s k) :
    wtwokTwoFun (c • T) = c • wtwokTwoFun T := rfl

/-- `wtwokTwoFun` is injective: an element of `WtwokTwo g r s k` is determined
by its underlying section. -/
lemma wtwokTwoFun_injective
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {k : ℕ} :
    Function.Injective
      (wtwokTwoFun (I := I) (M := M) (g := g) (r := r) (s := s) (k := k)) := by
  intro T₁ T₂ h
  exact Subtype.ext h

/-- `Norm` instance on `WtwokTwo g r s k`, with norm
`(wtwokTwoNorm g k T).toReal`. -/
instance instNormWtwokTwo
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ) :
    Norm (WtwokTwo (I := I) (M := M) g r s k) where
  norm T := wtwokTwoNormReal (I := I) (M := M) g k (wtwokTwoFun T)

@[simp] lemma norm_wtwokTwo_def
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {k : ℕ}
    (T : WtwokTwo (I := I) (M := M) g r s k) :
    ‖T‖ = wtwokTwoNormReal (I := I) (M := M) g k (wtwokTwoFun T) := rfl

/-- The `NormedSpace.Core` for `WtwokTwo g r s k`: non-negativity, scalar
homogeneity, the triangle inequality, and — crucially — the genuine separation
axiom `‖T‖ = 0 ↔ T = 0`. The forward separation direction is the analytic
content: finiteness of the norm turns the vanishing real-valued norm into a
vanishing `ℝ≥0∞`-valued norm, and `eq_zero_of_wtwokTwoNorm_zero` then forces the
zero section. -/
lemma wtwokTwo_normedSpace_core
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ) :
    NormedSpace.Core ℝ (WtwokTwo (I := I) (M := M) g r s k) where
  norm_nonneg T := ENNReal.toReal_nonneg
  norm_smul c T := by
    have hmem := wtwokTwoFun_memWtwokTwo T
    change wtwokTwoNormReal (I := I) (M := M) g k (wtwokTwoFun (c • T)) =
      ‖c‖ * wtwokTwoNormReal (I := I) (M := M) g k (wtwokTwoFun T)
    rw [wtwokTwoFun_smul]
    rw [wtwokTwoNormReal_smul (I := I) (M := M) g c hmem]
  norm_triangle T₁ T₂ := by
    have h₁ := wtwokTwoFun_memWtwokTwo T₁
    have h₂ := wtwokTwoFun_memWtwokTwo T₂
    change wtwokTwoNormReal (I := I) (M := M) g k (wtwokTwoFun (T₁ + T₂)) ≤
      wtwokTwoNormReal (I := I) (M := M) g k (wtwokTwoFun T₁) +
        wtwokTwoNormReal (I := I) (M := M) g k (wtwokTwoFun T₂)
    rw [wtwokTwoFun_add]
    exact wtwokTwoNormReal_add_le (I := I) (M := M) g h₁ h₂
  norm_eq_zero_iff := by
    intro T
    constructor
    · intro hT
      have hmem := wtwokTwoFun_memWtwokTwo T
      have hne : wtwokTwoNorm (I := I) (M := M) g k (wtwokTwoFun T) ≠ ⊤ :=
        wtwokTwoNorm_ne_top (I := I) (M := M) g hmem
      have hreal : wtwokTwoNormReal (I := I) (M := M) g k (wtwokTwoFun T) = 0 :=
        hT
      have hnorm0 : wtwokTwoNorm (I := I) (M := M) g k (wtwokTwoFun T) = 0 := by
        have hzero := hreal
        unfold wtwokTwoNormReal at hzero
        exact (ENNReal.toReal_eq_zero_iff _).mp hzero |>.resolve_right hne
      have hfun0 : wtwokTwoFun T = (0 : SmoothCcTensor g r s) :=
        eq_zero_of_wtwokTwoNorm_zero (I := I) (M := M) g hnorm0
      apply wtwokTwoFun_injective (I := I) (M := M)
      rw [hfun0, wtwokTwoFun_zero]
    · intro hT
      rw [hT, norm_wtwokTwo_def, wtwokTwoFun_zero]
      exact wtwokTwoNormReal_zero_section (I := I) (M := M) g k

/-- `WtwokTwo g r s k` carries a genuine `NormedAddCommGroup` structure: the
real-valued tensor Sobolev norm separates points (a vanishing norm forces the
zero section). -/
instance instNormedAddCommGroupWtwokTwo
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ) :
    NormedAddCommGroup (WtwokTwo (I := I) (M := M) g r s k) :=
  NormedAddCommGroup.ofCore (wtwokTwo_normedSpace_core (I := I) (M := M) g r s k)

/-- `WtwokTwo g r s k` is a normed real vector space. -/
instance instNormedSpaceRealWtwokTwo
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (k : ℕ) :
    NormedSpace ℝ (WtwokTwo (I := I) (M := M) g r s k) :=
  NormedSpace.ofCore (wtwokTwo_normedSpace_core (I := I) (M := M) g r s k)

/-- The norm of an element of `WtwokTwo g r s k` equals the real-valued tensor
Sobolev norm of the underlying section. -/
theorem norm_wtwokTwo_eq
    {g : SmoothRiemannianMetric I M} {r s : ℕ} {k : ℕ}
    (T : WtwokTwo (I := I) (M := M) g r s k) :
    ‖T‖ = wtwokTwoNormReal (I := I) (M := M) g k (wtwokTwoFun T) := rfl

end Tensor
end Sobolev
end Analysis
end DifferentialGeometry
