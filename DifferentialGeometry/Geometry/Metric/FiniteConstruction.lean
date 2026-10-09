import DifferentialGeometry.Geometry.Metric.CompactExistence
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

noncomputable section
open Bundle Manifold Set Function Metric ContinuousLinearMap
open scoped Manifold ContDiff Topology BigOperators

namespace DifferentialGeometry.Geometry

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] in
theorem localFiber_apply_mfderiv {c x : M} (hx : x ∈ (chartAt H c).source)
    (v w : TangentSpace I x) :
    localFiber (I := I) c x v w = @inner ℝ E _
      ((mfderiv I 𝓘(ℝ, E) (extChartAt I c) x : E →L[ℝ] E) v)
      ((mfderiv I 𝓘(ℝ, E) (extChartAt I c) x : E →L[ℝ] E) w) := by
  change @inner ℝ E _
    (((trivializationAt E (TangentSpace I) c).continuousLinearMapAt ℝ x : E →L[ℝ] E) v)
    (((trivializationAt E (TangentSpace I) c).continuousLinearMapAt ℝ x : E →L[ℝ] E) w) = _
  rw [TangentBundle.continuousLinearMapAt_trivializationAt hx]
  rfl

variable [T2Space M]

theorem weighted_localFiber_contMDiff (c : M) (f : SmoothBumpFunction I c) :
    ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun x => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) x (f x • localFiber (I := I) c x)) := by
  let : ∀ x : M, ContinuousAdd (TangentSpace I x →L[ℝ] ℝ) :=
    fun _ => inferInstanceAs (ContinuousAdd (E →L[ℝ] ℝ))
  apply ContMDiffOn.smul_section_of_tsupport (F := E →L[ℝ] E →L[ℝ] ℝ)
    (V := fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (s := localFiber (I := I) c) f.contMDiff.contMDiffOn
    (trivializationAt E (TangentSpace I) c).open_baseSet
  · simpa only [TangentBundle.trivializationAt_baseSet] using f.tsupport_subset_chartAt_source
  · exact DifferentialGeometry.Geometry.localFiber_contMDiffOn c

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
theorem exists_finite_bump_cover [CompactSpace M] :
    ∃ (f : ∀ c : M, SmoothBumpFunction I c) (s : Finset M), ∀ x : M,
      ∃ c ∈ s, x ∈ (chartAt H c).source ∧
        dist (extChartAt I c x) (extChartAt I c c) < (f c).rIn := by
  classical
  let f : ∀ c : M, SmoothBumpFunction I c := fun c => Classical.choice inferInstance
  let U (c : M) := (chartAt H c).source ∩
    extChartAt I c ⁻¹' ball (extChartAt I c c) (f c).rIn
  have hopen (c : M) : IsOpen (U c) := by
    have hc := (continuousOn_extChartAt (I := I) c).isOpen_inter_preimage
      (by simpa only [extChartAt_source] using (chartAt H c).open_source)
      (isOpen_ball (x := extChartAt I c c) (ε := (f c).rIn))
    simpa only [extChartAt_source] using hc
  have hcover : (univ : Set M) ⊆ ⋃ c, U c := by
    intro x _
    exact mem_iUnion.mpr ⟨x, mem_chart_source H x, by
      change dist (extChartAt I x x) (extChartAt I x x) < (f x).rIn
      simpa using (f x).rIn_pos⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hopen hcover
  refine ⟨f, s, fun x => ?_⟩
  obtain ⟨c, hc⟩ := mem_iUnion.mp (hs (mem_univ x))
  obtain ⟨hcs, hxc⟩ := mem_iUnion.mp hc
  exact ⟨c, hcs, hxc⟩

def finiteBumpMetric (f : ∀ c : M, SmoothBumpFunction I c) (s : Finset M)
    (hcover : ∀ x : M, ∃ c ∈ s, x ∈ (chartAt H c).source ∧
      dist (extChartAt I c x) (extChartAt I c c) < (f c).rIn) :
    ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _) := by
  classical
  let S : M → ℝ := fun x => ∑ c ∈ s, f c x
  have hS (x : M) : 0 < S x := by
    obtain ⟨c, hc, hxc, hdist⟩ := hcover x
    apply Finset.sum_pos' (fun i _ => (f i).nonneg)
    exact ⟨c, hc, by rw [(f c).one_of_dist_le hxc hdist.le]; exact zero_lt_one⟩
  let g (x : M) : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
    (S x)⁻¹ • ∑ c ∈ s, f c x • localFiber (I := I) c x
  have hgpos (x : M) (v : TangentSpace I x) (hv : v ≠ 0) : 0 < g x v v := by
    change 0 < (S x)⁻¹ * (∑ c ∈ s, f c x • localFiber (I := I) c x) v v
    apply mul_pos (inv_pos.mpr (hS x))
    simp only [sum_apply, smul_apply, smul_eq_mul]
    apply Finset.sum_pos'
    · intro c _
      apply mul_nonneg (f c).nonneg
      change 0 ≤ inner ℝ
        (((trivializationAt E (TangentSpace I) c).continuousLinearMapAt ℝ x : E →L[ℝ] E) v) _
      exact real_inner_self_nonneg
    · obtain ⟨c, hc, hxc, hdist⟩ := hcover x
      refine ⟨c, hc, mul_pos ?_ ?_⟩
      · rw [(f c).one_of_dist_le hxc hdist.le]; exact zero_lt_one
      · exact DifferentialGeometry.Geometry.localFiber_pos c
          (by simpa only [TangentBundle.trivializationAt_baseSet] using hxc) v hv
  refine {
    inner := g
    symm := ?_
    pos := hgpos
    isVonNBounded := fun x => DifferentialGeometry.Geometry.posDef_isVonNBounded (E := E) (g x : E →L[ℝ] E →L[ℝ] ℝ) (hgpos x)
    contMDiff := ?_ }
  · intro x v w
    change (S x)⁻¹ * (∑ c ∈ s, f c x • localFiber (I := I) c x) v w =
      (S x)⁻¹ * (∑ c ∈ s, f c x • localFiber (I := I) c x) w v
    simp only [sum_apply, smul_apply, smul_eq_mul]
    congr 1
    apply Finset.sum_congr rfl
    intro c _
    congr 1
    exact DifferentialGeometry.Geometry.localFiber_symm c x v w
  · have hSsmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ S :=
      ContMDiff.sum (fun c _ => (f c).contMDiff)
    exact (hSsmooth.inv₀ (fun x => (hS x).ne')).smul_section
      (ContMDiff.sum_section (F := E →L[ℝ] E →L[ℝ] ℝ)
        (V := fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
        (fun c _ => weighted_localFiber_contMDiff I c (f c)))

theorem finiteBumpMetric_inner (f : ∀ c : M, SmoothBumpFunction I c) (s : Finset M)
    (hcover : ∀ x : M, ∃ c ∈ s, x ∈ (chartAt H c).source ∧
      dist (extChartAt I c x) (extChartAt I c c) < (f c).rIn) (x : M) :
    (finiteBumpMetric I f s hcover).inner x =
      (∑ c ∈ s, f c x)⁻¹ • ∑ c ∈ s, f c x • localFiber (I := I) c x := rfl

theorem exists_finiteBumpMetric [CompactSpace M] :
    ∃ (f : ∀ c : M, SmoothBumpFunction I c) (s : Finset M)
      (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)),
      (∀ x : M, ∃ c ∈ s, x ∈ (chartAt H c).source ∧
        dist (extChartAt I c x) (extChartAt I c c) < (f c).rIn) ∧
      ∀ x, g.inner x = (∑ c ∈ s, f c x)⁻¹ • ∑ c ∈ s, f c x • localFiber (I := I) c x := by
  obtain ⟨f, s, hs⟩ := exists_finite_bump_cover I (M := M)
  exact ⟨f, s, finiteBumpMetric I f s hs, hs, finiteBumpMetric_inner I f s hs⟩

end DifferentialGeometry.Geometry
