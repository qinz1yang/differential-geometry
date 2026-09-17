import DifferentialGeometry.Topology.Compactness.SublevelComponents
import DifferentialGeometry.Topology.Morse.ExtremumChart
import DifferentialGeometry.Topology.Morse.QuadraticComponent
import DifferentialGeometry.Topology.Morse.RegularLevel.Components

open Set Metric
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Morse

theorem isMinOn_univ_of_isPreconnected_lt
    {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p : M}
    (hnd : IsNondegenerateCriticalPointAt I f p) (hmin : IsLocalMin f p)
    (hconn : ∀ a, IsPreconnected {x | f x < a}) : IsMinOn f univ p := by
  obtain ⟨R, hR, χ, hsource, hχ0, hnormal⟩ :=
    exists_quadratic_chart_of_isLocalMin hf hnd hmin
  let r := R / 2
  have hr : 0 < r := half_pos hR
  have hclosed : closedBall 0 r ⊆ χ.source := by
    rw [hsource]
    exact closedBall_subset_ball (half_lt_self hR)
  have hcomp := χ.toOpenPartialHomeomorph.closedBall_image_eq_connectedComponentIn_sublevel
    hr.le (isCompact_closedBall 0 r) hclosed (by norm_num : (0 : ℝ) < 1)
    (f := f) (fun y hy => by
      change f (χ y) = f (χ 0) + 1 / 2 * ‖y‖ ^ 2
      rw [hχ0, hnormal y hy]
      ring)
  simp only [show χ.toOpenPartialHomeomorph 0 = p from hχ0] at hcomp
  have hp : p ∈ {x | f x < f p + 1 / 2 * r ^ 2} := by
    change f p < f p + 1 / 2 * r ^ 2
    nlinarith [sq_pos_of_pos hr]
  have hsub := (hconn (f p + 1 / 2 * r ^ 2)).subset_connectedComponentIn hp
    (show {x | f x < f p + 1 / 2 * r ^ 2} ⊆ f ⁻¹' Iic (f p + 1 / 2 * r ^ 2) from by
      intro x hx
      change f x ≤ f p + 1 / 2 * r ^ 2
      exact hx.le)
  intro x _
  by_contra hx
  have hxlt : f x < f p := lt_of_not_ge hx
  have hxmem := hsub (show x ∈ {x | f x < f p + 1 / 2 * r ^ 2} from hxlt.trans hp)
  rw [← hcomp] at hxmem
  obtain ⟨y, hy, rfl⟩ := hxmem
  change f (χ y) < f p at hxlt
  rw [hnormal y (hclosed hy)] at hxlt
  nlinarith [sq_nonneg ‖y‖]

theorem isMaxOn_univ_of_isPreconnected_gt
    {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p : M}
    (hnd : IsNondegenerateCriticalPointAt I f p) (hmax : IsLocalMax f p)
    (hconn : ∀ a, IsPreconnected {x | a < f x}) : IsMaxOn f univ p := by
  have hnd' : IsNondegenerateCriticalPointAt I (fun x => -f x) p := by
    simpa only [zero_sub] using
      (DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_const_sub_iff hf
        BoundarylessManifold.isInteriorPoint 0).mpr hnd
  have hconn' (a : ℝ) : IsPreconnected {x | -f x < a} := by
    convert hconn (-a) using 1
    ext x
    simp only [mem_ofPred_eq]
    constructor <;> intro hx <;> linarith
  have hmin := isMinOn_univ_of_isPreconnected_lt hf.neg hnd' hmax.neg hconn'
  intro x hx
  exact neg_le_neg_iff.mp (show -f p ≤ -f x from hmin hx)

theorem isMaxOn_connectedComponentIn_superlevel_of_no_critical_values
    {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p : M}
    (hnd : IsNondegenerateCriticalPointAt I f p) (hmax : IsLocalMax f p)
    {a : ℝ} (ha : a < f p) (hcompact : IsCompact (f ⁻¹' Icc a (f p)))
    (hregular : ∀ x, f x ∈ Ico a (f p) → ¬ IsCriticalPointAt I f x) :
    IsMaxOn f (connectedComponentIn {x | a ≤ f x} p) p := by
  obtain ⟨R, hR, χ, hsource, hχ0, hnormal⟩ := exists_quadratic_chart_of_isLocalMax hf hnd hmax
  obtain ⟨r, hr, hrsmall⟩ := exists_between (lt_min hR (Real.sqrt_pos.mpr (sub_pos.mpr ha)))
  have hrsq : r ^ 2 < f p - a := by
    have h := sq_lt_sq₀ hr.le (Real.sqrt_nonneg (f p - a)) |>.mpr
      (hrsmall.trans_le (min_le_right _ _))
    rwa [Real.sq_sqrt (sub_pos.mpr ha).le] at h
  let b := f p + (-1) / 2 * r ^ 2
  have hab : a < b := by dsimp [b]; nlinarith [sq_nonneg r]
  have hbp : b < f p := by dsimp [b]; nlinarith [sq_pos_of_pos hr]
  have hrsource : closedBall 0 r ⊆ χ.source := by
    rw [hsource]
    exact closedBall_subset_ball (hrsmall.trans_le (min_le_left _ _))
  have hcap := χ.toOpenPartialHomeomorph.closedBall_image_eq_connectedComponentIn_superlevel
    hr.le (isCompact_closedBall 0 r) hrsource (by norm_num : (-1 : ℝ) < 0)
    (f := f) (fun y hy => by
      change f (χ y) = f (χ 0) + (-1) / 2 * ‖y‖ ^ 2
      rw [hχ0, hnormal y hy]
      ring)
  simp only [show χ.toOpenPartialHomeomorph 0 = p from hχ0] at hcap
  change χ '' closedBall 0 r = connectedComponentIn {x | b ≤ f x} p at hcap
  obtain ⟨Φ, _, _, hcomponents, _⟩ := exists_diffeomorph_superlevel_components_of_no_critical_values
    hf hab.le (hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.continuous)
      (fun _ hx => ⟨hx.1, hx.2.trans hbp.le⟩))
    (fun x hx => hregular x ⟨hx.1, hx.2.trans_lt hbp⟩)
  intro q hq
  by_contra hnot
  have hpq : f p < f q := lt_of_not_ge hnot
  have hpqcomp : connectedComponentIn {x | b ≤ f x} p =
      connectedComponentIn {x | b ≤ f x} q := by
    rw [← hcomponents p hbp.le, ← hcomponents q (hbp.trans hpq).le,
      connectedComponentIn_eq hq]
  have hqcap : q ∈ χ '' closedBall 0 r := by
    rw [hcap, hpqcomp]
    exact mem_connectedComponentIn (hbp.trans hpq).le
  obtain ⟨y, hy, rfl⟩ := hqcap
  rw [hnormal y (hrsource hy)] at hpq
  nlinarith [sq_nonneg ‖y‖]

theorem isMinOn_connectedComponentIn_sublevel_of_no_critical_values
    {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p : M}
    (hnd : IsNondegenerateCriticalPointAt I f p) (hmin : IsLocalMin f p)
    {a : ℝ} (ha : f p < a) (hcompact : IsCompact (f ⁻¹' Icc (f p) a))
    (hregular : ∀ x, f x ∈ Ioc (f p) a → ¬ IsCriticalPointAt I f x) :
    IsMinOn f (connectedComponentIn {x | f x ≤ a} p) p := by
  have hnd' : IsNondegenerateCriticalPointAt I (fun x => -f x) p := by
    simpa only [zero_sub] using
      (DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_const_sub_iff hf
        BoundarylessManifold.isInteriorPoint 0).mpr hnd
  have hcompact' : IsCompact ((fun x => -f x) ⁻¹' Icc (-a) (-f p)) := by
    convert hcompact using 1
    ext x
    change (-a ≤ -f x ∧ -f x ≤ -f p) ↔ (f p ≤ f x ∧ f x ≤ a)
    constructor <;> intro hx <;> constructor <;> linarith [hx.1, hx.2]
  have hregular' (x : M) (hx : -f x ∈ Ico (-a) (-f p)) :
      ¬ IsCriticalPointAt I (fun x => -f x) x := by
    intro hc
    have hc' : IsCriticalPointAt I f x :=
      (DifferentialGeometry.Morse.isCriticalPointAt_const_sub_iff
        (hf.mdifferentiableAt (by simp)) 0).mp (by simpa only [zero_sub] using hc)
    exact hregular x ⟨by linarith [hx.2], by linarith [hx.1]⟩ hc'
  have hmax := isMaxOn_connectedComponentIn_superlevel_of_no_critical_values
    hf.neg hnd' hmin.neg (neg_lt_neg ha) hcompact' hregular'
  have hset : {x | -a ≤ -f x} = {x | f x ≤ a} := by
    ext x
    change -a ≤ -f x ↔ f x ≤ a
    exact neg_le_neg_iff
  rw [hset] at hmax
  intro x hx
  exact neg_le_neg_iff.mp (show -f x ≤ -f p from hmax hx)

theorem isMaxOn_connectedComponentIn_gt_of_no_critical_values
    {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p : M}
    (hnd : IsNondegenerateCriticalPointAt I f p) (hmax : IsLocalMax f p)
    {a : ℝ} (hcompact : IsCompact (f ⁻¹' Icc a (f p)))
    (hregular : ∀ x, f x ∈ Ioo a (f p) → ¬ IsCriticalPointAt I f x) :
    IsMaxOn f (connectedComponentIn {x | a < f x} p) p := by
  let : LocallyPathConnectedSpace H := I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  intro q hq
  obtain ⟨b, hab, hqb⟩ := hf.continuous.exists_lt_mem_connectedComponentIn_gt hq
  have hbp : p ∈ {x : M | b < f x} := connectedComponentIn_nonempty_iff.mp ⟨q, hqb⟩
  have hcompact' : IsCompact (f ⁻¹' Icc b (f p)) :=
    hcompact.of_isClosed_subset (isClosed_Icc.preimage hf.continuous)
      (fun _ hx => ⟨hab.le.trans hx.1, hx.2⟩)
  exact isMaxOn_connectedComponentIn_superlevel_of_no_critical_values hf hnd hmax hbp hcompact'
    (fun x hx => hregular x ⟨hab.trans_le hx.1, hx.2⟩)
    (connectedComponentIn_mono p (show {x : M | b < f x} ⊆ {x : M | b ≤ f x} from
      fun z hz => (show b < f z from hz).le) hqb)

theorem isMinOn_connectedComponentIn_lt_of_no_critical_values
    {E H M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] [TopologicalSpace M] [ChartedSpace H M]
    {I : ModelWithCorners ℝ E H} [I.Boundaryless] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M]
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) {p : M}
    (hnd : IsNondegenerateCriticalPointAt I f p) (hmin : IsLocalMin f p)
    {a : ℝ} (hcompact : IsCompact (f ⁻¹' Icc (f p) a))
    (hregular : ∀ x, f x ∈ Ioo (f p) a → ¬ IsCriticalPointAt I f x) :
    IsMinOn f (connectedComponentIn {x | f x < a} p) p := by
  have hnd' : IsNondegenerateCriticalPointAt I (fun x => -f x) p := by
    simpa only [zero_sub] using
      (DifferentialGeometry.Morse.isNondegenerateCriticalPointAt_const_sub_iff hf
        BoundarylessManifold.isInteriorPoint 0).mpr hnd
  have hcompact' : IsCompact ((fun x => -f x) ⁻¹' Icc (-a) (-f p)) := by
    convert hcompact using 1
    ext x
    change (-a ≤ -f x ∧ -f x ≤ -f p) ↔ (f p ≤ f x ∧ f x ≤ a)
    constructor <;> intro hx <;> constructor <;> linarith [hx.1, hx.2]
  have hregular' (x : M) (hx : -f x ∈ Ioo (-a) (-f p)) :
      ¬ IsCriticalPointAt I (fun x => -f x) x := by
    intro hc
    have hc' : IsCriticalPointAt I f x :=
      (DifferentialGeometry.Morse.isCriticalPointAt_const_sub_iff
        (hf.mdifferentiableAt (by simp)) 0).mp (by simpa only [zero_sub] using hc)
    exact hregular x ⟨by linarith [hx.2], by linarith [hx.1]⟩ hc'
  have hmax := isMaxOn_connectedComponentIn_gt_of_no_critical_values
    hf.neg hnd' hmin.neg hcompact' hregular'
  have hset : {x | -a < -f x} = {x | f x < a} := by
    ext x
    change -a < -f x ↔ f x < a
    exact neg_lt_neg_iff
  rw [hset] at hmax
  intro x hx
  exact neg_le_neg_iff.mp (show -f x ≤ -f p from hmax hx)

end DifferentialGeometry.Topology.Morse
