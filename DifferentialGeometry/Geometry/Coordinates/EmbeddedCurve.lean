import DifferentialGeometry.Geometry.Coordinates.OrthogonalCurve
import DifferentialGeometry.Geometry.Submanifold.SecondFundamentalForm.MetricCompatibility
import DifferentialGeometry.Topology.Manifold.ChartPartialDiffeomorph
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

noncomputable section
open Set Filter Bundle Manifold
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem contDiffOn_chartMetricBilin (g : SmoothRiemannianMetric I M) (a : M) :
    ContDiffOn ℝ ∞ (chartMetricBilin g a) (extChartAt I a).target := by
  apply contDiffOn_clm_apply.mpr
  intro v
  apply contDiffOn_clm_apply.mpr
  intro w
  have hEq (z : E) : chartMetricBilin g a z v w =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        Operator.chartGramOnE g a i j z * Riemannian.Geodesic.chartCoord (E := E) i v *
          Riemannian.Geodesic.chartCoord (E := E) j w := by
    exact Riemannian.AlongCurve.inner_eq_chartGramOnE_bilinear_on_baseSet g a v w
  have hs : ContDiffOn ℝ ∞ (fun z : E =>
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        Operator.chartGramOnE g a i j z * Riemannian.Geodesic.chartCoord (E := E) i v *
          Riemannian.Geodesic.chartCoord (E := E) j w) (extChartAt I a).target := by
    apply ContDiffOn.sum
    intro i _
    apply ContDiffOn.sum
    intro j _
    exact ((Operator.chartGramOnE_contDiffOn g a i j).mul contDiffOn_const).mul contDiffOn_const
  exact hs.congr (fun z _ => hEq z)

omit [FiniteDimensional ℝ E] in
private theorem chartMetricBilin_pos (g : SmoothRiemannianMetric I M) (a : M)
    {z : E} (hz : z ∈ (extChartAt I a).target) {v : E} (hv : v ≠ 0) :
    0 < chartMetricBilin g a z v v := by
  have hp : (extChartAt I a).symm z ∈ (trivializationAt E (TangentSpace I) a).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet, extChartAt_source] using
      (extChartAt I a).map_target hz
  apply g.pos
  intro hzero
  apply hv
  change Connection.trivFromE I a ((extChartAt I a).symm z) v = 0 at hzero
  calc
    v = Connection.trivToE I a ((extChartAt I a).symm z)
        (Connection.trivFromE I a ((extChartAt I a).symm z) v) :=
      (Connection.trivToE_trivFromE I a hp v).symm
    _ = 0 := by rw [hzero, map_zero]

omit [FiniteDimensional ℝ E] in
private theorem deriv_chartCurve_zero {c : ℝ → M}
    (hc : MDifferentiableAt 𝓘(ℝ, ℝ) I c 0) :
    deriv (fun s => extChartAt I (c 0) (c s)) 0 =
      mfderiv 𝓘(ℝ, ℝ) I c 0 1 := by
  rw [← fderiv_apply_one_eq_deriv, ← mfderiv_eq_fderiv]
  have hh := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := I) (I'' := 𝓘(ℝ, E)) 0
    (mdifferentiableAt_extChartAt (I := I) (mem_chart_source H (c 0))) hc
  change (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ((extChartAt I (c 0)) ∘ c) 0) 1 = _
  rw [hh, mfderiv_extChartAt_self]
  rfl

private theorem exists_restrict_curve_axis
    {V C N : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [TopologicalSpace C] [TopologicalSpace N]
    {γ : C → N} (hγ : Topology.IsEmbedding γ)
    (p : OpenPartialHomeomorph ℝ C) (hp0 : (0 : ℝ) ∈ p.source)
    (e : OpenPartialHomeomorph V N) (he0 : (0 : V) ∈ e.source)
    {l : V →L[ℝ] ℝ} {t : V} (hlt : l t = 1)
    (haxis : ∀ s, s • t ∈ e.source → e (s • t) = γ (p s)) :
    ∃ U : Set V, IsOpen U ∧ (0 : V) ∈ U ∧ U ⊆ e.source ∧
      ∀ x ∈ e.target, e.symm x ∈ U →
        (x ∈ range γ ↔ e.symm x = l (e.symm x) • t) := by
  let S : Set ℝ := p.source ∩ (fun s : ℝ => s • t) ⁻¹' e.source
  have hS : IsOpen S := p.open_source.inter
    (e.open_source.preimage (continuous_id.smul continuous_const))
  have h0S : (0 : ℝ) ∈ S := ⟨hp0, by simpa using he0⟩
  have hD : IsOpen (p '' S) := p.isOpen_image_of_subset_source hS inter_subset_left
  obtain ⟨W, hW, hpre⟩ := hγ.isInducing.isOpen_iff.mp hD
  have hc0 : e (0 : V) ∈ W := by
    have hpW : p 0 ∈ γ ⁻¹' W := by rw [hpre]; exact mem_image_of_mem p h0S
    have heq : e (0 : V) = γ (p 0) := by simpa using haxis 0 (by simpa using he0)
    rw [heq]
    exact hpW
  refine ⟨e.source ∩ e ⁻¹' W, e.isOpen_inter_preimage hW, ⟨he0, hc0⟩,
    inter_subset_left, ?_⟩
  intro x hx hxU
  constructor
  · rintro ⟨a, rfl⟩
    have hWa : a ∈ γ ⁻¹' W := by
      change γ a ∈ W
      rw [← e.right_inv hx]
      exact hxU.2
    rw [hpre] at hWa
    obtain ⟨s, hs, hsa⟩ := hWa
    have hEs : e (s • t) = γ a := (haxis s hs.2).trans (congrArg γ hsa)
    have hi : e.symm (γ a) = s • t := by rw [← hEs]; exact e.left_inv hs.2
    rw [hi]
    simp [map_smul, hlt]
  · intro hxt
    refine ⟨p (l (e.symm x)), ?_⟩
    rw [← haxis (l (e.symm x)) (by rw [← hxt]; exact e.map_target hx), ← hxt]
    exact e.right_inv hx

omit [FiniteDimensional ℝ E] in
private theorem chartMetricBilin_eq_pullback [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (a : M) {z : E}
    (hz : z ∈ (extChartAt I a).target) (v w : E) :
    chartMetricBilin g a z v w =
      g.inner ((extChartAt I a).symm z)
        (mfderiv 𝓘(ℝ, E) I (extChartAt I a).symm z v)
        (mfderiv 𝓘(ℝ, E) I (extChartAt I a).symm z w) := by
  have hp : (extChartAt I a).symm z ∈ (chartAt H a).source := by
    simpa only [extChartAt_source] using (extChartAt I a).map_target hz
  have hL : Connection.trivFromE I a ((extChartAt I a).symm z) =
      mfderiv 𝓘(ℝ, E) I (extChartAt I a).symm z := by
    rw [Connection.trivFromE, TangentBundle.symmL_trivializationAt hp,
      (extChartAt I a).right_inv hz, I.range_eq_univ, mfderivWithin_univ]
  change g.inner ((extChartAt I a).symm z)
    (Connection.trivFromE I a ((extChartAt I a).symm z) v)
    (Connection.trivFromE I a ((extChartAt I a).symm z) w) = _
  rw [hL]
  rfl

private theorem exists_orthogonal_local_curve_chart [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {c : ℝ → M} {J : Set ℝ}
    (hJ : IsOpen J) (h0 : (0 : ℝ) ∈ J)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ c J)
    (hv : mfderiv 𝓘(ℝ, ℝ) I c 0 1 ≠ 0) :
    ∃ (t : E) (l : E →L[ℝ] ℝ) (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞),
      l t = 1 ∧ 0 ∈ Φ.source ∧ Φ 0 = c 0 ∧ Φ.source ⊆ l ⁻¹' J ∧
      ∀ s, s • t ∈ Φ.source → Φ (s • t) = c s ∧
        0 < g.inner (Φ (s • t))
          (mfderiv 𝓘(ℝ, E) I Φ (s • t) t) (mfderiv 𝓘(ℝ, E) I Φ (s • t) t) ∧
        ∀ v : E, g.inner (Φ (s • t))
            (mfderiv 𝓘(ℝ, E) I Φ (s • t) t) (mfderiv 𝓘(ℝ, E) I Φ (s • t) v) =
          g.inner (Φ (s • t))
            (mfderiv 𝓘(ℝ, E) I Φ (s • t) t) (mfderiv 𝓘(ℝ, E) I Φ (s • t) t) * l v := by
  let a := c 0
  let α := extChartAtPartialDiffeomorph I ∞ a
  let J' : Set ℝ := J ∩ c ⁻¹' α.source
  have hJ' : IsOpen J' := hc.continuousOn.isOpen_inter_preimage hJ α.open_source
  have h0' : (0 : ℝ) ∈ J' := ⟨h0, mem_extChartAt_source a⟩
  let cc : ℝ → E := fun s => extChartAt I a (c s)
  have hcc : ContDiffOn ℝ ∞ cc J' := contMDiffOn_iff_contDiffOn.mp
    (α.contMDiffOn_toFun.comp (hc.mono inter_subset_left) inter_subset_right)
  have hccmap : MapsTo cc J' (extChartAt I a).target :=
    fun s hs => (extChartAt I a).map_source hs.2
  let B : ℝ → E →L[ℝ] E →L[ℝ] ℝ := fun s => chartMetricBilin g a (cc s)
  have hB : ContDiffOn ℝ ∞ B J' := (contDiffOn_chartMetricBilin g a).comp hcc hccmap
  have hdc : deriv cc 0 ≠ 0 := by
    rw [deriv_chartCurve_zero ((hc.contMDiffAt (hJ.mem_nhds h0)).mdifferentiableAt (by simp))]
    exact hv
  have hq0 : B 0 (deriv cc 0) (deriv cc 0) ≠ 0 :=
    (chartMetricBilin_pos g a (hccmap h0') hdc).ne'
  let t := deriv cc 0
  let l : E →L[ℝ] ℝ := (B 0 t t)⁻¹ • B 0 t
  have hlt : l t = 1 := by simp only [l, smul_apply, smul_eq_mul]; exact inv_mul_cancel₀ hq0
  obtain ⟨e, he0, heJ, he, hei, _, haxis⟩ :=
    exists_orthogonal_curve_coordinates hJ' h0' hcc hB hq0
  let R : PartialDiffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) E E ∞ :=
    { e.toPartialEquiv with
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := contMDiffOn_iff_contDiffOn.mpr he
      contMDiffOn_invFun := contMDiffOn_iff_contDiffOn.mpr hei }
  let Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞ := R.trans α.symm
  have hΦ0 : (0 : E) ∈ Φ.source := by
    refine ⟨he0, ?_⟩
    have hezero : e (0 : E) = cc 0 := by simpa using (haxis 0 (by simpa using he0)).1
    change e (0 : E) ∈ (extChartAt I a).target
    rw [hezero]
    exact hccmap h0'
  have hΦJ : Φ.source ⊆ l ⁻¹' J := fun z hz => (heJ hz.1).1
  have hsJ (s : ℝ) (hs : s • t ∈ Φ.source) : s ∈ J' := by
    have hh := heJ hs.1
    change l (s • t) ∈ J' at hh
    simpa only [map_smul, hlt, smul_eq_mul, mul_one] using hh
  have hΦaxis (s : ℝ) (hs : s • t ∈ Φ.source) : Φ (s • t) = c s := by
    change (extChartAt I a).symm (e (s • t)) = c s
    rw [(haxis s hs.1).1]
    exact (extChartAt I a).left_inv (hsJ s hs).2
  have hchain (z : E) (hz : z ∈ Φ.source) : mfderiv 𝓘(ℝ, E) I Φ z =
      (mfderiv 𝓘(ℝ, E) I (extChartAt I a).symm (e z)).comp (fderiv ℝ e z) := by
    have hh := mfderiv_comp (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ, E)) (I'' := I) z
      (α.symm.mdifferentiableAt (by simp) hz.2) (R.mdifferentiableAt (by simp) hz.1)
    rw [mfderiv_eq_fderiv] at hh
    exact hh
  have hmetric (z : E) (hz : z ∈ Φ.source) (v w : E) :
      g.inner (Φ z) (mfderiv 𝓘(ℝ, E) I Φ z v) (mfderiv 𝓘(ℝ, E) I Φ z w) =
        chartMetricBilin g a (e z) (fderiv ℝ e z v) (fderiv ℝ e z w) := by
    rw [hchain z hz]
    exact (chartMetricBilin_eq_pullback g a hz.2 (fderiv ℝ e z v) (fderiv ℝ e z w)).symm
  refine ⟨t, l, Φ, hlt, hΦ0, ?_, hΦJ, ?_⟩
  · simpa using hΦaxis 0 (by simpa using hΦ0)
  · intro s hs
    have hdiag : g.inner (Φ (s • t))
        (mfderiv 𝓘(ℝ, E) I Φ (s • t) t) (mfderiv 𝓘(ℝ, E) I Φ (s • t) t) =
        B s (deriv cc s) (deriv cc s) := by
      rw [hmetric (s • t) hs, (haxis s hs.1).1]
      have hh := (haxis s hs.1).2.2.2 t
      change B s (fderiv ℝ e (s • t) t) (fderiv ℝ e (s • t) t) =
        B s (deriv cc s) (deriv cc s) * l t at hh
      rw [hlt, mul_one] at hh
      exact hh
    have hT : deriv cc s ≠ 0 := by
      intro hzero
      apply (haxis s hs.1).2.2.1
      rw [hzero, map_zero]
    refine ⟨hΦaxis s hs, ?_, ?_⟩
    · rw [hdiag]
      exact chartMetricBilin_pos g a (hccmap (hsJ s hs)) hT
    · intro v
      rw [hdiag]
      erw [hmetric (s • t) hs t v]
      rw [(haxis s hs.1).1]
      exact (haxis s hs.1).2.2.2 v

theorem exists_orthogonal_chart_of_embedded_curve [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) {C : Type*} [TopologicalSpace C]
    {γ : C → M} (hγ : Topology.IsEmbedding γ)
    (p : OpenPartialHomeomorph ℝ C) (hp0 : (0 : ℝ) ∈ p.source)
    (hc : ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (γ ∘ p) p.source)
    (hv : mfderiv 𝓘(ℝ, ℝ) I (γ ∘ p) 0 1 ≠ 0) :
    ∃ (t : E) (l : E →L[ℝ] ℝ) (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞),
      l t = 1 ∧ 0 ∈ Φ.source ∧ Φ 0 = γ (p 0) ∧ Φ.source ⊆ l ⁻¹' p.source ∧
      (∀ s, s • t ∈ Φ.source → Φ (s • t) = γ (p s) ∧
        0 < g.inner (Φ (s • t))
          (mfderiv 𝓘(ℝ, E) I Φ (s • t) t) (mfderiv 𝓘(ℝ, E) I Φ (s • t) t) ∧
        ∀ v : E, g.inner (Φ (s • t))
            (mfderiv 𝓘(ℝ, E) I Φ (s • t) t) (mfderiv 𝓘(ℝ, E) I Φ (s • t) v) =
          g.inner (Φ (s • t))
            (mfderiv 𝓘(ℝ, E) I Φ (s • t) t) (mfderiv 𝓘(ℝ, E) I Φ (s • t) t) * l v) ∧
      ∀ x ∈ Φ.target, x ∈ range γ ↔ Φ.symm x - l (Φ.symm x) • t = 0 := by
  obtain ⟨t, l, Φ, hlt, hΦ0, hΦc, hΦJ, haxis⟩ :=
    exists_orthogonal_local_curve_chart g p.open_source hp0 hc hv
  obtain ⟨U, hU, hU0, hUs, hcurve⟩ := exists_restrict_curve_axis hγ p hp0
    Φ.toOpenPartialHomeomorph hΦ0 hlt (fun s hs => (haxis s hs).1)
  let ψ := Φ.toOpenPartialHomeomorph.restrOpen U hU
  let Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞ :=
    { ψ.toPartialEquiv with
      open_source := ψ.open_source
      open_target := ψ.open_target
      contMDiffOn_toFun := Φ.contMDiffOn_toFun.mono inter_subset_left
      contMDiffOn_invFun := Φ.contMDiffOn_invFun.mono inter_subset_left }
  refine ⟨t, l, Ψ, hlt, ⟨hΦ0, hU0⟩, hΦc, fun z hz => hΦJ hz.1,
    fun s hs => haxis s hs.1, ?_⟩
  intro x hx
  have hh := hcurve x hx.1 (Ψ.toOpenPartialHomeomorph.map_target hx).2
  exact hh.trans sub_eq_zero.symm

end DifferentialGeometry.Geometry
