import DifferentialGeometry.Geometry.Metric.Distance.CompactMinimizer
import DifferentialGeometry.Geometry.Metric.Comparison.Finiteness
import DifferentialGeometry.Topology.FirstExit
import Mathlib.Topology.MetricSpace.HausdorffDistance

noncomputable section
open Set Filter Bundle Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]

omit [T2Space M] [SigmaCompactSpace M] in
private theorem exists_first_level
    (f : M → ℝ) (hf : Continuous f) {A : ℝ} {p z : M}
    (hp : f p < A) (hz : A ≤ f z)
    {γ : ℝ → M} (hγ : ContinuousOn γ (Icc 0 1)) (hγ0 : γ 0 = p) (hγ1 : γ 1 = z) :
    ∃ t ∈ Ioc (0 : ℝ) 1, f (γ t) = A ∧ ∀ s ∈ Icc 0 t, f (γ s) ≤ A := by
  let U : Set M := {x | f x < A}
  have hU : IsOpen U := isOpen_lt hf continuous_const
  have hpU : γ 0 ∈ interior U := by rw [hU.interior_eq, hγ0]; exact hp
  have hzU : γ 1 ∉ interior U := by rw [hU.interior_eq, hγ1]; exact not_lt_of_ge hz
  obtain ⟨t, ht, hbefore, hfront⟩ :=
    exists_first_exit_frontier_of_not_mem_interior zero_lt_one hγ hpU hzU
  have heq : f (γ t) = A := frontier_lt_subset_eq hf continuous_const hfront
  refine ⟨t, ht, heq, ?_⟩
  intro s hs
  rcases lt_or_eq_of_le hs.2 with hst | rfl
  · exact (hbefore s ⟨hs.1, hst⟩ |> interior_subset).le
  · exact heq.le

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [I.Boundaryless]
  [T2Space (TangentBundle I M)] [T2Space M] [SigmaCompactSpace M] in
private theorem nearest_level_edist_le
    (g g' : SmoothRiemannianMetric I M) (f : M → ℝ) (hf : Continuous f)
    {A : ℝ} {p q z : M} (hp : f p < A) (hz : A ≤ f z)
    (heq : ∀ x, f x ≤ A → g'.inner x = g.inner x)
    (hnearest : ∀ y, f y = A → riemannianEDistOf g' p q ≤ riemannianEDistOf g' p y) :
    riemannianEDistOf g' p q ≤ riemannianEDistOf g p z := by
  by_contra hnot
  obtain ⟨γ, hγ0, hγ1, hγ, hlength⟩ := exists_lt_of_edistOf_lt g (lt_of_not_ge hnot)
  obtain ⟨t, ht, hlevel, hprefix⟩ := exists_first_level f hf hp hz hγ.continuousOn hγ0 hγ1
  have hlen : metricPathELength g' γ 0 t = metricPathELength g γ 0 t :=
    metricPathELength_congr g g' (fun s hs => heq _ (hprefix s ⟨hs.1.le, hs.2.le⟩))
  have hdist := edistOf_le_metricPathELength g' ht.1.le
    (hγ.mono (Icc_subset_Icc le_rfl ht.2))
  rw [hγ0, hlen] at hdist
  have hbound := (hnearest (γ t) hlevel).trans
    (hdist.trans (metricPathELength_mono g γ le_rfl ht.2))
  exact (not_lt_of_ge hbound) hlength

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] [T2Space (TangentBundle I M)] in
private theorem exists_closest_level_in_complete_extension
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (hf : Continuous f)
    {A : ℝ} (hK : IsCompact {x | f x ≤ A}) (p z : M)
    (hp : f p < A) (hz : A ≤ f z) (hfinite : riemannianEDistOf g p z ≠ ⊤) :
    ∃ (g' : SmoothRiemannianMetric I M) (U : Set M) (q : M),
      RiemannianMetricComplete g' ∧ IsOpen U ∧ {x | f x ≤ A} ⊆ U ∧
      (∀ x ∈ U, g'.inner x = g.inner x) ∧
      (∀ x (v : TangentSpace I x), g.inner x v v ≤ g'.inner x v v) ∧
      f q = A ∧ riemannianEDistOf g' p q ≠ ⊤ ∧
      riemannianEDistOf g p q = riemannianEDistOf g' p q ∧
      riemannianEDistOf g p q ≤ riemannianEDistOf g p z ∧
      ∀ y, f y = A → riemannianEDistOf g' p q ≤ riemannianEDistOf g' p y := by
  obtain ⟨g', U, hcomplete, hU, hKU, heq, hmono⟩ :=
    exists_riemannianMetricComplete_eqOn_of_isCompact g hK
  have hpath : ∃ γ : ℝ → M, γ 0 = p ∧ γ 1 = z ∧ ContinuousOn γ (Icc 0 1) := by
    obtain ⟨γ, h0, h1, hγ, _⟩ := exists_lt_of_edistOf_lt g (lt_top_iff_ne_top.mpr hfinite)
    exact ⟨γ, h0, h1, hγ.continuousOn⟩
  obtain ⟨γ, h0, h1, hγ⟩ := hpath
  obtain ⟨t, ht, hlevel, _⟩ := exists_first_level f hf hp hz hγ h0 h1
  let level : Set M := {x | f x = A}
  have hlevelK : IsCompact level := hK.of_isClosed_subset
    (isClosed_eq hf continuous_const) (fun _ hx => hx.le)
  have hne : level.Nonempty := ⟨γ t, hlevel⟩
  have hcont : Continuous (fun y => riemannianEDistOf g' p y) := by
    unfold riemannianEDistOf
    exact Riemannian.continuous_riemannianEDist g' p
  obtain ⟨q, hq, hmin⟩ := hlevelK.exists_isMinOn hne hcont.continuousOn
  have hnearest : ∀ y, f y = A → riemannianEDistOf g' p q ≤ riemannianEDistOf g' p y := hmin
  have hnearOriginal : ∀ y, A ≤ f y → riemannianEDistOf g' p q ≤ riemannianEDistOf g p y :=
    fun y hy => nearest_level_edist_le g g' f hf hp hy
      (fun x hx => heq x (hKU hx)) hnearest
  have heqdist : riemannianEDistOf g p q = riemannianEDistOf g' p q :=
    le_antisymm (edistOf_mono g g' hmono p q) (hnearOriginal q hq.ge)
  have hfinq : riemannianEDistOf g' p q ≠ ⊤ := ne_top_of_le_ne_top hfinite (hnearOriginal z hz)
  exact ⟨g', U, q, hcomplete, hU, hKU, heq, hmono, hq, hfinq, heqdist,
    heqdist ▸ hnearOriginal z hz, hnearest⟩


attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_minimizing_segment_to_level_of_isCompact_sublevel
    (g : SmoothRiemannianMetric I M) (f : M → ℝ) (hf : Continuous f)
    {A : ℝ} (hK : IsCompact {x | f x ≤ A}) (p z : M)
    (hp : f p < A) (hz : A ≤ f z) (hfinite : riemannianEDistOf g p z ≠ ⊤) :
    ∃ (q : M) (gamma : ℝ → M),
      f q = A ∧ riemannianEDistOf g p q ≠ ⊤ ∧
      riemannianEDistOf g p q ≤ riemannianEDistOf g p z ∧
      gamma 0 = p ∧ gamma (riemannianEDistOf g p q).toReal = q ∧
      ContMDiffOn 𝓘(ℝ, ℝ) I ∞ gamma (Icc 0 (riemannianEDistOf g p q).toReal) ∧
      (∀ t ∈ Ico 0 (riemannianEDistOf g p q).toReal, f (gamma t) < A) ∧
      (∀ t ∈ Icc 0 (riemannianEDistOf g p q).toReal, f (gamma t) ≤ A) ∧
      ∀ s ∈ Icc 0 (riemannianEDistOf g p q).toReal,
        ∀ t ∈ Icc 0 (riemannianEDistOf g p q).toReal,
          riemannianEDistOf g (gamma s) (gamma t) = ENNReal.ofReal |s - t| := by
  obtain ⟨g', U, q, hcomplete, hU, hKU, heq, hmono, hq, hfinq, heqdist, hqz, hnearest⟩ :=
    exists_closest_level_in_complete_extension g f hf hK p z hp hz hfinite
  let L := (riemannianEDistOf g' p q).toReal
  have hnonzero : riemannianEDistOf g' p q ≠ 0 := by
    intro hzero
    let _ : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional (M := M) I
    let _ : RegularSpace M := inferInstance
    let _ : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g'.toRiemannianMetric⟩
    let _ : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
      ⟨g'.inner, g'.contMDiff.continuous, fun _ _ _ => rfl⟩
    have hpq : p = q := Riemannian.Exponential.riemannianEDist_eq_zero_imp_eq (I := I) p q hzero
    exact hp.ne (hpq ▸ hq)
  have hL : 0 < L := ENNReal.toReal_pos hnonzero hfinq
  have hr : riemannianEDistOf g' p q < ENNReal.ofReal (L + 1) :=
    (ENNReal.lt_ofReal_iff_toReal_lt hfinq).mpr (lt_add_one _)
  obtain ⟨gamma, h0, h1, hsmooth, hmin⟩ :=
    Riemannian.exists_distance_parametrized_minimizer_of_isCompact_riemannianClosedBall g' p q hr
      (hcomplete.closedEBall_isCompact p (L + 1))
  have hbelow : ∀ t ∈ Ico 0 L, f (gamma t) < A := by
    intro t ht
    by_contra hhigh
    have hft : A ≤ f (gamma t) := le_of_not_gt hhigh
    have hc : ContinuousOn (f ∘ gamma) (Icc 0 t) :=
      hf.comp_continuousOn (hsmooth.continuousOn.mono (Icc_subset_Icc le_rfl ht.2.le))
    obtain ⟨u, hu, hfu⟩ := intermediate_value_Icc ht.1 hc (by
      simp only [Function.comp_apply, h0]
      exact ⟨hp.le, hft⟩)
    have hnear := hnearest (gamma u) hfu
    rw [← h0, hmin 0 ⟨le_rfl, hL.le⟩ u ⟨hu.1, hu.2.trans ht.2.le⟩,
      zero_sub, abs_neg, abs_of_nonneg hu.1, h0] at hnear
    have hreal : L ≤ u := ENNReal.toReal_le_of_le_ofReal hu.1 hnear
    exact (not_lt_of_ge hreal) (hu.2.trans_lt ht.2)
  have hmem : ∀ t ∈ Icc 0 L, f (gamma t) ≤ A := by
    intro t ht
    rcases lt_or_eq_of_le ht.2 with htL | rfl
    · exact (hbelow t ⟨ht.1, htL⟩).le
    · simpa only [L, h1] using hq.le
  have hlength (s t : ℝ) (hs : s ∈ Icc 0 L) (ht : t ∈ Icc 0 L) (hst : s ≤ t) :
      riemannianEDistOf g (gamma s) (gamma t) ≤ ENNReal.ofReal (t - s) := by
    have hle := edistOf_mono g g' hmono (gamma s) (gamma t)
    rw [hmin s hs t ht, abs_of_nonpos (sub_nonpos.mpr hst), neg_sub] at hle
    exact hle
  have hordered (s t : ℝ) (hs : s ∈ Icc 0 L) (ht : t ∈ Icc 0 L) (hst : s ≤ t) :
      riemannianEDistOf g (gamma s) (gamma t) = ENNReal.ofReal (t - s) := by
    have hstfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hlength s t hs ht hst)
    have h0s := hlength 0 s ⟨le_rfl, hL.le⟩ hs hs.1
    have htL := hlength t L ht ⟨hL.le, le_rfl⟩ ht.2
    have htri := (riemannianEDistOf_triangle g (gamma 0) (gamma s) (gamma L)).trans
      (add_le_add le_rfl (riemannianEDistOf_triangle g (gamma s) (gamma t) (gamma L)))
    have hbound := htri.trans (add_le_add h0s (add_le_add le_rfl htL))
    rw [h0, h1, heqdist, sub_zero] at hbound
    have hre := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top,
      ENNReal.add_ne_top.mpr ⟨hstfin, ENNReal.ofReal_ne_top⟩⟩) hbound
    rw [ENNReal.toReal_add ENNReal.ofReal_ne_top
        (ENNReal.add_ne_top.mpr ⟨hstfin, ENNReal.ofReal_ne_top⟩),
      ENNReal.toReal_add hstfin ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal hs.1, ENNReal.toReal_ofReal (sub_nonneg.mpr ht.2)] at hre
    have hu := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hlength s t hs ht hst)
    rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hst)] at hu
    have heqd : (riemannianEDistOf g (gamma s) (gamma t)).toReal = t - s := by
      change L ≤ s + ((riemannianEDistOf g (gamma s) (gamma t)).toReal + (L - t)) at hre
      linarith
    exact (ENNReal.ofReal_toReal hstfin).symm.trans (congrArg ENNReal.ofReal heqd)
  refine ⟨q, gamma, hq, heqdist ▸ hfinq, hqz, h0, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [heqdist] using h1
  · simpa only [heqdist] using hsmooth
  · simpa only [heqdist] using hbelow
  · simpa only [heqdist] using hmem
  · intro s hs t ht
    rw [heqdist] at hs ht
    rcases le_total s t with hst | hts
    · rw [hordered s t hs ht hst, abs_of_nonpos (sub_nonpos.mpr hst), neg_sub]
    · rw [riemannianEDistOf_comm g (gamma s) (gamma t), hordered t s ht hs hts,
        abs_of_nonneg (sub_nonneg.mpr hts)]

end DifferentialGeometry.Geometry
