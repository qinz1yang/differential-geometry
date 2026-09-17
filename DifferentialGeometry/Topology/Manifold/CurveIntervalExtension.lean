import DifferentialGeometry.Analysis.Calculus.Smoothness.ExtendInterval
import DifferentialGeometry.Topology.Manifold.SmoothExtension
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import DifferentialGeometry.Analysis.Calculus.SmoothExtension.Curve
import Mathlib.Topology.Order.ProjIcc

section

open Set Filter Function
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {k : ℕ} [IsManifold I (k : ℕ) M]

theorem exists_contMDiffOn_local_extension_Icc
    {a b : ℝ} {gamma : ℝ → M}
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I (k : ℕ) gamma (Icc a b))
    {x : ℝ} (hx : x ∈ Icc a b) :
    ∃ U : ℝ → M, ∃ V : Set ℝ,
      IsOpen V ∧ x ∈ V ∧ ContMDiffOn 𝓘(ℝ, ℝ) I (k : ℕ) U V ∧
        EqOn U gamma (Icc a b ∩ V) := by
  let p : M := gamma x
  have hsrcNear : gamma ⁻¹' (chartAt H p).source ∈ 𝓝[Icc a b] x := by
    have hc := hgamma.continuousOn x hx
    exact hc ((chartAt H p).open_source.mem_nhds (by
      simpa only [p] using mem_chart_source H (gamma x)))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhdsWithin_iff.mp hsrcNear
  let c := max a (x - r / 2)
  let d := min b (x + r / 2)
  have hsub : Icc c d ⊆ Icc a b := by
    intro t ht
    exact ⟨(le_max_left _ _).trans ht.1, ht.2.trans (min_le_left _ _)⟩
  have hxsmall : x ∈ Icc c d := by
    constructor
    · exact max_le hx.1 (by linarith)
    · exact le_min hx.2 (by linarith)
  have hsrc : MapsTo gamma (Icc c d) (chartAt H p).source := by
    intro t ht
    apply hball
    refine ⟨?_, hsub ht⟩
    rw [Metric.mem_ball, Real.dist_eq, abs_lt]
    constructor
    · have hh := (le_max_right a (x - r / 2)).trans ht.1
      linarith
    · have hh := ht.2.trans (min_le_right b (x + r / 2))
      linarith
  have hchart : ContDiffOn ℝ (k : ℕ) ((extChartAt I p) ∘ gamma) (Icc c d) :=
    ((contMDiffOn_extChartAt (I := I) (n := (k : ℕ∞)) (x := p)).comp
      (hgamma.mono hsub) hsrc).contDiffOn
  obtain ⟨g, hg, hgeq⟩ := Analysis.exists_contDiff_extension_Icc k _ hchart
  let V := g ⁻¹' (extChartAt I p).target ∩ Ioo (x - r / 2) (x + r / 2)
  have hV : IsOpen V :=
    ((isOpen_extChartAt_target (I := I) p).preimage hg.continuous).inter isOpen_Ioo
  have hxV : x ∈ V := by
    refine ⟨?_, ⟨by linarith, by linarith⟩⟩
    rw [mem_preimage, hgeq hxsmall]
    exact (extChartAt I p).map_source (by
      rw [extChartAt_source]
      exact hsrc hxsmall)
  refine ⟨(extChartAt I p).symm ∘ g, V, hV, hxV,
    (contMDiffOn_extChartAt_symm (I := I) (n := (k : ℕ∞)) p).comp
      hg.contMDiff.contMDiffOn (fun _ ht => ht.1), ?_⟩
  intro t ht
  have htsmall : t ∈ Icc c d :=
    ⟨max_le ht.1.1 ht.2.2.1.le, le_min ht.1.2 ht.2.2.2.le⟩
  change (extChartAt I p).symm (g t) = gamma t
  rw [hgeq htsmall]
  exact (extChartAt I p).left_inv (by
    rw [extChartAt_source]
    exact hsrc htsmall)

end DifferentialGeometry.Topology

end
section

open Set Filter Function
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {k : ℕ} [IsManifold I (k : ℕ) M]

private theorem exists_contMDiff_extension_Icc_of_lt
    {a b : ℝ} (hab : a < b) {gamma : ℝ → M}
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I (k : ℕ) gamma (Icc a b)) :
    ∃ g : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I (k : ℕ) g ∧ EqOn g gamma (Icc a b) := by
  let gamma0 : ℝ → M := IccExtend hab.le (fun t : Icc a b => gamma t)
  have h0 : Continuous gamma0 :=
    (continuous_IccExtend_iff (h := hab.le)).mpr
      (continuousOn_iff_continuous_domRestrict.mp hgamma.continuousOn)
  have h0eq : EqOn gamma0 gamma (Icc a b) := by
    intro t ht
    exact IccExtend_of_mem hab.le _ ht
  obtain ⟨g, _, hgeq, N, hN, hsub, hgs⟩ :=
    exists_contMDiffOn_eqOn_of_locally_extendable (I := I) (n := (k : ℕ∞)) h0 isCompact_Icc (by
      intro t ht
      obtain ⟨U, V, hV, htV, hU, heq⟩ := exists_contMDiffOn_local_extension_Icc hgamma ht
      refine ⟨U, V, hV, htV, hU, ?_⟩
      intro s hs
      exact (heq hs).trans (h0eq hs.1).symm)
  obtain ⟨G, hG, hGeq⟩ := hgs.exists_extension_uIcc (a := a) (b := b) hN (by
    simpa only [uIcc_of_le hab.le] using hsub)
  refine ⟨G, hG, ?_⟩
  intro t ht
  exact ((hGeq t (by simpa only [uIcc_of_le hab.le] using ht)).self_of_nhds).trans
    ((hgeq ht).trans (h0eq ht))

theorem exists_contMDiff_extension_Icc
    {a b : ℝ} {gamma : ℝ → M}
    (hgamma : ContMDiffOn 𝓘(ℝ, ℝ) I (k : ℕ) gamma (Icc a b)) :
    ∃ g : ℝ → M, ContMDiff 𝓘(ℝ, ℝ) I (k : ℕ) g ∧ EqOn g gamma (Icc a b) := by
  rcases lt_trichotomy a b with hab | hab | hab
  · exact exists_contMDiff_extension_Icc_of_lt hab hgamma
  · subst b
    refine ⟨fun _ ↦ gamma a, contMDiff_const, ?_⟩
    intro t ht
    have ht' : t = a := le_antisymm ht.2 ht.1
    rw [ht']
  · refine ⟨fun _ ↦ gamma a, contMDiff_const, ?_⟩
    simp only [Icc_eq_empty_of_lt hab, eqOn_empty]

end DifferentialGeometry.Topology

end
