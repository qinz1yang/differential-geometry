import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.ExtendedSolutionRegularity
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.SmoothStrongPair
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature

/-!
# Interior Ricci--DeTurck uniqueness from chart-Gram regularity

This file is the geometric consumer of the reverse strong-solution bridge.  It
starts from the chart-Gram regularity carried by smooth Ricci-flow solution
packages, constructs `MetricFamilySmoothOn`, translates one regular interior
time to zero, and invokes the automatic local Ricci--DeTurck uniqueness
theorem.
-/

noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Analysis.Spectral DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M]

private theorem continuousOn_prod_slice
    {α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]
    {s : Set α} {t : Set β} {f : α × β → γ}
    (hf : ContinuousOn f (s ×ˢ t)) {x : β} (hx : x ∈ t) :
    ContinuousOn (fun y => f (y, x)) s :=
  hf.comp (continuous_id.prodMk continuous_const).continuousOn
    (fun _y hy => ⟨hy, hx⟩)

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] in
/-- Two smooth Riemannian metrics are equal if their Gram matrices agree in
the chart basis centred at every base point. -/
theorem metric_eq_chartGram
    (g h : SmoothRiemannianMetric I M)
    (hgram : ∀ (x : M) (i j : Fin (Module.finrank Real E)),
      chartGramMatrix (I := I) g x x i j =
        chartGramMatrix (I := I) h x x i j) :
    g = h := by
  have hinner : g.inner = h.inner := by
    funext x
    have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
      FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x
    let basis := chartBasisFamily (I := I) x hx
    have hb (i j : Fin (Module.finrank Real E)) :
        g.inner x (basis i) (basis j) = h.inner x (basis i) (basis j) := by
      simpa only [basis, chartBasisFamily_apply, chartGramMatrix_apply] using
        hgram x i j
    have hcoe : (g.inner x).toLinearMap = (h.inner x).toLinearMap := by
      apply Module.Basis.ext basis
      intro i
      have hrow : ((g.inner x) (basis i)).toLinearMap =
          ((h.inner x) (basis i)).toLinearMap := by
        apply Module.Basis.ext basis
        intro j
        exact hb i j
      ext z
      exact LinearMap.congr_fun hrow z
    ext v w
    have hv := LinearMap.congr_fun hcoe v
    exact congrArg (fun eta => eta w) hv
  cases g with
  | mk gi gsymm gpos gvon gcont =>
    cases h with
    | mk hi hsymm hpos hvon hcont =>
      cases hinner
      rfl

omit [NeZero (Module.finrank ℝ E)] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] in
/-- Equality on a left half-window passes to its right endpoint from the
existing joint chart-Gram `C⁰` regularity.  This is the closedness input for
forward Ricci--DeTurck continuation. -/
theorem metric_eq_leftLim
    (g₁ g₂ : Real → SmoothRiemannianMetric I M) {a b c d : Real}
    (hd : d ∈ Ioo a b) (hcd : c < d)
    (hcont₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContinuousOn
        (fun p : Real × M =>
          chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hcont₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContinuousOn
        (fun p : Real × M =>
          chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (heq : ∀ t ∈ Ico c d, g₁ t = g₂ t) :
    g₁ d = g₂ d := by
  apply metric_eq_chartGram
  intro x i j
  let f₁ : Real → Real := fun t =>
    chartGramMatrix (I := I) (g₁ t) x x i j
  let f₂ : Real → Real := fun t =>
    chartGramMatrix (I := I) (g₂ t) x x i j
  have hx : x ∈ (trivializationAt E (TangentSpace I) x).baseSet :=
    FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x
  have hf₁ : ContinuousOn f₁ (Ico a b) := by
    change ContinuousOn
      (fun t : Real => chartGramMatrix (I := I) (g₁ t) x x i j) (Ico a b)
    exact continuousOn_prod_slice (hcont₁ x i j) hx
  have hf₂ : ContinuousOn f₂ (Ico a b) := by
    change ContinuousOn
      (fun t : Real => chartGramMatrix (I := I) (g₂ t) x x i j) (Ico a b)
    exact continuousOn_prod_slice (hcont₂ x i j) hx
  have hdmem : d ∈ Ico a b := ⟨hd.1.le, hd.2⟩
  have hdnhds : Ico a b ∈ 𝓝 d := Ico_mem_nhds hd.1 hd.2
  have hf₁d : ContinuousAt f₁ d := (hf₁ d hdmem).continuousAt hdnhds
  have hf₂d : ContinuousAt f₂ d := (hf₂ d hdmem).continuousAt hdnhds
  have hclos : d ∈ closure (Ico c d) := by
    rw [closure_Ico (ne_of_lt hcd)]
    exact ⟨hcd.le, le_rfl⟩
  have hcluster : (𝓝[Ico c d] d).NeBot := by
    rw [mem_closure_iff_clusterPt] at hclos
    exact hclos
  have hlim₁ : Tendsto f₁ (𝓝[Ico c d] d) (𝓝 (f₁ d)) :=
    hf₁d.tendsto.mono_left inf_le_left
  have hlim₂ : Tendsto f₂ (𝓝[Ico c d] d) (𝓝 (f₂ d)) :=
    hf₂d.tendsto.mono_left inf_le_left
  have heqGram : EqOn f₁ f₂ (Ico c d) := by
    intro t ht
    simp only [f₁, f₂]
    rw [heq t ht]
  have hlim₁' : Tendsto f₁ (𝓝[Ico c d] d) (𝓝 (f₂ d)) :=
    hlim₂.congr' (heqGram.eventuallyEq_of_mem self_mem_nhdsWithin).symm
  exact tendsto_nhds_unique hlim₁ hlim₁'

/-- Two smooth Ricci--DeTurck metric paths with chart-Gram regularity which
agree at one interior time agree on a positive common forward window.  The
window length and all maximal-regularity budgets are chosen internally.

This is an interior continuation theorem.  It neither constructs a harmonic
map heat-flow gauge nor starts from a merely continuous original endpoint. -/
theorem chartRD_local
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) {a b c : ℝ} (hab : a < b)
    (hc : c ∈ Ioo a b) (g_bg : SmoothRiemannianMetric I M)
    (hsmooth₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hcont₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hsmooth₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ) ∞
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hcont₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn
        (fun p : ℝ × M =>
          chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hagree : g₁ c = g₂ c)
    (hPDE₁ : ∀ t ∈ Ioo a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivAt (fun tau => (g₁ tau).inner x v w)
        (deTurckRicciRHS (I := I) g_bg (g₁ t) x v w) t)
    (hPDE₂ : ∀ t ∈ Ioo a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivAt (fun tau => (g₂ tau).inner x v w)
        (deTurckRicciRHS (I := I) g_bg (g₂ t) x v w) t) :
    ∃ T : ℝ, 0 < T ∧
      ∀ t ∈ Icc (0 : ℝ) T, g₁ (c + t) = g₂ (c + t) := by
  let D : RealTimeInterval := RealTimeInterval.closedOpen a b hab
  let Sol₁ : SolutionOn (I := I) (M := M) D := { base := { metric := g₁ } }
  let Sol₂ : SolutionOn (I := I) (M := M) D := { base := { metric := g₂ } }
  let G₁ : RealizedMetricFamilyOn (I := I) (M := M) D := Sol₁.family
  let G₂ : RealizedMetricFamilyOn (I := I) (M := M) D := Sol₂.family
  have hG₁ : MetricFamilySmoothOn (I := I) (M := M) D G₁ := by
    simpa only [D, G₁, Sol₁] using
      metricFamilySmoothOn_of_chartGram (I := I) (M := M)
        g₁ hab hsmooth₁ hcont₁
  have hG₂ : MetricFamilySmoothOn (I := I) (M := M) D G₂ := by
    simpa only [D, G₂, Sol₂] using
      metricFamilySmoothOn_of_chartGram (I := I) (M := M)
        g₂ hab hsmooth₂ hcont₂
  let S : Set ℝ := (fun t : ℝ => c + t) ⁻¹' Ioo a b
  have hS : IsOpen S := by
    exact isOpen_Ioo.preimage (continuous_const.add continuous_id)
  have h0S : (0 : ℝ) ∈ S := by
    simpa only [S, Set.mem_preimage, add_zero] using hc
  have hmap : ∀ t ∈ S, c + t ∈ D.regular := by
    intro t ht
    exact ht
  have hshift₁ : ∀ t ∈ S, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivAt (fun tau => (G₁.metric (c + tau)).inner x v w)
        (deTurckRicciRHS (I := I) g_bg (G₁.metric (c + t)) x v w) t := by
    intro t ht x v w
    have hpde := hPDE₁ (t + c) (by simpa only [add_comm] using ht) x v w
    simpa only [G₁, Sol₁, SolutionOn.family, SolutionFamily.connection,
      add_comm] using hpde.comp_add_const t c
  have hshift₂ : ∀ t ∈ S, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivAt (fun tau => (G₂.metric (c + tau)).inner x v w)
        (deTurckRicciRHS (I := I) g_bg (G₂.metric (c + t)) x v w) t := by
    intro t ht x v w
    have hpde := hPDE₂ (t + c) (by simpa only [add_comm] using ht) x v w
    simpa only [G₂, Sol₂, SolutionOn.family, SolutionFamily.connection,
      add_comm] using hpde.comp_add_const t c
  obtain ⟨T, hT, huniq⟩ := metricRD_local (I := I) (M := M)
    G₁ G₂ hG₁ hG₂ (g₁ c) g_bg c hS h0S hmap rfl (by
      simpa only [G₂, Sol₂, SolutionOn.family] using hagree.symm) hshift₁ hshift₂
  refine ⟨T, hT, ?_⟩
  intro t ht
  simpa only [G₁, G₂, Sol₁, Sol₂, SolutionOn.family] using huniq t ht

/-- Two smooth Ricci--DeTurck paths which agree at one interior time agree on
the whole common forward interior interval.  The proof uses a supremum of
already-reached times.  Closedness at the supremum is supplied by
`metric_eq_leftLim`; no uniform lower bound on the successive local lifetimes
is assumed. -/
theorem chartRD_forward
    (g₁ g₂ : Real → SmoothRiemannianMetric I M) {a b c : Real} (hab : a < b)
    (hc : c ∈ Ioo a b) (g_bg : SmoothRiemannianMetric I M)
    (hsmooth₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M =>
          chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hcont₁ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContinuousOn
        (fun p : Real × M =>
          chartGramMatrix (I := I) (g₁ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hsmooth₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContMDiffOn (𝓘(Real, Real).prod I) 𝓘(Real) ∞
        (fun p : Real × M =>
          chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Ioo a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hcont₂ : ∀ (x₀ : M) (i j : Fin (Module.finrank Real E)),
      ContinuousOn
        (fun p : Real × M =>
          chartGramMatrix (I := I) (g₂ p.1) x₀ p.2 i j)
        (Ico a b ×ˢ (trivializationAt E (TangentSpace I) x₀).baseSet))
    (hagree : g₁ c = g₂ c)
    (hPDE₁ : ∀ t ∈ Ioo a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivAt (fun tau => (g₁ tau).inner x v w)
        (deTurckRicciRHS (I := I) g_bg (g₁ t) x v w) t)
    (hPDE₂ : ∀ t ∈ Ioo a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivAt (fun tau => (g₂ tau).inner x v w)
        (deTurckRicciRHS (I := I) g_bg (g₂ t) x v w) t) :
    ∀ t ∈ Ico c b, g₁ t = g₂ t := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with htc | hct
  · simpa [htc] using hagree
  set S : Set Real :=
    {s | s ∈ Icc c t ∧ ∀ r ∈ Icc c s, g₁ r = g₂ r} with hS
  have hcS : c ∈ S := ⟨⟨le_rfl, hct.le⟩, by
    intro r hr
    have hrc : r = c := le_antisymm hr.2 hr.1
    simpa [hrc] using hagree⟩
  have hSbdd : BddAbove S := ⟨t, fun s hs => hs.1.2⟩
  have hSne : S.Nonempty := ⟨c, hcS⟩
  set d : Real := sSup S with hd
  have hdIcc : d ∈ Icc c t :=
    ⟨le_csSup hSbdd hcS, csSup_le hSne (fun s hs => hs.1.2)⟩
  have heqBelow : ∀ r ∈ Ico c d, g₁ r = g₂ r := by
    intro r hr
    obtain ⟨s, hsS, hrs⟩ : ∃ s ∈ S, r ≤ s := by
      by_contra hcon
      simp only [not_exists, not_and, not_le] at hcon
      have hdr : d ≤ r := csSup_le hSne (fun s hs => le_of_lt (hcon s hs))
      exact absurd hr.2 (not_lt.mpr hdr)
    exact hsS.2 r ⟨hr.1, hrs⟩
  have hdeq : g₁ d = g₂ d := by
    rcases eq_or_lt_of_le hdIcc.1 with hdc | hcd
    · rw [← hdc]
      exact hagree
    · apply metric_eq_leftLim (I := I) (M := M) g₁ g₂
        (⟨lt_trans hc.1 hcd, lt_of_le_of_lt hdIcc.2 ht.2⟩ : d ∈ Ioo a b)
        hcd hcont₁ hcont₂ heqBelow
  have hdS : d ∈ S := by
    refine ⟨hdIcc, ?_⟩
    intro r hr
    rcases eq_or_lt_of_le hr.2 with hrd | hrd
    · simpa [hrd] using hdeq
    · exact heqBelow r ⟨hr.1, hrd⟩
  rcases eq_or_lt_of_le hdIcc.2 with hdt | hdt
  · rw [hdt] at hdS
    exact hdS.2 t ⟨ht.1, le_rfl⟩
  · exfalso
    have hdreg : d ∈ Ioo a b :=
      ⟨lt_of_lt_of_le hc.1 hdIcc.1, lt_of_le_of_lt hdIcc.2 ht.2⟩
    obtain ⟨T, hT, hlocal⟩ := chartRD_local (I := I) (M := M)
      g₁ g₂ hab hdreg g_bg hsmooth₁ hcont₁ hsmooth₂ hcont₂ hdeq
      hPDE₁ hPDE₂
    let delta : Real := min T (t - d) / 2
    have hmindelta : 0 < min T (t - d) := lt_min hT (sub_pos.mpr hdt)
    have hdelta : 0 < delta := by simp only [delta]; positivity
    have hdeltaT : delta ≤ T := by
      have hle := min_le_left T (t - d)
      dsimp [delta]
      nlinarith
    have hdeltat : d + delta ≤ t := by
      have hle := min_le_right T (t - d)
      dsimp [delta]
      nlinarith
    have hdDeltaS : d + delta ∈ S := by
      refine ⟨⟨le_trans hdIcc.1 (by linarith), hdeltat⟩, ?_⟩
      intro r hr
      rcases le_or_gt r d with hrd | hrd
      · exact hdS.2 r ⟨hr.1, hrd⟩
      · have hrs : r - d ∈ Icc (0 : Real) T := by
          refine ⟨sub_nonneg.mpr hrd.le, ?_⟩
          have hrdelta : r - d ≤ delta := by linarith [hr.2]
          exact le_trans hrdelta hdeltaT
        have heq := hlocal (r - d) hrs
        simpa [add_sub_cancel_left] using heq
    have hle : d + delta ≤ d := le_csSup hSbdd hdDeltaS
    linarith

end DifferentialGeometry.PDE.RicciFlow

end
