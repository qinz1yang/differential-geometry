import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.RampContinuation

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace ProductCurve

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem continuousOn_map {J : Set ℝ} {c : ProductCurve M} (hc : c.SmoothOn (I := I) J)
    (z : Surgery.Topology.Circle) : ContinuousOn (fun t : ℝ => c.map z t) J := by
  obtain ⟨x, -, hx⟩ := AddCircle.eq_coe_Ico (p := (1 : ℝ)) z
  rw [← hx]
  have hmap : (fun t : ℝ => c.map (x : Surgery.Topology.Circle) t) =
      fun t : ℝ => (c.projection.lift x t, (c.y x t : Surgery.Topology.Circle)) := by
    funext t
    exact Prod.ext rfl (c.lift_eq x t).symm
  rw [hmap]
  refine ((CurveMap.time_slice_contMDiffOn c.projection J hc.1 x).continuousOn).prodMk ?_
  exact (AddCircle.continuous_mk' (1 : ℝ)).comp_continuousOn
    ((hc.2.comp (by fun_prop : ContDiffOn ℝ ∞ (fun t : ℝ => (x, t)) J)
      (fun t ht => ⟨mem_univ x, ht⟩)).continuousOn)

end ProductCurve

variable [SigmaCompactSpace M] [T2Space M] [CompactSpace M] [Nonempty M] [I.Boundaryless]
variable {D : RealTimeInterval} {a b : ℝ}

def RampShortTimeUniqueness
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ) : Prop :=
  ∀ (s T : ℝ), a ≤ s → s < T → T ≤ b →
    ∀ c₁ c₂ : ProductCurve M,
      c₁.IsSolutionOn B.family.metric lambda (Icc s T) →
      c₂.IsSolutionOn B.family.metric lambda (Icc s T) →
      (∀ z, c₁.map z s = c₂.map z s) →
      ∃ δ > 0, ∀ z t, t ∈ Icc s (min T (s + δ)) → c₁.map z t = c₂.map z t

omit [SigmaCompactSpace M] [CompactSpace M] [Nonempty M] [I.Boundaryless] in
theorem RampShortTimeUniqueness.of_localUniqueness
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ)
    (U : RampLocalUniqueness (I := I) (M := M) (D := D) (a := a) (b := b) B lambda) :
    RampShortTimeUniqueness (I := I) (M := M) (D := D) (a := a) (b := b) B lambda := by
  intro s T has hsT hTb c₁ c₂ hc₁ hc₂ h₀
  have hst : s + (T - s) = T := by ring
  exact ⟨T - s, by linarith,
    fun z t ht => U s T T has hsT hsT hTb hTb c₁ c₂ hc₁ hc₂ h₀ z t (by
      simpa only [hst, min_self] using ht)⟩

omit [SigmaCompactSpace M] [CompactSpace M] [Nonempty M] [I.Boundaryless] in
theorem RampLocalUniqueness.of_shortTime
    (B : RicciBackground (I := I) (M := M) D a b) (lambda : ℝ)
    (H : RampShortTimeUniqueness (I := I) (M := M) (D := D) (a := a) (b := b) B lambda) :
    RampLocalUniqueness (I := I) (M := M) (D := D) (a := a) (b := b) B lambda := by
  intro s t₁ t₂ has hs₁ hs₂ hb₁ hb₂ c₁ c₂ hc₁ hc₂ h₀
  set L : ℝ := min t₁ t₂ with hL
  have hsL : s < L := by rw [hL]; exact lt_min hs₁ hs₂
  have hLt₁ : L ≤ t₁ := by rw [hL]; exact min_le_left t₁ t₂
  have hLt₂ : L ≤ t₂ := by rw [hL]; exact min_le_right t₁ t₂
  have hLb : L ≤ b := hLt₁.trans hb₁
  set A : Set ℝ := {t | t ∈ Icc s L ∧ ∀ z u, u ∈ Icc s t → c₁.map z u = c₂.map z u} with hA
  have hsA : s ∈ A := by
    rw [hA]
    refine ⟨⟨le_rfl, hsL.le⟩, fun z u hu => ?_⟩
    rw [Icc_self] at hu
    rw [hu]
    exact h₀ z
  have hAbdd : BddAbove A := ⟨L, fun t ht => by rw [hA] at ht; exact ht.1.2⟩
  have hBclosed : IsClosed (⋂ z : Surgery.Topology.Circle,
      {t : ℝ | t ∈ Icc s L ∧ c₁.map z t = c₂.map z t}) := by
    refine isClosed_iInter (fun z => ?_)
    rw [hL]
    exact isClosed_Icc.isClosed_eq
      ((ProductCurve.continuousOn_map hc₁.smooth z).mono
        (Icc_subset_Icc le_rfl (min_le_left t₁ t₂)))
      ((ProductCurve.continuousOn_map hc₂.smooth z).mono
        (Icc_subset_Icc le_rfl (min_le_right t₁ t₂)))
  have hAsub : A ⊆ ⋂ z : Surgery.Topology.Circle,
      {t : ℝ | t ∈ Icc s L ∧ c₁.map z t = c₂.map z t} := by
    intro t ht
    rw [hA] at ht
    exact Set.mem_iInter.mpr fun z => ⟨ht.1, ht.2 z t ⟨ht.1.1, le_rfl⟩⟩
  have hTmemB : sSup A ∈ ⋂ z : Surgery.Topology.Circle,
      {t : ℝ | t ∈ Icc s L ∧ c₁.map z t = c₂.map z t} := by
    have hcl : sSup A ∈ closure A := csSup_mem_closure ⟨s, hsA⟩ hAbdd
    rw [← hBclosed.closure_eq]
    exact closure_mono hAsub hcl
  have hTmem : sSup A ∈ Icc s L ∧
      ∀ z u, u ∈ Icc s (sSup A) → c₁.map z u = c₂.map z u := by
    rw [hA]
    refine ⟨(Set.mem_iInter.mp hTmemB (0 : Surgery.Topology.Circle)).1, fun z u hu => ?_⟩
    rcases lt_or_eq_of_le hu.2 with hlt | heq
    · obtain ⟨t, htA, hut⟩ := (lt_csSup_iff hAbdd ⟨s, hsA⟩).mp hlt
      rw [hA] at htA
      exact htA.2 z u ⟨hu.1, hut.le⟩
    · rw [heq]
      exact (Set.mem_iInter.mp hTmemB z).2
  have hsT : s ≤ sSup A := hTmem.1.1
  have hTle : sSup A ≤ L := hTmem.1.2
  have hTL : sSup A = L := by
    by_contra hne
    have hlt : sSup A < L := lt_of_le_of_ne hTle hne
    have hrestrict₁ : c₁.IsSolutionOn B.family.metric lambda (Icc (sSup A) L) :=
      hc₁.mono_Icc hsT hLt₁ hlt
    have hrestrict₂ : c₂.IsSolutionOn B.family.metric lambda (Icc (sSup A) L) :=
      hc₂.mono_Icc hsT hLt₂ hlt
    obtain ⟨δ, hδ, hagree⟩ :=
      H (sSup A) L (has.trans hsT) hlt hLb c₁ c₂ hrestrict₁ hrestrict₂
        (fun z => hTmem.2 z (sSup A) ⟨hsT, le_rfl⟩)
    have hnew : min L (sSup A + δ) ∈ A := by
      rw [hA]
      refine ⟨⟨le_min hsL.le (by linarith), min_le_left L (sSup A + δ)⟩, fun z u hu => ?_⟩
      rcases le_total u (sSup A) with hle | hle
      · exact hTmem.2 z u ⟨hu.1, hle⟩
      · exact hagree z u ⟨hle, hu.2⟩
    have hbound : min L (sSup A + δ) ≤ sSup A := le_csSup hAbdd hnew
    have hgt : sSup A < min L (sSup A + δ) := lt_min hlt (by linarith)
    linarith
  intro z t ht
  have ht' : t ∈ Icc s (sSup A) := by rw [hTL, hL]; exact ht
  exact hTmem.2 z t ht'

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
