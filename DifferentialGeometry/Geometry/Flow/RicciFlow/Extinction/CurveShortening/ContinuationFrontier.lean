import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.WindowGluing

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [t2M : T2Space M] [compactM : CompactSpace M]
  [nonemptyM : Nonempty M] [hBoundary : I.Boundaryless]
include t2M compactM nonemptyM hBoundary
variable {D : RealTimeInterval} {a b : ℝ}

omit [SigmaCompactSpace M] compactM nonemptyM hBoundary in
theorem curveShorteningContinuation_iff_terminalClosure_and_extension
    (B : RicciBackground (I := I) (M := M) D a b) :
    curveShorteningContinuation (I := I) (M := M) B ↔
      curveShorteningTerminalClosure (I := I) (M := M) B ∧
        curveShorteningExtension (I := I) (M := M) B := by
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · intro T haT hTb c K hK hc hcurv
      obtain ⟨cT, _, hclosed, _⟩ := h T haT hTb c hc K hK hcurv
      obtain ⟨closed, hsol, hagr, _⟩ := hclosed
      exact ⟨closed, hsol, hagr⟩
    · intro T haT hTb c K hK hc hcurv
      obtain ⟨cT, _, _, hext⟩ := h T haT hTb.le c hc K hK hcurv
      exact hext hTb
  · rintro ⟨hclose, hext⟩ T haT hTb c hc K hK hcurv
    obtain ⟨closed, hsol, hagr⟩ := hclose T haT hTb c K hK hc hcurv
    exact ⟨SmoothImmersion.slice closed hsol.smooth hsol.immersed T ⟨haT.le, le_rfl⟩,
      fun N e => CurveMap.tendsto_slice_of_terminalClosure e haT hsol hagr hc.smooth hc.immersed,
      ⟨closed, hsol, hagr, fun z => rfl⟩,
      fun hlt => hext T haT hlt c K hK hc hcurv⟩

omit [SigmaCompactSpace M] compactM nonemptyM hBoundary in
theorem curveShorteningExtension_of_terminalClosure_and_localWindow
    (B : RicciBackground (I := I) (M := M) D a b)
    (hclose : curveShorteningTerminalClosure (I := I) (M := M) B)
    (hwin : curveShorteningLocalWindow (I := I) (M := M) B.toSmoothMetricWindow)
    (huniq : curveShorteningLocalUniqueness (I := I) (M := M) B.toSmoothMetricWindow)
    {N : ℕ} (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N) :
    curveShorteningExtension (I := I) (M := M) B := by
  intro T haT hTb c K hK hc hcurv
  obtain ⟨closed, hsol, hagr⟩ := hclose T haT hTb.le c K hK hc hcurv
  exact exists_extension_of_localWindow B.toSmoothMetricWindow e haT hTb hc
    ⟨closed, hsol, hagr⟩ hwin huniq


omit [CompleteSpace E] [SigmaCompactSpace M] t2M compactM nonemptyM hBoundary in
theorem curveShorteningLocalWindow_of_uniformLocalWindow
    (B : SmoothMetricWindow (I := I) (M := M) D a b)
    (h : curveShorteningUniformLocalWindow (I := I) (M := M) B) :
    curveShorteningLocalWindow (I := I) (M := M) B := by
  obtain ⟨τ, hτpos, hwin⟩ := h
  intro t₀ c₀ N e
  let instImm : TopologicalSpace (SmoothImmersion (I := I) (M := M)) := smoothImmersionTopology e
  let instCyl : TopologicalSpace (CurveMap M) := smoothCylinderTopology e (Icc a b)
  obtain ⟨U, hUopen, hmem, sols, hcont, hprop⟩ := hwin t₀ c₀ N e
  have ht₀min : (t₀.1 : ℝ) < min b ((t₀.1 : ℝ) + τ) := lt_min t₀.2.2 (by linarith)
  set ρ : ℝ := min (min b ((t₀.1 : ℝ) + τ) - t₀.1) ((b - t₀.1) / 2) with hρ
  have hρpos : 0 < ρ := by
    rw [hρ]
    exact lt_min (by linarith) (half_pos (by linarith [t₀.2.2]))
  have hρle : ρ ≤ τ := by
    rw [hρ]
    have h1 : min b ((t₀.1 : ℝ) + τ) - t₀.1 ≤ τ := by
      have h2 := min_le_right b ((t₀.1 : ℝ) + τ)
      linarith
    exact (min_le_left _ _).trans h1
  have hρb : (t₀.1 : ℝ) + ρ < b := by
    rw [hρ]
    have h2 := min_le_right (min b ((t₀.1 : ℝ) + τ) - t₀.1) ((b - t₀.1) / 2)
    linarith
  set U' : Set ({t : ℝ // t ∈ Ico a b} × SmoothImmersion (I := I) (M := M)) :=
    U ∩ {p | (p.1.1 : ℝ) + ρ < b} with hU'def
  have hU'open : IsOpen U' := by
    rw [hU'def]
    refine hUopen.inter ?_
    have hcont₁ : Continuous fun p : ({t : ℝ // t ∈ Ico a b} ×
        SmoothImmersion (I := I) (M := M)) => ((p.1.1 : ℝ)) :=
      continuous_subtype_val.comp continuous_fst
    exact isOpen_lt (hcont₁.add continuous_const) continuous_const
  have hsub : Continuous fun p : U' => (⟨(p : {t : ℝ // t ∈ Ico a b} ×
      SmoothImmersion (I := I) (M := M)), p.2.1⟩ : U) :=
    Continuous.subtype_mk continuous_subtype_val _
  have hcont' : Continuous (fun p : U' => sols ⟨p.1, p.2.1⟩) := hcont.comp hsub
  refine ⟨ρ, hρpos, U', hU'open, ⟨hmem, hρb⟩, fun p => sols ⟨p.1, p.2.1⟩,
    hcont', fun p => ?_⟩
  obtain ⟨hsol, hinit⟩ := hprop ⟨p.1, p.2.1⟩
  have hle : (p.1.1 : ℝ) + ρ ≤ min b ((p.1.1 : ℝ) + τ) :=
    le_min (le_of_lt p.2.2) (by linarith [hρle])
  exact ⟨le_of_lt p.2.2, hsol.mono_Icc le_rfl hle (by linarith), fun z => hinit z⟩


end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
