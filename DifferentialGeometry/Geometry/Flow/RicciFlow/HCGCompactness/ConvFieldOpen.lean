import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ConvFieldMain
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricPreconvDiag
import DifferentialGeometry.Geometry.Curvature.Realized.TimeInterval

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Open-time convergence for the P4 metric field

This file isolates the convergence predicate needed to diagonalize the checked
fixed-window `ConvOut` producers over the canonical compact windows of one open
time interval.  It does not choose new bump families or add endpoint data.
-/

noncomputable section

open Set Function Filter Bundle Manifold TopologicalSpace
open scoped Manifold Topology ContDiff BigOperators
open DifferentialGeometry.Integral.Connection

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [Module.Finite Real E] [FiniteDimensional Real E] [CompleteSpace E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedFlowSeq (I := I)}
variable {P : PointedRiemannianManifold (I := I)}
variable {subseq : Nat → Nat}
variable (Φ : PointedCGHMaps (I := I) X P subseq)

/-- Uniform compact-open smooth convergence of the fixed bump-extended metric
sequence along an explicitly supplied reindexing, on one closed time window. -/
structure BumpMetricConv
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    (ρ : Nat → Nat)
    (gInf : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      Real → SmoothRiemannianMetric I P.M)
    (β ψ : Real) : Prop where
  conv : letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    ∀ K : Set P.M, IsCompact K → ∀ p : Nat, ∀ ε : Real, 0 < ε →
      ∃ k₀ : Nat, ∀ k : Nat, k₀ ≤ k → ∀ t, t ∈ Set.Icc β ψ →
        metricDerivNormSupOn (I := I) K p
          (gSeqExt (I := I) Φ R bf hsrc htgt (ρ k) t) (gInf t) R < ε
  convPt : letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : T2Space P.M := P.t2
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    ∀ K : Set P.M, IsCompact K → ∀ p : Nat, ∀ ε : Real, 0 < ε →
      ∃ k₀ : Nat, ∀ k : Nat, k₀ ≤ k → ∀ t, t ∈ Set.Icc β ψ →
        ∀ a : Nat, a ≤ p → ∀ x, x ∈ K →
          metricDerivNorm (I := I) a
            (gSeqExt (I := I) Φ R bf hsrc htgt (ρ k) t) (gInf t) R x < ε

namespace BumpMetricConv

/-- Compact-window convergence persists under a further strict subsequence. -/
theorem comp
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    {ρ : Nat → Nat}
    {gInf : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      Real → SmoothRiemannianMetric I P.M}
    {β ψ : Real}
    (h : BumpMetricConv (I := I) Φ R bf hsrc htgt ρ gInf β ψ)
    (η : Nat → Nat) (hη : StrictMono η) :
    BumpMetricConv (I := I) Φ R bf hsrc htgt (ρ ∘ η) gInf β ψ := by
  refine ⟨?_, ?_⟩
  · intro K hK p ε hε
    obtain ⟨k₀, hk₀⟩ := h.conv K hK p ε hε
    refine ⟨k₀, fun k hk t ht => ?_⟩
    simpa only [Function.comp_apply] using
      hk₀ (η k) (hk.trans (hη.id_le k)) t ht
  · intro K hK p ε hε
    obtain ⟨k₀, hk₀⟩ := h.convPt K hK p ε hε
    refine ⟨k₀, fun k hk t ht a ha x hx => ?_⟩
    simpa only [Function.comp_apply] using
      hk₀ (η k) (hk.trans (hη.id_le k)) t ht a ha x hx

/-- Read convergence proved after reindexing the comparison maps as convergence
of the original bump-extended sequence along the composed subsequence. -/
theorem of_compSubseq
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    (ρ : Nat -> Nat) (hρ : StrictMono ρ) {τ : Nat -> Nat}
    {gInf : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      Real -> SmoothRiemannianMetric I P.M}
    {β ψ : Real}
    (h : BumpMetricConv (I := I) (Φ.compSubseq ρ hρ) R
      (BumpFamily.compSubseq (I := I) Φ bf ρ hρ)
      (SrcSigma.compSubseq (I := I) Φ hsrc ρ hρ)
      (TgtSigma.compSubseq (I := I) Φ htgt ρ hρ) τ gInf β ψ) :
    BumpMetricConv (I := I) Φ R bf hsrc htgt (ρ ∘ τ) gInf β ψ := by
  refine ⟨?_, ?_⟩
  · intro K hK p ε hε
    obtain ⟨k₀, hk₀⟩ := h.conv K hK p ε hε
    refine ⟨k₀, fun k hk t ht => ?_⟩
    simpa only [Function.comp_apply, gSeqExt_compSubseq] using hk₀ k hk t ht
  · intro K hK p ε hε
    obtain ⟨k₀, hk₀⟩ := h.convPt K hK p ε hε
    refine ⟨k₀, fun k hk t ht a ha x hx => ?_⟩
    simpa only [Function.comp_apply, gSeqExt_compSubseq] using
      hk₀ k hk t ht a ha x hx

/-- If a tail of a reindexed metric sequence converges on a compact window,
then the whole reindexed sequence has the same asymptotic convergence. -/
theorem of_tail
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    {ρ : Nat → Nat}
    {gInf : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      Real → SmoothRiemannianMetric I P.M}
    {β ψ : Real} (m : Nat)
    (h : BumpMetricConv (I := I) Φ R bf hsrc htgt
      (fun k => ρ (k + m)) gInf β ψ) :
    BumpMetricConv (I := I) Φ R bf hsrc htgt ρ gInf β ψ := by
  refine ⟨?_, ?_⟩
  · intro K hK p ε hε
    obtain ⟨k₀, hk₀⟩ := h.conv K hK p ε hε
    refine ⟨k₀ + m, fun k hk t ht => ?_⟩
    have hval := hk₀ (k - m) (by omega) t ht
    simpa only [Nat.sub_add_cancel (show m ≤ k by omega)] using hval
  · intro K hK p ε hε
    obtain ⟨k₀, hk₀⟩ := h.convPt K hK p ε hε
    refine ⟨k₀ + m, fun k hk t ht a ha x hx => ?_⟩
    have hval := hk₀ (k - m) (by omega) t ht a ha x hx
    simpa only [Nat.sub_add_cancel (show m ≤ k by omega)] using hval

/-- Window convergence restricts to a smaller closed time interval. -/
theorem mono
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    {ρ : Nat → Nat}
    {gInf : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      Real → SmoothRiemannianMetric I P.M}
    {β ψ c d : Real}
    (h : BumpMetricConv (I := I) Φ R bf hsrc htgt ρ gInf β ψ)
    (hsub : Set.Icc c d ⊆ Set.Icc β ψ) :
    BumpMetricConv (I := I) Φ R bf hsrc htgt ρ gInf c d := by
  refine ⟨?_, ?_⟩
  · intro K hK p ε hε
    obtain ⟨k₀, hk₀⟩ := h.conv K hK p ε hε
    exact ⟨k₀, fun k hk t ht => hk₀ k hk t (hsub ht)⟩
  · intro K hK p ε hε
    obtain ⟨k₀, hk₀⟩ := h.convPt K hK p ε hε
    exact ⟨k₀, fun k hk t ht => hk₀ k hk t (hsub ht)⟩

/-- Window convergence is unchanged by pointwise replacement of the limit
family on that window. -/
theorem congr
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    {ρ : Nat → Nat}
    {A B : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      Real → SmoothRiemannianMetric I P.M}
    {β ψ : Real}
    (h : BumpMetricConv (I := I) Φ R bf hsrc htgt ρ A β ψ)
    (hAB : ∀ t, t ∈ Set.Icc β ψ → A t = B t) :
    BumpMetricConv (I := I) Φ R bf hsrc htgt ρ B β ψ := by
  refine ⟨?_, ?_⟩
  · intro K hK p ε hε
    obtain ⟨k₀, hk₀⟩ := h.conv K hK p ε hε
    refine ⟨k₀, fun k hk t ht => ?_⟩
    simpa only [← hAB t ht] using hk₀ k hk t ht
  · intro K hK p ε hε
    obtain ⟨k₀, hk₀⟩ := h.convPt K hK p ε hε
    refine ⟨k₀, fun k hk t ht a ha x hx => ?_⟩
    simpa only [← hAB t ht] using hk₀ k hk t ht a ha x hx

/-- Two window limits of the same reindexed bump-extended sequence agree at
every time belonging to both windows. -/
theorem unique
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    {ρ : Nat → Nat}
    {A B : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      Real → SmoothRiemannianMetric I P.M}
    {β₁ ψ₁ β₂ ψ₂ t : Real}
    (hA : BumpMetricConv (I := I) Φ R bf hsrc htgt ρ A β₁ ψ₁)
    (hB : BumpMetricConv (I := I) Φ R bf hsrc htgt ρ B β₂ ψ₂)
    (htA : t ∈ Set.Icc β₁ ψ₁) (htB : t ∈ Set.Icc β₂ ψ₂) :
    A t = B t := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  refine metricCInf_unique (I := I)
    (fun k => gSeqExt (I := I) Φ R bf hsrc htgt (ρ k) t) (A t) (B t) R R ?_ ?_
  · intro K hK p ε hε
    obtain ⟨k₀, hk₀⟩ := hA.conv K hK p ε hε
    exact ⟨k₀, fun k hk => hk₀ k hk t htA⟩
  · intro K hK p ε hε
    obtain ⟨k₀, hk₀⟩ := hB.conv K hK p ε hε
    exact ⟨k₀, fun k hk => hk₀ k hk t htB⟩

end BumpMetricConv

namespace ConvOut

/-- Forget a fixed-window `ConvOut` down to the convergence predicate used by
the open-window diagonal. -/
theorem bump_conv
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    {β ψ : Real} (co : ConvOut (I := I) Φ R bf hsrc htgt β ψ) :
    BumpMetricConv (I := I) Φ R bf hsrc htgt co.φ co.gInf β ψ :=
  ⟨co.conv, co.convPt⟩

end ConvOut

/-- One subsequence and one limit metric family converging on every canonical
compact window of an open time interval. -/
structure OpenConvOut
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    (a b t₀ : Real) where
  φ : Nat → Nat
  hφ : StrictMono φ
  gInf : letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    Real → SmoothRiemannianMetric I P.M
  convOn : ∀ n : Nat,
    BumpMetricConv (I := I) Φ R bf hsrc htgt φ gInf
      (RealTimeInterval.openWindowLeft a t₀ n)
      (RealTimeInterval.openWindowRight b t₀ n)

namespace OpenConvOut

/-- Read an open-interval convergence output as the existing fixed-window
`ConvOut` package on one canonical window. -/
noncomputable def at_window
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    {a b t₀ : Real}
    (co : OpenConvOut (I := I) Φ R bf hsrc htgt a b t₀) (n : Nat) :
    ConvOut (I := I) Φ R bf hsrc htgt
      (RealTimeInterval.openWindowLeft a t₀ n)
      (RealTimeInterval.openWindowRight b t₀ n) where
  φ := co.φ
  hφ := co.hφ
  gInf := co.gInf
  conv := (co.convOn n).conv
  convPt := (co.convOn n).convPt

/-- The open-interval output supplies the same convergence on every closed
time interval compactly contained in the open interval. -/
theorem conv_Icc
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    {a b t₀ c d : Real}
    (co : OpenConvOut (I := I) Φ R bf hsrc htgt a b t₀)
    (ht₀ : t₀ ∈ Set.Ioo a b) (hcd : Set.Icc c d ⊆ Set.Ioo a b) :
    BumpMetricConv (I := I) Φ R bf hsrc htgt co.φ co.gInf c d := by
  obtain ⟨n, hn⟩ := RealTimeInterval.exists_window_superset ht₀ hcd
  exact BumpMetricConv.mono (Φ := Φ) (co.convOn n) hn

end OpenConvOut

/-- Diagonalize compatible fixed-window convergence producers and glue their
uniquely determined metric limits into one open-interval output.  The bump
family and the underlying extended metric sequence are fixed before this
theorem is called. -/
theorem exists_openConv
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    {a b t₀ : Real} (ht₀ : t₀ ∈ Set.Ioo a b)
    (hrefine : ∀ n : Nat, ∀ ρ : Nat → Nat, StrictMono ρ →
      ∃ τ : Nat → Nat, StrictMono τ ∧
        ∃ gN : letI : TopologicalSpace P.M := P.topology
          letI : ChartedSpace H P.M := P.charted
          letI : IsManifold I ∞ P.M := P.smooth
          Real → SmoothRiemannianMetric I P.M,
          BumpMetricConv (I := I) Φ R bf hsrc htgt (ρ ∘ τ) gN
            (RealTimeInterval.openWindowLeft a t₀ n)
            (RealTimeInterval.openWindowRight b t₀ n)) :
    Nonempty (OpenConvOut (I := I) Φ R bf hsrc htgt a b t₀) := by
  classical
  let Pwin : Nat → (Nat → Nat) → Prop := fun n ρ =>
    ∃ gN : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      Real → SmoothRiemannianMetric I P.M,
      BumpMetricConv (I := I) Φ R bf hsrc htgt ρ gN
        (RealTimeInterval.openWindowLeft a t₀ n)
        (RealTimeInterval.openWindowRight b t₀ n)
  obtain ⟨φ, hφ, hPφ⟩ := exists_diag_subseq Pwin
    (fun n ρ hρ => by
      obtain ⟨τ, hτ, gN, hgN⟩ := hrefine n ρ hρ
      exact ⟨τ, hτ, gN, hgN⟩)
    (fun _n _ρ τ hτ hP => by
      obtain ⟨gN, hgN⟩ := hP
      exact ⟨gN, BumpMetricConv.comp (Φ := Φ) hgN τ hτ⟩)
    (fun _n ρ m hP => by
      obtain ⟨gN, hgN⟩ := hP
      exact ⟨gN, BumpMetricConv.of_tail (Φ := Φ) m hgN⟩)
  choose gN hgN using hPφ
  let idx : Real → Nat := fun t =>
    if ht : t ∈ Set.Ioo a b then
      Classical.choose (RealTimeInterval.mem_openWindow (t₀ := t₀) ht)
    else 0
  have hidx : ∀ {t : Real}, t ∈ Set.Ioo a b →
      t ∈ RealTimeInterval.openWindow a b t₀ (idx t) := by
    intro t ht
    dsimp only [idx]
    rw [dif_pos ht]
    exact Classical.choose_spec (RealTimeInterval.mem_openWindow (t₀ := t₀) ht)
  let gInf : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      Real → SmoothRiemannianMetric I P.M := fun t =>
    if ht : t ∈ Set.Ioo a b then gN (idx t) t else R
  have hgInf : ∀ n : Nat, ∀ t : Real,
      t ∈ RealTimeInterval.openWindow a b t₀ n → gInf t = gN n t := by
    intro n t ht
    have htOpen : t ∈ Set.Ioo a b := RealTimeInterval.openWindow_subset ht₀ n ht
    have hdef : gInf t = gN (idx t) t := by
      dsimp only [gInf]
      rw [dif_pos htOpen]
    rw [hdef]
    exact BumpMetricConv.unique (Φ := Φ) (hgN (idx t)) (hgN n) (hidx htOpen) ht
  exact ⟨{
    φ := φ
    hφ := hφ
    gInf := gInf
    convOn := fun n =>
      BumpMetricConv.congr (Φ := Φ) (hgN n) fun t ht => (hgInf n t ht).symm
  }⟩

/-- Produce one open-interval convergence output from the four raw
fixed-window hypotheses of `convOut`, supplied on every canonical compact
window.  The original bump family is fixed once; each prescribed refinement
is handled by reindexing that family and rerunning `convOut`. -/
theorem exists_openConv_raw
    {R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    {a b t₀ : Real} (ht₀ : t₀ ∈ Set.Ioo a b)
    (cLow : Nat -> Real) (hcLow : ∀ n, 0 < cLow n)
    (hbound : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : IsManifold I ∞ P.M := P.smooth
      ∀ n k : Nat, ∀ t : Real,
        t ∈ RealTimeInterval.openWindow a b t₀ n ->
        ∀ (y : SourceDomain (I := I) Φ k)
          (v : letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
                sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
                sourceDomCharted (I := I) Φ k
            TangentSpace I y),
          cLow n * R.inner (y : P.M) v v <=
            letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
              sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
              sourceDomCharted (I := I) Φ k
            letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
              sourceDomSmooth (I := I) Φ k
            (srcMetric (I := I) Φ hsrc htgt k t).inner y v v)
    (hcovTail : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : T2Space P.M := P.t2
        letI : IsManifold I ∞ P.M := P.smooth
        letI : SigmaCompactSpace P.M := P.sigmaCompact
      ∀ n q : Nat, ∃ C : Real, ∀ (k : Nat) (t : Real),
        t ∈ RealTimeInterval.openWindow a b t₀ n ->
        ∀ z : P.M, z ∈ bf.grow k ->
          metricCovDerivNorm (I := I) q
            (gSeqExt (I := I) Φ R bf hsrc htgt k t) R z <= C)
    (hlipTail : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : T2Space P.M := P.t2
        letI : IsManifold I ∞ P.M := P.smooth
        letI : SigmaCompactSpace P.M := P.sigmaCompact
      ∀ n p : Nat, ∃ Lt : Real, 0 <= Lt /\
        ∀ (k : Nat) (s t : Real),
          s ∈ RealTimeInterval.openWindow a b t₀ n ->
          t ∈ RealTimeInterval.openWindow a b t₀ n ->
          ∀ q : Nat, q <= p -> ∀ z : P.M, z ∈ bf.grow k ->
            metricDerivNorm (I := I) q
              (gSeqExt (I := I) Φ R bf hsrc htgt k s)
              (gSeqExt (I := I) Φ R bf hsrc htgt k t) R z <=
                Lt * |s - t|)
    (hlipSrc : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : T2Space P.M := P.t2
        letI : IsManifold I ∞ P.M := P.smooth
        letI : SigmaCompactSpace P.M := P.sigmaCompact
      ∀ n k : Nat,
        letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
          sourceDomTop (I := I) Φ k
        letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
          sourceDomCharted (I := I) Φ k
        letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
        letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) :=
          sourceDomSmooth (I := I) Φ k
        letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
          sourceDomSigmaOf (I := I) Φ k (hsrc k)
        letI : SigmaCompactSpace ↥(sourceOpen (I := I) Φ k) :=
          sourceDomSigmaOf (I := I) Φ k (hsrc k)
        letI : T2Space ↥(sourceOpen (I := I) Φ k) := sourceDomT2 (I := I) Φ k
        ∀ C : Set (SourceDomain (I := I) Φ k), IsCompact C -> ∀ p : Nat,
          ∃ Ls : Real, 0 <= Ls /\
            ∀ (s t : Real),
              s ∈ RealTimeInterval.openWindow a b t₀ n ->
              t ∈ RealTimeInterval.openWindow a b t₀ n ->
              ∀ q : Nat, q <= p ->
                ∀ y : SourceDomain (I := I) Φ k, y ∈ C ->
                  metricDerivNorm (I := I) q
                    (srcMetric (I := I) Φ hsrc htgt k s)
                    (srcMetric (I := I) Φ hsrc htgt k t)
                    (refRes (I := I) Φ R hsrc k) y <= Ls * |s - t|) :
    Nonempty (OpenConvOut (I := I) Φ R bf hsrc htgt a b t₀) := by
  classical
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  refine exists_openConv (Φ := Φ) ht₀ ?_
  intro n ρ hρ
  let bfρ := BumpFamily.compSubseq (I := I) Φ bf ρ hρ
  let hsrcρ := SrcSigma.compSubseq (I := I) Φ hsrc ρ hρ
  let htgtρ := TgtSigma.compSubseq (I := I) Φ htgt ρ hρ
  have hboundρ : ∀ (k : Nat) (t : Real),
      t ∈ RealTimeInterval.openWindow a b t₀ n ->
      ∀ (y : SourceDomain (I := I) (Φ.compSubseq ρ hρ) k)
        (v : letI : TopologicalSpace
              (SourceDomain (I := I) (Φ.compSubseq ρ hρ) k) :=
                sourceDomTop (I := I) (Φ.compSubseq ρ hρ) k
          letI : ChartedSpace H
              (SourceDomain (I := I) (Φ.compSubseq ρ hρ) k) :=
                sourceDomCharted (I := I) (Φ.compSubseq ρ hρ) k
          TangentSpace I y),
        cLow n * R.inner (y : P.M) v v <=
          letI : TopologicalSpace
              (SourceDomain (I := I) (Φ.compSubseq ρ hρ) k) :=
                sourceDomTop (I := I) (Φ.compSubseq ρ hρ) k
          letI : ChartedSpace H
              (SourceDomain (I := I) (Φ.compSubseq ρ hρ) k) :=
                sourceDomCharted (I := I) (Φ.compSubseq ρ hρ) k
          letI : IsManifold I ∞
              (SourceDomain (I := I) (Φ.compSubseq ρ hρ) k) :=
                sourceDomSmooth (I := I) (Φ.compSubseq ρ hρ) k
          (srcMetric (I := I) (Φ.compSubseq ρ hρ) hsrcρ htgtρ k t).inner y v v := by
    intro k t ht y v
    simpa only [hsrcρ, htgtρ, srcMetric_compSubseq] using
      hbound n (ρ k) t ht y v
  have hcovTailρ : ∀ q : Nat, ∃ C : Real, ∀ (k : Nat) (t : Real),
      t ∈ RealTimeInterval.openWindow a b t₀ n ->
      ∀ z : P.M, z ∈ bfρ.grow k ->
        metricCovDerivNorm (I := I) q
          (gSeqExt (I := I) (Φ.compSubseq ρ hρ) R bfρ hsrcρ htgtρ k t) R z <= C := by
    intro q
    obtain ⟨C, hC⟩ := hcovTail n q
    refine ⟨C, fun k t ht z hz => ?_⟩
    simpa only [bfρ, hsrcρ, htgtρ, gSeqExt_compSubseq] using
      hC (ρ k) t ht z hz
  have hlipTailρ : ∀ p : Nat, ∃ Lt : Real, 0 <= Lt /\
      ∀ (k : Nat) (s t : Real),
        s ∈ RealTimeInterval.openWindow a b t₀ n ->
        t ∈ RealTimeInterval.openWindow a b t₀ n ->
        ∀ q : Nat, q <= p -> ∀ z : P.M, z ∈ bfρ.grow k ->
          metricDerivNorm (I := I) q
            (gSeqExt (I := I) (Φ.compSubseq ρ hρ) R bfρ hsrcρ htgtρ k s)
            (gSeqExt (I := I) (Φ.compSubseq ρ hρ) R bfρ hsrcρ htgtρ k t) R z <=
              Lt * |s - t| := by
    intro p
    obtain ⟨Lt, hLt0, hLt⟩ := hlipTail n p
    refine ⟨Lt, hLt0, fun k s t hs ht q hq z hz => ?_⟩
    simpa only [bfρ, hsrcρ, htgtρ, gSeqExt_compSubseq] using
      hLt (ρ k) s t hs ht q hq z hz
  have hlipSrcρ : ∀ k : Nat,
      letI : TopologicalSpace (SourceDomain (I := I) (Φ.compSubseq ρ hρ) k) :=
        sourceDomTop (I := I) (Φ.compSubseq ρ hρ) k
      letI : ChartedSpace H (SourceDomain (I := I) (Φ.compSubseq ρ hρ) k) :=
        sourceDomCharted (I := I) (Φ.compSubseq ρ hρ) k
      letI : T2Space (SourceDomain (I := I) (Φ.compSubseq ρ hρ) k) :=
        sourceDomT2 (I := I) (Φ.compSubseq ρ hρ) k
      letI : IsManifold I ∞ (SourceDomain (I := I) (Φ.compSubseq ρ hρ) k) :=
        sourceDomSmooth (I := I) (Φ.compSubseq ρ hρ) k
      letI : SigmaCompactSpace (SourceDomain (I := I) (Φ.compSubseq ρ hρ) k) :=
        sourceDomSigmaOf (I := I) (Φ.compSubseq ρ hρ) k (hsrcρ k)
      letI : SigmaCompactSpace ↥(sourceOpen (I := I) (Φ.compSubseq ρ hρ) k) :=
        sourceDomSigmaOf (I := I) (Φ.compSubseq ρ hρ) k (hsrcρ k)
      letI : T2Space ↥(sourceOpen (I := I) (Φ.compSubseq ρ hρ) k) :=
        sourceDomT2 (I := I) (Φ.compSubseq ρ hρ) k
      ∀ C : Set (SourceDomain (I := I) (Φ.compSubseq ρ hρ) k), IsCompact C ->
        ∀ p : Nat, ∃ Ls : Real, 0 <= Ls /\
          ∀ (s t : Real),
            s ∈ RealTimeInterval.openWindow a b t₀ n ->
            t ∈ RealTimeInterval.openWindow a b t₀ n ->
            ∀ q : Nat, q <= p ->
              ∀ y : SourceDomain (I := I) (Φ.compSubseq ρ hρ) k, y ∈ C ->
                metricDerivNorm (I := I) q
                  (srcMetric (I := I) (Φ.compSubseq ρ hρ) hsrcρ htgtρ k s)
                  (srcMetric (I := I) (Φ.compSubseq ρ hρ) hsrcρ htgtρ k t)
                  (refRes (I := I) (Φ.compSubseq ρ hρ) R hsrcρ k) y <=
                    Ls * |s - t| := by
    intro k C hC p
    obtain ⟨Ls, hLs0, hLs⟩ := hlipSrc n (ρ k) C hC p
    refine ⟨Ls, hLs0, fun s t hs ht q hq y hy => ?_⟩
    simpa only [hsrcρ, htgtρ, srcMetric_compSubseq, refRes_compSubseq] using
      hLs s t hs ht q hq y hy
  have hβψ : RealTimeInterval.openWindowLeft a t₀ n <=
      RealTimeInterval.openWindowRight b t₀ n :=
    (RealTimeInterval.initial_mem_window ht₀ n).1.trans
      (RealTimeInterval.initial_mem_window ht₀ n).2
  let coρ := convOut (I := I) (Φ := Φ.compSubseq ρ hρ) R bfρ hsrcρ htgtρ
    (RealTimeInterval.openWindowLeft a t₀ n)
    (RealTimeInterval.openWindowRight b t₀ n) hβψ (cLow n) (hcLow n)
    hboundρ hcovTailρ hlipTailρ hlipSrcρ
  refine ⟨coρ.φ, coρ.hφ, coρ.gInf, ?_⟩
  exact BumpMetricConv.of_compSubseq (Φ := Φ) ρ hρ
    (ConvOut.bump_conv (Φ := Φ.compSubseq ρ hρ) coρ)

end HCGCompactness
end DifferentialGeometry
