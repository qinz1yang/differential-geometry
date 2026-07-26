import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ConvFieldInputs
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.ConvFieldPDE
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.FlowLimitBuild
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.FlowLimitUpgrade
import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCompactnessSubseq

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

/-!
# Brick 7b of the P4 conv engine — the endgame assembly (MSM135 Thm 3.10 ⇐ 3.9)

Assembles the DONE Bricks 4–7a into the theorem-facing upgrade
`CompactnessConclusion X`, modulo the THREE tracked inputs (Thm 3.9's `mc`, the
moving-Shi bound `hShiT`, and the joint regularity `hsmooth` of the limit) plus
the mc-comparison data the plan sanctions (`hequivT`/`hrel`/`hcp`/`hcovSrc`/
`hlipG`/`hkcont`).

See `ConvFieldEndgame.md` for the route, ruling A/B decisions, and gotchas.
-/

noncomputable section

open Set Function Filter Bundle Manifold Tensor0SBundle
open scoped Manifold Topology ContDiff BigOperators
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.PDE.RicciFlow (SolutionOn IsSolutionOn)

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

set_option maxHeartbeats 1600000 in
/-- Compatibility wrapper promoting the pointwise closed-window scalar
producer to all carrier times when the carrier lies in that one window. -/
theorem ConvOut.scalar_conv
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat → Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    (β ψ : Real) (cLow : Real) (hcLow : 0 < cLow)
    (hbound : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : IsManifold I ∞ P.M := P.smooth
      ∀ (k : Nat) (t : Real), t ∈ Set.Icc β ψ →
        ∀ (y : SourceDomain (I := I) Φ k)
          (v : letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
              sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
              sourceDomCharted (I := I) Φ k
            TangentSpace I y),
          cLow * R.inner (y : P.M) v v ≤
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
      ∀ q : Nat, ∃ C : Real, ∀ (k : Nat) (t : Real), t ∈ Set.Icc β ψ →
        ∀ z : P.M, z ∈ bf.grow k →
          metricCovDerivNorm (I := I) q
            (gSeqExt (I := I) Φ R bf hsrc htgt k t) R z ≤ C)
    (co : ConvOut (I := I) Φ R bf hsrc htgt β ψ)
    (hcarrier : X.D.carrier ⊆ Set.Icc β ψ) :
    FunctionPullbackTendsto (I := I) (Φ.compSubseq co.φ co.hφ)
      (fun k t x ↦
        letI : TopologicalSpace (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).topology
        letI : ChartedSpace H (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).charted
        letI : IsManifold I ∞ (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).smooth
        letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
            (X.term ((subseq ∘ co.φ) k)).M := by
          change IsManifold I ∞ (X.term ((subseq ∘ co.φ) k)).M
          infer_instance
        letI : SigmaCompactSpace (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).sigmaCompact
        letI : T2Space (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).t2
        (X.term ((subseq ∘ co.φ) k)).S.scalar t x)
      (fun t x ↦
        letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : IsManifold I ∞ P.M := P.smooth
        letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
          change IsManifold I ∞ P.M
          infer_instance
        letI : SigmaCompactSpace P.M := P.sigmaCompact
        letI : T2Space P.M := P.t2
        metricScalarAt (I := I) (co.gInf t) x) := by
  intro t ht x
  simpa only [Function.comp_apply, PointedCGHMaps.compSubseq, PointedCGHMaps.map] using
    ConvOut.scalar_conv_at (I := I) Φ R bf hsrc htgt β ψ cLow hcLow hbound
      hcovTail co (hcarrier ht) x

set_option maxHeartbeats 1600000 in
/-- Compatibility wrapper promoting the pointwise closed-window squared
Ricci-norm producer to all carrier times. -/
theorem ConvOut.ricNorm_conv
    {X : PointedFlowSeq (I := I)}
    {P : PointedRiemannianManifold (I := I)}
    {subseq : Nat → Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (R : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    (β ψ : Real) (cLow : Real) (hcLow : 0 < cLow)
    (hbound : letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : IsManifold I ∞ P.M := P.smooth
      ∀ (k : Nat) (t : Real), t ∈ Set.Icc β ψ →
        ∀ (y : SourceDomain (I := I) Φ k)
          (v : letI : TopologicalSpace (SourceDomain (I := I) Φ k) :=
                sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) :=
                sourceDomCharted (I := I) Φ k
            TangentSpace I y),
          cLow * R.inner (y : P.M) v v ≤
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
      ∀ q : Nat, ∃ C : Real, ∀ (k : Nat) (t : Real), t ∈ Set.Icc β ψ →
        ∀ z : P.M, z ∈ bf.grow k →
          metricCovDerivNorm (I := I) q
            (gSeqExt (I := I) Φ R bf hsrc htgt k t) R z ≤ C)
    (co : ConvOut (I := I) Φ R bf hsrc htgt β ψ)
    (hcarrier : X.D.carrier ⊆ Set.Icc β ψ) :
    FunctionPullbackTendsto (I := I) (Φ.compSubseq co.φ co.hφ)
      (fun k t x ↦
        letI : TopologicalSpace (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).topology
        letI : ChartedSpace H (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).charted
        letI : IsManifold I ∞ (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).smooth
        letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
            (X.term ((subseq ∘ co.φ) k)).M := by
          change IsManifold I ∞ (X.term ((subseq ∘ co.φ) k)).M
          infer_instance
        letI : SigmaCompactSpace (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).sigmaCompact
        letI : T2Space (X.term ((subseq ∘ co.φ) k)).M :=
          (X.term ((subseq ∘ co.φ) k)).t2
        DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I)
          (X.term ((subseq ∘ co.φ) k)).S t x)
      (fun t x ↦
        letI : TopologicalSpace P.M := P.topology
        letI : ChartedSpace H P.M := P.charted
        letI : IsManifold I ∞ P.M := P.smooth
        letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) P.M := by
          change IsManifold I ∞ P.M
          infer_instance
        letI : SigmaCompactSpace P.M := P.sigmaCompact
        letI : T2Space P.M := P.t2
        normSq0S (I := I) (co.gInf t) x 2
          (metricRicci (I := I) (co.gInf t) x)) := by
  intro t ht x
  simpa only [Function.comp_apply, PointedCGHMaps.compSubseq,
    PointedCGHMaps.map] using
    ConvOut.ricNorm_conv_at (I := I) Φ R bf hsrc htgt β ψ cLow hcLow hbound
      hcovTail co (hcarrier ht) x

section Endgame

variable {X : PointedFlowSeq (I := I)}

/-! ### The comparison-map scaffold and the AA output

The AA extraction `convOut` needs a `Φ : PointedCGHMaps X L subseq`, hence a
`L : PointedFlowData` on the limit manifold, to name the pulled-back source flows.
The endgame is therefore parametrized by the limit flow `L` and `hL0 : L.atTime 0
= mc.limit` (ruling 5b), and `Φ := pointedCGHMaps_of_atZero X L mc.subseq
(hL0.symm ▸ mc.maps)`.  The AA output family `(endgameCo …).gInf` is the metric of
the limit flow (`hLmetric`), so the conv-field bridge closes by that identification. -/

/-- The comparison maps for the limit flow `L`, from the time-0 maps `mc.maps`
transported along `hL0` (the `cghMaps_of_hL0` producer specialized to `mc`). -/
noncomputable def endgamePhi
    (mc : MetricCompactnessConclusion (I := I) (X.atZero (I := I)))
    (L : PointedFlowData (I := I) X.D)
    (hL0 : L.atTime (I := I) 0 = mc.limit) :
    PointedCGHMaps (I := I) X (L.atTime 0) mc.subseq :=
  pointedCGHMaps_of_atZero (I := I) X L mc.subseq (hL0.symm ▸ mc.maps)

/-- **Brick 7b: the concrete endgame upgrade data.**  From the limit flow `L`
with `hL0 : L.atTime 0 = mc.limit`, the AA output `co` for the comparison maps
`endgamePhi mc L hL0`, the metric identification `hLmetric` (the limit-flow metric
IS the AA limit `co.gInf` on the window), the scalar-curvature pullback convergence
`scalar`, and the window-covering hypothesis `hcarrier : X.D.carrier ⊆ [β,ψ]`,
produce `FlowUpgradeData` over the time-zero Cheeger--Gromov compactness
conclusion `mc`.

The subsequence is re-indexed along `co.φ`; the re-indexed maps
`(endgamePhi mc L hL0).compSubseq co.φ co.hφ` have, at stage `k`, source/target and
partial diffeomorphism definitionally those of `endgamePhi` at `co.φ k`, so the conv
field's `ofRestrictPullback` data reduces to the `ofRP_supOn_conv` bridge output by
`rfl` (no `▸`-cast reconciliation needed). -/
noncomputable def flowUpgrade_of_maps
    (mc : MetricCompactnessConclusion (I := I) (X.atZero (I := I)))
    (L : PointedFlowData (I := I) X.D)
    (P : PointedRiemannianManifold (I := I))
    (hPlim : P = mc.limit)
    (hPL : L.atTime (I := I) 0 = P)
    (Φ : PointedCGHMaps (I := I) X P mc.subseq)
    (R :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ)
    (hsrc : SrcSigma (I := I) Φ)
    (htgt : TgtSigma (I := I) Φ)
    (β ψ : Real)
    (hcarrier : X.D.carrier ⊆ Set.Icc β ψ)
    (co : ConvOut (I := I) Φ R bf hsrc htgt β ψ)
    (hLmetric :
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      forall t : Real, t ∈ Set.Icc β ψ ->
        HEq (L.S.family.metric t) (co.gInf t))
    (scalar : ScalarPullbackTendsto (I := I)
      (hPL.symm ▸ (Φ.compSubseq co.φ co.hφ) :
        PointedCGHMaps (I := I) X (L.atTime 0) (mc.subseq ∘ co.φ)))
    (ricciNorm : RicNormPullback (I := I)
      (hPL.symm ▸ (Φ.compSubseq co.φ co.hφ) :
        PointedCGHMaps (I := I) X (L.atTime 0) (mc.subseq ∘ co.φ))) :
    FlowUpgradeData (I := I) X mc := by
  have hL0 : L.atTime (I := I) 0 = mc.limit := hPL.trans hPlim
  subst hPL
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : T2Space L.M := L.t2
  letI : IsManifold I ∞ L.M := L.smooth
  letI : SigmaCompactSpace L.M := L.sigmaCompact
  letI : TopologicalSpace (L.atTime 0).M := L.topology
  letI : ChartedSpace H (L.atTime 0).M := L.charted
  letI : T2Space (L.atTime 0).M := L.t2
  letI : IsManifold I ∞ (L.atTime 0).M := L.smooth
  letI : SigmaCompactSpace (L.atTime 0).M := L.sigmaCompact
  have hLm : forall t : Real, t ∈ Set.Icc β ψ -> L.S.family.metric t = co.gInf t :=
    fun t ht => eq_of_heq (hLmetric t ht)
  have hscalar : ScalarPullbackTendsto (I := I) (Φ.compSubseq co.φ co.hφ) := scalar
  have hricciNorm : RicNormPullback (I := I) (Φ.compSubseq co.φ co.hφ) := ricciNorm
  -- the re-indexed Theorem 3.9 conclusion and the re-indexed spacetime maps
  set mc' := mc.compSubseq co.φ co.hφ with hmc'
  set Φ' := (Φ).compSubseq co.φ co.hφ with hΦ'
  -- expose the further subsequence and its concrete FlowLimitData
  refine ⟨co.φ, co.hφ, ?_⟩
  change FlowLimitData (I := I) X mc'
  refine
    { L := L
      hL0 := by simpa [mc'] using hL0
      maps := Φ'
      scalar := hscalar
      ricciNorm := hricciNorm
      hσsrc := ?_
      hσtgt := ?_
      refMetric := ?_
      conv := ?_ }
  · -- source σ-compactness: `Φ'.source k = endgamePhi.source (co.φ k)`, open in `L.M`
    intro k
    exact Geometry.isSigmaCompact_of_isOpen I (PointedCGHMaps.source_open (I := I) Φ' k)
  · -- target σ-compactness
    intro k
    letI : TopologicalSpace (X.term (mc'.subseq k)).M := (X.term (mc'.subseq k)).topology
    letI : ChartedSpace H (X.term (mc'.subseq k)).M := (X.term (mc'.subseq k)).charted
    letI : SigmaCompactSpace (X.term (mc'.subseq k)).M := (X.term (mc'.subseq k)).sigmaCompact
    exact Geometry.isSigmaCompact_of_isOpen I (PointedCGHMaps.target_open (I := I) Φ' k)
  · -- the per-`k` reference metric: the restricted reference on the source domain
    intro k
    exact fun _ => refRes (I := I) Φ' R
      (fun j => Geometry.isSigmaCompact_of_isOpen I
        (PointedCGHMaps.source_open (I := I) Φ' j)) k
  · -- the conv field: the `ofRP_supOn_conv` bridge, sub-window inclusion.
    -- `Φ'.partialDiffeomorph k = endgamePhi.partialDiffeomorph (co.φ k)` by `rfl`,
    -- so `ofRestrictPullback Φ' k` reduces to `ofRestrictPullback endgamePhi (co.φ k)`.
    intro K hK p a b hab ε hε
    have hbridge := ofRP_supOn_conv (I := I) (Φ) R bf hsrc htgt β ψ
      co (letI : TopologicalSpace L.M := L.topology; letI : ChartedSpace H L.M := L.charted; letI : IsManifold I ∞ L.M := L.smooth; letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) L.M := (by change IsManifold I ∞ L.M; infer_instance); letI : SigmaCompactSpace L.M := L.sigmaCompact; letI : T2Space L.M := L.t2; L.S.family.metric) hLm K hK p ε hε
    obtain ⟨k0, hk0⟩ := hbridge
    refine ⟨k0, fun k hk t ht => ?_⟩
    have htβψ : t ∈ Set.Icc β ψ := hcarrier (hab ht)
    exact hk0 k hk t htβψ

/-- Assemble the smooth CGH compactness conclusion from the concrete endgame
upgrade data produced by `flowUpgrade_of_maps`. -/
theorem flowLimit_of_maps
    (mc : MetricCompactnessConclusion (I := I) (X.atZero (I := I)))
    (L : PointedFlowData (I := I) X.D)
    (P : PointedRiemannianManifold (I := I))
    (hPlim : P = mc.limit)
    (hPL : L.atTime (I := I) 0 = P)
    (Φ : PointedCGHMaps (I := I) X P mc.subseq)
    (R :
      letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ)
    (hsrc : SrcSigma (I := I) Φ)
    (htgt : TgtSigma (I := I) Φ)
    (β ψ : Real)
    (hcarrier : X.D.carrier ⊆ Set.Icc β ψ)
    (co : ConvOut (I := I) Φ R bf hsrc htgt β ψ)
    (hLmetric :
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      forall t : Real, t ∈ Set.Icc β ψ ->
        HEq (L.S.family.metric t) (co.gInf t))
    (scalar : ScalarPullbackTendsto (I := I)
      (hPL.symm ▸ (Φ.compSubseq co.φ co.hφ) :
        PointedCGHMaps (I := I) X (L.atTime 0) (mc.subseq ∘ co.φ)))
    (ricciNorm : RicNormPullback (I := I)
      (hPL.symm ▸ (Φ.compSubseq co.φ co.hφ) :
        PointedCGHMaps (I := I) X (L.atTime 0) (mc.subseq ∘ co.φ))) :
    CompactnessConclusion (I := I) X :=
  (flowUpgrade_of_maps (I := I) (X := X) mc L P hPlim hPL Φ R bf hsrc htgt
    β ψ hcarrier co hLmetric scalar ricciNorm).toConclusion

/-- Compatibility wrapper: `flowLimit_of_maps` at the endgame maps
`endgamePhi mc L hL0` (the time-0 comparison maps transported to `L`). -/
theorem flowLimit_of_co
    (mc : MetricCompactnessConclusion (I := I) (X.atZero (I := I)))
    (L : PointedFlowData (I := I) X.D)
    (hL0 : L.atTime (I := I) 0 = mc.limit)
    (R :
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : IsManifold I ∞ L.M := L.smooth
      SmoothRiemannianMetric I L.M)
    (bf : BumpFamily (I := I) (endgamePhi (I := I) mc L hL0))
    (hsrc : SrcSigma (I := I) (endgamePhi (I := I) mc L hL0))
    (htgt : TgtSigma (I := I) (endgamePhi (I := I) mc L hL0))
    (β ψ : Real)
    (hcarrier : X.D.carrier ⊆ Set.Icc β ψ)
    (co : ConvOut (I := I) (endgamePhi (I := I) mc L hL0) R bf hsrc htgt β ψ)
    (hLmetric :
      letI : TopologicalSpace L.M := L.topology
      letI : ChartedSpace H L.M := L.charted
      letI : T2Space L.M := L.t2
      letI : IsManifold I ∞ L.M := L.smooth
      letI : SigmaCompactSpace L.M := L.sigmaCompact
      forall t : Real, t ∈ Set.Icc β ψ -> L.S.family.metric t = co.gInf t)
    (scalar : ScalarPullbackTendsto (I := I)
      ((endgamePhi (I := I) mc L hL0).compSubseq co.φ co.hφ))
    (ricciNorm : RicNormPullback (I := I)
      ((endgamePhi (I := I) mc L hL0).compSubseq co.φ co.hφ)) :
    CompactnessConclusion (I := I) X :=
  flowLimit_of_maps (I := I) mc L (L.atTime 0) hL0 rfl (endgamePhi (I := I) mc L hL0) R bf hsrc htgt β ψ
    hcarrier co (fun t ht => heq_of_eq (hLmetric t ht)) scalar ricciNorm

/-- **The concrete P4 endgame data — MSM135 Thm 3.10 ⇐ 3.9.**
From the time-0 metric Cheeger–Gromov compactness `mc`, the limit-manifold
comparison maps `Φ₀` (built from `mc.maps` on `mc.limit`), the Arzelà–Ascoli
output `co := convOut …` (the tracked AA producer, fed by the Brick-7a
producers), the time-0 identification `hzero : co.gInf 0 = mc.limit.metric`
(discharger = `gInf_zero_eq` from `mc.convergence`), the limit Ricci-flow
certificate `hsol` (built by `isSolutionOn_of_reg` from the tracked joint
regularity `hsmooth` and the PDE/continuity producers), and the scalar-curvature
pullback convergence `scalar` (discharger = `scalarConv_of_dnConv`), produce the
concrete `FlowUpgradeData` consumed by the canonical Theorem 3.10 endpoint.

The limit flow is `L := flowOfMetric X.D mc.limit co.gInf hsol`, whose time-0
slice is `mc.limit` by `flowOfMetric_atTime` (this is `hL0`), and whose metric
family is `co.gInf` definitionally.  `flowLimit_of_maps` is instantiated at
`P := mc.limit` with the maps `Φ₀` DIRECTLY — no phantom-`L` cast, since the AA
machinery is re-indexed by `P` (2026-07-06 refactor). -/
noncomputable def flowUpgrade_of_mc
    (mc : MetricCompactnessConclusion (I := I) (X.atZero (I := I)))
    (Φ₀ : PointedCGHMaps (I := I) X mc.limit mc.subseq)
    (R :
      letI : TopologicalSpace mc.limit.M := mc.limit.topology
      letI : ChartedSpace H mc.limit.M := mc.limit.charted
      letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
      SmoothRiemannianMetric I mc.limit.M)
    (bf : BumpFamily (I := I) Φ₀)
    (hsrc : SrcSigma (I := I) Φ₀)
    (htgt : TgtSigma (I := I) Φ₀)
    (β ψ : Real)
    (hcarrier : X.D.carrier ⊆ Set.Icc β ψ)
    (co : ConvOut (I := I) Φ₀ R bf hsrc htgt β ψ)
    (hzero :
      letI : TopologicalSpace mc.limit.M := mc.limit.topology
      letI : ChartedSpace H mc.limit.M := mc.limit.charted
      letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
      co.gInf 0 = mc.limit.metric)
    (hsol :
      letI : TopologicalSpace mc.limit.M := mc.limit.topology
      letI : ChartedSpace H mc.limit.M := mc.limit.charted
      letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
      letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact
      letI : T2Space mc.limit.M := mc.limit.t2
      letI : IsManifold I 1 mc.limit.M :=
        IsManifold.of_le (I := I) (M := mc.limit.M) (n := ∞)
          (by decide : (1 : WithTop ℕ∞) ≤ ∞)
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) mc.limit.M := by
        change IsManifold I ∞ mc.limit.M
        infer_instance
      DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I)
        ({ base := { metric := co.gInf } } :
          DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := mc.limit.M) X.D))
    (scalar : ScalarPullbackTendsto (I := I)
      ((flowOfMetric_atTime (I := I) X.D mc.limit co.gInf hsol 0 hzero).symm ▸
        (Φ₀.compSubseq co.φ co.hφ) :
        PointedCGHMaps (I := I) X
          ((flowOfMetric (I := I) X.D mc.limit co.gInf hsol).atTime 0)
          (mc.subseq ∘ co.φ)))
    (ricciNorm : RicNormPullback (I := I)
      ((flowOfMetric_atTime (I := I) X.D mc.limit co.gInf hsol 0 hzero).symm ▸
        (Φ₀.compSubseq co.φ co.hφ) :
        PointedCGHMaps (I := I) X
          ((flowOfMetric (I := I) X.D mc.limit co.gInf hsol).atTime 0)
          (mc.subseq ∘ co.φ))) :
    FlowUpgradeData (I := I) X mc := by
  have hL0 :
      (flowOfMetric (I := I) X.D mc.limit co.gInf hsol).atTime (I := I) 0 = mc.limit :=
    flowOfMetric_atTime (I := I) X.D mc.limit co.gInf hsol 0 hzero
  exact flowUpgrade_of_maps (I := I) mc
    (flowOfMetric (I := I) X.D mc.limit co.gInf hsol) mc.limit rfl hL0 Φ₀
    R bf hsrc htgt β ψ hcarrier co (fun t _ => HEq.rfl) scalar ricciNorm

/-- **The P4 endgame theorem — MSM135 Theorem 3.10 from Theorem 3.9.**
Assemble the smooth CGH compactness conclusion from `flowUpgrade_of_mc`. -/
theorem flowLimit_of_mc
    (mc : MetricCompactnessConclusion (I := I) (X.atZero (I := I)))
    (Φ₀ : PointedCGHMaps (I := I) X mc.limit mc.subseq)
    (R :
      letI : TopologicalSpace mc.limit.M := mc.limit.topology
      letI : ChartedSpace H mc.limit.M := mc.limit.charted
      letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
      SmoothRiemannianMetric I mc.limit.M)
    (bf : BumpFamily (I := I) Φ₀)
    (hsrc : SrcSigma (I := I) Φ₀)
    (htgt : TgtSigma (I := I) Φ₀)
    (β ψ : Real)
    (hcarrier : X.D.carrier ⊆ Set.Icc β ψ)
    (co : ConvOut (I := I) Φ₀ R bf hsrc htgt β ψ)
    (hzero :
      letI : TopologicalSpace mc.limit.M := mc.limit.topology
      letI : ChartedSpace H mc.limit.M := mc.limit.charted
      letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
      co.gInf 0 = mc.limit.metric)
    (hsol :
      letI : TopologicalSpace mc.limit.M := mc.limit.topology
      letI : ChartedSpace H mc.limit.M := mc.limit.charted
      letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
      letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact
      letI : T2Space mc.limit.M := mc.limit.t2
      letI : IsManifold I 1 mc.limit.M :=
        IsManifold.of_le (I := I) (M := mc.limit.M) (n := ∞)
          (by decide : (1 : WithTop ℕ∞) ≤ ∞)
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) mc.limit.M := by
        change IsManifold I ∞ mc.limit.M
        infer_instance
      DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I)
        ({ base := { metric := co.gInf } } :
          DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := mc.limit.M) X.D))
    (scalar : ScalarPullbackTendsto (I := I)
      ((flowOfMetric_atTime (I := I) X.D mc.limit co.gInf hsol 0 hzero).symm ▸
        (Φ₀.compSubseq co.φ co.hφ) :
        PointedCGHMaps (I := I) X
          ((flowOfMetric (I := I) X.D mc.limit co.gInf hsol).atTime 0)
          (mc.subseq ∘ co.φ)))
    (ricciNorm : RicNormPullback (I := I)
      ((flowOfMetric_atTime (I := I) X.D mc.limit co.gInf hsol 0 hzero).symm ▸
        (Φ₀.compSubseq co.φ co.hφ) :
        PointedCGHMaps (I := I) X
          ((flowOfMetric (I := I) X.D mc.limit co.gInf hsol).atTime 0)
          (mc.subseq ∘ co.φ))) :
    CompactnessConclusion (I := I) X :=
  (flowUpgrade_of_mc (I := I) (X := X) mc Φ₀ R bf hsrc htgt β ψ
    hcarrier co hzero hsol scalar ricciNorm).toConclusion

/-- **P4 endgame wiring, steps 1–3: the AA output from the book-cited
sequence-flow inputs.**  Executes the four Brick-7a producers
(`hbound_of_equiv`/`covTail_of_bounds`/`lipTail_of_src`/`lipSrc_of_soln`,
`ConvFieldInputs.lean`) into `convOut` with `cLow := (Crel·Bmax)⁻¹`.  Since this
is a `def`, `(endgameCo …).gInf` is a term the tracked regularity inputs
(`hsmooth`, the four continuity fields) and the endgame theorem are stated
against (ruling 5a). -/
noncomputable def endgameCo
    {P : PointedRiemannianManifold (I := I)} {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (R : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    (β ψ : Real) (hβψ : β <= ψ) (hwin : Set.Icc β ψ ⊆ X.D.regular)
    (gRefT : forall k : Nat,
      letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
      letI : IsManifold I ∞ (X.term (subseq k)).M := (X.term (subseq k)).smooth
      SmoothRiemannianMetric I ((X.term (subseq k)).M))
    (B : Real -> Real) (Crel Bmax : Real)
    (hBmax : forall t : Real, t ∈ Set.Icc β ψ -> B t <= Bmax)
    (hCrel1 : 1 <= Crel) (hBmax1 : 1 <= Bmax)
    (hequivT : forall k : Nat,
      letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
      letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
      letI : IsManifold I ∞ (X.term (subseq k)).M := (X.term (subseq k)).smooth
      letI : SigmaCompactSpace (X.term (subseq k)).M := (X.term (subseq k)).sigmaCompact
      MetricUniformEquivalentOnWindow (I := I) (Φ.target k) β ψ (gRefT k)
        (fun _ t => (X.term (subseq k)).S.family.metric t) B)
    (hrel : forall k : Nat,
      letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
      letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
      MetricUniformEquivalentOn (I := I)
        (Set.univ : Set (SourceDomain (I := I) Φ k))
        (refRes (I := I) Φ R hsrc k)
        (tgtRefSrc (I := I) Φ gRefT hsrc htgt k) Crel)
    (hShiT : forall N : Nat, exists KShi : Real, 0 <= KShi /\
      forall k : Nat,
        letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
        letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
        letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
        letI : IsManifold I ∞ (X.term (subseq k)).M := (X.term (subseq k)).smooth
        letI : SigmaCompactSpace (X.term (subseq k)).M := (X.term (subseq k)).sigmaCompact
        MovingShiBoundOn (I := I) (Φ.target k) β ψ
          (fun _ t => (X.term (subseq k)).S.family.metric t) N KShi)
    (hcovSrc : letI : TopologicalSpace P.M := P.topology;
        letI : ChartedSpace H P.M := P.charted; letI : T2Space P.M := P.t2;
        letI : IsManifold I ∞ P.M := P.smooth; letI : SigmaCompactSpace P.M := P.sigmaCompact;
      forall j : Nat, exists Cs : Real, 0 <= Cs /\
        forall (k : Nat) (t : Real), t ∈ Set.Icc β ψ ->
          forall y : SourceDomain (I := I) Φ k, (y : P.M) ∈ bf.grow k ->
            letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
            letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
            letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
            letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
              sourceDomSigmaOf (I := I) Φ k (hsrc k)
            metricCovDerivNorm (I := I) j (srcMetric (I := I) Φ hsrc htgt k t)
              (refRes (I := I) Φ R hsrc k) y <= Cs)
    (hlipG : letI : TopologicalSpace P.M := P.topology;
        letI : ChartedSpace H P.M := P.charted; letI : T2Space P.M := P.t2;
        letI : IsManifold I ∞ P.M := P.smooth; letI : SigmaCompactSpace P.M := P.sigmaCompact;
      forall p : Nat, exists Lt : Real, 0 <= Lt /\
        forall (k : Nat) (s t : Real), s ∈ Set.Icc β ψ -> t ∈ Set.Icc β ψ ->
          forall a : Nat, a <= p ->
            forall y : SourceDomain (I := I) Φ k, (y : P.M) ∈ bf.grow k ->
              letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
              letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
              letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
              letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
              letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
                sourceDomSigmaOf (I := I) Φ k (hsrc k)
              metricDerivNorm (I := I) a (srcMetric (I := I) Φ hsrc htgt k s)
                (srcMetric (I := I) Φ hsrc htgt k t)
                (refRes (I := I) Φ R hsrc k) y <= Lt * |s - t|) :
    ConvOut (I := I) Φ R bf hsrc htgt β ψ :=
  convOut (I := I) (Φ := Φ) R bf hsrc htgt β ψ hβψ ((Crel * Bmax)⁻¹)
    (inv_pos.2 (mul_pos (lt_of_lt_of_le one_pos hCrel1) (lt_of_lt_of_le one_pos hBmax1)))
    (hbound_of_equiv (I := I) (Φ := Φ) R hsrc htgt β ψ gRefT B Crel Bmax hBmax hCrel1 hequivT hrel)
    (covTail_of_bounds (I := I) (Φ := Φ) R bf hsrc htgt β ψ hcovSrc)
    (lipTail_of_src (I := I) (Φ := Φ) R bf hsrc htgt β ψ hlipG)
    (lipSrc_of_soln (I := I) (Φ := Φ) R hsrc htgt β ψ hβψ hwin gRefT B Crel Bmax hBmax hCrel1
      hBmax1 hequivT hrel hShiT)

/-- **P4 endgame wiring, step 4: the time-0 identification.**  `(endgameCo …).gInf 0`
is the time-0 CG limit metric `g0`, via `gInf_zero_eq` fed by `conv0_of_cp` from the
`MetricSourceCPConvOn`-shaped time-0 input `hcp` (discharger = `mc.convergence`). -/
theorem endgameCo_zero
    {P : PointedRiemannianManifold (I := I)} {subseq : Nat -> Nat}
    (Φ : PointedCGHMaps (I := I) X P subseq)
    (R : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SrcSigma Φ) (htgt : TgtSigma Φ)
    (β ψ : Real) (hβψ : β <= ψ) (hwin : Set.Icc β ψ ⊆ X.D.regular)
    (gRefT : forall k : Nat,
      letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
      letI : IsManifold I ∞ (X.term (subseq k)).M := (X.term (subseq k)).smooth
      SmoothRiemannianMetric I ((X.term (subseq k)).M))
    (B : Real -> Real) (Crel Bmax : Real)
    (hBmax : forall t : Real, t ∈ Set.Icc β ψ -> B t <= Bmax)
    (hCrel1 : 1 <= Crel) (hBmax1 : 1 <= Bmax)
    (hequivT : forall k : Nat,
      letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
      letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
      letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
      letI : IsManifold I ∞ (X.term (subseq k)).M := (X.term (subseq k)).smooth
      letI : SigmaCompactSpace (X.term (subseq k)).M := (X.term (subseq k)).sigmaCompact
      MetricUniformEquivalentOnWindow (I := I) (Φ.target k) β ψ (gRefT k)
        (fun _ t => (X.term (subseq k)).S.family.metric t) B)
    (hrel : forall k : Nat,
      letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
      letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
      MetricUniformEquivalentOn (I := I)
        (Set.univ : Set (SourceDomain (I := I) Φ k))
        (refRes (I := I) Φ R hsrc k)
        (tgtRefSrc (I := I) Φ gRefT hsrc htgt k) Crel)
    (hShiT : forall N : Nat, exists KShi : Real, 0 <= KShi /\
      forall k : Nat,
        letI : TopologicalSpace (X.term (subseq k)).M := (X.term (subseq k)).topology
        letI : ChartedSpace H (X.term (subseq k)).M := (X.term (subseq k)).charted
        letI : T2Space (X.term (subseq k)).M := (X.term (subseq k)).t2
        letI : IsManifold I ∞ (X.term (subseq k)).M := (X.term (subseq k)).smooth
        letI : SigmaCompactSpace (X.term (subseq k)).M := (X.term (subseq k)).sigmaCompact
        MovingShiBoundOn (I := I) (Φ.target k) β ψ
          (fun _ t => (X.term (subseq k)).S.family.metric t) N KShi)
    (hcovSrc : letI : TopologicalSpace P.M := P.topology;
        letI : ChartedSpace H P.M := P.charted; letI : T2Space P.M := P.t2;
        letI : IsManifold I ∞ P.M := P.smooth; letI : SigmaCompactSpace P.M := P.sigmaCompact;
      forall j : Nat, exists Cs : Real, 0 <= Cs /\
        forall (k : Nat) (t : Real), t ∈ Set.Icc β ψ ->
          forall y : SourceDomain (I := I) Φ k, (y : P.M) ∈ bf.grow k ->
            letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
            letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
            letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
            letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
              sourceDomSigmaOf (I := I) Φ k (hsrc k)
            metricCovDerivNorm (I := I) j (srcMetric (I := I) Φ hsrc htgt k t)
              (refRes (I := I) Φ R hsrc k) y <= Cs)
    (hlipG : letI : TopologicalSpace P.M := P.topology;
        letI : ChartedSpace H P.M := P.charted; letI : T2Space P.M := P.t2;
        letI : IsManifold I ∞ P.M := P.smooth; letI : SigmaCompactSpace P.M := P.sigmaCompact;
      forall p : Nat, exists Lt : Real, 0 <= Lt /\
        forall (k : Nat) (s t : Real), s ∈ Set.Icc β ψ -> t ∈ Set.Icc β ψ ->
          forall a : Nat, a <= p ->
            forall y : SourceDomain (I := I) Φ k, (y : P.M) ∈ bf.grow k ->
              letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
              letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
              letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
              letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
              letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
                sourceDomSigmaOf (I := I) Φ k (hsrc k)
              metricDerivNorm (I := I) a (srcMetric (I := I) Φ hsrc htgt k s)
                (srcMetric (I := I) Φ hsrc htgt k t)
                (refRes (I := I) Φ R hsrc k) y <= Lt * |s - t|)
    (g0 : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (h0 : (0 : Real) ∈ Set.Icc β ψ)
    (hcp : letI : TopologicalSpace P.M := P.topology;
        letI : ChartedSpace H P.M := P.charted; letI : T2Space P.M := P.t2;
        letI : IsManifold I ∞ P.M := P.smooth; letI : SigmaCompactSpace P.M := P.sigmaCompact;
      forall K : Set P.M, IsCompact K -> forall ε : Real, 0 < ε ->
        exists k0 : Nat, forall k : Nat, k0 <= k -> K ⊆ Φ.source k ∧
          (letI : TopologicalSpace (SourceDomain (I := I) Φ k) := sourceDomTop (I := I) Φ k
           letI : ChartedSpace H (SourceDomain (I := I) Φ k) := sourceDomCharted (I := I) Φ k
           letI : T2Space (SourceDomain (I := I) Φ k) := sourceDomT2 (I := I) Φ k
           letI : IsManifold I ∞ (SourceDomain (I := I) Φ k) := sourceDomSmooth (I := I) Φ k
           letI : SigmaCompactSpace (SourceDomain (I := I) Φ k) :=
             sourceDomSigmaOf (I := I) Φ k (hsrc k)
           metricDerivNormSupOn (I := I) (sourceCompactSet (I := I) Φ k K) 0
             (srcMetric (I := I) Φ hsrc htgt k 0)
             (resSrc (I := I) Φ hsrc k g0)
             (refRes (I := I) Φ R hsrc k) < ε)) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    (endgameCo Φ R bf hsrc htgt β ψ hβψ hwin gRefT B Crel Bmax hBmax hCrel1 hBmax1 hequivT hrel hShiT hcovSrc hlipG).gInf 0 = g0 :=
  gInf_zero_eq (I := I) Φ R bf hsrc htgt β ψ
    (endgameCo Φ R bf hsrc htgt β ψ hβψ hwin gRefT B Crel Bmax hBmax hCrel1 hBmax1 hequivT hrel hShiT hcovSrc hlipG) h0 g0
    (conv0_of_cp (I := I) Φ R hsrc htgt g0 hcp)

/-- **The book-facing P4 endgame theorem — MSM135 Thm 3.10 ⇐ 3.9.**  Hypotheses:
`mc` (Thm 3.9); the book-cited sequence-flow inputs (`hequivT`/`hrel`/`hShiT`/`hcovSrc`/
`hlipG` + the reference/window data + the time-0 `hcp`); and the tracked
limit-regularity/scalar inputs `hsol`/`scalar` (stated against the `endgameCo` def per
ruling 5a).  `Φ₀ = pointedCGHMaps_of_manifold X mc.limit mc.subseq mc.maps`; `bf`/`hsrc`/
`htgt` are `nonempty_bumpFamily`/`isSigmaCompact_of_isOpen`.  The AA output and time-0
identification are executed by `endgameCo`/`endgameCo_zero`; the conclusion is `flowLimit_of_mc`. -/
theorem flowLimit_endgame
    (mc : MetricCompactnessConclusion (I := I) (X.atZero (I := I)))
    (Φ₀ : PointedCGHMaps (I := I) X mc.limit mc.subseq)
    (R : letI : TopologicalSpace mc.limit.M := mc.limit.topology;
      letI : ChartedSpace H mc.limit.M := mc.limit.charted; letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth;
      SmoothRiemannianMetric I mc.limit.M)
    (bf : BumpFamily (I := I) Φ₀) (hsrc : SrcSigma Φ₀) (htgt : TgtSigma Φ₀)
    (β ψ : Real) (hβψ : β <= ψ) (hwin : Set.Icc β ψ ⊆ X.D.regular)
    (gRefT : forall k : Nat,
      letI : TopologicalSpace (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).topology
      letI : ChartedSpace H (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).charted
      letI : IsManifold I ∞ (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).smooth
      SmoothRiemannianMetric I ((X.term (mc.subseq k)).M))
    (B : Real -> Real) (Crel Bmax : Real)
    (hBmax : forall t : Real, t ∈ Set.Icc β ψ -> B t <= Bmax)
    (hCrel1 : 1 <= Crel) (hBmax1 : 1 <= Bmax)
    (hequivT : forall k : Nat,
      letI : TopologicalSpace (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).topology
      letI : ChartedSpace H (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).charted
      letI : T2Space (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).t2
      letI : IsManifold I ∞ (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).smooth
      letI : SigmaCompactSpace (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).sigmaCompact
      MetricUniformEquivalentOnWindow (I := I) (Φ₀.target k) β ψ (gRefT k)
        (fun _ t => (X.term (mc.subseq k)).S.family.metric t) B)
    (hrel : forall k : Nat,
      letI : TopologicalSpace (SourceDomain (I := I) Φ₀ k) := sourceDomTop (I := I) Φ₀ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ₀ k) := sourceDomCharted (I := I) Φ₀ k
      letI : T2Space (SourceDomain (I := I) Φ₀ k) := sourceDomT2 (I := I) Φ₀ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ₀ k) := sourceDomSmooth (I := I) Φ₀ k
      MetricUniformEquivalentOn (I := I)
        (Set.univ : Set (SourceDomain (I := I) Φ₀ k))
        (refRes (I := I) Φ₀ R hsrc k)
        (tgtRefSrc (I := I) Φ₀ gRefT hsrc htgt k) Crel)
    (hShiT : forall N : Nat, exists KShi : Real, 0 <= KShi /\
      forall k : Nat,
        letI : TopologicalSpace (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).topology
        letI : ChartedSpace H (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).charted
        letI : T2Space (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).t2
        letI : IsManifold I ∞ (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).smooth
        letI : SigmaCompactSpace (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).sigmaCompact
        MovingShiBoundOn (I := I) (Φ₀.target k) β ψ
          (fun _ t => (X.term (mc.subseq k)).S.family.metric t) N KShi)
    (hcovSrc : letI : TopologicalSpace mc.limit.M := mc.limit.topology;
        letI : ChartedSpace H mc.limit.M := mc.limit.charted; letI : T2Space mc.limit.M := mc.limit.t2;
        letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth; letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact;
      forall j : Nat, exists Cs : Real, 0 <= Cs /\
        forall (k : Nat) (t : Real), t ∈ Set.Icc β ψ ->
          forall y : SourceDomain (I := I) Φ₀ k, (y : mc.limit.M) ∈ bf.grow k ->
            letI : TopologicalSpace (SourceDomain (I := I) Φ₀ k) := sourceDomTop (I := I) Φ₀ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ₀ k) := sourceDomCharted (I := I) Φ₀ k
            letI : T2Space (SourceDomain (I := I) Φ₀ k) := sourceDomT2 (I := I) Φ₀ k
            letI : IsManifold I ∞ (SourceDomain (I := I) Φ₀ k) := sourceDomSmooth (I := I) Φ₀ k
            letI : SigmaCompactSpace (SourceDomain (I := I) Φ₀ k) :=
              sourceDomSigmaOf (I := I) Φ₀ k (hsrc k)
            metricCovDerivNorm (I := I) j (srcMetric (I := I) Φ₀ hsrc htgt k t)
              (refRes (I := I) Φ₀ R hsrc k) y <= Cs)
    (hlipG : letI : TopologicalSpace mc.limit.M := mc.limit.topology;
        letI : ChartedSpace H mc.limit.M := mc.limit.charted; letI : T2Space mc.limit.M := mc.limit.t2;
        letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth; letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact;
      forall p : Nat, exists Lt : Real, 0 <= Lt /\
        forall (k : Nat) (s t : Real), s ∈ Set.Icc β ψ -> t ∈ Set.Icc β ψ ->
          forall a : Nat, a <= p ->
            forall y : SourceDomain (I := I) Φ₀ k, (y : mc.limit.M) ∈ bf.grow k ->
              letI : TopologicalSpace (SourceDomain (I := I) Φ₀ k) := sourceDomTop (I := I) Φ₀ k
              letI : ChartedSpace H (SourceDomain (I := I) Φ₀ k) := sourceDomCharted (I := I) Φ₀ k
              letI : T2Space (SourceDomain (I := I) Φ₀ k) := sourceDomT2 (I := I) Φ₀ k
              letI : IsManifold I ∞ (SourceDomain (I := I) Φ₀ k) := sourceDomSmooth (I := I) Φ₀ k
              letI : SigmaCompactSpace (SourceDomain (I := I) Φ₀ k) :=
                sourceDomSigmaOf (I := I) Φ₀ k (hsrc k)
              metricDerivNorm (I := I) a (srcMetric (I := I) Φ₀ hsrc htgt k s)
                (srcMetric (I := I) Φ₀ hsrc htgt k t)
                (refRes (I := I) Φ₀ R hsrc k) y <= Lt * |s - t|)
    (hcarrier : X.D.carrier ⊆ Set.Icc β ψ)
    (h0 : (0 : Real) ∈ Set.Icc β ψ)
    (hcp : letI : TopologicalSpace mc.limit.M := mc.limit.topology;
        letI : ChartedSpace H mc.limit.M := mc.limit.charted; letI : T2Space mc.limit.M := mc.limit.t2;
        letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth;
        letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact;
      forall K : Set mc.limit.M, IsCompact K -> forall ε : Real, 0 < ε ->
        exists k0 : Nat, forall k : Nat, k0 <= k -> K ⊆ Φ₀.source k ∧
          (letI : TopologicalSpace (SourceDomain (I := I) Φ₀ k) := sourceDomTop (I := I) Φ₀ k
           letI : ChartedSpace H (SourceDomain (I := I) Φ₀ k) := sourceDomCharted (I := I) Φ₀ k
           letI : T2Space (SourceDomain (I := I) Φ₀ k) := sourceDomT2 (I := I) Φ₀ k
           letI : IsManifold I ∞ (SourceDomain (I := I) Φ₀ k) := sourceDomSmooth (I := I) Φ₀ k
           letI : SigmaCompactSpace (SourceDomain (I := I) Φ₀ k) :=
             sourceDomSigmaOf (I := I) Φ₀ k (hsrc k)
           metricDerivNormSupOn (I := I) (sourceCompactSet (I := I) Φ₀ k K) 0
             (srcMetric (I := I) Φ₀ hsrc htgt k 0)
             (resSrc (I := I) Φ₀ hsrc k mc.limit.metric)
             (refRes (I := I) Φ₀ R hsrc k) < ε))
    (hsol :
      letI : TopologicalSpace mc.limit.M := mc.limit.topology
      letI : ChartedSpace H mc.limit.M := mc.limit.charted
      letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
      letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact
      letI : T2Space mc.limit.M := mc.limit.t2
      letI : IsManifold I 1 mc.limit.M :=
        IsManifold.of_le (I := I) (M := mc.limit.M) (n := ∞)
          (by decide : (1 : WithTop ℕ∞) ≤ ∞)
      letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) mc.limit.M := by
        change IsManifold I ∞ mc.limit.M
        infer_instance
      DifferentialGeometry.PDE.RicciFlow.IsSolutionOn (I := I)
        ({ base := { metric := (endgameCo Φ₀ R bf hsrc htgt β ψ hβψ hwin gRefT B Crel Bmax hBmax hCrel1 hBmax1 hequivT hrel hShiT hcovSrc hlipG).gInf } } :
          DifferentialGeometry.PDE.RicciFlow.SolutionOn (I := I) (M := mc.limit.M) X.D))
    (scalar : ScalarPullbackTendsto (I := I)
      ((flowOfMetric_atTime (I := I) X.D mc.limit (endgameCo Φ₀ R bf hsrc htgt β ψ hβψ hwin gRefT B Crel Bmax hBmax hCrel1 hBmax1 hequivT hrel hShiT hcovSrc hlipG).gInf hsol 0
          (endgameCo_zero Φ₀ R bf hsrc htgt β ψ hβψ hwin gRefT B Crel Bmax hBmax hCrel1 hBmax1
            hequivT hrel hShiT hcovSrc hlipG mc.limit.metric h0 hcp)).symm ▸
        (Φ₀.compSubseq (endgameCo Φ₀ R bf hsrc htgt β ψ hβψ hwin gRefT B Crel Bmax hBmax hCrel1 hBmax1 hequivT hrel hShiT hcovSrc hlipG).φ (endgameCo Φ₀ R bf hsrc htgt β ψ hβψ hwin gRefT B Crel Bmax hBmax hCrel1 hBmax1 hequivT hrel hShiT hcovSrc hlipG).hφ) :
        PointedCGHMaps (I := I) X
          ((flowOfMetric (I := I) X.D mc.limit (endgameCo Φ₀ R bf hsrc htgt β ψ hβψ hwin gRefT B Crel Bmax hBmax hCrel1 hBmax1 hequivT hrel hShiT hcovSrc hlipG).gInf hsol).atTime 0)
          (mc.subseq ∘ (endgameCo Φ₀ R bf hsrc htgt β ψ hβψ hwin gRefT B Crel Bmax hBmax hCrel1 hBmax1 hequivT hrel hShiT hcovSrc hlipG).φ))) :
    CompactnessConclusion (I := I) X := by
  letI : TopologicalSpace mc.limit.M := mc.limit.topology
  letI : ChartedSpace H mc.limit.M := mc.limit.charted
  letI : T2Space mc.limit.M := mc.limit.t2
  letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
  letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact
  letI : IsManifold I 1 mc.limit.M :=
    IsManifold.of_le (I := I) (M := mc.limit.M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) mc.limit.M := by
    change IsManifold I ∞ mc.limit.M
    infer_instance
  let co := endgameCo Φ₀ R bf hsrc htgt β ψ hβψ hwin gRefT B Crel Bmax hBmax
    hCrel1 hBmax1 hequivT hrel hShiT hcovSrc hlipG
  have hzero : co.gInf 0 = mc.limit.metric :=
    endgameCo_zero Φ₀ R bf hsrc htgt β ψ hβψ hwin gRefT B Crel Bmax hBmax
      hCrel1 hBmax1 hequivT hrel hShiT hcovSrc hlipG mc.limit.metric h0 hcp
  have hL0 :
      (flowOfMetric (I := I) X.D mc.limit co.gInf hsol).atTime 0 = mc.limit :=
    flowOfMetric_atTime (I := I) X.D mc.limit co.gInf hsol 0 hzero
  have hricRaw := ConvOut.ricNorm_conv (I := I) (Φ := Φ₀) R bf hsrc htgt β ψ
    ((Crel * Bmax)⁻¹)
    (inv_pos.2 (mul_pos (lt_of_lt_of_le one_pos hCrel1)
      (lt_of_lt_of_le one_pos hBmax1)))
    (hbound_of_equiv (I := I) (Φ := Φ₀) R hsrc htgt β ψ gRefT B Crel Bmax
      hBmax hCrel1 hequivT hrel)
    (covTail_of_bounds (I := I) (Φ := Φ₀) R bf hsrc htgt β ψ hcovSrc)
    co hcarrier
  have map_cast {P Q : PointedRiemannianManifold (I := I)}
      {s : Nat → Nat} (h : P = Q) (maps : PointedCGHMaps (I := I) X Q s)
      (k : Nat) (x : P.M) :
      HEq ((h.symm ▸ maps : PointedCGHMaps (I := I) X P s).map k x)
        (maps.map k (h ▸ x)) := by
    cases h
    rfl
  have hmap (k : Nat) (x : mc.limit.M) :
      (hL0.symm ▸ (Φ₀.compSubseq co.φ co.hφ) : PointedCGHMaps (I := I) X
        ((flowOfMetric (I := I) X.D mc.limit co.gInf hsol).atTime 0)
        (mc.subseq ∘ co.φ)).map k x =
        (Φ₀.compSubseq co.φ co.hφ).map k x := by
    have hx : hL0 ▸ x = x :=
      eq_of_heq ((eqRec_heq
        (φ := fun P : PointedRiemannianManifold (I := I) => P.M) hL0) x)
    exact (eq_of_heq (map_cast hL0 (Φ₀.compSubseq co.φ co.hφ) k x)).trans
      (congrArg (fun y => (Φ₀.compSubseq co.φ co.hφ).map k y) hx)
  have ricciNorm : RicNormPullback (I := I)
      (hL0.symm ▸ (Φ₀.compSubseq co.φ co.hφ) : PointedCGHMaps (I := I) X
        ((flowOfMetric (I := I) X.D mc.limit co.gInf hsol).atTime 0)
        (mc.subseq ∘ co.φ)) := by
    unfold RicNormPullback FunctionPullbackTendsto
    intro t ht x
    change mc.limit.M at x
    change Filter.Tendsto _ Filter.atTop
      (nhds (normSq0S (I := I) (co.gInf t) x 2
        (metricRicci (I := I) (co.gInf t) x)))
    refine Filter.Tendsto.congr' (Filter.Eventually.of_forall (fun k => ?_))
      (hricRaw t ht x)
    letI : TopologicalSpace (X.term ((mc.subseq ∘ co.φ) k)).M :=
      (X.term ((mc.subseq ∘ co.φ) k)).topology
    letI : ChartedSpace H (X.term ((mc.subseq ∘ co.φ) k)).M :=
      (X.term ((mc.subseq ∘ co.φ) k)).charted
    letI : IsManifold I ∞ (X.term ((mc.subseq ∘ co.φ) k)).M :=
      (X.term ((mc.subseq ∘ co.φ) k)).smooth
    letI : SigmaCompactSpace (X.term ((mc.subseq ∘ co.φ) k)).M :=
      (X.term ((mc.subseq ∘ co.φ) k)).sigmaCompact
    letI : T2Space (X.term ((mc.subseq ∘ co.φ) k)).M :=
      (X.term ((mc.subseq ∘ co.φ) k)).t2
    letI : IsManifold I 1 (X.term ((mc.subseq ∘ co.φ) k)).M :=
      IsManifold.of_le (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1)
        (X.term ((mc.subseq ∘ co.φ) k)).M := by
      change IsManifold I ∞ (X.term ((mc.subseq ∘ co.φ) k)).M
      infer_instance
    exact congrArg
      (fun y => DifferentialGeometry.PDE.RicciFlow.ricciNorm (I := I)
        (X.term ((mc.subseq ∘ co.φ) k)).S t y) (hmap k x).symm
  exact flowLimit_of_mc (I := I) mc Φ₀ R bf hsrc htgt β ψ hcarrier co hzero
    hsol scalar ricciNorm

/-- Compatibility refinement of `flowLimit_endgame` with the limit-flow equation
produced internally.  It replaces the whole `IsSolutionOn` input by the five
regularity and curvature-continuity inputs of
`PDE.RicciFlow.isSolutionOn_of_reg`; the metric Ricci-flow equation is supplied
by `ConvOut.gInf_pde`, and scalar pullback convergence by
`ConvOut.scalar_conv`.  It deliberately preserves the older endgame's closed
window assumptions and is not the unconditional P4 endpoint. -/
theorem flowLimit_of_reg
    (mc : MetricCompactnessConclusion (I := I) (X.atZero (I := I)))
    (Φ₀ : PointedCGHMaps (I := I) X mc.limit mc.subseq)
    (R : letI : TopologicalSpace mc.limit.M := mc.limit.topology;
      letI : ChartedSpace H mc.limit.M := mc.limit.charted;
      letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth;
      SmoothRiemannianMetric I mc.limit.M)
    (bf : BumpFamily (I := I) Φ₀) (hsrc : SrcSigma Φ₀) (htgt : TgtSigma Φ₀)
    (β ψ : Real) (hβψ : β ≤ ψ) (hwin : Set.Icc β ψ ⊆ X.D.regular)
    (gRefT : ∀ k : Nat,
      letI : TopologicalSpace (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).topology
      letI : ChartedSpace H (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).charted
      letI : IsManifold I ∞ (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).smooth
      SmoothRiemannianMetric I ((X.term (mc.subseq k)).M))
    (B : Real → Real) (Crel Bmax : Real)
    (hBmax : ∀ t : Real, t ∈ Set.Icc β ψ → B t ≤ Bmax)
    (hCrel1 : 1 ≤ Crel) (hBmax1 : 1 ≤ Bmax)
    (hequivT : ∀ k : Nat,
      letI : TopologicalSpace (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).topology
      letI : ChartedSpace H (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).charted
      letI : T2Space (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).t2
      letI : IsManifold I ∞ (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).smooth
      letI : SigmaCompactSpace (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).sigmaCompact
      MetricUniformEquivalentOnWindow (I := I) (Φ₀.target k) β ψ (gRefT k)
        (fun _ t ↦ (X.term (mc.subseq k)).S.family.metric t) B)
    (hrel : ∀ k : Nat,
      letI : TopologicalSpace (SourceDomain (I := I) Φ₀ k) := sourceDomTop (I := I) Φ₀ k
      letI : ChartedSpace H (SourceDomain (I := I) Φ₀ k) := sourceDomCharted (I := I) Φ₀ k
      letI : T2Space (SourceDomain (I := I) Φ₀ k) := sourceDomT2 (I := I) Φ₀ k
      letI : IsManifold I ∞ (SourceDomain (I := I) Φ₀ k) := sourceDomSmooth (I := I) Φ₀ k
      MetricUniformEquivalentOn (I := I)
        (Set.univ : Set (SourceDomain (I := I) Φ₀ k))
        (refRes (I := I) Φ₀ R hsrc k)
        (tgtRefSrc (I := I) Φ₀ gRefT hsrc htgt k) Crel)
    (hShiT : ∀ N : Nat, ∃ KShi : Real, 0 ≤ KShi ∧
      ∀ k : Nat,
        letI : TopologicalSpace (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).topology
        letI : ChartedSpace H (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).charted
        letI : T2Space (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).t2
        letI : IsManifold I ∞ (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).smooth
        letI : SigmaCompactSpace (X.term (mc.subseq k)).M := (X.term (mc.subseq k)).sigmaCompact
        MovingShiBoundOn (I := I) (Φ₀.target k) β ψ
          (fun _ t ↦ (X.term (mc.subseq k)).S.family.metric t) N KShi)
    (hcovSrc : letI : TopologicalSpace mc.limit.M := mc.limit.topology;
        letI : ChartedSpace H mc.limit.M := mc.limit.charted;
        letI : T2Space mc.limit.M := mc.limit.t2;
        letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth;
        letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact;
      ∀ j : Nat, ∃ Cs : Real, 0 ≤ Cs ∧
        ∀ (k : Nat) (t : Real), t ∈ Set.Icc β ψ →
          ∀ y : SourceDomain (I := I) Φ₀ k, (y : mc.limit.M) ∈ bf.grow k →
            letI : TopologicalSpace (SourceDomain (I := I) Φ₀ k) := sourceDomTop (I := I) Φ₀ k
            letI : ChartedSpace H (SourceDomain (I := I) Φ₀ k) := sourceDomCharted (I := I) Φ₀ k
            letI : T2Space (SourceDomain (I := I) Φ₀ k) := sourceDomT2 (I := I) Φ₀ k
            letI : IsManifold I ∞ (SourceDomain (I := I) Φ₀ k) := sourceDomSmooth (I := I) Φ₀ k
            letI : SigmaCompactSpace (SourceDomain (I := I) Φ₀ k) :=
              sourceDomSigmaOf (I := I) Φ₀ k (hsrc k)
            metricCovDerivNorm (I := I) j (srcMetric (I := I) Φ₀ hsrc htgt k t)
              (refRes (I := I) Φ₀ R hsrc k) y ≤ Cs)
    (hlipG : letI : TopologicalSpace mc.limit.M := mc.limit.topology;
        letI : ChartedSpace H mc.limit.M := mc.limit.charted;
        letI : T2Space mc.limit.M := mc.limit.t2;
        letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth;
        letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact;
      ∀ p : Nat, ∃ Lt : Real, 0 ≤ Lt ∧
        ∀ (k : Nat) (s t : Real), s ∈ Set.Icc β ψ → t ∈ Set.Icc β ψ →
          ∀ a : Nat, a ≤ p →
            ∀ y : SourceDomain (I := I) Φ₀ k, (y : mc.limit.M) ∈ bf.grow k →
              letI : TopologicalSpace (SourceDomain (I := I) Φ₀ k) := sourceDomTop (I := I) Φ₀ k
              letI : ChartedSpace H (SourceDomain (I := I) Φ₀ k) := sourceDomCharted (I := I) Φ₀ k
              letI : T2Space (SourceDomain (I := I) Φ₀ k) := sourceDomT2 (I := I) Φ₀ k
              letI : IsManifold I ∞ (SourceDomain (I := I) Φ₀ k) := sourceDomSmooth (I := I) Φ₀ k
              letI : SigmaCompactSpace (SourceDomain (I := I) Φ₀ k) :=
                sourceDomSigmaOf (I := I) Φ₀ k (hsrc k)
              metricDerivNorm (I := I) a (srcMetric (I := I) Φ₀ hsrc htgt k s)
                (srcMetric (I := I) Φ₀ hsrc htgt k t)
                (refRes (I := I) Φ₀ R hsrc k) y ≤ Lt * |s - t|)
    (hcarrier : X.D.carrier ⊆ Set.Icc β ψ)
    (h0 : (0 : Real) ∈ Set.Icc β ψ)
    (hcp : letI : TopologicalSpace mc.limit.M := mc.limit.topology;
        letI : ChartedSpace H mc.limit.M := mc.limit.charted;
        letI : T2Space mc.limit.M := mc.limit.t2;
        letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth;
        letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact;
      ∀ K : Set mc.limit.M, IsCompact K → ∀ ε : Real, 0 < ε →
        ∃ k0 : Nat, ∀ k : Nat, k0 ≤ k → K ⊆ Φ₀.source k ∧
          (letI : TopologicalSpace (SourceDomain (I := I) Φ₀ k) := sourceDomTop (I := I) Φ₀ k
           letI : ChartedSpace H (SourceDomain (I := I) Φ₀ k) := sourceDomCharted (I := I) Φ₀ k
           letI : T2Space (SourceDomain (I := I) Φ₀ k) := sourceDomT2 (I := I) Φ₀ k
           letI : IsManifold I ∞ (SourceDomain (I := I) Φ₀ k) := sourceDomSmooth (I := I) Φ₀ k
           letI : SigmaCompactSpace (SourceDomain (I := I) Φ₀ k) :=
             sourceDomSigmaOf (I := I) Φ₀ k (hsrc k)
           metricDerivNormSupOn (I := I) (sourceCompactSet (I := I) Φ₀ k K) 0
             (srcMetric (I := I) Φ₀ hsrc htgt k 0)
             (resSrc (I := I) Φ₀ hsrc k mc.limit.metric)
             (refRes (I := I) Φ₀ R hsrc k) < ε)) :
    letI : TopologicalSpace mc.limit.M := mc.limit.topology
    letI : ChartedSpace H mc.limit.M := mc.limit.charted
    letI : T2Space mc.limit.M := mc.limit.t2
    letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
    letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact
    letI : IsManifold I 1 mc.limit.M :=
      IsManifold.of_le (I := I) (M := mc.limit.M) (n := ∞)
        (by decide : (1 : WithTop ℕ∞) ≤ ∞)
    letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) mc.limit.M := by
      change IsManifold I ∞ mc.limit.M
      infer_instance
    let co := endgameCo Φ₀ R bf hsrc htgt β ψ hβψ hwin gRefT B Crel Bmax hBmax
      hCrel1 hBmax1 hequivT hrel hShiT hcovSrc hlipG
    ∀ (hsmooth : MetricFamilySmoothOn (I := I) (M := mc.limit.M) X.D
          ({ base := { metric := co.gInf } } :
            SolutionOn (I := I) (M := mc.limit.M) X.D).family)
      (hscalarCont : ContinuousOn
        (fun q : Real × mc.limit.M ↦ metricScalarAt (I := I) (co.gInf q.1) q.2)
        (X.D.carrier ×ˢ (Set.univ : Set mc.limit.M)))
      (hscalarTime : ∀ t ∈ X.D.carrier, ∀ x : mc.limit.M,
        DifferentiableWithinAt Real
          (fun s : Real ↦ metricScalarAt (I := I) (co.gInf s) x) X.D.carrier t)
      (hricciCont : Tensor0SFamilyContinuousOnSet (I := I) (M := mc.limit.M) 2
        X.D.carrier (fun t x ↦ metricRicciAt (I := I) (co.gInf t) x))
      (hrm04Cont : Tensor0SFamilyContinuousOnSet (I := I) (M := mc.limit.M) 4
        X.D.carrier (fun t x ↦ metricRm04At (I := I) (co.gInf t) x)),
      CompactnessConclusion (I := I) X := by
  dsimp only
  intro hsmooth hscalarCont hscalarTime hricciCont hrm04Cont
  letI : TopologicalSpace mc.limit.M := mc.limit.topology
  letI : ChartedSpace H mc.limit.M := mc.limit.charted
  letI : T2Space mc.limit.M := mc.limit.t2
  letI : IsManifold I ∞ mc.limit.M := mc.limit.smooth
  letI : SigmaCompactSpace mc.limit.M := mc.limit.sigmaCompact
  letI : IsManifold I 1 mc.limit.M :=
    IsManifold.of_le (I := I) (M := mc.limit.M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  letI : IsManifold I ((∞ : WithTop ℕ∞) + 1) mc.limit.M := by
    change IsManifold I ∞ mc.limit.M
    infer_instance
  let co := endgameCo Φ₀ R bf hsrc htgt β ψ hβψ hwin gRefT B Crel Bmax hBmax
    hCrel1 hBmax1 hequivT hrel hShiT hcovSrc hlipG
  have hpde : ∀ t ∈ X.D.regular, ∀ (x : mc.limit.M) (v w : TangentSpace I x),
      HasDerivAt (fun s : Real ↦ (co.gInf s).inner x v w)
        ((-2 : Real) * ricciTensor (I := I) (co.gInf t) x v w) t := by
    intro t ht x v w
    have htIcc : t ∈ Set.Icc β ψ := hcarrier (X.D.regular_subset ht)
    have hIcc : Set.Icc β ψ ∈ 𝓝 t :=
      Filter.mem_of_superset (X.D.regular_mem_nhds ht) hcarrier
    exact (ConvOut.gInf_pde (I := I) (Φ := Φ₀) R bf hsrc htgt β ψ hwin
      ((Crel * Bmax)⁻¹)
      (inv_pos.2 (mul_pos (lt_of_lt_of_le one_pos hCrel1)
        (lt_of_lt_of_le one_pos hBmax1)))
      (hbound_of_equiv (I := I) (Φ := Φ₀) R hsrc htgt β ψ gRefT B Crel Bmax
        hBmax hCrel1 hequivT hrel)
      (covTail_of_bounds (I := I) (Φ := Φ₀) R bf hsrc htgt β ψ hcovSrc)
      co x v w htIcc).hasDerivAt hIcc
  have hsol : IsSolutionOn (I := I)
      ({ base := { metric := co.gInf } } : SolutionOn (I := I) (M := mc.limit.M) X.D) :=
    DifferentialGeometry.PDE.RicciFlow.isSolutionOn_of_reg
      (I := I) co.gInf hsmooth hpde hscalarCont hscalarTime hricciCont hrm04Cont
  have hzero : co.gInf 0 = mc.limit.metric :=
    endgameCo_zero Φ₀ R bf hsrc htgt β ψ hβψ hwin gRefT B Crel Bmax hBmax
      hCrel1 hBmax1 hequivT hrel hShiT hcovSrc hlipG mc.limit.metric h0 hcp
  have hL0 :
      (flowOfMetric (I := I) X.D mc.limit co.gInf hsol).atTime 0 = mc.limit :=
    flowOfMetric_atTime (I := I) X.D mc.limit co.gInf hsol 0 hzero
  have hscalarRaw := ConvOut.scalar_conv (I := I) (Φ := Φ₀) R bf hsrc htgt β ψ
    ((Crel * Bmax)⁻¹)
    (inv_pos.2 (mul_pos (lt_of_lt_of_le one_pos hCrel1)
      (lt_of_lt_of_le one_pos hBmax1)))
    (hbound_of_equiv (I := I) (Φ := Φ₀) R hsrc htgt β ψ gRefT B Crel Bmax
      hBmax hCrel1 hequivT hrel)
    (covTail_of_bounds (I := I) (Φ := Φ₀) R bf hsrc htgt β ψ hcovSrc)
    co hcarrier
  have map_cast {P Q : PointedRiemannianManifold (I := I)}
      {s : Nat → Nat} (h : P = Q) (maps : PointedCGHMaps (I := I) X Q s)
      (k : Nat) (x : P.M) :
      HEq ((h.symm ▸ maps : PointedCGHMaps (I := I) X P s).map k x)
        (maps.map k (h ▸ x)) := by
    cases h
    rfl
  have hmap (k : Nat) (x : mc.limit.M) :
      (hL0.symm ▸ (Φ₀.compSubseq co.φ co.hφ) : PointedCGHMaps (I := I) X
        ((flowOfMetric (I := I) X.D mc.limit co.gInf hsol).atTime 0)
        (mc.subseq ∘ co.φ)).map k x =
        (Φ₀.compSubseq co.φ co.hφ).map k x := by
    have hx : hL0 ▸ x = x :=
      eq_of_heq ((eqRec_heq
        (φ := fun P : PointedRiemannianManifold (I := I) => P.M) hL0) x)
    exact (eq_of_heq (map_cast hL0 (Φ₀.compSubseq co.φ co.hφ) k x)).trans
      (congrArg (fun y => (Φ₀.compSubseq co.φ co.hφ).map k y) hx)
  have scalar : ScalarPullbackTendsto (I := I)
      (hL0.symm ▸ (Φ₀.compSubseq co.φ co.hφ) : PointedCGHMaps (I := I) X
        ((flowOfMetric (I := I) X.D mc.limit co.gInf hsol).atTime 0)
        (mc.subseq ∘ co.φ)) := by
    unfold ScalarPullbackTendsto FunctionPullbackTendsto
    intro t ht x
    change mc.limit.M at x
    simpa only [hmap, flowOfMetric, DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar,
      DifferentialGeometry.PDE.RicciFlow.SolutionFamily.scalar] using hscalarRaw t ht x
  exact flowLimit_endgame (I := I) mc Φ₀ R bf hsrc htgt β ψ hβψ hwin gRefT B Crel
    Bmax hBmax hCrel1 hBmax1 hequivT hrel hShiT hcovSrc hlipG hcarrier h0 hcp
    hsol scalar

end Endgame

end HCGCompactness
end DifferentialGeometry
