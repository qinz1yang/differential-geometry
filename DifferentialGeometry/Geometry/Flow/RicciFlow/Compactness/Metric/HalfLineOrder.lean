import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.HalfLine

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : PointedFlowSeq.{u, uE, uH} (I := I)}
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedFlowData.topology PointedFlowData.charted PointedFlowData.smooth
  PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem HalfLineMetricConvergenceData.inner_le_of_eventually_source_inner_le
    (Phi : PointedCGHMaps X P phi) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    {s t : ℝ} (hs : s ≤ 0) (ht : t ≤ 0)
    (horder : ∀ᶠ k in atTop, ∀ (y : (X.term (phi (co.φ k))).M)
      (w : TangentSpace I y),
      ((X.term (phi (co.φ k))).S.base.metric s).inner y w w ≤
        ((X.term (phi (co.φ k))).S.base.metric t).inner y w w)
    (x : P.M) (v : TangentSpace I x) :
    (co.gInf s).inner x v v ≤ (co.gInf t).inner x v v := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hconv (r : ℝ) (hr : r ≤ 0) :
      Tendsto (fun k => (gSeqExt Phi R bf hsrc htgt (co.φ k) r).inner x v v)
        atTop (𝓝 ((co.gInf r).inner x v v)) := by
    obtain ⟨n, hn⟩ := exists_nat_ge (-r)
    have hrwin : r ∈ Icc (-(n : ℝ)) 0 := ⟨by linarith, hr⟩
    apply metricInner_tendsto
      (fun k => gSeqExt Phi R bf hsrc htgt (co.φ k) r) (co.gInf r) R x
    intro epsilon hepsilon
    obtain ⟨N, hN⟩ := (co.convergenceOn n).convergencePt {x} isCompact_singleton 0
      epsilon hepsilon
    exact ⟨N, fun k hk => hN k hk r hrwin 0 le_rfl x (mem_singleton x)⟩
  apply le_of_tendsto_of_tendsto (hconv s hs) (hconv t ht)
  have hpull := co.strictMono.tendsto_atTop.eventually
    (DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.eventually_gSeqExt_eq_pullback
      Phi R bf hsrc htgt {x} isCompact_singleton)
  filter_upwards [hpull, horder] with k hk hle
  obtain ⟨U, _hU, hxU, _hsource, heq⟩ := hk
  rw [heq s x (hxU (mem_singleton x)) v v, heq t x (hxU (mem_singleton x)) v v]
  exact hle _ _

end DifferentialGeometry.CheegerGromovCompactness

end
