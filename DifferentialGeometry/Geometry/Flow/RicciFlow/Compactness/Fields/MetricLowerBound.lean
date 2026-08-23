import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Convergence

import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.Equation
open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open Set Bundle Manifold
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry
namespace HCGCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]

variable {X : PointedFlowSeq (I := I)}
variable {P : PointedRiemannianManifold (I := I)}
variable {subseq : Nat → Nat}
variable (Φ : PointedCGHMaps (I := I) X P subseq)

namespace ConvOut

omit [NeZero (Module.finrank ℝ E)]
  [I.Boundaryless] in
theorem lower_of
    {R : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted;
      letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SrcSigma Φ} {htgt : TgtSigma Φ}
    {β ψ c : Real} (co : ConvOut (I := I) Φ R bf hsrc htgt β ψ)
    (hseq : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted;
      letI : IsManifold I ∞ P.M := P.smooth;
      ∀ (k : Nat) (t : Real), t ∈ Set.Icc β ψ →
        ∀ (x : P.M) (v : TangentSpace I x),
          c * R.inner x v v ≤
            (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) t).inner x v v) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    ∀ (t : Real), t ∈ Set.Icc β ψ →
      ∀ (x : P.M) (v : TangentSpace I x),
        c * R.inner x v v ≤ (co.gInf t).inner x v v := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : T2Space P.M := P.t2
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  intro t ht x v
  have hinner : Filter.Tendsto
      (fun k ↦ (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) t).inner x v v)
      Filter.atTop (nhds ((co.gInf t).inner x v v)) := by
    apply metricInner_tendsto (I := I)
      (fun k ↦ gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) t)
      (co.gInf t) R x
    intro ε hε
    obtain ⟨k₀, hk₀⟩ := co.convPt {x} isCompact_singleton 0 ε hε
    exact ⟨k₀, fun k hk ↦ hk₀ k hk t ht 0 le_rfl x (Set.mem_singleton x)⟩
  exact ge_of_tendsto hinner
    (Filter.Eventually.of_forall fun k ↦ hseq k t ht x v)

end ConvOut
end HCGCompactness
end DifferentialGeometry
