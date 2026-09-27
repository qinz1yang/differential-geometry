import DifferentialGeometry.Geometry.Comparison.NormalCoordinates.ExponentialBallPartialDiffeomorph



import DifferentialGeometry.Geometry.Exponential.NormalCoordinates.Framed
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Defs
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Covering.GoodCovering.Sequence

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Exponential

section

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [neZeroFinrank : NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

omit [NeZero (Module.finrank Real E)] in
theorem PointedRiemannianManifold.exists_exponential_ball_partial_diffeomorph
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (c : Y.M) {ρ : Real} :
    letI := Y.topology
    letI := Y.charted
    letI := Y.smooth
    letI := Y.sigmaCompact
    letI := Y.t2
    letI := Y.t2TangentBundle
    ENNReal.ofReal ρ < injRadius (I := I) Y.metric c →
    ρ ≤ expMapC2Radius (I := I) Y.metric c →
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) I E Y.M 1,
        Φ.source = Metric.ball (0 : E) ρ ∧
        Φ.target = (fun v : E =>
          (expMap (I := I) Y.metric c (show TangentSpace I c from v) : Y.M)) ''
            Metric.ball (0 : E) ρ ∧
        Set.EqOn Φ (fun v : E =>
          (expMap (I := I) Y.metric c (show TangentSpace I c from v) : Y.M))
          (Metric.ball (0 : E) ρ) := by
  let := Y.topology
  let := Y.charted
  let := Y.smooth
  let := Y.sigmaCompact
  let := Y.t2
  let := Y.t2TangentBundle
  intro hinj hC2
  exact exists_exponential_ball_partial_diffeomorph_of_lt (I := I) Y.metric c hinj hC2

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

def exponentialBallRadiusFactor (hd : InjectivityRadiusDecay (I := I) X) (D : Real) : Real :=
  205 * Real.exp (hd.C * (20 * hd.lambda D 0))

omit [CompleteSpace E] in
theorem exponential_ball_radius_factor_pos (hd : InjectivityRadiusDecay (I := I) X) (D : Real) :
    0 < exponentialBallRadiusFactor hd D := by
  exact mul_pos (by norm_num) (Real.exp_pos _)

def ExponentialBallRadiusBounds (hd : InjectivityRadiusDecay (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) (ρ : Nat → Nat → Real) : Prop :=
  ∀ k α : Nat, ∀ c : (X.obj k).M, c ∈ seqCenter hd D P k α →
    letI := (X.obj k).topology
    letI := (X.obj k).charted
    letI := (X.obj k).smooth
    letI := (X.obj k).sigmaCompact
    letI := (X.obj k).t2
    letI := (X.obj k).t2TangentBundle
    ENNReal.ofReal (ρ k α) < injRadius (I := I) (X.obj k).metric c ∧
      ρ k α ≤ expMapC2Radius (I := I) (X.obj k).metric c

def ExponentialBallRadiusAt (hd : InjectivityRadiusDecay (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData (I := I) hd D P) (pb : hd.PackingBound D) (r a : Real)
    (n : Nat) : Prop :=
  ∀ γ : Fin (pb.A r), ∀ c : (X.obj (L.φ n)).M,
    seqCenter hd D P (L.φ n) (γ : Nat) = some c →
      letI := (X.obj (L.φ n)).topology
      letI := (X.obj (L.φ n)).charted
      letI := (X.obj (L.φ n)).smooth
      letI := (X.obj (L.φ n)).sigmaCompact
      letI := (X.obj (L.φ n)).t2
      letI := (X.obj (L.φ n)).t2TangentBundle
      0 < a * L.lamInf (γ : Nat) ∧
        a * L.lamInf (γ : Nat) ≤
          expMapC2Radius (I := I) (X.obj (L.φ n)).metric c

def ExponentialBallRadiusTail (hd : InjectivityRadiusDecay (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData (I := I) hd D P) (pb : hd.PackingBound D) (r a : Real) : Prop :=
  ∀ᶠ n in Filter.atTop, ExponentialBallRadiusAt (I := I) hd D P L pb r a n

theorem ExponentialBallRadiusTail.subseq (hd : InjectivityRadiusDecay (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData (I := I) hd D P) (pb : hd.PackingBound D) (r a : Real)
    (hrad : ExponentialBallRadiusTail (I := I) hd D P L pb r a)
    {ψ : Nat → Nat} (hψ : StrictMono ψ) :
    ExponentialBallRadiusTail (I := I) hd D P (L.subseq hψ) pb r a := by
  filter_upwards [hψ.tendsto_atTop.eventually hrad] with n hn
  intro γ c hc
  exact hn γ c hc

namespace ExponentialBallRadiusBounds

theorem subseq (hd : InjectivityRadiusDecay (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) (ρ : Nat → Nat → Real)
    (hrad : ExponentialBallRadiusBounds (I := I) hd D P ρ) (f : Nat -> Nat) :
    ExponentialBallRadiusBounds (I := I) (hd.subseq f) D (fun k => P (f k))
      (fun k α => ρ (f k) α) := by
  intro k α c hc
  have hc' : c ∈ seqCenter hd D P (f k) α := by
    have hcenter :
        seqCenter (hd.subseq f) D (fun j ↦ P (f j)) k α =
          seqCenter hd D P (f k) α := rfl
    rw [hcenter] at hc
    exact hc
  simpa [InjectivityRadiusDecay.subseq, PointedRiemannianSeq.subseq] using
    hrad (f k) α c hc'

end ExponentialBallRadiusBounds

theorem exists_sequence_exponential_ball_partial_diffeomorph
    (hd : InjectivityRadiusDecay (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) (ρ : Nat → Nat → Real)
    (hrad : ExponentialBallRadiusBounds (I := I) hd D P ρ)
    (k α : Nat) (c : (X.obj k).M) (hc : c ∈ seqCenter hd D P k α) :
    letI := (X.obj k).topology
    letI := (X.obj k).charted
    letI := (X.obj k).smooth
    letI := (X.obj k).sigmaCompact
    letI := (X.obj k).t2
    letI := (X.obj k).t2TangentBundle
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) I E (X.obj k).M 1,
        Φ.source = Metric.ball (0 : E) (ρ k α) ∧
        Φ.target = (fun v : E =>
          (expMap (I := I) (X.obj k).metric c (show TangentSpace I c from v) :
            (X.obj k).M)) '' Metric.ball (0 : E) (ρ k α) ∧
        Set.EqOn Φ (fun v : E =>
          (expMap (I := I) (X.obj k).metric c (show TangentSpace I c from v) :
            (X.obj k).M))
          (Metric.ball (0 : E) (ρ k α)) :=
  (X.obj k).exists_exponential_ball_partial_diffeomorph c (hrad k α c hc).1 (hrad k α c hc).2

theorem exists_exponential_ball_partial_diffeomorph
    (hd : InjectivityRadiusDecay (I := I) X) {D a r : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData (I := I) hd D P) (pb : hd.PackingBound D) (n : Nat)
    (hrad : ExponentialBallRadiusAt (I := I) hd D P L pb r a n)
    (γ : Fin (pb.A r)) (c : (X.obj (L.φ n)).M)
    (hc : seqCenter hd D P (L.φ n) (γ : Nat) = some c) :
    letI := (X.obj (L.φ n)).topology
    letI := (X.obj (L.φ n)).charted
    letI := (X.obj (L.φ n)).smooth
    letI := (X.obj (L.φ n)).sigmaCompact
    letI := (X.obj (L.φ n)).t2
    letI := (X.obj (L.φ n)).t2TangentBundle
    ENNReal.ofReal (a * L.lamInf (γ : Nat)) <
      injRadius (I := I) (X.obj (L.φ n)).metric c →
    ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) I E (X.obj (L.φ n)).M 1,
      Φ.source = Metric.ball (0 : E) (a * L.lamInf (γ : Nat)) ∧
      Φ.target = (fun v : E =>
        (expMap (I := I) (X.obj (L.φ n)).metric c
          (show TangentSpace I c from v) : (X.obj (L.φ n)).M)) ''
            Metric.ball (0 : E) (a * L.lamInf (γ : Nat)) ∧
      Set.EqOn Φ (fun v : E =>
        (expMap (I := I) (X.obj (L.φ n)).metric c
          (show TangentSpace I c from v) : (X.obj (L.φ n)).M))
        (Metric.ball (0 : E) (a * L.lamInf (γ : Nat))) := by
  let _ := neZeroFinrank
  exact fun hinj => (X.obj (L.φ n)).exists_exponential_ball_partial_diffeomorph c
    hinj (hrad γ c hc).2

def ExponentialRadiusScaleBounds (hd : InjectivityRadiusDecay (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData (I := I) hd D P) : Prop :=
  ∀ n γ : Nat, ∀ c : (X.obj (L.φ n)).M,
    seqCenter hd D P (L.φ n) γ = some c →
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      4 * L.lamInf γ < metricCoerciveExpRadius (I := I) (X.obj (L.φ n)).metric c

def ExponentialRadiusScaleAt (hd : InjectivityRadiusDecay (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData (I := I) hd D P) (pb : hd.PackingBound D) (r : Real)
    (n : Nat) : Prop :=
  ∀ γ : Fin (pb.A r), ∀ c : (X.obj (L.φ n)).M,
    seqCenter hd D P (L.φ n) (γ : Nat) = some c →
      letI : TopologicalSpace (X.obj (L.φ n)).M := (X.obj (L.φ n)).topology
      letI : ChartedSpace H (X.obj (L.φ n)).M := (X.obj (L.φ n)).charted
      letI : IsManifold I ∞ (X.obj (L.φ n)).M := (X.obj (L.φ n)).smooth
      letI : T2Space (X.obj (L.φ n)).M := (X.obj (L.φ n)).t2
      letI : T2Space (TangentBundle I (X.obj (L.φ n)).M) :=
        (X.obj (L.φ n)).t2TangentBundle
      4 * L.lamInf (γ : Nat) < metricCoerciveExpRadius (I := I) (X.obj (L.φ n)).metric c

def ExponentialRadiusScaleTail (hd : InjectivityRadiusDecay (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData (I := I) hd D P) (pb : hd.PackingBound D) (r : Real) : Prop :=
  ∀ᶠ n in Filter.atTop, ExponentialRadiusScaleAt (I := I) hd D P L pb r n

theorem ExponentialRadiusScaleBounds.at (hd : InjectivityRadiusDecay (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData (I := I) hd D P)
    (hgp : ExponentialRadiusScaleBounds (I := I) hd D P L)
    (pb : hd.PackingBound D) (r : Real) (n : Nat) :
    ExponentialRadiusScaleAt (I := I) hd D P L pb r n := by
  intro γ c hc
  exact hgp n (γ : Nat) c hc

theorem ExponentialRadiusScaleBounds.to_tail (hd : InjectivityRadiusDecay (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData (I := I) hd D P)
    (hgp : ExponentialRadiusScaleBounds (I := I) hd D P L)
    (pb : hd.PackingBound D) (r : Real) :
    ExponentialRadiusScaleTail (I := I) hd D P L pb r :=
  Filter.Eventually.of_forall fun n => hgp.at hd D P L pb r n

theorem ExponentialRadiusScaleBounds.subseq (hd : InjectivityRadiusDecay (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData (I := I) hd D P)
    (hgp : ExponentialRadiusScaleBounds (I := I) hd D P L)
    {ψ : Nat → Nat} (hψ : StrictMono ψ) :
    ExponentialRadiusScaleBounds (I := I) hd D P (L.subseq hψ) := by
  intro n γ c hc
  exact hgp (ψ n) γ c hc

theorem ExponentialRadiusScaleTail.subseq (hd : InjectivityRadiusDecay (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData (I := I) hd D P) (pb : hd.PackingBound D) (r : Real)
    (hgp : ExponentialRadiusScaleTail (I := I) hd D P L pb r)
    {ψ : Nat → Nat} (hψ : StrictMono ψ) :
    ExponentialRadiusScaleTail (I := I) hd D P (L.subseq hψ) pb r := by
  filter_upwards [hψ.tendsto_atTop.eventually hgp] with n hn
  intro γ c hc
  exact hn γ c hc

end

section

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

theorem PointedRiemannianManifold.exists_framed_exponential_ball_partial_diffeomorph
    (Y : PointedRiemannianManifold.{u, uE, uH} (I := I)) (c : Y.M) {ρ : Real} :
    letI := Y.topology
    letI := Y.charted
    letI := Y.smooth
    letI := Y.sigmaCompact
    letI := Y.t2
    letI := Y.t2TangentBundle
    ENNReal.ofReal ρ < framedInjRadius (I := I) Y.metric c →
    ρ ≤ metricCoerciveExpRadius (I := I) Y.metric c →
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) I E Y.M 1,
        Φ.source = Metric.ball (0 : E) ρ ∧
        Φ.target = framedExpMap (I := I) Y.metric c '' Metric.ball (0 : E) ρ ∧
        Set.EqOn Φ (framedExpMap (I := I) Y.metric c)
          (Metric.ball (0 : E) ρ) := by
  let := Y.topology
  let := Y.charted
  let := Y.smooth
  let := Y.sigmaCompact
  let := Y.t2
  let := Y.t2TangentBundle
  intro hinj hC2
  exact exists_framed_exponential_ball_partial_diffeomorph_of_lt (I := I) Y.metric c hinj hC2

variable {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}

def FramedExponentialBallRadiusBounds (hd : InjectivityRadiusDecay (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) (ρ : Nat → Nat → Real) : Prop :=
  ∀ k α : Nat, ∀ c : (X.obj k).M, c ∈ seqCenter hd D P k α →
    letI := (X.obj k).topology
    letI := (X.obj k).charted
    letI := (X.obj k).smooth
    letI := (X.obj k).sigmaCompact
    letI := (X.obj k).t2
    letI := (X.obj k).t2TangentBundle
    ENNReal.ofReal (ρ k α) < framedInjRadius (I := I) (X.obj k).metric c ∧
      ρ k α ≤ metricCoerciveExpRadius (I := I) (X.obj k).metric c

def FramedExponentialBallRadiusAt (hd : InjectivityRadiusDecay (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData (I := I) hd D P) (pb : hd.PackingBound D) (r a : Real)
    (n : Nat) : Prop :=
  ∀ γ : Fin (pb.A r), ∀ c : (X.obj (L.φ n)).M,
    seqCenter hd D P (L.φ n) (γ : Nat) = some c →
      letI := (X.obj (L.φ n)).topology
      letI := (X.obj (L.φ n)).charted
      letI := (X.obj (L.φ n)).smooth
      letI := (X.obj (L.φ n)).sigmaCompact
      letI := (X.obj (L.φ n)).t2
      letI := (X.obj (L.φ n)).t2TangentBundle
      ENNReal.ofReal (a * L.lamInf (γ : Nat)) <
          framedInjRadius (I := I) (X.obj (L.φ n)).metric c ∧
        a * L.lamInf (γ : Nat) ≤
          metricCoerciveExpRadius (I := I) (X.obj (L.φ n)).metric c

def FramedExponentialBallRadiusTail (hd : InjectivityRadiusDecay (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData (I := I) hd D P) (pb : hd.PackingBound D) (r a : Real) : Prop :=
  ∀ᶠ n in Filter.atTop, FramedExponentialBallRadiusAt (I := I) hd D P L pb r a n

theorem FramedExponentialBallRadiusTail.subseq
    (hd : InjectivityRadiusDecay (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData (I := I) hd D P) (pb : hd.PackingBound D) (r a : Real)
    (hrad : FramedExponentialBallRadiusTail (I := I) hd D P L pb r a)
    {ψ : Nat → Nat} (hψ : StrictMono ψ) :
    FramedExponentialBallRadiusTail (I := I) hd D P (L.subseq hψ) pb r a := by
  filter_upwards [hψ.tendsto_atTop.eventually hrad] with n hn
  intro γ c hc
  exact hn γ c hc

namespace FramedExponentialBallRadiusBounds

theorem subseq (hd : InjectivityRadiusDecay (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) (ρ : Nat → Nat → Real)
    (hrad : FramedExponentialBallRadiusBounds (I := I) hd D P ρ) (f : Nat → Nat) :
    FramedExponentialBallRadiusBounds (I := I) (hd.subseq f) D (fun k => P (f k))
      (fun k α => ρ (f k) α) := by
  intro k α c hc
  have hc' : c ∈ seqCenter hd D P (f k) α := by
    have hcenter :
        seqCenter (hd.subseq f) D (fun j ↦ P (f j)) k α =
          seqCenter hd D P (f k) α := rfl
    rw [hcenter] at hc
    exact hc
  simpa [InjectivityRadiusDecay.subseq, PointedRiemannianSeq.subseq] using
    hrad (f k) α c hc'

end FramedExponentialBallRadiusBounds

theorem exists_sequence_framed_exponential_ball_partial_diffeomorph
    (hd : InjectivityRadiusDecay (I := I) X) (D : Real)
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k)) (ρ : Nat → Nat → Real)
    (hrad : FramedExponentialBallRadiusBounds (I := I) hd D P ρ)
    (k α : Nat) (c : (X.obj k).M) (hc : c ∈ seqCenter hd D P k α) :
    letI := (X.obj k).topology
    letI := (X.obj k).charted
    letI := (X.obj k).smooth
    letI := (X.obj k).sigmaCompact
    letI := (X.obj k).t2
    letI := (X.obj k).t2TangentBundle
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) I E (X.obj k).M 1,
        Φ.source = Metric.ball (0 : E) (ρ k α) ∧
        Φ.target = framedExpMap (I := I) (X.obj k).metric c ''
          Metric.ball (0 : E) (ρ k α) ∧
        Set.EqOn Φ (framedExpMap (I := I) (X.obj k).metric c)
          (Metric.ball (0 : E) (ρ k α)) :=
  (X.obj k).exists_framed_exponential_ball_partial_diffeomorph c (hrad k α c hc).1 (hrad k α c hc).2

theorem exists_framed_exponential_ball_partial_diffeomorph
    (hd : InjectivityRadiusDecay (I := I) X) {D a r : Real}
    (P : ∀ k : Nat, ProperMetricOn (I := I) (X.obj k))
    (L : NetLimitData (I := I) hd D P) (pb : hd.PackingBound D) (n : Nat)
    (hrad : FramedExponentialBallRadiusAt (I := I) hd D P L pb r a n)
    (γ : Fin (pb.A r)) (c : (X.obj (L.φ n)).M)
    (hc : seqCenter hd D P (L.φ n) (γ : Nat) = some c) :
    letI := (X.obj (L.φ n)).topology
    letI := (X.obj (L.φ n)).charted
    letI := (X.obj (L.φ n)).smooth
    letI := (X.obj (L.φ n)).sigmaCompact
    letI := (X.obj (L.φ n)).t2
    letI := (X.obj (L.φ n)).t2TangentBundle
      ∃ Φ : PartialDiffeomorph 𝓘(ℝ, E) I E (X.obj (L.φ n)).M 1,
        Φ.source = Metric.ball (0 : E) (a * L.lamInf (γ : Nat)) ∧
        Φ.target = framedExpMap (I := I) (X.obj (L.φ n)).metric c ''
          Metric.ball (0 : E) (a * L.lamInf (γ : Nat)) ∧
        Set.EqOn Φ (framedExpMap (I := I) (X.obj (L.φ n)).metric c)
          (Metric.ball (0 : E) (a * L.lamInf (γ : Nat))) :=
  (X.obj (L.φ n)).exists_framed_exponential_ball_partial_diffeomorph c
    (hrad γ c hc).1 (hrad γ c hc).2

end

end CheegerGromovCompactness
end DifferentialGeometry
