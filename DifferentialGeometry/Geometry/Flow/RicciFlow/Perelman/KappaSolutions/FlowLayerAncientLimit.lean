import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.WindowCompactnessProducer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Metric.AncientHalfLine
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CGHSubsequenceClosure
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.WindowEstimatesTransfer

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open Filter
open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [T2Space M] [IsManifold I ∞ M]

structure AncientMetricInput
    (gSeq : Nat → Real → SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) : Prop where
  lipschitz_in_time : ∀ (n : Nat) (K : Set M), IsCompact K → ∀ p : Nat,
    ∃ L : Real, 0 ≤ L ∧
      ∀ (k : Nat) (s : Real), s ∈ Set.Icc (-(n : Real)) 0 →
        ∀ t : Real, t ∈ Set.Icc (-(n : Real)) 0 → ∀ a : Nat, a ≤ p →
          ∀ x : M, x ∈ K →
            metricDerivNorm (I := I) a (gSeq k s) (gSeq k t) gRef x ≤ L * |s - t|
  covariant_derivative_bounds :
    ∀ (ρ : Nat → Nat), StrictMono ρ → ∀ t : Real, t ≤ 0 →
      ∀ q : Nat, ∀ K : Set M, IsCompact K → ∃ C : Real, ∀ k : Nat, ∀ z : M, z ∈ K →
        metricCovDerivNorm (I := I) q (gSeq (ρ k) t) gRef z ≤ C
  local_lower_bound : ∀ (ρ : Nat → Nat), StrictMono ρ → ∀ t : Real, t ≤ 0 →
    ∃ c : Real, 0 < c ∧ ∀ (k : Nat) (x : M) (v : TangentSpace I x),
      c * gRef.inner x v v ≤ (gSeq (ρ k) t).inner x v v

structure AncientMetricSubsequence
    (gSeq : Nat → Real → SmoothRiemannianMetric I M)
    (gRef : SmoothRiemannianMetric I M) where
  subseq : Nat → Nat
  strictMono : StrictMono subseq
  limit : Real → SmoothRiemannianMetric I M
  converges : ∀ (n : Nat) (K : Set M), IsCompact K → ∀ (p : Nat) (ε : Real), 0 < ε →
    ∃ k0 : Nat, ∀ k : Nat, k0 ≤ k → ∀ t : Real, t ∈ Set.Icc (-(n : Real)) 0 →
      metricDerivNormSupOn (I := I) K p (gSeq (subseq k) t) (limit t) gRef < ε

namespace AncientMetricSubsequence

noncomputable def comp {gSeq : Nat → Real → SmoothRiemannianMetric I M}
    {gRef : SmoothRiemannianMetric I M}
    (h : AncientMetricSubsequence (I := I) gSeq gRef) (ψ : Nat → Nat) (hψ : StrictMono ψ) :
    AncientMetricSubsequence (I := I) gSeq gRef where
  subseq := h.subseq ∘ ψ
  strictMono := h.strictMono.comp hψ
  limit := h.limit
  converges := by
    intro n K hK p ε hε
    obtain ⟨k0, hk0⟩ := h.converges n K hK p ε hε
    exact ⟨k0, fun k hk t ht => hk0 (ψ k) (le_trans hk (hψ.id_le k)) t ht⟩

end AncientMetricSubsequence

theorem nonempty_ancientMetricSubsequence
    [I.Boundaryless] [IsManifold I 1 M] [SigmaCompactSpace M] [WeaklyLocallyCompactSpace M]
    (gSeq : Nat → Real → SmoothRiemannianMetric I M) (gRef : SmoothRiemannianMetric I M)
    (hne : Nonempty M) (h : AncientMetricInput (I := I) gSeq gRef) :
    Nonempty (AncientMetricSubsequence (I := I) gSeq gRef) := by
  obtain ⟨φ, hφ, gInf, hconv⟩ :=
    exists_ancient_locally_uniform_subsequence (I := I) hne gSeq gRef
      h.lipschitz_in_time h.covariant_derivative_bounds h.local_lower_bound
  exact ⟨{ subseq := φ, strictMono := hφ, limit := gInf, converges := hconv }⟩

theorem ancientMetricInput_const (gRef : SmoothRiemannianMetric I M) :
    AncientMetricInput (I := I) (fun _ _ => gRef) gRef where
  lipschitz_in_time := by
    intro n K hK p
    exact ⟨0, le_rfl, fun k s hs t ht a ha x hx => by
      rw [zero_mul, metricDerivNorm_self]⟩
  covariant_derivative_bounds := by
    intro ρ hρ t ht q K hK
    obtain ⟨C, hC⟩ := metricCovDerivNorm_bddOn (I := I) hK q gRef gRef
    exact ⟨C, fun k z hz => hC z hz⟩
  local_lower_bound := by
    intro ρ hρ t ht
    exact ⟨1, one_pos, fun k x v => by rw [one_mul]⟩

theorem nonempty_ancientMetricSubsequence_const (gRef : SmoothRiemannianMetric I M)
    [I.Boundaryless] [IsManifold I 1 M] [SigmaCompactSpace M] [WeaklyLocallyCompactSpace M]
    (hne : Nonempty M) :
    Nonempty (AncientMetricSubsequence (I := I) (fun _ _ => gRef) gRef) :=
  nonempty_ancientMetricSubsequence (I := I) (fun _ _ => gRef) gRef hne
    (ancientMetricInput_const (I := I) gRef)

end CheegerGromovCompactness
end DifferentialGeometry

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Filter
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff _root_.Topology

universe u uE uH

section SameManifold

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M]
variable [T2Space M] [SigmaCompactSpace M]

structure SameManifoldFlowSeq (I : ModelWithCorners Real E H) (M : Type u)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [IsManifold I 1 M]
    [T2Space M] [SigmaCompactSpace M] where
  horizon : Nat → Real
  horizon_pos : ∀ n : Nat, 0 < horizon n
  basepoint : Nat → M
  [t2TangentBundle : T2Space (TangentBundle I M)]
  solution : (n : Nat) → SolutionOn (I := I) (M := M) (arcInterval (horizon n))
  isSolution : ∀ n : Nat, IsSolutionOn (I := I) (solution n)

namespace SameManifoldFlowSeq

noncomputable def toFiniteArcFlowSeq (Y : SameManifoldFlowSeq I M) :
    FiniteArcFlowSeq.{u, uE, uH} (I := I) where
  horizon := Y.horizon
  horizon_pos := Y.horizon_pos
  term n :=
    letI : T2Space (TangentBundle I M) := Y.t2TangentBundle
    { M := M
      basepoint := Y.basepoint n
      S := Y.solution n
      isSolution := Y.isSolution n }

@[simp] theorem toFiniteArcFlowSeq_horizon (Y : SameManifoldFlowSeq I M) :
    Y.toFiniteArcFlowSeq.horizon = Y.horizon := rfl

@[simp] theorem toFiniteArcFlowSeq_term_basepoint (Y : SameManifoldFlowSeq I M) (n : Nat) :
    (Y.toFiniteArcFlowSeq.term n).basepoint = Y.basepoint n := rfl

@[simp] theorem toFiniteArcFlowSeq_term_atTime_metric (Y : SameManifoldFlowSeq I M)
    (n : Nat) (t : Real) :
    ((Y.toFiniteArcFlowSeq.term n).atTime (I := I) t).metric =
      (Y.solution n).family.metric t := rfl

noncomputable def metricFamily (Y : SameManifoldFlowSeq I M) :
    Nat → Real → SmoothRiemannianMetric I M :=
  fun n t => (Y.solution n).family.metric t

@[simp] theorem metricFamily_apply (Y : SameManifoldFlowSeq I M) (n : Nat) (t : Real) :
    Y.metricFamily n t = (Y.solution n).family.metric t := rfl

noncomputable def windowMetricFamily (Y : SameManifoldFlowSeq I M) (N : Nat) :
    Nat → Real → SmoothRiemannianMetric I M :=
  fun k t => Y.metricFamily (k + N) t

@[simp] theorem windowMetricFamily_apply (Y : SameManifoldFlowSeq I M) (N k : Nat) (t : Real) :
    Y.windowMetricFamily N k t = Y.metricFamily (k + N) t := rfl

@[simp] theorem windowSeq_term_atTime_metric (Y : SameManifoldFlowSeq I M)
    (hT : Tendsto Y.horizon atTop atTop) (m : Nat) (k : Nat) (t : Real) :
    (((Y.toFiniteArcFlowSeq.windowSeq hT m).term k).atTime (I := I) t).metric =
      Y.windowMetricFamily (Y.toFiniteArcFlowSeq.windowShift hT m) k t := rfl

end SameManifoldFlowSeq

end SameManifold

section Window

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable [NeZero (Module.finrank Real E)]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M] [IsManifold I 1 M]
variable [T2Space M] [SigmaCompactSpace M]

def SameManifoldWindowCompactness (Y : SameManifoldFlowSeq.{u, uE, uH} I M)
    (hT : Tendsto Y.horizon atTop atTop) : Prop :=
  ∀ (m : Nat) (φ : Nat → Nat), StrictMono φ →
    WindowCompactnessEstimates (Y.toFiniteArcFlowSeq.tail
        (Y.toFiniteArcFlowSeq.windowShift hT m))
      (windowHorizon m) (windowHorizon_pos m)
      (fun k => Y.toFiniteArcFlowSeq.le_horizon_add_windowShift hT m k) →
    ∃ ψ : Nat → Nat, StrictMono ψ ∧
      Y.toFiniteArcFlowSeq.WindowConverges hT m (φ ∘ ψ)

omit [NeZero (Module.finrank Real E)] in
theorem SameManifoldFlowSeq.nonempty_ancientMetricSubsequence [WeaklyLocallyCompactSpace M]
    (Y : SameManifoldFlowSeq.{u, uE, uH} I M) (gRef : SmoothRiemannianMetric I M)
    (hne : Nonempty M) (h : AncientMetricInput (I := I) Y.metricFamily gRef) :
    Nonempty (AncientMetricSubsequence (I := I) Y.metricFamily gRef) :=
  DifferentialGeometry.CheegerGromovCompactness.nonempty_ancientMetricSubsequence
    (I := I) Y.metricFamily gRef hne h

theorem sameManifoldWindowCompactness_of_finiteArcWindowCompactnessInput
    (Y : SameManifoldFlowSeq.{u, uE, uH} I M) (hT : Tendsto Y.horizon atTop atTop)
    (h : FiniteArcWindowCompactnessInput Y.toFiniteArcFlowSeq hT) :
    SameManifoldWindowCompactness Y hT :=
  fun m φ hφ _ => h m φ hφ

theorem sameManifoldWindowCompactness_of_windowCompactnessFrontier
    (Y : SameManifoldFlowSeq.{u, uE, uH} I M) (hT : Tendsto Y.horizon atTop atTop)
    (hfrontier : WindowCompactnessFrontier Y.toFiniteArcFlowSeq hT) :
    SameManifoldWindowCompactness Y hT :=
  fun m φ hφ hest => hfrontier.compact m φ hφ hest

end Window

section SubsequenceClosure

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

theorem FiniteArcFlowSeq.windowConverges_subseqClosure
    (X : FiniteArcFlowSeq.{u, uE, uH} (I := I))
    (hT : Tendsto X.horizon atTop atTop) :
    ∀ (_m : Nat) (_φ _ψ : Nat → Nat)
      (_L : PointedFlowData.{u, uE, uH} (I := I) (arcInterval (windowHorizon _m))),
      StrictMono _ψ →
      Nonempty (SmoothCGHConverges (I := I) (X.windowSeq hT _m) _L _φ) →
      Nonempty (SmoothCGHConverges (I := I) (X.windowSeq hT _m) _L (_φ ∘ _ψ)) :=
  fun _m _φ _ψ _L hψ hconv => ⟨(Classical.choice hconv).compSubseq _ψ hψ⟩

theorem FiniteArcFlowSeq.windowConverges_compSubseq
    (X : FiniteArcFlowSeq.{u, uE, uH} (I := I))
    (hT : Tendsto X.horizon atTop atTop) {m : Nat} {ρ σ : Nat → Nat}
    (h : X.WindowConverges hT m ρ) (hσ : StrictMono σ) :
    X.WindowConverges hT m (ρ ∘ σ) := by
  obtain ⟨L, hL⟩ := h
  exact ⟨L, ⟨(Classical.choice hL).compSubseq σ hσ⟩⟩

end SubsequenceClosure

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
