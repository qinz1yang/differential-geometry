import DifferentialGeometry.Geometry.Flow.RicciFlow.HCGCompactness.MetricCompactness

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

/-!
# Re-indexing the Theorem 3.9 conclusion along a further subsequence

`MetricCompactnessConclusion.compSubseq` follows the whole MSM135 Theorem 3.9
conclusion record along a further strictly monotone subsequence `φ`: the
extracted subsequence composes with `φ`, the limit manifold and its
completeness are unchanged, the comparison maps re-index stage-wise, and the
compact-open `C^p` metric convergence passes to the subsequence (its `∃ k0`
shape is asymptotic in `k`).

This is the re-indexing step of the `conv`-field assembly (Brick 5 of
`P4_CONV_PLAN.md`): after Arzelà–Ascoli extracts a further subsequence, the
Theorem 3.9 data must follow it before the limit flow is assembled.

The source domain of the re-indexed comparison maps at stage `k` is
definitionally the original source domain at stage `φ k`, so the
`MetricSourceData` re-index is a field-by-field re-wrap
(`MetricSourceData.compSubseq`) with no transport lemmas.
-/

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace HCGCompactness

open scoped Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E]
variable [InnerProductSpace Real E] [Module.Finite Real E] [FiniteDimensional Real E]
variable [NeZero (Module.finrank Real E)] [CompleteSpace E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable [I.Boundaryless]

namespace PointedRiemannianCGMaps

/-- Riemannian comparison maps re-indexed along a further strictly monotone
subsequence: stage `k` of the new record is stage `φ k` of the old one. -/
def compSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq)
    (φ : Nat -> Nat) (hφ : StrictMono φ) :
    PointedRiemannianCGMaps (I := I) X L (subseq ∘ φ) where
  partialDiffeomorph k := Φ.partialDiffeomorph (φ k)
  source_exhausts := by
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    exact Φ.source_exhausts.comp_subseq hφ
  base_mem k := Φ.base_mem (φ k)
  basepoint_map k := Φ.basepoint_map (φ k)

/-- Regard maps from a sequence already reindexed by `f` as maps from the
original sequence at the composed subsequence. -/
def ofSeqSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {inner : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) (X.subseq f) L inner) :
    PointedRiemannianCGMaps (I := I) X L (f ∘ inner) where
  partialDiffeomorph := Φ.partialDiffeomorph
  source_exhausts := Φ.source_exhausts
  base_mem := Φ.base_mem
  basepoint_map := Φ.basepoint_map

/-- Regard maps from a sequence already reindexed by `f` at the identity
subsequence as maps from the original sequence at subsequence `f`. -/
def ofSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    (Φ : PointedRiemannianCGMaps (I := I) (X.subseq f) L id) :
    PointedRiemannianCGMaps (I := I) X L f :=
  Φ.ofSeqSubseq f

/-- The source of the re-indexed comparison map is the original source at the
re-indexed stage (definitional). -/
@[simp] theorem compSubseq_source
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) X L subseq)
    (φ : Nat -> Nat) (hφ : StrictMono φ) (k : Nat) :
    (Φ.compSubseq φ hφ).source k = Φ.source (φ k) := rfl

@[simp] theorem ofSeqSubseq_source
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {inner : Nat -> Nat}
    (Φ : PointedRiemannianCGMaps (I := I) (X.subseq f) L inner)
    (k : Nat) :
    (Φ.ofSeqSubseq f).source k = Φ.source k := rfl

/-- The identity-inner lift preserves each source definitionally. -/
@[simp] theorem ofSubseq_source
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    (Φ : PointedRiemannianCGMaps (I := I) (X.subseq f) L id)
    (k : Nat) :
    (Φ.ofSubseq f).source k = Φ.source k := rfl

end PointedRiemannianCGMaps

namespace MetricSourceData

/-- Metric source-domain data transported to the re-indexed comparison maps.

The source domain of `Φ.compSubseq φ hφ` at stage `k` is definitionally the
source domain of `Φ` at stage `φ k` (the new `partialDiffeomorph k` is
literally `Φ.partialDiffeomorph (φ k)`), so the data re-wraps field by field
with no casts or transport lemmas. -/
def compSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedRiemannianCGMaps (I := I) X L subseq}
    (φ : Nat -> Nat) (hφ : StrictMono φ) (k : Nat)
    (D : MetricSourceData (I := I) Φ (φ k)) :
    MetricSourceData (I := I) (Φ.compSubseq φ hφ) k where
  topology := D.topology
  charted := D.charted
  t2 := D.t2
  smooth := D.smooth
  sigmaCompact := D.sigmaCompact
  limitMetric := D.limitMetric
  pullbackMetric := D.pullbackMetric
  referenceMetric := D.referenceMetric
  compact_preimage := D.compact_preimage
  limit_inner := D.limit_inner
  pullback_inner := D.pullback_inner

/-- Re-wrap source-domain metric data when a sequence-level subsequence is
moved into the maps record's subsequence index. -/
def ofSeqSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {inner : Nat -> Nat}
    {Φ : PointedRiemannianCGMaps (I := I) (X.subseq f) L inner}
    (k : Nat) (D : MetricSourceData (I := I) Φ k) :
    MetricSourceData (I := I) (Φ.ofSeqSubseq f) k where
  topology := D.topology
  charted := D.charted
  t2 := D.t2
  smooth := D.smooth
  sigmaCompact := D.sigmaCompact
  limitMetric := D.limitMetric
  pullbackMetric := D.pullbackMetric
  referenceMetric := D.referenceMetric
  compact_preimage := D.compact_preimage
  limit_inner := D.limit_inner
  pullback_inner := D.pullback_inner

/-- Re-wrap source-domain metric data for the identity inner subsequence. -/
def ofSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {Φ : PointedRiemannianCGMaps (I := I) (X.subseq f) L id}
    (k : Nat) (D : MetricSourceData (I := I) Φ k) :
    MetricSourceData (I := I) (Φ.ofSubseq f) k :=
  MetricSourceData.ofSeqSubseq (I := I) f k D

/-- The source-domain seminorm `derivNormSupOn` is unchanged by the
re-indexing re-wrap (definitional). -/
@[simp] theorem compSubseq_supOn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedRiemannianCGMaps (I := I) X L subseq}
    (φ : Nat -> Nat) (hφ : StrictMono φ) (k : Nat)
    (D : MetricSourceData (I := I) Φ (φ k)) (K : Set L.M) (p : Nat) :
    (MetricSourceData.compSubseq (I := I) φ hφ k D).derivNormSupOn (I := I) K p =
      D.derivNormSupOn (I := I) K p := rfl

@[simp] theorem ofSeqSubseq_supOn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {inner : Nat -> Nat}
    {Φ : PointedRiemannianCGMaps (I := I) (X.subseq f) L inner}
    (k : Nat) (D : MetricSourceData (I := I) Φ k)
    (K : Set L.M) (p : Nat) :
    (MetricSourceData.ofSeqSubseq (I := I) f k D).derivNormSupOn (I := I) K p =
      D.derivNormSupOn (I := I) K p := rfl

/-- The identity-inner source-data lift preserves `derivNormSupOn`. -/
@[simp] theorem ofSubseq_supOn
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {Φ : PointedRiemannianCGMaps (I := I) (X.subseq f) L id}
    (k : Nat) (D : MetricSourceData (I := I) Φ k)
    (K : Set L.M) (p : Nat) :
    (MetricSourceData.ofSubseq (I := I) f k D).derivNormSupOn (I := I) K p =
      D.derivNormSupOn (I := I) K p := rfl

end MetricSourceData

namespace MetricCGConvergenceData

/-- Metric Cheeger--Gromov convergence data re-indexed along a further strictly
monotone subsequence: the domain data re-wraps stage-wise, and the
`∃ k0`-shaped compact-open convergence passes to the subsequence via
`k ≤ φ k`. -/
def compSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedRiemannianCGMaps (I := I) X L subseq}
    (Cd : MetricCGConvergenceData (I := I) Φ)
    (φ : Nat -> Nat) (hφ : StrictMono φ) :
    MetricCGConvergenceData (I := I) (Φ.compSubseq φ hφ) where
  domain k := MetricSourceData.compSubseq (I := I) φ hφ k (Cd.domain (φ k))
  converges := by
    intro K hK p ε hε
    obtain ⟨k0, hk0⟩ := Cd.converges K hK p ε hε
    exact ⟨k0, fun k hk => hk0 (φ k) (le_trans hk (hφ.id_le k))⟩

/-- Move convergence from `X.subseq f` to `X` at the composed subsequence. -/
def ofSeqSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {inner : Nat -> Nat}
    {Φ : PointedRiemannianCGMaps (I := I) (X.subseq f) L inner}
    (Cd : MetricCGConvergenceData (I := I) Φ) :
    MetricCGConvergenceData (I := I) (Φ.ofSeqSubseq f) where
  domain k := MetricSourceData.ofSeqSubseq (I := I) f k (Cd.domain k)
  converges := by
    intro K hK p ε hε
    simpa only [PointedRiemannianCGMaps.ofSeqSubseq_source,
      MetricSourceData.ofSeqSubseq_supOn] using Cd.converges K hK p ε hε

/-- Move identity-indexed convergence from `X.subseq f` to `X`. -/
def ofSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {Φ : PointedRiemannianCGMaps (I := I) (X.subseq f) L id}
    (Cd : MetricCGConvergenceData (I := I) Φ) :
    MetricCGConvergenceData (I := I) (Φ.ofSubseq f) :=
  Cd.ofSeqSubseq f

end MetricCGConvergenceData

namespace PointedRiemannianCGConverges

/-- Pointed Riemannian Cheeger--Gromov convergence re-indexed along a further
strictly monotone subsequence. -/
def compSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {subseq : Nat -> Nat}
    {Φ : PointedRiemannianCGMaps (I := I) X L subseq}
    (C : PointedRiemannianCGConverges (I := I) X L subseq Φ)
    (φ : Nat -> Nat) (hφ : StrictMono φ) :
    PointedRiemannianCGConverges (I := I) X L (subseq ∘ φ) (Φ.compSubseq φ hφ) where
  metrics := C.metrics.compSubseq φ hφ

/-- Move pointed convergence from `X.subseq f` to `X` at the composed
subsequence. -/
def ofSeqSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {inner : Nat -> Nat}
    {Φ : PointedRiemannianCGMaps (I := I) (X.subseq f) L inner}
    (C : PointedRiemannianCGConverges (I := I) (X.subseq f) L inner Φ) :
    PointedRiemannianCGConverges (I := I) X L (f ∘ inner) (Φ.ofSeqSubseq f) where
  metrics := C.metrics.ofSeqSubseq f

/-- Move identity-indexed pointed convergence from `X.subseq f` to `X`. -/
def ofSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat)
    {L : PointedRiemannianManifold.{u, uE, uH} (I := I)}
    {Φ : PointedRiemannianCGMaps (I := I) (X.subseq f) L id}
    (C : PointedRiemannianCGConverges (I := I) (X.subseq f) L id Φ) :
    PointedRiemannianCGConverges (I := I) X L f (Φ.ofSubseq f) :=
  C.ofSeqSubseq f

end PointedRiemannianCGConverges

namespace MetricCompactnessConclusion

/-- Move a compactness conclusion for `X.subseq f` back to `X`, composing its
extracted subsequence with `f`. -/
def ofSeqSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat) (hf : StrictMono f)
    (mc : MetricCompactnessConclusion (I := I) (X.subseq f)) :
    MetricCompactnessConclusion (I := I) X where
  subseq := f ∘ mc.subseq
  strictMono := hf.comp mc.strictMono
  limit := mc.limit
  limit_complete := mc.limit_complete
  maps := mc.maps.ofSeqSubseq f
  convergence := mc.convergence.ofSeqSubseq f

/-- The lifted conclusion extracts the composed subsequence. -/
@[simp] theorem ofSeqSubseq_subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat) (hf : StrictMono f)
    (mc : MetricCompactnessConclusion (I := I) (X.subseq f)) :
    (mc.ofSeqSubseq f hf).subseq = f ∘ mc.subseq := rfl

/-- The lifted conclusion keeps the same limit manifold. -/
@[simp] theorem ofSeqSubseq_limit
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (f : Nat -> Nat) (hf : StrictMono f)
    (mc : MetricCompactnessConclusion (I := I) (X.subseq f)) :
    (mc.ofSeqSubseq f hf).limit = mc.limit := rfl

/-- The MSM135 Theorem 3.9 conclusion re-indexed along a further strictly
monotone subsequence: the extracted subsequence composes with `φ`, the limit
manifold and its completeness are unchanged, the comparison maps re-index
stage-wise, and the compact-open metric convergence passes to the
subsequence. -/
def compSubseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (mc : MetricCompactnessConclusion (I := I) X)
    (φ : Nat -> Nat) (hφ : StrictMono φ) :
    MetricCompactnessConclusion (I := I) X where
  subseq := mc.subseq ∘ φ
  strictMono := mc.strictMono.comp hφ
  limit := mc.limit
  limit_complete := mc.limit_complete
  maps := mc.maps.compSubseq φ hφ
  convergence := mc.convergence.compSubseq φ hφ

/-- The re-indexed conclusion extracts the composed subsequence. -/
@[simp] theorem compSubseq_subseq
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (mc : MetricCompactnessConclusion (I := I) X)
    (φ : Nat -> Nat) (hφ : StrictMono φ) :
    (mc.compSubseq φ hφ).subseq = mc.subseq ∘ φ := rfl

/-- The re-indexed conclusion keeps the same limit manifold. -/
@[simp] theorem compSubseq_limit
    {X : PointedRiemannianSeq.{u, uE, uH} (I := I)}
    (mc : MetricCompactnessConclusion (I := I) X)
    (φ : Nat -> Nat) (hφ : StrictMono φ) :
    (mc.compSubseq φ hφ).limit = mc.limit := rfl

end MetricCompactnessConclusion

end HCGCompactness
end DifferentialGeometry
