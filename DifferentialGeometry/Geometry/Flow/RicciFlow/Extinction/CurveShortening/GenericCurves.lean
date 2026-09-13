import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaEvolution

noncomputable section

open Set
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Surgery.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
private theorem isEmbedding_of_continuous_injective_of_compact {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [CompactSpace X] [T2Space Y] {f : X → Y}
    (hf : Continuous f) (hinj : Function.Injective f) : Topology.IsEmbedding f :=
  (Topology.IsClosedEmbedding.of_continuous_injective_isClosedMap hf hinj
    fun _ hs => (hs.isCompact.image hf).isClosed).toIsEmbedding

def LoopFamilyEmbeddedOffFinset (γ : ℝ → ContinuousFreeLoop M) (J : Set ℝ) : Prop :=
  ∃ exceptional : Finset ℝ, ∀ t ∈ J, t ∉ exceptional → Topology.IsEmbedding (γ t)

namespace LoopFamilyEmbeddedOffFinset

variable {γ : ℝ → ContinuousFreeLoop M} {J J' : Set ℝ}

theorem mono (h : J' ⊆ J) (hγ : LoopFamilyEmbeddedOffFinset γ J) :
    LoopFamilyEmbeddedOffFinset γ J' :=
  let ⟨exceptional, hexc⟩ := hγ
  ⟨exceptional, fun t ht hne => hexc t (h ht) hne⟩

theorem of_slicewiseEmbedding (h : ∀ t ∈ J, Topology.IsEmbedding (γ t)) :
    LoopFamilyEmbeddedOffFinset γ J :=
  ⟨∅, fun t ht _ => h t ht⟩

end LoopFamilyEmbeddedOffFinset

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem loopFamilyEmbeddedOffFinset_iff_injective [T2Space M]
    (γ : ℝ → ContinuousFreeLoop M) (J : Set ℝ) :
    LoopFamilyEmbeddedOffFinset γ J ↔ ∃ exceptional : Finset ℝ,
      ∀ t ∈ J, t ∉ exceptional → Function.Injective (γ t) := by
  constructor
  · rintro ⟨exceptional, hexc⟩
    exact ⟨exceptional, fun t ht hne => (hexc t ht hne).injective⟩
  · rintro ⟨exceptional, hinj⟩
    exact ⟨exceptional, fun t ht hne =>
      isEmbedding_of_continuous_injective_of_compact (γ t).continuous (hinj t ht hne)⟩

theorem loopFamily_spacetimeMap_injOn_of_embeddedOffFinset (γ : ℝ → ContinuousFreeLoop M)
    {J : Set ℝ} (hemb : LoopFamilyEmbeddedOffFinset γ J) :
    ∃ exceptional : Finset ℝ,
      Set.InjOn (fun p : ℝ × Surgery.Topology.Circle => (p.1, γ p.1 p.2))
        ((J \ ↑exceptional) ×ˢ univ) :=
  let ⟨exceptional, hexc⟩ := hemb
  ⟨exceptional, loopFamily_spacetimeMap_injective γ (J := J \ ↑exceptional)
    (fun t ht => hexc t ht.1 ht.2)⟩

variable [hBoundary : I.Boundaryless] [hT2 : T2Space M]
    [hCompact : CompactSpace M] [hNonempty : Nonempty M]
variable [SigmaCompactSpace M]
variable {D : RealTimeInterval} {a b : ℝ}

include hBoundary hT2 hCompact hNonempty

omit hBoundary hCompact hNonempty [SigmaCompactSpace M] in
theorem rfs_csf_generic_curves_of_slicewiseEmbedding
    (B : RicciBackground (I := I) (M := M) D a b) {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (hemb : ∀ t ∈ Icc a b, Topology.IsEmbedding (γ t)) :
    ∃ approximants : ℕ → ℝ → ContinuousFreeLoop M,
      (∀ j, (curveOfLoopFamily (approximants j)).SmoothOn (I := I) (Icc a b) ∧
        (curveOfLoopFamily (approximants j)).ImmersedOn (I := I) (Icc a b) ∧
        ∃ exceptional : Finset ℝ, ∀ t ∈ Icc a b,
          t ∉ exceptional → Topology.IsEmbedding (approximants j t)) ∧
      (∀ ε > 0, ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ m : ℕ, m ≤ 2 →
        ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc a b,
          ‖iteratedFDerivWithin ℝ m
              (fun q : ℝ × ℝ => e.map (approximants j q.2 (q.1 : Surgery.Topology.Circle)))
              (univ ×ˢ Icc a b) p -
            iteratedFDerivWithin ℝ m
              (fun q : ℝ × ℝ => e.map (γ q.2 (q.1 : Surgery.Topology.Circle)))
              (univ ×ˢ Icc a b) p‖ < ε) ∧
      (∀ ε > 0, ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ t ∈ Icc a b,
        |(curveOfLoopFamily (approximants j)).areaError B.family.metric (Icc a b) t -
          (curveOfLoopFamily γ).areaError B.family.metric (Icc a b) t| < ε) ∧
      ((∀ t ∈ Icc a b, IsContractibleLoop (γ t)) →
        (∀ j t, t ∈ Icc a b → IsContractibleLoop (approximants j t)) ∧
        ∀ ε > 0, ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ t ∈ Icc a b,
          |loopFamilyLeastArea B.family.metric (approximants j) t -
            loopFamilyLeastArea B.family.metric γ t| < ε) := by
  refine ⟨fun _ => γ, ?_, ?_, ?_, ?_⟩
  · intro j
    exact ⟨hγ, hi, ⟨∅, fun t ht _ => hemb t ht⟩⟩
  · intro ε hε
    refine ⟨0, ?_⟩
    intro j _ m _ p _
    rw [sub_self, norm_zero]
    exact hε
  · intro ε hε
    refine ⟨0, ?_⟩
    intro j _ t _
    rw [sub_self, abs_zero]
    exact hε
  · intro hctr
    refine ⟨fun j t ht => hctr t ht, ?_⟩
    intro ε hε
    refine ⟨0, ?_⟩
    intro j _ t _
    rw [sub_self, abs_zero]
    exact hε

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
