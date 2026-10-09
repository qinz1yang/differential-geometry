import DifferentialGeometry.Topology.LoopSpace.GenericApproximation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LoopFamilyExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.ContractibleLoopPerturbation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.LeastAreaConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaError.Convergence
import Mathlib.Analysis.SpecificLimits.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.AreaEvolution.Basic

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

end

noncomputable section

open Set Filter Metric Manifold
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Surgery.Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_generic_loopFamily_approximation_of_smoothOn_univ
    (hdim : Module.finrank ℝ E = 3) {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (γ : ℝ → ContinuousFreeLoop M) {a b : ℝ} (hab : a < b)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) univ)
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Γ : ℝ → ContinuousFreeLoop M,
      (curveOfLoopFamily Γ).SmoothOn (I := I) univ ∧
      (curveOfLoopFamily Γ).ImmersedOn (I := I) (Icc a b) ∧
      (∃ exceptional : Finset ℝ, ∀ t ∈ Icc a b, t ∉ exceptional → Topology.IsEmbedding (Γ t)) ∧
      ∀ m : ℕ, m ≤ n → ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc a b,
        ‖iteratedFDerivWithin ℝ m
            (fun q : ℝ × ℝ => e.map (Γ q.2 (q.1 : Surgery.Topology.Circle)))
            (univ ×ˢ Icc a b) p -
          iteratedFDerivWithin ℝ m
            (fun q : ℝ × ℝ => e.map (γ q.2 (q.1 : Surgery.Topology.Circle)))
            (univ ×ˢ Icc a b) p‖ < ε := by
  obtain ⟨β, hβ, hβi, hβemb, hβjets⟩ :=
    DifferentialGeometry.Topology.exists_generic_loop_family_approximation_of_contMDiff
      hdim e.map e.smooth e.isClosedEmbedding.isEmbedding e.injective_mfderiv
      (fun p => γ p.1 p.2) hab (contMDiff_uncurry_of_smoothOn_univ γ hγ) hi n hε
  let Γ : ℝ → ContinuousFreeLoop M := fun t =>
    ⟨fun z => β (t, z), hβ.continuous.comp (continuous_const.prodMk continuous_id)⟩
  exact ⟨Γ, smoothOn_curveOfLoopFamily_of_contMDiff Γ hβ univ, hβi, hβemb, hβjets⟩

theorem exists_generic_loopFamily_approximation
    (hdim : Module.finrank ℝ E = 3) {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    (R : Width.SmoothTubularRetraction e)
    (γ : ℝ → ContinuousFreeLoop M) {a b : ℝ} (hab : a < b)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b))
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ Γ : ℝ → ContinuousFreeLoop M,
      (curveOfLoopFamily Γ).SmoothOn (I := I) univ ∧
      (curveOfLoopFamily Γ).ImmersedOn (I := I) (Icc a b) ∧
      (∃ exceptional : Finset ℝ, ∀ t ∈ Icc a b, t ∉ exceptional → Topology.IsEmbedding (Γ t)) ∧
      ∀ m : ℕ, m ≤ n → ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc a b,
        ‖iteratedFDerivWithin ℝ m
            (fun q : ℝ × ℝ => e.map (Γ q.2 (q.1 : Surgery.Topology.Circle)))
            (univ ×ˢ Icc a b) p -
          iteratedFDerivWithin ℝ m
            (fun q : ℝ × ℝ => e.map (γ q.2 (q.1 : Surgery.Topology.Circle)))
            (univ ×ˢ Icc a b) p‖ < ε := by
  obtain ⟨γext, lo, hi', hlo, hhi, hext, hiext, heq⟩ :=
    exists_smooth_immersed_loopFamily_extension hab.le e R γ hγ hi
  have hiexact : (curveOfLoopFamily γext).ImmersedOn (I := I) (Icc a b) :=
    fun x t ht => hiext x t ⟨hlo.le.trans ht.1, ht.2.trans hhi.le⟩
  obtain ⟨Γ, hΓ, hΓi, hΓemb, hΓjets⟩ :=
    exists_generic_loopFamily_approximation_of_smoothOn_univ hdim e γext hab hext hiexact n hε
  refine ⟨Γ, hΓ, hΓi, hΓemb, ?_⟩
  have hagree : EqOn
      (fun q : ℝ × ℝ => e.map (γext q.2 (q.1 : Surgery.Topology.Circle)))
      (fun q : ℝ × ℝ => e.map (γ q.2 (q.1 : Surgery.Topology.Circle))) (univ ×ˢ Icc a b) := by
    intro q hq
    change e.map (γext q.2 (q.1 : Surgery.Topology.Circle)) =
      e.map (γ q.2 (q.1 : Surgery.Topology.Circle))
    rw [heq q.2 hq.2]
  intro m hm p hp
  have h := hΓjets m hm p hp
  rw [iteratedFDerivWithin_congr hagree ⟨mem_univ _, hp.2⟩ m] at h
  exact h

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

noncomputable section

open Set Filter Manifold
open scoped Topology ContDiff Manifold
open DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

open Surgery.Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless] [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [CompactSpace M]

theorem exists_generic_loopFamily_approximation_sequence
    (hdim : Module.finrank ℝ E = 3) {N : ℕ}
    (e : Width.SmoothLoopEmbedding (I := I) (Q := M) N)
    {D : RealTimeInterval} (g : ℝ → SmoothRiemannianMetric I M)
    (hg : MetricFamilySmoothOn D g) {a b : ℝ} (hab : a < b) (hreg : Icc a b ⊆ D.regular)
    (γ : ℝ → ContinuousFreeLoop M)
    (hγ : (curveOfLoopFamily γ).SmoothOn (I := I) (Icc a b))
    (hi : (curveOfLoopFamily γ).ImmersedOn (I := I) (Icc a b)) :
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
        |(curveOfLoopFamily (approximants j)).areaError g (Icc a b) t -
          (curveOfLoopFamily γ).areaError g (Icc a b) t| < ε) ∧
      ((∀ t ∈ Icc a b, IsContractibleLoop (γ t)) →
        (∀ j t, t ∈ Icc a b → IsContractibleLoop (approximants j t)) ∧
        ∀ ε > 0, ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ t ∈ Icc a b,
          |loopFamilyLeastArea g (approximants j) t - loopFamilyLeastArea g γ t| < ε) := by
  let _ : Nonempty M := ⟨γ a 0⟩
  let _ : NeZero (Module.finrank ℝ E) := ⟨by rw [hdim]; norm_num⟩
  obtain ⟨r, U, hU, heU, hr, hleft⟩ :=
    DifferentialGeometry.Geometry.exists_smooth_neighborhood_retraction
      e.smooth e.isClosedEmbedding.isEmbedding e.injective_mfderiv
  let R : Width.SmoothTubularRetraction e := ⟨U, hU, heU, r, hr, hleft⟩
  obtain ⟨δ, hδ, hctr⟩ :=
    exists_pos_forall_loopFamily_isContractibleLoop_of_iteratedFDerivWithin_zero
      (g a) e.map e.isClosedEmbedding.isEmbedding
  have hsize (j : ℕ) : 0 < min δ (1 / ((j : ℝ) + 1)) :=
    lt_min hδ (by positivity)
  choose app hsmooth himm hemb hbound using fun j : ℕ =>
    exists_generic_loopFamily_approximation hdim e R γ hab hγ hi 2 (hsize j)
  have hs (j : ℕ) : (curveOfLoopFamily (app j)).SmoothOn (I := I) (Icc a b) :=
    (hsmooth j).mono (prod_mono subset_rfl (subset_univ _))
  have hconv : ∀ ε > 0, ∃ j₀ : ℕ, ∀ j ≥ j₀, ∀ m : ℕ, m ≤ 2 →
      ∀ p ∈ Icc (0 : ℝ) 1 ×ˢ Icc a b,
        ‖iteratedFDerivWithin ℝ m
            (fun q : ℝ × ℝ => e.map (app j q.2 (q.1 : Surgery.Topology.Circle)))
            (univ ×ˢ Icc a b) p -
          iteratedFDerivWithin ℝ m
            (fun q : ℝ × ℝ => e.map (γ q.2 (q.1 : Surgery.Topology.Circle)))
            (univ ×ˢ Icc a b) p‖ < ε := by
    intro ε hε
    have hsmall : ∀ᶠ j : ℕ in atTop, 1 / ((j : ℝ) + 1) < ε :=
      tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hε)
    obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp hsmall
    exact ⟨j₀, fun j hj m hm p hp =>
      (hbound j m hm p hp).trans ((min_le_right _ _).trans_lt (hj₀ j hj))⟩
  have hjet : ∀ m ≤ 2, TendstoUniformlyOn
      (fun j p => iteratedFDerivWithin ℝ m
        (fun q : ℝ × ℝ => e.map ((curveOfLoopFamily (app j)).lift q.1 q.2))
        (univ ×ˢ Icc a b) p)
      (fun p => iteratedFDerivWithin ℝ m
        (fun q : ℝ × ℝ => e.map ((curveOfLoopFamily γ).lift q.1 q.2))
        (univ ×ˢ Icc a b) p) atTop (Icc (0 : ℝ) 1 ×ˢ Icc a b) := by
    intro m hm
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨j₀, hj₀⟩ := hconv ε hε
    filter_upwards [eventually_ge_atTop j₀] with j hj p hp
    rw [dist_eq_norm, norm_sub_rev]
    exact hj₀ j hj m hm p hp
  have harea := CurveMap.tendstoUniformlyOn_areaError_of_embedding_iteratedFDerivWithin
    hg hab hreg e.smooth e.isClosedEmbedding.isEmbedding e.injective_mfderiv
    (fun j => curveOfLoopFamily (app j)) (curveOfLoopFamily γ) hs himm hγ hi hjet
  refine ⟨app, fun j => ⟨hs j, himm j, hemb j⟩, hconv, ?_, ?_⟩
  · intro ε hε
    have h := Metric.tendstoUniformlyOn_iff.mp harea ε hε
    obtain ⟨j₀, hj₀⟩ := eventually_atTop.mp h
    refine ⟨j₀, fun j hj t ht => ?_⟩
    simpa only [Real.dist_eq, abs_sub_comm] using hj₀ j hj t ht
  · intro hγctr
    have happctr : ∀ j t, t ∈ Icc a b → IsContractibleLoop (app j t) := fun j =>
      hctr γ (app j) (Icc a b) hγctr (fun p hp =>
        (hbound j 0 (by norm_num) p hp).trans_le (min_le_left _ _))
    refine ⟨happctr, ?_⟩
    exact uniform_loopFamilyLeastArea_of_uniform_c1 D g hg hab (hreg.trans D.regular_subset)
      e γ app hγ hs hγctr happctr (fun ε hε => by
        obtain ⟨j₀, hj₀⟩ := hconv ε hε
        exact ⟨j₀, fun j hj m hm p hp => hj₀ j hj m (hm.trans (by norm_num)) p hp⟩)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end
