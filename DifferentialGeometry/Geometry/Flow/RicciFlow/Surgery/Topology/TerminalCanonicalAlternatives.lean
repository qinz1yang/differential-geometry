import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalCapCapture
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalScalarSublevel
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalStrictBounds
import Mathlib.Topology.Order.IsLUB

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u
variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

theorem TerminalLimitMetric.eventually_canonical_neck_or_cap
    (L : G.TerminalLimitMetric) (x y : G.terminalRegularOpen)
    (hy : y.val ∈ connectedComponent x.val) {eps C1 C2 : ℝ}
    (hscalar : C2 * metricScalarAt L.metric y < metricScalarAt L.metric x) :
    ∀ᶠ t in 𝓝[<] s, ∀ W : CanonicalWitness G.flow eps C1 C2 x.val t,
      (∃ neck : LocalNeck G.flow eps x.val t W.domain.carrier,
        W.alternative = CanonicalAlternative.neck neck) ∨
      ∃ cap : LocalCap G.flow eps x.val t W.domain.carrier,
        ∃ depth, W.alternative = CanonicalAlternative.cap cap depth := by
  have hc := ((L.tendsto_metricScalarAt y).const_mul C2).eventually_lt
    (L.tendsto_metricScalarAt x) hscalar
  filter_upwards [hc] with t ht
  intro W
  exact W.alternative_eq_neck_or_cap_of_mul_scalar_lt hy ht

theorem TerminalLimitMetric.eventually_canonical_neck_or_cap_of_not_isCompact
    (L : G.TerminalLimitMetric) (x : G.terminalRegularOpen)
    (hnoncompact : ¬ IsCompact (connectedComponent x)) (eps C1 C2 : ℝ) :
    ∀ᶠ t in 𝓝[<] s, ∀ W : CanonicalWitness G.flow eps C1 C2 x.val t,
      (∃ neck : LocalNeck G.flow eps x.val t W.domain.carrier,
        W.alternative = CanonicalAlternative.neck neck) ∨
      ∃ cap : LocalCap G.flow eps x.val t W.domain.carrier,
        ∃ depth, W.alternative = CanonicalAlternative.cap cap depth := by
  obtain ⟨y, hy, hscalar⟩ :=
    L.exists_scalar_gt_on_connectedComponent_of_not_isCompact x hnoncompact
      (C2 * metricScalarAt L.metric x)
  have hy' : y.val ∈ connectedComponent x.val :=
    continuous_subtype_val.mapsTo_connectedComponent x hy
  have hc := ((L.tendsto_metricScalarAt x).const_mul C2).eventually_lt
    (L.tendsto_metricScalarAt y) hscalar
  filter_upwards [hc] with t ht
  intro W
  have hproper : W.domain.carrier ≠ connectedComponent x.val := by
    intro hwhole
    exact (not_le_of_gt ht) (W.scalar_bounds y.val (hwhole.symm ▸ hy')).2
  cases W.alternative with
  | neck data => exact Or.inl ⟨data, rfl⟩
  | cap data deep => exact Or.inr ⟨data, deep, rfl⟩
  | positive whole data hsec => exact (hproper whole).elim
  | round whole data => exact (hproper whole).elim

theorem exists_canonical_neck_or_cap_sequence_of_eventually
    {x : P.Carrier} {eps C1 C2 q : ℝ}
    (hcanonical : ∀ t ∈ Ioo a s, q < G.flow.scalar t x →
      ∃ W : CanonicalWitness G.flow eps C1 C2 x t, W.capTubeHasNeckChart eps)
    (hhigh : ∀ᶠ t in 𝓝[<] s, q < G.flow.scalar t x)
    (hbranch : ∀ᶠ t in 𝓝[<] s, ∀ W : CanonicalWitness G.flow eps C1 C2 x t,
      (∃ neck : LocalNeck G.flow eps x t W.domain.carrier,
        W.alternative = CanonicalAlternative.neck neck) ∨
      ∃ cap : LocalCap G.flow eps x t W.domain.carrier,
        ∃ depth, W.alternative = CanonicalAlternative.cap cap depth) :
    ∃ τ : ℕ → ℝ, StrictMono τ ∧ (∀ n, τ n ∈ Ioo a s) ∧ Tendsto τ atTop (𝓝[<] s) ∧
      ∃ W : ∀ n, CanonicalWitness G.flow eps C1 C2 x (τ n),
        (∀ n, (W n).capTubeHasNeckChart eps) ∧
        ((∃ neck : ∀ n, LocalNeck G.flow eps x (τ n) (W n).domain.carrier,
          ∀ n, (W n).alternative = CanonicalAlternative.neck (neck n)) ∨
         ∃ cap : ∀ n, LocalCap G.flow eps x (τ n) (W n).domain.carrier,
           ∃ depth : ∀ n, ∀ z ∈ (cap n).tube,
             10000 / Real.sqrt (G.flow.scalar (τ n) x) ≤
               metricDistance (G.flow.base.metric (τ n)) x z,
             ∀ n, (W n).alternative = CanonicalAlternative.cap (cap n) (depth n)) := by
  classical
  obtain ⟨d, hd, hlate⟩ := (mem_nhdsLT_iff_exists_mem_Ico_Ioo_subset G.lt).mp
    (hhigh.and hbranch)
  obtain ⟨τ, hτmono, hτmem, hτlim⟩ := exists_seq_strictMono_tendsto' hd.2
  have hτ : Tendsto τ atTop (𝓝[<] s) :=
    tendsto_nhdsWithin_iff.mpr ⟨hτlim, Eventually.of_forall (fun n => (hτmem n).2)⟩
  have hτdomain (n : ℕ) : τ n ∈ Ioo a s := ⟨hd.1.trans_lt (hτmem n).1, (hτmem n).2⟩
  choose W hW using fun n => hcanonical (τ n) (hτdomain n) (hlate (hτmem n)).1
  have halt (n : ℕ) := (hlate (hτmem n)).2 (W n)
  let isNeck (n : ℕ) : Prop := ∃ neck : LocalNeck G.flow eps x (τ n) (W n).domain.carrier,
    (W n).alternative = CanonicalAlternative.neck neck
  by_cases hfrequent : ∃ᶠ n in atTop, isNeck n
  · obtain ⟨φ, hφ, hφneck⟩ := extraction_of_frequently_atTop hfrequent
    choose neck hneck using hφneck
    exact ⟨fun n => τ (φ n), hτmono.comp hφ, fun n => hτdomain (φ n), hτ.comp hφ.tendsto_atTop,
      fun n => W (φ n), fun n => hW (φ n), Or.inl ⟨neck, hneck⟩⟩
  · have hcaps : ∀ᶠ n in atTop, ∃ cap : LocalCap G.flow eps x (τ n) (W n).domain.carrier,
        ∃ depth, (W n).alternative = CanonicalAlternative.cap cap depth := by
      filter_upwards [not_frequently.mp hfrequent] with n hn
      exact (halt n).resolve_left hn
    obtain ⟨φ, hφ, hφcap⟩ := extraction_of_eventually_atTop hcaps
    choose cap depth hcap using hφcap
    exact ⟨fun n => τ (φ n), hτmono.comp hφ, fun n => hτdomain (φ n), hτ.comp hφ.tendsto_atTop,
      fun n => W (φ n), fun n => hW (φ n), Or.inr ⟨cap, depth, hcap⟩⟩

theorem exists_uniform_canonical_neck_or_cap_sequence
    {eps : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (P : OrientedThreeStage.{u}) (a s : ℝ)
      (G : P.IncomingSlab a s), ∃ q : ℝ, 0 < q ∧
        ∀ (L : G.TerminalLimitMetric) (x y : G.terminalRegularOpen), q < metricScalarAt L.metric x →
          y.val ∈ connectedComponent x.val →
          C * metricScalarAt L.metric y < metricScalarAt L.metric x →
          ∃ τ : ℕ → ℝ, StrictMono τ ∧ (∀ n, τ n ∈ Ioo a s) ∧ Tendsto τ atTop (𝓝[<] s) ∧
            ∃ W : ∀ n, CanonicalWitness G.flow eps C C x.val (τ n),
              (∀ n, (W n).capTubeHasNeckChart eps) ∧
              ((∃ neck : ∀ n, LocalNeck G.flow eps x.val (τ n) (W n).domain.carrier,
                ∀ n, (W n).alternative = CanonicalAlternative.neck (neck n)) ∨
               ∃ cap : ∀ n, LocalCap G.flow eps x.val (τ n) (W n).domain.carrier,
                 ∃ depth : ∀ n, ∀ z ∈ (cap n).tube,
                   10000 / Real.sqrt (G.flow.scalar (τ n) x.val) ≤
                     metricDistance (G.flow.base.metric (τ n)) x.val z,
                   ∀ n, (W n).alternative = CanonicalAlternative.cap (cap n) (depth n)) := by
  obtain ⟨C, hC, hmain⟩ :=
    exists_uniform_canonical_constants_with_cap_neck_charts.{u} heps hsmall
  refine ⟨C, hC, ?_⟩
  intro P a s G
  obtain ⟨q, hq, hcanonical⟩ := hmain P a s G
  refine ⟨q, hq, ?_⟩
  intro L x y hx hy hscalar
  have hhigh : ∀ᶠ t in 𝓝[<] s, q < G.flow.scalar t x.val :=
    (L.tendsto_metricScalarAt x).eventually (Ioi_mem_nhds hx)
  have hbranch := L.eventually_canonical_neck_or_cap x y hy (eps := eps) (C1 := C) hscalar
  exact exists_canonical_neck_or_cap_sequence_of_eventually
    (fun t ht hx => hcanonical x.val t ⟨ht.1.le, ht.2⟩ hx.le) hhigh hbranch

theorem exists_uniform_canonical_neck_or_cap_sequence_of_not_isCompact
    {eps : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (P : OrientedThreeStage.{u}) (a s : ℝ)
      (G : P.IncomingSlab a s), ∃ q : ℝ, 0 < q ∧
        ∀ (L : G.TerminalLimitMetric) (x : G.terminalRegularOpen), q < metricScalarAt L.metric x →
          ¬ IsCompact (connectedComponent x) →
          ∃ τ : ℕ → ℝ, StrictMono τ ∧ (∀ n, τ n ∈ Ioo a s) ∧ Tendsto τ atTop (𝓝[<] s) ∧
            ∃ W : ∀ n, CanonicalWitness G.flow eps C C x.val (τ n),
              (∀ n, (W n).capTubeHasNeckChart eps) ∧
              ((∃ neck : ∀ n, LocalNeck G.flow eps x.val (τ n) (W n).domain.carrier,
                ∀ n, (W n).alternative = CanonicalAlternative.neck (neck n)) ∨
               ∃ cap : ∀ n, LocalCap G.flow eps x.val (τ n) (W n).domain.carrier,
                 ∃ depth : ∀ n, ∀ z ∈ (cap n).tube,
                   10000 / Real.sqrt (G.flow.scalar (τ n) x.val) ≤
                     metricDistance (G.flow.base.metric (τ n)) x.val z,
                   ∀ n, (W n).alternative = CanonicalAlternative.cap (cap n) (depth n)) := by
  obtain ⟨C, hC, hmain⟩ :=
    exists_uniform_canonical_constants_with_cap_neck_charts.{u} heps hsmall
  refine ⟨C, hC, ?_⟩
  intro P a s G
  obtain ⟨q, hq, hcanonical⟩ := hmain P a s G
  refine ⟨q, hq, ?_⟩
  intro L x hx hnoncompact
  have hhigh : ∀ᶠ t in 𝓝[<] s, q < G.flow.scalar t x.val :=
    (L.tendsto_metricScalarAt x).eventually (Ioi_mem_nhds hx)
  have hbranch := L.eventually_canonical_neck_or_cap_of_not_isCompact x hnoncompact eps C C
  exact exists_canonical_neck_or_cap_sequence_of_eventually
    (fun t ht hx => hcanonical x.val t ⟨ht.1.le, ht.2⟩ hx.le) hhigh hbranch

theorem TerminalLimitMetric.exists_canonical_neck_or_cap_sequence
    (L : G.TerminalLimitMetric) :
    ∃ epsCan : ℝ, 0 < epsCan ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsCan →
      ∃ C1 C2 q : ℝ, 1 ≤ C1 ∧ 1 ≤ C2 ∧ 0 < q ∧
        ∀ x y : G.terminalRegularOpen, q < metricScalarAt L.metric x →
          y.val ∈ connectedComponent x.val →
          C2 * metricScalarAt L.metric y < metricScalarAt L.metric x →
          ∃ τ : ℕ → ℝ, StrictMono τ ∧ (∀ n, τ n ∈ Ioo a s) ∧ Tendsto τ atTop (𝓝[<] s) ∧
            ∃ W : ∀ n, CanonicalWitness G.flow eps C1 C2 x.val (τ n),
              (∀ n, (W n).capTubeHasNeckChart eps) ∧
              ((∃ neck : ∀ n, LocalNeck G.flow eps x.val (τ n) (W n).domain.carrier,
                ∀ n, (W n).alternative = CanonicalAlternative.neck (neck n)) ∨
               ∃ cap : ∀ n, LocalCap G.flow eps x.val (τ n) (W n).domain.carrier,
                 ∃ depth : ∀ n, ∀ z ∈ (cap n).tube,
                   10000 / Real.sqrt (G.flow.scalar (τ n) x.val) ≤
                     metricDistance (G.flow.base.metric (τ n)) x.val z,
                   ∀ n, (W n).alternative = CanonicalAlternative.cap (cap n) (depth n)) := by
  refine ⟨1 / 44, by norm_num, ?_⟩
  intro eps heps hsmall
  obtain ⟨C, hC, hmain⟩ := exists_uniform_canonical_neck_or_cap_sequence.{u} heps
    (hsmall.trans_lt (by norm_num))
  obtain ⟨q, hq, hsequence⟩ := hmain P a s G
  exact ⟨C, C, q, hC, hC, hq, hsequence L⟩


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
