import DifferentialGeometry.Geometry.Collapse.SelectedZeroPacketsOriginalBuffer
import DifferentialGeometry.Geometry.Collapse.RadialAnnularCutoff

/-!
# LPA05's selected zero packets and LPA06's zero cutoffs

Blueprint `master207A.tex`, LPA05 (`thm:collapse-simultaneous-selected-zero-packets`,
A:30548–30584) and the zero kind of LPA06 (`thm:collapse-simultaneous-finite-local-cover`,
A:30586–30660: "Zero cutoffs from LC31 are supported strictly within their selected radius balls:
their outer profile level is 9/10 and their value error is e < 1/40. Those balls are pairwise
disjoint", and "the zero tenth-radius balls lie inside the actual smooth cores, since
η < 1/10 + e < 1/5 there").

* `selected_zero_cutoffs`: the LC31 cutoffs of a disjoint selected family (kernel).
* `exists_selected_zero_packets_of_aligned_metric`: LCP04 transported from `inducedMetricSpace g`
  to any aligned metric (the standing-sequence convention `mX i` + `hmetric`), via
  `MetricSpace.ext` and `subst`; LC73's clause is not transported (see its docstring).
* `exists_selected_zero_packets_with_cutoffs`: LPA05's post-selection content with ONE global
  zero-scale buffer, together with the zero cutoffs.

The witnesses at every centre (LPA02), LFR54's sublevel types and the selected LC61 identifications
are NOT produced here: LPA02 needs LFR49, LFR54 is not started (sheet `sheet-F8-LPA.md`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Metric
open scoped Topology ContDiff Manifold ENNReal
open GC.MetricGeometry
open DifferentialGeometry
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Comparison.Toponogov
open DifferentialGeometry.Geometry.Topology
open DifferentialGeometry.Analysis.Calculus

namespace DifferentialGeometry.Geometry.Collapse

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

universe u v uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
/-- **LPA06, zero kind (kernel).** For a family `J` of centres with pairwise disjoint balls
`B(i, r_i)` and, at every selected centre, a radial function `η_i` with LC31's inputs at scale
`r_i` (continuous, smooth on an open `O_i ⊇ η_i⁻¹[1/5, 9/10]`, value error
`|η_i − d(·,i)/r_i| < e` with `e < 1/40`, gradient at most `1 + ε` in `r_i⁻² g` on the band),
the LC31 cutoffs `ζ_i = Φ ∘ η_i` are smooth, `[0,1]`-valued, equal to one on
`η_i ∈ [3/10, 4/5]`, have closed support in `{(1/5 − e) r_i < d(·,i) < (9/10 + e) r_i}`, hence
strictly inside `B(i, r_i)` and compact, have gradient at most `L (1 + ε)` in `r_i⁻² g` for ONE
`L`, the tenth ball `B(i, r_i/10)` lies in `{η_i < 1/5}`, and the closed supports are pairwise
disjoint. -/
theorem selected_zero_cutoffs {M : Type u} [MetricSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [ProperSpace M] (g : SmoothRiemannianMetric I M) (J : Set M)
    (r : M → ℝ) (hr : ∀ i, 0 < r i) (hdisj : J.PairwiseDisjoint fun i => ball i (r i))
    (η : M → M → ℝ) (O : M → Set M) {ε e : ℝ} (hε : 0 ≤ ε) (he : e < 1 / 40)
    (hηc : ∀ i ∈ J, Continuous (η i)) (hO : ∀ i ∈ J, IsOpen (O i))
    (hηO : ∀ i ∈ J, ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (η i) (O i))
    (hband : ∀ i ∈ J, η i ⁻¹' Icc (1 / 5 : ℝ) (9 / 10) ⊆ O i)
    (hclose : ∀ i ∈ J, ∀ x, |η i x - (r i)⁻¹ * dist x i| < e)
    (hgrad : ∀ i ∈ J, ∀ q ∈ η i ⁻¹' Icc (1 / 5 : ℝ) (9 / 10),
      Real.sqrt ((scaleMetric ((r i)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hr i)) 2) g).inner q
        (gradFun (scaleMetric ((r i)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hr i)) 2) g) (η i) q)
        (gradFun (scaleMetric ((r i)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hr i)) 2) g) (η i) q)) ≤
        1 + ε) :
    ∃ L : ℝ, 0 ≤ L ∧
      (∀ i ∈ J,
        let ζ : M → ℝ := fun x => annularCutoff cutoffProfile (η i x)
        let gr := scaleMetric ((r i)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hr i)) 2) g
        ContMDiff I 𝓘(ℝ, ℝ) ∞ ζ ∧ (∀ x, ζ x ∈ Icc (0 : ℝ) 1) ∧
        (∀ x, η i x ∈ Icc (3 / 10 : ℝ) (4 / 5) → ζ x = 1) ∧
        tsupport ζ ⊆ {x | (1 / 5 - e) * r i < dist x i ∧ dist x i < (9 / 10 + e) * r i} ∧
        tsupport ζ ⊆ ball i (r i) ∧ HasCompactSupport ζ ∧
        (∀ q, Real.sqrt (gr.inner q (gradFun gr ζ q) (gradFun gr ζ q)) ≤ L * (1 + ε)) ∧
        ball i (r i / 10) ⊆ {x | η i x < 1 / 5}) ∧
      J.PairwiseDisjoint fun i => tsupport fun x => annularCutoff cutoffProfile (η i x) := by
  obtain ⟨L, hL0, hL⟩ := exists_abs_deriv_annularCutoff_le cutoffProfile_contDiff
    (fun t ht => cutoffProfile_eq_zero ht)
  have key : ∀ i ∈ J,
      let ζ : M → ℝ := fun x => annularCutoff cutoffProfile (η i x)
      let gr := scaleMetric ((r i)⁻¹ ^ 2) (pow_pos (inv_pos.mpr (hr i)) 2) g
      ContMDiff I 𝓘(ℝ, ℝ) ∞ ζ ∧ (∀ x, ζ x ∈ Icc (0 : ℝ) 1) ∧
      (∀ x, η i x ∈ Icc (3 / 10 : ℝ) (4 / 5) → ζ x = 1) ∧
      tsupport ζ ⊆ {x | (1 / 5 - e) * r i < dist x i ∧ dist x i < (9 / 10 + e) * r i} ∧
      tsupport ζ ⊆ ball i (r i) ∧ HasCompactSupport ζ ∧
      (∀ q, Real.sqrt (gr.inner q (gradFun gr ζ q) (gradFun gr ζ q)) ≤ L * (1 + ε)) ∧
      ball i (r i / 10) ⊆ {x | η i x < 1 / 5} := by
    intro i hi ζ gr
    have hri := hr i
    have h31 := by
      letI : MetricSpace M := (inferInstance : MetricSpace M).rescale (r i)⁻¹ (inv_pos.mpr hri)
      exact annularCutoff_comp_radial (I := I) cutoffProfile_contDiff cutoffProfile_mem_Icc
        (fun t ht => cutoffProfile_eq_one ht) (fun t ht => cutoffProfile_eq_zero ht) gr i
        hε (hηc i hi) (hO i hi) (hηO i hi) (hband i hi) (hclose i hi) (hgrad i hi) hL
    obtain ⟨hsm, hrange, hone, hsupp, hgr⟩ := h31
    have hsupp' : tsupport ζ ⊆
        {x | (1 / 5 - e) * r i < dist x i ∧ dist x i < (9 / 10 + e) * r i} := by
      intro x hx
      obtain ⟨h1, h2⟩ := hsupp hx
      have h1' : 1 / 5 - e < (r i)⁻¹ * dist x i := h1
      have h2' : (r i)⁻¹ * dist x i < 9 / 10 + e := h2
      rw [inv_mul_eq_div, lt_div_iff₀ hri] at h1'
      rw [inv_mul_eq_div, div_lt_iff₀ hri] at h2'
      exact ⟨h1', h2'⟩
    have hball : tsupport ζ ⊆ ball i (r i) := by
      intro x hx
      rw [mem_ball]
      have h := (hsupp' hx).2
      nlinarith
    refine ⟨hsm, hrange, hone, hsupp', hball, ?_, hgr, ?_⟩
    · exact IsCompact.of_isClosed_subset (isCompact_closedBall i (r i)) (isClosed_tsupport _)
        (hball.trans ball_subset_closedBall)
    · intro x hx
      rw [mem_ball] at hx
      have h := abs_lt.mp (hclose i hi x)
      have hd : (r i)⁻¹ * dist x i < 1 / 10 := by
        rw [inv_mul_eq_div, div_lt_iff₀ hri]
        linarith
      change η i x < 1 / 5
      linarith [h.2]
  refine ⟨L, hL0, key, ?_⟩
  exact hdisj.mono_on fun i hi => (key i hi).2.2.2.2.1

/-- **LCP04 for an aligned metric.** LCP04 (`exists_selected_zero_packets_of_original_buffer`)
for ANY metric space structure `m` whose distance is the real form of the `g`-length distance,
with the original buffer stated on `m`-balls. The LC73 clause is not included: it installs
`radialScaledManifold`, whose type requires the ambient topology to BE the metric's, so it cannot
be transported by `subst` (it stays available for `inducedMetricSpace g` in LCP04 itself). -/
theorem exists_selected_zero_packets_of_aligned_metric (hE : Module.finrank ℝ E = 3)
    {β : ℕ → ℝ} (hβ : 0 < β 1) (hβone : β 1 < 1) {ζ : ℝ} (hβζ : β 1 < ζ) (hζone : ζ < 1) :
    ∃ ε δ' Λ' : ℝ, 0 < ε ∧ ε < 1 / 4 ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T3Space M]
        [SigmaCompactSpace M] [ConnectedSpace M] [CompactSpace M]
        (g : SmoothRiemannianMetric I M) (m : MetricSpace M),
      (∀ a b : M, riemannianEDistOf (I := I) g a b = ENNReal.ofReal (@dist M m.toDist a b)) →
      letI := m
      ∀ (N C : M → Type v) [mN : ∀ i, MetricSpace (N i)] [∀ i, ProperSpace (N i)]
        [mC : ∀ i, MetricSpace (C i)] [∀ i, ProperSpace (C i)]
        (n₀ : ∀ i, N i) (o : ∀ i, C i), (∀ i, RadialConeData (o i)) →
      ∀ (δ : M → ℝ) (η : M → M → ℝ) (r ρ : M → ℝ), Continuous ρ →
      ∀ (hρpos : ∀ p, 0 < ρ p) {T U : ℝ} (hT : 0 < T), 20 * Λ' ≤ T → T ≤ U →
      ∀ (hlower : ∀ p, T * ρ p ≤ r p), (∀ p, r p ≤ U * ρ p) →
      ∃ J : Set M, J.Finite ∧ J.PairwiseDisjoint (fun i => ball i (r i)) ∧
        (∀ i ∈ J, (ball i (r i) ∩
          {q | @splittingRank.{u, 0} M (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 = 0}
          ).Nonempty) ∧
        (∀ i ∈ J, ∀ q, dist i q ≤ 10 * r i → r q ≤ 20 * r i ∧ T / 20 ≤ r i / ρ q) ∧
        ((∀ i ∈ J,
            (∀ y ∈ ball i (400 * r i),
              SectionalBoundedBelowAt g y (-((1 / 60) ^ 2 * (r i)⁻¹ ^ 2))) ∧
            fourPointComparison 0 (univ : Set (N i)) ∧
            (∀ x y : N i, ∃ f : Icc (0 : ℝ) 1 → N i,
              Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
              ∀ s t, dist (f s) (f t) = dist x y * dist s t) ∧
            (∀ δ₁ : ℝ, 0 < δ₁ → δ₁ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ,
              R₀ ≤ R → ∀ hR : 0 < R, Nonempty (@KleinerLottApprox (N i) (C i)
                ((mN i).rescale R⁻¹ (inv_pos.mpr hR)) (mC i) (n₀ i) (o i) δ₁)) ∧
            δ i < δ' ∧
            Nonempty (@KleinerLottApprox M (C i)
              (m.rescale (r i)⁻¹ (inv_pos.mpr ((mul_pos hT (hρpos i)).trans_le (hlower i))))
              (mC i) i (o i) (δ i)) ∧
            ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (η i)
              {x | 3 / 40 ≤ (r i)⁻¹ * dist x i ∧ (r i)⁻¹ * dist x i ≤ 11} ∧
            ∀ x y, |(η i x - (r i)⁻¹ * dist i x) - (η i y - (r i)⁻¹ * dist i y)| ≤
              ε * ((r i)⁻¹ * dist x y)) →
          (∀ i ∈ J, ∀ q, r i / 10 ≤ dist i q → dist i q ≤ 10 * r i →
            @HasEuclideanSplitting.{u, 0} M (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q 1
              (β 1) ∧
            @splittingRank.{u, 0} M (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 ≠ 0) ∧
          {q | @splittingRank.{u, 0} M (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 = 0} ⊆
            ⋃ i ∈ J, ball i (r i / 10) ∧
          (∀ i ∈ J, ∀ q, r i / 10 ≤ dist i q → dist i q ≤ 10 * r i →
            ∃ (Z : Type) (mZ : MetricSpace Z), letI := mZ
              ∃ (z : Z) (F : @KleinerLottApprox M
                (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Z))
                (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) inferInstance
                q (WithLp.toLp 2 (0, z)) (β 1)),
                ∀ x : M, (@KleinerLottApprox.toFun M
                  (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Z))
                  (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) inferInstance
                  q (WithLp.toLp 2 (0, z)) (β 1) F x).fst = WithLp.toLp 2
                  (Function.const (Fin 1) ((ρ q)⁻¹ * (dist i x - dist i q)))) ∧
          ∀ i ∈ J, ∀ K : Set (N i), IsCompact K → ∀ a b : N i,
            ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a) →
            ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b) →
            connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ b) := by
  obtain ⟨ε, δ', Λ', hε, hε4, hδ', hΛ', h⟩ :=
    exists_selected_zero_packets_of_original_buffer.{u, v} (E := E) (H := H) (I := I) hE hβ hβone
      hβζ hζone
  refine ⟨ε, δ', Λ', hε, hε4, hδ', hΛ', ?_⟩
  intro M _ _ _ _ _ _ _ g m hm
  have hmeq : m = inducedMetricSpace g := by
    apply MetricSpace.ext
    change (⟨fun a b => @dist M m.toDist a b⟩ : Dist M) =
      ⟨fun a b => @dist M (inducedMetricSpace g).toDist a b⟩
    congr 1
    funext a b
    rw [inducedMetricSpace_dist, hm a b,
      ENNReal.toReal_ofReal (@dist_nonneg M m.toPseudoMetricSpace a b)]
  subst hmeq
  intro N C mN _ mC _ n₀ o H δ η r ρ hρ hρpos T U hT hTΛ hTU hlower hupper
  obtain ⟨J, hfin, hdisj, hmeet, hloc, himp⟩ :=
    h M g N C n₀ o H δ η r ρ hρ hρpos hT hTΛ hTU hlower hupper
  refine ⟨J, hfin, hdisj, hmeet, hloc, fun hdata => ?_⟩
  obtain ⟨h1, h2, h3, -, h5⟩ := himp fun i hi => ⟨fun y hy => (hdata i hi).1 y (by
    rw [inducedMetricSpace_ball g]; exact hy), (hdata i hi).2⟩
  exact ⟨h1, h2, h3, h5⟩


/-- **LPA05 kernel with LPA06's zero cutoffs.** On a closed connected manifold `M` with an aligned
metric, for every `r` with `T ρ ≤ r ≤ U ρ` and ONE curvature buffer `sec ≥ −(1/60)² r(p)⁻²` on
`B(p, 400 r(p))` at every point (on the LPA04 tail this is LPA01's zero-scale clause, see
`SharedInteriorAssignment`), and for ANY families of models, cones, maps and radial functions fixed
before the selection: one LC66 selection `J` (finite, disjoint `r`-balls meeting the zero stratum,
LC62 locality) such that, under the original data at the selected centres, LC80's shell splitting,
tenth-radius cover of the zero stratum, ORIGINAL radial coordinate and LC77's end count hold for
the SAME data, and the LC31 cutoffs of the SAME radial functions have the conclusions of
`selected_zero_cutoffs` (disjoint closed supports strictly inside the selected balls). -/
theorem exists_selected_zero_packets_with_cutoffs (hE : Module.finrank ℝ E = 3)
    {β : ℕ → ℝ} (hβ : 0 < β 1) (hβone : β 1 < 1) {ζ : ℝ} (hβζ : β 1 < ζ) (hζone : ζ < 1) :
    ∃ ε δ' Λ' : ℝ, 0 < ε ∧ ε < 1 / 4 ∧ 0 < δ' ∧ 0 < Λ' ∧
      ∀ (M : Type u) [m : MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
        [ConnectedSpace M] [CompactSpace M] (g : SmoothRiemannianMetric I M),
      (∀ a b : M, riemannianEDistOf (I := I) g a b = ENNReal.ofReal (dist a b)) →
      ∀ (r ρ : M → ℝ), Continuous ρ →
      ∀ (hρpos : ∀ p, 0 < ρ p) {T U : ℝ} (hT : 0 < T), 20 * Λ' ≤ T → T ≤ U →
      ∀ (hlower : ∀ p, T * ρ p ≤ r p), (∀ p, r p ≤ U * ρ p) →
      (∀ p, ∀ y ∈ ball p (400 * r p),
        SectionalBoundedBelowAt g y (-((1 / 60) ^ 2 * (r p)⁻¹ ^ 2))) →
      ∀ (N C : M → Type v) [mN : ∀ i, MetricSpace (N i)] [∀ i, ProperSpace (N i)]
        [mC : ∀ i, MetricSpace (C i)] [∀ i, ProperSpace (C i)]
        (n₀ : ∀ i, N i) (o : ∀ i, C i), (∀ i, RadialConeData (o i)) →
      ∀ (δ : M → ℝ) (η : M → M → ℝ) (O : M → Set M) {e : ℝ}, e < 1 / 40 →
      ∃ J : Set M, J.Finite ∧ J.PairwiseDisjoint (fun i => ball i (r i)) ∧
        (∀ i ∈ J, (ball i (r i) ∩
          {q | @splittingRank.{u, 0} M (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 = 0}
          ).Nonempty) ∧
        (∀ i ∈ J, ∀ q, dist i q ≤ 10 * r i → r q ≤ 20 * r i ∧ T / 20 ≤ r i / ρ q) ∧
        ((∀ i ∈ J,
            fourPointComparison 0 (univ : Set (N i)) ∧
            (∀ x y : N i, ∃ f : Icc (0 : ℝ) 1 → N i,
              Continuous f ∧ f ⟨0, by norm_num⟩ = x ∧ f ⟨1, by norm_num⟩ = y ∧
              ∀ s t, dist (f s) (f t) = dist x y * dist s t) ∧
            (∀ δ₁ : ℝ, 0 < δ₁ → δ₁ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ,
              R₀ ≤ R → ∀ hR : 0 < R, Nonempty (@KleinerLottApprox (N i) (C i)
                ((mN i).rescale R⁻¹ (inv_pos.mpr hR)) (mC i) (n₀ i) (o i) δ₁)) ∧
            δ i < δ' ∧
            Nonempty (@KleinerLottApprox M (C i)
              (m.rescale (r i)⁻¹ (inv_pos.mpr ((mul_pos hT (hρpos i)).trans_le (hlower i))))
              (mC i) i (o i) (δ i)) ∧
            ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (η i)
              {x | 3 / 40 ≤ (r i)⁻¹ * dist x i ∧ (r i)⁻¹ * dist x i ≤ 11} ∧
            (∀ x y, |(η i x - (r i)⁻¹ * dist i x) - (η i y - (r i)⁻¹ * dist i y)| ≤
              ε * ((r i)⁻¹ * dist x y)) ∧
            Continuous (η i) ∧ IsOpen (O i) ∧ ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (η i) (O i) ∧
            η i ⁻¹' Icc (1 / 5 : ℝ) (9 / 10) ⊆ O i ∧
            (∀ x, |η i x - (r i)⁻¹ * dist x i| < e) ∧
            ∀ q ∈ η i ⁻¹' Icc (1 / 5 : ℝ) (9 / 10),
              Real.sqrt ((scaleMetric ((r i)⁻¹ ^ 2) (pow_pos (inv_pos.mpr
                ((mul_pos hT (hρpos i)).trans_le (hlower i))) 2) g).inner q
                (gradFun (scaleMetric ((r i)⁻¹ ^ 2) (pow_pos (inv_pos.mpr
                  ((mul_pos hT (hρpos i)).trans_le (hlower i))) 2) g) (η i) q)
                (gradFun (scaleMetric ((r i)⁻¹ ^ 2) (pow_pos (inv_pos.mpr
                  ((mul_pos hT (hρpos i)).trans_le (hlower i))) 2) g) (η i) q)) ≤ 1 + ε) →
          (∀ i ∈ J, ∀ q, r i / 10 ≤ dist i q → dist i q ≤ 10 * r i →
            @HasEuclideanSplitting.{u, 0} M (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q 1
              (β 1) ∧
            @splittingRank.{u, 0} M (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 ≠ 0) ∧
          {q | @splittingRank.{u, 0} M (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) q β 3 = 0} ⊆
            ⋃ i ∈ J, ball i (r i / 10) ∧
          (∀ i ∈ J, ∀ q, r i / 10 ≤ dist i q → dist i q ≤ 10 * r i →
            ∃ (Z : Type) (mZ : MetricSpace Z), letI := mZ
              ∃ (z : Z) (F : @KleinerLottApprox M
                (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Z))
                (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) inferInstance
                q (WithLp.toLp 2 (0, z)) (β 1)),
                ∀ x : M, (@KleinerLottApprox.toFun M
                  (WithLp 2 (EuclideanSpace ℝ (Fin 1) × Z))
                  (m.rescale (ρ q)⁻¹ (inv_pos.mpr (hρpos q))) inferInstance
                  q (WithLp.toLp 2 (0, z)) (β 1) F x).fst = WithLp.toLp 2
                  (Function.const (Fin 1) ((ρ q)⁻¹ * (dist i x - dist i q)))) ∧
          (∀ i ∈ J, ∀ K : Set (N i), IsCompact K → ∀ a b : N i,
            ¬ Bornology.IsBounded (connectedComponentIn Kᶜ a) →
            ¬ Bornology.IsBounded (connectedComponentIn Kᶜ b) →
            connectedComponentIn Kᶜ a = connectedComponentIn Kᶜ b) ∧
          ∃ L : ℝ, 0 ≤ L ∧
            (∀ i ∈ J,
              let ζi : M → ℝ := fun x => annularCutoff cutoffProfile (η i x)
              let gr := scaleMetric ((r i)⁻¹ ^ 2) (pow_pos (inv_pos.mpr
                ((mul_pos hT (hρpos i)).trans_le (hlower i))) 2) g
              ContMDiff I 𝓘(ℝ, ℝ) ∞ ζi ∧ (∀ x, ζi x ∈ Icc (0 : ℝ) 1) ∧
              (∀ x, η i x ∈ Icc (3 / 10 : ℝ) (4 / 5) → ζi x = 1) ∧
              tsupport ζi ⊆
                {x | (1 / 5 - e) * r i < dist x i ∧ dist x i < (9 / 10 + e) * r i} ∧
              tsupport ζi ⊆ ball i (r i) ∧ HasCompactSupport ζi ∧
              (∀ q, Real.sqrt (gr.inner q (gradFun gr ζi q) (gradFun gr ζi q)) ≤ L * (1 + ε)) ∧
              ball i (r i / 10) ⊆ {x | η i x < 1 / 5}) ∧
            J.PairwiseDisjoint fun i => tsupport fun x => annularCutoff cutoffProfile (η i x)) := by
  obtain ⟨ε, δ', Λ', hε, hε4, hδ', hΛ', h⟩ :=
    exists_selected_zero_packets_of_aligned_metric.{u, v} (E := E) (H := H) (I := I) hE hβ hβone
      hβζ hζone
  refine ⟨ε, δ', Λ', hε, hε4, hδ', hΛ', ?_⟩
  intro M m _ _ _ _ g hmetric r ρ hρ hρpos T U hT hTΛ hTU hlower hupper hsec N C mN _ mC _ n₀ o
    H δ η O e he
  have hr : ∀ p, 0 < r p := fun p => (mul_pos hT (hρpos p)).trans_le (hlower p)
  obtain ⟨J, hfin, hdisj, hmeet, hloc, himp⟩ :=
    h M g m hmetric N C n₀ o H δ η r ρ hρ hρpos hT hTΛ hTU hlower hupper
  refine ⟨J, hfin, hdisj, hmeet, hloc, fun hdata => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := himp fun i hi => by
    obtain ⟨d1, d2, d3, d4, d5, d6, d7, -⟩ := hdata i hi
    exact ⟨hsec i, d1, d2, d3, d4, d5, d6, d7⟩
  refine ⟨h1, h2, h3, h4, ?_⟩
  exact selected_zero_cutoffs g J r hr hdisj η O hε.le he
    (fun i hi => (hdata i hi).2.2.2.2.2.2.2.1)
    (fun i hi => (hdata i hi).2.2.2.2.2.2.2.2.1)
    (fun i hi => (hdata i hi).2.2.2.2.2.2.2.2.2.1)
    (fun i hi => (hdata i hi).2.2.2.2.2.2.2.2.2.2.1)
    (fun i hi => (hdata i hi).2.2.2.2.2.2.2.2.2.2.2.1)
    (fun i hi => (hdata i hi).2.2.2.2.2.2.2.2.2.2.2.2)


end DifferentialGeometry.Geometry.Collapse
