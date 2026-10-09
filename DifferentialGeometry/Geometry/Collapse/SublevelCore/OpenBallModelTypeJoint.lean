import DifferentialGeometry.Geometry.Collapse.SublevelCore.OpenBallModelTypeAtScale
import DifferentialGeometry.Geometry.Collapse.SublevelCore.CompactTransfer
import DifferentialGeometry.Geometry.Collapse.SublevelCore.PushedCollarMargin

/-!
# LC57/LC61 from LC56 at one fixed scale, either model branch

Master207A, A:23106 (LC57) and A:23460 (LC61): with LC56's data (A1 maps), for EITHER a compact or
a noncompact model `(N, g, n)` with `sec ≥ 0`, there is `R₀ > 0` such that for every `R ≥ R₀` one
tail has every open ball `B(p_i, ρ R)`, `ρ ∈ [1/5, 2]`, diffeomorphic to `N`.
* noncompact: `exists_scale_eventually_open_ball_model_type`;
* compact: the A1 maps are eventually global (the ball `B(n, D + 1)` is all of `N`), the `C⁰`
  convergence gives `j_i^* g_i ≤ 4 g`, so `j_i` is a diffeomorphism `N ≃ M_i`
  (`exists_diffeomorph_of_compactSpace`) and `d_i(p_i, ·) ≤ 2 D < ρ R` (`riemannianEDistOf_map_le_two_mul`):
  every such ball is all of `M_i`.

The instances of the sources carry names (`mM`, `rbM`, `rmM`, `hMc`, `crM`) so that a caller can pass
the normalized ones (`(mM i).rescale ρ_i⁻¹`, `radialScaledBundle`, …).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff ENNReal Topology NNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Manifold
open GC.MetricGeometry

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {N : Type} [m : MetricSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [SigmaCompactSpace N]
  [ConnectedSpace N] [RiemannianBundle (fun x : N => TangentSpace I x)]
  [IsRiemannianManifold I N] [hNc : CompleteSpace N]
  [IsContinuousRiemannianBundle E (fun x : N => TangentSpace I x)]
  [T2Space (TangentBundle I N)]
  {M : ℕ → Type} [mM : ∀ i, MetricSpace (M i)] [∀ i, ChartedSpace H (M i)]
  [∀ i, IsManifold I ∞ (M i)] [∀ i, SigmaCompactSpace (M i)] [∀ i, ConnectedSpace (M i)]
  [rbM : ∀ i, RiemannianBundle (fun x : M i => TangentSpace I x)]
  [rmM : ∀ i, IsRiemannianManifold I (M i)] [hMc : ∀ i, CompleteSpace (M i)]
  [crM : ∀ i, IsContinuousRiemannianBundle E (fun x : M i => TangentSpace I x)]

/-- **LC57/LC61 from LC56 at a fixed scale, either branch.** For a complete connected model with
`sec ≥ 0` (compact or not), LC56's data give `R₀ > 0` such that for every `R ≥ R₀` one tail has
every open ball `B(p_i, ρ R)`, `ρ ∈ [1/5, 2]`, diffeomorphic to `N`. -/
theorem exists_scale_eventually_open_ball_model_type_joint {mdim : ℕ}
    (hdim : Module.finrank ℝ E = mdim + 1) (g : SmoothRiemannianMetric I N)
    (hNorm : IsMetricNorm (I := I) (M := N) g) (hsec : ∀ x, SectionalBoundedBelowAt g x 0)
    (n : N) {C : Type} [MetricSpace C] {o : C} (Hc : RadialConeData o)
    (hcone : ∀ τ : ℝ, 0 < τ → τ < 1 → ∃ R₀ : ℝ, ∀ R : ℝ, ∀ hR : 0 < R, R₀ ≤ R →
      Nonempty (@KleinerLottApprox N C (m.rescale R⁻¹ (inv_pos.mpr hR)) _ n o τ))
    (gSeq : ∀ i, SmoothRiemannianMetric I (M i)) (hSeqNorm : ∀ i, IsMetricNorm (gSeq i))
    (j : ∀ i, PartialDiffeomorph I I N (M i) ∞)
    (hGH : PointedGHConverges (fun i => j i n) n)
    (hC1 : ∀ r : ℝ, 0 < r → ∃ i₀ : ℕ, ∃ hsub : ∀ k,
      ((⟨Metric.ball n r, Metric.isOpen_ball⟩ : TopologicalSpace.Opens N) : Set N) ⊆
        (j (k + i₀)).source,
      ∀ C : Set (⟨Metric.ball n r, Metric.isOpen_ball⟩ : TopologicalSpace.Opens N),
        IsCompact C → MetricCPConvergenceOn C 1
          (fun k => PartialDiffeomorph.pullbackMetricOn (j (k + i₀)) _ (hsub k) (gSeq (k + i₀)))
          (g.restrictOpen _) (g.restrictOpen _))
    (Hb : ℕ → ℝ) (hHb : Tendsto Hb atTop atTop)
    (hsecM : ∀ i, ∀ y ∈ Metric.ball (j i n) (Hb i),
      SectionalBoundedBelowAt (gSeq i) y (-((Hb i)⁻¹ ^ 2))) :
    ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, R₀ ≤ R → ∀ᶠ i in atTop, ∀ ρ ∈ Icc (1 / 5 : ℝ) 2,
      ∃ Ψ : PartialDiffeomorph I I (M i) N ∞,
        Ψ.source = Metric.ball (j i n) (ρ * R) ∧ Ψ.target = univ := by
  by_cases hcpt : CompactSpace N
  · -- compact model: the maps are eventually global diffeomorphisms
    obtain ⟨D₀, hD₀⟩ := (isCompact_univ (X := N)).isBounded.subset_closedBall n
    set D : ℝ := max D₀ 0 with hDdef
    have hD0 : 0 ≤ D := le_max_right _ _
    have hdist : ∀ x, dist x n ≤ D := fun x =>
      (Metric.mem_closedBall.mp (hD₀ (mem_univ x))).trans (le_max_left _ _)
    obtain ⟨i₀, hsub, hconv⟩ := hC1 (D + 1) (by positivity)
    have hUuniv : (Metric.ball n (D + 1) : Set N) = univ :=
      eq_univ_of_forall fun x => Metric.mem_ball.mpr (by linarith [hdist x])
    have hsrc : ∀ k, (j (k + i₀)).source = univ := fun k =>
      eq_univ_of_univ_subset (hUuniv ▸ hsub k)
    have hUc : IsCompact
        (univ : Set (⟨Metric.ball n (D + 1), Metric.isOpen_ball⟩ : TopologicalSpace.Opens N)) :=
      isCompact_iff_isCompact_univ.mp (by
        change IsCompact (Metric.ball n (D + 1) : Set N)
        rw [hUuniv]
        exact isCompact_univ)
    have hq := (metricCPConvergenceOn_zero_of_one hUc (hconv univ hUc)).eventually_quadratic_bounds
      hUc (by norm_num : (0 : ℝ) < 3)
    have hupk : ∀ᶠ k in atTop, ∀ z (v : TangentSpace I z),
        (gSeq (k + i₀)).inner (j (k + i₀) z) (mfderiv I I (j (k + i₀) : N → M (k + i₀)) z v)
          (mfderiv I I (j (k + i₀) : N → M (k + i₀)) z v) ≤ 4 * g.inner z v v := by
      filter_upwards [hq] with k hk z v
      have hz : z ∈ Metric.ball n (D + 1) := by rw [hUuniv]; exact mem_univ z
      have h := (hk ⟨z, hz⟩ (mem_univ _) v).2
      have hp := PartialDiffeomorph.pullbackMetricOn_inner (j (k + i₀))
        (⟨Metric.ball n (D + 1), Metric.isOpen_ball⟩ : TopologicalSpace.Opens N) (hsub k)
        (gSeq (k + i₀)) ⟨z, hz⟩ v v
      have hr : (g.restrictOpen (⟨Metric.ball n (D + 1), Metric.isOpen_ball⟩ :
          TopologicalSpace.Opens N)).inner ⟨z, hz⟩ v v = g.inner z v v := rfl
      rw [hp, hr] at h
      linarith
    refine ⟨10 * D + 1, by positivity, fun R hR => ?_⟩
    refine eventually_atTop_of_eventually_add_nat i₀ (P := fun i => ∀ ρ ∈ Icc (1 / 5 : ℝ) 2,
      ∃ Ψ : PartialDiffeomorph I I (M i) N ∞,
        Ψ.source = Metric.ball (j i n) (ρ * R) ∧ Ψ.target = univ) ?_
    filter_upwards [hupk] with k hk
    intro ρ hρ
    have : Nonempty N := ⟨n⟩
    obtain ⟨d, hd⟩ := exists_diffeomorph_of_compactSpace (j (k + i₀)) (hsrc k)
    refine ⟨d.symm.toPartialDiffeomorph, ?_, rfl⟩
    symm
    apply eq_univ_of_forall
    intro y
    obtain ⟨x, rfl⟩ : ∃ x, j (k + i₀) x = y := ⟨d.symm y, by rw [← hd, d.apply_symm_apply]⟩
    have hmap := riemannianEDistOf_map_le_two_mul g (gSeq (k + i₀)) (j (k + i₀)) (hsrc k) hk n x
    rw [riemannianEDistOf_eq_ofReal_dist (gSeq (k + i₀)) (hSeqNorm (k + i₀)),
      riemannianEDistOf_eq_ofReal_dist g hNorm] at hmap
    have hle : dist (j (k + i₀) n) (j (k + i₀) x) ≤ 2 * D := by
      have h3 : ENNReal.ofReal (dist (j (k + i₀) n) (j (k + i₀) x)) ≤ ENNReal.ofReal (2 * D) := by
        calc ENNReal.ofReal (dist (j (k + i₀) n) (j (k + i₀) x))
            ≤ 2 * ENNReal.ofReal (dist n x) := hmap
          _ = ENNReal.ofReal (2 * dist n x) := by
            rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
          _ ≤ ENNReal.ofReal (2 * D) := by
            apply ENNReal.ofReal_le_ofReal
            have := hdist x
            rw [dist_comm] at this
            linarith
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h3
    rw [Metric.mem_ball, dist_comm]
    have hρR : 2 * D < ρ * R := by nlinarith [hρ.1]
    linarith
  · have : NoncompactSpace N := not_compactSpace_iff.mp hcpt
    exact exists_scale_eventually_open_ball_model_type hdim g hNorm hsec n Hc hcone gSeq hSeqNorm j
      hGH hC1 Hb hHb hsecM

end DifferentialGeometry.Geometry.Collapse
