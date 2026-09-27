import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Limit.Metric.QuadraticBounds
import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphCurves
import DifferentialGeometry.Geometry.Comparison.HopfRinow.Proper
import DifferentialGeometry.Geometry.Compactness.SegmentTail

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter Set TopologicalSpace Bundle Manifold
open scoped Manifold ContDiff _root_.Topology NNReal ENNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : ℕ → Type*} [∀ j, MetricSpace (M j)] [∀ j, ChartedSpace H (M j)]
  [∀ j, IsManifold I ∞ (M j)]
  [∀ j, RiemannianBundle (fun z : M j => TangentSpace I z)]
  [∀ j, IsRiemannianManifold I (M j)]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem tendsto_dist_inverse_curve_of_chain_pullback_convergence
    (U : ∀ j, Opens (M j)) [∀ j, Nonempty (U j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) ∞)
    (hUstep : ∀ j, (U j : Set (M j)) ⊆ (Ψ j).source)
    (hmap : ∀ j, (Ψ j : M j → M (j + 1)) '' (U j : Set (M j)) ⊆
      (U (j + 1) : Set (M (j + 1))))
    (hU : ∀ j l, (U j : Set (M j)) ⊆ (chainComp Ψ j l).source)
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hgNorm : ∀ j, Geometry.Riemannian.IsMetricNorm (g j))
    (gInf gRef : ∀ j, SmoothRiemannianMetric I (U j))
    (hg : (SmoothSeqSystem.ofPartialDiffeomorphs U Ψ hUstep hmap).MetricCocycle gInf)
    [ConnectedSpace (SmoothSeqSystem.ofPartialDiffeomorphs U Ψ hUstep hmap).toSeqSystem.Lim]
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : ∀ j, ∀ K : Set (U j), IsCompact K → MetricCPConvergenceOn K 0
      (fun k => chainPullbackSeq Ψ g (U j) (hU j) (φ k - j)) (gInf j) (gRef j))
    (gamma : ∀ k, ℝ → M (φ k)) {a b : ℝ}
    (hgamma : ∀ C : ℝ≥0, 1 < C → ∀ᶠ k in atTop, LipschitzOnWith C (gamma k) (Icc a b))
    (hdist : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      Tendsto (fun k => dist (gamma k s) (gamma k t)) atTop (𝓝 (dist s t))) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    let S := SmoothSeqSystem.ofPartialDiffeomorphs U Ψ hUstep hmap
    letI : LocallyCompactSpace H := I.locallyCompactSpace
    letI : LocallyCompactSpace S.toSeqSystem.Lim :=
      ChartedSpace.locallyCompactSpace H S.toSeqSystem.Lim
    letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨(S.limitMetric gInf hg).toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨⟨(S.limitMetric gInf hg).inner, (S.limitMetric gInf hg).contMDiff.continuous, fun _ _ _ => rfl⟩⟩
    letI : MetricSpace S.toSeqSystem.Lim := Geometry.Riemannian.HopfRinow.riemMetricSpace (I := I)
    let Φ : ∀ k, PartialDiffeomorph I I S.toSeqSystem.Lim (M (φ k)) ∞ :=
      fun k => PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo (φ k)) rfl
    (∃ K : Set S.toSeqSystem.Lim, IsCompact K ∧ ∀ᶠ k in atTop,
      K ⊆ (Φ k).source ∧ MapsTo ((Φ k).symm ∘ gamma k) (Icc a b) K ∧
      ∀ s ∈ Icc a b, Φ k ((Φ k).symm (gamma k s)) = gamma k s) →
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      Tendsto (fun k => dist ((Φ k).symm (gamma k s)) ((Φ k).symm (gamma k t)))
        atTop (𝓝 (dist s t)) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let S := SmoothSeqSystem.ofPartialDiffeomorphs U Ψ hUstep hmap
  let G := S.limitMetric gInf hg
  let : LocallyCompactSpace H := I.locallyCompactSpace
  let : LocallyCompactSpace S.toSeqSystem.Lim :=
    ChartedSpace.locallyCompactSpace H S.toSeqSystem.Lim
  let : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨G.toRiemannianMetric⟩
  let : IsContinuousRiemannianBundle E (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
    ⟨⟨G.inner, G.contMDiff.continuous, fun _ _ _ => rfl⟩⟩
  let : MetricSpace S.toSeqSystem.Lim := Geometry.Riemannian.HopfRinow.riemMetricSpace (I := I)
  have : IsRiemannianManifold I S.toSeqSystem.Lim := ⟨fun _ _ => rfl⟩
  let Φ : ∀ k, PartialDiffeomorph I I S.toSeqSystem.Lim (M (φ k)) ∞ :=
    fun k => PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo (φ k)) rfl
  dsimp only
  intro htrap
  have hGNorm : Geometry.Riemannian.IsMetricNorm G :=
    Geometry.Riemannian.isMetricNorm_of_riemannianBundle G
  have hquad := eventually_quadratic_bounds_of_chain_pullback_convergence
    U Ψ hUstep hmap hU g gInf gRef hg φ hφ hconv
  have hderiv := eventually_enorm_mfderiv_le_of_chain_pullback_convergence
    U Ψ hUstep hmap hU g gInf gRef hg hGNorm hgNorm φ hφ hconv
  have hcompact : ∃ K : Set S.toSeqSystem.Lim, IsCompact K ∧ ∀ᶠ k in atTop,
      MapsTo ((Φ k).symm ∘ gamma k) (Icc a b) K := by
    obtain ⟨K, hK, hKmap⟩ := htrap
    exact ⟨K, hK, hKmap.mono fun k hk => hk.2.1⟩
  have htarget : ∀ᶠ k in atTop, MapsTo (gamma k) (Icc a b) (Φ k).target := by
    obtain ⟨K, _hK, hKmap⟩ := htrap
    filter_upwards [hKmap] with k hk
    intro s hs
    rw [← hk.2.2 s hs]
    exact (Φ k).map_source (hk.1 (hk.2.1 hs))
  apply PartialDiffeomorph.tendsto_dist_symm_curve_of_compact_metric_bounds
    Φ G (fun k => g (φ k)) hGNorm (fun k => hgNorm (φ k))
    (fun K hK ε hε => (hquad K hK ε hε).mono fun k hk =>
      ⟨hk.1, fun z hz v => (hk.2 z hz v).1⟩)
    (fun K hK L hL => (hderiv K hK L hL).mono fun k hk => hk.2)
    gamma hgamma htarget hcompact hdist

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem tendsto_dist_inverse_rescaled_segment_tail_of_chain_pullback_convergence
    (U : ∀ j, Opens (M j)) [∀ j, Nonempty (U j)]
    (Ψ : ∀ j, PartialDiffeomorph I I (M j) (M (j + 1)) ∞)
    (hUstep : ∀ j, (U j : Set (M j)) ⊆ (Ψ j).source)
    (hmap : ∀ j, (Ψ j : M j → M (j + 1)) '' (U j : Set (M j)) ⊆
      (U (j + 1) : Set (M (j + 1))))
    (hU : ∀ j l, (U j : Set (M j)) ⊆ (chainComp Ψ j l).source)
    (g : ∀ j, SmoothRiemannianMetric I (M j))
    (hgNorm : ∀ j, Geometry.Riemannian.IsMetricNorm (g j))
    (gInf gRef : ∀ j, SmoothRiemannianMetric I (U j))
    (hg : (SmoothSeqSystem.ofPartialDiffeomorphs U Ψ hUstep hmap).MetricCocycle gInf)
    [ConnectedSpace (SmoothSeqSystem.ofPartialDiffeomorphs U Ψ hUstep hmap).toSeqSystem.Lim]
    (φ : ℕ → ℕ) (hφ : StrictMono φ)
    (hconv : ∀ j, ∀ K : Set (U j), IsCompact K → MetricCPConvergenceOn K 0
      (fun k => chainPullbackSeq Ψ g (U j) (hU j) (φ k - j)) (gInf j) (gRef j))
    (gamma : ∀ k, ℝ → M k) (length start : ℕ → ℝ) {ell : ℝ} (hell : 0 < ell)
    (hstart : ∀ k, start k ∈ Icc 0 (length k))
    (hsegment : ∀ k, ∀ s ∈ Icc 0 (length k), ∀ t ∈ Icc 0 (length k),
      dist (gamma k s) (gamma k t) = |s - t|)
    (htail : Tendsto (fun k => length k - start k) atTop (𝓝 ell)) :
    letI : CompleteSpace E := FiniteDimensional.complete ℝ E
    let S := SmoothSeqSystem.ofPartialDiffeomorphs U Ψ hUstep hmap
    letI : LocallyCompactSpace H := I.locallyCompactSpace
    letI : LocallyCompactSpace S.toSeqSystem.Lim :=
      ChartedSpace.locallyCompactSpace H S.toSeqSystem.Lim
    letI : RiemannianBundle (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨(S.limitMetric gInf hg).toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun z : S.toSeqSystem.Lim => TangentSpace I z) :=
      ⟨⟨(S.limitMetric gInf hg).inner, (S.limitMetric gInf hg).contMDiff.continuous, fun _ _ _ => rfl⟩⟩
    letI : MetricSpace S.toSeqSystem.Lim := Geometry.Riemannian.HopfRinow.riemMetricSpace (I := I)
    let Φ : ∀ k, PartialDiffeomorph I I S.toSeqSystem.Lim (M k) ∞ :=
      fun k => PartialDiffeomorph.liftTargetOpen (S.inclPartialDiffeo k) rfl
    (∀ T : ℝ, 0 ≤ T → T < ell → ∃ K : Set S.toSeqSystem.Lim, IsCompact K ∧
      ∀ᶠ k in atTop, K ⊆ (Φ k).source ∧
        MapsTo ((Φ k).symm ∘ (fun s => gamma k (start k + (length k - start k) * s / ell)))
          (Icc (0 : ℝ) T) K ∧
        ∀ s ∈ Icc (0 : ℝ) T,
          Φ k ((Φ k).symm (gamma k (start k + (length k - start k) * s / ell))) =
            gamma k (start k + (length k - start k) * s / ell)) →
    ∀ s ∈ Ico 0 ell, ∀ t ∈ Ico 0 ell,
      Tendsto (fun k => dist
        ((Φ (φ k)).symm (gamma (φ k) (start (φ k) + (length (φ k) - start (φ k)) * s / ell)))
        ((Φ (φ k)).symm (gamma (φ k) (start (φ k) + (length (φ k) - start (φ k)) * t / ell))))
        atTop (𝓝 |s - t|) := by
  dsimp only
  intro htrap s hs t ht
  let T : ℝ := max s t
  have hT : 0 ≤ T := hs.1.trans (le_max_left s t)
  have hTell : T < ell := max_lt hs.2 ht.2
  have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs.1, le_max_left s t⟩
  have htT : t ∈ Icc (0 : ℝ) T := ⟨ht.1, le_max_right s t⟩
  have hgamma : ∀ C : ℝ≥0, 1 < C → ∀ᶠ k in atTop,
      LipschitzOnWith C
        (fun r => gamma (φ k) (start (φ k) + (length (φ k) - start (φ k)) * r / ell))
        (Icc (0 : ℝ) T) := by
    intro C hC
    exact (hφ.tendsto_atTop.eventually
      (Geometry.eventually_lipschitzOnWith_rescaled_segment_tail
        gamma length start hell hstart hsegment htail hC)).mono
      fun k hk => hk.mono (Icc_subset_Icc_right hTell.le)
  have hdist : ∀ u ∈ Icc (0 : ℝ) T, ∀ v ∈ Icc (0 : ℝ) T,
      Tendsto (fun k => dist
        (gamma (φ k) (start (φ k) + (length (φ k) - start (φ k)) * u / ell))
        (gamma (φ k) (start (φ k) + (length (φ k) - start (φ k)) * v / ell)))
        atTop (𝓝 (dist u v)) := by
    intro u hu v hv
    simpa only [Real.dist_eq, Function.comp_def] using
      (Geometry.tendsto_rescaled_segment_tail_dist gamma length start hell hstart hsegment htail
        (⟨hu.1, hu.2.trans hTell.le⟩ : u ∈ Icc 0 ell)
        (⟨hv.1, hv.2.trans hTell.le⟩ : v ∈ Icc 0 ell)).comp hφ.tendsto_atTop
  apply tendsto_dist_inverse_curve_of_chain_pullback_convergence
    U Ψ hUstep hmap hU g hgNorm gInf gRef hg φ hφ hconv
    (fun k r => gamma (φ k) (start (φ k) + (length (φ k) - start (φ k)) * r / ell))
    hgamma hdist _ s hsT t htT
  obtain ⟨K, hK, hKmap⟩ := htrap T hT hTell
  exact ⟨K, hK, hφ.tendsto_atTop.eventually hKmap⟩

end DifferentialGeometry.CheegerGromovCompactness
