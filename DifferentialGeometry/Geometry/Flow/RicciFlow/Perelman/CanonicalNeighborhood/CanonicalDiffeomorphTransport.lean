import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.DiffeomorphComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NeckLimitTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalCapTransport
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalToleranceMonotone
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.Restriction

set_option autoImplicit false
noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem StrongNeck.eventually_transport_of_diffeomorph_tendsto
    {S : SolutionOn (I := I3) (M := M) ancientTimeInterval} (hS : IsSolutionOn S)
    {eps alpha : ℝ} {x : M} (nk : StrongNeck S eps x 0)
    (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11)
    (heps : eps < neckModelTolerance alpha)
    (Y : P → M ≃ₘ⟮I3, I3⟯ M)
    (hY : ContMDiff (𝓘(ℝ, P).prod I3) I3 ∞ (fun p : P × M => Y p.1 p.2))
    {p₀ : P} (hY₀ : Y p₀ = _root_.Diffeomorph.refl I3 M ∞)
    (τ : ℕ → P) (hτ : Tendsto τ atTop (𝓝 p₀)) :
    ∀ᶠ n in atTop, ∃ nk' : StrongNeck S (2 * alpha) (Y (τ n) x) 0,
      nk'.map = partialDiffeomorphTransMixed nk.map (Y (τ n)).toPartialDiffeomorph := by
  let B : Set Cylinder := univ ×ˢ Icc (-alpha⁻¹) alpha⁻¹
  have hB : IsCompact B := isCompact_univ.prod isCompact_Icc
  have hrad : alpha⁻¹ < eps⁻¹ :=
    inv_strictAnti₀ nk.eps_pos (heps.trans_le (neckModelTolerance_le alpha))
  have hBsource : B ⊆ nk.map.source := by
    intro y hy
    exact nk.domain ⟨hy.1, by linarith [hy.2.1], by linarith [hy.2.2]⟩
  let K := nk.map '' B
  have hK : IsCompact K := hB.image_of_continuousOn
    (nk.map.contMDiffOn_toFun.continuousOn.mono hBsource)
  let _ : LocallyCompactSpace M := ChartedSpace.locallyCompactSpace ThreeSpace M
  let _ : RegularSpace M := inferInstance
  obtain ⟨U, hUopen, hKU, _hUuniv, hUcompact⟩ :=
    exists_open_between_and_isCompact_closure hK isOpen_univ (subset_univ K)
  let U' : TopologicalSpace.Opens M := ⟨U, hUopen⟩
  let nk0 := nk.mono heps.le
    ((neckModelTolerance_le alpha).trans_lt (by linarith : alpha < 1 / 11))
  have houter : ∀ y ∈ univ ×ˢ Ioo (-alpha⁻¹) alpha⁻¹, nk0.map y ∈ K := by
    intro y hy
    exact ⟨y, ⟨hy.1, hy.2.1.le, hy.2.2.le⟩, rfl⟩
  apply nk0.eventually_transport_of_comparisons hS ha hsmall U' hUcompact hK hKU houter
    (fun _ => S) (fun _ => hS) (fun n => (Y (τ n)).toPartialDiffeomorph)
  · exact Eventually.of_forall (fun _ => subset_univ _)
  · intro A _hA
    exact Eventually.of_forall (fun _ => ⟨fun _ ht => ht.2, fun _ ht => ht.2⟩)
  · intro A hA order delta hdelta
    let D := RealTimeInterval.closed (-A - 1) 0 (by linarith)
    have hwin : IsSolutionOn (S.timeRestrict D) :=
      isSolutionOn_timeRestrict hS (fun _ ht => ht.2) (fun _ ht => ht.2)
    have hc := eventually_metricComparisonOn_of_diffeomorph_tendsto
      (S.timeRestrict D) hwin (a := -A - 1) (c := -A) (b := 0)
      (by linarith) (by linarith) rfl (Subset.rfl) Y hY hY₀ τ hτ
      (uniqueDiffOn_Icc (by linarith : -A < 0)) (Subset.rfl) hUcompact order hdelta
    filter_upwards [hc] with n hn
    obtain ⟨C⟩ := hn
    exact ⟨C.mono subset_closure le_rfl le_rfl⟩

theorem LocalCap.eventually_transport_of_diffeomorph_tendsto
    {S : SolutionOn (I := I3) (M := M) ancientTimeInterval} (hS : IsSolutionOn S)
    {eps alpha : ℝ} {x : M} {U : Set M} (cap : LocalCap S eps x 0 U)
    (ha : 0 < alpha) (hsmall : 2 * alpha < 1 / 11)
    (heps : eps < neckModelTolerance alpha)
    (Y : P → M ≃ₘ⟮I3, I3⟯ M)
    (hY : ContMDiff (𝓘(ℝ, P).prod I3) I3 ∞ (fun p : P × M => Y p.1 p.2))
    {p₀ : P} (hY₀ : Y p₀ = _root_.Diffeomorph.refl I3 M ∞)
    (τ : ℕ → P) (hτ : Tendsto τ atTop (𝓝 p₀)) :
    ∀ᶠ n in atTop, ∃ cap' : LocalCap S (2 * alpha) (Y (τ n) x) 0 (Y (τ n) '' U),
      cap'.tube = Y (τ n) '' cap.tube ∧
      cap'.core.carrier = Y (τ n) '' cap.core.carrier ∧
      cap'.tube_map = cap.tube_map.trans (Y (τ n)).toPartialDiffeomorph := by
  classical
  have hnecks : ∀ j : Fin cap.chain.count, ∀ᶠ n in atTop,
      ∃ nk : StrongNeck S (2 * alpha) (Y (τ n) (cap.chain.centers j)) 0,
        nk.map = partialDiffeomorphTransMixed (cap.chain.necks j).map
          (Y (τ n)).toPartialDiffeomorph := by
    intro j
    exact StrongNeck.eventually_transport_of_diffeomorph_tendsto hS
      (cap.chain.necks j) ha hsmall heps Y hY hY₀ τ hτ
  have htol : eps ≤ 2 * alpha :=
    heps.le.trans ((neckModelTolerance_le alpha).trans (by linarith))
  filter_upwards [eventually_all.mpr hnecks] with n hn
  choose necks hmap using hn
  exact ⟨LocalCap.mapOfNeckFamily (cap.mono_eps htol hsmall)
    (Y (τ n)).toPartialDiffeomorph (subset_univ U) necks (fun j => hmap j), rfl, rfl, rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
