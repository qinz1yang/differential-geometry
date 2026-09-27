import DifferentialGeometry.Geometry.Comparison.Variation.EndpointParallel
import DifferentialGeometry.Geometry.Comparison.Variation.ExponentialEndpoint

noncomputable section

namespace DifferentialGeometry.Geometry.Riemannian.Variation

open Bundle Filter Set
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open scoped ContDiff Manifold Topology

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_smooth_tail_variation_with_geodesic_endpoint
    (g : SmoothRiemannianMetric I M) (gamma beta : ℝ → M) {c b : ℝ}
    (hcb : c < b) (hgamma : ContMDiff 𝓘(ℝ, ℝ) I ∞ gamma)
    (hbeta : IsGeodesicAt (I := I) g beta 0) (hbeta0 : beta 0 = gamma b)
    :
    ∃ f : ℝ → ℝ → M,
      IsSmoothVariation (I := I) f ∧
      (∀ s ∈ Icc c b, f 0 =ᶠ[𝓝 s] gamma) ∧
      (∀ u, f u c = gamma c) ∧
      (fun u ↦ f u b) =ᶠ[𝓝 (0 : ℝ)] beta := by
  let L := b - c
  have hL : 0 < L := sub_pos.mpr hcb
  let delta : ℝ → M := fun s ↦ gamma (c + s)
  have hdelta : ContMDiff 𝓘(ℝ, ℝ) I ∞ delta :=
    hgamma.comp (contMDiff_const.add contMDiff_id)
  let v : E := mfderiv 𝓘(ℝ, ℝ) I beta 0 (1 : ℝ)
  have hdeltaL : delta L = gamma b := by simp [delta, L]
  obtain ⟨Gamma, V, _hVtotal, hGamma, hGammaGerm, hterminalV,
      _hVdiff, _hVpar, _hVunit, W, hWtotal, hWradial, _hWcov,
      K, hKcompact, hWmem⟩ :=
    exists_smooth_parallel_field_with_terminal
      g delta hdelta L hL v
  obtain ⟨_eta, f0, _hetaSmooth, _hetaId, _hetaBound, hf0, hfcentral,
      _hfField, hfFix, hfTerminal⟩ :=
    exists_clamped_geodesic_variation_on_compactCarrier
      g Gamma (fun s ↦ (W s : E)) L univ K hWtotal hKcompact
      (fun s _ ↦ hWmem s) (mem_univ L)
  have hWL : (W L : E) = v := by
    rw [hWradial L ⟨hL.le, le_rfl⟩]
    have hVL : (V L : E) = v :=
      congrArg (fun q : TangentBundle I M ↦ q.snd) hterminalV
    simpa [hL.ne'] using hVL
  have hW0 : W 0 = 0 := by
    rw [hWradial 0 ⟨le_rfl, hL.le⟩]
    simp
  have hbeta0Gamma : beta 0 = Gamma L :=
    hbeta0.trans (hdeltaL.symm.trans (hGamma L ⟨hL.le, le_rfl⟩).symm)
  obtain ⟨B, hBproj, hBint, hB0⟩ :=
    exists_centered_lift_of_isGeodesicAt g beta (Gamma L) (W L)
      hbeta hbeta0Gamma hWL.symm
  have hterm : (fun u ↦ f0 u L) =ᶠ[𝓝 (0 : ℝ)] beta :=
    hfTerminal beta B hBproj hBint hB0
  let f : ℝ → ℝ → M := fun u s ↦ f0 u (s - c)
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · exact hf0.comp (contMDiff_fst.prodMk (contMDiff_snd.sub contMDiff_const))
  · intro s hs
    have hsc : s - c ∈ Icc 0 L := by
      constructor
      · linarith [hs.1]
      · dsimp [L]
        linarith [hs.2]
    have heq := (hGammaGerm (s - c) hsc).comp_tendsto
      (continuous_id.sub continuous_const).continuousAt
    filter_upwards [heq] with t ht
    change f0 0 (t - c) = gamma t
    change Gamma (t - c) = delta (t - c) at ht
    rw [hfcentral, ht]
    simp [delta]
  · intro u
    change f0 u (c - c) = gamma c
    rw [sub_self, hfFix hW0 u, hGamma 0 ⟨le_rfl, hL.le⟩]
    simp [delta]
  · exact hterm

end DifferentialGeometry.Geometry.Riemannian.Variation
