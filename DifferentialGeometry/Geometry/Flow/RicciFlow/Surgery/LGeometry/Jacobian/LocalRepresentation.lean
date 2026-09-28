import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Jacobian.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.LGeometry.Exponential.SmoothFamily

set_option autoImplicit false

noncomputable section

open Set Filter Matrix
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman
open DifferentialGeometry.Tensor.Coordinates (chartModelBasis)

universe u
variable {H : ObservedHistory.{u}}

variable {first last : Fin (H.eventCount + 1)} {hle : first ≤ last} {T v : ℝ}
  {p : (H.stage last).Carrier} {Z₀ : H.historyLExpDomain hle T v p}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_window_historyLJacobianDensity_eq_lJacobianDensity (hv : 0 < v)
    (hZ₀ : Z₀.1 ∈ H.historyLExpOpenDomain hle T v p) {s₀ : ℝ} (hs₀ : s₀ ∈ Ioo 0 v) :
    ∃ (lo hi : Fin (H.eventCount + 1)) (hlo : first ≤ lo) (hhi : hi ≤ last)
      (W : H.LWindow lo hi T) (K : Set ℝ) (β : ThreeSpace × ℝ → W.X),
      IsOpen K ∧ s₀ ∈ K ∧ K ⊆ Ioo W.a W.b ∧
      IsLRegularizedGeodesicOn W.S T (fun r => β (Z₀.1, r)) K ∧
      (∀ (j : H.StageInterval lo hi) {D' : RealTimeInterval}
        (S' : SolutionOn (I := ThreeModel) (M := (H.stage j.val).Carrier) D') {K' : Set ℝ},
        IsOpen K' →
        K' ⊆ K ∩ Ioo (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val) →
        (∀ s ∈ K', S'.base.metric (T - s ^ 2) = H.stageMetric j.val (T - s ^ 2)) →
        ∀ i : Fin (Module.finrank ℝ ThreeSpace),
        IsLRegularizedJacobi S' T (fun r => H.historyLCurveMap hle T v p Z₀
            ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩ r Z₀.1)
          (fun r => H.historyLJacobiField hle T v p Z₀
            ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩ i r) K') ∧
      (∀ (j : H.StageInterval lo hi) {τ : ℝ}, Real.sqrt τ ∈
        K ∩ Ioo (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val) →
        H.historyLGram hle T v p Z₀ ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩
            (Real.sqrt τ) =
          lGram W.S T (fun q => β (Z₀.1, Real.sqrt q))
            (fun i q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt q)) Z₀.1
              (chartModelBasis ThreeSpace i)) τ) ∧
      (∀ (j : H.StageInterval lo hi) {τ : ℝ}, Real.sqrt τ ∈
        K ∩ Ioo (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val) →
        H.historyLJacobianDensity hle T v p Z₀
            ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩ (Real.sqrt τ) =
          lJacobianDensity W.S T (fun q => β (Z₀.1, Real.sqrt q))
            (fun i q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt q)) Z₀.1
              (chartModelBasis ThreeSpace i)) τ) ∧
      (∀ (j : H.StageInterval lo hi) {τ : ℝ}, Real.sqrt τ ∈
        K ∩ Ioo (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val) →
        0 < (lGram W.S T (fun q => β (Z₀.1, Real.sqrt q))
          (fun i q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt q)) Z₀.1
            (chartModelBasis ThreeSpace i)) τ).det →
        HasDerivAt (fun τ' => H.historyLJacobianDensity hle T v p Z₀
            ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩ (Real.sqrt τ'))
          ((1 / 2) * trace ((lGram W.S T (fun q => β (Z₀.1, Real.sqrt q))
              (fun i q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt q)) Z₀.1
                (chartModelBasis ThreeSpace i)) τ)⁻¹ *
            lGramDeriv W.S T (fun q => β (Z₀.1, Real.sqrt q))
              (fun i q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt q)) Z₀.1
                (chartModelBasis ThreeSpace i)) τ) *
            lJacobianDensity W.S T (fun q => β (Z₀.1, Real.sqrt q))
              (fun i q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt q)) Z₀.1
                (chartModelBasis ThreeSpace i)) τ) τ) ∧
      ∀ (j : H.StageInterval lo hi) {s₁ : ℝ}, s₁ ∈ K → ∀ {l : Filter ℝ}, l ≤ 𝓝 s₁ →
        (∀ᶠ r in l,
          r ∈ Ioo (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val)) →
        Tendsto (H.historyLJacobianDensity hle T v p Z₀
            ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩) l
          (𝓝 (lJacobianDensity W.S T (fun q => β (Z₀.1, Real.sqrt q))
            (fun i q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt q)) Z₀.1
              (chartModelBasis ThreeSpace i)) (s₁ ^ 2))) := by
  obtain ⟨V, hV, hZ₀V, -, hVdom, lo, hi, hlo, hhi, W, K, hK, hs₀K, hKW, β, hβ, hgeo, hrep⟩ :=
    exists_contMDiffOn_window_family_historyLCurve hv hZ₀ hs₀
  exact ⟨lo, hi, hlo, hhi, W, K, β, hK, hs₀K, hKW, hgeo _ hZ₀V,
    fun j _ S' _ hK' hK'sub hS' i => isLRegularizedJacobi_historyLJacobiField (hlo := hlo)
      (hhi := hhi) (Z₀ := Z₀) hV hZ₀V hVdom hK hβ hgeo hrep j S' hK' hK'sub hS' i,
    fun j _ hτ => historyLGram_eq_lGram (hlo := hlo) (hhi := hhi) (Z₀ := Z₀) hV hZ₀V hVdom hK
      hKW hβ hrep j hτ,
    fun j _ hτ => historyLJacobianDensity_eq_lJacobianDensity (hlo := hlo) (hhi := hhi)
      (Z₀ := Z₀) hV hZ₀V hVdom hK hKW hβ hrep j hτ,
    fun j _ hτ hpos => hasDerivAt_historyLJacobianDensity (hlo := hlo) (hhi := hhi) (Z₀ := Z₀)
      hV hZ₀V hVdom hK hKW hβ hgeo hrep j hτ hpos,
    fun j _ hs₁ _ hl hpiece => tendsto_historyLJacobianDensity (hlo := hlo) (hhi := hhi)
      (Z₀ := Z₀) hV hZ₀V hVdom hK hKW hβ hgeo hrep j hs₁ hl hpiece⟩

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem exists_seam_window_tendsto_historyLJacobianDensity (hv : 0 < v)
    (hZ₀ : Z₀.1 ∈ H.historyLExpOpenDomain hle T v p) (i : Fin H.eventCount)
    (hlo : first ≤ i.castSucc) (hhi : i.succ ≤ last)
    (hw : Real.sqrt (T - H.time i.succ) ∈ Ioo 0 v) :
    ∃ (W : H.LWindow i.castSucc i.succ T) (K : Set ℝ) (β : ThreeSpace × ℝ → W.X),
      IsOpen K ∧ Real.sqrt (T - H.time i.succ) ∈ K ∧ K ⊆ Ioo W.a W.b ∧
      IsLRegularizedGeodesicOn W.S T (fun r => β (Z₀.1, r)) K ∧
      (∀ (j : H.StageInterval i.castSucc i.succ) {τ : ℝ}, Real.sqrt τ ∈
        K ∩ Ioo (H.regularizedStageStart T W.a j.val) (H.regularizedStageEnd T W.b j.val) →
        H.historyLJacobianDensity hle T v p Z₀
            ⟨j.val, hlo.trans j.property.1, j.property.2.trans hhi⟩ (Real.sqrt τ) =
          lJacobianDensity W.S T (fun q => β (Z₀.1, Real.sqrt q))
            (fun k q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt q)) Z₀.1
              (chartModelBasis ThreeSpace k)) τ) ∧
      Tendsto (H.historyLJacobianDensity hle T v p Z₀
          ⟨i.succ, hlo.trans i.castSucc_lt_succ.le, hhi⟩)
          (𝓝[<] Real.sqrt (T - H.time i.succ))
          (𝓝 (lJacobianDensity W.S T (fun q => β (Z₀.1, Real.sqrt q))
            (fun k q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt q)) Z₀.1
              (chartModelBasis ThreeSpace k)) (Real.sqrt (T - H.time i.succ) ^ 2))) ∧
      Tendsto (H.historyLJacobianDensity hle T v p Z₀
          ⟨i.castSucc, hlo, i.castSucc_lt_succ.le.trans hhi⟩)
          (𝓝[>] Real.sqrt (T - H.time i.succ))
          (𝓝 (lJacobianDensity W.S T (fun q => β (Z₀.1, Real.sqrt q))
            (fun k q => mfderiv 𝓘(ℝ, ThreeSpace) ThreeModel (fun Z => β (Z, Real.sqrt q)) Z₀.1
              (chartModelBasis ThreeSpace k)) (Real.sqrt (T - H.time i.succ) ^ 2))) := by
  obtain ⟨V, hV, hZ₀V, -, hVdom, W, K, hK, hwK, hKW, β, hβ, hgeo, hrep⟩ :=
    exists_contMDiffOn_seam_window_family_historyLCurve hv hZ₀ i hlo hhi hw
  exact ⟨W, K, β, hK, hwK, hKW, hgeo _ hZ₀V,
    fun j _ hτ => historyLJacobianDensity_eq_lJacobianDensity (hlo := hlo) (hhi := hhi)
      (Z₀ := Z₀) hV hZ₀V hVdom hK hKW hβ hrep j hτ,
    tendsto_historyLJacobianDensity_seam (hlo := hlo) (hhi := hhi) (Z₀ := Z₀) hV hZ₀V hVdom hK
      hKW hβ hgeo hrep hwK⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
