import DifferentialGeometry.Geometry.Collapse.SmallResidualRows

/-!
The produced external small packet has invariant quantitative fields on its original source.
Its same scale and same selected zero radius supply actual original smooth cutoff consumers.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Manifold Set Bundle
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.Calculus
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "I3" => 𝓡 3

variable {M : Type u} [mM : MetricSpace M] [cM : ChartedSpace E3 M]
  [sM : IsManifold I3 ∞ M] [compactM : CompactSpace M]
  (S : SmallManifoldModel (I := I3) M)

local instance smallMetricOriginalPacket : MetricSpace S.Carrier := S.metricSpace
local instance smallCompactOriginalPacket : CompactSpace S.Carrier :=
  S.diffeo.toHomeomorph.symm.compactSpace

variable (g : SmoothRiemannianMetric I3 M)
  (hmetric : ∀ a b : M, riemannianEDistOf g a b = ENNReal.ofReal (dist a b))
  (ρ : M → ℝ) (hρ : ∀ p, 0 < ρ p) (Λ : ℝ) (β : ℕ → ℝ) (Δ σs : ℝ) (K : ℕ)
  (σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V : ℝ)
  (P : LocalChartPacketsR S.Carrier (S.metric g) (S.metric_aligned g hmetric)
    (ρ ∘ S.diffeo) (fun p => hρ (S.diffeo p)) Λ β Δ σs K
    σc μ b s b' s' ε γc βc Lmax τ γ δ εr e T V)

include P in
theorem smallModel_packet_scale_original :
    ContMDiff I3 𝓘(ℝ, ℝ) ∞ ρ ∧ LipschitzWith (Real.toNNReal Λ) ρ := by
  refine ⟨?_, ?_⟩
  · have hscale := P.toLocalChartFamily.contMDiff_scale
    have ht := hscale.comp S.diffeo.symm.contMDiff
    simpa only [Function.comp_def, Diffeomorph.apply_symm_apply] using ht
  · have hscale := P.toLocalChartFamily.lipschitz_scale
    have ht := hscale.comp S.isometryEquiv.symm.isometry.lipschitzWith
    change LipschitzWith (Real.toNNReal Λ * 1) ((ρ ∘ S.diffeo) ∘ S.diffeo.symm) at ht
    simpa only [mul_one, Function.comp_def, Diffeomorph.apply_symm_apply] using ht

theorem smallModel_packet_zero_cutoff_original :
    letI _modelMetrics := P.instMetricN
    letI _modelCharts := P.instChartedN
    letI _coneMetrics := P.instMetricC
    ∀ c (hc : c ∈ P.zero.centres),
    let Z := P.zero.zero c hc
    let radial := smallModel_backFunction S Z.radial
    let gR := scaleMetric (Z.radius⁻¹ ^ 2) (pow_pos (inv_pos.mpr Z.radius_pos) 2) g
    letI _sourceRescaled := mM.rescale Z.radius⁻¹ (inv_pos.mpr Z.radius_pos)
    ∃ L : ℝ, 0 ≤ L ∧
      ContMDiff I3 𝓘(ℝ, ℝ) ∞ (fun x => annularCutoff cutoffProfile (radial x)) ∧
      ∀ q, Real.sqrt (gR.inner q
        (gradFun gR (fun x => annularCutoff cutoffProfile (radial x)) q)
        (gradFun gR (fun x => annularCutoff cutoffProfile (radial x)) q)) ≤ L * (1 + εr) := by
  let modelMetrics := P.instMetricN
  let modelCharts := P.instChartedN
  let coneMetrics := P.instMetricC
  intro c hc
  have ht := smallModel_zeroRadial_back (mM := mM) S g P.N P.C P.o δ εr e (P.zero.zero c hc)
  obtain ⟨L, hL⟩ := ht.2.2.2.2.2.2.2.2.2.2.2
  exact ⟨L, hL.1, hL.2.2.1, hL.2.2.2.2.2.2⟩

end DifferentialGeometry.Geometry.Collapse
