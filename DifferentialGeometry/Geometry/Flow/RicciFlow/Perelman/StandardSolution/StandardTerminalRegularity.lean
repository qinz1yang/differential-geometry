import DifferentialGeometry.Analysis.Calculus.TimeJet.ClosedJetEvolution
import DifferentialGeometry.Geometry.Metric.TerminalFamily
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardMetricControl
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardInitialExistence
import DifferentialGeometry.Analysis.Calculus.IteratedDerivative.Pi
import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.ChartBridge
import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.Curvature
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

set_option autoImplicit false
noncomputable section
open Set Bundle Manifold Filter DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Analysis
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Geometry.Metric DifferentialGeometry.Analysis
open scoped Manifold ContDiff BigOperators Topology ENNReal
namespace DifferentialGeometry.PDE.RicciFlow
private abbrev E3 := EuclideanSpace ℝ (Fin 3)

private theorem pi_jet_continuous {E F A : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [Fintype A] (f : A → ℝ → E → F) (J : Set ℝ) (V : Set E) (hV : IsOpen V)
    (hs : ∀ i, ∀ t ∈ J, ContDiffOn ℝ ∞ (f i t) V)
    (hj : ∀ i, ∀ r : ℕ, ContinuousOn
      (fun p : ℝ × E => iteratedFDeriv ℝ r (f i p.1) p.2) (J ×ˢ V)) (r : ℕ) :
    ContinuousOn (fun p : ℝ × E => iteratedFDeriv ℝ r (fun x i => f i p.1 x) p.2) (J ×ˢ V) := by
  let L : (A → E [×r]→L[ℝ] F) ≃ₗᵢ[ℝ] (E [×r]→L[ℝ] (A → F)) :=
    ContinuousMultilinearMap.piₗᵢ _ _
  have hh := L.continuous.comp_continuousOn (continuousOn_pi.mpr fun i => hj i r)
  apply hh.congr
  intro p hp
  exact iteratedFDeriv_pi (fun i => (hs i p.1 hp.1 p.2 hp.2).contDiffAt (hV.mem_nhds hp.2))
    (by exact_mod_cast le_top)

private theorem closed_metric_gram (g : ℝ → SmoothRiemannianMetric (𝓡 3) E3)
    (T : ℝ) (hT : 0 < T)
    (hjets : ∀ (r : ℕ) (x₀ : E3) (i j : Fin (Module.finrank ℝ E3)),
      ContinuousOn (fun p : ℝ × E3 => iteratedFDeriv ℝ r (chartGramOnE (g p.1) x₀ i j) p.2)
        (Icc 0 T ×ˢ interior (extChartAt (𝓡 3) x₀).target))
    (hpde : ∀ t ∈ Ico 0 T, ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
      HasDerivWithinAt (fun s => (g s).inner x v w) (-2 * ricciTensor (g t) x v w) (Ici 0) t) :
    ∀ (x₀ : E3) (i j : Fin (Module.finrank ℝ E3)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × E3 => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ p.2 i j)
        (Icc 0 T ×ˢ (trivializationAt E3 (TangentSpace (𝓡 3)) x₀).baseSet) := by
  intro x₀ i j
  let V := interior (extChartAt (𝓡 3) x₀).target
  let G := fun t => chartGramPi (g t) x₀
  have hs (a b : Fin (Module.finrank ℝ E3)) (t : ℝ) (_ht : t ∈ Icc 0 T) :
      ContDiffOn ℝ ∞ (chartGramOnE (g t) x₀ a b) V :=
    (chartGramOnE_contDiffOn (g t) x₀ a b).mono interior_subset
  have hGs (t : ℝ) (ht : t ∈ Icc 0 T) : ContDiffOn ℝ ∞ (G t) V :=
    contDiffOn_pi.mpr (fun a => contDiffOn_pi.mpr (fun b => hs a b t ht))
  have hGjets (r : ℕ) : ContinuousOn
      (fun p : ℝ × E3 => iteratedFDeriv ℝ r (G p.1) p.2) (Icc 0 T ×ˢ V) := by
    apply pi_jet_continuous (fun a t x b => chartGramOnE (g t) x₀ a b x) (Icc 0 T) V isOpen_interior
    · intro a t ht
      exact contDiffOn_pi.mpr (fun b => hs a b t ht)
    · intro a k
      exact pi_jet_continuous (fun b t => chartGramOnE (g t) x₀ a b) (Icc 0 T) V
        isOpen_interior (hs a) (fun b k => hjets k x₀ a b) k
  let Ω : Set (MatJet E3 (Module.finrank ℝ E3)) := {p | (Matrix.of p.1).det ≠ 0}
  have hΩ : IsOpen Ω := isOpen_ne_fun
    ((contDiff_det_of_entries (fun p : MatJet E3 (Module.finrank ℝ E3) => Matrix.of p.1)
      (fun a b => contDiff_jetVal a b)).continuous) continuous_const
  have hΦ : ContDiffOn ℝ ∞ (jetRicciFlow (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E3)) Ω :=
    fun p hp => (contDiffAt_jetRicciFlow (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E3) hp).contDiffWithinAt
  have hmap : MapsTo (Function.uncurry (fun t y => jet2 (G t) y)) (Icc 0 T ×ˢ V) Ω := by
    intro p _
    change (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ ((extChartAt (𝓡 3) x₀).symm p.2)).det ≠ 0
    exact (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_det_pos (g p.1) x₀ (by change _ ∈ (univ : Set E3); trivial)).ne'
  have hGPDE (t : ℝ) (ht : t ∈ Ioo 0 T) (y : E3) (hy : y ∈ V) :
      HasDerivAt (fun s => G s y) (jetRicciFlow (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E3) (jet2 (G t) y)) t := by
    have hAt := (hGs t (Ioo_subset_Icc_self ht) y hy).contDiffAt (isOpen_interior.mem_nhds hy)
    have hG1 : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ (G t) z := by
      filter_upwards [isOpen_interior.mem_nhds hy] with z hz
      exact ((hGs t (Ioo_subset_Icc_self ht) z hz).contDiffAt
        (isOpen_interior.mem_nhds hz)).differentiableAt (by simp)
    have hG2 := (hAt.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
    have hyT : y ∈ (extChartAt (𝓡 3) x₀).target := interior_subset hy
    have hgs : (extChartAt (𝓡 3) x₀).symm y ∈ chartLeviCivitaGoodSet (I := 𝓡 3) x₀ := by
      rw [chartLeviCivitaGoodSet_eq_extChartAt_source]
      exact (extChartAt (𝓡 3) x₀).map_target hyT
    apply hasDerivAt_pi.mpr
    intro a
    apply hasDerivAt_pi.mpr
    intro b
    change HasDerivAt (fun s => chartGramOnE (g s) x₀ a b y)
      (jetRicciFlow (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E3) (jet2 (G t) y) a b) t
    rw [jetRicciFlow_chartGram (g t) x₀ hy (hAt.differentiableAt (by simp)) hG1 hG2]
    have hmetric := (hpde t ⟨ht.1.le, ht.2⟩ ((extChartAt (𝓡 3) x₀).symm y)
      (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := 𝓡 3) x₀ a ((extChartAt (𝓡 3) x₀).symm y))
      (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := 𝓡 3) x₀ b ((extChartAt (𝓡 3) x₀).symm y))).hasDerivAt
        (Ici_mem_nhds ht.1)
    exact (chartGramEntryPDE_of_metricPDE g x₀ (sL := univ) hgs
      ((extChartAt (𝓡 3) x₀).right_inv hyT) a b hmetric.hasDerivWithinAt).hasDerivAt univ_mem
  have hSmooth := (contDiffOn_and_equation_Icc_of_spatial_jets G 0 T hT V isOpen_interior
    (jetRicciFlow (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E3)) Ω hΩ hΦ hmap hGs hGjets hGPDE).1
  have hentry := (contDiffOn_pi.mp (contDiffOn_pi.mp hSmooth i)) j
  have hnative : ContDiffOn ℝ ∞ (fun p : ℝ × E3 => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ p.2 i j)
      (Icc 0 T ×ˢ (univ : Set E3)) := by
    change ContDiffOn ℝ ∞
      (fun p : ℝ × E3 => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ ((extChartAt (𝓡 3) x₀).symm p.2) i j)
      (Icc 0 T ×ˢ V) at hentry
    simpa only [V, extChartAt_model_space_eq_id, PartialEquiv.refl_target, interior_univ,
      PartialEquiv.refl_symm, PartialEquiv.refl_coe, id_eq] using hentry
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  exact (hnative.mono (prod_mono subset_rfl (subset_univ _))).contMDiffOn

private theorem equation_closed (g : ℝ → SmoothRiemannianMetric (𝓡 3) E3)
    (T : ℝ) (hT : 0 < T)
    (hgram : ∀ (x₀ : E3) (i j : Fin (Module.finrank ℝ E3)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × E3 => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ p.2 i j)
        (Icc 0 T ×ˢ (trivializationAt E3 (TangentSpace (𝓡 3)) x₀).baseSet))
    (hpde : ∀ t ∈ Ico 0 T, ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
      HasDerivWithinAt (fun s => (g s).inner x v w) (-2 * ricciTensor (g t) x v w) (Ici 0) t) :
    ∀ t ∈ Icc 0 T, ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
      HasDerivWithinAt (fun s => (g s).inner x v w) (-2 * ricciTensor (g t) x v w) (Icc 0 T) t := by
  have hCartesian := cartesian_contDiffOn_of_chartGram g (Icc 0 T) hgram
  have hRicField := ricciCont_of_joint g (Icc 0 T) (uniqueDiffOn_Icc hT) hgram
  intro t ht x v w
  have hg : ContinuousOn (fun s => (g s).inner x v w) (Icc 0 T) := by
    have hh := hCartesian.continuousOn.comp (continuousOn_id.prodMk continuousOn_const)
      (fun s hs => ⟨hs, mem_univ x⟩)
    exact (hh.clm_apply continuousOn_const).clm_apply continuousOn_const
  have hRic : ContinuousOn (fun s => ricciTensor (g s) x v w) (Icc 0 T) := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun s : Icc 0 T => ricciTensor (g s.val) x v w)
    have hh := hRicField.eval_continuous
      (P := Icc 0 T) (τ := Subtype.val) (b := fun _ => x)
      continuous_subtype_val (fun s => s.property) continuous_const
      (v := fun i _ => vec2 v w i) (fun _ => continuous_const)
    simpa only [metricRicciAt_apply_eq_ricciTensor] using hh
  exact hasDerivIcc_of_int hT hg (continuousOn_const.mul hRic)
    (fun s hs => (hpde s ⟨hs.1.le, hs.2⟩ x v w).hasDerivAt (Ici_mem_nhds hs.1)) ht

private theorem closed_seed :
    ∃ α : ℝ, 0 < α ∧ ∃ Λ : ℝ, 1 ≤ Λ ∧ ∃ C L : ℕ → ℝ,
      (∀ N, 0 ≤ C N) ∧ (∀ N, 0 ≤ L N) ∧
      ∀ S : PartialStandardSolution, ∀ T : ℝ, 0 < T → T ≤ α →
        ENNReal.ofReal T ≤ S.lifetime →
        ∃ G : ℝ → SmoothRiemannianMetric (𝓡 3) E3,
          (∀ t ∈ Ico 0 T, G t = S.metric t) ∧
          G 0 = DifferentialGeometry.PDE.RicciFlow.StandardCap.metric ∧
          (∀ t ∈ Icc 0 T, RiemannianMetricComplete (G t)) ∧
          (∀ t ∈ Icc 0 T, MetricUniformEquivalentOn univ DifferentialGeometry.PDE.RicciFlow.StandardCap.metric (G t) Λ) ∧
          (∀ N : ℕ, ∀ t ∈ Icc 0 T, ∀ x : E3,
            metricCovDerivNorm N (G t) DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x ≤ C N) ∧
          (∀ N : ℕ, ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ∀ x : E3,
            metricDerivNorm N (G s) (G t) DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x ≤ L N * |s - t|) ∧
          (∀ (r : ℕ) (x₀ : E3) (i j : Fin (Module.finrank ℝ E3)),
            ContinuousOn
              (fun p : ℝ × E3 => iteratedFDeriv ℝ r (chartGramOnE (G p.1) x₀ i j) p.2)
              (Icc 0 T ×ˢ interior (extChartAt (𝓡 3) x₀).target)) ∧
          ∀ t ∈ Ico 0 T, ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
            HasDerivWithinAt (fun s => (G s).inner x v w)
              (-2 * ricciTensor (G t) x v w) (Ici 0) t := by
  obtain ⟨α, hα, Λ, hΛ, C, L, hC, hL, hb⟩ := standard_uniform_fixed_cap_metric_bounds
  refine ⟨α, hα, Λ, hΛ, C, L, hC, hL, ?_⟩
  intro S T hT hTα hTS
  have hw (θ : ℝ) (hθ : θ ∈ Ico 0 T) := hb S θ hθ.1 (hθ.2.le.trans hTα)
    ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hθ.1).mpr hθ.2 |>.trans_le hTS)
  have he (t : ℝ) (ht : t ∈ Ico 0 T) := (hw t ht).1 t ⟨ht.1, le_rfl⟩
  have hc (N : ℕ) (t : ℝ) (ht : t ∈ Ico 0 T) (x : E3) := (hw t ht).2.1 N t ⟨ht.1, le_rfl⟩ x
  have hl (N : ℕ) (s : ℝ) (hs : s ∈ Ico 0 T) (t : ℝ) (ht : t ∈ Ico 0 T) (x : E3) :=
    (hw (max s t) ⟨hs.1.trans (le_max_left _ _), max_lt hs.2 ht.2⟩).2.2 N
      s ⟨hs.1, le_max_left _ _⟩ t ⟨ht.1, le_max_right _ _⟩ x
  obtain ⟨G, hEq, hComp, hEquiv, hCov, hLip, hJets⟩ :=
    exists_closed_terminal_family_of_reference_bounds (I := 𝓡 3) (M := E3)
      inferInstance DifferentialGeometry.PDE.RicciFlow.StandardCap.metric DifferentialGeometry.PDE.RicciFlow.StandardCap.metric_complete
      S.metric T Λ hT hΛ C L hL he hc hl
  refine ⟨G, hEq, (hEq 0 ⟨le_rfl, hT⟩).trans S.initial, hComp, hEquiv, hCov, hLip, hJets, ?_⟩
  intro t ht x v w
  have hdom : t ∈ S.domain := (mem_lifetimeInterval_carrier S.lifetime S.lifetime_pos t).mpr
    ⟨ht.1, (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ht.1).mpr ht.2 |>.trans_le hTS⟩
  have hgerm : (fun s => (G s).inner x v w) =ᶠ[𝓝[Ici 0] t]
      (fun s => (S.metric s).inner x v w) := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds ht.2)] with s hs hsT
    rw [hEq s ⟨hs, hsT⟩]
  rw [hEq t ht]
  exact (S.equation t hdom x v w).congr_of_eventuallyEq hgerm (by rw [hEq t ht])

theorem standard_uniform_smooth_terminal_families :
    ∃ α : ℝ, 0 < α ∧ ∃ Λ : ℝ, 1 ≤ Λ ∧ ∃ C L : ℕ → ℝ,
      (∀ N, 0 ≤ C N) ∧ (∀ N, 0 ≤ L N) ∧
      ∀ S : PartialStandardSolution, ∀ T : ℝ, 0 < T → T ≤ α →
        ENNReal.ofReal T ≤ S.lifetime →
        ∃ G : ℝ → SmoothRiemannianMetric (𝓡 3) E3,
          (∀ t ∈ Ico 0 T, G t = S.metric t) ∧
          G 0 = DifferentialGeometry.PDE.RicciFlow.StandardCap.metric ∧
          (∀ t ∈ Icc 0 T, RiemannianMetricComplete (G t)) ∧
          (∀ t ∈ Icc 0 T, MetricUniformEquivalentOn univ DifferentialGeometry.PDE.RicciFlow.StandardCap.metric (G t) Λ) ∧
          (∀ N : ℕ, ∀ t ∈ Icc 0 T, ∀ x : E3,
            metricCovDerivNorm N (G t) DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x ≤ C N) ∧
          (∀ N : ℕ, ∀ s ∈ Icc 0 T, ∀ t ∈ Icc 0 T, ∀ x : E3,
            metricDerivNorm N (G s) (G t) DifferentialGeometry.PDE.RicciFlow.StandardCap.metric x ≤ L N * |s - t|) ∧
          (∀ (r : ℕ) (x₀ : E3) (i j : Fin (Module.finrank ℝ E3)),
            ContinuousOn
              (fun p : ℝ × E3 => iteratedFDeriv ℝ r (chartGramOnE (G p.1) x₀ i j) p.2)
              (Icc 0 T ×ˢ interior (extChartAt (𝓡 3) x₀).target)) ∧
          (∀ t ∈ Ico 0 T, ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
            HasDerivWithinAt (fun s => (G s).inner x v w)
              (-2 * ricciTensor (G t) x v w) (Ici 0) t) ∧
          (∀ (x₀ : E3) (i j : Fin (Module.finrank ℝ E3)),
            ContMDiffOn (𝓘(ℝ, ℝ).prod (𝓡 3)) 𝓘(ℝ, ℝ) ∞
              (fun p : ℝ × E3 => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (G p.1) x₀ p.2 i j)
              (Icc 0 T ×ˢ (trivializationAt E3 (TangentSpace (𝓡 3)) x₀).baseSet)) ∧
          ∀ t ∈ Icc 0 T, ∀ (x : E3) (v w : TangentSpace (𝓡 3) x),
            HasDerivWithinAt (fun s => (G s).inner x v w)
              (-2 * ricciTensor (G t) x v w) (Icc 0 T) t := by
  obtain ⟨α, hα, Λ, hΛ, C, L, hC, hL, hs⟩ := closed_seed
  refine ⟨α, hα, Λ, hΛ, C, L, hC, hL, ?_⟩
  intro S T hT hTα hTS
  obtain ⟨G, hEq, hzero, hc, he, hCov, hLip, hj, hpde⟩ := hs S T hT hTα hTS
  have hgram := closed_metric_gram G T hT hj hpde
  exact ⟨G, hEq, hzero, hc, he, hCov, hLip, hj, hpde, hgram, equation_closed G T hT hgram hpde⟩
end DifferentialGeometry.PDE.RicciFlow
