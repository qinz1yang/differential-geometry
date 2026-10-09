import DifferentialGeometry.Analysis.Calculus.TimeJet.ClosedJetEvolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.ClosedMetricLipschitz
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
open DifferentialGeometry.Analysis
open scoped Manifold ContDiff BigOperators Topology
namespace DifferentialGeometry.PDE.RicciFlow
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

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

private theorem closed_metric_gram (g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (α β : ℝ) (hab : α < β)
    (hjets : ∀ (r : ℕ) (x₀ : E) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn (fun p : ℝ × E => iteratedFDeriv ℝ r (chartGramOnE (g p.1) x₀ i j) p.2)
        (Icc α β ×ˢ interior (extChartAt 𝓘(ℝ, E) x₀).target))
    (hpde : ∀ t ∈ Ioo α β, ∀ (x : E) (v w : TangentSpace 𝓘(ℝ, E) x),
      HasDerivAt (fun s => (g s).inner x v w) (-2 * ricciTensor (g t) x v w) t) :
    ∀ (x₀ : E) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × E => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ p.2 i j)
        (Icc α β ×ˢ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).baseSet) := by
  intro x₀ i j
  let V := interior (extChartAt 𝓘(ℝ, E) x₀).target
  let G := fun t => chartGramPi (g t) x₀
  have hs (i₁ i₂ : Fin (Module.finrank ℝ E)) (t : ℝ) (_ht : t ∈ Icc α β) :
      ContDiffOn ℝ ∞ (chartGramOnE (g t) x₀ i₁ i₂) V :=
    (chartGramOnE_contDiffOn (g t) x₀ i₁ i₂).mono interior_subset
  have hGs (t : ℝ) (ht : t ∈ Icc α β) : ContDiffOn ℝ ∞ (G t) V :=
    contDiffOn_pi.mpr (fun a => contDiffOn_pi.mpr (fun b => hs a b t ht))
  have hGjets (r : ℕ) : ContinuousOn
      (fun p : ℝ × E => iteratedFDeriv ℝ r (G p.1) p.2) (Icc α β ×ˢ V) := by
    apply pi_jet_continuous (fun a t x b => chartGramOnE (g t) x₀ a b x) (Icc α β) V isOpen_interior
    · intro a t ht
      exact contDiffOn_pi.mpr (fun b => hs a b t ht)
    · intro a k
      exact pi_jet_continuous (fun b t => chartGramOnE (g t) x₀ a b) (Icc α β) V
        isOpen_interior (hs a) (fun b k => hjets k x₀ a b) k
  let Ω : Set (MatJet E (Module.finrank ℝ E)) := {p | (Matrix.of p.1).det ≠ 0}
  have hΩ : IsOpen Ω := isOpen_ne_fun
    ((contDiff_det_of_entries (fun p : MatJet E (Module.finrank ℝ E) => Matrix.of p.1)
      (fun a b => contDiff_jetVal a b)).continuous) continuous_const
  have hΦ : ContDiffOn ℝ ∞ (jetRicciFlow (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E)) Ω :=
    fun p hp => (contDiffAt_jetRicciFlow (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) hp).contDiffWithinAt
  have hmap : MapsTo (Function.uncurry (fun t y => jet2 (G t) y)) (Icc α β ×ˢ V) Ω := by
    intro p _
    change (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ ((extChartAt 𝓘(ℝ, E) x₀).symm p.2)).det ≠ 0
    exact (DifferentialGeometry.Tensor.Coordinates.chartGramMatrix_det_pos (g p.1) x₀ (by change _ ∈ (univ : Set E); trivial)).ne'
  have hGPDE (t : ℝ) (ht : t ∈ Ioo α β) (y : E) (hy : y ∈ V) :
      HasDerivAt (fun s => G s y) (jetRicciFlow (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (jet2 (G t) y)) t := by
    have hAt := (hGs t (Ioo_subset_Icc_self ht) y hy).contDiffAt (isOpen_interior.mem_nhds hy)
    have hG1 : ∀ᶠ z in 𝓝 y, DifferentiableAt ℝ (G t) z := by
      filter_upwards [isOpen_interior.mem_nhds hy] with z hz
      exact ((hGs t (Ioo_subset_Icc_self ht) z hz).contDiffAt
        (isOpen_interior.mem_nhds hz)).differentiableAt (by simp)
    have hG2 := (hAt.fderiv_right (m := ∞) (by simp)).differentiableAt (by simp)
    have hyT : y ∈ (extChartAt 𝓘(ℝ, E) x₀).target := interior_subset hy
    have hgs : (extChartAt 𝓘(ℝ, E) x₀).symm y ∈ chartLeviCivitaGoodSet (I := 𝓘(ℝ, E)) x₀ := by
      rw [chartLeviCivitaGoodSet_eq_extChartAt_source]
      exact (extChartAt 𝓘(ℝ, E) x₀).map_target hyT
    apply hasDerivAt_pi.mpr
    intro a
    apply hasDerivAt_pi.mpr
    intro b
    change HasDerivAt (fun s => chartGramOnE (g s) x₀ a b y)
      (jetRicciFlow (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) (jet2 (G t) y) a b) t
    rw [jetRicciFlow_chartGram (g t) x₀ hy (hAt.differentiableAt (by simp)) hG1 hG2]
    have hmetric := (hpde t ht ((extChartAt 𝓘(ℝ, E) x₀).symm y)
      (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := 𝓘(ℝ, E)) x₀ a ((extChartAt 𝓘(ℝ, E) x₀).symm y))
      (DifferentialGeometry.Tensor.Coordinates.chartBasisVecFiber (I := 𝓘(ℝ, E)) x₀ b ((extChartAt 𝓘(ℝ, E) x₀).symm y)))
    exact (chartGramEntryPDE_of_metricPDE g x₀ (sL := univ) hgs
      ((extChartAt 𝓘(ℝ, E) x₀).right_inv hyT) a b hmetric.hasDerivWithinAt).hasDerivAt univ_mem
  have hSmooth := (contDiffOn_and_equation_Icc_of_spatial_jets G α β hab V isOpen_interior
    (jetRicciFlow (DifferentialGeometry.Tensor.Coordinates.chartModelBasis E)) Ω hΩ hΦ hmap hGs hGjets hGPDE).1
  have hentry := (contDiffOn_pi.mp (contDiffOn_pi.mp hSmooth i)) j
  have hnative : ContDiffOn ℝ ∞ (fun p : ℝ × E => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ p.2 i j)
      (Icc α β ×ˢ (univ : Set E)) := by
    change ContDiffOn ℝ ∞
      (fun p : ℝ × E => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ ((extChartAt 𝓘(ℝ, E) x₀).symm p.2) i j)
      (Icc α β ×ˢ V) at hentry
    simpa only [V, extChartAt_model_space_eq_id, PartialEquiv.refl_target, interior_univ,
      PartialEquiv.refl_symm, PartialEquiv.refl_coe, id_eq] using hentry
  rw [← modelWithCornersSelf_prod, chartedSpaceSelf_prod]
  exact (hnative.mono (prod_mono subset_rfl (subset_univ _))).contMDiffOn

private theorem equation_closed (g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (α β : ℝ) (hab : α < β)
    (hgram : ∀ (x₀ : E) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × E => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ p.2 i j)
        (Icc α β ×ˢ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).baseSet))
    (hpde : ∀ t ∈ Ioo α β, ∀ (x : E) (v w : TangentSpace 𝓘(ℝ, E) x),
      HasDerivAt (fun s => (g s).inner x v w) (-2 * ricciTensor (g t) x v w) t) :
    ∀ t ∈ Icc α β, ∀ (x : E) (v w : TangentSpace 𝓘(ℝ, E) x),
      HasDerivWithinAt (fun s => (g s).inner x v w) (-2 * ricciTensor (g t) x v w) (Icc α β) t := by
  have hRicField := ricciCont_of_joint g (Icc α β) (uniqueDiffOn_Icc hab) hgram
  intro t ht x v w
  have hg : ContinuousOn (fun s => (g s).inner x v w) (Icc α β) := by
    exact (tensor0SEvalCLM (I := 𝓘(ℝ, E)) (vec2 v w)).continuous.comp_continuousOn
      (metricCovDeriv_contDiffOn_time g (Icc α β) hgram (g α) 0 x).continuousOn
  have hRic : ContinuousOn (fun s => ricciTensor (g s) x v w) (Icc α β) := by
    rw [continuousOn_iff_continuous_domRestrict]
    change Continuous (fun s : Icc α β => ricciTensor (g s.val) x v w)
    have hh := hRicField.eval_continuous
      (P := Icc α β) (τ := Subtype.val) (b := fun _ => x)
      continuous_subtype_val (fun s => s.property) continuous_const
      (v := fun i _ => vec2 v w i) (fun _ => continuous_const)
    simpa only [metricRicciAt_apply_eq_ricciTensor] using hh
  exact hasDerivIcc_of_int hab hg (continuousOn_const.mul hRic)
    (fun s hs => hpde s hs x v w) ht

theorem contMDiffOn_and_equation_Icc_of_spatial_jets
    (g : ℝ → SmoothRiemannianMetric 𝓘(ℝ, E) E)
    (α β : ℝ) (hab : α < β)
    (hjets : ∀ (r : ℕ) (x₀ : E) (i j : Fin (Module.finrank ℝ E)),
      ContinuousOn (fun p : ℝ × E => iteratedFDeriv ℝ r (chartGramOnE (g p.1) x₀ i j) p.2)
        (Icc α β ×ˢ interior (extChartAt 𝓘(ℝ, E) x₀).target))
    (hpde : ∀ t ∈ Ioo α β, ∀ (x : E) (v w : TangentSpace 𝓘(ℝ, E) x),
      HasDerivAt (fun s => (g s).inner x v w) (-2 * ricciTensor (g t) x v w) t) :
    (∀ (x₀ : E) (i j : Fin (Module.finrank ℝ E)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
        (fun p : ℝ × E => DifferentialGeometry.Tensor.Coordinates.chartGramMatrix (g p.1) x₀ p.2 i j)
        (Icc α β ×ˢ (trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).baseSet)) ∧
      ∀ t ∈ Icc α β, ∀ (x : E) (v w : TangentSpace 𝓘(ℝ, E) x),
        HasDerivWithinAt (fun s => (g s).inner x v w)
          (-2 * ricciTensor (g t) x v w) (Icc α β) t := by
  have hgram := closed_metric_gram g α β hab hjets hpde
  exact ⟨hgram, equation_closed g α β hab hgram hpde⟩

end DifferentialGeometry.PDE.RicciFlow
