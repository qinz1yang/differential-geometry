import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.SlabTimeTranslation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.RetainedCoreTower
set_option autoImplicit false
noncomputable section
open Set
open scoped Manifold ContDiff
namespace GC.GeneralFlow
open DifferentialGeometry
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u

theorem translated_terminal_region {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) (c : ℝ) :
    (G.timeTranslate c).terminalRegularRegion = G.terminalRegularRegion := by
  ext x
  constructor
  · rintro ⟨U,hU,hx,d,hd,K,hK,hb⟩
    refine ⟨U,hU,hx,d-c,⟨by linarith [hd.1],by linarith [hd.2]⟩,K,hK,?_⟩
    intro y hy t ht
    have h := hb y hy (t+c) ⟨by linarith [ht.1],by linarith [ht.2]⟩
    simpa only [OrientedThreeStage.IncomingSlab.timeTranslate_riemannNorm,
      add_sub_cancel_right] using h
  · rintro ⟨U,hU,hx,d,hd,K,hK,hb⟩
    refine ⟨U,hU,hx,d+c,⟨by linarith [hd.1],by linarith [hd.2]⟩,K,hK,?_⟩
    intro y hy t ht
    exact hb y hy (t-c) ⟨by linarith [ht.1],by linarith [ht.2]⟩

theorem translated_terminal_open {P : OrientedThreeStage.{u}} {a s : ℝ}
    (G : P.IncomingSlab a s) (c : ℝ) :
    (G.timeTranslate c).terminalRegularOpen = G.terminalRegularOpen := by
  apply SetLike.coe_injective
  exact translated_terminal_region G c

private theorem translated_convergence {P : OrientedThreeStage.{u}}
    (U V : TopologicalSpace.Opens P.Carrier) (hUV : U = V)
    (g : ℝ → P.Metric) (m : SmoothRiemannianMetric ThreeModel U)
    (a s c : ℝ)
    (h : ∀ K : Set U, IsCompact K → ∀ j ε, 0 < ε → ∃ d ∈ Ico a s,
      ∀ t ∈ Ioo d s, ∀ x ∈ K,
        CheegerGromovCompactness.metricDerivNorm j ((g t).restrictOpen U) m m x < ε) :
    ∀ K : Set V, IsCompact K → ∀ j ε, 0 < ε → ∃ d ∈ Ico (a+c) (s+c),
      ∀ t ∈ Ioo d (s+c), ∀ x ∈ K,
        CheegerGromovCompactness.metricDerivNorm j ((g (t-c)).restrictOpen V)
          (hUV ▸ m) (hUV ▸ m) x < ε := by
  cases hUV
  intro K hK j ε hε
  obtain ⟨d,hd,hb⟩ := h K hK j ε hε
  refine ⟨d+c,⟨by linarith [hd.1],by linarith [hd.2]⟩,?_⟩
  intro t ht x hx
  exact hb (t-c) ⟨by linarith [ht.1],by linarith [ht.2]⟩ x hx

def translate_terminal_metric {P : OrientedThreeStage.{u}} {a s : ℝ}
    {G : P.IncomingSlab a s} (L : G.TerminalLimitMetric) (c : ℝ) :
    (G.timeTranslate c).TerminalLimitMetric where
  metric := (translated_terminal_open G c).symm ▸ L.metric
  converges := translated_convergence G.terminalRegularOpen
    (G.timeTranslate c).terminalRegularOpen (translated_terminal_open G c).symm
    G.flow.base.metric L.metric a s c L.converges

end GC.GeneralFlow
