import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.InitialTerminalRegionFrontier
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalSmoothSphericalRegion
import DifferentialGeometry.Geometry.Neck.Chart

set_option autoImplicit false
noncomputable section
open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Topology (SmoothTwoSidedCollar symmetricOpenInterval)
open scoped Manifold ContDiff Topology
namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Contract
universe u
variable {D : OneStepIncoming.{u}} {W : SmoothSphericalRegion D.stage} {ε : ℝ}

noncomputable def TerminalNeckFrontier.ofUniformSmoothRegionData
    (F : ∃ η : ℝ, η < ε ∧
      ∀ b : W.Boundary, ∃ chart : DifferentialGeometry.Geometry.Neck.cylindricalChart
        ThreeModel (M := D.slab.terminalRegularOpen),
        ∃ level : ℝ, level ∈ Icc (-4 : ℝ) 4 ∧
        (∀ y t, t ∈ Icc (-101 : ℝ) 101 → (y, t) ∈ chart.domain) ∧
        (∀ y, ∃ hy : (y, level) ∈ chart.domain,
          (chart.chart ⟨(y, level), hy⟩ : D.slab.terminalRegularOpen).1 =
            (W.sphere b y).1) ∧
        chart.metricCloseOn D.terminal.metric η
          {z : chart.domain | (z.1.2 : ℝ) ∈ Icc (-101 : ℝ) 101} ∧
        ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
          ∃ c : SmoothTwoSidedCollar (𝓡 2) ThreeModel
            (fun y : Sphere 2 => (W.sphere b y).1),
            c.radius < 1 ∧
            (∀ p : Sphere 2 × symmetricOpenInterval c.radius,
              ∃ hp : (p.1, level + σ * (p.2 : ℝ)) ∈ chart.domain,
                c.toFun p =
                  (chart.chart ⟨(p.1, level + σ * (p.2 : ℝ)), hp⟩ :
                    D.slab.terminalRegularOpen).1) ∧
            (∀ p : Sphere 2 × symmetricOpenInterval c.radius,
              c.toFun p ∈ W.region ↔ (p.2 : ℝ) ≤ 0)) :
    TerminalNeckFrontier D W ε := by
  classical
  let η := Classical.choose F
  have hF := Classical.choose_spec F
  have hη : η < ε := hF.1
  have hFchart : ∀ b : W.Boundary, ∃ chart : DifferentialGeometry.Geometry.Neck.cylindricalChart
        ThreeModel (M := D.slab.terminalRegularOpen),
        ∃ level : ℝ, level ∈ Icc (-4 : ℝ) 4 ∧
        (∀ y t, t ∈ Icc (-101 : ℝ) 101 → (y, t) ∈ chart.domain) ∧
        (∀ y, ∃ hy : (y, level) ∈ chart.domain,
          (chart.chart ⟨(y, level), hy⟩ : D.slab.terminalRegularOpen).1 =
            (W.sphere b y).1) ∧
        chart.metricCloseOn D.terminal.metric η
          {z : chart.domain | (z.1.2 : ℝ) ∈ Icc (-101 : ℝ) 101} ∧
        ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
          ∃ c : SmoothTwoSidedCollar (𝓡 2) ThreeModel
            (fun y : Sphere 2 => (W.sphere b y).1),
            c.radius < 1 ∧
            (∀ p : Sphere 2 × symmetricOpenInterval c.radius,
              ∃ hp : (p.1, level + σ * (p.2 : ℝ)) ∈ chart.domain,
                c.toFun p =
                  (chart.chart ⟨(p.1, level + σ * (p.2 : ℝ)), hp⟩ :
                    D.slab.terminalRegularOpen).1) ∧
            (∀ p : Sphere 2 × symmetricOpenInterval c.radius,
              c.toFun p ∈ W.region ↔ (p.2 : ℝ) ≤ 0) := hF.2
  choose chart hchart using hFchart
  choose level hlevel using hchart
  have hlevel_mem : ∀ b, level b ∈ Icc (-4 : ℝ) 4 := fun b => (hlevel b).1
  have hdomain : ∀ b (y : Sphere 2) t, t ∈ Icc (-101 : ℝ) 101 →
      (y, t) ∈ (chart b).domain := fun b y t ht => (hlevel b).2.1 y t ht
  have hboundary : ∀ b (y : Sphere 2), ∀ hy : (y, level b) ∈ (chart b).domain,
      ((chart b).chart ⟨(y, level b), hy⟩ : D.slab.terminalRegularOpen).1 =
        (W.sphere b y).1 := by
    intro b y hy
    obtain ⟨hy', h⟩ := (hlevel b).2.2.1 y
    have heq : (⟨(y, level b), hy⟩ : (chart b).domain) =
        ⟨(y, level b), hy'⟩ := Subtype.ext (by rfl)
    rw [heq]
    exact h
  have hmetric : ∀ b,
      (chart b).metricCloseOn D.terminal.metric η
        {z : (chart b).domain | (z.1.2 : ℝ) ∈ Icc (-101 : ℝ) 101} :=
    fun b => (hlevel b).2.2.2.1
  have htail : ∀ b, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
      ∃ c : SmoothTwoSidedCollar (𝓡 2) ThreeModel
        (fun y : Sphere 2 => (W.sphere b y).1),
        c.radius < 1 ∧
        (∀ p : Sphere 2 × symmetricOpenInterval c.radius,
          ∃ hp : (p.1, level b + σ * (p.2 : ℝ)) ∈ (chart b).domain,
            c.toFun p =
              ((chart b).chart ⟨(p.1, level b + σ * (p.2 : ℝ)), hp⟩ :
                D.slab.terminalRegularOpen).1) ∧
        (∀ p : Sphere 2 × symmetricOpenInterval c.radius,
          c.toFun p ∈ W.region ↔ (p.2 : ℝ) ≤ 0) := fun b => (hlevel b).2.2.2.2
  choose collarSign hsign htail using htail
  choose collar hcollar using htail
  have hcollar_radius : ∀ b, (collar b).radius < 1 :=
    fun b => (hcollar b).1
  have hcollar_chart : ∀ b (p : Sphere 2 × symmetricOpenInterval (collar b).radius),
      ∃ hp : (p.1, level b + collarSign b * (p.2 : ℝ)) ∈ (chart b).domain,
        (collar b).toFun p =
          ((chart b).chart ⟨(p.1, level b + collarSign b * (p.2 : ℝ)), hp⟩ :
            D.slab.terminalRegularOpen).1 := by
    intro b p
    exact (hcollar b).2.1 p
  have hcollar_region : ∀ b (p : Sphere 2 × symmetricOpenInterval (collar b).radius),
      (collar b).toFun p ∈ W.region ↔ (p.2 : ℝ) ≤ 0 :=
    fun b => (hcollar b).2.2
  exact {
    chart := chart
    level := level
    level_mem := hlevel_mem
    chart_domain := hdomain
    boundary_eq := hboundary
    metric_close := ⟨η, hη, hmetric⟩
    collar := collar
    collarSign := collarSign
    collar_sign_unit := hsign
    collar_chart := hcollar_chart
    collar_region := hcollar_region }

end DifferentialGeometry.PDE.RicciFlow.Surgery.Contract
