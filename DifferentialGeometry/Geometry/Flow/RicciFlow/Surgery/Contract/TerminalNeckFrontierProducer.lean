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

noncomputable def TerminalNeckFrontier.ofSmoothRegion
    (F : ∀ b : W.Boundary, ∃ chart : DifferentialGeometry.Geometry.Neck.cylindricalChart
        ThreeModel (M := D.slab.terminalRegularOpen),
        ∃ level : ℝ, level ∈ Icc (-4 : ℝ) 4 ∧
        (∀ y t, t ∈ Icc (-101 : ℝ) 101 → (y, t) ∈ chart.domain) ∧
        (∀ y, ∃ hy : (y, level) ∈ chart.domain,
          (chart.chart ⟨(y, level), hy⟩ : D.slab.terminalRegularOpen).1 =
            (W.sphere b y).1) ∧
        ∃ η : ℝ, η < ε ∧ chart.metricCloseOn D.terminal.metric η
          {z : chart.domain | (z.1.2 : ℝ) ∈ Icc (-101 : ℝ) 101} ∧
        ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
          ∃ c : SmoothTwoSidedCollar (𝓡 2) ThreeModel
          (fun y : Sphere 2 => (W.sphere b y).1),
            (∀ p : Sphere 2 × symmetricOpenInterval c.radius,
              ∃ hp : (p.1, level + σ * (p.2 : ℝ)) ∈ chart.domain,
                c.toFun p =
                  (chart.chart ⟨(p.1, level + σ * (p.2 : ℝ)), hp⟩ :
                    D.slab.terminalRegularOpen).1) ∧
            (∀ p : Sphere 2 × symmetricOpenInterval c.radius,
              c.toFun p ∈ W.region ↔ (p.2 : ℝ) ≤ 0)) :
    TerminalNeckFrontier D W ε := by
  classical
  letI := W.finiteBoundary
  choose chart hchart using F
  choose level hlevel using hchart
  let eta_b : W.Boundary → ℝ := fun b =>
    Classical.choose ((hlevel b).2.2.2)
  have heta_b : ∀ b, eta_b b < ε := fun b =>
    (Classical.choose_spec ((hlevel b).2.2.2)).1
  let s : Finset W.Boundary := Finset.univ
  let η : ℝ := if hs : s.Nonempty then s.sup' hs eta_b else ε - 1
  have hη : η < ε := by
    by_cases hs : s.Nonempty
    · simp only [η, dite_eq_left hs]
      exact (Finset.sup'_lt_iff hs).2 (fun b _ => heta_b b)
    · simp only [η, dite_eq_right hs]
      linarith
  have hηle (b : W.Boundary) : eta_b b ≤ η := by
    by_cases hs : s.Nonempty
    · simp only [η, dite_eq_left hs]
      exact Finset.le_sup' eta_b (Finset.mem_univ b)
    · have hb : b ∈ s := by simp [s]
      exact (hs ⟨b, hb⟩).elim
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
        {z : (chart b).domain | (z.1.2 : ℝ) ∈ Icc (-101 : ℝ) 101} := by
    intro b x hx k hk
    exact le_trans
      ((Classical.choose_spec ((hlevel b).2.2.2)).2.1 x hx k hk)
      (hηle b)
  have htail : ∀ b, ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
        ∃ c : SmoothTwoSidedCollar (𝓡 2) ThreeModel
        (fun y : Sphere 2 => (W.sphere b y).1),
        (∀ p : Sphere 2 × symmetricOpenInterval c.radius,
          ∃ hp : (p.1, level b + σ * (p.2 : ℝ)) ∈ (chart b).domain,
            c.toFun p =
              ((chart b).chart ⟨(p.1, level b + σ * (p.2 : ℝ)), hp⟩ :
                D.slab.terminalRegularOpen).1) ∧
        (∀ p : Sphere 2 × symmetricOpenInterval c.radius,
        c.toFun p ∈ W.region ↔ (p.2 : ℝ) ≤ 0) := fun b =>
    (Classical.choose_spec ((hlevel b).2.2.2)).2.2
  choose collarSign hsign htail using htail
  choose collar hcollar using htail
  have hcollar_chart : ∀ b (p : Sphere 2 × symmetricOpenInterval (collar b).radius),
      ∃ hp : (p.1, level b + collarSign b * (p.2 : ℝ)) ∈ (chart b).domain,
        (collar b).toFun p =
          ((chart b).chart ⟨(p.1, level b + collarSign b * (p.2 : ℝ)), hp⟩ :
            D.slab.terminalRegularOpen).1 := by
    intro b p
    exact (hcollar b).1 p
  have hcollar_region : ∀ b (p : Sphere 2 × symmetricOpenInterval (collar b).radius),
      (collar b).toFun p ∈ W.region ↔ (p.2 : ℝ) ≤ 0 :=
    fun b => (hcollar b).2
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
  have hFb := hF.2
  choose chart hchart using hFb
  choose level hlevel using hchart
  apply TerminalNeckFrontier.ofSmoothRegion
  intro b
  refine ⟨chart b, level b, (hlevel b).1, (hlevel b).2.1, (hlevel b).2.2.1, ?_⟩
  exact ⟨η, hη, (hlevel b).2.2.2.1, (hlevel b).2.2.2.2⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Contract
