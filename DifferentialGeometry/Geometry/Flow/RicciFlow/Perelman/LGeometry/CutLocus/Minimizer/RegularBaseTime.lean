import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.Injectivity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutLocus.Minimizer.Domain
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Geodesic.ExponentialMap

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Set
open scoped ContDiff Manifold Topology

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]
variable {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem mem_lRegularizedDomain_zero_of_nonempty
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x : M) (Z : TangentSpace I x)
    (h : (lRegularizedDomain S T x Z).Nonempty) :
    (0 : ℝ) ∈ lRegularizedDomain S T x Z := by
  obtain ⟨s, alpha, J, hJ, hJc, h0J, hsJ, hcurve⟩ := h
  exact ⟨alpha, J, hJ, hJc, h0J, h0J, hcurve⟩

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem mem_regular_of_nonempty_lRegularizedDomain
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x : M) (Z : TangentSpace I x)
    (h : (lRegularizedDomain S T x Z).Nonempty) :
    T ∈ D.regular := by
  have h0 := mem_lRegularizedDomain_zero_of_nonempty S T x Z h
  simpa using lRegularizedDomain_regularity S T x Z h0

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lExpPosDom_eq_empty_of_notMem_regular
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x : M) (hT : T ∉ D.regular) :
    lExpPosDom S T x = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro ⟨Z, tau⟩ hp
  rw [lExpPosDom, Set.mem_ofPred_eq] at hp
  exact hT (mem_regular_of_nonempty_lRegularizedDomain S T x Z
    ⟨Real.sqrt tau, by simpa only [lRegularizedJointDom, Set.mem_ofPred_eq] using hp.2⟩)

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lMinDomain_eq_empty_of_notMem_regular
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x : M) (hT : T ∉ D.regular) :
    lMinDomain S T x = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro ⟨Z, tau⟩ hp
  exact Set.eq_empty_iff_forall_notMem.mp (lExpPosDom_eq_empty_of_notMem_regular S T x hT)
    ⟨Z, tau⟩ ((mem_lMinDomain S T x Z tau).1 hp).1

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lInjDomain_eq_empty_of_notMem_regular
    (S : SolutionOn (I := I) (M := M) D) (T : ℝ) (x : M) (tau : ℝ)
    (hT : T ∉ D.regular) :
    lInjDomain S T x tau = ∅ := by
  rw [Set.eq_empty_iff_forall_notMem]
  rintro Z ⟨sigma, _hsigma, hZmin⟩
  exact Set.eq_empty_iff_forall_notMem.mp (lMinDomain_eq_empty_of_notMem_regular S T x hT)
    ⟨Z, sigma⟩ hZmin

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
theorem lExpPosDom_nonempty_iff_mem_regular
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : ℝ) (x : M) :
    (lExpPosDom S T x).Nonempty ↔ T ∈ D.regular := by
  constructor
  · rintro ⟨⟨Z, tau⟩, hp⟩
    rw [lExpPosDom, Set.mem_ofPred_eq] at hp
    exact mem_regular_of_nonempty_lRegularizedDomain S T x Z
      ⟨Real.sqrt tau, by simpa only [lRegularizedJointDom, Set.mem_ofPred_eq] using hp.2⟩
  · intro hT
    obtain ⟨epsilon, hepsilon, alpha, h0, hvel, hgeo⟩ :=
      exists_lRegularizedCurve S hS T x (0 : TangentSpace I x) hT
    have hzero : (0 : ℝ) ∈ Set.Ioo (-epsilon) epsilon := ⟨by linarith, by linarith⟩
    have hhalf : epsilon / 2 ∈ Set.Ioo (-epsilon) epsilon := ⟨by linarith, by linarith⟩
    have hmem : epsilon / 2 ∈ lRegularizedDomain S T x (0 : TangentSpace I x) :=
      ⟨alpha, Set.Ioo (-epsilon) epsilon, isOpen_Ioo, isPreconnected_Ioo,
        hzero, hhalf, h0, hvel, hgeo⟩
    refine ⟨((0 : TangentSpace I x), (epsilon / 2) ^ 2), ?_⟩
    simp only [lExpPosDom, lRegularizedJointDom, Set.mem_ofPred_eq]
    exact ⟨by positivity, by rwa [Real.sqrt_sq (by positivity)]⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman
