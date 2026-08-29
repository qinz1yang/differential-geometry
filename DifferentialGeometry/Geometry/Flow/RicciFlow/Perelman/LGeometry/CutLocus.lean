import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.CutInjectivity

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bornology Bundle Filter Function Set
open scoped ContDiff Manifold Topology

open DifferentialGeometry.Geometry.Curvature

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

def lCutDomain
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (tau : Real) : Set E :=
  {Z | IsGreatest {sigma : Real | (Z, sigma) ∈ lMinDomain S T x} tau}

def lCutImage
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (tau : Real) : Set M :=
  (fun Z : E ↦ lExp S T x Z tau) '' lCutDomain S T x tau

def lCutConj
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (tau : Real) : Set M :=
  {y | ∃ Z : E, Z ∈ lCutDomain S T x tau ∧
    IsLConj S T x Z tau ∧ lExp S T x Z tau = y}

def lCutMulti
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (tau : Real) : Set M :=
  {y | ∃ Z : E, Z ∈ lCutDomain S T x tau ∧
    ∃ W : TangentSpace I x, W ≠ Z ∧
      ((W : E), tau) ∈ lMinDomain S T x ∧
        lExp S T x W tau = lExp S T x Z tau ∧ lExp S T x Z tau = y}

omit [NeZero (Module.finrank Real E)] [CompactSpace M] in
theorem mem_lCutDomain
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M)
    (tau : Real) (Z : E) :
    Z ∈ lCutDomain S T x tau ↔
      (Z, tau) ∈ lMinDomain S T x ∧ Z ∉ lInjDomain S T x tau := by
  constructor
  · intro hcut
    refine ⟨hcut.1, ?_⟩
    rintro ⟨sigma, hsigma, hmin⟩
    exact (not_lt_of_ge (hcut.2 hmin)) hsigma
  · rintro ⟨hmin, hnot⟩
    refine ⟨hmin, ?_⟩
    intro sigma hminSigma
    apply le_of_not_gt
    intro hlt
    exact hnot ⟨sigma, hlt, hminSigma⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem lMinSlice_closed
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (tau : Real) (htau : 0 < tau) :
    IsClosed {Z : E | (Z, tau) ∈ lMinDomain S T x} := by
  rw [← isSeqClosed_iff_isClosed]
  intro Z Z₀ hmin hZ
  have hdom0 : (Z 0, tau) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x (Z 0) tau).1 (hmin 0)).1
  let b : Real := Real.sqrt tau
  have hb : 0 ≤ b := by
    exact Real.sqrt_nonneg _
  have hb2 : b ^ 2 = tau := by
    simpa only [b] using Real.sq_sqrt htau.le
  have hslab : Icc (T - b ^ 2) T ⊆ D.regular := by
    intro r hr
    have hnonneg : 0 ≤ T - r := by
      linarith [hr.2]
    have hle : T - r ≤ tau := by
      rw [hb2] at hr
      linarith [hr.1]
    have hsqrt : Real.sqrt (T - r) ∈ Icc (0 : Real) (Real.sqrt tau) :=
      ⟨Real.sqrt_nonneg _, Real.sqrt_le_sqrt hle⟩
    have hreg := lExpPosDom_reg S T x (Z 0) hdom0 hsqrt
    have heq : T - (Real.sqrt (T - r)) ^ 2 = r := by
      rw [Real.sq_sqrt hnonneg]
      ring
    simpa only [heq] using hreg
  have hreg : b ∈ lRegDomain S T x Z₀ :=
    lRegDomain_of_slab S hS T x Z₀ b hb hslab
  have hdom : (Z₀, tau) ∈ lExpPosDom S T x :=
    (mem_lExpPosDom S T x Z₀ tau).2 ⟨htau, htau.le, by
      simpa only [b] using hreg⟩
  exact lMinVec_lim S hS T x hmin hZ hdom

theorem lCutDom_closed
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (tau : Real) (htau : 0 < tau) :
    IsClosed (lCutDomain S T x tau) := by
  have hslice := lMinSlice_closed S hS T x tau htau
  have hinj := (lInj_isOpen S hS T x tau).isClosed_compl
  rw [show lCutDomain S T x tau =
      {Z : E | (Z, tau) ∈ lMinDomain S T x} ∩ (lInjDomain S T x tau)ᶜ by
    ext Z
    simpa only [mem_ofPred_eq, mem_inter_iff, mem_compl_iff] using
      (mem_lCutDomain S T x tau Z)]
  exact hslice.inter hinj

theorem lCutDom_meas
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (tau : Real) (htau : 0 < tau) :
    MeasurableSet (lCutDomain S T x tau) :=
  (lCutDom_closed S hS T x tau htau).measurableSet

theorem lCut_split
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (x : M) (tau : Real) :
    lCutImage S T x tau = lCutConj S T x tau ∪ lCutMulti S T x tau := by
  ext y
  constructor
  · rintro ⟨Z, hcut, rfl⟩
    rcases lCut_alt S hS T x Z tau hcut with hconj | ⟨W, hWne, hWmin, hend⟩
    · exact Or.inl ⟨Z, hcut, hconj, rfl⟩
    · exact Or.inr ⟨Z, hcut, W, hWne, hWmin, hend, rfl⟩
  · rintro (⟨Z, hcut, hconj, rfl⟩ | ⟨Z, hcut, W, hWne, hWmin, hend, rfl⟩)
    · exact ⟨Z, hcut, rfl⟩
    · exact ⟨Z, hcut, rfl⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman
