import DifferentialGeometry.Topology.Engulfing.Newman.Membrane.NewmanAssignedCharts

namespace DifferentialGeometry.Topology.Engulfing

open Set Metric _root_.Geometry _root_.Topology
open scoped ContinuousMap

noncomputable section

set_option linter.unusedSectionVars false

variable {M : Type*} [MetricSpace M]

def preservesCoreValues {Z : Type*} (C : Set M) (f g : Z → M) : Prop :=
  (∀ x, g x ∈ C ↔ f x ∈ C) ∧ ∀ x, f x ∈ C → g x = f x

theorem preservesCoreValues.refl {Z : Type*} (C : Set M) (f : Z → M) :
    preservesCoreValues C f f := ⟨fun _ => Iff.rfl, fun _ _ => rfl⟩

theorem preservesCoreValues.trans {Z : Type*} {C : Set M} {f g h : Z → M}
    (hfg : preservesCoreValues C f g) (hgh : preservesCoreValues C g h) :
    preservesCoreValues C f h :=
  ⟨fun x => (hgh.1 x).trans (hfg.1 x),
    fun x hx => (hgh.2 x ((hfg.1 x).mpr hx)).trans (hfg.2 x hx)⟩

def homeomorphCoreComplement (C : Set M) (e : M ≃ₜ M)
    (he : ∀ x ∈ C, e x = x) : ↥(Cᶜ) ≃ₜ ↥(Cᶜ) :=
  e.subtype (by
    intro x
    change x ∉ C ↔ e x ∉ C
    constructor
    · intro hx hex
      have heq : e x = x := e.injective (he (e x) hex)
      exact hx (heq ▸ hex)
    · intro hx hxc
      exact hx ((he x hxc).symm ▸ hxc))

def coreProtectedConnectivity (C U : Set M) (p : ℕ) : Prop :=
  NewmanConnectivity ↥(Cᶜ) (Subtype.val ⁻¹' U) p

theorem coreProtectedConnectivity.mono {C U : Set M} {p r : ℕ}
    (h : coreProtectedConnectivity C U p) (hrp : r ≤ p) :
    coreProtectedConnectivity C U r := NewmanConnectivity.mono h hrp

theorem coreProtectedConnectivity.image {C U : Set M} {p : ℕ}
    (h : coreProtectedConnectivity C U p) (e : M ≃ₜ M)
    (he : ∀ x ∈ C, e x = x) : coreProtectedConnectivity C (e '' U) p := by
  let c := homeomorphCoreComplement C e he
  have hsets : c '' (Subtype.val ⁻¹' U) =
      (Subtype.val ⁻¹' (e '' U) : Set ↥(Cᶜ)) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.1, hx, rfl⟩
    · rintro ⟨x, hx, hxy⟩
      have hxc : x ∈ Cᶜ := by
        intro hxc
        have hex : e x ∈ C := (he x hxc).symm ▸ hxc
        exact y.2 (hxy ▸ hex)
      exact ⟨⟨x, hxc⟩, hx, Subtype.ext hxy⟩
  change NewmanConnectivity ↥(Cᶜ) (Subtype.val ⁻¹' (e '' U)) p
  rw [← hsets]
  exact NewmanConnectivity.image h c

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def hasAdaptedPiecewiseLinearChartsOffCore (K L : SimplicialComplex ℝ E) (f : C(K.space, M))
    (C : Set M) (n p : ℕ) : Prop :=
  ∀ y ∉ C, ∃ b : AdaptedPiecewiseLinearChart K L f ∅ n p,
    y ∈ b.toBufferedChart.core ∧ Disjoint b.chart.source C

theorem hasAdaptedPiecewiseLinearChartsOffCore.withMap {K L : SimplicialComplex ℝ E}
    {f : C(K.space, M)} {C : Set M} {n p : ℕ}
    (h : hasAdaptedPiecewiseLinearChartsOffCore K L f C n p) (g : C(K.space, M))
    (hfix : ∀ x : K.space, x.1 ∈ L.space → g x = f x) :
    hasAdaptedPiecewiseLinearChartsOffCore K L g C n p := by
  intro y hy
  obtain ⟨b, hb, hsource⟩ := h y hy
  exact ⟨b.withMap g hfix, hb, hsource⟩

structure CoreProtectedNewmanProblem (E M : Type*) [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MetricSpace M] (n p q : ℕ) where
  source : SimplicialComplex ℝ E
  fixed : SimplicialComplex ℝ E
  target : SimplicialComplex ℝ E
  source_finite : source.faces.Finite
  fixed_subcomplex : fixed.faces ⊆ source.faces
  target_subcomplex : target.faces ⊆ source.faces
  source_dimension : ∀ s ∈ source.faces, s.card ≤ p + 2
  target_dimension : ∀ s ∈ target.faces, s.card ≤ p + 1
  map : C(source.space, M)
  fixed_injective : InjOn map (Subtype.val ⁻¹' fixed.space)
  core : Set M
  openSet : Set M
  core_closed : IsClosed core
  open_openSet : IsOpen openSet
  core_subset : core ⊆ openSet
  localData : hasAdaptedPiecewiseLinearChartsOffCore source fixed map core n p
  codimension : p + 3 ≤ n
  connectivity : coreProtectedConnectivity core openSet p
  decomposition : engulfingDecomposition source target map openSet q

def CoreProtectedNewmanProblem.conclusion {n p q : ℕ}
    (P : CoreProtectedNewmanProblem E M n p q) (ε : ℝ) : Prop :=
  ∃ (g : C(P.source.space, M)) (h : M ≃ₜ M),
    (∀ x : P.source.space, x.1 ∈ P.fixed.space → g x = P.map x) ∧
    preservesCoreValues P.core P.map g ∧
    (∀ x, dist (g x) (P.map x) < ε) ∧
    P.core ∪ g '' (Subtype.val ⁻¹' P.target.space) ⊆ h '' P.openSet ∧
    (∀ x ∈ P.core, h x = x) ∧ IsCompact (closure {x | h x ≠ x})

theorem CoreProtectedNewmanProblem.conclusion_zero {n p : ℕ}
    (P : CoreProtectedNewmanProblem E M n p 0) {ε : ℝ} (hε : 0 < ε) :
    P.conclusion ε := by
  refine ⟨P.map, Homeomorph.refl M, fun _ _ => rfl,
    preservesCoreValues.refl _ _, fun _ => by simpa using hε, ?_, fun _ _ => rfl, ?_⟩
  · intro y hy
    refine ⟨y, ?_, rfl⟩
    exact hy.elim (fun hy => P.core_subset hy)
      (fun hy => P.decomposition.to_outsideDimension.zero_covered hy)
  · simp

theorem CoreProtectedNewmanProblem.conclusion.to_newmanConclusion {n p q : ℕ}
    {P : CoreProtectedNewmanProblem E M n p q} {ε : ℝ} (h : P.conclusion ε) :
    newmanConclusion P.source P.fixed P.target P.map P.core P.openSet ε := by
  obtain ⟨g, H, hfix, _, hnear, hcover, _, hcompact⟩ := h
  exact ⟨g, H, hfix, hnear, hcover, hcompact⟩

def coreProtectedRelativeNewmanAt (M : Type*) [MetricSpace M] (n p q : ℕ) : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E],
    ∀ P : CoreProtectedNewmanProblem E M n p q, ∀ ε : ℝ, 0 < ε → P.conclusion ε

theorem coreProtectedRelativeNewmanAt_zero (n p : ℕ) :
    coreProtectedRelativeNewmanAt M n p 0 := by
  intro E _ _ _ P ε hε
  exact P.conclusion_zero hε

def coreProtectedSingleSimplexNewmanAt (M : Type*) [MetricSpace M] (n p q : ℕ) : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E],
    ∀ P : CoreProtectedNewmanProblem E M n p (q + 1), ∀ s : Finset E,
      s ∈ P.target.faces → s.card = q + 1 →
      (∀ t ∈ P.target.faces, t ≠ s →
        ∀ x : P.source.space, x.1 ∈ convexHull ℝ (t : Set E) → P.map x ∈ P.openSet) →
      Disjoint (P.map '' (Subtype.val ⁻¹' convexHull ℝ (s : Set E))) P.core →
      ∀ ε : ℝ, 0 < ε → P.conclusion ε

end

end DifferentialGeometry.Topology.Engulfing
