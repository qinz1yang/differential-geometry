import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.Convergence

open DifferentialGeometry.PDE.RicciFlow
open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

open Set Function Filter Bundle Manifold
open scoped Manifold Topology ContDiff BigOperators

namespace DifferentialGeometry
namespace CheegerGromovCompactness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {X : PointedFlowSeq (I := I)}
variable {P : PointedRiemannianManifold (I := I)}
variable {subseq : Nat → Nat}
variable (Φ : PointedCGHMaps (I := I) X P subseq)

structure HalfLineMetricConvergenceData
    (R : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ) where
  φ : Nat → Nat
  strictMono : StrictMono φ
  gInf : letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    Real → SmoothRiemannianMetric I P.M
  convergenceOn : ∀ n : Nat,
    BumpMetricConvergence (I := I) Φ R bf hsrc htgt φ gInf (-(n : Real)) 0

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
theorem nonempty_halfLineMetricConvergenceData
    {R : letI : TopologicalSpace P.M := P.topology;
      letI : ChartedSpace H P.M := P.charted; letI : IsManifold I ∞ P.M := P.smooth;
      SmoothRiemannianMetric I P.M}
    {bf : BumpFamily (I := I) Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
    (hrefine : ∀ n : Nat, ∀ ρ : Nat → Nat, StrictMono ρ →
      ∃ τ : Nat → Nat, StrictMono τ ∧
        ∃ gN : letI : TopologicalSpace P.M := P.topology
          letI : ChartedSpace H P.M := P.charted
          letI : IsManifold I ∞ P.M := P.smooth
          Real → SmoothRiemannianMetric I P.M,
          BumpMetricConvergence (I := I) Φ R bf hsrc htgt (ρ ∘ τ) gN (-(n : Real)) 0) :
    Nonempty (HalfLineMetricConvergenceData (I := I) Φ R bf hsrc htgt) := by
  classical
  let Pwin : Nat → (Nat → Nat) → Prop := fun n ρ =>
    ∃ gN : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      Real → SmoothRiemannianMetric I P.M,
      BumpMetricConvergence (I := I) Φ R bf hsrc htgt ρ gN (-(n : Real)) 0
  obtain ⟨φ, hφ, hPφ⟩ := exists_diag_subseq Pwin
    (fun n ρ hρ => by
      obtain ⟨τ, hτ, gN, hgN⟩ := hrefine n ρ hρ
      exact ⟨τ, hτ, gN, hgN⟩)
    (fun _n _ρ τ hτ hP => by
      obtain ⟨gN, hgN⟩ := hP
      exact ⟨gN, BumpMetricConvergence.comp (Φ := Φ) hgN τ hτ⟩)
    (fun _n ρ m hP => by
      obtain ⟨gN, hgN⟩ := hP
      exact ⟨gN, BumpMetricConvergence.of_tail (Φ := Φ) m hgN⟩)
  choose gN hgN using hPφ
  let idx : Real → Nat := fun t =>
    if ht : t ≤ 0 then Classical.choose (exists_nat_ge (-t)) else 0
  have hidx : ∀ {t : Real}, t ≤ 0 → t ∈ Set.Icc (-(idx t : Real)) 0 := by
    intro t ht
    have h := Classical.choose_spec (exists_nat_ge (-t))
    have hle : -(idx t : Real) ≤ t := by
      dsimp only [idx]
      rw [dif_pos ht]
      linarith
    exact ⟨hle, ht⟩
  let gInf : letI : TopologicalSpace P.M := P.topology
      letI : ChartedSpace H P.M := P.charted
      letI : IsManifold I ∞ P.M := P.smooth
      Real → SmoothRiemannianMetric I P.M := fun t =>
    if ht : t ≤ 0 then gN (idx t) t else R
  have hgInf : ∀ n : Nat, ∀ t : Real,
      t ∈ Set.Icc (-(n : Real)) 0 → gInf t = gN n t := by
    intro n t ht
    have ht0 : t ≤ 0 := ht.2
    have hdef : gInf t = gN (idx t) t := by
      dsimp only [gInf]
      rw [dif_pos ht0]
    rw [hdef]
    exact BumpMetricConvergence.unique (Φ := Φ) (hgN (idx t)) (hgN n) (hidx ht0) ht
  exact ⟨{
    φ := φ
    strictMono := hφ
    gInf := gInf
    convergenceOn := fun n =>
      BumpMetricConvergence.congr (Φ := Φ) (hgN n) fun t ht => (hgInf n t ht).symm
  }⟩

end CheegerGromovCompactness
end DifferentialGeometry
