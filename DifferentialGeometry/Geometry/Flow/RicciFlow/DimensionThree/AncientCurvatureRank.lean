import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.ClosedRankTrichotomy
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Curvature.Flatness
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.Positivity
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorEigenvalues
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorVanishing
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureRank
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.HamiltonIvey.Complete

set_option autoImplicit false
noncomputable section
open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_curvatureOperatorImageAt_finrank_eq_on_past_interval
    [ConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    {T : ℝ} (hreg : Iio T ⊆ D.regular)
    (hR : ∀ t < T, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    ∃ t₀ < T, ∃ q : ℕ, (q = 0 ∨ q = 1 ∨ q = 3) ∧
      ∀ t ≤ t₀, ∀ x,
        Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
          ⟨metricRm04At (S.family.metric t) x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) = q := by
  classical
  let rank (t : ℝ) (x : M) : ℕ :=
    Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
      ⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩)
  let values : Set ℕ := {q | ∃ t < T, ∃ x, rank t x = q}
  let x₀ : M := Classical.choice inferInstance
  have hvalues : values.Nonempty := ⟨rank (T-1) x₀, T-1, by linarith, x₀, rfl⟩
  obtain ⟨s, hs, x, hx⟩ : sInf values ∈ values := Nat.sInf_mem hvalues
  let t₀ := s - 1
  have ht₀ : t₀ < T := by dsimp [t₀]; linarith
  have hconstant : ∀ t ≤ t₀, ∀ y, rank t y = sInf values := by
    intro t ht y
    have hts : t < s := by dsimp [t₀] at ht; linarith
    have htT : t < T := hts.trans hs
    apply le_antisymm
    · rw [← hx]
      exact curvatureOperatorImageAt_finrank_le_at_later_time S hS hdim hts
        (fun r hr => hreg (hr.2.trans_lt hs))
        (fun r hr => hR r (hr.2.trans_lt hs)) y x
    · exact Nat.sInf_le ⟨t, htT, y, rfl⟩
  refine ⟨t₀, ht₀, sInf values, ?_, hconstant⟩
  have htri := curvatureOperatorImageAt_finrank_trichotomy_at_later_time S hS hdim
    (s := t₀-1) (t := t₀) (by linarith)
    (fun r hr => hreg (hr.2.trans_lt ht₀))
    (fun r hr => hR r (hr.2.trans_lt ht₀)) x₀
  change rank t₀ x₀ = 0 ∨ rank t₀ x₀ = 1 ∨ rank t₀ x₀ = 3 at htri
  rwa [hconstant t₀ le_rfl x₀] at htri

theorem exists_curvatureOperatorImageAt_finrank_eq_on_past_interval_of_complete_ancient
    [ConnectedSpace M] [SigmaCompactSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    {T : ℝ} (hreg : Iio T ⊆ D.regular)
    (hcomplete : ∀ t < T, RiemannianMetricComplete (I := I) (S.family.metric t)) :
    ∃ t₀ < T, ∃ q : ℕ, (q = 0 ∨ q = 1 ∨ q = 3) ∧
      ∀ t ≤ t₀, ∀ x,
        Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
          ⟨metricRm04At (S.family.metric t) x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) = q := by
  apply exists_curvatureOperatorImageAt_finrank_eq_on_past_interval S hS hdim hreg
  intro t ht x
  exact curvatureOperator_nonnegative_of_complete_ancient S hS
    (fun r hr => D.regular_subset (hreg (hr.trans_lt ht)))
    (fun r hr => hreg (hr.trans ht))
    (fun r hr => hcomplete r (hr.trans_lt ht)) hdim x

section Nonflat

variable [SigmaCompactSpace M] [ConnectedSpace M]

open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Tensor0SBundle

omit [I.Boundaryless] [SigmaCompactSpace M] [ConnectedSpace M] in
private theorem rm04_eq_zero_of_image_finrank_eq_zero
    (g : SmoothRiemannianMetric I M) (x : M) (hdim : Module.finrank ℝ E = 3)
    (hzero : Module.finrank ℝ (curvatureOperatorImageAt g x
      (metricAlgebraicCurvatureTensorAt g x)) = 0) : metricRm04At g x = 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  apply metricRm04At_eq_zero_of_curvatureOperatorEndomorphismAt_eq_zero g x hdim
  let _ : FiniteDimensional ℝ (TangentSpace I x [⋀^Fin 2]→L[ℝ] ℝ) :=
    (ContinuousAlternatingMap.elementaryCovectorBasis (k := 2)
      (Module.finBasis ℝ (TangentSpace I x))).finiteDimensional_of_finite
  have hrange := Submodule.finrank_eq_zero.mp hzero
  rw [curvatureOperatorImageAt_eq_range] at hrange
  refine ContinuousLinearMap.ext fun v => ?_
  have hmem : curvatureOperatorEndomorphismAt g x (metricAlgebraicCurvatureTensorAt g x) v ∈
      (curvatureOperatorEndomorphismAt g x (metricAlgebraicCurvatureTensorAt g x)).range := ⟨v, rfl⟩
  rw [hrange] at hmem
  exact hmem

theorem curvatureOperatorImageAt_finrank_pos_of_complete_ancient_nonflat
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3) {T : ℝ}
    (hcarrier : Iic T ⊆ D.carrier) (hregular : Iio T ⊆ D.regular)
    (hcomplete : ∀ t ≤ T, RiemannianMetricComplete (S.base.metric t))
    (hbound : ∀ a b : ℝ, a < b → b ≤ T →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, ∀ x : M,
        normSq0S (S.base.metric t) x 4 (metricRm04At (S.base.metric t) x) ≤ C)
    (hnonflat : ∃ t ≤ T, ∃ x : M, metricRm04At (S.base.metric t) x ≠ 0)
    {t : ℝ} (ht : t ≤ T) (x : M) :
    0 < Module.finrank ℝ (curvatureOperatorImageAt (S.base.metric t) x
      (metricAlgebraicCurvatureTensorAt (S.base.metric t) x)) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hR (r : ℝ) (hr : r ≤ T) (z : M) :
      metricAlgebraicCurvatureTensorAt (S.base.metric r) z ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) :=
    curvatureOperator_nonnegative_of_complete_ancient S hS
      (fun q hq => hcarrier (hq.trans hr))
      (fun q hq => hregular (hq.trans_le hr))
      (fun q hq => hcomplete q (hq.trans hr)) hdim z
  apply Nat.pos_of_ne_zero
  intro hzero
  have hrank (y : M) : Module.finrank ℝ (curvatureOperatorImageAt (S.base.metric t) y
      (metricAlgebraicCurvatureTensorAt (S.base.metric t) y)) = 0 := by
    have heq := curvatureOperatorImageAt_finrank_eq_at_right_endpoint S hS hdim
      (a := t - 1) (b := t) (by linarith)
      (fun r hr => hcarrier (hr.2.trans ht))
      (fun r hr => hregular (hr.2.trans_le ht))
      (fun r hr => hR r (hr.2.trans ht)) y x
    exact heq.trans hzero
  obtain ⟨s, hs, y, hy⟩ := hnonflat
  rcases lt_trichotomy s t with hst | rfl | hts
  · have hle := curvatureOperatorImageAt_finrank_le_at_later_time_on_closed_interval S hS hdim
      (a := s - 1) (by linarith) hst
      (fun r hr => hcarrier (hr.2.trans ht))
      (fun r hr => hregular (hr.2.trans_le ht))
      (fun r hr => hR r (hr.2.trans ht)) y x
    exact hy (rm04_eq_zero_of_image_finrank_eq_zero _ y hdim
      (Nat.eq_zero_of_le_zero (hle.trans_eq hzero)))
  · exact hy (rm04_eq_zero_of_image_finrank_eq_zero _ y hdim (hrank y))
  · have hflat (z : M) : normSq0S (S.base.metric t) z 4 (S.base.rm04 t z) = 0 := by
      have hz := rm04_eq_zero_of_image_finrank_eq_zero _ z hdim (hrank z)
      apply (normSq0S_eq_zero_iff _ z 4 _).mpr
      exact hz
    have hz := curvature_normSq_eq_zero_on_Icc_of_eq_zero_at_left S hS hts
      (fun r hr => hcarrier (hr.2.trans hs))
      (fun r hr => hregular (hr.2.trans_le hs))
      (hcomplete t ht) (hbound t s hts hs) hflat s ⟨hts.le, le_rfl⟩ y
    exact hy ((normSq0S_eq_zero_iff _ y 4 _).mp hz)


theorem curvatureOperatorImageAt_finrank_eq_one_of_complete_ancient_nonflat_null_plane
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3) {T : ℝ}
    (hcarrier : Iic T ⊆ D.carrier) (hregular : Iio T ⊆ D.regular)
    (hcomplete : ∀ t ≤ T, RiemannianMetricComplete (S.base.metric t))
    (hbound : ∀ a b : ℝ, a < b → b ≤ T →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc a b, ∀ x : M,
        normSq0S (S.base.metric t) x 4 (metricRm04At (S.base.metric t) x) ≤ C)
    (hnonflat : ∃ t ≤ T, ∃ x : M, metricRm04At (S.base.metric t) x ≠ 0)
    {s : ℝ} (hs : s ≤ T) (x₀ : M) (v w : TangentSpace I x₀)
    (hplane : 0 < (S.base.metric s).inner x₀ v v * (S.base.metric s).inner x₀ w w -
      ((S.base.metric s).inner x₀ v w) ^ 2)
    (hnull : metricRm04StandardAt (S.base.metric s) x₀ v w w v = 0)
    {t : ℝ} (ht : t ≤ s) (x : M) :
    Module.finrank ℝ (curvatureOperatorImageAt (S.base.metric t) x
      (metricAlgebraicCurvatureTensorAt (S.base.metric t) x)) = 1 := by
  have hR (r : ℝ) (hr : r ≤ T) (z : M) :
      metricAlgebraicCurvatureTensorAt (S.base.metric r) z ∈
        algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) :=
    curvatureOperator_nonnegative_of_complete_ancient S hS
      (fun q hq => hcarrier (hq.trans hr))
      (fun q hq => hregular (hq.trans_le hr))
      (fun q hq => hcomplete q (hq.trans hr)) hdim z
  have hpos (r : ℝ) (hr : r ≤ T) (z : M) :=
    curvatureOperatorImageAt_finrank_pos_of_complete_ancient_nonflat
      S hS hdim hcarrier hregular hcomplete hbound hnonflat hr z
  have htri := curvatureOperatorImageAt_finrank_trichotomy_at_right_endpoint
    S hS hdim (a := s - 1) (b := s) (by linarith)
    (fun r hr => hcarrier (hr.2.trans hs))
    (fun r hr => hregular (hr.2.trans_le hs))
    (fun r hr => hR r (hr.2.trans hs))
  have hone : ∀ z, Module.finrank ℝ (curvatureOperatorImageAt (S.base.metric s) z
      (metricAlgebraicCurvatureTensorAt (S.base.metric s) z)) = 1 := by
    rcases htri with hz | ho | hthree
    · have h := hpos s hs x₀
      have heq := hz x₀
      exact False.elim ((Nat.ne_of_gt h) heq)
    · exact ho
    · have hp := leastCurvatureOperatorEigenvalueAt_pos_of_image_finrank_eq_three
        (S.base.metric s) x₀ hdim (metricAlgebraicCurvatureTensorAt (S.base.metric s) x₀)
        (hR s hs x₀) (hthree x₀)
      have hoperator := Perelman.KappaSolutions.curvatureOperatorPositiveAt_of_leastCurvatureOperatorEigenvalueAt_pos
        (S.base.metric s) x₀ hdim hp
      have hsec := (Perelman.KappaSolutions.curvatureOperatorPositiveAt_iff_sectional (S.base.metric s) x₀ hdim).mp
        hoperator v w hplane
      rw [hnull] at hsec
      exact False.elim (lt_irrefl 0 hsec)
  rcases lt_or_eq_of_le ht with hlt | rfl
  · have hle := curvatureOperatorImageAt_finrank_le_at_later_time_on_closed_interval S hS hdim
      (a := t - 1) (by linarith) hlt
      (fun r hr => hcarrier (hr.2.trans hs))
      (fun r hr => hregular (hr.2.trans_le hs))
      (fun r hr => hR r (hr.2.trans hs)) x x₀
    have hu := hle.trans_eq (hone x₀)
    exact Nat.le_antisymm hu (hpos t (ht.trans hs) x)
  · exact hone x

end Nonflat

end DifferentialGeometry.PDE.RicciFlow
