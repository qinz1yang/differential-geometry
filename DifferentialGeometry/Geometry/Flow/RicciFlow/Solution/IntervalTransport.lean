import DifferentialGeometry.Geometry.Flow.RicciFlow.Scaling.Parabolic

open DifferentialGeometry.Geometry.Curvature

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

namespace RealTimeInterval

theorem ext {D D' : RealTimeInterval}
    (hcarrier : D.carrier = D'.carrier)
    (hregular : D.regular = D'.regular)
    (hinitial : D.initial = D'.initial) :
    D = D' := by
  cases D with
  | mk c r i hi hs ho hn =>
      cases D' with
      | mk c' r' i' hi' hs' ho' hn' =>
          subst hcarrier
          subst hregular
          subst hinitial
          rfl

end RealTimeInterval

end DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M]
variable [SigmaCompactSpace M] [T2Space M]



section Interval

private theorem parabolicTime_mem_Ico_iff {a b τ R s : Real} (hR : 0 < R) :
    parabolicTime τ R s ∈ Set.Ico a b ↔
      s ∈ Set.Ico (R * (a - τ)) (R * (b - τ)) := by
  have hRne : R ≠ 0 := ne_of_gt hR
  have hs : R * (s / R) = s := by
    field_simp
  simp only [Set.mem_Ico, parabolicTime]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · have h := mul_le_mul_of_nonneg_left (by linarith : a - τ ≤ s / R) hR.le
      rwa [hs] at h
    · have h := mul_lt_mul_of_pos_left (by linarith : s / R < b - τ) hR
      rwa [hs] at h
  · rintro ⟨h1, h2⟩
    constructor
    · have h : a - τ ≤ s / R := by
        refine le_of_mul_le_mul_left ?_ hR
        rw [hs]
        exact h1
      linarith
    · have h : s / R < b - τ := by
        refine lt_of_mul_lt_mul_left ?_ hR.le
        rw [hs]
        exact h2
      linarith

private theorem parabolicTime_mem_Ioo_iff {a b τ R s : Real} (hR : 0 < R) :
    parabolicTime τ R s ∈ Set.Ioo a b ↔
      s ∈ Set.Ioo (R * (a - τ)) (R * (b - τ)) := by
  have hRne : R ≠ 0 := ne_of_gt hR
  have hs : R * (s / R) = s := by
    field_simp
  simp only [Set.mem_Ioo, parabolicTime]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · have h := mul_lt_mul_of_pos_left (by linarith : a - τ < s / R) hR
      rwa [hs] at h
    · have h := mul_lt_mul_of_pos_left (by linarith : s / R < b - τ) hR
      rwa [hs] at h
  · rintro ⟨h1, h2⟩
    constructor
    · have h : a - τ < s / R := by
        refine lt_of_mul_lt_mul_left ?_ hR.le
        rw [hs]
        exact h1
      linarith
    · have h : s / R < b - τ := by
        refine lt_of_mul_lt_mul_left ?_ hR.le
        rw [hs]
        exact h2
      linarith

theorem parabolicInterval_closedOpen_carrier_eq
    {a b : Real} (hab : a < b) {τ R : Real} (hR : 0 < R)
    (hτ : τ ∈ (RealTimeInterval.closedOpen a b hab).carrier) :
    (parabolicInterval (RealTimeInterval.closedOpen a b hab) τ R hτ).carrier =
      Set.Ico (R * (a - τ)) (R * (b - τ)) := by
  ext s
  exact parabolicTime_mem_Ico_iff hR

theorem parabolicInterval_closedOpen_regular_eq
    {a b : Real} (hab : a < b) {τ R : Real} (hR : 0 < R)
    (hτ : τ ∈ (RealTimeInterval.closedOpen a b hab).carrier) :
    (parabolicInterval (RealTimeInterval.closedOpen a b hab) τ R hτ).regular =
      Set.Ioo (R * (a - τ)) (R * (b - τ)) := by
  ext s
  exact parabolicTime_mem_Ioo_iff hR

theorem parabolicInterval_eq_closedOpen
    {a b : Real} (hab : a < b) {R : Real} (hR : 0 < R)
    (ha : a ∈ (RealTimeInterval.closedOpen a b hab).carrier)
    (hlt : (0 : Real) < R * (b - a)) :
    parabolicInterval (RealTimeInterval.closedOpen a b hab) a R ha =
      RealTimeInterval.closedOpen 0 (R * (b - a)) hlt := by
  refine RealTimeInterval.ext ?_ ?_ rfl
  · rw [parabolicInterval_closedOpen_carrier_eq hab hR ha, sub_self, mul_zero]
    rfl
  · rw [parabolicInterval_closedOpen_regular_eq hab hR ha, sub_self, mul_zero]
    rfl

end Interval



namespace SolutionOn

def cast {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D)
    (D' : DifferentialGeometry.Geometry.Curvature.RealTimeInterval) :
    SolutionOn (I := I) (M := M) D' where
  base := S.base

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [SigmaCompactSpace M]
    [T2Space M] in
@[simp] theorem cast_base
    {D D' : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    (S.cast D').base = S.base := rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I 1 M] [SigmaCompactSpace M]
    [T2Space M] in
@[simp] theorem cast_metric
    {D D' : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    (S.cast D').base.metric t = S.base.metric t := rfl

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem cast_family_metric
    {D D' : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    (S.cast D').family.metric t = S.family.metric t := rfl

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem cast_family_connection
    {D D' : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    (S.cast D').family.connection t = S.family.connection t := rfl

omit [SigmaCompactSpace M] in
@[simp] theorem cast_rm04
    {D D' : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M) :
    (S.cast D').base.rm04 t x = S.base.rm04 t x := rfl

omit [SigmaCompactSpace M] in
@[simp] theorem cast_ricci
    {D D' : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) :
    (S.cast D').ricci t = S.ricci t := rfl

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem cast_ricciAt
    {D D' : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M) :
    (S.cast D').ricciAt t x = S.ricciAt t x := rfl

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem cast_scalar
    {D D' : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M) :
    (S.cast D').scalar t x = S.scalar t x := rfl

omit [SigmaCompactSpace M] [T2Space M] in
@[simp] theorem cast_flowG
    {D D' : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) :
    flowG (I := I) (S.cast D') = flowG (I := I) S := rfl

omit [SigmaCompactSpace M] in
@[simp] theorem cast_ricciNorm
    {D D' : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (S : SolutionOn (I := I) (M := M) D) (t : Real) (x : M) :
    ricciNorm (I := I) (S.cast D') t x = ricciNorm (I := I) S t x := rfl

end SolutionOn

omit [SigmaCompactSpace M] in
theorem isSolutionOn_cast
    {D D' : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {S : SolutionOn (I := I) (M := M) D}
    (hS : IsSolutionOn (I := I) S)
    (hcarrier : D.carrier = D'.carrier)
    (hregular : D.regular = D'.regular) :
    IsSolutionOn (I := I) (S.cast D') where
  smoothMetric := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro x X Y
      rw [← hregular]
      exact hS.smoothMetric.coeff x X Y
    · intro x X Y
      rw [← hcarrier]
      exact hS.smoothMetric.coeff_cont x X Y
    · rw [← hcarrier]
      exact hS.smoothMetric.metricTensor_cont
    · intro Idx _ frame u hframe i j
      rw [← hregular]
      exact hS.smoothMetric.frameCompSmooth frame hframe i j
  smoothConnection := by
    intro t
    exact hS.smoothConnection ⟨(t : Real), by rw [hcarrier]; exact t.2⟩
  equation := by
    intro t x X Y
    rw [← hcarrier]
    exact hS.equation ⟨(t : Real), by rw [hregular]; exact t.2⟩ x X Y
  scalarCont := by
    rw [← hcarrier]
    exact hS.scalarCont
  scalarTime := by
    intro K t ht hK x
    exact hS.scalarTime ht (by rw [hcarrier]; exact hK) x
  ricciCont := by
    rw [← hcarrier]
    exact hS.ricciCont
  rm04Cont := by
    rw [← hcarrier]
    exact hS.rm04Cont
  ricciNormSpace := by
    intro t ht x
    exact hS.ricciNormSpace t (by rw [hcarrier]; exact ht) x
  ricciNormGrad := by
    intro t ht x
    exact hS.ricciNormGrad t (by rw [hcarrier]; exact ht) x

omit [SigmaCompactSpace M] in
theorem isSolutionOn_paraSolution_cast_closedOpen
    {a b : Real} (hab : a < b)
    (S : SolutionOn (I := I) (M := M) (RealTimeInterval.closedOpen a b hab))
    (hS : IsSolutionOn (I := I) S)
    {τ R : Real} (hR : 0 < R)
    (hτ : τ ∈ (RealTimeInterval.closedOpen a b hab).carrier)
    (hlt : R * (a - τ) < R * (b - τ)) :
    IsSolutionOn (I := I)
      ((parabolicSolution (I := I) S τ R hR hτ).cast
        (RealTimeInterval.closedOpen (R * (a - τ)) (R * (b - τ)) hlt)) :=
  isSolutionOn_cast (I := I) (parabolicSolution_isSolutionOn (I := I) S hS τ R hR hτ)
    (parabolicInterval_closedOpen_carrier_eq hab hR hτ)
    (parabolicInterval_closedOpen_regular_eq hab hR hτ)

end DifferentialGeometry.PDE.RicciFlow

end
