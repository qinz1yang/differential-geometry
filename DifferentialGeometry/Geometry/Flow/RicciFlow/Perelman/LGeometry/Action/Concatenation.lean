import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Defs

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature
open Bundle Filter MeasureTheory Set
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {D : RealTimeInterval}

theorem lLength_piecewise_Iic
    (S : SolutionOn (I := I) (M := M) D) (T a c b : Real)
    (gamma0 gamma1 : Real -> M) (hac : a ≤ c) (hcb : c ≤ b)
    (h0 : IntervalIntegrable (lDensity S T gamma0) volume a c)
    (h1 : IntervalIntegrable (lDensity S T gamma1) volume c b) :
    lLength S T (Set.piecewise (Set.Iic c) gamma0 gamma1) a b =
      lLength S T gamma0 a c + lLength S T gamma1 c b := by
  classical
  let gamma : Real -> M := Set.piecewise (Set.Iic c) gamma0 gamma1
  have hleft_ae :
      lDensity S T gamma0 =ᵐ[volume.restrict (Set.uIoc a c)]
        lDensity S T gamma := by
    filter_upwards
      [MeasureTheory.ae_restrict_mem measurableSet_uIoc,
        MeasureTheory.Measure.ae_ne (volume.restrict (Set.uIoc a c)) c]
        with s hs hsc
    have hs' : s ∈ Set.Ioc a c := by
      simpa only [Set.uIoc_of_le hac] using hs
    have hlt : s < c := lt_of_le_of_ne hs'.2 hsc
    apply lDensity_congr S T s
    filter_upwards [Iio_mem_nhds hlt] with r hr
    exact ((Set.Iic c).piecewise_eq_of_mem gamma0 gamma1
      (Set.mem_Iic.mpr hr.le)).symm
  have hright_ae :
      lDensity S T gamma1 =ᵐ[volume.restrict (Set.uIoc c b)]
        lDensity S T gamma := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc]
      with s hs
    have hs' : s ∈ Set.Ioc c b := by
      simpa only [Set.uIoc_of_le hcb] using hs
    apply lDensity_congr S T s
    filter_upwards [Ioi_mem_nhds hs'.1] with r hr
    exact ((Set.Iic c).piecewise_eq_of_notMem gamma0 gamma1
      (by simpa only [Set.mem_Iic] using not_le_of_gt hr)).symm
  have hleft : IntervalIntegrable (lDensity S T gamma) volume a c :=
    h0.congr_ae hleft_ae
  have hright : IntervalIntegrable (lDensity S T gamma) volume c b :=
    h1.congr_ae hright_ae
  have hleft_eq : lLength S T gamma a c = lLength S T gamma0 a c := by
    unfold lLength
    exact intervalIntegral.integral_congr_ae_restrict hleft_ae.symm
  have hright_eq : lLength S T gamma c b = lLength S T gamma1 c b := by
    unfold lLength
    exact intervalIntegral.integral_congr_ae_restrict hright_ae.symm
  change lLength S T gamma a b =
    lLength S T gamma0 a c + lLength S T gamma1 c b
  calc
    lLength S T gamma a b =
        lLength S T gamma a c + lLength S T gamma c b :=
      (lLength_add_adj S T gamma a c b hleft hright).symm
    _ = lLength S T gamma0 a c + lLength S T gamma1 c b := by
      rw [hleft_eq, hright_eq]

end DifferentialGeometry.PDE.RicciFlow.Perelman
