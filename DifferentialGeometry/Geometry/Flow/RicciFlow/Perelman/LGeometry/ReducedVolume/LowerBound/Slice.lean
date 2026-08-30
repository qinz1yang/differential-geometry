import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.LowerBound.SliceLengthBound
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.SetLowerBound

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle MeasureTheory Set
open scoped ContDiff ENNReal Manifold Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [NeZero (Module.finrank ℝ E)] in
theorem redVolume_slice_low
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    {a₀ a₁ a omega l₀ : Real} (ha₀a₁ : a₀ < a₁) (ha₁a : a₁ < a)
    (haomega : a < omega) (hregFwd : Icc a₀ a₁ ⊆ D.regular)
    (x₀ : M) :
    ∃ v₀ : ENNReal, 0 < v₀ ∧
      ∀ {T : Real}, a ≤ T → T < omega →
        ∀ {x : M} {W : TangentSpace I x},
          Icc a₀ T ⊆ D.regular →
          Real.sqrt (T - a₀) ∈ lRegDomain S T x W →
          (W, T - a₁) ∈ lMinDomain S T x →
          redLength S T x
              (lRegCurve S T x W (Real.sqrt (T - a₁))) (T - a₁) ≤ l₀ →
          v₀ ≤ redVolume S T x (T - a₀) := by
  classical
  obtain ⟨K, v, _hK, hv, hslice⟩ :=
    redLen_slice_bound (I := I) S hS (l₀ := l₀) ha₀a₁ ha₁a haomega
      hregFwd x₀
  let d : Real := (Module.finrank Real E : Real) / 2
  let c : Real := Real.exp
    (-K - d * Real.log (omega - a₀) - d * Real.log (4 * Real.pi))
  let v₀ : ENNReal := v * ENNReal.ofReal c
  have hc : 0 < c := by
    dsimp only [c]
    exact Real.exp_pos _
  refine ⟨v₀, ENNReal.mul_pos hv.ne' (ENNReal.ofReal_pos.mpr hc).ne', ?_⟩
  intro T haT hTomega x W hslab hbdom hmin hred
  obtain ⟨A, hAmeas, hAvol, hAlen⟩ :=
    hslice haT hTomega hslab hbdom hmin hred
  have htau : 0 < T - a₀ := by linarith
  have htau_le : T - a₀ ≤ omega - a₀ := by linarith
  have hlog : Real.log (T - a₀) ≤ Real.log (omega - a₀) :=
    Real.log_le_log htau htau_le
  have hd : 0 ≤ d := by
    dsimp only [d]
    positivity
  have hlog_mul : d * Real.log (T - a₀) ≤
      d * Real.log (omega - a₀) :=
    mul_le_mul_of_nonneg_left hlog hd
  have hexp : c ≤ Real.exp
      (-K - d * Real.log (T - a₀) - d * Real.log (4 * Real.pi)) := by
    dsimp only [c]
    apply Real.exp_le_exp.mpr
    linarith
  have hfactor : ENNReal.ofReal c ≤ ENNReal.ofReal
      (Real.exp
        (-K -
          ((Module.finrank Real E : Real) / 2) * Real.log (T - a₀) -
          ((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi))) := by
    dsimp only [d] at hexp
    exact ENNReal.ofReal_le_ofReal hexp
  have hAvol' :
      v ≤ riemannianVolumeMeasure (I := I) (M := M)
        (S.base.metric (T - (T - a₀))) A := by
    have htime : T - (T - a₀) = a₀ := by linarith
    rw [htime]
    exact hAvol
  have hset := redVolume_set_low (I := I) S T x (T - a₀) K hAmeas hAlen
  calc
    v₀ = v * ENNReal.ofReal c := rfl
    _ ≤ riemannianVolumeMeasure (I := I) (M := M)
          (S.base.metric (T - (T - a₀))) A *
        ENNReal.ofReal
          (Real.exp
            (-K -
              ((Module.finrank Real E : Real) / 2) * Real.log (T - a₀) -
              ((Module.finrank Real E : Real) / 2) * Real.log (4 * Real.pi))) :=
      mul_le_mul' hAvol' hfactor
    _ ≤ redVolume S T x (T - a₀) := hset

end DifferentialGeometry.PDE.RicciFlow.Perelman

end
