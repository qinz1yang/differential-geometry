import DifferentialGeometry.Analysis.Parabolic.Euclidean.HeatKernel.PositiveDefinite.GaussianTail
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Jacobian.SourceGaussian

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Filter Set
open scoped ContDiff ENNReal Manifold Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open MeasureTheory
open DifferentialGeometry.Analysis.Parabolic.Euclidean

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
theorem lSourceGaussian_tail_tendsto_zero
    (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M) :
    Tendsto
      (fun R : Real ↦
        ∫⁻ Z : E in
          {Z | R < Real.sqrt ((S.base.metric T).inner x Z Z)},
          ENNReal.ofReal (lSourceGaussian S T x Z)
            ∂(modelHaar (E := E)))
      atTop (nhds 0) := by
  let q : E → Real := fun Z ↦
    Real.sqrt ((S.base.metric T).inner x Z Z)
  let s : Real → Set E := fun R ↦ {Z | R < q Z}
  let ν : Measure E :=
    (modelHaar (E := E)).withDensity
      (fun Z ↦ ENNReal.ofReal (lSourceGaussian S T x Z))
  have hq : Continuous q := by
    dsimp only [q]
    fun_prop
  have hs : ∀ R, MeasurableSet (s R) := by
    intro R
    exact measurableSet_lt measurable_const hq.measurable
  have hanti : Antitone s := by
    intro R R' hRR' Z hZ
    exact lt_of_le_of_lt hRR' hZ
  have hinter : ⋂ R, s R = ∅ := by
    apply le_antisymm
    · intro Z hZ
      exact False.elim ((lt_irrefl (q Z)) (mem_iInter.mp hZ (q Z)))
    · exact empty_subset _
  have hνuniv : ν Set.univ = 1 := by
    simp only [ν, withDensity_apply _ MeasurableSet.univ]
    simpa only [Measure.restrict_univ] using lSourceGaussian_mass S T x
  have hfin : ∃ R, ν (s R) ≠ (⊤ : ENNReal) := by
    refine ⟨0, ne_of_lt ((measure_mono (subset_univ (s 0))).trans_lt ?_)⟩
    rw [hνuniv]
    exact ENNReal.one_lt_top
  have ht := tendsto_measure_iInter_atTop
    (μ := ν) (s := s) (fun R ↦ (hs R).nullMeasurableSet) hanti hfin
  have ht' : Tendsto (fun R ↦ ν (s R)) atTop (nhds 0) := by
    change Tendsto (ν ∘ s) atTop (nhds 0)
    simpa only [hinter, measure_empty] using ht
  have heq :
      (fun R ↦ ν (s R)) =
        (fun R : Real ↦
          ∫⁻ Z : E in
            {Z | R < Real.sqrt ((S.base.metric T).inner x Z Z)},
            ENNReal.ofReal (lSourceGaussian S T x Z)
              ∂(modelHaar (E := E))) := by
    funext R
    simp only [ν, withDensity_apply _ (hs R)]
    rfl
  rw [heq] at ht'
  exact ht'

omit [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] in
theorem lSourceGaussian_uniform_tail (eps : ENNReal) (heps : 0 < eps) :
    ∃ R : Real, 0 ≤ R ∧
      ∀ (S : SolutionOn (I := I) (M := M) D) (T : Real) (x : M),
        (∫⁻ Z : E in
            {Z | R < Real.sqrt ((S.base.metric T).inner x Z Z)},
            ENNReal.ofReal (lSourceGaussian S T x Z)
              ∂(modelHaar (E := E))) ≤ eps := by
  classical
  let : Nonempty (Fin (Module.finrank Real E)) :=
    ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne (Module.finrank Real E))⟩⟩
  obtain ⟨R, hR, htail⟩ := gaussianPosDef_uniform_tail
    (n := Fin (Module.finrank Real E)) eps heps
  refine ⟨R, hR, ?_⟩
  intro S T x
  let A := lSourceGram S T x
  let e := toEuclidean (E := E)
  let sE : Set E :=
    {Z | R < Real.sqrt ((S.base.metric T).inner x Z Z)}
  let sU : Set (EuclideanSpace Real (Fin (Module.finrank Real E))) :=
    {y | R < Real.sqrt (inner Real y
      (Matrix.toEuclideanCLM (n := Fin (Module.finrank Real E))
        (𝕜 := Real) A y))}
  let G : E → ENNReal :=
    sE.indicator (fun Z ↦ ENNReal.ofReal (lSourceGaussian S T x Z))
  have hsE : MeasurableSet sE := by
    dsimp only [sE]
    apply measurableSet_lt measurable_const
    fun_prop
  have hsU : MeasurableSet sU := by
    dsimp only [sU]
    apply measurableSet_lt measurable_const
    fun_prop
  have hmem : ∀ y,
      e.symm y ∈ sE ↔ y ∈ sU := by
    intro y
    simp only [sE, sU, Set.mem_ofPred_eq]
    have hquad := lSourceGram_quadraticForm S T x (e.symm y)
    simp only [e, ContinuousLinearEquiv.apply_symm_apply] at hquad
    rw [← hquad]
  have hpoint : ∀ y,
      G (e.symm y) =
        sU.indicator
          (fun z ↦ ENNReal.ofReal
            (((Real.pi : Real) ^
                ((Module.finrank Real E : Real) / 2))⁻¹ *
              Real.sqrt A.det *
              Real.exp (-inner Real z
                (Matrix.toEuclideanCLM
                  (n := Fin (Module.finrank Real E))
                  (𝕜 := Real) A z)))) y := by
    intro y
    by_cases hy : y ∈ sU
    · have hEy : e.symm y ∈ sE := (hmem y).2 hy
      simp only [G, Set.indicator_of_mem hEy, Set.indicator_of_mem hy]
      rw [lSourceGaussian_eq_metric_norm]
      have hquad := lSourceGram_quadraticForm S T x (e.symm y)
      simp only [e, ContinuousLinearEquiv.apply_symm_apply] at hquad
      rw [← hquad]
      rfl
    · have hEy : e.symm y ∉ sE := fun h ↦ hy ((hmem y).1 h)
      simp only [G, Set.indicator_of_notMem hEy,
        Set.indicator_of_notMem hy]
  calc
    (∫⁻ Z : E in sE, ENNReal.ofReal (lSourceGaussian S T x Z)
        ∂(modelHaar (E := E))) =
        ∫⁻ Z : E, G Z ∂(modelHaar (E := E)) := by
      rw [← lintegral_indicator hsE]
    _ = ∫⁻ y, G ((toEuclidean (E := E)).symm y)
          ∂(Measure.map (toEuclidean (E := E)) (modelHaar (E := E))) := by
      symm
      calc
        (∫⁻ y, G ((toEuclidean (E := E)).symm y)
            ∂(Measure.map (toEuclidean (E := E)) (modelHaar (E := E)))) =
            ∫⁻ Z, G ((toEuclidean (E := E)).symm
              (toEuclidean (E := E) Z)) ∂(modelHaar (E := E)) :=
          (toEuclidean (E := E)).toHomeomorph.measurableEmbedding.lintegral_map _
        _ = ∫⁻ Z, G Z ∂(modelHaar (E := E)) := by
          refine lintegral_congr fun Z ↦ ?_
          rw [ContinuousLinearEquiv.symm_apply_apply]
    _ = ∫⁻ y, G ((toEuclidean (E := E)).symm y)
          ∂(volume : Measure
            (EuclideanSpace Real (Fin (Module.finrank Real E)))) := by
      rw [map_toEuclidean_modelHaar_eq_volume (E := E)]
    _ = ∫⁻ y in sU,
          ENNReal.ofReal
            (((Real.pi : Real) ^
                ((Module.finrank Real E : Real) / 2))⁻¹ *
              Real.sqrt A.det *
              Real.exp (-inner Real y
                (Matrix.toEuclideanCLM
                  (n := Fin (Module.finrank Real E))
                  (𝕜 := Real) A y))) ∂volume := by
      rw [← lintegral_indicator hsU]
      exact lintegral_congr fun y ↦ by
        simpa only [e] using hpoint y
    _ ≤ eps := by
      simpa only [sU, Fintype.card_fin] using
        htail A (lSourceGram_posDef S T x)

end DifferentialGeometry.PDE.RicciFlow.Perelman
