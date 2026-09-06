import DifferentialGeometry.Analysis.Integration.Measure.ParamEvaluation
import DifferentialGeometry.Geometry.Metric.Pullback

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
  [IsManifold I ∞ N]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace N := borel N
private local instance : BorelSpace N := ⟨rfl⟩

private noncomputable def chartParam [I.Boundaryless] (x : M) :
    PartialDiffeomorph 𝓘(Real, E) I E M 1 where
  toFun := (extChartAt I x).symm
  invFun := extChartAt I x
  source := (extChartAt I x).target
  target := (extChartAt I x).source
  map_source' := fun {y} hy => (extChartAt I x).map_target hy
  map_target' := fun {y} hy => (extChartAt I x).map_source hy
  left_inv' := fun {y} hy => (extChartAt I x).right_inv hy
  right_inv' := fun {y} hy => (extChartAt I x).left_inv hy
  open_source := isOpen_extChartAt_target (I := I) x
  open_target := isOpen_extChartAt_source (I := I) x
  contMDiffOn_toFun := contMDiffOn_extChartAt_symm (I := I) (n := 1) x
  contMDiffOn_invFun := by
    simpa only [extChartAt_source] using
      contMDiffOn_extChartAt (I := I) (n := 1) (x := x)

private noncomputable def diffeomorphPartialOne
    (Phi : M ≃ₘ⟮I, I⟯ N) : PartialDiffeomorph I I M N 1 where
  toPartialEquiv := Phi.toHomeomorph.toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun x _ := (Phi.contMDiff_toFun x).of_le (by norm_num)
  contMDiffOn_invFun x _ := (Phi.symm.contMDiff_toFun x).of_le (by norm_num)

private theorem paramGramMatrix_pullback_trans
    [T2Space M]
    (g : SmoothRiemannianMetric I N) (Phi : M ≃ₘ⟮I, I⟯ N)
    (Psi : PartialDiffeomorph 𝓘(Real, E) I E M 1)
    {w : E} (hw : w ∈ Psi.source) :
    paramGramMatrix (I := I) (Diffeomorph.pullbackMetric g Phi) Psi w =
      paramGramMatrix (I := I) g
        (Psi.trans (diffeomorphPartialOne Phi)) w := by
  have hPsi : MDifferentiableAt 𝓘(Real, E) I (Psi : E → M) w :=
    (Psi.contMDiffOn_toFun.mdifferentiableOn one_ne_zero w hw).mdifferentiableAt
      (Psi.open_source.mem_nhds hw)
  have hPhi : MDifferentiableAt I I (Phi : M → N) (Psi w) :=
    (Phi.contMDiff_toFun (Psi w)).mdifferentiableAt (by norm_num)
  have hchain :
      mfderiv 𝓘(Real, E) I
          ((Psi.trans (diffeomorphPartialOne Phi)) : E → N) w =
        (mfderiv I I (Phi : M → N) (Psi w)).comp
          (mfderiv 𝓘(Real, E) I (Psi : E → M) w) := by
    change mfderiv 𝓘(Real, E) I (fun y => Phi (Psi y)) w = _
    exact mfderiv_comp w hPhi hPsi
  ext i j
  rw [paramGramMatrix_apply, paramGramMatrix_apply,
    Diffeomorph.pullbackMetric_inner, hchain]
  rfl

private theorem paramDensity_pullback_trans
    [T2Space M]
    (g : SmoothRiemannianMetric I N) (Phi : M ≃ₘ⟮I, I⟯ N)
    (Psi : PartialDiffeomorph 𝓘(Real, E) I E M 1)
    {w : E} (hw : w ∈ Psi.source) :
    paramDensity (I := I) (Diffeomorph.pullbackMetric g Phi) Psi w =
      paramDensity (I := I) g (Psi.trans (diffeomorphPartialOne Phi)) w := by
  unfold paramDensity
  rw [paramGramMatrix_pullback_trans (I := I) g Phi Psi hw]

private theorem riemannianVolumeMeasure_pullback_apply_of_subset_chart
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [T2Space N] [SigmaCompactSpace N]
    (g : SmoothRiemannianMetric I N) (Phi : M ≃ₘ⟮I, I⟯ N)
    (alpha : M) {A : Set M} (hA_meas : MeasurableSet A)
    (hA_chart : A ⊆ (chartAt H alpha).source) :
    riemannianVolumeMeasure (I := I) (M := M)
        (Diffeomorph.pullbackMetric g Phi) A =
      Measure.map (Phi.symm : N → M)
        (riemannianVolumeMeasure (I := I) (M := N) g) A := by
  let Psi : PartialDiffeomorph 𝓘(Real, E) I E M 1 := chartParam (I := I) alpha
  let Theta : PartialDiffeomorph 𝓘(Real, E) I E N 1 :=
    Psi.trans (diffeomorphPartialOne Phi)
  let B : Set E := Psi.symm '' A
  have hA_target : A ⊆ Psi.target := by
    simpa only [Psi, chartParam, extChartAt_source] using hA_chart
  have hB_meas : MeasurableSet B := by
    exact measurableSet_symm_image_param (I := I) Psi hA_meas hA_target
  have hB_source : B ⊆ Psi.source := by
    rintro w ⟨x, hxA, rfl⟩
    exact Psi.toPartialEquiv.map_target (hA_target hxA)
  have hB_theta : B ⊆ Theta.source := by
    intro w hw
    change w ∈ Psi.source ∩ Psi ⁻¹' (Set.univ : Set M)
    exact ⟨hB_source hw, Set.mem_univ _⟩
  have hPsi_image : Psi '' B = A := by
    exact PartialEquiv.image_symm_image_of_subset_target Psi.toPartialEquiv hA_target
  have hTheta_image : Theta '' B = Phi '' A := by
    rw [show Theta '' B = Phi '' (Psi '' B) by
      ext y
      constructor
      · rintro ⟨w, hw, rfl⟩
        exact ⟨Psi w, ⟨w, hw, rfl⟩, rfl⟩
      · rintro ⟨x, ⟨w, hw, rfl⟩, rfl⟩
        exact ⟨w, hw, rfl⟩]
    rw [hPsi_image]
  have hpull := riemannianVolumeMeasure_image_param_eq
    (I := I) (Diffeomorph.pullbackMetric g Phi) Psi hB_meas hB_source
  have htarget := riemannianVolumeMeasure_image_param_eq
    (I := I) g Theta hB_meas hB_theta
  rw [hPsi_image] at hpull
  rw [hTheta_image] at htarget
  calc
    riemannianVolumeMeasure (I := I) (M := M)
          (Diffeomorph.pullbackMetric g Phi) A =
        ∫⁻ w in B,
          ENNReal.ofReal
            (paramDensity (I := I) (Diffeomorph.pullbackMetric g Phi) Psi w)
          ∂(modelHaar (E := E)) := hpull
    _ = ∫⁻ w in B,
          ENNReal.ofReal (paramDensity (I := I) g Theta w)
          ∂(modelHaar (E := E)) := by
      refine MeasureTheory.setLIntegral_congr_fun hB_meas (fun w hw => ?_)
      rw [paramDensity_pullback_trans (I := I) g Phi Psi (hB_source hw)]
    _ = riemannianVolumeMeasure (I := I) (M := N) g (Phi '' A) := htarget.symm
    _ = Measure.map (Phi.symm : N → M)
        (riemannianVolumeMeasure (I := I) (M := N) g) A := by
      rw [Measure.map_apply Phi.symm.continuous.measurable hA_meas]
      congr 1
      ext y
      constructor
      · rintro ⟨x, hxA, rfl⟩
        change Phi.symm (Phi x) ∈ A
        rw [Phi.symm_apply_apply]
        exact hxA
      · intro hy
        exact ⟨Phi.symm y, hy, Phi.apply_symm_apply y⟩

theorem riemannianVolumeMeasure_pullback
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [T2Space N] [SigmaCompactSpace N]
    (g : SmoothRiemannianMetric I N) (Phi : M ≃ₘ⟮I, I⟯ N) :
    riemannianVolumeMeasure (I := I) (M := M)
        (Diffeomorph.pullbackMetric g Phi) =
      Measure.map (Phi.symm : N → M)
        (riemannianVolumeMeasure (I := I) (M := N) g) := by
  classical
  obtain ⟨S, hS_count, hS_cover⟩ :
      ∃ S : Set M, S.Countable ∧
        ⋃ (x : M) (_ : x ∈ S), (chartAt H x).source = Set.univ :=
    countable_cover_nhds_of_sigmaCompact
      (fun x : M => chart_source_mem_nhds H x)
  apply Measure.ext_of_biUnion_eq_univ hS_count hS_cover
  intro alpha _
  ext A hA
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
  exact riemannianVolumeMeasure_pullback_apply_of_subset_chart
    (I := I) g Phi alpha
      (hA.inter (chartAt H alpha).open_source.measurableSet) Set.inter_subset_right

omit [FiniteDimensional Real E] [IsManifold I ∞ M] [IsManifold I ∞ N] in
private theorem map_symm_withDensity
    (mu : Measure N) (Phi : M ≃ₘ⟮I, I⟯ N)
    (rho : M → ENNReal) (hrho : Measurable rho) :
    (Measure.map (Phi.symm : N → M) mu).withDensity rho =
      Measure.map (Phi.symm : N → M)
        (mu.withDensity (fun y => rho (Phi.symm y))) := by
  ext A hA
  rw [MeasureTheory.withDensity_apply _ hA]
  rw [MeasureTheory.setLIntegral_map hA hrho Phi.symm.continuous.measurable]
  rw [Measure.map_apply Phi.symm.continuous.measurable hA]
  have hpre : MeasurableSet ((Phi.symm : N → M) ⁻¹' A) :=
    Phi.symm.continuous.measurable hA
  rw [MeasureTheory.withDensity_apply _ hpre]

theorem riemannianVolumeMeasure_pullback_withDensity
    [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]
    [T2Space N] [SigmaCompactSpace N]
    (g : SmoothRiemannianMetric I N) (Phi : M ≃ₘ⟮I, I⟯ N)
    (rho : M → ENNReal) (hrho : Measurable rho) :
    (riemannianVolumeMeasure (I := I) (M := M)
        (Diffeomorph.pullbackMetric g Phi)).withDensity rho =
      Measure.map (Phi.symm : N → M)
        ((riemannianVolumeMeasure (I := I) (M := N) g).withDensity
          (fun y => rho (Phi.symm y))) := by
  rw [riemannianVolumeMeasure_pullback (I := I) g Phi]
  exact map_symm_withDensity (I := I)
    (riemannianVolumeMeasure (I := I) (M := N) g) Phi rho hrho

end DifferentialGeometry.Integral.Measure
