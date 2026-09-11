import DifferentialGeometry.Geometry.Neck.InsertionInput

set_option autoImplicit false
noncomputable section
open Set Function Bundle Manifold TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry.Neck.datumIsometry
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
variable {E E' H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Fact (Module.finrank ℝ E = 3)]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [Fact (Module.finrank ℝ E' = 3)]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ E' H'} [I.Boundaryless] [J.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N] [T2Space N]
  {g : SmoothRiemannianMetric I M} {g' : SmoothRiemannianMetric J N}
  {x₀ : M} {x₀' : N} {δ : ℝ} {k : ℕ}
  {d : normalizedDatum g x₀ δ k} {d' : normalizedDatum g' x₀' δ k}

private def sourceMap (F : datumIsometry d d') : bufferedCylinder δ → F.source :=
  fun q => ⟨d.map q, F.image_source q⟩
private theorem sourceMap_smooth (F : datumIsometry d d') : ContMDiff IC I ∞ (sourceMap F) :=
  (ContMDiff.subtypeVal_comp_iff F.source (sourceMap F)).mp d.smooth
private theorem sourceMap_deriv (F : datumIsometry d d') (q : bufferedCylinder δ) :
    mfderiv IC I (sourceMap F) q = mfderiv IC I d.map q := by
  have he : (Subtype.val : F.source → M) ∘ sourceMap F = d.map := rfl
  rw [← he, mfderiv_comp q
    (contMDiff_subtype_val.mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0))
    ((sourceMap_smooth F).mdifferentiableAt (by decide)), mfderiv_subtype_val]
  rfl

private theorem targetMap_deriv (F : datumIsometry d d') (q : bufferedCylinder δ) :
    mfderiv IC J d'.map q =
      (mfderiv I J F.equiv (sourceMap F q)).comp (mfderiv IC I d.map q) := by
  have he : (Subtype.val : F.target → N) ∘ F.equiv ∘ sourceMap F = d'.map :=
    funext F.chart_eq
  rw [← he, mfderiv_comp q
    (contMDiff_subtype_val.mdifferentiableAt (by decide : (∞ : ℕ∞ω) ≠ 0))
    ((F.equiv.contMDiff.comp (sourceMap_smooth F)).mdifferentiableAt (by decide)),
    mfderiv_subtype_val]
  change mfderiv IC J (F.equiv ∘ sourceMap F) q = _
  rw [mfderiv_comp q (F.equiv.contMDiff.mdifferentiableAt (by decide))
    ((sourceMap_smooth F).mdifferentiableAt (by decide)), sourceMap_deriv]

theorem normalizedMetric_eq (F : datumIsometry d d') : d'.normalizedMetric = d.normalizedMetric := by
  apply SmoothRiemannianMetric.ext_inner
  intro q u v
  rw [normalizedDatum.normalizedMetric_inner, normalizedDatum.normalizedMetric_inner, F.scalar_eq]
  congr 1
  have hh := congrArg (fun G : SmoothRiemannianMetric I F.source =>
    G.inner (sourceMap F q) (mfderiv IC I d.map q u) (mfderiv IC I d.map q v)) F.metric_eq
  erw [Diffeomorph.pullbackMetricCross_inner] at hh
  change g'.inner (F.equiv (sourceMap F q)).val
      (mfderiv I J F.equiv (sourceMap F q) (mfderiv IC I d.map q u))
      (mfderiv I J F.equiv (sourceMap F q) (mfderiv IC I d.map q v)) =
    g.inner (d.map q) (mfderiv IC I d.map q u) (mfderiv IC I d.map q v) at hh
  have hp : (F.equiv (sourceMap F q)).val = d'.map q := F.chart_eq q
  rw [hp] at hh
  rw [targetMap_deriv F q]
  exact hh

theorem controlledMetric_eq (F : datumIsometry d d') : d'.controlledMetric = d.controlledMetric := by
  change d'.normalizedMetric.restrictOpenOfSubset _ = d.normalizedMetric.restrictOpenOfSubset _
  rw [F.normalizedMetric_eq]
end DifferentialGeometry.Geometry.Neck.datumIsometry
