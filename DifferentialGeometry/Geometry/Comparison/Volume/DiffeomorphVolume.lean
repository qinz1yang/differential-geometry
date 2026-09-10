import DifferentialGeometry.Analysis.Integration.Measure.Parametric.Evaluation
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.OpenSubtype
import DifferentialGeometry.Geometry.Metric.Pullback.Basic
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens
import DifferentialGeometry.Topology.SigmaCompactOpen
import DifferentialGeometry.Tensor.Coordinates.ModelBasis

set_option autoImplicit false

noncomputable section

open Bundle Manifold MeasureTheory Set TopologicalSpace
open scoped ContDiff ENNReal Manifold Topology

namespace Poincare.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable [I.Boundaryless]
variable {M N : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N]
  [T2Space N] [SigmaCompactSpace N]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance : MeasurableSpace N := borel N
private local instance : BorelSpace N := ⟨rfl⟩

private def diffeomorphPartialOne (Φ : M ≃ₘ⟮I, I⟯ N) :
    PartialDiffeomorph I I M N 1 where
  toPartialEquiv := Φ.toEquiv.toPartialEquiv
  open_source := isOpen_univ
  open_target := isOpen_univ
  contMDiffOn_toFun := Φ.contMDiff.contMDiffOn.of_le (by norm_num)
  contMDiffOn_invFun := Φ.symm.contMDiff.contMDiffOn.of_le (by norm_num)

private def chartParam (x : M) :
    PartialDiffeomorph 𝓘(ℝ, E) I E M 1 where
  toPartialEquiv := (extChartAt I x).symm
  open_source := isOpen_extChartAt_target x
  open_target := isOpen_extChartAt_source x
  contMDiffOn_toFun := contMDiffOn_extChartAt_symm x
  contMDiffOn_invFun := by
    change ContMDiffOn I 𝓘(ℝ, E) 1 (extChartAt I x) (extChartAt I x).source
    simpa only [extChartAt_source] using
      (contMDiffOn_extChartAt (I := I) (M := M) (x := x) (n := 1))

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
@[simp] private lemma chartParam_source (x : M) :
    (chartParam (I := I) x).source = (extChartAt I x).target := rfl

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
@[simp] private lemma chartParam_target (x : M) :
    (chartParam (I := I) x).target = (extChartAt I x).source := rfl

omit [FiniteDimensional ℝ E] [T2Space M] [SigmaCompactSpace M] in
@[simp] private lemma chartParam_apply (x : M) (w : E) :
    chartParam (I := I) x w = (extChartAt I x).symm w := rfl

omit [I.Boundaryless] [SigmaCompactSpace M] [T2Space N]
    [SigmaCompactSpace N] in
private lemma paramGramMatrix_pullback_trans
    (g : SmoothRiemannianMetric I N) (Φ : M ≃ₘ⟮I, I⟯ N)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {w : E} (hw : w ∈ Ψ.source) :
    paramGramMatrix (I := I) (Diffeomorph.pullbackMetric g Φ) Ψ w =
      paramGramMatrix (I := I) g
        (Ψ.trans (diffeomorphPartialOne Φ)) w := by
  have hΨdiff : MDifferentiableAt 𝓘(ℝ, E) I Ψ w :=
    Ψ.mdifferentiableAt one_ne_zero hw
  have hΦdiff : MDifferentiableAt I I Φ (Ψ w) :=
    Φ.contMDiff.mdifferentiableAt (by norm_num)
  ext i j
  rw [paramGramMatrix_apply, paramGramMatrix_apply,
    Diffeomorph.pullbackMetric_inner]
  have hi := mfderiv_comp_apply
    (I := 𝓘(ℝ, E)) (I' := I) (I'' := I)
    (f := (Ψ : E → M)) (g := (Φ : M → N)) (x := w)
    hΦdiff hΨdiff ((chartModelBasis E) i)
  have hj := mfderiv_comp_apply
    (I := 𝓘(ℝ, E)) (I' := I) (I'' := I)
    (f := (Ψ : E → M)) (g := (Φ : M → N)) (x := w)
    hΦdiff hΨdiff ((chartModelBasis E) j)
  change
    g.inner (Φ (Ψ w))
        (mfderiv I I Φ (Ψ w)
          (mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) i)))
        (mfderiv I I Φ (Ψ w)
          (mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) j))) =
      g.inner (Φ (Ψ w))
        (mfderiv 𝓘(ℝ, E) I (fun z ↦ Φ (Ψ z)) w
          ((chartModelBasis E) i))
        (mfderiv 𝓘(ℝ, E) I (fun z ↦ Φ (Ψ z)) w
          ((chartModelBasis E) j))
  simpa only [PartialEquiv.coe_trans, Function.comp_apply, Function.comp_def] using
    congrArg₂ (fun v z ↦ g.inner (Φ (Ψ w)) v z) hi.symm hj.symm

omit [I.Boundaryless] [SigmaCompactSpace M] [T2Space N]
    [SigmaCompactSpace N] in
private lemma paramDensity_pullback_trans
    (g : SmoothRiemannianMetric I N) (Φ : M ≃ₘ⟮I, I⟯ N)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1)
    {w : E} (hw : w ∈ Ψ.source) :
    paramDensity (I := I) (Diffeomorph.pullbackMetric g Φ) Ψ w =
      paramDensity (I := I) g
        (Ψ.trans (diffeomorphPartialOne Φ)) w := by
  unfold paramDensity
  rw [paramGramMatrix_pullback_trans (I := I) g Φ Ψ hw]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ N]
    [T2Space N] [SigmaCompactSpace N] in
private lemma trans_diffeomorphPartialOne_source
    (Φ : M ≃ₘ⟮I, I⟯ N)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1) :
    (Ψ.trans (diffeomorphPartialOne Φ)).source = Ψ.source := by
  change (Ψ.toPartialEquiv.trans
    (diffeomorphPartialOne Φ).toPartialEquiv).source = Ψ.source
  rw [PartialEquiv.trans_source]
  simp [diffeomorphPartialOne]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ N]
    [T2Space N] [SigmaCompactSpace N] in
private lemma trans_diffeomorphPartialOne_target
    (Φ : M ≃ₘ⟮I, I⟯ N)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1) :
    (Ψ.trans (diffeomorphPartialOne Φ)).target = Φ '' Ψ.target := by
  change (Ψ.toPartialEquiv.trans
    (diffeomorphPartialOne Φ).toPartialEquiv).target = Φ '' Ψ.target
  rw [PartialEquiv.trans_target'']
  simp only [diffeomorphPartialOne, Equiv.toPartialEquiv_source, univ_inter,
    Equiv.toPartialEquiv_apply, Diffeomorph.coe_toEquiv]

omit [I.Boundaryless] in
private theorem map_restrict_param_target
    (g : SmoothRiemannianMetric I N) (Φ : M ≃ₘ⟮I, I⟯ N)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1) :
    (Measure.map Φ
        (riemannianVolumeMeasure (I := I) (M := M)
          (Diffeomorph.pullbackMetric g Φ))).restrict (Φ '' Ψ.target) =
      (riemannianVolumeMeasure (I := I) (M := N) g).restrict (Φ '' Ψ.target) := by
  let Θ : PartialDiffeomorph 𝓘(ℝ, E) I E N 1 :=
    Ψ.trans (diffeomorphPartialOne Φ)
  have hΘsource : Θ.source = Ψ.source :=
    trans_diffeomorphPartialOne_source (I := I) Φ Ψ
  have hΘtarget : Θ.target = Φ '' Ψ.target :=
    trans_diffeomorphPartialOne_target (I := I) Φ Ψ
  have hΦmeas : Measurable (Φ : M → N) := Φ.continuous.measurable
  ext A hA
  have htargetMeas : MeasurableSet (Φ '' Ψ.target) := by
    rw [← hΘtarget]
    exact Θ.open_target.measurableSet
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
  rw [Measure.map_apply hΦmeas (hA.inter htargetMeas)]
  let S : Set N := A ∩ Φ '' Ψ.target
  let B : Set E := Θ.symm '' S
  have hSmeas : MeasurableSet S := hA.inter htargetMeas
  have hStarget : S ⊆ Θ.target := by
    rw [hΘtarget]
    exact inter_subset_right
  have hBmeas : MeasurableSet B :=
    measurableSet_symm_image_param (I := I) Θ hSmeas hStarget
  have hBΘsource : B ⊆ Θ.source := by
    rintro w ⟨y, hyS, rfl⟩
    exact Θ.toPartialEquiv.map_target (hStarget hyS)
  have hBΨsource : B ⊆ Ψ.source := by
    rwa [← hΘsource]
  have hΘimage : Θ '' B = S := by
    exact Θ.toPartialEquiv.image_symm_image_of_subset_target hStarget
  have hpreimage : Φ ⁻¹' S = Ψ '' B := by
    rw [← hΘimage]
    ext x
    constructor
    · intro hx
      obtain ⟨w, hwB, hw⟩ := hx
      refine ⟨w, hwB, Φ.injective ?_⟩
      change Θ w = Φ x at hw
      change Φ (Ψ w) = Φ x
      exact hw
    · rintro ⟨w, hwB, rfl⟩
      refine ⟨w, hwB, ?_⟩
      rfl
  change riemannianVolumeMeasure (I := I) (M := M)
      (Diffeomorph.pullbackMetric g Φ) (Φ ⁻¹' S) =
    riemannianVolumeMeasure (I := I) (M := N) g S
  rw [hpreimage, ← hΘimage]
  rw [riemannianVolumeMeasure_image_param_eq
      (I := I) (Diffeomorph.pullbackMetric g Φ) Ψ hBmeas hBΨsource,
    riemannianVolumeMeasure_image_param_eq (I := I) g Θ hBmeas hBΘsource]
  exact MeasureTheory.setLIntegral_congr_fun hBmeas fun w hw ↦ by
    rw [paramDensity_pullback_trans (I := I) g Φ Ψ (hBΨsource hw)]

theorem riemannianVolumeMeasure_map_pullback
    (g : SmoothRiemannianMetric I N) (Φ : M ≃ₘ⟮I, I⟯ N) :
    Measure.map Φ
        (riemannianVolumeMeasure (I := I) (M := M)
          (Diffeomorph.pullbackMetric g Φ)) =
      riemannianVolumeMeasure (I := I) (M := N) g := by
  obtain ⟨s, hs_countable, hs_cover⟩ :=
    countable_cover_nhds_of_sigmaCompact
      (fun x : M ↦ chart_source_mem_nhds H x)
  have hcover : ⋃ x ∈ s, Φ '' (chartAt H x).source = (Set.univ : Set N) := by
    apply Set.eq_univ_of_forall
    intro y
    have hy : Φ.symm y ∈ ⋃ x ∈ s, (chartAt H x).source := by
      rw [hs_cover]
      exact Set.mem_univ _
    simp only [Set.mem_iUnion] at hy ⊢
    obtain ⟨x, hx_s, hx_chart⟩ := hy
    exact ⟨x, hx_s, Φ.symm y, hx_chart, Φ.apply_symm_apply y⟩
  refine Measure.ext_of_biUnion_eq_univ hs_countable hcover ?_
  intro x hx
  simpa only [chartParam_target, extChartAt_source] using
    (map_restrict_param_target (I := I) g Φ (chartParam (I := I) x))

theorem measurePreserving_riemannianVolume_pullback
    (g : SmoothRiemannianMetric I N) (Φ : M ≃ₘ⟮I, I⟯ N) :
    MeasurePreserving Φ
      (riemannianVolumeMeasure (I := I) (M := M)
        (Diffeomorph.pullbackMetric g Φ))
      (riemannianVolumeMeasure (I := I) (M := N) g) := by
  exact ⟨Φ.continuous.measurable,
    riemannianVolumeMeasure_map_pullback (I := I) g Φ⟩

private local instance opensMeasurableSpace (U : Opens M) :
    MeasurableSpace U := borel U

private local instance opensBorelSpace (U : Opens M) : BorelSpace U :=
  ⟨rfl⟩

omit [T2Space M] in
private def opensInclusionPartial
    (U : Opens M) (hU : Nonempty U) : PartialDiffeomorph I I U M 1 := by
  let e : OpenPartialHomeomorph U M := U.openPartialHomeomorphSubtypeCoe hU
  exact
    { toPartialEquiv := e.toPartialEquiv
      open_source := e.open_source
      open_target := e.open_target
      contMDiffOn_toFun := by
        change ContMDiffOn I I 1 (Subtype.val : U → M) e.source
        exact (contMDiff_subtype_val (I := I) (U := U)).contMDiffOn
      contMDiffOn_invFun := by
        intro x hx
        have heq : (id : M → M) =ᶠ[nhds x]
            (fun z ↦ ((e.symm z : U) : M)) :=
          Filter.eventuallyEq_of_mem (e.open_target.mem_nhds hx) fun z hz ↦ by
            symm
            exact e.right_inv hz
        have hcoe : ContMDiffAt I I ∞
            (fun z ↦ ((e.symm z : U) : M)) x :=
          (contMDiffAt_id (I := I)).congr_of_eventuallyEq heq.symm
        exact ((codRestr_contMDiffAt
          (I := I) (J := I) (V := U)
          (fun z ↦ (e.symm z : U).property) hcoe).contMDiffWithinAt).of_le
            (by norm_num) }

omit [I.Boundaryless] [SigmaCompactSpace M] [T2Space N]
    [SigmaCompactSpace N] in
private lemma paramGramMatrix_restrictOpen_trans
    (g : SmoothRiemannianMetric I M) (U : Opens M) (hU : Nonempty U)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E U 1)
    {w : E} (hw : w ∈ Ψ.source) :
    paramGramMatrix (I := I) (g.restrictOpen (I := I) U) Ψ w =
      paramGramMatrix (I := I) g
        (Ψ.trans (opensInclusionPartial (I := I) U hU)) w := by
  have hΨdiff : MDifferentiableAt 𝓘(ℝ, E) I Ψ w :=
    Ψ.mdifferentiableAt one_ne_zero hw
  have hinclDiff : MDifferentiableAt I I (Subtype.val : U → M) (Ψ w) :=
    (contMDiff_subtype_val (I := I) (U := U)).mdifferentiableAt one_ne_zero
  ext i j
  rw [paramGramMatrix_apply, paramGramMatrix_apply,
    SmoothRiemannianMetric.restrictOpen_inner]
  have hi := mfderiv_comp_apply
    (I := 𝓘(ℝ, E)) (I' := I) (I'' := I)
    (f := (Ψ : E → U)) (g := (Subtype.val : U → M)) (x := w)
    hinclDiff hΨdiff ((chartModelBasis E) i)
  have hj := mfderiv_comp_apply
    (I := 𝓘(ℝ, E)) (I' := I) (I'' := I)
    (f := (Ψ : E → U)) (g := (Subtype.val : U → M)) (x := w)
    hinclDiff hΨdiff ((chartModelBasis E) j)
  rw [mfderiv_subtype_val_apply] at hi hj
  change
    g.inner (Ψ w : M)
        (mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) i))
        (mfderiv 𝓘(ℝ, E) I Ψ w ((chartModelBasis E) j)) =
      g.inner (Ψ w : M)
        (mfderiv 𝓘(ℝ, E) I (fun z ↦ ((Ψ z : U) : M)) w
          ((chartModelBasis E) i))
        (mfderiv 𝓘(ℝ, E) I (fun z ↦ ((Ψ z : U) : M)) w
          ((chartModelBasis E) j))
  simpa only [PartialEquiv.coe_trans, Function.comp_apply, Function.comp_def,
    opensInclusionPartial, Opens.openPartialHomeomorphSubtypeCoe_coe] using
    congrArg₂ (fun v z ↦ g.inner (Ψ w : M) v z) hi.symm hj.symm

omit [I.Boundaryless] [SigmaCompactSpace M] [T2Space N]
    [SigmaCompactSpace N] in
private lemma paramDensity_restrictOpen_trans
    (g : SmoothRiemannianMetric I M) (U : Opens M) (hU : Nonempty U)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E U 1)
    {w : E} (hw : w ∈ Ψ.source) :
    paramDensity (I := I) (g.restrictOpen (I := I) U) Ψ w =
      paramDensity (I := I) g
        (Ψ.trans (opensInclusionPartial (I := I) U hU)) w := by
  unfold paramDensity
  rw [paramGramMatrix_restrictOpen_trans (I := I) g U hU Ψ hw]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ N]
    [T2Space N] [SigmaCompactSpace N] in
private lemma trans_opensInclusionPartial_source
    (U : Opens M) (hU : Nonempty U)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E U 1) :
    (Ψ.trans (opensInclusionPartial (I := I) U hU)).source = Ψ.source := by
  change (Ψ.toPartialEquiv.trans
    (opensInclusionPartial (I := I) U hU).toPartialEquiv).source = Ψ.source
  rw [PartialEquiv.trans_source]
  simp [opensInclusionPartial]

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ N]
    [T2Space N] [SigmaCompactSpace N] in
private lemma trans_opensInclusionPartial_target
    (U : Opens M) (hU : Nonempty U)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E U 1) :
    (Ψ.trans (opensInclusionPartial (I := I) U hU)).target =
      (Subtype.val : U → M) '' Ψ.target := by
  change (Ψ.toPartialEquiv.trans
    (opensInclusionPartial (I := I) U hU).toPartialEquiv).target =
      (Subtype.val : U → M) '' Ψ.target
  rw [PartialEquiv.trans_target'']
  simp only [opensInclusionPartial,
    Opens.openPartialHomeomorphSubtypeCoe_source, univ_inter]
  change (Subtype.val : U → M) '' Ψ.target = _
  rfl

omit [I.Boundaryless] [T2Space N] [SigmaCompactSpace N] in
private theorem map_restrictOpen_restrict_param_target
    (g : SmoothRiemannianMetric I M) (U : Opens M) [SigmaCompactSpace U]
    (hU : Nonempty U)
    (Ψ : PartialDiffeomorph 𝓘(ℝ, E) I E U 1) :
    (Measure.map (Subtype.val : U → M)
        (riemannianVolumeMeasure (I := I) (M := U)
          (g.restrictOpen (I := I) U))).restrict
            ((Subtype.val : U → M) '' Ψ.target) =
      (riemannianVolumeMeasure (I := I) (M := M) g).restrict
        ((Subtype.val : U → M) '' Ψ.target) := by
  let Θ : PartialDiffeomorph 𝓘(ℝ, E) I E M 1 :=
    Ψ.trans (opensInclusionPartial (I := I) U hU)
  have hΘsource : Θ.source = Ψ.source :=
    trans_opensInclusionPartial_source (I := I) U hU Ψ
  have hΘtarget : Θ.target = (Subtype.val : U → M) '' Ψ.target :=
    trans_opensInclusionPartial_target (I := I) U hU Ψ
  have hinclMeas : Measurable (Subtype.val : U → M) :=
    continuous_subtype_val.measurable
  ext A hA
  have htargetMeas :
      MeasurableSet ((Subtype.val : U → M) '' Ψ.target) := by
    rw [← hΘtarget]
    exact Θ.open_target.measurableSet
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
  rw [Measure.map_apply hinclMeas (hA.inter htargetMeas)]
  let S : Set M := A ∩ (Subtype.val : U → M) '' Ψ.target
  let B : Set E := Θ.symm '' S
  have hSmeas : MeasurableSet S := hA.inter htargetMeas
  have hStarget : S ⊆ Θ.target := by
    rw [hΘtarget]
    exact inter_subset_right
  have hBmeas : MeasurableSet B :=
    measurableSet_symm_image_param (I := I) Θ hSmeas hStarget
  have hBΘsource : B ⊆ Θ.source := by
    rintro w ⟨y, hyS, rfl⟩
    exact Θ.toPartialEquiv.map_target (hStarget hyS)
  have hBΨsource : B ⊆ Ψ.source := by
    rwa [← hΘsource]
  have hΘimage : Θ '' B = S :=
    Θ.toPartialEquiv.image_symm_image_of_subset_target hStarget
  have hpreimage : (Subtype.val : U → M) ⁻¹' S = Ψ '' B := by
    rw [← hΘimage]
    ext x
    constructor
    · intro hx
      obtain ⟨w, hwB, hw⟩ := hx
      refine ⟨w, hwB, Subtype.ext ?_⟩
      change Θ w = (x : M) at hw
      exact hw
    · rintro ⟨w, hwB, rfl⟩
      exact ⟨w, hwB, rfl⟩
  change riemannianVolumeMeasure (I := I) (M := U)
      (g.restrictOpen (I := I) U) ((Subtype.val : U → M) ⁻¹' S) =
    riemannianVolumeMeasure (I := I) (M := M) g S
  rw [hpreimage, ← hΘimage]
  rw [riemannianVolumeMeasure_image_param_eq
      (I := I) (g.restrictOpen (I := I) U) Ψ hBmeas hBΨsource,
    riemannianVolumeMeasure_image_param_eq (I := I) g Θ hBmeas hBΘsource]
  exact MeasureTheory.setLIntegral_congr_fun hBmeas fun w hw ↦ by
    rw [paramDensity_restrictOpen_trans (I := I) g U hU Ψ (hBΨsource hw)]

theorem riemannianVolumeMeasure_map_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : Opens M) [SigmaCompactSpace U] :
    Measure.map (Subtype.val : U → M)
        (riemannianVolumeMeasure (I := I) (M := U)
          (g.restrictOpen (I := I) U)) =
      (riemannianVolumeMeasure (I := I) (M := M) g).restrict U := by
  cases isEmpty_or_nonempty U with
  | inl hUempty =>
      ext A hA
      rw [Measure.map_apply continuous_subtype_val.measurable hA,
        Measure.restrict_apply hA]
      have hpre : (Subtype.val : U → M) ⁻¹' A = ∅ :=
        Set.eq_empty_iff_forall_notMem.mpr fun x _ ↦ isEmptyElim x
      have hinter : A ∩ (U : Set M) = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        rintro x ⟨_, hxU⟩
        exact hUempty.false ⟨x, hxU⟩
      change (riemannianVolumeMeasure (I := I) (M := U)
          (g.restrictOpen (I := I) U)) ((Subtype.val : U → M) ⁻¹' A) =
        riemannianVolumeMeasure (I := I) (M := M) g (A ∩ (U : Set M))
      rw [hpre, hinter, measure_empty, measure_empty]
  | inr hUnonempty =>
      let μU : Measure U :=
        riemannianVolumeMeasure (I := I) (M := U)
          (g.restrictOpen (I := I) U)
      let μM : Measure M := riemannianVolumeMeasure (I := I) (M := M) g
      let incl : U → M := Subtype.val
      obtain ⟨s, hs_countable, hs_cover⟩ :=
        countable_cover_nhds_of_sigmaCompact
          (fun x : U ↦ chart_source_mem_nhds H x)
      have hcover :
          ⋃ x ∈ s, incl '' (chartAt H x).source = (U : Set M) := by
        apply Set.Subset.antisymm
        · exact iUnion₂_subset fun x _ ↦ image_subset_iff.mpr fun y _ ↦ y.property
        · intro y hy
          let yu : U := ⟨y, hy⟩
          have hyu : yu ∈ ⋃ x ∈ s, (chartAt H x).source := by
            rw [hs_cover]
            exact Set.mem_univ _
          simp only [Set.mem_iUnion] at hyu ⊢
          obtain ⟨x, hx_s, hyu_chart⟩ := hyu
          exact ⟨x, hx_s, yu, hyu_chart, rfl⟩
      have hlocal : ∀ x ∈ s,
          (Measure.map incl μU).restrict (incl '' (chartAt H x).source) =
            (μM.restrict U).restrict (incl '' (chartAt H x).source) := by
        intro x hx
        have hsubset : incl '' (chartAt H x).source ⊆ (U : Set M) :=
          image_subset_iff.mpr fun y _ ↦ y.property
        rw [Measure.restrict_restrict_of_subset hsubset]
        simpa only [μU, μM, incl, chartParam_target, extChartAt_source] using
          (map_restrictOpen_restrict_param_target (I := I) g U hUnonempty
            (chartParam (I := I) (M := U) x))
      have honU :
          (Measure.map incl μU).restrict U =
            (μM.restrict U).restrict U := by
        have hchartUnion :=
          (Measure.restrict_biUnion_congr hs_countable).2 hlocal
        rw [hcover] at hchartUnion
        exact hchartUnion
      have hinclMeas : Measurable incl := continuous_subtype_val.measurable
      have hmapSupport : (Measure.map incl μU).restrict U = Measure.map incl μU := by
        ext A hA
        calc
          (Measure.map incl μU).restrict U A =
              (Measure.map incl μU) (A ∩ (U : Set M)) :=
            Measure.restrict_apply hA
          _ = μU (incl ⁻¹' (A ∩ (U : Set M))) :=
            Measure.map_apply hinclMeas (hA.inter U.2.measurableSet)
          _ = μU (incl ⁻¹' A) := by
            congr 1
            ext x
            simp only [Set.mem_preimage, mem_inter_iff]
            exact and_iff_left x.property
          _ = Measure.map incl μU A :=
            (Measure.map_apply hinclMeas hA).symm
      have hrestrictIdem : (μM.restrict U).restrict U = μM.restrict U :=
        Measure.restrict_restrict_of_subset Subset.rfl
      rw [hmapSupport, hrestrictIdem] at honU
      exact honU

theorem measurePreserving_riemannianVolume_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : Opens M) [SigmaCompactSpace U] :
    MeasurePreserving (Subtype.val : U → M)
      (riemannianVolumeMeasure (I := I) (M := U)
        (g.restrictOpen (I := I) U))
      ((riemannianVolumeMeasure (I := I) (M := M) g).restrict U) := by
  exact ⟨continuous_subtype_val.measurable,
    riemannianVolumeMeasure_map_restrictOpen (I := I) g U⟩

end Poincare.Geometry.Riemannian.VolumeComparison
