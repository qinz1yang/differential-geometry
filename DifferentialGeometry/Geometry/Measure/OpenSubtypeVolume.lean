import DifferentialGeometry.Analysis.Integration.Measure.Parametric.Evaluation
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.OpenSubtype
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import Mathlib.MeasureTheory.Measure.Restrict
import DifferentialGeometry.Geometry.Metric.Coordinates.ChartGram

set_option autoImplicit false

noncomputable section

open Bundle Filter Function Manifold MeasureTheory Set TopologicalSpace
open DifferentialGeometry DifferentialGeometry.Integral.Measure
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Measure

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

include I in
omit [I.Boundaryless] [IsManifold I ∞ M] [T2Space M] in
private theorem openSubtype_sigmaCompact (U : Opens M) : SigmaCompactSpace U := by
  let : ProperSpace E := FiniteDimensional.proper ℝ E
  let : SecondCountableTopology H := I.secondCountableTopology
  let : SecondCountableTopology M := ChartedSpace.secondCountable_of_sigmaCompact H M
  let : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  let : LocallyCompactSpace U := U.isOpen.locallyCompactSpace
  infer_instance

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩
private local instance (U : Opens M) : MeasurableSpace U := borel U
private local instance (U : Opens M) : BorelSpace U := ⟨rfl⟩

private def volumeChartParam (p : M) : PartialDiffeomorph 𝓘(ℝ, E) I E M 1 where
  toPartialEquiv := (extChartAt I p).symm
  open_source := isOpen_extChartAt_target p
  open_target := isOpen_extChartAt_source p
  contMDiffOn_toFun := contMDiffOn_extChartAt_symm (I := I) (n := 1) p
  contMDiffOn_invFun := by
    change ContMDiffOn I 𝓘(ℝ, E) 1 (extChartAt I p) (extChartAt I p).source
    simpa only [extChartAt_source] using
      (contMDiffOn_extChartAt (I := I) (n := 1) (x := p))

omit [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] in
private theorem exists_inclusion_param (U : Opens M) (p : U) :
    ∃ Phi : PartialDiffeomorph I I U M 1,
      p ∈ Phi.source ∧ EqOn (Subtype.val : U → M) Phi Phi.source := by
  have hid : IsLocalDiffeomorphOn I I ∞ (id : M → M) (U : Set M) :=
    (Diffeomorph.refl I M ∞).isLocalDiffeomorph.isLocalDiffeomorphOn U
  have hinc : IsLocalDiffeomorph I I ∞ (Subtype.val : U → M) :=
    isLocalDiffeomorph_restrict_open (I := I) (J := I) U hid
  obtain ⟨Phi, hp, heq⟩ := hinc p
  refine ⟨{
    toPartialEquiv := Phi.toPartialEquiv
    open_source := Phi.open_source
    open_target := Phi.open_target
    contMDiffOn_toFun := Phi.contMDiffOn_toFun.of_le (by norm_num)
    contMDiffOn_invFun := Phi.contMDiffOn_invFun.of_le (by norm_num) }, hp, heq⟩

omit [I.Boundaryless] [SigmaCompactSpace M] in
private theorem restriction_param_density
    (g : SmoothRiemannianMetric I M) (U : Opens M)
    (Psi : PartialDiffeomorph 𝓘(ℝ, E) I E U 1)
    (Phi : PartialDiffeomorph I I U M 1)
    (hPhi : EqOn (Subtype.val : U → M) Phi Phi.source)
    {w : E} (hw : w ∈ (Psi.trans Phi).source) :
    paramDensity (g.restrictOpen U) Psi w = paramDensity g (Psi.trans Phi) w := by
  have hw' : w ∈ Psi.source ∧ Psi w ∈ Phi.source := hw
  have he : (Subtype.val ∘ Psi : E → M) =ᶠ[𝓝 w] (Psi.trans Phi : E → M) :=
    Filter.eventuallyEq_of_mem ((Psi.trans Phi).open_source.mem_nhds hw) (by
      intro z hz
      exact hPhi hz.2)
  have hd := he.mfderiv_eq (I := 𝓘(ℝ, E)) (I' := I)
  rw [mfderiv_comp w (hasMFDerivAt_subtype_val (I := I) U (Psi w)).mdifferentiableAt
    (Psi.mdifferentiableAt (by norm_num) hw'.1), mfderiv_subtype_val] at hd
  change (mfderiv 𝓘(ℝ, E) I Psi w : E →L[ℝ] E) =
    (mfderiv 𝓘(ℝ, E) I (Psi.trans Phi) w : E →L[ℝ] E) at hd
  have hpoint : (Psi w : U).val = (Psi.trans Phi) w := hPhi hw'.2
  rw [paramDensity_apply, paramDensity_apply]
  congr 2
  ext i j
  simp only [paramGramMatrix_apply, SmoothRiemannianMetric.restrictOpen_inner]
  change g.inner (Psi w : M)
      ((mfderiv 𝓘(ℝ, E) I Psi w : E →L[ℝ] E) ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))
      ((mfderiv 𝓘(ℝ, E) I Psi w : E →L[ℝ] E) ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j)) =
    g.inner ((Psi.trans Phi) w)
      ((mfderiv 𝓘(ℝ, E) I (Psi.trans Phi) w : E →L[ℝ] E) ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))
      ((mfderiv 𝓘(ℝ, E) I (Psi.trans Phi) w : E →L[ℝ] E) ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j))
  rw [hd]
  exact congrArg
    (fun z : M ↦ g.inner z
      (mfderiv 𝓘(ℝ, E) I (Psi.trans Phi) w ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) i))
      (mfderiv 𝓘(ℝ, E) I (Psi.trans Phi) w ((DifferentialGeometry.Tensor.Coordinates.chartModelBasis E) j))) hpoint

omit [I.Boundaryless] in
private theorem restriction_volume_on_param_patch
    (g : SmoothRiemannianMetric I M) (U : Opens M)
    (Psi : PartialDiffeomorph 𝓘(ℝ, E) I E U 1)
    (Phi : PartialDiffeomorph I I U M 1)
    (hPhi : EqOn (Subtype.val : U → M) Phi Phi.source)
    {A : Set U} (hA : MeasurableSet A) (hpatch : A ⊆ Psi.target ∩ Phi.source) :
    let : SigmaCompactSpace U := openSubtype_sigmaCompact (I := I) U
    riemannianVolumeMeasure (I := I) (M := U) (g.restrictOpen U) A =
      riemannianVolumeMeasure (I := I) (M := M) g (Subtype.val '' A) := by
  let : SigmaCompactSpace U := openSubtype_sigmaCompact (I := I) U
  let B : Set E := Psi.symm '' A
  have hB : MeasurableSet B :=
    measurableSet_symm_image_param Psi hA (fun z hz ↦ (hpatch hz).1)
  have hsource : B ⊆ Psi.source := by
    rintro w ⟨z, hz, rfl⟩
    exact Psi.toPartialEquiv.map_target (hpatch hz).1
  have htransSource : B ⊆ (Psi.trans Phi).source := by
    rintro w ⟨z, hz, rfl⟩
    change Psi.symm z ∈ Psi.source ∧ Psi (Psi.symm z) ∈ Phi.source
    refine ⟨Psi.toPartialEquiv.map_target (hpatch hz).1, ?_⟩
    exact (Psi.toPartialEquiv.right_inv (hpatch hz).1).symm ▸ (hpatch hz).2
  have hPsiB : Psi '' B = A := by
    ext z
    constructor
    · rintro ⟨w, ⟨y, hy, rfl⟩, rfl⟩
      exact (Psi.toPartialEquiv.right_inv (hpatch hy).1).symm ▸ hy
    · intro hz
      exact ⟨Psi.symm z, ⟨z, hz, rfl⟩,
        Psi.toPartialEquiv.right_inv (hpatch hz).1⟩
  have htransB : (Psi.trans Phi) '' B = Subtype.val '' A := by
    calc
      (Psi.trans Phi) '' B = (Subtype.val ∘ Psi) '' B := by
        apply image_congr
        intro w hw
        exact (hPhi (htransSource hw).2).symm
      _ = Subtype.val '' (Psi '' B) :=
        (image_image (Subtype.val : U → M) (Psi : E → U) B).symm
      _ = Subtype.val '' A := by rw [hPsiB]
  calc
    riemannianVolumeMeasure (I := I) (M := U) (g.restrictOpen U) A =
        ∫⁻ w in B, ENNReal.ofReal (paramDensity (g.restrictOpen U) Psi w)
          ∂modelHaar (E := E) := by
      rw [← hPsiB]
      exact riemannianVolumeMeasure_image_param_eq (g.restrictOpen U) Psi hB hsource
    _ = ∫⁻ w in B, ENNReal.ofReal (paramDensity g (Psi.trans Phi) w)
        ∂modelHaar (E := E) := by
      apply setLIntegral_congr_fun hB
      intro w hw
      exact congrArg ENNReal.ofReal (restriction_param_density g U Psi Phi hPhi (htransSource hw))
    _ = riemannianVolumeMeasure (I := I) (M := M) g (Subtype.val '' A) := by
      rw [← htransB]
      exact (riemannianVolumeMeasure_image_param_eq g (Psi.trans Phi) hB htransSource).symm

private theorem restriction_volume_eq_comap
    (g : SmoothRiemannianMetric I M) (U : Opens M) :
    let : SigmaCompactSpace U := openSubtype_sigmaCompact (I := I) U
    riemannianVolumeMeasure (I := I) (M := U) (g.restrictOpen U) =
      Measure.comap (Subtype.val : U → M) (riemannianVolumeMeasure (I := I) (M := M) g) := by
  let : SigmaCompactSpace U := openSubtype_sigmaCompact (I := I) U
  classical
  choose Phi hpoint hPhi using fun p : U ↦ exists_inclusion_param (I := I) U p
  let Psi : U → PartialDiffeomorph 𝓘(ℝ, E) I E U 1 :=
    fun p ↦ volumeChartParam (I := I) (M := U) p
  let W : U → Set U := fun p ↦ (Psi p).target ∩ (Phi p).source
  have hWopen (p : U) : IsOpen (W p) := (Psi p).open_target.inter (Phi p).open_source
  have hpW (p : U) : p ∈ W p :=
    ⟨mem_extChartAt_source (I := I) p, hpoint p⟩
  obtain ⟨C, hC, hcover⟩ := countable_cover_nhds_of_sigmaCompact
    (fun p : U ↦ (hWopen p).mem_nhds (hpW p))
  have hval : MeasurableEmbedding (Subtype.val : U → M) :=
    U.isOpen.isOpenEmbedding_subtypeVal.measurableEmbedding (mα := borel U)
  apply Measure.ext_of_biUnion_eq_univ hC hcover
  intro p _hp
  ext A hA
  rw [Measure.restrict_apply hA, Measure.restrict_apply hA, hval.comap_apply]
  exact restriction_volume_on_param_patch g U (Psi p) (Phi p) (hPhi p)
    (hA.inter (hWopen p).measurableSet) inter_subset_right

theorem riemannianVolumeMeasure_map_restrictOpen
    (g : SmoothRiemannianMetric I M) (U : Opens M) :
    let : SigmaCompactSpace U := openSubtype_sigmaCompact (I := I) U
    Measure.map (Subtype.val : U → M)
        (riemannianVolumeMeasure (I := I) (M := U) (g.restrictOpen U)) =
      (riemannianVolumeMeasure (I := I) (M := M) g).restrict (U : Set M) := by
  let : SigmaCompactSpace U := openSubtype_sigmaCompact (I := I) U
  have hval : MeasurableEmbedding (Subtype.val : U → M) :=
    U.isOpen.isOpenEmbedding_subtypeVal.measurableEmbedding (mα := borel U)
  dsimp only
  rw [restriction_volume_eq_comap g U, hval.map_comap, Subtype.range_coe]

theorem riemannianVolumeMeasure_restrictOpen_preimage_of_subset
    (g : SmoothRiemannianMetric I M) (U : Opens M)
    {A : Set M} (hA : MeasurableSet A) (hAU : A ⊆ U) :
    let : SigmaCompactSpace U := openSubtype_sigmaCompact (I := I) U
    riemannianVolumeMeasure (I := I) (M := U) (g.restrictOpen U) (Subtype.val ⁻¹' A) =
      riemannianVolumeMeasure (I := I) (M := M) g A := by
  let : SigmaCompactSpace U := openSubtype_sigmaCompact (I := I) U
  have hval : MeasurableEmbedding (Subtype.val : U → M) :=
    U.isOpen.isOpenEmbedding_subtypeVal.measurableEmbedding (mα := borel U)
  have hmap := congrArg (fun mu : Measure M ↦ mu A) (riemannianVolumeMeasure_map_restrictOpen g U)
  rw [Measure.map_apply hval.measurable hA, Measure.restrict_apply hA,
    inter_eq_left.mpr hAU] at hmap
  exact hmap

end DifferentialGeometry.Geometry.Measure

end
