import DifferentialGeometry.Geometry.Thurston.QuaternionHopfBaseSign_X127
import DifferentialGeometry.Topology.Ehresmann.CircleBundleTrivializationEFE
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.SphereProduct
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RawUniverseLift
import Mathlib.Topology.Bases

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Geometry GC.GraphManifold
open GC.Geometry.QuaternionAmbientHopfX127 GC.Geometry.QuaternionHopfBaseSignX127
open GC.Geometry.QuaternionProjectiveX127
open scoped Manifold ContDiff Topology

local notation "E4" => EuclideanSpace ℝ (Fin 4)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

attribute [local instance] uliftChartedSpace isManifold_ulift finrank_real_complex_fact'

local instance projectivePlaneFinrank_X127 :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

local instance sphereFourFinrank_X127 :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

local instance sphereCarrierCharts_X127 :
    ChartedSpace (EuclideanSpace ℝ (Fin 3)) SphereCarrier :=
  standardThreeSphereLift.charts

local instance sphereCarrierSmooth_X127 : IsManifold (𝓡 3) ∞ SphereCarrier :=
  standardThreeSphereLift.smooth

local instance projectivePlaneManifold_X127 :
    IsManifold (𝓡 2) ∞ RealProjectivePlane := inferInstance

local instance projectivePlaneSecondCountable_X127 :
    SecondCountableTopology RealProjectivePlane :=
  Topology.IsOpenQuotientMap.secondCountableTopology
    realProjectivePlaneQuotientMap_isOpenQuotientMap

noncomputable abbrev realProjectivePlaneSurface_X127 : CompactSurface.{0} where
  kind := .closed
  Carrier := RealProjectivePlane
  topology := inferInstance
  charts := inferInstance
  smooth := inferInstance
  hausdorff := inferInstance
  compact := inferInstance
  secondCountable := inferInstance
  connected := inferInstance

local instance projectivePlaneSurfaceChartedSpace_X127 :
    ChartedSpace (SurfaceModel.Space realProjectivePlaneSurface_X127.kind)
      RealProjectivePlane := realProjectivePlaneSurface_X127.charts

local instance projectivePlaneSurfaceManifold_X127 :
    IsManifold (SurfaceModel.model realProjectivePlaneSurface_X127.kind) ∞
      RealProjectivePlane := realProjectivePlaneSurface_X127.smooth

local instance projectivePlaneSurfaceBoundaryless_X127 :
    (SurfaceModel.model realProjectivePlaneSurface_X127.kind).Boundaryless := by
  change (𝓡 2).Boundaryless
  infer_instance

local instance projectivePlaneProductChartedSpace_X127
    (Q : TopologicalSpace.Opens RealProjectivePlane) :
    ChartedSpace
      (ModelProd (SurfaceModel.Space realProjectivePlaneSurface_X127.kind)
        (EuclideanSpace ℝ (Fin 1))) (Q × Circle) := by
  change ChartedSpace
    (ModelProd (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 1)))
    (Q × Circle)
  infer_instance

private theorem mfderiv_surjective_of_localDiffeomorph_X127
    {M N : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N]
    {f : M → N} (hf : IsLocalDiffeomorph (𝓡 3) (𝓡 2) ∞ f) (x : M) :
    Function.Surjective (mfderiv (𝓡 3) (𝓡 2) f x) :=
  (hf.mfderivToContinuousLinearEquiv (by simp) x).surjective

theorem hopfMap_mfderiv_surjective_X127 (x : SphereCarrier.{0}) :
    Function.Surjective (mfderiv (𝓡 3) (𝓡 2) hopfMap x) := by
  let b : SphereTwoLift.{0} := hopfMap x
  by_cases hb : sphereTwoHeight b = -1
  · have hb' : sphereTwoHeight b ≠ 1 := by rw [hb]; norm_num
    let w : Circle := unitOf (sphereSecond x)
    let q : hopfLower.{0} := ⟨b, hb'⟩
    let s : hopfLower.{0} → SphereCarrier.{0} := fun p => hopfLowerSection (p, w)
    have hs : ContMDiff (𝓡 2) (𝓡 3) ∞ s :=
      contMDiff_hopfLowerSection.comp (contMDiff_id.prodMk contMDiff_const)
    have hcomp : hopfMap ∘ s = (Subtype.val : hopfLower.{0} → SphereTwoLift.{0}) := by
      funext p
      exact hopfMap_hopfLowerSection (p, w)
    have hpoint : s q = x := (eq_hopfLowerPoint hb' rfl).symm
    have hlocal := DifferentialGeometry.isLocalDiffeomorph_subtype_val
      (I := 𝓡 2) hopfLower.{0}
    have hchain := mfderiv_comp q
      (contMDiff_hopfMap.mdifferentiableAt (by simp))
      (hs.mdifferentiableAt (by simp))
    rw [hcomp] at hchain
    rw [← hpoint]
    intro y
    obtain ⟨v, hv⟩ :=
      (hlocal.mfderivToContinuousLinearEquiv (by simp) q).surjective y
    refine ⟨mfderiv (𝓡 2) (𝓡 3) s q v, ?_⟩
    have hc := congrArg (fun L => L v) hchain
    change mfderiv (𝓡 2) (𝓡 2)
      (Subtype.val : hopfLower.{0} → SphereTwoLift.{0}) q v =
        mfderiv (𝓡 3) (𝓡 2) hopfMap (s q)
          (mfderiv (𝓡 2) (𝓡 3) s q v) at hc
    have hcoe := hlocal.mfderivToContinuousLinearEquiv_coe (by simp) q
    have hcoe_v : mfderiv (𝓡 2) (𝓡 2)
        (Subtype.val : hopfLower.{0} → SphereTwoLift.{0}) q v =
          (hlocal.mfderivToContinuousLinearEquiv (by simp) q) v :=
      (congrArg (fun L => L v) hcoe).symm
    have hv' : mfderiv (𝓡 2) (𝓡 2)
        (Subtype.val : hopfLower.{0} → SphereTwoLift.{0}) q v = y :=
      Eq.trans hcoe_v hv
    exact hc.symm.trans hv'
  · have hb' : sphereTwoHeight b ≠ -1 := hb
    let w : Circle := unitOf (sphereFirst x)
    let q : hopfUpper.{0} := ⟨b, hb'⟩
    let s : hopfUpper.{0} → SphereCarrier.{0} := fun p => hopfUpperSection (p, w)
    have hs : ContMDiff (𝓡 2) (𝓡 3) ∞ s :=
      contMDiff_hopfUpperSection.comp (contMDiff_id.prodMk contMDiff_const)
    have hcomp : hopfMap ∘ s = (Subtype.val : hopfUpper.{0} → SphereTwoLift.{0}) := by
      funext p
      exact hopfMap_hopfUpperSection (p, w)
    have hpoint : s q = x := (eq_hopfUpperPoint hb' rfl).symm
    have hlocal := DifferentialGeometry.isLocalDiffeomorph_subtype_val
      (I := 𝓡 2) hopfUpper.{0}
    have hchain := mfderiv_comp q
      (contMDiff_hopfMap.mdifferentiableAt (by simp))
      (hs.mdifferentiableAt (by simp))
    rw [hcomp] at hchain
    rw [← hpoint]
    intro y
    obtain ⟨v, hv⟩ :=
      (hlocal.mfderivToContinuousLinearEquiv (by simp) q).surjective y
    refine ⟨mfderiv (𝓡 2) (𝓡 3) s q v, ?_⟩
    have hc := congrArg (fun L => L v) hchain
    change mfderiv (𝓡 2) (𝓡 2)
      (Subtype.val : hopfUpper.{0} → SphereTwoLift.{0}) q v =
        mfderiv (𝓡 3) (𝓡 2) hopfMap (s q)
          (mfderiv (𝓡 2) (𝓡 3) s q v) at hc
    have hcoe := hlocal.mfderivToContinuousLinearEquiv_coe (by simp) q
    have hcoe_v : mfderiv (𝓡 2) (𝓡 2)
        (Subtype.val : hopfUpper.{0} → SphereTwoLift.{0}) q v =
          (hlocal.mfderivToContinuousLinearEquiv (by simp) q) v :=
      (congrArg (fun L => L v) hcoe).symm
    have hv' : mfderiv (𝓡 2) (𝓡 2)
        (Subtype.val : hopfUpper.{0} → SphereTwoLift.{0}) q v = y :=
      Eq.trans hcoe_v hv
    exact hc.symm.trans hv'


private theorem mfderiv_comp_surjective_X127
    {E F G H H' H'' M N P : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    {K : ModelWithCorners ℝ G H''}
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace H' N]
    [TopologicalSpace P] [ChartedSpace H'' P]
    {f : M → N} {g : N → P} (x : M)
    (hg : MDifferentiableAt J K g (f x)) (hf : MDifferentiableAt I J f x)
    (hdf : Function.Surjective (mfderiv I J f x))
    (hdg : Function.Surjective (mfderiv J K g (f x))) :
    Function.Surjective (mfderiv I K (g ∘ f) x) := by
  intro z
  obtain ⟨y, hy⟩ := hdg z
  obtain ⟨v, hv⟩ := hdf y
  refine ⟨v, ?_⟩
  rw [mfderiv_comp x hg hf]
  change mfderiv J K g (f x) (mfderiv I J f x v) = z
  rw [hv]
  exact hy

private theorem mfderiv_surjective_localDiffeomorph_X127
    {E F H H' M N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace H']
    {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H M]
    [TopologicalSpace N] [ChartedSpace H' N]
    {f : M → N} (hf : IsLocalDiffeomorph I J ∞ f) (x : M) :
    Function.Surjective (mfderiv I J f x) :=
  (hf.mfderivToContinuousLinearEquiv (by simp) x).surjective

private def q8HopfSourceDiffeomorph_X127 :
    Metric.sphere (0 : E4) 1 ≃ₘ⟮𝓡 3, 𝓡 3⟯ SphereCarrier.{0} :=
  (DifferentialGeometry.Geometry.sphereDiffeo (n := 3) conjugateAmbient_X127).trans
    standardThreeSphereLiftDiffeomorph.{0}

private def q8HopfLiftDownDiffeomorph_X127 :
    SphereTwoLift.{0} ≃ₘ⟮𝓡 2, 𝓡 2⟯ Metric.sphere (0 : E3) 1 :=
  (DifferentialGeometry.Topology.uliftDiffeomorph.{0, 0} (𝓡 2)
    (Metric.sphere (0 : E3) 1)).symm

theorem projectedHopf_mfderiv_surjective_X127
    (x : Metric.sphere (0 : E4) 1) :
    Function.Surjective (mfderiv (𝓡 3) (𝓡 2) projectedHopf_X127 x) := by
  let d := q8HopfSourceDiffeomorph_X127
  let e := q8HopfLiftDownDiffeomorph_X127
  let f₁ : Metric.sphere (0 : E4) 1 → SphereTwoLift.{0} :=
    fun z => hopfMap (d z)
  let f₂ : Metric.sphere (0 : E4) 1 → Metric.sphere (0 : E3) 1 :=
    fun z => e (f₁ z)
  let f₃ : Metric.sphere (0 : E4) 1 → RealProjectivePlane :=
    fun z => realProjectivePlaneQuotientMap (f₂ z)
  have hd : Function.Surjective (mfderiv (𝓡 3) (𝓡 3) d x) :=
    (d.mfderivToContinuousLinearEquiv (by simp) x).surjective
  have hh := hopfMap_mfderiv_surjective_X127 (d x)
  have hdHopf := mfderiv_comp_surjective_X127 (f := d) (g := hopfMap) x
    (contMDiff_hopfMap.mdifferentiableAt (by simp))
    (d.contMDiff.mdifferentiableAt (by simp)) hd hh
  have hf₁ : ContMDiff (𝓡 3) (𝓡 2) ∞ f₁ :=
    contMDiff_hopfMap.comp d.contMDiff
  have he : Function.Surjective
      (mfderiv (𝓡 2) (𝓡 2) e (f₁ x)) :=
    (e.mfderivToContinuousLinearEquiv (by simp) (f₁ x)).surjective
  have hdLift := mfderiv_comp_surjective_X127 (f := f₁) (g := e) x
    (e.contMDiff.mdifferentiableAt (by simp))
    (hf₁.mdifferentiableAt (by simp)) hdHopf he
  have hqLocal : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞
      realProjectivePlaneQuotientMap :=
    realProjectiveSpaceQuotientMap_isLocalDiffeomorph
  have hq := mfderiv_surjective_localDiffeomorph_X127 hqLocal (f₂ x)
  have hf₂ : ContMDiff (𝓡 3) (𝓡 2) ∞ f₂ :=
    e.contMDiff.comp hf₁
  have hfinal := mfderiv_comp_surjective_X127 (f := f₂)
    (g := realProjectivePlaneQuotientMap) x
    ((hqLocal (f₂ x)).mdifferentiableAt (by simp))
    (hf₂.mdifferentiableAt (by simp)) hdLift hq
  change Function.Surjective (mfderiv (𝓡 3) (𝓡 2) f₃ x)
  exact hfinal

theorem quaternionEightProjectedHopf_mfderiv_surjective_X127
    (x : Metric.sphere (0 : E4) 1) :
    Function.Surjective (mfderiv (𝓡 3) (𝓡 2)
      quaternionEightProjectedHopf_X127 (quaternionEightSpaceForm.projection x)) := by
  have hcomp : quaternionEightProjectedHopf_X127 ∘
      quaternionEightSpaceForm.projection = projectedHopf_X127 := by
    funext z
    exact quaternionEightProjectedHopf_projection_X127 z
  have hchain := mfderiv_comp x
    (quaternionEightProjectedHopf_smooth_X127.mdifferentiableAt (by simp))
    ((quaternionEightSpaceForm.projection_isLocalDiffeomorph x).mdifferentiableAt
      (by simp))
  rw [hcomp] at hchain
  intro y
  obtain ⟨v, hv⟩ := projectedHopf_mfderiv_surjective_X127 x y
  refine ⟨mfderiv (𝓡 3) (𝓡 3) quaternionEightSpaceForm.projection x v, ?_⟩
  have hc := congrArg (fun L => L v) hchain
  change mfderiv (𝓡 3) (𝓡 2) quaternionEightProjectedHopf_X127
      (quaternionEightSpaceForm.projection x)
      (mfderiv (𝓡 3) (𝓡 3) quaternionEightSpaceForm.projection x v) = y
  exact hc.symm.trans hv

theorem quaternionEightProjectedHopf_isProper_X127 :
    IsProperMap quaternionEightProjectedHopf_X127 := by
  have hcont := quaternionEightProjectedHopf_smooth_X127.continuous
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨hcont, ?_⟩
  intro K hK
  exact isCompact_univ.of_isClosed_subset (hK.isClosed.preimage hcont)
    (by intro x hx; exact Set.mem_univ x)


private theorem quaternionEightHopfMap_a1_flips_X127
    (x : Metric.sphere (0 : E4) 1) :
    ((hopfMap (q8HopfSourceDiffeomorph_X127
      (DifferentialGeometry.Geometry.sphereDiffeo (n := 3)
        (quaternionEightSpaceFormEquiv (.a 1)).val x))).down : E3) =
      -((hopfMap (q8HopfSourceDiffeomorph_X127 x)).down : E3) := by
  let q : QuaternionGroup 2 := .a 1
  have hnot : q ∉ quaternionHopfAxisStabilizer_X127 := by
    rw [quaternionEightHom_axisKernel_iff_X127]
    decide
  have hpoly : ambientHopf_X127 (conjugateAmbient_X127
      ((quaternionEightSpaceFormEquiv q).val (x : E4))) =
      -ambientHopf_X127 (conjugateAmbient_X127 (x : E4)) := by
    rcases quaternionEightAmbientHopf_axisSign_X127 q (x : E4) with h | h
    · exact (hnot h.1).elim
    · exact h.2
  change ((hopfMap (standardThreeSphereLiftDiffeomorph.{0}
      (DifferentialGeometry.Geometry.sphereDiffeo (n := 3) conjugateAmbient_X127
        (DifferentialGeometry.Geometry.sphereDiffeo (n := 3)
          (quaternionEightSpaceFormEquiv q).val x)))).down : E3) =
      -((hopfMap (standardThreeSphereLiftDiffeomorph.{0}
        (DifferentialGeometry.Geometry.sphereDiffeo (n := 3)
          conjugateAmbient_X127 x))).down : E3)
  rw [hopfMap_lift_ambient_X127, hopfMap_lift_ambient_X127]
  simpa only [DifferentialGeometry.Geometry.sphereDiffeo_coe] using hpoly

theorem quaternionEightProjectedHopf_fiber_connected_X127
    (y : quaternionEightSpaceForm.Orbit) :
    IsConnected {z | quaternionEightProjectedHopf_X127 z =
      quaternionEightProjectedHopf_X127 y} := by
  let d := q8HopfSourceDiffeomorph_X127
  obtain ⟨x₀, hx₀⟩ := quaternionEightSpaceForm.projection_surjective y
  let b : SphereTwoLift.{0} := hopfMap (d x₀)
  have hY : quaternionEightProjectedHopf_X127 y =
      realProjectivePlaneQuotientMap b.down := by
    calc
      quaternionEightProjectedHopf_X127 y =
          quaternionEightProjectedHopf_X127
            (quaternionEightSpaceForm.projection x₀) := congrArg
              quaternionEightProjectedHopf_X127 hx₀.symm
      _ = projectedHopf_X127 x₀ :=
        quaternionEightProjectedHopf_projection_X127 x₀
      _ = realProjectivePlaneQuotientMap b.down := rfl
  by_cases hb : sphereTwoHeight b = -1
  · have hb' : sphereTwoHeight b ≠ 1 := by rw [hb]; norm_num
    let q : hopfLower.{0} := ⟨b, hb'⟩
    let c : Circle → quaternionEightSpaceForm.Orbit := fun w =>
      quaternionEightSpaceForm.projection
        (d.symm (hopfLowerSection (q, w)))
    have hc : Continuous c := by
      dsimp [c]
      exact quaternionEightSpaceForm.projection_continuous.comp
        (d.symm.continuous.comp
          (contMDiff_hopfLowerSection.continuous.comp
            (continuous_const.prodMk continuous_id)))
    have hcurve : ∀ w, quaternionEightProjectedHopf_X127 (c w) =
        realProjectivePlaneQuotientMap b.down := by
      intro w
      change quaternionEightProjectedHopf_X127
        (quaternionEightSpaceForm.projection
          (d.symm (hopfLowerSection (q, w)))) = _
      rw [quaternionEightProjectedHopf_projection_X127]
      change realProjectivePlaneQuotientMap
        (hopfMap (d (d.symm (hopfLowerSection (q, w))))).down = _
      rw [d.apply_symm_apply]
      have hsecw : hopfMap (hopfLowerSection (q, w)) = b := by
        simpa [q] using hopfMap_hopfLowerSection (q, w)
      rw [hsecw]
    have hrange : Set.range c =
        {z | quaternionEightProjectedHopf_X127 z =
          quaternionEightProjectedHopf_X127 y} := by
      ext z
      constructor
      · rintro ⟨w, rfl⟩
        calc
          quaternionEightProjectedHopf_X127 (c w) =
              realProjectivePlaneQuotientMap b.down := hcurve w
          _ = quaternionEightProjectedHopf_X127 y := hY.symm
      · intro hz
        obtain ⟨x, hx⟩ := quaternionEightSpaceForm.projection_surjective z
        have hproj : realProjectivePlaneQuotientMap
            (hopfMap (d x)).down = realProjectivePlaneQuotientMap b.down := by
          calc
            realProjectivePlaneQuotientMap (hopfMap (d x)).down =
                quaternionEightProjectedHopf_X127
                  (quaternionEightSpaceForm.projection x) := by
                    rw [quaternionEightProjectedHopf_projection_X127]
                    rfl
            _ = quaternionEightProjectedHopf_X127 y := by rw [hx]; exact hz
            _ = realProjectivePlaneQuotientMap b.down := hY
        rcases realProjectivePlaneQuotientMap_eq_iff.mp hproj with
          hplus | hminus
        · have hbase : hopfMap (d x) = b := by
            apply ULift.ext
            apply Subtype.ext
            exact congrArg Subtype.val hplus
          let w : Circle := unitOf (sphereSecond (d x))
          have hpoint := eq_hopfLowerPoint hb' hbase
          have hraw : x = d.symm (hopfLowerSection (q, w)) := by
            calc
              x = d.symm (d x) := (d.symm_apply_apply x).symm
              _ = d.symm (hopfLowerSection (q, w)) := by
                have hpoint' : d x = hopfLowerSection (q, w) := by
                  simpa [q, w, hopfLowerSection] using hpoint
                exact congrArg d.symm hpoint'
          refine ⟨w, ?_⟩
          dsimp [c]
          calc
            quaternionEightSpaceForm.projection
                (d.symm (hopfLowerSection (q, w))) =
                quaternionEightSpaceForm.projection x :=
                  (congrArg quaternionEightSpaceForm.projection hraw).symm
            _ = z := hx
        · let q₁ : QuaternionGroup 2 := .a 1
          let γ := quaternionEightSpaceFormEquiv q₁
          let x₁ := DifferentialGeometry.Geometry.sphereDiffeo
            (n := 3) γ.val x
          have hπ : quaternionEightSpaceForm.projection x₁ = z := by
            calc
              quaternionEightSpaceForm.projection x₁ =
                  quaternionEightSpaceForm.projection x :=
                    quaternionEightSpaceForm.projection_invariant γ x
              _ = z := hx
          have hbase : hopfMap (d x₁) = b := by
            apply ULift.ext
            apply Subtype.ext
            calc
              ((hopfMap (d x₁)).down : E3) =
                  -((hopfMap (d x)).down : E3) := by
                    simpa [x₁, γ, d, q8HopfSourceDiffeomorph_X127] using
                      quaternionEightHopfMap_a1_flips_X127 x
              _ = -(-(b.down : E3)) := by rw [hminus]
              _ = b.down := by simp
          let w : Circle := unitOf (sphereSecond (d x₁))
          have hpoint := eq_hopfLowerPoint hb' hbase
          have hraw : x₁ = d.symm (hopfLowerSection (q, w)) := by
            calc
              x₁ = d.symm (d x₁) := (d.symm_apply_apply x₁).symm
              _ = d.symm (hopfLowerSection (q, w)) := by
                have hpoint' : d x₁ = hopfLowerSection (q, w) := by
                  simpa [q, w, hopfLowerSection] using hpoint
                exact congrArg d.symm hpoint'
          refine ⟨w, ?_⟩
          dsimp [c]
          calc
            quaternionEightSpaceForm.projection
                (d.symm (hopfLowerSection (q, w))) =
                quaternionEightSpaceForm.projection x₁ :=
                  (congrArg quaternionEightSpaceForm.projection hraw).symm
            _ = z := hπ
    have hconn : IsConnected (Set.range c) := by
      simpa only [Set.image_univ] using
        (isConnected_univ : IsConnected (Set.univ : Set Circle)).image c
          hc.continuousOn
    rw [← hrange]
    exact hconn
  · have hb' : sphereTwoHeight b ≠ -1 := hb
    let q : hopfUpper.{0} := ⟨b, hb'⟩
    let c : Circle → quaternionEightSpaceForm.Orbit := fun w =>
      quaternionEightSpaceForm.projection
        (d.symm (hopfUpperSection (q, w)))
    have hc : Continuous c := by
      dsimp [c]
      exact quaternionEightSpaceForm.projection_continuous.comp
        (d.symm.continuous.comp
          (contMDiff_hopfUpperSection.continuous.comp
            (continuous_const.prodMk continuous_id)))
    have hcurve : ∀ w, quaternionEightProjectedHopf_X127 (c w) =
        realProjectivePlaneQuotientMap b.down := by
      intro w
      change quaternionEightProjectedHopf_X127
        (quaternionEightSpaceForm.projection
          (d.symm (hopfUpperSection (q, w)))) = _
      rw [quaternionEightProjectedHopf_projection_X127]
      change realProjectivePlaneQuotientMap
        (hopfMap (d (d.symm (hopfUpperSection (q, w))))).down = _
      rw [d.apply_symm_apply]
      have hsecw : hopfMap (hopfUpperSection (q, w)) = b := by
        simpa [q] using hopfMap_hopfUpperSection (q, w)
      rw [hsecw]
    have hrange : Set.range c =
        {z | quaternionEightProjectedHopf_X127 z =
          quaternionEightProjectedHopf_X127 y} := by
      ext z
      constructor
      · rintro ⟨w, rfl⟩
        calc
          quaternionEightProjectedHopf_X127 (c w) =
              realProjectivePlaneQuotientMap b.down := hcurve w
          _ = quaternionEightProjectedHopf_X127 y := hY.symm
      · intro hz
        obtain ⟨x, hx⟩ := quaternionEightSpaceForm.projection_surjective z
        have hproj : realProjectivePlaneQuotientMap
            (hopfMap (d x)).down = realProjectivePlaneQuotientMap b.down := by
          calc
            realProjectivePlaneQuotientMap (hopfMap (d x)).down =
                quaternionEightProjectedHopf_X127
                  (quaternionEightSpaceForm.projection x) := by
                    rw [quaternionEightProjectedHopf_projection_X127]
                    rfl
            _ = quaternionEightProjectedHopf_X127 y := by rw [hx]; exact hz
            _ = realProjectivePlaneQuotientMap b.down := hY
        rcases realProjectivePlaneQuotientMap_eq_iff.mp hproj with
          hplus | hminus
        · have hbase : hopfMap (d x) = b := by
            apply ULift.ext
            apply Subtype.ext
            exact congrArg Subtype.val hplus
          let w : Circle := unitOf (sphereFirst (d x))
          have hpoint := eq_hopfUpperPoint hb' hbase
          have hraw : x = d.symm (hopfUpperSection (q, w)) := by
            calc
              x = d.symm (d x) := (d.symm_apply_apply x).symm
              _ = d.symm (hopfUpperSection (q, w)) := by
                have hpoint' : d x = hopfUpperSection (q, w) := by
                  simpa [q, w, hopfUpperSection] using hpoint
                exact congrArg d.symm hpoint'
          refine ⟨w, ?_⟩
          dsimp [c]
          calc
            quaternionEightSpaceForm.projection
                (d.symm (hopfUpperSection (q, w))) =
                quaternionEightSpaceForm.projection x :=
                  (congrArg quaternionEightSpaceForm.projection hraw).symm
            _ = z := hx
        · let q₁ : QuaternionGroup 2 := .a 1
          let γ := quaternionEightSpaceFormEquiv q₁
          let x₁ := DifferentialGeometry.Geometry.sphereDiffeo
            (n := 3) γ.val x
          have hπ : quaternionEightSpaceForm.projection x₁ = z := by
            calc
              quaternionEightSpaceForm.projection x₁ =
                  quaternionEightSpaceForm.projection x :=
                    quaternionEightSpaceForm.projection_invariant γ x
              _ = z := hx
          have hbase : hopfMap (d x₁) = b := by
            apply ULift.ext
            apply Subtype.ext
            calc
              ((hopfMap (d x₁)).down : E3) =
                  -((hopfMap (d x)).down : E3) := by
                    simpa [x₁, γ, d, q8HopfSourceDiffeomorph_X127] using
                      quaternionEightHopfMap_a1_flips_X127 x
              _ = -(-(b.down : E3)) := by rw [hminus]
              _ = b.down := by simp
          let w : Circle := unitOf (sphereFirst (d x₁))
          have hpoint := eq_hopfUpperPoint hb' hbase
          have hraw : x₁ = d.symm (hopfUpperSection (q, w)) := by
            calc
              x₁ = d.symm (d x₁) := (d.symm_apply_apply x₁).symm
              _ = d.symm (hopfUpperSection (q, w)) := by
                have hpoint' : d x₁ = hopfUpperSection (q, w) := by
                  simpa [q, w, hopfUpperSection] using hpoint
                exact congrArg d.symm hpoint'
          refine ⟨w, ?_⟩
          dsimp [c]
          calc
            quaternionEightSpaceForm.projection
                (d.symm (hopfUpperSection (q, w))) =
                quaternionEightSpaceForm.projection x₁ :=
                  (congrArg quaternionEightSpaceForm.projection hraw).symm
            _ = z := hπ
    have hconn : IsConnected (Set.range c) := by
      simpa only [Set.image_univ] using
        (isConnected_univ : IsConnected (Set.univ : Set Circle)).image c
          hc.continuousOn
    rw [← hrange]
    exact hconn


theorem quaternionEightProjectedHopf_mfderiv_surjective_all_X127
    (x : quaternionEightSpaceForm.Orbit) :
    Function.Surjective (mfderiv (𝓡 3) (𝓡 2)
      quaternionEightProjectedHopf_X127 x) := by
  obtain ⟨z, rfl⟩ := quaternionEightSpaceForm.projection_surjective x
  exact quaternionEightProjectedHopf_mfderiv_surjective_X127 z


private def quaternionEightProjectedHopfTopMap_X127 :
    C((⊤ : TopologicalSpace.Opens quaternionEightSpaceForm.Orbit),
      RealProjectivePlane) :=
  ⟨fun x => quaternionEightProjectedHopf_X127 x.val,
    quaternionEightProjectedHopf_smooth_X127.continuous.comp
      continuous_subtype_val⟩

private abbrev quaternionEightProjectedHopfFullPreimage_X127
    (Q : TopologicalSpace.Opens RealProjectivePlane) :
    TopologicalSpace.Opens quaternionEightSpaceForm.Orbit :=
  ⟨quaternionEightProjectedHopf_X127 ⁻¹' Q,
    Q.isOpen.preimage quaternionEightProjectedHopf_smooth_X127.continuous⟩

private def quaternionEightProjectedHopfOpenTransport_X127
    (Q : TopologicalSpace.Opens RealProjectivePlane) :
    TopologicalSpace.Opens.comap quaternionEightProjectedHopfTopMap_X127 Q ≃ₘ⟮
      𝓡 3, 𝓡 3⟯ quaternionEightProjectedHopfFullPreimage_X127 Q where
  toEquiv :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      invFun := fun x => ⟨⟨x.val, by simp⟩, x.property⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun x => by ext; rfl }
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff
      (quaternionEightProjectedHopfFullPreimage_X127 Q) _).mp
    change ContMDiff (𝓡 3) (𝓡 3) ∞
      ((Subtype.val : (⊤ : TopologicalSpace.Opens
        quaternionEightSpaceForm.Orbit) → quaternionEightSpaceForm.Orbit) ∘
        (Subtype.val : TopologicalSpace.Opens.comap
          quaternionEightProjectedHopfTopMap_X127 Q →
          (⊤ : TopologicalSpace.Opens quaternionEightSpaceForm.Orbit)))
    exact contMDiff_subtype_val.comp contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff
      (TopologicalSpace.Opens.comap quaternionEightProjectedHopfTopMap_X127 Q) _).mp
    apply (ContMDiff.subtypeVal_comp_iff
      (⊤ : TopologicalSpace.Opens quaternionEightSpaceForm.Orbit) _).mp
    exact contMDiff_subtype_val

noncomputable def quaternionEightHopfCircleFibration_X127 :
    CircleFibration (NoCuts.carrier quaternionEightSpaceForm.manifold) ⊤ := by
  let f := quaternionEightProjectedHopf_X127
  letI : ChartedSpace (SurfaceModel.Space realProjectivePlaneSurface_X127.kind)
      RealProjectivePlane := realProjectivePlaneSurface_X127.charts
  letI : IsManifold (SurfaceModel.model realProjectivePlaneSurface_X127.kind) ∞
      RealProjectivePlane := by
    change IsManifold (𝓡 2) ∞ RealProjectivePlane
    exact projectivePlaneManifold_X127
  letI : (SurfaceModel.model realProjectivePlaneSurface_X127.kind).Boundaryless :=
    projectivePlaneSurfaceBoundaryless_X127
  have hlocal : ∀ y : RealProjectivePlane,
      ∃ Q : TopologicalSpace.Opens RealProjectivePlane, y ∈ Q ∧
        ∃ Ψ : Diffeomorph (𝓡 3)
          ((SurfaceModel.model realProjectivePlaneSurface_X127.kind).prod (𝓡 1))
          (⟨f ⁻¹' Q, Q.isOpen.preimage
            quaternionEightProjectedHopf_smooth_X127.continuous⟩ :
              TopologicalSpace.Opens quaternionEightSpaceForm.Orbit)
          (Q × Circle) ∞,
          ∀ x, (Ψ x).1.1 = f x := by
    intro y
    exact DifferentialGeometry.Topology.Ehresmann.exists_circle_trivialization_of_proper_submersion_EFE
      (J := SurfaceModel.model realProjectivePlaneSurface_X127.kind)
      f quaternionEightProjectedHopf_smooth_X127
      quaternionEightProjectedHopf_isProper_X127
      quaternionEightProjectedHopf_mfderiv_surjective_all_X127
      (by simp)
      (fun y => by
        obtain ⟨x, hx⟩ := quaternionEightProjectedHopf_surjective_X127 y
        simpa [hx] using quaternionEightProjectedHopf_fiber_connected_X127 x)
      y
  choose Q hQ Ψ hΨ using hlocal
  exact
    { base := realProjectivePlaneSurface_X127
      projection := quaternionEightProjectedHopfTopMap_X127
      surjective := by
        intro y
        obtain ⟨x, hx⟩ := quaternionEightProjectedHopf_surjective_X127 y
        exact ⟨⟨x, Set.mem_univ x⟩, hx⟩
      smooth := quaternionEightProjectedHopf_smooth_X127.comp
        contMDiff_subtype_val
      neighborhood := Q
      mem_neighborhood := hQ
      trivialization := fun y => by
        letI : ChartedSpace
            (ModelProd (SurfaceModel.Space realProjectivePlaneSurface_X127.kind)
              (EuclideanSpace ℝ (Fin 1))) (Q y × Circle) :=
          projectivePlaneProductChartedSpace_X127 (Q y)
        exact (quaternionEightProjectedHopfOpenTransport_X127 (Q y)).trans (Ψ y)
      projection_trivialization := by
        intro y x
        exact hΨ y (quaternionEightProjectedHopfOpenTransport_X127 (Q y) x) }

noncomputable def quaternionEightHopfRawPresentation_X127 :
    RawGraphPresentation (NoCuts.carrier quaternionEightSpaceForm.manifold) :=
  RawGraphPresentation.ofClosedCircleFibration quaternionEightSpaceForm.manifold
    quaternionEightHopfCircleFibration_X127

universe u

theorem quaternionEightHopfRawPresentation_ulift_X127 :
    Nonempty (RawGraphPresentation (NoCuts.carrier
      quaternionEightSpaceForm.manifold.ulift.{0, u})) :=
  RawUniverseLift.nonempty_rawGraphPresentation_ulift
    quaternionEightSpaceForm.manifold quaternionEightHopfRawPresentation_X127

end
