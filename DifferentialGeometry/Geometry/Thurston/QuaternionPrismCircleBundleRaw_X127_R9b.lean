import DifferentialGeometry.Geometry.Thurston.QuaternionPrismActions_X127_R17b
import DifferentialGeometry.Geometry.Thurston.QuaternionPrismAxisSign_X127_R3b
import DifferentialGeometry.Geometry.Thurston.QuaternionPrismHopfRotate_X127_R4b
import DifferentialGeometry.Geometry.Thurston.QuaternionPrismHopfInvariance_X127_R3b
import DifferentialGeometry.Geometry.Thurston.QuaternionPrismQuotientAction_X127_R2b
import DifferentialGeometry.Geometry.Thurston.QuaternionQ8CircleBundleRaw_X127
import DifferentialGeometry.Topology.Ehresmann.CircleBundleTrivializationEFE
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.SphereProduct
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.RawUniverseLift
import Mathlib.Topology.Bases
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Geometry GC.GraphManifold
open GC.Geometry.QuaternionPrismX127R3
open GC.Geometry.QuaternionPrismAxisSignX127
open GC.Geometry.QuaternionPrismHopfRotateX127
open GC.Geometry.QuaternionPrismHopfInvarianceX127
open GC.Geometry.QuaternionPrismQuotientActionX127
open GC.Geometry.QuaternionProjectiveX127
open GC.Geometry.QuaternionAmbientHopfX127
open scoped Manifold ContDiff Topology

attribute [local instance] uliftChartedSpace isManifold_ulift finrank_real_complex_fact'

attribute [local instance] projectivePlaneFinrank_X127 sphereFourFinrank_X127

namespace GC.Geometry.QuaternionPrismCircleBundleRawX127

local notation "E4" => EuclideanSpace ℝ (Fin 4)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

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

noncomputable def prismHopfSourceDiffeomorph_X127 :
    Metric.sphere (0 : E4) 1 ≃ₘ⟮𝓡 3, 𝓡 3⟯ SphereCarrier.{0} :=
  (DifferentialGeometry.Geometry.sphereDiffeo (n := 3) rotateAmbient_X127).trans
    ((DifferentialGeometry.Geometry.sphereDiffeo (n := 3) conjugateAmbient_X127).trans
      standardThreeSphereLiftDiffeomorph.{0})

def prismProjectedHopf_X127 (n : ℕ) [NeZero n] :
    (spaceForm_X127 n).Orbit → RealProjectivePlane :=
  Quotient.lift prismProjectedHopfCover_X127 (by
    intro x y hxy
    have hp : (spaceForm_X127 n).projection x =
        (spaceForm_X127 n).projection y := Quotient.sound hxy
    obtain ⟨γ, hγ⟩ := ((spaceForm_X127 n).projection_eq_iff x y).mp hp
    obtain ⟨q, hq⟩ := prismQuotientGroupMap_surjective_X127 n γ
    rw [← hγ, ← hq, prismQuotientGroupMap_action_X127]
    exact (prismProjectedHopfCover_invariant_X127 n q x).symm)

theorem prismProjectedHopf_projection_X127 (n : ℕ) [NeZero n]
    (x : Metric.sphere (0 : E4) 1) :
    prismProjectedHopf_X127 n ((spaceForm_X127 n).projection x) =
      prismProjectedHopfCover_X127 x := rfl

theorem prismProjectedHopf_smooth_X127 (n : ℕ) [NeZero n] :
    ContMDiff (𝓡 3) (𝓡 2) ∞ (prismProjectedHopf_X127 n) := by
  apply IsLocalDiffeomorph.contMDiff_of_comp_of_surjective
    (spaceForm_X127 n).projection_isLocalDiffeomorph
    (spaceForm_X127 n).projection_surjective ?_
  have hfactor : prismProjectedHopf_X127 n ∘ (spaceForm_X127 n).projection =
      prismProjectedHopfCover_X127 := by
    funext x
    exact prismProjectedHopf_projection_X127 n x
  rw [hfactor]
  change ContMDiff (𝓡 3) (𝓡 2) ∞
    (projectedHopf_X127 ∘
      (DifferentialGeometry.Geometry.sphereDiffeo (n := 3) rotateAmbient_X127))
  exact projectedHopf_smooth_X127.comp
    (DifferentialGeometry.Geometry.sphereDiffeo (n := 3)
      rotateAmbient_X127).contMDiff

theorem prismProjectedHopf_surjective_X127 (n : ℕ) [NeZero n] :
    Function.Surjective (prismProjectedHopf_X127 n) := by
  intro b
  let d := DifferentialGeometry.Geometry.sphereDiffeo (n := 3) rotateAmbient_X127
  obtain ⟨x, hx⟩ := projectedHopf_surjective_X127 b
  refine ⟨(spaceForm_X127 n).projection (d.symm x), ?_⟩
  rw [prismProjectedHopf_projection_X127]
  change projectedHopf_X127 (d (d.symm x)) = b
  rw [d.apply_symm_apply]
  exact hx

theorem prismProjectedHopfCover_mfderiv_surjective_X127
    (x : Metric.sphere (0 : E4) 1) :
    Function.Surjective (mfderiv (𝓡 3) (𝓡 2)
      prismProjectedHopfCover_X127 x) := by
  let d := DifferentialGeometry.Geometry.sphereDiffeo (n := 3) rotateAmbient_X127
  have h := mfderiv_comp_surjective_X127 (f := d)
    (g := projectedHopf_X127) x
    (projectedHopf_smooth_X127.mdifferentiableAt (by simp))
    (d.contMDiff.mdifferentiableAt (by simp))
    ((d.mfderivToContinuousLinearEquiv (by simp) x).surjective)
    (projectedHopf_mfderiv_surjective_X127 (d x))
  change Function.Surjective (mfderiv (𝓡 3) (𝓡 2)
    (projectedHopf_X127 ∘
      (DifferentialGeometry.Geometry.sphereDiffeo (n := 3) rotateAmbient_X127)) x)
  exact h

theorem prismProjectedHopf_mfderiv_surjective_X127 (n : ℕ) [NeZero n]
    (x : (spaceForm_X127 n).Orbit) :
    Function.Surjective (mfderiv (𝓡 3) (𝓡 2) (prismProjectedHopf_X127 n) x) := by
  obtain ⟨z, rfl⟩ := (spaceForm_X127 n).projection_surjective x
  have hfactor : prismProjectedHopf_X127 n ∘ (spaceForm_X127 n).projection =
      prismProjectedHopfCover_X127 := by
    funext y
    exact prismProjectedHopf_projection_X127 n y
  have hchain := mfderiv_comp z
    ((prismProjectedHopf_smooth_X127 n).mdifferentiableAt (by simp))
    (((spaceForm_X127 n).projection_isLocalDiffeomorph z).mdifferentiableAt (by simp))
  rw [hfactor] at hchain
  intro y
  obtain ⟨v, hv⟩ := prismProjectedHopfCover_mfderiv_surjective_X127 z y
  refine ⟨mfderiv (𝓡 3) (𝓡 3) (spaceForm_X127 n).projection z v, ?_⟩
  have hc := congrArg (fun L => L v) hchain
  change mfderiv (𝓡 3) (𝓡 2) (prismProjectedHopf_X127 n)
      ((spaceForm_X127 n).projection z)
      (mfderiv (𝓡 3) (𝓡 3) (spaceForm_X127 n).projection z v) = y
  exact hc.symm.trans hv

theorem prismProjectedHopf_isProper_X127 (n : ℕ) [NeZero n] :
    IsProperMap (prismProjectedHopf_X127 n) := by
  have hcont := (prismProjectedHopf_smooth_X127 n).continuous
  apply isProperMap_iff_isCompact_preimage.mpr
  refine ⟨hcont, ?_⟩
  intro K hK
  exact isCompact_univ.of_isClosed_subset (hK.isClosed.preimage hcont)
    (by intro x hx; exact Set.mem_univ x)



theorem prismHopfMap_flip_X127 (n : ℕ) [NeZero n]
    (x : Metric.sphere (0 : E4) 1) :
    ((hopfMap (prismHopfSourceDiffeomorph_X127
      (DifferentialGeometry.Geometry.sphereDiffeo (n := 3)
        (prismQuotientGroupMap_X127 n (.xa 0)).val x))).down : E3) =
      -((hopfMap (prismHopfSourceDiffeomorph_X127 x)).down : E3) := by
  let qflip : QuaternionGroup n := .xa 0
  let γ := prismQuotientGroupMap_X127 n qflip
  have hsign : star (value_X127 n qflip : Quaternion ℝ) * axisI_X127 *
      (value_X127 n qflip : Quaternion ℝ) = -axisI_X127 := by
    simpa [qflip, value_X127, characterQ_zero_X127] using j_flips_axisI_X127
  have hact : s3Quat
      ((DifferentialGeometry.Geometry.sphereDiffeo (n := 3) γ.val x :
        Metric.sphere (0 : E4) 1)) =
      (value_X127 n qflip : Quaternion ℝ) * s3Quat x := by
    change s3Quat (γ.val (x : E4)) = _
    rw [prismQuotientGroupMap_action_X127]
    exact quaternionLeftHom_apply (value_X127 n qflip) (x : E4)
  have hq : star ((value_X127 n qflip : Quaternion ℝ) * s3Quat x) *
      axisI_X127 * ((value_X127 n qflip : Quaternion ℝ) * s3Quat x) =
        -(star (s3Quat x) * axisI_X127 * s3Quat x) := by
    calc
      star ((value_X127 n qflip : Quaternion ℝ) * s3Quat x) *
          axisI_X127 * ((value_X127 n qflip : Quaternion ℝ) * s3Quat x) =
        star (s3Quat x) *
          (star (value_X127 n qflip : Quaternion ℝ) * axisI_X127 *
            (value_X127 n qflip : Quaternion ℝ)) * s3Quat x := by
              rw [star_mul]
              noncomm_ring
      _ = star (s3Quat x) * (-axisI_X127) * s3Quat x := by rw [hsign]
      _ = -(star (s3Quat x) * axisI_X127 * s3Quat x) := by noncomm_ring
  have hbase : axisBase_X127
      ((value_X127 n qflip : Quaternion ℝ) * s3Quat x) =
        -axisBase_X127 (s3Quat x) := by
    calc
      axisBase_X127 ((value_X127 n qflip : Quaternion ℝ) * s3Quat x) =
          imaginaryVector_X127
            (star ((value_X127 n qflip : Quaternion ℝ) * s3Quat x) *
              axisI_X127 * ((value_X127 n qflip : Quaternion ℝ) * s3Quat x)) := rfl
      _ = imaginaryVector_X127 (-(star (s3Quat x) * axisI_X127 * s3Quat x)) :=
        congrArg imaginaryVector_X127 hq
      _ = -axisBase_X127 (s3Quat x) := imaginaryVector_neg_X127 _
  calc
    ((hopfMap (prismHopfSourceDiffeomorph_X127
      (DifferentialGeometry.Geometry.sphereDiffeo (n := 3) γ.val x))).down : E3) =
        axisBase_X127 (s3Quat
          (DifferentialGeometry.Geometry.sphereDiffeo (n := 3) γ.val x)) := by
      change ((hopfMap (standardThreeSphereLiftDiffeomorph.{0}
        (DifferentialGeometry.Geometry.sphereDiffeo (n := 3) conjugateAmbient_X127
          (DifferentialGeometry.Geometry.sphereDiffeo (n := 3) rotateAmbient_X127
            (DifferentialGeometry.Geometry.sphereDiffeo (n := 3) γ.val x))))).down : E3) = _
      exact rotatedHopfVector_X127 _
    _ = -axisBase_X127 (s3Quat x) := by rw [hact]; exact hbase
    _ = -((hopfMap (prismHopfSourceDiffeomorph_X127 x)).down : E3) := by
      change -axisBase_X127 (s3Quat x) =
        -((hopfMap (standardThreeSphereLiftDiffeomorph.{0}
          (DifferentialGeometry.Geometry.sphereDiffeo (n := 3) conjugateAmbient_X127
            (DifferentialGeometry.Geometry.sphereDiffeo (n := 3) rotateAmbient_X127 x)))).down : E3)
      rw [rotatedHopfVector_X127 x]

theorem prismProjectedHopf_fiber_connected_X127 (n : ℕ) [NeZero n]
    (y : (spaceForm_X127 n).Orbit) :
    IsConnected {z | prismProjectedHopf_X127 n z =
      prismProjectedHopf_X127 n y} := by
  let d := prismHopfSourceDiffeomorph_X127
  obtain ⟨x₀, hx₀⟩ := (spaceForm_X127 n).projection_surjective y
  let b : SphereTwoLift.{0} := hopfMap (d x₀)
  have hY : prismProjectedHopf_X127 n y =
      realProjectivePlaneQuotientMap b.down := by
    calc
      prismProjectedHopf_X127 n y =
          prismProjectedHopf_X127 n
            ((spaceForm_X127 n).projection x₀) := congrArg (prismProjectedHopf_X127 n) hx₀.symm
      _ = prismProjectedHopfCover_X127 x₀ :=
        prismProjectedHopf_projection_X127 n x₀
      _ = realProjectivePlaneQuotientMap b.down := rfl
  by_cases hb : sphereTwoHeight b = -1
  · have hb' : sphereTwoHeight b ≠ 1 := by rw [hb]; norm_num
    let q : hopfLower.{0} := ⟨b, hb'⟩
    let c : Circle → (spaceForm_X127 n).Orbit := fun w =>
      (spaceForm_X127 n).projection
        (d.symm (hopfLowerSection (q, w)))
    have hc : Continuous c := by
      dsimp [c]
      exact (spaceForm_X127 n).projection_continuous.comp
        (d.symm.continuous.comp
          (contMDiff_hopfLowerSection.continuous.comp
            (continuous_const.prodMk continuous_id)))
    have hcurve : ∀ w, prismProjectedHopf_X127 n (c w) =
        realProjectivePlaneQuotientMap b.down := by
      intro w
      change prismProjectedHopf_X127 n
        ((spaceForm_X127 n).projection
          (d.symm (hopfLowerSection (q, w)))) = _
      rw [prismProjectedHopf_projection_X127 n]
      change realProjectivePlaneQuotientMap
        (hopfMap (d (d.symm (hopfLowerSection (q, w))))).down = _
      rw [d.apply_symm_apply]
      have hsecw : hopfMap (hopfLowerSection (q, w)) = b := by
        simpa [q] using hopfMap_hopfLowerSection (q, w)
      rw [hsecw]
    have hrange : Set.range c =
        {z | prismProjectedHopf_X127 n z =
          prismProjectedHopf_X127 n y} := by
      ext z
      constructor
      · rintro ⟨w, rfl⟩
        calc
          prismProjectedHopf_X127 n (c w) =
              realProjectivePlaneQuotientMap b.down := hcurve w
          _ = prismProjectedHopf_X127 n y := hY.symm
      · intro hz
        obtain ⟨x, hx⟩ := (spaceForm_X127 n).projection_surjective z
        have hproj : realProjectivePlaneQuotientMap
            (hopfMap (d x)).down = realProjectivePlaneQuotientMap b.down := by
          calc
            realProjectivePlaneQuotientMap (hopfMap (d x)).down =
                prismProjectedHopf_X127 n
                  ((spaceForm_X127 n).projection x) := by
                    rw [prismProjectedHopf_projection_X127 n]
                    rfl
            _ = prismProjectedHopf_X127 n y := by rw [hx]; exact hz
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
            (spaceForm_X127 n).projection
                (d.symm (hopfLowerSection (q, w))) =
                (spaceForm_X127 n).projection x :=
                  (congrArg (spaceForm_X127 n).projection hraw).symm
            _ = z := hx
        · let q₁ : QuaternionGroup n := .xa 0
          let γ := prismQuotientGroupMap_X127 n q₁
          let x₁ := DifferentialGeometry.Geometry.sphereDiffeo
            (n := 3) γ.val x
          have hπ : (spaceForm_X127 n).projection x₁ = z := by
            calc
              (spaceForm_X127 n).projection x₁ =
                  (spaceForm_X127 n).projection x :=
                    (spaceForm_X127 n).projection_invariant γ x
              _ = z := hx
          have hbase : hopfMap (d x₁) = b := by
            apply ULift.ext
            apply Subtype.ext
            calc
              ((hopfMap (d x₁)).down : E3) =
                  -((hopfMap (d x)).down : E3) := by
                    simpa [x₁, γ, d, prismHopfSourceDiffeomorph_X127] using
                      prismHopfMap_flip_X127 n x
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
            (spaceForm_X127 n).projection
                (d.symm (hopfLowerSection (q, w))) =
                (spaceForm_X127 n).projection x₁ :=
                  (congrArg (spaceForm_X127 n).projection hraw).symm
            _ = z := hπ
    have hconn : IsConnected (Set.range c) := by
      simpa only [Set.image_univ] using
        (isConnected_univ : IsConnected (Set.univ : Set Circle)).image c
          hc.continuousOn
    rw [← hrange]
    exact hconn
  · have hb' : sphereTwoHeight b ≠ -1 := hb
    let q : hopfUpper.{0} := ⟨b, hb'⟩
    let c : Circle → (spaceForm_X127 n).Orbit := fun w =>
      (spaceForm_X127 n).projection
        (d.symm (hopfUpperSection (q, w)))
    have hc : Continuous c := by
      dsimp [c]
      exact (spaceForm_X127 n).projection_continuous.comp
        (d.symm.continuous.comp
          (contMDiff_hopfUpperSection.continuous.comp
            (continuous_const.prodMk continuous_id)))
    have hcurve : ∀ w, prismProjectedHopf_X127 n (c w) =
        realProjectivePlaneQuotientMap b.down := by
      intro w
      change prismProjectedHopf_X127 n
        ((spaceForm_X127 n).projection
          (d.symm (hopfUpperSection (q, w)))) = _
      rw [prismProjectedHopf_projection_X127 n]
      change realProjectivePlaneQuotientMap
        (hopfMap (d (d.symm (hopfUpperSection (q, w))))).down = _
      rw [d.apply_symm_apply]
      have hsecw : hopfMap (hopfUpperSection (q, w)) = b := by
        simpa [q] using hopfMap_hopfUpperSection (q, w)
      rw [hsecw]
    have hrange : Set.range c =
        {z | prismProjectedHopf_X127 n z =
          prismProjectedHopf_X127 n y} := by
      ext z
      constructor
      · rintro ⟨w, rfl⟩
        calc
          prismProjectedHopf_X127 n (c w) =
              realProjectivePlaneQuotientMap b.down := hcurve w
          _ = prismProjectedHopf_X127 n y := hY.symm
      · intro hz
        obtain ⟨x, hx⟩ := (spaceForm_X127 n).projection_surjective z
        have hproj : realProjectivePlaneQuotientMap
            (hopfMap (d x)).down = realProjectivePlaneQuotientMap b.down := by
          calc
            realProjectivePlaneQuotientMap (hopfMap (d x)).down =
                prismProjectedHopf_X127 n
                  ((spaceForm_X127 n).projection x) := by
                    rw [prismProjectedHopf_projection_X127 n]
                    rfl
            _ = prismProjectedHopf_X127 n y := by rw [hx]; exact hz
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
            (spaceForm_X127 n).projection
                (d.symm (hopfUpperSection (q, w))) =
                (spaceForm_X127 n).projection x :=
                  (congrArg (spaceForm_X127 n).projection hraw).symm
            _ = z := hx
        · let q₁ : QuaternionGroup n := .xa 0
          let γ := prismQuotientGroupMap_X127 n q₁
          let x₁ := DifferentialGeometry.Geometry.sphereDiffeo
            (n := 3) γ.val x
          have hπ : (spaceForm_X127 n).projection x₁ = z := by
            calc
              (spaceForm_X127 n).projection x₁ =
                  (spaceForm_X127 n).projection x :=
                    (spaceForm_X127 n).projection_invariant γ x
              _ = z := hx
          have hbase : hopfMap (d x₁) = b := by
            apply ULift.ext
            apply Subtype.ext
            calc
              ((hopfMap (d x₁)).down : E3) =
                  -((hopfMap (d x)).down : E3) := by
                    simpa [x₁, γ, d, prismHopfSourceDiffeomorph_X127] using
                      prismHopfMap_flip_X127 n x
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
            (spaceForm_X127 n).projection
                (d.symm (hopfUpperSection (q, w))) =
                (spaceForm_X127 n).projection x₁ :=
                  (congrArg (spaceForm_X127 n).projection hraw).symm
            _ = z := hπ
    have hconn : IsConnected (Set.range c) := by
      simpa only [Set.image_univ] using
        (isConnected_univ : IsConnected (Set.univ : Set Circle)).image c
          hc.continuousOn
    rw [← hrange]
    exact hconn




attribute [local instance] projectivePlaneSurfaceChartedSpace_X127
  projectivePlaneSurfaceManifold_X127 projectivePlaneSurfaceBoundaryless_X127
  projectivePlaneProductChartedSpace_X127

private def prismProjectedHopfTopMap_X127 (n : ℕ) [NeZero n] :
    C((⊤ : TopologicalSpace.Opens (spaceForm_X127 n).Orbit),
      RealProjectivePlane) :=
  ⟨fun x => prismProjectedHopf_X127 n x.val,
    (prismProjectedHopf_smooth_X127 n).continuous.comp
      continuous_subtype_val⟩

private abbrev prismProjectedHopfFullPreimage_X127 (n : ℕ) [NeZero n]
    (Q : TopologicalSpace.Opens RealProjectivePlane) :
    TopologicalSpace.Opens (spaceForm_X127 n).Orbit :=
  ⟨prismProjectedHopf_X127 n ⁻¹' Q,
    Q.isOpen.preimage (prismProjectedHopf_smooth_X127 n).continuous⟩

private def prismProjectedHopfOpenTransport_X127 (n : ℕ) [NeZero n]
    (Q : TopologicalSpace.Opens RealProjectivePlane) :
    TopologicalSpace.Opens.comap (prismProjectedHopfTopMap_X127 n) Q ≃ₘ⟮
      𝓡 3, 𝓡 3⟯ prismProjectedHopfFullPreimage_X127 n Q where
  toEquiv :=
    { toFun := fun x => ⟨x.val.val, x.property⟩
      invFun := fun x => ⟨⟨x.val, by simp⟩, x.property⟩
      left_inv := fun x => by ext; rfl
      right_inv := fun x => by ext; rfl }
  contMDiff_toFun := by
    apply (ContMDiff.subtypeVal_comp_iff
      (prismProjectedHopfFullPreimage_X127 n Q) _).mp
    change ContMDiff (𝓡 3) (𝓡 3) ∞
      ((Subtype.val : (⊤ : TopologicalSpace.Opens
        (spaceForm_X127 n).Orbit) → (spaceForm_X127 n).Orbit) ∘
        (Subtype.val : TopologicalSpace.Opens.comap
          (prismProjectedHopfTopMap_X127 n) Q →
          (⊤ : TopologicalSpace.Opens (spaceForm_X127 n).Orbit)))
    exact contMDiff_subtype_val.comp contMDiff_subtype_val
  contMDiff_invFun := by
    apply (ContMDiff.subtypeVal_comp_iff
      (TopologicalSpace.Opens.comap (prismProjectedHopfTopMap_X127 n) Q) _).mp
    apply (ContMDiff.subtypeVal_comp_iff
      (⊤ : TopologicalSpace.Opens (spaceForm_X127 n).Orbit) _).mp
    exact contMDiff_subtype_val

noncomputable def prismHopfCircleFibration_X127 (n : ℕ) [NeZero n] :
    CircleFibration (NoCuts.carrier (spaceForm_X127 n).manifold) ⊤ := by
  let f := prismProjectedHopf_X127 n
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
            (prismProjectedHopf_smooth_X127 n).continuous⟩ :
              TopologicalSpace.Opens (spaceForm_X127 n).Orbit)
          (Q × Circle) ∞,
          ∀ x, (Ψ x).1.1 = f x := by
    intro y
    exact Ehresmann.exists_circle_trivialization_of_proper_submersion_EFE
      (J := SurfaceModel.model realProjectivePlaneSurface_X127.kind)
      f (prismProjectedHopf_smooth_X127 n)
      (prismProjectedHopf_isProper_X127 n)
      (prismProjectedHopf_mfderiv_surjective_X127 n)
      (by simp)
      (fun y => by
        obtain ⟨x, hx⟩ := prismProjectedHopf_surjective_X127 n y
        simpa [hx] using prismProjectedHopf_fiber_connected_X127 n x)
      y
  choose Q hQ Ψ hΨ using hlocal
  exact
    { base := realProjectivePlaneSurface_X127
      projection := prismProjectedHopfTopMap_X127 n
      surjective := by
        intro y
        obtain ⟨x, hx⟩ := prismProjectedHopf_surjective_X127 n y
        exact ⟨⟨x, Set.mem_univ x⟩, hx⟩
      smooth := (prismProjectedHopf_smooth_X127 n).comp
        contMDiff_subtype_val
      neighborhood := Q
      mem_neighborhood := hQ
      trivialization := fun y => by
        letI : ChartedSpace
            (ModelProd (SurfaceModel.Space realProjectivePlaneSurface_X127.kind)
              (EuclideanSpace ℝ (Fin 1))) (Q y × Circle) :=
          projectivePlaneProductChartedSpace_X127 (Q y)
        exact (prismProjectedHopfOpenTransport_X127 n (Q y)).trans (Ψ y)
      projection_trivialization := by
        intro y x
        exact hΨ y (prismProjectedHopfOpenTransport_X127 n (Q y) x) }

noncomputable def prismHopfRawPresentation_X127 (n : ℕ) [NeZero n] :
    RawGraphPresentation (NoCuts.carrier (spaceForm_X127 n).manifold) :=
  RawGraphPresentation.ofClosedCircleFibration (spaceForm_X127 n).manifold
    (prismHopfCircleFibration_X127 n)



universe u

theorem prismHopfRawPresentation_ulift_X127 (n : ℕ) [NeZero n] :
    Nonempty (RawGraphPresentation (NoCuts.carrier
      ((spaceForm_X127 n).manifold.ulift.{0, u}))) :=
  RawUniverseLift.nonempty_rawGraphPresentation_ulift
    (spaceForm_X127 n).manifold (prismHopfRawPresentation_X127 n)

end GC.Geometry.QuaternionPrismCircleBundleRawX127
