import DifferentialGeometry.Geometry.Collapse.FixtureC2.SphereLoopCover

/-!
# The shifted covering of the sphere loop (S-FIXTURE-C2b, K2, G2 file 1)

`loopCoverS_FXC2 ℓ a (z, t) = (z, (t + a) / ℓ mod 1)`: the covering of `SphereLoop_FXC2` by the
round cylinder, with the circle coordinate shifted by `a`. Every lemma of `SphereLoopCover` holds
verbatim with the shift (the derivative is unchanged). Reason for the shift: the base point
`(z, 0)` of the cylinder is sent to the point `(z, a / ℓ)` of the loop, so the cylinder ball at
`(z, 0)` serves as the lift of the loop ball at every centre `(z, a / ℓ)` and the volume and the
curvature constants never depend on `a` or on `ℓ`.

* `loopCoverS_isCoveringMap_FXC2`, `localPull_loopMetricS_FXC2`: the shifted cover is a covering
  and a local isometry from the cylinder;
* `loopCoverS_eq_iff_FXC2`: the fibres are `ℓ`-translates;
* `loopDist_eq_cylS_of_close_FXC2`: exact loop distance of two points with lifts at height
  difference at most `ℓ / 2`.
-/

set_option autoImplicit false
noncomputable section
open Bundle Manifold Set Metric
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Geometry.Collapse
open scoped Manifold ContDiff

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
attribute [local instance] sphereDimension cylinderDimension sphereCompact sphereConnected
  intrinsicMetric intrinsicUniform intrinsicEMetric intrinsicPseudoMetric intrinsicBundle
  cylinderRiemannian cylinderContinuous cylinderComplete

namespace DifferentialGeometry.Geometry.Collapse

local notation "S2" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "IC" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
local notation "gS2" => roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)
local notation "gR1" => DifferentialGeometry.euclideanMetric (E := ℝ)

def circleCoverS_FXC2 (ℓ a : ℝ) : ℝ → AddCircle (1 : ℝ) :=
  fun t => (((t + a) / ℓ : ℝ) : AddCircle (1 : ℝ))

def loopCoverS_FXC2 (ℓ a : ℝ) : sphereCylinder → SphereLoop_FXC2 :=
  Prod.map id (circleCoverS_FXC2 ℓ a)

theorem contDiff_shiftDiv_FXC2 (ℓ a : ℝ) : ContDiff ℝ ∞ (fun s : ℝ => (s + a) / ℓ) :=
  (contDiff_id.add contDiff_const).div_const ℓ

theorem circleCoverS_contMDiff_FXC2 (ℓ a : ℝ) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (circleCoverS_FXC2 ℓ a) :=
  AddCircle.contMDiff_coe.comp (contDiff_shiftDiv_FXC2 ℓ a).contMDiff

theorem loopCoverS_contMDiff_FXC2 (ℓ a : ℝ) : ContMDiff IC IC ∞ (loopCoverS_FXC2 ℓ a) :=
  contMDiff_id.prodMap (circleCoverS_contMDiff_FXC2 ℓ a)

theorem mfderiv_circleCoverS_FXC2 (ℓ a : ℝ) (t : ℝ) (v : TangentSpace 𝓘(ℝ, ℝ) t) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (circleCoverS_FXC2 ℓ a) t v =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => (s : AddCircle (1 : ℝ))) ((t + a) / ℓ)
        (tangentReal_FXC2 ((t + a) / ℓ) (ℓ⁻¹ * realOfTangent_FXC2 v)) := by
  have h1 : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => (s : AddCircle (1 : ℝ)))
      ((t + a) / ℓ) :=
    AddCircle.contMDiff_coe.mdifferentiableAt (by decide)
  have h2 : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => (s + a) / ℓ) t :=
    (contDiff_shiftDiv_FXC2 ℓ a).contMDiff.mdifferentiableAt (by decide)
  have hcomp : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (circleCoverS_FXC2 ℓ a) t =
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => (s : AddCircle (1 : ℝ))) ((t + a) / ℓ)).comp
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => (s + a) / ℓ) t) :=
    mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓘(ℝ, ℝ))
      (f := fun s : ℝ => (s + a) / ℓ) (g := fun s : ℝ => (s : AddCircle (1 : ℝ))) t h1 h2
  have hd : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => (s + a) / ℓ) t v =
      tangentReal_FXC2 ((t + a) / ℓ) (ℓ⁻¹ * realOfTangent_FXC2 v) := by
    rw [mfderiv_eq_fderiv]
    have : HasFDerivAt (fun s : ℝ => (s + a) / ℓ) (ℓ⁻¹ • (ContinuousLinearMap.id ℝ ℝ)) t := by
      simpa [div_eq_inv_mul] using ((hasFDerivAt_id t).add_const a).const_mul ℓ⁻¹
    rw [this.fderiv]
    rfl
  exact (congrArg (fun L => L v) hcomp).trans
    (congrArg (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => (s : AddCircle (1 : ℝ))) ((t + a) / ℓ)) hd)

theorem mfderiv_loopCoverS_FXC2 (ℓ a : ℝ) (x : sphereCylinder) (v : TangentSpace IC x) :
    mfderiv IC IC (loopCoverS_FXC2 ℓ a) x v =
      (v.1, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (circleCoverS_FXC2 ℓ a) x.2 v.2) := by
  have h1 : MDifferentiableAt (𝓡 2) (𝓡 2) (id : S2 → S2) x.1 := mdifferentiableAt_id
  have h2 : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (circleCoverS_FXC2 ℓ a) x.2 :=
    (circleCoverS_contMDiff_FXC2 ℓ a).mdifferentiableAt (by decide)
  have := mfderiv_prodMap (I := 𝓡 2) (I' := 𝓘(ℝ, ℝ)) (J := 𝓡 2) (J' := 𝓘(ℝ, ℝ))
    (p := x) h1 h2
  change mfderiv IC IC (Prod.map id (circleCoverS_FXC2 ℓ a)) x v = _
  rw [this]
  simp [mfderiv_id]
  rfl

theorem circleCoverS_inner_FXC2 (ℓ a : ℝ) (hℓ : 0 < ℓ) (t : ℝ)
    (u v : TangentSpace 𝓘(ℝ, ℝ) t) :
    (scaleMetric (ℓ ^ 2) (pow_pos hℓ 2) AddCircle.flatMetric).inner (circleCoverS_FXC2 ℓ a t)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (circleCoverS_FXC2 ℓ a) t u)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (circleCoverS_FXC2 ℓ a) t v) =
        (gR1).inner t u v := by
  rw [mfderiv_circleCoverS_FXC2, mfderiv_circleCoverS_FXC2]
  change (scaleMetric (ℓ ^ 2) (pow_pos hℓ 2) AddCircle.flatMetric).inner
    ((((t + a) / ℓ : ℝ)) : AddCircle (1 : ℝ)) _ _ = _
  rw [scaleMetric_inner]
  have h := AddCircle.flatMetric_inner_mfderiv_coe ((t + a) / ℓ) (ℓ⁻¹ * realOfTangent_FXC2 u)
    (ℓ⁻¹ * realOfTangent_FXC2 v)
  rw [DifferentialGeometry.euclideanMetric_inner, h]
  change ℓ ^ 2 * (ℓ⁻¹ * realOfTangent_FXC2 u * (ℓ⁻¹ * realOfTangent_FXC2 v)) =
    inner ℝ (realOfTangent_FXC2 u) (realOfTangent_FXC2 v)
  rw [real_inner_comm, real_inner_eq_re_inner]
  simp
  field_simp

theorem loopCoverS_inner_FXC2 (ℓ a : ℝ) (hℓ : 0 < ℓ) (x : sphereCylinder)
    (v w : TangentSpace IC x) :
    (loopMetric_FXC2 ℓ hℓ).inner (loopCoverS_FXC2 ℓ a x)
      (mfderiv IC IC (loopCoverS_FXC2 ℓ a) x v)
      (mfderiv IC IC (loopCoverS_FXC2 ℓ a) x w) = slimSphereMetric.inner x v w := by
  have hp : ∀ (y : SphereLoop_FXC2) (u b : TangentSpace IC y),
      (loopMetric_FXC2 ℓ hℓ).inner y u b =
        (gS2).inner y.1 u.1 b.1 +
          (scaleMetric (ℓ ^ 2) (pow_pos hℓ 2) AddCircle.flatMetric).inner y.2 u.2 b.2 :=
    fun y u b => SmoothRiemannianMetric.prod_inner _ _ y u b
  have hq : ∀ (u b : TangentSpace IC x), slimSphereMetric.inner x u b =
      (gS2).inner x.1 u.1 b.1 +
        (gR1).inner x.2 u.2 b.2 :=
    fun u b => SmoothRiemannianMetric.prod_inner _ _ x u b
  rw [hq, hp, mfderiv_loopCoverS_FXC2, mfderiv_loopCoverS_FXC2]
  congr 1
  exact circleCoverS_inner_FXC2 ℓ a hℓ x.2 v.2 w.2

theorem mfderiv_circleCoverS_injective_FXC2 (ℓ a : ℝ) (hℓ : 0 < ℓ) (t : ℝ) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (circleCoverS_FXC2 ℓ a) t) := by
  intro u b hub
  rw [mfderiv_circleCoverS_FXC2, mfderiv_circleCoverS_FXC2] at hub
  have h3 := (AddCircle.bijective_mfderiv_coe ((t + a) / ℓ)).1 hub
  have h4 : ℓ⁻¹ * realOfTangent_FXC2 u = ℓ⁻¹ * realOfTangent_FXC2 b := h3
  have h5 : realOfTangent_FXC2 u = realOfTangent_FXC2 b :=
    mul_left_cancel₀ (inv_ne_zero hℓ.ne') h4
  exact h5

theorem loopCoverS_isLocalDiffeomorph_FXC2 (ℓ a : ℝ) (hℓ : 0 < ℓ) :
    IsLocalDiffeomorph IC IC ∞ (loopCoverS_FXC2 ℓ a) := by
  refine DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
    (loopCoverS_contMDiff_FXC2 ℓ a) (fun x v w hvw => ?_) rfl
  rw [mfderiv_loopCoverS_FXC2, mfderiv_loopCoverS_FXC2] at hvw
  obtain ⟨h1, h2⟩ := Prod.mk.inj hvw
  exact Prod.ext h1 (mfderiv_circleCoverS_injective_FXC2 ℓ a hℓ x.2 h2)

theorem loopCoverS_isCoveringMap_FXC2 (ℓ a : ℝ) (hℓ : 0 < ℓ) :
    IsCoveringMap (loopCoverS_FXC2 ℓ a) ∧ Function.Surjective (loopCoverS_FXC2 ℓ a) :=
  isCoveringMap_of_isLocalIsometry slimSphereMetric (loopMetric_FXC2 ℓ hℓ)
    cylinderMetricComplete_FXC2 (loopCoverS_isLocalDiffeomorph_FXC2 ℓ a hℓ)
    (loopCoverS_inner_FXC2 ℓ a hℓ)

theorem loopCoverS_eq_iff_FXC2 {ℓ : ℝ} (a : ℝ) (hℓ : 0 < ℓ) {x y : sphereCylinder} :
    loopCoverS_FXC2 ℓ a x = loopCoverS_FXC2 ℓ a y ↔ x.1 = y.1 ∧ ∃ n : ℤ, y.2 = x.2 + n * ℓ := by
  change (x.1, circleCoverS_FXC2 ℓ a x.2) = (y.1, circleCoverS_FXC2 ℓ a y.2) ↔ _
  rw [Prod.mk.injEq]
  refine and_congr_right fun _ => ?_
  change (((x.2 + a) / ℓ : ℝ) : AddCircle (1 : ℝ)) = (((y.2 + a) / ℓ : ℝ) : AddCircle (1 : ℝ)) ↔ _
  rw [coe_eq_coe_iff_FXC2]
  refine exists_congr fun n => ?_
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    rw [h]
    field_simp
    ring

theorem localPull_loopMetricS_FXC2 (ℓ a : ℝ) (hℓ : 0 < ℓ) :
    localPullMetric (loopMetric_FXC2 ℓ hℓ) (loopCoverS_FXC2 ℓ a)
      (loopCoverS_isLocalDiffeomorph_FXC2 ℓ a hℓ) = slimSphereMetric := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [localPullMetric_inner]
  exact loopCoverS_inner_FXC2 ℓ a hℓ x v w

theorem loopDist_le_cylS_FXC2 (ℓ a : ℝ) (hℓ : 0 < ℓ) (x y : sphereCylinder) :
    loopDist_FXC2 ℓ hℓ (loopCoverS_FXC2 ℓ a x) (loopCoverS_FXC2 ℓ a y) ≤ dist x y := by
  have h := Geometry.Metric.edistOf_le_of_quad_of_localDiffeomorph slimSphereMetric
    (loopMetric_FXC2 ℓ hℓ) (loopCoverS_FXC2 ℓ a) (loopCoverS_isLocalDiffeomorph_FXC2 ℓ a hℓ)
    (c := 1) one_pos (fun x v => by rw [loopCoverS_inner_FXC2, one_mul]) x y
  rw [Real.sqrt_one, ENNReal.ofReal_one, one_mul, cyl_edist_FXC2] at h
  exact ENNReal.toReal_le_of_le_ofReal dist_nonneg h

theorem loopDist_eq_cylS_of_close_FXC2 (ℓ a : ℝ) (hℓ : 0 < ℓ) (x y : sphereCylinder)
    (hxy : |x.2 - y.2| ≤ ℓ / 2) :
    loopDist_FXC2 ℓ hℓ (loopCoverS_FXC2 ℓ a x) (loopCoverS_FXC2 ℓ a y) = dist x y := by
  apply le_antisymm (loopDist_le_cylS_FXC2 ℓ a hℓ x y)
  have hcov := (loopCoverS_isCoveringMap_FXC2 ℓ a hℓ).1
  have h := le_edistOf_of_coveringMap_localPullMetric slimSphereMetric (loopMetric_FXC2 ℓ hℓ)
    (loopCoverS_isLocalDiffeomorph_FXC2 ℓ a hℓ) hcov (localPull_loopMetricS_FXC2 ℓ a hℓ)
    (r := ENNReal.ofReal (dist x y)) x (loopCoverS_FXC2 ℓ a y) (fun x' hx' => by
      obtain ⟨h1, n, hn⟩ := (loopCoverS_eq_iff_FXC2 a hℓ).mp hx'
      rw [cyl_edist_FXC2]
      apply ENNReal.ofReal_le_ofReal
      have hs := cyl_sq_dist_FXC2 x y
      have hs' := cyl_sq_dist_FXC2 x x'
      have hsq := sq_le_sq_sub_int_FXC2 ℓ (x.2 - y.2) hℓ hxy (-n)
      rw [← h1] at hs
      have h6 : (x.2 - x'.2) ^ 2 = (x.2 - y.2 - ((-n : ℤ) : ℝ) * ℓ) ^ 2 := by
        have : x'.2 = y.2 - n * ℓ := by linarith
        rw [this]
        push_cast
        ring
      have h7 : dist x y ^ 2 ≤ dist x x' ^ 2 := by nlinarith
      exact le_of_sq_le_sq h7 dist_nonneg)
  have hne := riemannianEDistOf_ne_top (loopMetric_FXC2 ℓ hℓ) (loopCoverS_FXC2 ℓ a x)
    (loopCoverS_FXC2 ℓ a y)
  exact (ENNReal.ofReal_le_iff_le_toReal hne).mp h

end DifferentialGeometry.Geometry.Collapse
