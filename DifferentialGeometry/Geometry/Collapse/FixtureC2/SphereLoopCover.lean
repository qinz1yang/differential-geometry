import DifferentialGeometry.Geometry.Collapse.Inhabitants.SlimSpherePacket
import DifferentialGeometry.Geometry.Metric.AddCircle
import DifferentialGeometry.Geometry.Metric.LocalIsometryCovering
import DifferentialGeometry.Topology.Manifold.AddCircle.ParameterDerivative
import DifferentialGeometry.Geometry.Comparison.ParallelLines
import DifferentialGeometry.Geometry.Metric.Product.Completeness

/-!
# The sphere loop `S² × S¹_ℓ` and its exact distance on short arcs (S-FIXTURE-C2, K2, file 1)

`SphereLoop_FXC2 = S² × AddCircle 1` with the product metric `loopMetric_FXC2 ℓ`
(round unit sphere times the circle of length `ℓ`), as a quotient of the round cylinder
`sphereCylinder = S² × ℝ` by the covering `loopCover_FXC2 ℓ (z, t) = (z, t / ℓ mod 1)`.

* `loopCover_isLocalDiffeomorph_FXC2`, `loopCover_inner_FXC2`, `loopCover_isCoveringMap_FXC2`:
  the covering is a local isometry onto the closed manifold (`isCoveringMap_of_isLocalIsometry`);
* `cyl_sq_dist_FXC2`: Pythagoras on the cylinder (Toponogov calibrated lines, as in
  `EdgeCapSplitting`): `d((z,s),(z',t))² = (s-t)² + d_{S²}(z,z')²`;
* `loopDist_eq_cyl_of_close_FXC2`: for lifts with `|s - t| ≤ ℓ/2` the loop distance equals the
  cylinder distance (path lifting lower bound, `le_edistOf_of_coveringMap_localPullMetric`).
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

abbrev SphereLoop_FXC2 := S2 × AddCircle (1 : ℝ)

def loopMetric_FXC2 (ℓ : ℝ) (hℓ : 0 < ℓ) : SmoothRiemannianMetric IC SphereLoop_FXC2 :=
  (gS2).prod
    (scaleMetric (ℓ ^ 2) (pow_pos hℓ 2) AddCircle.flatMetric)

def circleCover_FXC2 (ℓ : ℝ) : ℝ → AddCircle (1 : ℝ) := fun t => ((t / ℓ : ℝ) : AddCircle (1 : ℝ))

def loopCover_FXC2 (ℓ : ℝ) : sphereCylinder → SphereLoop_FXC2 :=
  Prod.map id (circleCover_FXC2 ℓ)

theorem circleCover_contMDiff_FXC2 (ℓ : ℝ) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ∞ (circleCover_FXC2 ℓ) :=
  AddCircle.contMDiff_coe.comp (contDiff_id.div_const ℓ).contMDiff

theorem loopCover_contMDiff_FXC2 (ℓ : ℝ) : ContMDiff IC IC ∞ (loopCover_FXC2 ℓ) :=
  contMDiff_id.prodMap (circleCover_contMDiff_FXC2 ℓ)

abbrev tangentReal_FXC2 (t : ℝ) (s : ℝ) : TangentSpace 𝓘(ℝ, ℝ) t := s
abbrev realOfTangent_FXC2 {t : ℝ} (a : TangentSpace 𝓘(ℝ, ℝ) t) : ℝ := a

theorem mfderiv_circleCover_FXC2 (ℓ : ℝ) (t : ℝ) (a : TangentSpace 𝓘(ℝ, ℝ) t) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (circleCover_FXC2 ℓ) t a =
      mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => (s : AddCircle (1 : ℝ))) (t / ℓ)
        (tangentReal_FXC2 (t / ℓ) (ℓ⁻¹ * realOfTangent_FXC2 a)) := by
  have h1 : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => (s : AddCircle (1 : ℝ))) (t / ℓ) :=
    AddCircle.contMDiff_coe.mdifferentiableAt (by decide)
  have h2 : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s / ℓ) t :=
    ((contDiff_id.div_const ℓ : ContDiff ℝ ∞ (fun s : ℝ => s / ℓ)).contMDiff).mdifferentiableAt
      (by decide)
  have hcomp : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (circleCover_FXC2 ℓ) t =
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => (s : AddCircle (1 : ℝ))) (t / ℓ)).comp
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s / ℓ) t) :=
    mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (I'' := 𝓘(ℝ, ℝ))
      (f := fun s : ℝ => s / ℓ) (g := fun s : ℝ => (s : AddCircle (1 : ℝ))) t h1 h2
  have hd : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => s / ℓ) t a =
      tangentReal_FXC2 (t / ℓ) (ℓ⁻¹ * realOfTangent_FXC2 a) := by
    rw [mfderiv_eq_fderiv]
    have : HasFDerivAt (fun s : ℝ => s / ℓ) (ℓ⁻¹ • (ContinuousLinearMap.id ℝ ℝ)) t := by
      simpa [div_eq_inv_mul] using (hasFDerivAt_id t).const_mul ℓ⁻¹
    rw [this.fderiv]
    rfl
  exact (congrArg (fun L => L a) hcomp).trans
    (congrArg (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun s : ℝ => (s : AddCircle (1 : ℝ))) (t / ℓ)) hd)

theorem mfderiv_loopCover_FXC2 (ℓ : ℝ) (x : sphereCylinder) (v : TangentSpace IC x) :
    mfderiv IC IC (loopCover_FXC2 ℓ) x v =
      (v.1, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (circleCover_FXC2 ℓ) x.2 v.2) := by
  have h1 : MDifferentiableAt (𝓡 2) (𝓡 2) (id : S2 → S2) x.1 := mdifferentiableAt_id
  have h2 : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (circleCover_FXC2 ℓ) x.2 :=
    (circleCover_contMDiff_FXC2 ℓ).mdifferentiableAt (by decide)
  have := mfderiv_prodMap (I := 𝓡 2) (I' := 𝓘(ℝ, ℝ)) (J := 𝓡 2) (J' := 𝓘(ℝ, ℝ))
    (p := x) h1 h2
  change mfderiv IC IC (Prod.map id (circleCover_FXC2 ℓ)) x v = _
  rw [this]
  simp [mfderiv_id]
  rfl

theorem circleCover_inner_FXC2 (ℓ : ℝ) (hℓ : 0 < ℓ) (t : ℝ) (a b : TangentSpace 𝓘(ℝ, ℝ) t) :
    (scaleMetric (ℓ ^ 2) (pow_pos hℓ 2) AddCircle.flatMetric).inner (circleCover_FXC2 ℓ t)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (circleCover_FXC2 ℓ) t a)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (circleCover_FXC2 ℓ) t b) =
        (gR1).inner t a b := by
  rw [mfderiv_circleCover_FXC2, mfderiv_circleCover_FXC2]
  change (scaleMetric (ℓ ^ 2) (pow_pos hℓ 2) AddCircle.flatMetric).inner
    (((t / ℓ : ℝ)) : AddCircle (1 : ℝ)) _ _ = _
  rw [scaleMetric_inner]
  have h := AddCircle.flatMetric_inner_mfderiv_coe (t / ℓ) (ℓ⁻¹ * realOfTangent_FXC2 a)
    (ℓ⁻¹ * realOfTangent_FXC2 b)
  rw [DifferentialGeometry.euclideanMetric_inner, h]
  change ℓ ^ 2 * (ℓ⁻¹ * realOfTangent_FXC2 a * (ℓ⁻¹ * realOfTangent_FXC2 b)) =
    inner ℝ (realOfTangent_FXC2 a) (realOfTangent_FXC2 b)
  rw [real_inner_comm, real_inner_eq_re_inner]
  simp
  field_simp

theorem loopCover_inner_FXC2 (ℓ : ℝ) (hℓ : 0 < ℓ) (x : sphereCylinder)
    (v w : TangentSpace IC x) :
    (loopMetric_FXC2 ℓ hℓ).inner (loopCover_FXC2 ℓ x) (mfderiv IC IC (loopCover_FXC2 ℓ) x v)
      (mfderiv IC IC (loopCover_FXC2 ℓ) x w) = slimSphereMetric.inner x v w := by
  have hp : ∀ (y : SphereLoop_FXC2) (a b : TangentSpace IC y),
      (loopMetric_FXC2 ℓ hℓ).inner y a b =
        (gS2).inner y.1 a.1 b.1 +
          (scaleMetric (ℓ ^ 2) (pow_pos hℓ 2) AddCircle.flatMetric).inner y.2 a.2 b.2 :=
    fun y a b => SmoothRiemannianMetric.prod_inner _ _ y a b
  have hq : ∀ (a b : TangentSpace IC x), slimSphereMetric.inner x a b =
      (gS2).inner x.1 a.1 b.1 +
        (gR1).inner x.2 a.2 b.2 :=
    fun a b => SmoothRiemannianMetric.prod_inner _ _ x a b
  rw [hq, hp, mfderiv_loopCover_FXC2, mfderiv_loopCover_FXC2]
  congr 1
  exact circleCover_inner_FXC2 ℓ hℓ x.2 v.2 w.2

theorem mfderiv_circleCover_injective_FXC2 (ℓ : ℝ) (hℓ : 0 < ℓ) (t : ℝ) :
    Function.Injective (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (circleCover_FXC2 ℓ) t) := by
  intro a b hab
  rw [mfderiv_circleCover_FXC2, mfderiv_circleCover_FXC2] at hab
  have h3 := (AddCircle.bijective_mfderiv_coe (t / ℓ)).1 hab
  have h4 : ℓ⁻¹ * realOfTangent_FXC2 a = ℓ⁻¹ * realOfTangent_FXC2 b := h3
  have h5 : realOfTangent_FXC2 a = realOfTangent_FXC2 b :=
    mul_left_cancel₀ (inv_ne_zero hℓ.ne') h4
  exact h5

theorem loopCover_isLocalDiffeomorph_FXC2 (ℓ : ℝ) (hℓ : 0 < ℓ) :
    IsLocalDiffeomorph IC IC ∞ (loopCover_FXC2 ℓ) := by
  refine DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv _
    (loopCover_contMDiff_FXC2 ℓ) (fun x v w hvw => ?_) rfl
  rw [mfderiv_loopCover_FXC2, mfderiv_loopCover_FXC2] at hvw
  obtain ⟨h1, h2⟩ := Prod.mk.inj hvw
  exact Prod.ext h1 (mfderiv_circleCover_injective_FXC2 ℓ hℓ x.2 h2)

theorem cylinderMetricComplete_FXC2 :
    DifferentialGeometry.RiemannianMetricComplete slimSphereMetric :=
  (DifferentialGeometry.RiemannianMetricComplete.of_compact
    (gS2)).prod
      (euclideanMetric_complete (E := ℝ))

theorem loopCover_isCoveringMap_FXC2 (ℓ : ℝ) (hℓ : 0 < ℓ) :
    IsCoveringMap (loopCover_FXC2 ℓ) ∧ Function.Surjective (loopCover_FXC2 ℓ) :=
  isCoveringMap_of_isLocalIsometry slimSphereMetric (loopMetric_FXC2 ℓ hℓ)
    cylinderMetricComplete_FXC2 (loopCover_isLocalDiffeomorph_FXC2 ℓ hℓ)
    (loopCover_inner_FXC2 ℓ hℓ)

open private slimSphereLine_isometry
  from DifferentialGeometry.Geometry.Collapse.Inhabitants.SlimSphere

/-- The intrinsic distance of the round unit sphere. -/
def sphereDist_FXC2 (s s' : S2) : ℝ :=
  (riemannianEDistOf (gS2) s s').toReal

theorem cyl_snd_le_dist_FXC2 (x y : sphereCylinder) : |x.2 - y.2| ≤ dist x y := by
  have hd := riemannianEDistOf_snd_le_prod
    (gS2) (gR1) x y
  have hr : riemannianEDistOf (gR1) x.2 y.2 =
      ENNReal.ofReal |x.2 - y.2| := by
    change riemannianEDist 𝓘(ℝ, ℝ) x.2 y.2 = _
    rw [← IsRiemannianManifold.out (I := 𝓘(ℝ, ℝ)), edist_dist, Real.dist_eq]
  rw [hr] at hd
  change ENNReal.ofReal |x.2 - y.2| ≤ riemannianEDistOf slimSphereMetric x y at hd
  rw [inducedMetricSpace_hmetric slimSphereMetric] at hd
  exact (ENNReal.ofReal_le_ofReal_iff dist_nonneg).mp hd

theorem cyl_fourPoint_FXC2 :
    Comparison.Toponogov.fourPointComparison 0 (univ : Set sphereCylinder) :=
  (model_lcp04_clauses_of_sectional_nonneg slimSphereMetric slimSphereMetricNorm
    slimSphereMetric_sectional_nonneg).2.1

theorem cyl_lineCoordinate_FXC2 (x : sphereCylinder) :
    Comparison.Toponogov.lineCoordinate slimSphereLine x = x.2 := by
  have hcomp := cyl_fourPoint_FXC2
  let a := x.2
  let b := Comparison.Toponogov.lineCoordinate slimSphereLine x
  let c := dist x (slimSphereLine 0) ^ 2
  have hh (t : ℝ) : 2 * (b - a) * t ≤ c - a ^ 2 := by
    have hl := cyl_snd_le_dist_FXC2 x (slimSphereLine t)
    change |x.2 - t| ≤ dist x (slimSphereLine t) at hl
    have hs := Comparison.Toponogov.sq_dist_isometry_line hcomp slimSphereLine_isometry x t
    have hsq := sq_le_sq₀ (abs_nonneg (x.2 - t)) dist_nonneg |>.2 hl
    rw [sq_abs] at hsq
    dsimp [a, b, c]
    nlinarith
  by_contra hne
  have hn : 2 * (b - a) ≠ 0 := by
    dsimp [a, b]
    exact mul_ne_zero (by norm_num) (sub_ne_zero.mpr hne)
  have hb := hh ((c - a ^ 2 + 1) / (2 * (b - a)))
  rw [mul_div_cancel₀ _ hn] at hb
  linarith

theorem cyl_dist_line_FXC2 (z : S2) (t t' : ℝ) :
    dist ((z, t) : sphereCylinder) (z, t') = |t - t'| := by
  change (riemannianEDistOf slimSphereMetric (z, t) (z, t')).toReal = _
  rw [slimSphereMetric, riemannianEDistOf_prod_right]
  change (riemannianEDist 𝓘(ℝ, ℝ) t t').toReal = _
  rw [← IsRiemannianManifold.out (I := 𝓘(ℝ, ℝ)), edist_dist,
    ENNReal.toReal_ofReal dist_nonneg, Real.dist_eq]

theorem cyl_dist_slice_FXC2 (z z' : S2) (t : ℝ) :
    dist ((z, t) : sphereCylinder) (z', t) = sphereDist_FXC2 z z' := by
  change (riemannianEDistOf slimSphereMetric (z, t) (z', t)).toReal = _
  rw [slimSphereMetric, riemannianEDistOf_prod_left]
  rfl

theorem cyl_isometry_line_FXC2 (z : S2) : Isometry (fun t : ℝ => ((z, t) : sphereCylinder)) := by
  apply Isometry.of_dist_eq
  intro t t'
  rw [cyl_dist_line_FXC2, Real.dist_eq]

theorem cyl_sq_dist_FXC2 (x y : sphereCylinder) :
    dist x y ^ 2 = (x.2 - y.2) ^ 2 + sphereDist_FXC2 x.1 y.1 ^ 2 := by
  have h := Comparison.Toponogov.sq_dist_calibrated_lines cyl_fourPoint_FXC2
    slimSphereLine_isometry (cyl_isometry_line_FXC2 x.1) (cyl_isometry_line_FXC2 y.1)
    (fun t => by
      rw [cyl_lineCoordinate_FXC2, cyl_lineCoordinate_FXC2]; simp)
    (fun t => by
      rw [cyl_lineCoordinate_FXC2, cyl_lineCoordinate_FXC2]; simp) x.2 y.2
  rw [cyl_lineCoordinate_FXC2, cyl_lineCoordinate_FXC2] at h
  simp only [sub_self, zero_add] at h
  have h0 : dist ((x.1, (0 : ℝ)) : sphereCylinder) (y.1, 0) = sphereDist_FXC2 x.1 y.1 :=
    cyl_dist_slice_FXC2 x.1 y.1 0
  have hxy : dist ((x.1, x.2) : sphereCylinder) (y.1, y.2) = dist x y := rfl
  rw [h0] at h
  nlinarith [h, hxy]

theorem coe_eq_coe_iff_FXC2 {a b : ℝ} :
    ((a : ℝ) : AddCircle (1 : ℝ)) = ((b : ℝ) : AddCircle (1 : ℝ)) ↔ ∃ n : ℤ, b = a + n := by
  rw [← sub_eq_zero, ← AddCircle.coe_sub, AddCircle.coe_eq_zero_iff]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨-n, by simp at hn; push_cast; linarith⟩
  · rintro ⟨n, hn⟩
    exact ⟨-n, by simp; linarith⟩

theorem loopCover_eq_iff_FXC2 {ℓ : ℝ} (hℓ : 0 < ℓ) {x y : sphereCylinder} :
    loopCover_FXC2 ℓ x = loopCover_FXC2 ℓ y ↔ x.1 = y.1 ∧ ∃ n : ℤ, y.2 = x.2 + n * ℓ := by
  change (x.1, circleCover_FXC2 ℓ x.2) = (y.1, circleCover_FXC2 ℓ y.2) ↔ _
  rw [Prod.mk.injEq]
  refine and_congr_right fun _ => ?_
  change ((x.2 / ℓ : ℝ) : AddCircle (1 : ℝ)) = ((y.2 / ℓ : ℝ) : AddCircle (1 : ℝ)) ↔ _
  rw [coe_eq_coe_iff_FXC2]
  refine exists_congr fun n => ?_
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    rw [h]
    field_simp

/-- The intrinsic distance of the loop metric. -/
def loopDist_FXC2 (ℓ : ℝ) (hℓ : 0 < ℓ) (a b : SphereLoop_FXC2) : ℝ :=
  (riemannianEDistOf (loopMetric_FXC2 ℓ hℓ) a b).toReal

theorem localPull_loopMetric_FXC2 (ℓ : ℝ) (hℓ : 0 < ℓ) :
    localPullMetric (loopMetric_FXC2 ℓ hℓ) (loopCover_FXC2 ℓ)
      (loopCover_isLocalDiffeomorph_FXC2 ℓ hℓ) = slimSphereMetric := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [localPullMetric_inner]
  exact loopCover_inner_FXC2 ℓ hℓ x v w

theorem cyl_edist_FXC2 (x y : sphereCylinder) :
    riemannianEDistOf slimSphereMetric x y = ENNReal.ofReal (dist x y) :=
  inducedMetricSpace_hmetric slimSphereMetric x y

theorem loopDist_le_cyl_FXC2 (ℓ : ℝ) (hℓ : 0 < ℓ) (x y : sphereCylinder) :
    loopDist_FXC2 ℓ hℓ (loopCover_FXC2 ℓ x) (loopCover_FXC2 ℓ y) ≤ dist x y := by
  have h := Geometry.Metric.edistOf_le_of_quad_of_localDiffeomorph slimSphereMetric
    (loopMetric_FXC2 ℓ hℓ) (loopCover_FXC2 ℓ) (loopCover_isLocalDiffeomorph_FXC2 ℓ hℓ)
    (c := 1) one_pos (fun x v => by rw [loopCover_inner_FXC2, one_mul]) x y
  rw [Real.sqrt_one, ENNReal.ofReal_one, one_mul, cyl_edist_FXC2] at h
  exact ENNReal.toReal_le_of_le_ofReal dist_nonneg h

theorem sq_le_sq_sub_int_FXC2 (ℓ u : ℝ) (hℓ : 0 < ℓ) (hu : |u| ≤ ℓ / 2) (n : ℤ) :
    u ^ 2 ≤ (u - n * ℓ) ^ 2 := by
  have h1 : |u| ≤ |u - n * ℓ| := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
        have : (1 : ℤ) ≤ |n| := Int.one_le_abs hn
        exact_mod_cast this
      have h2 : |(n : ℝ) * ℓ| = |(n : ℝ)| * ℓ := by rw [abs_mul, abs_of_pos hℓ]
      have h3 : ℓ ≤ |(n : ℝ) * ℓ| := by rw [h2]; nlinarith
      have h4 : |(n : ℝ) * ℓ| ≤ |u - n * ℓ| + |u| := by
        have := abs_sub_abs_le_abs_sub ((n : ℝ) * ℓ) u
        have h5 : |(n : ℝ) * ℓ - u| = |u - n * ℓ| := abs_sub_comm _ _
        linarith [abs_sub_abs_le_abs_sub ((n : ℝ) * ℓ) u]
      linarith
  nlinarith [abs_nonneg u, sq_abs u, sq_abs (u - n * ℓ), sq_nonneg (|u| - |u - n * ℓ|)]

theorem loopDist_eq_cyl_of_close_FXC2 (ℓ : ℝ) (hℓ : 0 < ℓ) (x y : sphereCylinder)
    (hxy : |x.2 - y.2| ≤ ℓ / 2) :
    loopDist_FXC2 ℓ hℓ (loopCover_FXC2 ℓ x) (loopCover_FXC2 ℓ y) = dist x y := by
  apply le_antisymm (loopDist_le_cyl_FXC2 ℓ hℓ x y)
  have hcov := (loopCover_isCoveringMap_FXC2 ℓ hℓ).1
  have h := le_edistOf_of_coveringMap_localPullMetric slimSphereMetric (loopMetric_FXC2 ℓ hℓ)
    (loopCover_isLocalDiffeomorph_FXC2 ℓ hℓ) hcov (localPull_loopMetric_FXC2 ℓ hℓ)
    (r := ENNReal.ofReal (dist x y)) x (loopCover_FXC2 ℓ y) (fun x' hx' => by
      obtain ⟨h1, n, hn⟩ := (loopCover_eq_iff_FXC2 hℓ).mp hx'
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
  have hne := riemannianEDistOf_ne_top (loopMetric_FXC2 ℓ hℓ) (loopCover_FXC2 ℓ x)
    (loopCover_FXC2 ℓ y)
  exact (ENNReal.ofReal_le_iff_le_toReal hne).mp h

end DifferentialGeometry.Geometry.Collapse
