import DifferentialGeometry.Geometry.Thurston.Models.ConeModelSolidTorus
import DifferentialGeometry.Geometry.Thurston.Models.CoordinateHomogeneity
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPants

/-!
# Length-parametrised screw lifts and solid-torus marks

The four connection models with nonpositive base curvature have fibre-preserving isometric
recentering maps. Smooth screw diffeomorphisms are accompanied by their permutation groups,
whose multiplication applies the right factor first. Positive fibre length scales the actual
solid-torus quotient chart. The marked clockwise section and fibre satisfy exact Bezout
identities and the filling matrix sends the meridian to the negative filling slope.
-/

set_option autoImplicit false
noncomputable section
open DifferentialGeometry
open scoped Manifold ContDiff

namespace GC.Geometry

private def screwLiftTranslate (v : ModelCoordinates) :
    ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates where
  toFun x := x + v
  invFun x := x - v
  left_inv x := add_sub_cancel_right x v
  right_inv x := sub_add_cancel x v
  contMDiff_toFun := (by fun_prop : ContDiff ℝ ∞ fun x : ModelCoordinates => x + v).contMDiff
  contMDiff_invFun := (by fun_prop : ContDiff ℝ ∞ fun x : ModelCoordinates => x - v).contMDiff

private def screwLiftChart (m : ConnectionModel) :
    ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates :=
  match m with
  | .euclidean => shearDiffeo 0
  | .nil => shearDiffeo 1
  | .hyperbolicProduct => hyperboloidDiffeo 0
  | .universalSL2 => hyperboloidDiffeo 1
  | .sphericalProduct | .spherical => Diffeomorph.refl (𝓡 3) ModelCoordinates ∞

private def screwLiftNormalMetric (m : ConnectionModel) :
    SmoothRiemannianMetric (𝓡 3) ModelCoordinates :=
  match m with
  | .nil => coordinateModelMetric .nil
  | .hyperbolicProduct => coordinateModelMetric .hyperbolicProduct
  | .universalSL2 => coordinateModelMetric .universalSL2
  | .euclidean | .sphericalProduct | .spherical => euclideanModelMetric

private def screwLiftNormalShift (m : ConnectionModel) (a b : ModelCoordinates) :
    ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates :=
  match m with
  | .nil => coordinateShiftDiffeomorph .nil a b
  | .hyperbolicProduct => coordinateShiftDiffeomorph .hyperbolicProduct a b
  | .universalSL2 => coordinateShiftDiffeomorph .universalSL2 a b
  | .euclidean | .sphericalProduct | .spherical => screwLiftTranslate (b - a)

private def screwLiftRecentre (m : ConnectionModel) (v : ModelCoordinates) :
    ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates :=
  let Φ := screwLiftChart m
  Φ.trans ((screwLiftNormalShift m (Φ 0) (Φ v)).trans Φ.symm)

def recentre (m : ConnectionModel) (hm : m.baseCurvature ≤ 0) (v : ModelCoordinates) :
    ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates := by
  cases m
  · exact screwLiftRecentre .euclidean v
  · norm_num [ConnectionModel.baseCurvature] at hm
  · exact screwLiftRecentre .hyperbolicProduct v
  · exact screwLiftRecentre .nil v
  · exact screwLiftRecentre .universalSL2 v
  · norm_num [ConnectionModel.baseCurvature] at hm

private theorem screwLiftNormalShift_self (m : ConnectionModel) (a b : ModelCoordinates) :
    screwLiftNormalShift m a b a = b := by
  cases m <;> first
    | exact coordinateShift_self _ a b
    | change a + (b - a) = b
      abel

private theorem recentre_eq (m : ConnectionModel) (hm : m.baseCurvature ≤ 0)
    (v : ModelCoordinates) : recentre m hm v = screwLiftRecentre m v := by
  cases m <;> first
    | rfl
    | norm_num [ConnectionModel.baseCurvature] at hm

theorem recentre_zero (m : ConnectionModel) (hm : m.baseCurvature ≤ 0)
    (v : ModelCoordinates) : recentre m hm v 0 = v := by
  rw [recentre_eq]
  change (screwLiftChart m).symm
    (screwLiftNormalShift m ((screwLiftChart m) 0) ((screwLiftChart m) v)
      ((screwLiftChart m) 0)) = v
  rw [screwLiftNormalShift_self]
  exact (screwLiftChart m).symm_apply_apply v

private theorem screwLiftChart_metric (m : ConnectionModel) (hm : m.baseCurvature ≤ 0) :
    m.coneProfile.metric = Diffeomorph.pullbackMetricCross (screwLiftNormalMetric m)
      (screwLiftChart m) := by
  cases m
  · apply (flatProfile 0).metric_eq_pullbackMetricCross euclideanModelMetric (shearDiffeo 0)
    intro p v w
    have h := flatProfile_inner_shearMap 0 p v w
    rw [zero_smul_fibreConnection, connectionInner_euclidean] at h
    exact h
  · norm_num [ConnectionModel.baseCurvature] at hm
  · apply (hyperbolicProfile 0).metric_eq_pullbackMetricCross
      (coordinateModelMetric .hyperbolicProduct) (hyperboloidDiffeo 0)
    intro p v w
    have h := hyperbolicProfile_inner_hyperboloidMap 0 p v w
    rw [zero_smul_fibreConnection,
      connectionInner_eq_coordinateInner connectionCoframe_hyperbolicProduct,
      ← coordinateModelMetric_inner] at h
    exact h
  · apply (flatProfile 1).metric_eq_pullbackMetricCross
      (coordinateModelMetric .nil) (shearDiffeo 1)
    intro p v w
    have h := flatProfile_inner_shearMap 1 p v w
    rw [FibreConnection.one_smul',
      connectionInner_eq_coordinateInner connectionCoframe_nil,
      ← coordinateModelMetric_inner] at h
    exact h
  · apply (hyperbolicProfile 1).metric_eq_pullbackMetricCross
      (coordinateModelMetric .universalSL2) (hyperboloidDiffeo 1)
    intro p v w
    have h := hyperbolicProfile_inner_hyperboloidMap 1 p v w
    rw [FibreConnection.one_smul',
      connectionInner_eq_coordinateInner connectionCoframe_universalSL2,
      ← coordinateModelMetric_inner] at h
    exact h
  · norm_num [ConnectionModel.baseCurvature] at hm

private theorem screwLiftCoordinateShift_isometry (k : CoordinateModel)
    (a b : ModelCoordinates) :
    Diffeomorph.pullbackMetricCross (coordinateModelMetric k)
      (coordinateShiftDiffeomorph k a b) = coordinateModelMetric k := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [Diffeomorph.pullbackMetricCross_inner, mfderiv_eq_fderiv]
  change (coordinateModelMetric k).inner (coordinateShift k a b x)
    (fderiv ℝ (coordinateShift k a b) x v) (fderiv ℝ (coordinateShift k a b) x w) = _
  rw [(coordinateShift_hasFDerivAt k a b x).fderiv]
  change coordinateBilinear k (coordinateShift k a b x)
    (coordinateShiftLinear k a b v) (coordinateShiftLinear k a b w) =
      coordinateBilinear k x v w
  exact (coordinateBilinear_apply k _ _ _).trans
    ((coordinateShift_preserves_inner k a b x v w).trans
      (coordinateBilinear_apply k x v w).symm)

private theorem screwLiftNormalShift_isometry (m : ConnectionModel)
    (a b : ModelCoordinates) :
    Diffeomorph.pullbackMetricCross (screwLiftNormalMetric m)
      (screwLiftNormalShift m a b) = screwLiftNormalMetric m := by
  cases m
  · change Diffeomorph.pullbackMetricCross euclideanModelMetric
      (screwLiftTranslate (b - a)) = euclideanModelMetric
    rw [Diffeomorph.pullbackMetricCross_eq_pullbackMetric]
    exact euclideanModelMetric_pullback_affine _ (LinearIsometryEquiv.refl ℝ ModelCoordinates)
      (b - a) fun x => rfl
  · change Diffeomorph.pullbackMetricCross euclideanModelMetric
      (screwLiftTranslate (b - a)) = euclideanModelMetric
    rw [Diffeomorph.pullbackMetricCross_eq_pullbackMetric]
    exact euclideanModelMetric_pullback_affine _ (LinearIsometryEquiv.refl ℝ ModelCoordinates)
      (b - a) fun x => rfl
  · exact screwLiftCoordinateShift_isometry .hyperbolicProduct a b
  · exact screwLiftCoordinateShift_isometry .nil a b
  · exact screwLiftCoordinateShift_isometry .universalSL2 a b
  · change Diffeomorph.pullbackMetricCross euclideanModelMetric
      (screwLiftTranslate (b - a)) = euclideanModelMetric
    rw [Diffeomorph.pullbackMetricCross_eq_pullbackMetric]
    exact euclideanModelMetric_pullback_affine _ (LinearIsometryEquiv.refl ℝ ModelCoordinates)
      (b - a) fun x => rfl

theorem recentre_isometry (m : ConnectionModel) (hm : m.baseCurvature ≤ 0)
    (v : ModelCoordinates) :
    Diffeomorph.pullbackMetric m.coneProfile.metric (recentre m hm v) =
      m.coneProfile.metric := by
  rw [← Diffeomorph.pullbackMetricCross_eq_pullbackMetric, recentre_eq]
  let Φ := screwLiftChart m
  let S := screwLiftNormalShift m (Φ 0) (Φ v)
  change Diffeomorph.pullbackMetricCross m.coneProfile.metric (Φ.trans (S.trans Φ.symm)) = _
  rw [← Diffeomorph.pullbackMetricCross_trans, ← Diffeomorph.pullbackMetricCross_trans]
  have hinv : Diffeomorph.pullbackMetricCross m.coneProfile.metric Φ.symm =
      screwLiftNormalMetric m :=
    (Diffeomorph.pullbackMetricCross_symm_eq_iff.mp (screwLiftChart_metric m hm).symm)
  rw [hinv, screwLiftNormalShift_isometry]
  exact (screwLiftChart_metric m hm).symm

private theorem screwLiftCoordinateShift_fibre (k : CoordinateModel)
    (a b x : ModelCoordinates) (t : ℝ) :
    coordinateShift k a b (x + fibreShift t) = coordinateShift k a b x + fibreShift t := by
  cases k <;> ext i <;> fin_cases i <;>
    simp [coordinateShift, coordinateShiftLinear, fibreShift] <;> ring

private theorem screwLiftShear_fibre (l : ℝ) (x : ModelCoordinates) (t : ℝ) :
    shearMap l (x + fibreShift t) = shearMap l x + fibreShift t := by
  ext i
  fin_cases i <;> simp [shearMap]
  ring

private theorem screwLiftHyperInv_fibre (l : ℝ) (x : ModelCoordinates) (t : ℝ) :
    hyperboloidInv l (x + fibreShift t) = hyperboloidInv l x + fibreShift t := by
  ext i
  fin_cases i <;> simp [hyperboloidInv, hyperboloidHeight]
  ring

private theorem screwLiftHyperMap_fibre (l : ℝ) (x : ModelCoordinates) (t : ℝ) :
    hyperboloidMap l (x + fibreShift t) = hyperboloidMap l x + fibreShift t := by
  ext i
  fin_cases i <;> simp [hyperboloidMap]
  ring

private theorem screwLiftChart_fibre (m : ConnectionModel) (x : ModelCoordinates) (t : ℝ) :
    screwLiftChart m (x + fibreShift t) = screwLiftChart m x + fibreShift t := by
  cases m
  · exact screwLiftShear_fibre (-0) x t
  · rfl
  · exact screwLiftHyperInv_fibre 0 x t
  · exact screwLiftShear_fibre (-1) x t
  · exact screwLiftHyperInv_fibre 1 x t
  · rfl

private theorem screwLiftChart_symm_fibre (m : ConnectionModel)
    (x : ModelCoordinates) (t : ℝ) :
    (screwLiftChart m).symm (x + fibreShift t) =
      (screwLiftChart m).symm x + fibreShift t := by
  cases m
  · exact screwLiftShear_fibre 0 x t
  · rfl
  · exact screwLiftHyperMap_fibre 0 x t
  · exact screwLiftShear_fibre 1 x t
  · exact screwLiftHyperMap_fibre 1 x t
  · rfl

private theorem screwLiftNormalShift_fibre (m : ConnectionModel)
    (a b x : ModelCoordinates) (t : ℝ) :
    screwLiftNormalShift m a b (x + fibreShift t) =
      screwLiftNormalShift m a b x + fibreShift t := by
  cases m <;> first
    | exact screwLiftCoordinateShift_fibre _ a b x t
    | change (x + fibreShift t) + (b - a) = (x + (b - a)) + fibreShift t
      abel

private theorem recentre_add_fibreShift (m : ConnectionModel) (hm : m.baseCurvature ≤ 0)
    (v x : ModelCoordinates) (t : ℝ) :
    recentre m hm v (x + fibreShift t) = recentre m hm v x + fibreShift t := by
  rw [recentre_eq]
  change (screwLiftChart m).symm
    (screwLiftNormalShift m ((screwLiftChart m) 0) ((screwLiftChart m) v)
      (screwLiftChart m (x + fibreShift t))) = _
  rw [screwLiftChart_fibre, screwLiftNormalShift_fibre, screwLiftChart_symm_fibre]
  rfl

theorem recentre_fibreShift (m : ConnectionModel) (hm : m.baseCurvature ≤ 0)
    (v : ModelCoordinates) (t : ℝ) : recentre m hm v (fibreShift t) = v + fibreShift t := by
  simpa only [zero_add, recentre_zero] using recentre_add_fibreShift m hm v 0 t

def screwDiffeomorph (θ s : ℝ) :
    ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates :=
  MulAction.smulDiffeomorph (n := ∞) (𝓡 3) (⟨1⟩ : ScrewGroup θ s)

private theorem screwDiffeomorph_apply (θ s : ℝ) (x : ModelCoordinates) :
    screwDiffeomorph θ s x = planeRotation θ x + fibreShift s := by
  change planeRotation (θ * ((1 : ℤ) : ℝ)) x + fibreShift (s * ((1 : ℤ) : ℝ)) = _
  simp only [Int.cast_one, mul_one]

def fibreTranslation (s : ℝ) :
    ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates :=
  screwDiffeomorph 0 s

private theorem fibreTranslation_apply (s : ℝ) (x : ModelCoordinates) :
    fibreTranslation s x = x + fibreShift s := by
  rw [fibreTranslation, screwDiffeomorph_apply]
  congr 1
  ext i
  fin_cases i <;> simp

def screwGenerator (p : ℕ+) (a : ℤ) (ℓ : ℝ) :
    ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates :=
  screwDiffeomorph (2 * Real.pi * (-a) / p) (ℓ / p)

def screwAt (m : ConnectionModel) (hm : m.baseCurvature ≤ 0) (v : ModelCoordinates)
    (p : ℕ+) (q : ℤ) (ℓ : ℝ) :
    ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates :=
  let R := recentre m hm v
  R.symm.trans ((screwDiffeomorph (-2 * Real.pi / p) (-ℓ * q / p)).trans R)

private theorem screwLiftZpow (θ s : ℝ) (n : ℤ) :
    (⟨1⟩ : ScrewGroup θ s) ^ n = ⟨n⟩ := by
  induction n using Int.induction_on with
  | zero => rfl
  | succ n hn =>
    rw [zpow_add_one, hn]
    rfl
  | pred n hn =>
    rw [zpow_sub_one, hn]
    apply ScrewGroup.ext
    simp only [ScrewGroup.mul_shift, ScrewGroup.inv_shift]
    omega

theorem screwDiffeomorph_zpow (θ s : ℝ) (n : ℤ) :
    (screwDiffeomorph θ s).toEquiv ^ n =
      (screwDiffeomorph (θ * n) (s * n)).toEquiv := by
  change (MulAction.toPermHom (ScrewGroup θ s) ModelCoordinates ⟨1⟩) ^ n = _
  rw [← map_zpow, screwLiftZpow]
  apply Equiv.ext
  intro x
  change planeRotation (θ * n) x + fibreShift (s * n) = _
  exact (screwDiffeomorph_apply (θ * n) (s * n) x).symm

private theorem screwDiffeomorph_isometry (P : RadialProfile) (θ s : ℝ) :
    Diffeomorph.pullbackMetric P.metric (screwDiffeomorph θ s) = P.metric := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have hfun : (screwDiffeomorph θ s : ModelCoordinates → ModelCoordinates) =
      fun y => planeRotation θ y + fibreShift s :=
    funext (screwDiffeomorph_apply θ s)
  have hder : mfderiv (𝓡 3) (𝓡 3) (screwDiffeomorph θ s) x =
      (planeRotation θ : ModelCoordinates →L[ℝ] ModelCoordinates) := by
    rw [mfderiv_eq_fderiv, hfun]
    exact ((planeRotation θ).toContinuousLinearEquiv.hasFDerivAt.add_const _).fderiv
  rw [Diffeomorph.pullbackMetric_inner, hder, hfun]
  exact P.inner_rotation θ s x v w

theorem screwAt_isometry (m : ConnectionModel) (hm : m.baseCurvature ≤ 0)
    (v : ModelCoordinates) (p : ℕ+) (q : ℤ) (ℓ : ℝ) :
    Diffeomorph.pullbackMetric m.coneProfile.metric (screwAt m hm v p q ℓ) =
      m.coneProfile.metric := by
  rw [← Diffeomorph.pullbackMetricCross_eq_pullbackMetric]
  have hR : Diffeomorph.pullbackMetricCross m.coneProfile.metric (recentre m hm v) =
      m.coneProfile.metric := by
    rw [Diffeomorph.pullbackMetricCross_eq_pullbackMetric]
    exact recentre_isometry m hm v
  have hB : Diffeomorph.pullbackMetricCross m.coneProfile.metric
      (screwDiffeomorph (-2 * Real.pi / p) (-ℓ * q / p)) = m.coneProfile.metric := by
    rw [Diffeomorph.pullbackMetricCross_eq_pullbackMetric]
    exact screwDiffeomorph_isometry _ _ _
  have hRinv := Diffeomorph.pullbackMetricCross_symm_eq_iff.mp hR
  unfold screwAt
  rw [← Diffeomorph.pullbackMetricCross_trans, ← Diffeomorph.pullbackMetricCross_trans,
    hR, hB, hRinv]

private theorem screwLiftPeriodic (θ s : ℝ) (n : ℤ) :
    (screwDiffeomorph (θ + n * (2 * Real.pi)) s).toEquiv =
      (screwDiffeomorph θ s).toEquiv := by
  apply Equiv.ext
  intro x
  change screwDiffeomorph (θ + n * (2 * Real.pi)) s x = screwDiffeomorph θ s x
  apply modelCoordinates_ext
  · simp only [screwDiffeomorph_apply,
      planeOf_add_fibreShift, planeOf_planeRotation]
    rw [Circle.exp_add, Circle.exp_int_mul_two_pi, mul_one]
  · simp only [screwDiffeomorph_apply,
      PiLp.add_apply, planeRotation_apply_two, fibreShift_apply_two]

private theorem screwLiftFullRotation (n : ℤ) (s : ℝ) :
    (screwDiffeomorph (n * (2 * Real.pi)) s).toEquiv = (fibreTranslation s).toEquiv := by
  simpa only [zero_add, fibreTranslation] using screwLiftPeriodic 0 s n

private theorem recentre_conj_fibreTranslation (m : ConnectionModel)
    (hm : m.baseCurvature ≤ 0) (v : ModelCoordinates) (t : ℝ) :
    (MulAut.conj (recentre m hm v).toEquiv) (fibreTranslation t).toEquiv =
      (fibreTranslation t).toEquiv := by
  apply Equiv.ext
  intro x
  change recentre m hm v (fibreTranslation t ((recentre m hm v).symm x)) =
    fibreTranslation t x
  rw [fibreTranslation_apply, recentre_add_fibreShift, Diffeomorph.apply_symm_apply,
    fibreTranslation_apply]

private theorem screwAt_conj (m : ConnectionModel) (hm : m.baseCurvature ≤ 0)
    (v : ModelCoordinates) (p : ℕ+) (q : ℤ) (ℓ : ℝ) :
    (screwAt m hm v p q ℓ).toEquiv = (MulAut.conj (recentre m hm v).toEquiv)
      (screwDiffeomorph (-2 * Real.pi / p) (-ℓ * q / p)).toEquiv := by
  apply Equiv.ext
  intro x
  rfl

private theorem screwLiftBase_pow (p : ℕ+) (q : ℤ) (ℓ : ℝ) :
    (screwDiffeomorph (-2 * Real.pi / p) (-ℓ * q / p)).toEquiv ^ (p : ℕ) =
      (fibreTranslation (-ℓ * q)).toEquiv := by
  rw [← zpow_natCast, screwDiffeomorph_zpow]
  have hp : (p : ℝ) ≠ 0 := by positivity
  have hθ : (-2 * Real.pi / (p : ℝ)) * (p : ℤ) = (-1 : ℤ) * (2 * Real.pi) := by
    push_cast
    field_simp
  have hs : (-ℓ * q / (p : ℝ)) * (p : ℤ) = -ℓ * q := by
    push_cast
    field_simp
  rw [hθ, hs]
  exact screwLiftFullRotation (-1) (-ℓ * q)

theorem screwAt_pow (m : ConnectionModel) (hm : m.baseCurvature ≤ 0)
    (v : ModelCoordinates) (p : ℕ+) (q : ℤ) (ℓ : ℝ) :
    (screwAt m hm v p q ℓ).toEquiv ^ (p : ℕ) =
      (fibreTranslation (-ℓ * q)).toEquiv := by
  rw [screwAt_conj, ← map_pow, screwLiftBase_pow, recentre_conj_fibreTranslation]

private theorem screwLiftBase_commute (θ s t : ℝ) :
    Commute (screwDiffeomorph θ s).toEquiv (fibreTranslation t).toEquiv := by
  change (screwDiffeomorph θ s).toEquiv * (fibreTranslation t).toEquiv =
    (fibreTranslation t).toEquiv * (screwDiffeomorph θ s).toEquiv
  apply Equiv.ext
  intro x
  change screwDiffeomorph θ s (fibreTranslation t x) =
    fibreTranslation t (screwDiffeomorph θ s x)
  rw [fibreTranslation_apply, screwDiffeomorph_apply, screwDiffeomorph_apply,
    fibreTranslation_apply]
  ext i
  fin_cases i <;> simp
  ring

theorem screwAt_commute (m : ConnectionModel) (hm : m.baseCurvature ≤ 0)
    (v : ModelCoordinates) (p : ℕ+) (q : ℤ) (ℓ t : ℝ) :
    Function.Commute (screwAt m hm v p q ℓ) (fibreTranslation t) := by
  have h := (screwLiftBase_commute (-2 * Real.pi / p) (-ℓ * q / p) t).map
    (MulAut.conj (recentre m hm v).toEquiv)
  rw [recentre_conj_fibreTranslation, ← screwAt_conj] at h
  intro x
  exact congrArg (fun e : Equiv.Perm ModelCoordinates => e x) h.eq

private theorem screwGenerator_pow (p : ℕ+) (a : ℤ) (ℓ : ℝ) :
    (screwGenerator p a ℓ).toEquiv ^ (p : ℕ) = (fibreTranslation ℓ).toEquiv := by
  unfold screwGenerator
  rw [← zpow_natCast, screwDiffeomorph_zpow]
  have hp : (p : ℝ) ≠ 0 := by positivity
  have hθ : (2 * Real.pi * (-a) / (p : ℝ)) * (p : ℤ) =
      (-a : ℤ) * (2 * Real.pi) := by
    push_cast
    field_simp
  have hs : (ℓ / (p : ℝ)) * (p : ℤ) = ℓ := by
    push_cast
    field_simp
  rw [hθ, hs]
  exact screwLiftFullRotation (-a) ℓ

private theorem screwLiftBezoutAlgebra {G : Type*} [Group G] (u h : G)
    (p : ℕ+) (q a b : ℤ) (hu : u ^ (p : ℕ) = h)
    (hpb : (p : ℤ) * b - a * q = 1) :
    (u ^ (-q)) ^ (p : ℕ) = h ^ (-q) ∧ (u ^ (-q)) ^ a * h ^ b = u ∧
      Subgroup.closure ({u ^ (-q), h} : Set G) = Subgroup.zpowers u := by
  have huz : u ^ (p : ℤ) = h := by simpa only [zpow_natCast] using hu
  have hpower : (u ^ (-q)) ^ (p : ℕ) = h ^ (-q) := by
    rw [← zpow_natCast, ← huz, ← zpow_mul, ← zpow_mul]
    congr 1
    ring
  have hlongitude : (u ^ (-q)) ^ a * h ^ b = u := by
    rw [← huz, ← zpow_mul, ← zpow_mul, ← zpow_add]
    have he : (-q) * a + (p : ℤ) * b = 1 := by nlinarith [hpb]
    rw [he, zpow_one]
  refine ⟨hpower, hlongitude, le_antisymm ?_ ?_⟩
  · apply (Subgroup.closure_le (Subgroup.zpowers u)).mpr
    intro z hz
    rcases Set.mem_insert_iff.mp hz with rfl | hz
    · exact Subgroup.mem_zpowers_iff.mpr ⟨-q, rfl⟩
    · have he : z = h := Set.mem_singleton_iff.mp hz
      subst z
      exact Subgroup.mem_zpowers_iff.mpr ⟨p, huz⟩
  · apply Subgroup.zpowers_le.mpr
    let K := Subgroup.closure ({u ^ (-q), h} : Set G)
    have hc : u ^ (-q) ∈ K := Subgroup.subset_closure (Or.inl rfl)
    have hh : h ∈ K := Subgroup.subset_closure (Or.inr rfl)
    have hmem := K.mul_mem (K.zpow_mem hc a) (K.zpow_mem hh b)
    simpa only [hlongitude] using hmem

private theorem screwLiftClockwise (p : ℕ+) (q a b : ℤ) (ℓ : ℝ)
    (hpb : (p : ℤ) * b - a * q = 1) :
    (screwGenerator p a ℓ).toEquiv ^ (-q) =
      (screwDiffeomorph (-2 * Real.pi / p) (-ℓ * q / p)).toEquiv := by
  unfold screwGenerator
  rw [screwDiffeomorph_zpow]
  have hp : (p : ℝ) ≠ 0 := by positivity
  have hpbR : (p : ℝ) * b - (a : ℝ) * q = 1 := by exact_mod_cast hpb
  have hθ : (2 * Real.pi * (-a) / (p : ℝ)) * (-q) =
      -2 * Real.pi / p + (b : ℝ) * (2 * Real.pi) := by
    field_simp
    nlinarith only [hpbR]
  have hs : (ℓ / (p : ℝ)) * (-q) = -ℓ * q / p := by
    ring
  simp only [Int.cast_neg]
  rw [hθ, hs]
  exact screwLiftPeriodic (-2 * Real.pi / p) (-ℓ * q / p) b

theorem screwBezout (m : ConnectionModel) (hm : m.baseCurvature ≤ 0)
    (v : ModelCoordinates) (p : ℕ+) (q a b : ℤ) (ℓ : ℝ)
    (hpb : (p : ℤ) * b - a * q = 1) :
    let u := (screwGenerator p a ℓ).toEquiv
    let h := (fibreTranslation ℓ).toEquiv
    let c := u ^ (-q)
    u ^ (p : ℕ) = h ∧ c ^ (p : ℕ) = h ^ (-q) ∧ c ^ a * h ^ b = u ∧
      Subgroup.closure ({c, h} : Set (Equiv.Perm ModelCoordinates)) = Subgroup.zpowers u ∧
        (screwAt m hm v p q ℓ).toEquiv = (MulAut.conj (recentre m hm v).toEquiv) c := by
  dsimp only
  have hu := screwGenerator_pow p a ℓ
  obtain ⟨hpower, hlongitude, hsubgroup⟩ :=
    screwLiftBezoutAlgebra (screwGenerator p a ℓ).toEquiv (fibreTranslation ℓ).toEquiv
      p q a b hu hpb
  refine ⟨hu, hpower, hlongitude, hsubgroup, ?_⟩
  rw [screwLiftClockwise p q a b ℓ hpb, screwAt_conj]

private instance screwLiftStep_ne_zero (p : ℕ+) (ℓ : ℝ) [Fact (0 < ℓ)] :
    Fact (ℓ / (p : ℝ) ≠ 0) :=
  ⟨ne_of_gt (div_pos (Fact.out : 0 < ℓ) (by positivity))⟩

def scaledScrewTubeDiffeomorph (p : ℕ+) (a : ℤ) (ℓ : ℝ) [Fact (0 < ℓ)] :
    ScrewQuotient (2 * Real.pi * (-a) / p) (ℓ / p)
      ≃ₘ⟮𝓡 3, 𝓘(ℝ, ℂ).prod (𝓡 1)⟯ openUnitDisc × Circle :=
  (ScrewGroup.untwistDiffeo _ _).trans
    (discDiffeo.prodCongr (Diffeomorph.refl (𝓡 1) Circle ∞))

theorem scaledScrewTubeDiffeomorph_mk (p : ℕ+) (a : ℤ) (ℓ : ℝ) [Fact (0 < ℓ)]
    (x : ModelCoordinates) :
    scaledScrewTubeDiffeomorph p a ℓ (Quotient.mk'' x) =
      (discDiffeo ((Circle.exp (2 * Real.pi * a * x 2 / ℓ) : ℂ) * planeOf x),
        Circle.exp (2 * Real.pi * p * x 2 / ℓ)) := by
  have hp : (p : ℝ) ≠ 0 := by positivity
  have hℓ : ℓ ≠ 0 := ne_of_gt (Fact.out : 0 < ℓ)
  change (discDiffeo (ScrewGroup.untwist (2 * Real.pi * (-a) / p) (ℓ / p) x).1,
    (ScrewGroup.untwist (2 * Real.pi * (-a) / p) (ℓ / p) x).2) = _
  simp only [ScrewGroup.untwist]
  have hphase : -(2 * Real.pi * -(a : ℝ) / (p : ℝ) * x 2 / (ℓ / p)) =
      2 * Real.pi * a * x 2 / ℓ := by
    push_cast
    field_simp
  have hcircle : 2 * Real.pi * x 2 / (ℓ / (p : ℝ)) =
      2 * Real.pi * p * x 2 / ℓ := by
    field_simp
  rw [hphase, hcircle]

private theorem screwLiftDisc_phase (c : Circle) (w : ℂ) :
    discMap ((c : ℂ) * w) = (c : ℂ) * discMap w := by
  simp only [discMap, norm_mul, Circle.norm_coe, one_mul]
  rw [mul_smul_comm]

theorem scaledScrewTube_fibre (p : ℕ+) (a : ℤ) (ℓ : ℝ) [Fact (0 < ℓ)]
    (x : ModelCoordinates) (t : ℝ) :
    let T := fun y : ModelCoordinates => scaledScrewTubeDiffeomorph p a ℓ (Quotient.mk'' y)
    ((T (x + fibreShift t)).1 : ℂ) =
      (Circle.exp (2 * Real.pi * a * t / ℓ) : ℂ) * ((T x).1 : ℂ) ∧
      (T (x + fibreShift t)).2 = Circle.exp (2 * Real.pi * p * t / ℓ) * (T x).2 := by
  dsimp only
  rw [scaledScrewTubeDiffeomorph_mk, scaledScrewTubeDiffeomorph_mk]
  simp only [discDiffeo_apply_coe, planeOf_add_fibreShift]
  have hz : (x + fibreShift t) 2 = x 2 + t := by simp [fibreShift]
  rw [hz]
  have ha : 2 * Real.pi * a * (x 2 + t) / ℓ =
      2 * Real.pi * a * t / ℓ + 2 * Real.pi * a * x 2 / ℓ := by ring
  have hp : 2 * Real.pi * p * (x 2 + t) / ℓ =
      2 * Real.pi * p * t / ℓ + 2 * Real.pi * p * x 2 / ℓ := by ring
  rw [ha, hp, Circle.exp_add, Circle.exp_add, Circle.coe_mul, mul_assoc]
  exact ⟨screwLiftDisc_phase _ _, rfl⟩

theorem screwMark_basis (p : ℕ+) (q a b : ℤ) (ℓ : ℝ)
    (hpb : (p : ℤ) * b - a * q = 1) :
    let u := (screwGenerator p a ℓ).toEquiv
    let h := (fibreTranslation ℓ).toEquiv
    let c := u ^ (-q)
    Matrix.mulVec (!![-(p : ℤ), a; -q, b]) ![(1 : ℤ), 0] = ![-(p : ℤ), -q] ∧
      Matrix.mulVec (!![-(p : ℤ), a; -q, b]) ![(0 : ℤ), 1] = ![a, b] ∧
        c ^ (-(p : ℤ)) * h ^ (-q) = 1 ∧ c ^ a * h ^ b = u := by
  dsimp only
  have hu := screwGenerator_pow p a ℓ
  obtain ⟨hpower, hlongitude, hsubgroup⟩ :=
    screwLiftBezoutAlgebra (screwGenerator p a ℓ).toEquiv (fibreTranslation ℓ).toEquiv
      p q a b hu hpb
  refine ⟨?_, ?_, ?_, hlongitude⟩
  · ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · have huz : (screwGenerator p a ℓ).toEquiv ^ (p : ℤ) =
        (fibreTranslation ℓ).toEquiv := by simpa only [zpow_natCast] using hu
    rw [← huz, ← zpow_mul, ← zpow_mul, ← zpow_add]
    have he : (-q) * (-(p : ℤ)) + (p : ℤ) * (-q) = 0 := by ring
    rw [he, zpow_zero]

theorem screwLift_regressions :
    (2 : ℤ) * 1 - 1 * 1 = 1 ∧ (3 : ℤ) * 1 - 2 * 1 = 1 ∧
      (3 : ℤ) * 1 - 1 * 2 = 1 ∧ (5 : ℤ) * 1 - 2 * 2 = 1 ∧
        (-2 : ℤ) % 5 = 3 ∧ (3 : ℤ) ≠ 2 := by
  norm_num

end GC.Geometry
