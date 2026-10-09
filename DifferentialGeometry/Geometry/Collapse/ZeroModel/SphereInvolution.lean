import DifferentialGeometry.Geometry.Curvature.Surface.PositiveCurvatureSphere
import DifferentialGeometry.Geometry.Metric.Sphere.Isometry.Representation
import DifferentialGeometry.Topology.Manifold.SmoothOrientationCompatible

/-!
# Free isometric involutions of a positively curved closed surface

Lane LFR54-Q0, group G4 (the sphere case of Q0). Let `S` be a compact connected oriented surface
with a smooth metric `g` of positive scalar curvature and `τ` a smooth free involution of `S` which
is an isometry of `g`. Then there is a diffeomorphism `Φ : S² → S` with `Φ (-x) = τ (Φ x)`
(`exists_antipodal_diffeomorph_of_scalar_pos_involution`).

Route (all classical inputs are in the tree):
1. Synge (`ClosedSurface.simplyConnectedSpace_of_scalar_pos`): `S` is simply connected.
2. The surface Ricci flow theorem U1 in its isometry-invariant form
   (`GC.Geometry.exists_isometryInvariant_roundMetric_proved`) gives a metric `h₁` of curvature one
   for which `τ` is still an isometry (transported to the Morse-model charts).
3. The simply connected space form theorem gives an isometry `Φ` of `(S, h₁)` with the round `S²`;
   `σ = Φ τ Φ⁻¹` is a round isometry, hence orthogonal
   (`exists_linearIsometryEquiv_of_localPullMetric_roundMetric_eq`).
4. An orthogonal map which is a fixed-point free involution of the unit sphere is `-1`
   (`linearIsometryEquiv_apply_eq_neg_of_involutive_of_fixedPoint_free`).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Function Metric Module
open scoped Manifold ContDiff Topology
open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Topology.Morse

namespace DifferentialGeometry.Geometry.Collapse.ZeroModel

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "MM2" => DifferentialGeometry.Topology.Morse.MorseModel 2

/-- An orthogonal map which is an involution on unit vectors and fixes no unit vector is `-1` on
unit vectors. -/
theorem linearIsometryEquiv_apply_eq_neg_of_involutive_of_fixedPoint_free {W : Type*}
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] (e : W ≃ₗᵢ[ℝ] W)
    (hinv : ∀ x : W, ‖x‖ = 1 → e (e x) = x) (hfree : ∀ x : W, ‖x‖ = 1 → e x ≠ x)
    (x : W) (hx : ‖x‖ = 1) : e x = -x := by
  by_contra hne
  have hy0 : x + e x ≠ 0 := fun h => hne (eq_neg_of_add_eq_zero_right h)
  have hey : e (x + e x) = x + e x := by rw [map_add, hinv x hx, add_comm]
  have hn : ‖(‖x + e x‖⁻¹ • (x + e x))‖ = 1 := by
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hy0)]
  apply hfree _ hn
  rw [map_smul, hey]

variable {S : Type*} [TopologicalSpace S] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) S]
  [IsManifold (𝓡 2) ∞ S] [T2Space S] [CompactSpace S] [ConnectedSpace S]

/-- **G4 (T7).** A free isometric involution of a compact connected oriented surface with a smooth
metric of positive scalar curvature is conjugate to the antipodal map of the round `S²`. -/
theorem exists_antipodal_diffeomorph_of_scalar_pos_involution (o : SmoothOrientation (𝓡 2) S)
    (g : SmoothRiemannianMetric (𝓡 2) S) (hscal : ∀ x, 0 < metricScalarAt g x)
    (τ : S → S) (hτ : ContMDiff (𝓡 2) (𝓡 2) ∞ τ) (hτinv : ∀ x, τ (τ x) = x)
    (hτfree : ∀ x, τ x ≠ x)
    (hτiso : ∀ x (v w : TangentSpace (𝓡 2) x),
      g.inner (τ x) (mfderiv (𝓡 2) (𝓡 2) τ x v) (mfderiv (𝓡 2) (𝓡 2) τ x w) = g.inner x v w) :
    ∃ Φ : Metric.sphere (0 : E3) 1 ≃ₘ⟮𝓡 2, 𝓡 2⟯ S, ∀ x, Φ (-x) = τ (Φ x) := by
  -- Synge: `S` is simply connected
  obtain ⟨O, -⟩ := exists_manifoldOrientation_eq_of_smoothOrientation (𝓡 2) o
  let O2 : ManifoldOrientation (𝓡 2) S 2 :=
    Eq.rec (motive := fun m _ => ManifoldOrientation (𝓡 2) S m) O finrank_euclideanSpace_fin
  have hsc : SimplyConnectedSpace S := ClosedSurface.simplyConnectedSpace_of_scalar_pos O2 g hscal
  -- `τ` as an isometric diffeomorphism
  let τD : S ≃ₘ⟮𝓡 2, 𝓡 2⟯ S :=
    { toEquiv := ⟨τ, τ, hτinv, hτinv⟩, contMDiff_toFun := hτ, contMDiff_invFun := hτ }
  have hτD : Diffeomorph.pullbackMetric g τD = g := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [Diffeomorph.pullbackMetric_inner]
    exact hτiso x v w
  -- the Morse-model charts
  let _ := euclideanModelMorseModelChartedSpace 2 S
  have hMM : IsManifold 𝓘(ℝ, MM2) ∞ S := isManifold_euclideanModelMorseModel (n := 2) (M := S)
  let Ψ : S ≃ₘ⟮𝓘(ℝ, MM2), 𝓡 2⟯ S := euclideanModelMorseModelDiffeomorph
  have hscal' : ∀ x, 0 < metricScalarAt (Diffeomorph.pullbackMetricCross g Ψ) x := fun x => by
    rw [DifferentialGeometry.CheegerGromovCompactness.metricScalar_cross g Ψ x]
    exact hscal _
  let τN : S ≃ₘ⟮𝓘(ℝ, MM2), 𝓘(ℝ, MM2)⟯ S := Ψ.trans (τD.trans Ψ.symm)
  have hτN : Diffeomorph.pullbackMetric (Diffeomorph.pullbackMetricCross g Ψ) τN =
      Diffeomorph.pullbackMetricCross g Ψ := by
    have he : τN.trans Ψ = Ψ.trans τD := Diffeomorph.ext fun x => Ψ.apply_symm_apply _
    rw [← Diffeomorph.pullbackMetricCross_eq_pullbackMetric, Diffeomorph.pullbackMetricCross_trans,
      he, ← Diffeomorph.pullbackMetricCross_trans,
      Diffeomorph.pullbackMetricCross_eq_pullbackMetric g τD, hτD]
  -- U1: an isometry-invariant round metric, and the space form isometry
  obtain ⟨h₁, hsec₁, hinv₁⟩ :=
    GC.Geometry.exists_isometryInvariant_roundMetric_proved (Diffeomorph.pullbackMetricCross g Ψ)
      hscal'
  have hτN₁ := hinv₁ τN hτN
  obtain ⟨Φ, hΦ⟩ := exists_isometry_round_sphere_of_constant_positive_sectional_curvature
    (I := 𝓘(ℝ, MM2)) (M := S) (n := 2) (by norm_num) (by simp) h₁ 1 one_pos hsec₁
  let _ : Fact (finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
  have hΦm : Diffeomorph.pullbackMetricCross (roundMetric (E := E3) (n := 2)) Φ = h₁ := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [Diffeomorph.pullbackMetricCross_inner, hΦ x v w, one_mul]
  -- the conjugated involution is a round isometry, hence `-1`
  let σ : Metric.sphere (0 : E3) 1 ≃ₘ⟮𝓡 2, 𝓡 2⟯ Metric.sphere (0 : E3) 1 :=
    Φ.symm.trans (τN.trans Φ)
  have hσm : Diffeomorph.pullbackMetric (roundMetric (E := E3) (n := 2)) σ = roundMetric := by
    rw [← Diffeomorph.pullbackMetricCross_eq_pullbackMetric, ← Diffeomorph.pullbackMetricCross_trans,
      ← Diffeomorph.pullbackMetricCross_trans, hΦm,
      Diffeomorph.pullbackMetricCross_eq_pullbackMetric h₁ τN, hτN₁, ← hΦm,
      Diffeomorph.pullbackMetricCross_trans, Diffeomorph.symm_trans_self,
      Diffeomorph.pullbackMetricCross_refl]
  have hσl : localPullMetric (roundMetric (E := E3) (n := 2)) σ σ.isLocalDiffeomorph =
      roundMetric := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    have hx := congrArg (fun m : SmoothRiemannianMetric (𝓡 2) (Metric.sphere (0 : E3) 1) =>
      m.inner x v w) hσm
    simp only [Diffeomorph.pullbackMetric_inner] at hx
    rw [localPullMetric_inner]
    exact hx
  obtain ⟨e, he⟩ := exists_linearIsometryEquiv_of_localPullMetric_roundMetric_eq (E := E3) (n := 2)
    (by norm_num) σ.isLocalDiffeomorph hσl
  have hσ : ∀ x, σ x = Φ (τ (Φ.symm x)) := fun x => rfl
  have heσ : ∀ x : Metric.sphere (0 : E3) 1, e (x : E3) = (σ x : E3) := fun x => by
    rw [← he]
    rfl
  have heneg : ∀ x : Metric.sphere (0 : E3) 1, σ x = -x := by
    intro x
    apply Subtype.ext
    rw [← heσ, coe_neg_sphere]
    refine linearIsometryEquiv_apply_eq_neg_of_involutive_of_fixedPoint_free e ?_ ?_ x
      (mem_sphere_zero_iff_norm.mp x.property)
    · intro y hy
      let y' : Metric.sphere (0 : E3) 1 := ⟨y, mem_sphere_zero_iff_norm.mpr hy⟩
      have h1 := heσ y'
      have h2 := heσ (σ y')
      rw [← h1] at h2
      rw [h2, hσ, hσ, Φ.symm_apply_apply, hτinv, Φ.apply_symm_apply]
    · intro y hy hfix
      let y' : Metric.sphere (0 : E3) 1 := ⟨y, mem_sphere_zero_iff_norm.mpr hy⟩
      have h1 := heσ y'
      rw [hfix] at h1
      have h3 : σ y' = y' := (Subtype.ext h1).symm
      rw [hσ] at h3
      apply hτfree (Φ.symm y')
      apply Φ.injective
      exact h3.trans (Φ.apply_symm_apply y').symm
  -- the conjugating diffeomorphism
  refine ⟨Φ.symm.trans Ψ, fun x => ?_⟩
  have hx : -x = Φ (τ (Φ.symm x)) := (heneg x).symm.trans (hσ x)
  change Ψ (Φ.symm (-x)) = τ (Ψ (Φ.symm x))
  rw [hx, Φ.symm_apply_apply]
  rfl

end DifferentialGeometry.Geometry.Collapse.ZeroModel
