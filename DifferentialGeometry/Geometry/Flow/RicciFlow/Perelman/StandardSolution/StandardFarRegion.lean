import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardCylinderSliceConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.CylinderAxialNormalization
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.NeckSpatialBridge
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.StandardCap.Distance
import DifferentialGeometry.Geometry.Neck.ScalarNormalization
import DifferentialGeometry.Geometry.Metric.BilinearPerturbation
import DifferentialGeometry.Geometry.Metric.Convergence.Scaling
import DifferentialGeometry.Geometry.Metric.Convergence.DerivativeNorm.Restriction
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Topology.Manifold.OpenSubtype

set_option autoImplicit false
noncomputable section
open Set Filter Function Manifold
open scoped Manifold ContDiff Topology ENNReal InnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Neck
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.PDE.RicciFlow.StandardCap
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

private abbrev E3 := EuclideanSpace ℝ (Fin 3)
private abbrev S2 := Metric.sphere (0 : E3) 1
private abbrev IC := (𝓡 2).prod 𝓘(ℝ)
private local instance : Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩
private local instance (δ : ℝ) : SigmaCompactSpace (bufferedCylinder δ) :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen IC (bufferedCylinder δ).isOpen)

private theorem scale_pullback_shrinkingCylinderMetric {s : ℝ} (hs : s < 1) :
    scaleMetric (1 - s)⁻¹ (inv_pos.mpr (sub_pos.mpr hs))
      (Diffeomorph.pullbackMetricCross (shrinkingCylinderMetric (E := E3) s)
        (cylinderAxialScale (Real.sqrt (1 - s)) (Real.sqrt_pos.mpr (sub_pos.mpr hs)).ne')) =
      roundCylinderMetric (E := E3) (n := 2) := by
  apply SmoothRiemannianMetric.ext_inner
  intro z v w
  have h1 : (0 : ℝ) < 1 - s := sub_pos.mpr hs
  rw [scaleMetric_inner, Diffeomorph.pullbackMetricCross_inner, cylinderAxialScale_mfderiv,
    cylinderAxialScale_mfderiv, cylinderAxialScale_apply]
  erw [shrinkingCylinderMetric_inner hs, roundCylinderMetric_inner, Geometry.roundMetric_inner]
  have hsq : Real.sqrt (1 - s) ^ 2 = 1 - s := Real.sq_sqrt h1.le
  field_simp
  rw [hsq]
  ring

private theorem inner_smul_left (g : SmoothRiemannianMetric (𝓡 3) E3) (y : E3) (a : ℝ)
    (v w : E3) : g.inner y (a • v) w = a * g.inner y v w := by
  have h := (g.inner y).map_smul a v
  exact DFunLike.congr_fun h w

private theorem inner_smul_right (g : SmoothRiemannianMetric (𝓡 3) E3) (y : E3) (a : ℝ)
    (v w : E3) : g.inner y v (a • w) = a * g.inner y v w :=
  (g.inner y v).map_smul a w

private theorem mfderiv_apply_mfderiv_symm_of_mem_source
    (F : PartialDiffeomorph IC (𝓡 3) (S2 × ℝ) E3 ∞) {z : S2 × ℝ} (hz : z ∈ F.source)
    (v : E3) :
    mfderiv IC (𝓡 3) F z (mfderiv (𝓡 3) IC F.symm (F z) v) = v := by
  have hp : F z ∈ F.target := F.toPartialEquiv.map_source hz
  have hsym : F.symm (F z) = z := F.toPartialEquiv.left_inv hz
  have hsd : MDifferentiableAt (𝓡 3) IC F.symm (F z) := F.symm.mdifferentiableAt (by simp) hp
  have hFd : MDifferentiableAt IC (𝓡 3) F (F.symm (F z)) := by
    rw [hsym]
    exact F.mdifferentiableAt (by simp) hz
  have hcomp := mfderiv_comp (F z) hFd hsd
  have heq : ((F : S2 × ℝ → E3) ∘ (F.symm : E3 → S2 × ℝ)) =ᶠ[𝓝 (F z)] id := by
    filter_upwards [F.open_target.mem_nhds hp] with y hy
    exact F.toPartialEquiv.right_inv hy
  rw [heq.mfderiv_eq, mfderiv_id] at hcomp
  have h := DFunLike.congr_fun hcomp v
  change v = mfderiv IC (𝓡 3) F (F.symm (F z)) (mfderiv (𝓡 3) IC F.symm (F z) v) at h
  have key : ∀ z' : S2 × ℝ, F.symm (F z) = z' →
      mfderiv IC (𝓡 3) F z' (mfderiv (𝓡 3) IC F.symm (F z) v) = v := by
    rintro z' rfl
    exact h.symm
  exact key z hsym

private theorem polar_center (x : E3) :
    initialPolarDiffeomorph (pointedInitialRotation x) ‖x‖ ((spherePoint : S2), (0 : ℝ)) = x :=
  pointedInitialRotation_center x

private theorem polar_source {x : E3} {z : S2 × ℝ} (hz : -‖x‖ < z.2) :
    z ∈ (initialPolarDiffeomorph (pointedInitialRotation x) ‖x‖).source := by
  rw [initialPolarDiffeomorph_source]
  change 0 < ‖x‖ + z.2
  linarith

private theorem polar_axial_mfderiv {x : E3} (hx : 0 < ‖x‖) :
    mfderiv IC (𝓡 3) (initialPolarDiffeomorph (pointedInitialRotation x) ‖x‖)
      ((spherePoint : S2), (0 : ℝ)) ((0 : EuclideanSpace ℝ (Fin 2)), (1 : ℝ)) =
      pointedInitialRotation x ((spherePoint : S2) : E3) := by
  set P := initialPolarDiffeomorph (pointedInitialRotation x) ‖x‖ with hP
  set w : E3 := pointedInitialRotation x ((spherePoint : S2) : E3) with hw
  have hsrc : ((spherePoint : S2), (0 : ℝ)) ∈ P.source :=
    polar_source (by change -‖x‖ < 0; linarith)
  have hFd : HasMFDerivAt IC (𝓡 3) P ((spherePoint : S2), (0 : ℝ))
      (mfderiv IC (𝓡 3) P ((spherePoint : S2), (0 : ℝ))) :=
    (P.mdifferentiableAt (by simp) hsrc).hasMFDerivAt
  have hγ : HasMFDerivAt 𝓘(ℝ) IC (fun a : ℝ => ((spherePoint : S2), a)) 0
      ((0 : ℝ →L[ℝ] EuclideanSpace ℝ (Fin 2)).prod (ContinuousLinearMap.id ℝ ℝ)) :=
    (hasMFDerivAt_const (I := 𝓘(ℝ)) (I' := 𝓡 2) (spherePoint : S2) (0 : ℝ)).prodMk
      (hasMFDerivAt_id (I := 𝓘(ℝ)) (0 : ℝ))
  have hcurve : (P : S2 × ℝ → E3) ∘ (fun a : ℝ => ((spherePoint : S2), a)) =
      fun a : ℝ => (‖x‖ + a) • w := by
    funext a
    exact initialPolarDiffeomorph_apply _ _ _
  have hline : HasFDerivAt (fun a : ℝ => (‖x‖ + a) • w)
      ((ContinuousLinearMap.id ℝ ℝ).smulRight w) 0 :=
    ((hasFDerivAt_id (0 : ℝ)).const_add ‖x‖).smul_const w
  have hcomp := hFd.comp (0 : ℝ) hγ
  rw [hcurve] at hcomp
  have h := DFunLike.congr_fun (hcomp.mfderiv.symm.trans hline.hasMFDerivAt.mfderiv) (1 : ℝ)
  change mfderiv IC (𝓡 3) P ((spherePoint : S2), (0 : ℝ))
    ((0 : EuclideanSpace ℝ (Fin 2)), (1 : ℝ)) = (1 : ℝ) • w at h
  rw [one_smul] at h
  exact h

private theorem radial_bounds_core {s θ : ℝ} (hs : s < 1) (hθ : θ < 1)
    (g : SmoothRiemannianMetric (𝓡 3) E3) {x w : E3} (hxw : x = ‖x‖ • w)
    (G : SmoothRiemannianMetric IC (S2 × ℝ)) (P : PartialDiffeomorph IC (𝓡 3) (S2 × ℝ) E3 ∞)
    {z0 : S2 × ℝ} (hsrc : z0 ∈ P.source) (hPz0 : P z0 = x)
    (u0 : TangentSpace IC z0) (hdF : mfderiv IC (𝓡 3) P z0 u0 = w)
    (hsh1 : (shrinkingCylinderMetric (E := E3) s).inner z0 u0 u0 = 1)
    (hmet : ∀ u : TangentSpace IC z0,
      StandardCap.metric.inner x w (mfderiv IC (𝓡 3) P z0 u) = u.2)
    (hG : ∀ v w : TangentSpace IC z0, G.inner z0 v w =
      g.inner (P z0) (mfderiv IC (𝓡 3) P z0 v) (mfderiv IC (𝓡 3) P z0 w))
    (hclose : metricDerivNorm 0 G (shrinkingCylinderMetric (E := E3) s)
      (shrinkingCylinderMetric (E := E3) s) z0 ≤ θ) :
    (∀ v : E3, ⟪x, v⟫_ℝ ^ 2 * (1 - θ) ≤ ‖x‖ ^ 2 * g.inner x v v) ∧
      g.inner x x x ≤ (1 + θ) * ‖x‖ ^ 2 := by
  have hθ' : 0 ≤ 1 - θ := by linarith
  have hbd : ∀ v : TangentSpace IC z0,
      (1 - θ) * (shrinkingCylinderMetric (E := E3) s).inner z0 v v ≤ G.inner z0 v v ∧
        G.inner z0 v v ≤ (1 + θ) * (shrinkingCylinderMetric (E := E3) s).inner z0 v v :=
    fun v => inner_bounds_of_metricDerivNorm_le (shrinkingCylinderMetric (E := E3) s) G z0
      hclose v
  have hsh : ∀ u : TangentSpace IC z0, u.2 ^ 2 ≤
      (shrinkingCylinderMetric (E := E3) s).inner z0 u u := by
    intro u
    erw [shrinkingCylinderMetric_inner hs]
    have hr := metric_inner_self_nonneg (Geometry.roundMetric (E := E3) (n := 2)) z0.1 u.1
    have h1 : 0 ≤ 1 - s := by linarith
    have h2 := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) h1) hr
    rw [sq]
    linarith
  refine ⟨fun v => ?_, ?_⟩
  · obtain ⟨u, hinv⟩ : ∃ u : TangentSpace IC z0, mfderiv IC (𝓡 3) P z0 u = v :=
      ⟨_, mfderiv_apply_mfderiv_symm_of_mem_source P hsrc v⟩
    have e := hG u u
    rw [hinv, hPz0] at e
    have hrad : ⟪x, v⟫_ℝ = ‖x‖ * u.2 := by
      calc ⟪x, v⟫_ℝ = StandardCap.metric.inner x x v := (metric_inner_radial x v).symm
        _ = StandardCap.metric.inner x (‖x‖ • w) v := by rw [← hxw]
        _ = ‖x‖ * StandardCap.metric.inner x w v := inner_smul_left _ _ _ _ _
        _ = ‖x‖ * u.2 := by rw [← hinv, hmet]
    have h1 := (hbd u).1
    rw [e] at h1
    have h3 : (1 - θ) * u.2 ^ 2 ≤ g.inner x v v :=
      (mul_le_mul_of_nonneg_left (hsh u) hθ').trans h1
    rw [hrad]
    calc (‖x‖ * u.2) ^ 2 * (1 - θ) = ‖x‖ ^ 2 * ((1 - θ) * u.2 ^ 2) := by ring
      _ ≤ ‖x‖ ^ 2 * g.inner x v v := mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
  · have e := hG u0 u0
    rw [hdF, hPz0] at e
    have h := (hbd u0).2
    rw [hsh1, mul_one, e] at h
    have hexp : g.inner x x x = ‖x‖ ^ 2 * g.inner x w w := by
      calc g.inner x x x = g.inner x (‖x‖ • w) (‖x‖ • w) := by rw [← hxw]
        _ = ‖x‖ ^ 2 * g.inner x w w := by
          rw [inner_smul_left, inner_smul_right]
          ring
    rw [hexp]
    calc ‖x‖ ^ 2 * g.inner x w w ≤ ‖x‖ ^ 2 * (1 + θ) :=
          mul_le_mul_of_nonneg_left h (sq_nonneg _)
      _ = (1 + θ) * ‖x‖ ^ 2 := by ring

private theorem radial_bounds_of_pullback_close {s θ : ℝ} (hs : s < 1) (hθ : θ < 1)
    (g : SmoothRiemannianMetric (𝓡 3) E3) {x : E3} (hxT : transitionEnd ≤ ‖x‖)
    (G : SmoothRiemannianMetric IC (S2 × ℝ)) (F : PartialDiffeomorph IC (𝓡 3) (S2 × ℝ) E3 ∞)
    (hF : ∀ z, F z = (‖x‖ + z.2) • pointedInitialRotation x z.1.val)
    (hsrc : ((spherePoint : S2), (0 : ℝ)) ∈ F.source)
    (hG : ∀ v w : TangentSpace IC ((spherePoint : S2), (0 : ℝ)),
      G.inner ((spherePoint : S2), (0 : ℝ)) v w =
        g.inner (F ((spherePoint : S2), (0 : ℝ)))
          (mfderiv IC (𝓡 3) F ((spherePoint : S2), (0 : ℝ)) v)
          (mfderiv IC (𝓡 3) F ((spherePoint : S2), (0 : ℝ)) w))
    (hclose : metricDerivNorm 0 G (shrinkingCylinderMetric (E := E3) s)
      (shrinkingCylinderMetric (E := E3) s) ((spherePoint : S2), (0 : ℝ)) ≤ θ) :
    (∀ v : E3, ⟪x, v⟫_ℝ ^ 2 * (1 - θ) ≤ ‖x‖ ^ 2 * g.inner x v v) ∧
      g.inner x x x ≤ (1 + θ) * ‖x‖ ^ 2 := by
  have hx0 : 0 < ‖x‖ := transitionEnd_pos.trans_le hxT
  have hmf : mfderiv IC (𝓡 3) F ((spherePoint : S2), (0 : ℝ)) =
      mfderiv IC (𝓡 3) (initialPolarDiffeomorph (pointedInitialRotation x) ‖x‖)
        ((spherePoint : S2), (0 : ℝ)) := by
    congr 1
    funext z
    exact (hF z).trans (initialPolarDiffeomorph_apply _ _ z).symm
  have hPz0 : F ((spherePoint : S2), (0 : ℝ)) = x :=
    (hF _).trans ((initialPolarDiffeomorph_apply _ _ _).symm.trans (polar_center x))
  have hdF : mfderiv IC (𝓡 3) F ((spherePoint : S2), (0 : ℝ))
      ((0 : EuclideanSpace ℝ (Fin 2)), (1 : ℝ)) =
        pointedInitialRotation x ((spherePoint : S2) : E3) := by
    rw [hmf]
    exact polar_axial_mfderiv hx0
  have hxw : x = ‖x‖ • pointedInitialRotation x ((spherePoint : S2) : E3) := by
    have h := polar_center x
    rw [initialPolarDiffeomorph_apply] at h
    change (‖x‖ + 0) • pointedInitialRotation x ((spherePoint : S2) : E3) = x at h
    rw [add_zero] at h
    exact h.symm
  have hsh1 : (shrinkingCylinderMetric (E := E3) s).inner ((spherePoint : S2), (0 : ℝ))
      ((0 : EuclideanSpace ℝ (Fin 2)), (1 : ℝ)) ((0 : EuclideanSpace ℝ (Fin 2)), (1 : ℝ)) =
        1 := by
    erw [shrinkingCylinderMetric_inner hs]
    change 2 * (1 - s) * (Geometry.roundMetric (E := E3) (n := 2)).inner (spherePoint : S2) 0 0 +
      1 * 1 = 1
    simp
  have hmetP : ∀ u : TangentSpace IC ((spherePoint : S2), (0 : ℝ)),
      StandardCap.metric.inner x (pointedInitialRotation x ((spherePoint : S2) : E3))
        (mfderiv IC (𝓡 3) (initialPolarDiffeomorph (pointedInitialRotation x) ‖x‖)
          ((spherePoint : S2), (0 : ℝ)) u) = u.2 := by
    intro u
    have h := initialPolarDiffeomorph_metric_inner (pointedInitialRotation x) ‖x‖
      ((spherePoint : S2), (0 : ℝ)) (by change transitionEnd ≤ ‖x‖ + 0; linarith)
      ((0 : EuclideanSpace ℝ (Fin 2)), (1 : ℝ)) u
    rw [polar_axial_mfderiv hx0, polar_center] at h
    refine h.trans ?_
    erw [roundCylinderMetric_inner]
    change 2 * inner ℝ (Geometry.dIncl (spherePoint : S2) 0)
      (Geometry.dIncl (spherePoint : S2) u.1) + 1 * u.2 = u.2
    simp
  have hmet : ∀ u : TangentSpace IC ((spherePoint : S2), (0 : ℝ)),
      StandardCap.metric.inner x (pointedInitialRotation x ((spherePoint : S2) : E3))
        (mfderiv IC (𝓡 3) F ((spherePoint : S2), (0 : ℝ)) u) = u.2 := by
    intro u
    rw [hmf]
    exact hmetP u
  exact radial_bounds_core hs hθ g hxw G F hsrc hPz0 _ hdF hsh1 hmet hG hclose

private theorem spatialNeck_cast_map {g : SmoothRiemannianMetric (𝓡 3) E3} {eps : ℝ}
    {p q : E3} (h : p = q) (nk : SpatialNeck g eps p) : (h ▸ nk).map = nk.map := by
  subst h
  rfl

private theorem exists_spatialNeck_of_pullback_close
    {eps s : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11) (hs0 : 0 ≤ s) (hs : s < 1)
    (g : SmoothRiemannianMetric (𝓡 3) E3) (x : E3)
    (G : SmoothRiemannianMetric IC (S2 × ℝ)) (F : PartialDiffeomorph IC (𝓡 3) (S2 × ℝ) E3 ∞)
    (hF : ∀ z, F z = (‖x‖ + z.2) • pointedInitialRotation x z.1.val)
    (hKs : (univ : Set S2) ×ˢ Icc (-(eps⁻¹ + 1)) (eps⁻¹ + 1) ⊆ F.source)
    (hG : ∀ z ∈ (univ : Set S2) ×ˢ Icc (-(eps⁻¹ + 1)) (eps⁻¹ + 1),
      ∀ v w : TangentSpace IC z, G.inner z v w =
        g.inner (F z) (mfderiv IC (𝓡 3) F z v) (mfderiv IC (𝓡 3) F z w))
    (hclose : ∀ j ≤ ⌈eps⁻¹⌉₊, ∀ z ∈ (univ : Set S2) ×ˢ Icc (-(eps⁻¹ + 1)) (eps⁻¹ + 1),
      metricDerivNorm j G (shrinkingCylinderMetric (E := E3) s)
        (shrinkingCylinderMetric (E := E3) s) z ≤ min (1 / 40000) (eps / 20000) / 2) :
    ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∃ nk : SpatialNeck g eps x,
      ∀ z : neckBuffer eps,
        nk.map z.val = (‖x‖ + c * z.val.2) • pointedInitialRotation x z.val.1 := by
  have h1 : (0 : ℝ) < 1 - s := sub_pos.mpr hs
  have hc : 0 < Real.sqrt (1 - s) := Real.sqrt_pos.mpr h1
  have hc1 : Real.sqrt (1 - s) ≤ 1 := Real.sqrt_le_one.mpr (by linarith)
  have hq : 0 < (1 - s)⁻¹ := inv_pos.mpr h1
  have hi : 0 < eps⁻¹ := inv_pos.mpr heps
  obtain ⟨A, hA⟩ : ∃ A, A = cylinderAxialScale (Real.sqrt (1 - s)) hc.ne' := ⟨_, rfl⟩
  have hAapp : ∀ z : S2 × ℝ, A z = (z.1, Real.sqrt (1 - s) * z.2) := by
    intro z
    rw [hA]
    rfl
  have hmem : ∀ z : bufferedCylinder eps,
      A z.val ∈ (univ : Set S2) ×ˢ Icc (-(eps⁻¹ + 1)) (eps⁻¹ + 1) := by
    intro z
    have hz : z.val.2 ∈ Ioo (-eps⁻¹ - 1) (eps⁻¹ + 1) := z.property
    rw [hAapp]
    refine ⟨mem_univ _, ?_, ?_⟩
    · change -(eps⁻¹ + 1) ≤ Real.sqrt (1 - s) * z.val.2
      rcases le_or_gt 0 z.val.2 with h | h
      · nlinarith
      · nlinarith [hz.1]
    · change Real.sqrt (1 - s) * z.val.2 ≤ eps⁻¹ + 1
      rcases le_or_gt 0 z.val.2 with h | h
      · nlinarith [hz.2]
      · nlinarith
  have hsrc : ∀ z : bufferedCylinder eps, A z.val ∈ F.source := fun z => hKs (hmem z)
  obtain ⟨Φ, hΦdef⟩ : ∃ Φ : bufferedCylinder eps → E3, Φ = fun z => F (A z.val) := ⟨_, rfl⟩
  have hΦ_apply : ∀ z : bufferedCylinder eps,
      Φ z = (‖x‖ + Real.sqrt (1 - s) * z.val.2) • pointedInitialRotation x z.val.1 := by
    intro z
    rw [hΦdef]
    change F (A z.val) = _
    rw [hF, hAapp]
  have hsm : ContMDiff IC (𝓡 3) ∞ Φ := by
    rw [hΦdef]
    exact fun z => (F.contMDiffOn.contMDiffAt (F.open_source.mem_nhds (hsrc z))).comp z
      ((A.contMDiff.comp contMDiff_subtype_val) z)
  have hd : ∀ (z : bufferedCylinder eps) (v : TangentSpace IC z),
      mfderiv IC (𝓡 3) Φ z v = mfderiv IC (𝓡 3) F (A z.val) (mfderiv IC IC A z.val v) := by
    intro z v
    have hval : MDifferentiableAt IC IC (Subtype.val : bufferedCylinder eps → S2 × ℝ) z :=
      (hasMFDerivAt_subtype_val (I := IC) (bufferedCylinder eps) z).mdifferentiableAt
    have hAd : MDifferentiableAt IC IC A z.val := A.contMDiff.mdifferentiableAt (by simp)
    have hFA : MDifferentiableAt IC (𝓡 3) F (A z.val) := F.mdifferentiableAt (by simp) (hsrc z)
    have h1 := mfderiv_comp_apply (x := z) (f := (Subtype.val : bufferedCylinder eps → S2 × ℝ))
      (g := (F : S2 × ℝ → E3) ∘ A) (hFA.comp z.val hAd) hval v
    rw [mfderiv_subtype_val_apply] at h1
    rw [show Φ = ((F : S2 × ℝ → E3) ∘ A) ∘ Subtype.val from hΦdef, h1]
    exact mfderiv_comp_apply z.val hFA hAd v
  have himm : ∀ z : bufferedCylinder eps, Injective (mfderiv IC (𝓡 3) Φ z) := by
    intro z v w hvw
    rw [hd, hd] at hvw
    have hFinj := ((PartialDiffeomorph.isLocalDiffeomorphAt IC (𝓡 3) ∞ F
      (hsrc z)).mfderivToContinuousLinearEquiv (by simp)).injective
    have h2 := hFinj hvw
    rw [hA] at h2
    have e1 := cylinderAxialScale_mfderiv (Real.sqrt (1 - s)) hc.ne' z.val v
    have e2 := cylinderAxialScale_mfderiv (Real.sqrt (1 - s)) hc.ne' z.val w
    have h3 := e1.symm.trans (h2.trans e2)
    have ha := congrArg Prod.fst h3
    have hb := congrArg Prod.snd h3
    exact Prod.ext ha (mul_left_cancel₀ hc.ne' hb)
  have hinj : Injective Φ := by
    intro z w hzw
    rw [hΦdef] at hzw
    have h2 := F.toPartialEquiv.injOn (hsrc z) (hsrc w) hzw
    exact Subtype.ext (A.injective h2)
  have hΦ : IsLocalDiffeomorph IC (𝓡 3) ∞ Φ :=
    DifferentialGeometry.Topology.Manifold.isLocalDiffeomorph_of_injective_mfderiv Φ hsm himm
      (by simp)
  have hpull : pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric (1 - s)⁻¹ hq g) Φ hΦ hinj =
      (scaleMetric (1 - s)⁻¹ hq (Diffeomorph.pullbackMetricCross G A)).restrictOpen
        (bufferedCylinder eps) := by
    apply SmoothRiemannianMetric.ext_inner
    intro z v w
    rw [pullbackMetricOfInjectiveLocalDiffeomorph_inner, scaleMetric_inner, hd, hd]
    have e1 := hG (A z.val) (hmem z) (mfderiv IC IC A z.val v) (mfderiv IC IC A z.val w)
    have e2 := Diffeomorph.pullbackMetricCross_inner G A z.val v w
    have hΦz : Φ z = F (A z.val) := by rw [hΦdef]
    change _ = (1 - s)⁻¹ * (Diffeomorph.pullbackMetricCross G A).inner z.val v w
    rw [hΦz]
    exact congrArg (fun r => (1 - s)⁻¹ * r) (e1.symm.trans e2.symm)
  have href : referenceMetric eps =
      (scaleMetric (1 - s)⁻¹ hq (Diffeomorph.pullbackMetricCross
        (shrinkingCylinderMetric (E := E3) s) A)).restrictOpen (bufferedCylinder eps) := by
    rw [hA]
    exact congrArg (fun m => SmoothRiemannianMetric.restrictOpen m (bufferedCylinder eps))
      (scale_pullback_shrinkingCylinderMetric hs).symm
  have hη₀ : 0 < min (1 / 40000 : ℝ) (eps / 20000) := lt_min (by norm_num) (by positivity)
  have hη₀small : min (1 / 40000 : ℝ) (eps / 20000) ≤ 1 / 40000 := min_le_left _ _
  have hη₀eps : 20000 * min (1 / 40000 : ℝ) (eps / 20000) ≤ eps := by
    have h := min_le_right (1 / 40000 : ℝ) (eps / 20000)
    linarith
  have hk : 2 ≤ ⌈eps⁻¹⌉₊ := by
    have h2 : (2 : ℝ) ≤ eps⁻¹ := by
      rw [inv_eq_one_div]
      apply (le_div_iff₀ heps).mpr
      linarith
    exact_mod_cast h2.trans (Nat.le_ceil _)
  have hclose' : metricDerivENormSupOn (controlledCylinder eps) ⌈eps⁻¹⌉₊
      (pullbackMetricOfInjectiveLocalDiffeomorph (scaleMetric (1 - s)⁻¹ hq g) Φ hΦ hinj)
      (referenceMetric eps) (referenceMetric eps) <
        ENNReal.ofReal (min (1 / 40000 : ℝ) (eps / 20000)) := by
    apply lt_of_le_of_lt _ ((ENNReal.ofReal_lt_ofReal_iff hη₀).mpr (half_lt_self hη₀))
    rw [metricDerivENormSupOn_le_iff]
    intro j hj z _
    apply ENNReal.ofReal_le_ofReal
    rw [hpull, href, metricDerivNorm_restrictOpen,
      CheegerGromovCompactness.metricDerivNorm_scale_all,
      CheegerGromovCompactness.metricDerivNorm_pullbackCross]
    have hw : Real.sqrt ((1 - s)⁻¹⁻¹ ^ j) ≤ 1 := by
      rw [Real.sqrt_le_one, inv_inv]
      exact pow_le_one₀ h1.le (by linarith)
    have hb := hclose j hj (A z.val) (hmem z)
    have h0 : 0 ≤ metricDerivNorm j G (shrinkingCylinderMetric (E := E3) s)
        (shrinkingCylinderMetric (E := E3) s) (A z.val) := Real.sqrt_nonneg _
    calc Real.sqrt ((1 - s)⁻¹⁻¹ ^ j) * metricDerivNorm j G (shrinkingCylinderMetric s)
          (shrinkingCylinderMetric s) (A z.val)
        ≤ 1 * metricDerivNorm j G (shrinkingCylinderMetric s) (shrinkingCylinderMetric s)
          (A z.val) := mul_le_mul_of_nonneg_right hw h0
      _ ≤ min (1 / 40000 : ℝ) (eps / 20000) / 2 := by rw [one_mul]; exact hb
  obtain ⟨d, hdmap, _, _⟩ := exists_normalizedDatum_of_cylinder_pullback_close g heps
    (by linarith) hη₀ hη₀small hη₀eps hq hk Φ hΦ hinj hclose'
  obtain ⟨nk, _, hmap⟩ := d.toNormalizedNeck.exists_spatialNeck le_rfl hsmall le_rfl
  have hcenter : Φ (cylinderCenter eps heps) = x := by
    rw [hΦ_apply]
    change (‖x‖ + Real.sqrt (1 - s) * 0) • pointedInitialRotation x ((spherePoint : S2) : E3) = x
    rw [mul_zero]
    have h := polar_center x
    rw [initialPolarDiffeomorph_apply] at h
    exact h
  change SpatialNeck g eps (Φ (cylinderCenter eps heps)) at nk
  refine ⟨Real.sqrt (1 - s), hc, hc1, hcenter ▸ nk, fun z => ?_⟩
  rw [spatialNeck_cast_map]
  exact (hmap z).trans ((congrFun hdmap z).trans (hΦ_apply z))

theorem StandardSolution.exists_far_radial_spatialNeck
    {eps Θ θ : ℝ} (heps : 0 < eps) (hsmall : eps < 1 / 11) (hΘ : Θ < 1) (hθ : 0 < θ) :
    ∃ D : ℝ, 0 < D ∧ ∀ (S : StandardSolution) (t : ℝ), t ∈ Icc 0 Θ → ∀ x : E3, D ≤ ‖x‖ →
      (∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∃ nk : SpatialNeck (S.val.metric t) eps x,
        ∀ z : neckBuffer eps,
          nk.map z.val = (‖x‖ + c * z.val.2) • pointedInitialRotation x z.val.1) ∧
      (∀ v : E3, ⟪x, v⟫_ℝ ^ 2 * (1 - θ) ≤ ‖x‖ ^ 2 * (S.val.metric t).inner x v v) ∧
      (S.val.metric t).inner x x x ≤ (1 + θ) * ‖x‖ ^ 2 := by
  by_contra hcon
  push Not at hcon
  choose S t ht x hx hbad using fun n : ℕ => hcon ((n : ℝ) + 1) (by positivity)
  obtain ⟨s, hsI, φ, hφ, hlim⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) Θ)).tendsto_subseq ht
  have hτ : 0 < max Θ (1 / 2) := lt_of_lt_of_le (by norm_num) (le_max_right _ _)
  have hτ1 : max Θ (1 / 2) < 1 := max_lt hΘ (by norm_num)
  have htime : ∀ n, (t ∘ φ) n ∈ Icc 0 (max Θ (1 / 2)) := fun n =>
    Icc_subset_Icc_right (le_max_left _ _) (ht (φ n))
  have hescape : Tendsto (fun n => (riemannianEDistOf ((S (φ n)).val.metric 0) 0
      (x (φ n))).toReal) atTop atTop := by
    have heq : ∀ n, (riemannianEDistOf ((S (φ n)).val.metric 0) 0 (x (φ n))).toReal =
        ‖x (φ n)‖ := by
      intro n
      rw [(S (φ n)).val.initial, distance_zero]
    simp only [heq]
    refine tendsto_atTop_mono (fun n => ?_) tendsto_natCast_atTop_atTop
    have h1 := hx (φ n)
    have h2 : (n : ℝ) ≤ φ n := by exact_mod_cast hφ.id_le n
    linarith
  obtain ⟨ψ, G, F, hψ, hconv, hFform, hloc⟩ :=
    exists_standard_cylinder_metric_subsequence_at_tendsto_time hτ hτ1 (S ∘ φ) (x ∘ φ)
      (t ∘ φ) htime hlim hescape
  have hs1 : s < 1 := lt_of_le_of_lt hsI.2 hΘ
  have hconv' := hconv.change_reference (shrinkingCylinderMetric (E := E3) s)
  have hK : IsCompact ((univ : Set S2) ×ˢ Icc (-(eps⁻¹ + 1)) (eps⁻¹ + 1)) :=
    isCompact_univ.prod isCompact_Icc
  have hθ' : 0 < min (min (1 / 40000 : ℝ) (eps / 20000) / 2) (min θ (1 / 2)) :=
    lt_min (by positivity) (lt_min hθ (by norm_num))
  have hθ'η : min (min (1 / 40000 : ℝ) (eps / 20000) / 2) (min θ (1 / 2)) ≤
      min (1 / 40000 : ℝ) (eps / 20000) / 2 := min_le_left _ _
  have hθ'θ : min (min (1 / 40000 : ℝ) (eps / 20000) / 2) (min θ (1 / 2)) ≤ θ :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hθ'1 : min (min (1 / 40000 : ℝ) (eps / 20000) / 2) (min θ (1 / 2)) < 1 :=
    lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _)) (by norm_num)
  obtain ⟨n0, hn0⟩ := hconv' _ hK ⌈eps⁻¹⌉₊ _ hθ'
  obtain ⟨n1, hn1⟩ := (hloc _ hK).exists_forall_of_atTop
  obtain ⟨U, _, hKU, hUs, hGU⟩ := hn1 (max (max n0 n1) ⌈transitionEnd⌉₊)
    ((le_max_right _ _).trans (le_max_left _ _))
  have hsup := hn0 (max (max n0 n1) ⌈transitionEnd⌉₊) ((le_max_left _ _).trans (le_max_left _ _))
  set n := max (max n0 n1) ⌈transitionEnd⌉₊ with hndef
  have hpt : ∀ j ≤ ⌈eps⁻¹⌉₊, ∀ z ∈ (univ : Set S2) ×ˢ Icc (-(eps⁻¹ + 1)) (eps⁻¹ + 1),
      metricDerivNorm j (G n) (shrinkingCylinderMetric (E := E3) s)
        (shrinkingCylinderMetric (E := E3) s) z ≤
          min (min (1 / 40000 : ℝ) (eps / 20000) / 2) (min θ (1 / 2)) :=
    fun j hj z hz => (derivNorm_le_sup hK hj _ _ _ hz).trans hsup.le
  set m := φ (ψ n) with hmdef
  have hmn : n ≤ m := (hψ.id_le n).trans (hφ.id_le (ψ n))
  have hxT : transitionEnd ≤ ‖x m‖ := by
    have h1 := hx m
    have h2 : transitionEnd ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
    have h3 : (n : ℝ) ≤ m := by exact_mod_cast hmn
    linarith
  have hFm : ∀ z, F n z = (‖x m‖ + z.2) • pointedInitialRotation (x m) z.1.val := hFform n
  have hKs : (univ : Set S2) ×ˢ Icc (-(eps⁻¹ + 1)) (eps⁻¹ + 1) ⊆ (F n).source := hKU.trans hUs
  have hGm : ∀ z ∈ (univ : Set S2) ×ˢ Icc (-(eps⁻¹ + 1)) (eps⁻¹ + 1),
      ∀ v w : TangentSpace IC z, (G n).inner z v w =
        ((S m).val.metric (t m)).inner (F n z) (mfderiv IC (𝓡 3) (F n) z v)
          (mfderiv IC (𝓡 3) (F n) z w) := fun z hz => hGU z (hKU hz)
  have hz0 : ((spherePoint : S2), (0 : ℝ)) ∈ (univ : Set S2) ×ˢ Icc (-(eps⁻¹ + 1)) (eps⁻¹ + 1) :=
    ⟨mem_univ _, by linarith [inv_pos.mpr heps], by linarith [inv_pos.mpr heps]⟩
  obtain ⟨c, hc, hc1, nk, hnk⟩ := exists_spatialNeck_of_pullback_close heps hsmall hsI.1 hs1
    ((S m).val.metric (t m)) (x m) (G n) (F n) hFm hKs hGm
    (fun j hj z hz => (hpt j hj z hz).trans hθ'η)
  obtain ⟨hR1, hR2⟩ := radial_bounds_of_pullback_close hs1 hθ'1 ((S m).val.metric (t m)) hxT
    (G n) (F n) hFm (hKs hz0) (hGm _ hz0) (hpt 0 (Nat.zero_le _) _ hz0)
  have hB : ∀ v : E3, ⟪x m, v⟫_ℝ ^ 2 * (1 - θ) ≤
      ‖x m‖ ^ 2 * ((S m).val.metric (t m)).inner (x m) v v := by
    intro v
    refine le_trans ?_ (hR1 v)
    exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
  have hC : ((S m).val.metric (t m)).inner (x m) (x m) (x m) ≤ (1 + θ) * ‖x m‖ ^ 2 :=
    (hR2).trans (mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _))
  exact (hbad m ⟨c, hc, hc1, nk, hnk⟩ hB).not_ge hC

end DifferentialGeometry.PDE.RicciFlow
