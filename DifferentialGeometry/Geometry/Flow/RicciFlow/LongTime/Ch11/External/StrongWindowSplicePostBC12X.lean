import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongWindowSplicePostAC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongWindowBirthC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.External.StrongWindowSurviveBC12X
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.StaticCapCoordinates

/-!
# Splice post part, band tools (C12X, S16 `hwin` far branch; O-C12X-S16J G3)

Tools for the post-surgery comparison `RetainedCoreHistory.exists_splicePost_C12X` (G4e-post,
`StrongWindowSplicePostCC12X`):

* radial window coordinates: a window point beyond the transition radius is the retained collar
  point `(x / ‖x‖, ‖x‖ - standardCapL)` (`HasRadialCoordinates`, the cover and the window
  embedding);
* `RetainedCoreHistory.splicePost_band_points_C12X`: every buffer point of the deep neck in the
  band `|z - z_u| < L + 1` lies in the survivor pull-in domain `Sv.U` (maximality, collar crossing
  `collar_regularCrossing_SG`, `recenter_chart`), and `Ψ` there is `Ξ` of the radial window point;
* `RetainedCoreHistory.splicePost_band_transfer_C12X`: abstract metric transfer from the radial
  band `cylBand_C12X L` to the band of `Sv.U` through the cylinder isometry `cylIso_C12X`, with the
  post-surgery identification `metric_post` as input.
-/

set_option autoImplicit false

noncomputable section

open Set Function TopologicalSpace
open scoped NNReal Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

universe u

private local instance s16j_opensSigmaB {M : Type*} [TopologicalSpace M]
    [ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ) M] [SigmaCompactSpace M] (U : Opens M) :
    SigmaCompactSpace U :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen SpatialNeckCylinderModel U.isOpen)

section Window

variable {P Q : OrientedThreeStage.{u}} {a s : ℝ} {E : MetricCutCapEvent P Q a s}
  {fixed : StaticCapScaffold} {D ε : ℝ} {m : ℕ} {b : E.RetainedBoundaryIndex}

/-- A window point beyond the transition radius is not a cap point. -/
private theorem s16j_window_ne_cap (S : E.PresentedStaticCap fixed D m ε b)
    (hcan : S.hasCanonicalWindow) {x : standardCapWindow D}
    (hx : StandardCap.transitionEnd < ‖x.val‖) (z : ThreeBall) :
    S.witness.window x ≠ S.witness.cap z := by
  intro hz
  obtain ⟨-, -, -, -, -, -, -, hcap⟩ := hcan
  obtain ⟨x', hx', hw⟩ := hcap z
  have h1 : S.window x' = S.window x := by
    rw [hw]
    change S.inclusion (S.witness.cap z) = S.inclusion (S.witness.window x)
    rw [hz]
  have h2 := S.window_smooth.isEmbedding.injective h1
  rw [h2] at hx'
  linarith

/-- The radial direction of a nonzero point, on the unit sphere. -/
private def s16j_dir (x : ThreeSpace) (hx : x ≠ 0) : Sphere 2 :=
  ⟨‖x‖⁻¹ • x, by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]⟩

private theorem s16j_polar_norm {r : ℝ} (hr : 0 ≤ r) (om : Sphere 2) :
    ‖r • (om : ThreeSpace)‖ = r := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hr, norm_eq_of_mem_sphere, mul_one]

/-- **Radial window coordinates.**  A window point beyond the transition radius is the retained
collar point with radial coordinates `(x / ‖x‖, ‖x‖ - standardCapL)`. -/
private theorem s16j_window_radial (S : E.PresentedStaticCap fixed D m ε b)
    (hcan : S.hasCanonicalWindow) (hcoord : S.witness.HasRadialCoordinates)
    {x : standardCapWindow D} (hx : StandardCap.transitionEnd < ‖x.val‖) :
    ∃ (hx0 : x.val ≠ 0) (hc : 0 ≤ ‖x.val‖ - standardCapL ∧ ‖x.val‖ - standardCapL < S.delta⁻¹),
      S.witness.window x =
        S.witness.retained ⟨(s16j_dir x.val hx0, ‖x.val‖ - standardCapL), hc⟩ := by
  have hL : standardCapL = StandardCap.transitionEnd := standardCapL_eq_transitionEnd
  have hTpos := StandardCap.transitionEnd_pos
  have hx0 : x.val ≠ 0 := norm_ne_zero_iff.mp (by linarith)
  have hxD : ‖x.val‖ < D + 1 := x.2
  have hlt : ‖x.val‖ - standardCapL < S.delta⁻¹ := by
    by_contra hge
    push Not at hge
    rcases (S.witness.cover ▸ mem_univ (S.witness.window x) :
        S.witness.window x ∈ range S.witness.retained ∪ range S.witness.cap) with ⟨c, hc⟩ | ⟨z, hz⟩
    · have hc2 : c.1.2 < S.delta⁻¹ := c.2.2
      have hmem : (standardCapL + c.1.2) • (c.1.1 : ThreeSpace) ∈ standardCapWindow D := by
        change ‖(standardCapL + c.1.2) • (c.1.1 : ThreeSpace)‖ < D + 1
        rw [s16j_polar_norm (by linarith [c.2.1]) c.1.1]
        linarith
      have h := hcoord.2 c hmem
      have heq : S.window ⟨_, hmem⟩ = S.window x := by
        change S.inclusion (S.witness.window _) = S.inclusion (S.witness.window x)
        rw [h, hc]
      have hxx := congrArg (fun w : standardCapWindow D => ‖w.val‖)
        (S.window_smooth.isEmbedding.injective heq)
      simp only at hxx
      rw [s16j_polar_norm (by linarith [c.2.1]) c.1.1] at hxx
      linarith
    · exact absurd hz.symm (s16j_window_ne_cap S hcan hx z)
  have hc : 0 ≤ ‖x.val‖ - standardCapL ∧ ‖x.val‖ - standardCapL < S.delta⁻¹ :=
    ⟨by linarith, hlt⟩
  refine ⟨hx0, hc, ?_⟩
  have hxeq : (standardCapL + (‖x.val‖ - standardCapL)) • ((s16j_dir x.val hx0 : Sphere 2) :
      ThreeSpace) = x.val := by
    change (standardCapL + (‖x.val‖ - standardCapL)) • (‖x.val‖⁻¹ • x.val) = x.val
    rw [smul_smul, show standardCapL + (‖x.val‖ - standardCapL) = ‖x.val‖ by ring,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hx0), one_smul]
  have hmem : (standardCapL + (‖x.val‖ - standardCapL)) •
      ((s16j_dir x.val hx0 : Sphere 2) : ThreeSpace) ∈ standardCapWindow D := by
    rw [hxeq]
    exact x.2
  have h := hcoord.2 ⟨(s16j_dir x.val hx0, ‖x.val‖ - standardCapL), hc⟩ hmem
  have hx' : (⟨_, hmem⟩ : standardCapWindow D) = x := Subtype.ext hxeq
  rw [hx'] at h
  exact h

end Window

private theorem s16j_vec_aux (e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace) (a c σ : ℝ) (y z : NeckCylinder)
    (hz : z = (sphereDiffeo (n := 2) e.symm y.1, -(σ * c) + σ * y.2)) :
    (a + z.2) • e (z.1 : ThreeSpace) = (a + σ * (y.2 - c)) • (y.1 : ThreeSpace) := by
  subst hz
  rw [Geometry.sphereDiffeo_coe, LinearIsometryEquiv.apply_symm_apply]
  congr 1
  ring

section PullCongr

variable {E F H H' M N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

private theorem s16j_localPull_congr (g : SmoothRiemannianMetric J N) {Φ Φ' : M → N}
    (h : Φ = Φ') (hΦ : IsLocalDiffeomorph I J ∞ Φ) (hΦ' : IsLocalDiffeomorph I J ∞ Φ') :
    localPullMetric g Φ hΦ = localPullMetric g Φ' hΦ' := by
  subst h
  rfl

end PullCongr

namespace RetainedCoreHistory

/-- Band points of the survivor pull-in: every buffer point `w'` with `|z_{w'} - z_u| < L + 1`
lies in `Sv.U`, and `Ψ w'` is `Ξ` of the radial window point `(‖x‖ + σ (z_{w'} - z_u)) • ω_{w'}`. -/
theorem splicePost_band_points_C12X {H : RetainedCoreHistory.{u}} {p : CutoffParameters}
    {records : ∀ i, GeometricCutoffRecord H.toHistory i p} {k : Fin (H.eventCount + 1)}
    {y : (H.stage k).Carrier} {t Dw θw : ℝ} (d : H.WindowDatum_C12X records k y t Dw θw)
    {L Dc s : ℝ} (hL : 0 ≤ L) (hcan : ((records d.j).static d.b).hasCanonicalWindow)
    (hcoord : ((records d.j).static d.b).witness.HasRadialCoordinates)
    (hxbig : standardCapL + L + 2 + 1 ≤ ‖d.x.val‖) (hfit : ‖d.x.val‖ + L + 1 ≤ Dc + 1)
    (hmod : ‖d.x.val‖ + L + 1 ≤ p.modelRadius + 1)
    {G : (H.stage k).IncomingSlab (H.time k) s}
    (Ξ : standardCapWindow Dc → H.toHistory.backwardSurvivorIncomingDomain d.j.succ k d.hl G)
    (hle : standardCapWindow Dc ≤ standardCapWindow p.modelRadius)
    (hΞwin : ∀ v, H.toHistory.backwardSurvivorMap d.j.succ k d.hl d.j.succ le_rfl d.hl (Ξ v).val =
      ((records d.j).static d.b).window (Opens.inclusion hle v))
    {θ : ℝ} {D : IncomingBackwardNeckDeep_C12X H.toHistory d.j ((records d.j).neck d.b.1.1)
      ((records d.j).nominalRadius ⟨d.b.1.1⟩) θ}
    (Sv : H.toHistory.SpliceSurvivor_C12X D k d.hl) (u : Sv.U)
    (ys : neckBuffer ((records d.j).static d.b).delta)
    (hys : 0 < ys.1.2 ∧ ys.1.2 < (((records d.j).static d.b).delta)⁻¹)
    (hwin : ((records d.j).static d.b).witness.window d.x =
      ((records d.j).static d.b).witness.retained ⟨ys.1, hys.1.le, hys.2⟩)
    (hu : u.1 = ⟨(ys.1.1, (if d.b.1.2 then 1 else -1) * (1 + ys.1.2)),
      (records d.j).recenter_in_buffer d.b ys⟩)
    (w' : neckBuffer ((records d.j).delta d.b.1.1)) (hw' : |w'.1.2 - u.1.1.2| < L + 1) :
    ∃ hv : (‖d.x.val‖ + (if d.b.1.2 then 1 else -1) * (w'.1.2 - u.1.1.2)) • (w'.1.1 : ThreeSpace) ∈
        standardCapWindow Dc,
      ∃ hw' : w' ∈ Sv.U, (Sv.Ψ ⟨w', hw'⟩).val = (Ξ ⟨_, hv⟩).val.val := by
  have hTE := StandardCap.transitionEnd_pos
  have hLcap : standardCapL = StandardCap.transitionEnd := standardCapL_eq_transitionEnd
  obtain ⟨σ, hσdef⟩ : ∃ σ : ℝ, (if d.b.1.2 then (1 : ℝ) else -1) = σ := ⟨_, rfl⟩
  have hσ2 : σ ^ 2 = 1 := by rw [← hσdef]; split_ifs <;> norm_num
  have hσabs : |σ| = 1 := by rw [← hσdef]; split_ifs <;> norm_num
  have hxT : StandardCap.transitionEnd < ‖d.x.val‖ := by linarith
  obtain ⟨hx0, hc0, hwx0⟩ := s16j_window_radial _ hcan hcoord hxT
  have hys1 : ys.1 = (s16j_dir d.x.val hx0, ‖d.x.val‖ - standardCapL) := by
    obtain ⟨-, hemb⟩ := ((records d.j).static d.b).witness.retained_smooth
    exact congrArg Subtype.val (hemb.injective (hwin.symm.trans hwx0))
  have hu2 : u.1.1.2 = σ * (1 + (‖d.x.val‖ - standardCapL)) := by
    have h := congrArg (fun v : neckBuffer ((records d.j).delta d.b.1.1) => v.1.2) hu
    simp only at h
    rw [h, hσdef, hys1]
  rw [hσdef]
  set ρ := ‖d.x.val‖ + σ * (w'.1.2 - u.1.1.2) with hρ
  have hρb : |σ * (w'.1.2 - u.1.1.2)| < L + 1 := by rw [abs_mul, hσabs, one_mul]; exact hw'
  have hρlo : ‖d.x.val‖ - (L + 1) < ρ := by
    have := neg_abs_le (σ * (w'.1.2 - u.1.1.2))
    linarith
  have hρhi : ρ < ‖d.x.val‖ + (L + 1) := by
    have := le_abs_self (σ * (w'.1.2 - u.1.1.2))
    linarith
  have hnorm : ‖ρ • (w'.1.1 : ThreeSpace)‖ = ρ := s16j_polar_norm (by linarith) w'.1.1
  have hv : ρ • (w'.1.1 : ThreeSpace) ∈ standardCapWindow Dc := by
    change ‖ρ • (w'.1.1 : ThreeSpace)‖ < Dc + 1
    rw [hnorm]
    linarith
  have hvm : ρ • (w'.1.1 : ThreeSpace) ∈ standardCapWindow p.modelRadius := by
    change ‖ρ • (w'.1.1 : ThreeSpace)‖ < p.modelRadius + 1
    rw [hnorm]
    linarith
  have hvT : StandardCap.transitionEnd <
      ‖(⟨_, hvm⟩ : standardCapWindow p.modelRadius).val‖ := by
    change _ < ‖ρ • (w'.1.1 : ThreeSpace)‖
    rw [hnorm]
    linarith
  obtain ⟨hv0, hcv, hwv⟩ := s16j_window_radial _ hcan hcoord hvT
  have hdir : s16j_dir (ρ • (w'.1.1 : ThreeSpace)) hv0 = w'.1.1 := by
    apply Subtype.ext
    change ‖ρ • (w'.1.1 : ThreeSpace)‖⁻¹ • (ρ • (w'.1.1 : ThreeSpace)) = w'.1.1
    rw [hnorm, smul_smul, inv_mul_cancel₀ (by linarith : ρ ≠ 0), one_smul]
  have hz2 : ‖ρ • (w'.1.1 : ThreeSpace)‖ - standardCapL = σ * w'.1.2 - 1 := by
    rw [hnorm, hρ, hu2]
    linear_combination (-(1 + (‖d.x.val‖ - standardCapL))) * hσ2
  have hcv' : 0 < σ * w'.1.2 - 1 ∧ σ * w'.1.2 - 1 < (((records d.j).static d.b).delta)⁻¹ := by
    rw [← hz2]
    exact ⟨by rw [hnorm]; linarith, hcv.2⟩
  let ysb : neckBuffer ((records d.j).static d.b).delta :=
    ⟨(w'.1.1, σ * w'.1.2 - 1), by constructor <;> linarith [hcv'.1, hcv'.2]⟩
  have hret : ((records d.j).static d.b).witness.retained ⟨ysb.1, hcv'.1.le, hcv'.2⟩ =
      ((records d.j).static d.b).witness.window ⟨_, hvm⟩ := by
    rw [hwv]
    congr 1
    apply Subtype.ext
    exact Prod.ext hdir.symm hz2.symm
  have hcross0 := collar_regularCrossing_SG (records d.j) d.b ysb hcv'
  have hrc := (records d.j).recenter_chart d.b ysb ((records d.j).recenter_in_buffer d.b ysb)
  have hweq : (⟨(ysb.1.1, (if d.b.1.2 then 1 else -1) * (1 + ysb.1.2)),
      (records d.j).recenter_in_buffer d.b ysb⟩ : neckBuffer ((records d.j).delta d.b.1.1)) =
        w' := by
    refine Subtype.ext (Prod.ext rfl ?_)
    change (if d.b.1.2 then 1 else -1) * (1 + (σ * w'.1.2 - 1)) = w'.1.2
    rw [hσdef]
    linear_combination w'.1.2 * hσ2
  rw [hrc, hweq, hret] at hcross0
  have hcross : (H.toHistory.event d.j).RegularCrossing
      (((records d.j).neck d.b.1.1).chart w').1
      (H.toHistory.backwardSurvivorMap d.j.succ k d.hl d.j.succ le_rfl d.hl
        (Ξ ⟨_, hv⟩).val) := by
    rw [hΞwin ⟨_, hv⟩]
    exact hcross0
  obtain ⟨hw'U, hΨ⟩ := Sv.maximal w' (Ξ ⟨_, hv⟩).val hcross
  exact ⟨hv, hw'U, hΨ⟩

/-- Abstract band transfer: on the band `|z - u₂| < L + 1` of the pull-in domain `U`, a metric
read through `ι ∘ Ψ = Ξ ∘ f ∘ J` is as close to `cylFam τ` as its `f`-pullback on the radial
band. -/
theorem splicePost_band_transfer_C12X {δ L τ q ε a σ u₂ Dc : ℝ} (r : ℕ) (hq : 0 < q) (hτ1 : τ < 1)
    (hσ2 : σ ^ 2 = 1) (hσabs : |σ| = 1) (e : ThreeSpace ≃ₗᵢ[ℝ] ThreeSpace)
    {U : Opens (neckBuffer δ)} {Nf N : Type*} [TopologicalSpace Nf] [ChartedSpace ThreeSpace Nf]
    [IsManifold ThreeModel ∞ Nf] [TopologicalSpace N] [ChartedSpace ThreeSpace N]
    [IsManifold ThreeModel ∞ N]
    (Ψ : U → Nf) (hΨ : IsLocalDiffeomorph NeckCylinderModel ThreeModel ∞ Ψ)
    (ι : Nf → N) (hι : IsLocalDiffeomorph ThreeModel ThreeModel ∞ ι)
    (Ξ : standardCapWindow Dc → N) (hΞ : IsLocalDiffeomorph ThreeModel ThreeModel ∞ Ξ)
    (gP : SmoothRiemannianMetric ThreeModel Nf) (gP' : SmoothRiemannianMetric ThreeModel N)
    (hpost : localPullMetric gP Ψ hΨ = localPullMetric gP' (ι ∘ Ψ) (isLocalDiffeomorph_comp hι hΨ))
    (f : cylBand_C12X L → standardCapWindow Dc)
    (hf : IsLocalDiffeomorph SpatialNeckCylinderModel ThreeModel ∞ f)
    (hform : ∀ z, (f z).val = (a + z.val.2) • e z.val.1.val)
    (hcl : ∀ q' ≤ r, ∀ z, metricDerivNorm q'
      (localPullMetric (localPullMetric (scaleMetric q hq gP') Ξ hΞ) f hf)
      ((cylFam_C12X τ).restrictOpen (cylBand_C12X L))
      ((cylFam_C12X τ).restrictOpen (cylBand_C12X L)) z ≤ ε)
    (hpt : ∀ w : U, |w.1.1.2 - u₂| < L + 1 →
      ∃ hv : (a + σ * (w.1.1.2 - u₂)) • (w.1.1.1 : ThreeSpace) ∈ standardCapWindow Dc,
        ι (Ψ w) = Ξ ⟨_, hv⟩)
    (w : U) (hw : |w.1.1.2 - u₂| < L + 1) (q' : ℕ) (hq' : q' ≤ r) :
    metricDerivNorm q' (localPullMetric (scaleMetric q hq gP) Ψ hΨ)
      (((cylFam_C12X τ).restrictOpen (neckBuffer δ)).restrictOpen U)
      (((cylFam_C12X τ).restrictOpen (neckBuffer δ)).restrictOpen U) w ≤ ε := by
  let W : Opens U := ⟨{w' | |w'.1.1.2 - u₂| < L + 1}, isOpen_lt (continuous_abs.comp
    ((continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)).sub
      continuous_const)) continuous_const⟩
  have hwW : w ∈ W := hw
  obtain ⟨J, hJ⟩ : ∃ J : SpatialNeckCylinder ≃ₘ⟮SpatialNeckCylinderModel, SpatialNeckCylinderModel⟯
      SpatialNeckCylinder, J = cylIso_C12X e.symm (-(σ * u₂)) σ hσ2 := ⟨_, rfl⟩
  have hJapp : ∀ y, J y = (sphereDiffeo (n := 2) e.symm y.1, -(σ * u₂) + σ * y.2) := fun y => by
    rw [hJ, cylIso_apply_C12X]
  have hJiso := localPullMetric_cylFam_cylIso_C12X hτ1 e.symm (-(σ * u₂)) σ hσ2
  rw [← hJ] at hJiso
  let ι3 : W → SpatialNeckCylinder := fun w' => w'.1.1.1
  have hι3 : IsLocalDiffeomorph SpatialNeckCylinderModel SpatialNeckCylinderModel ∞ ι3 :=
    isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val _)
      (isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val U)
        (isLocalDiffeomorph_subtype_val W))
  have hJb : ∀ w' : W, J (ι3 w') ∈ cylBand_C12X L := by
    intro w'
    refine ⟨mem_univ _, ?_⟩
    have h : |-(σ * u₂) + σ * (ι3 w').2| < L + 1 := by
      rw [show -(σ * u₂) + σ * (ι3 w').2 = σ * ((ι3 w').2 - u₂) by ring, abs_mul, hσabs, one_mul]
      exact w'.2
    rw [hJapp]
    exact abs_lt.mp h
  have hJι3 : IsLocalDiffeomorph SpatialNeckCylinderModel SpatialNeckCylinderModel ∞ (J ∘ ι3) :=
    isLocalDiffeomorph_comp J.isLocalDiffeomorph hι3
  let jW : W → cylBand_C12X L := fun w' => ⟨J (ι3 w'), hJb w'⟩
  have hjW : IsLocalDiffeomorph SpatialNeckCylinderModel SpatialNeckCylinderModel ∞ jW :=
    isLocalDiffeomorph_codRestrict_C12X (cylBand_C12X L) hJι3 hJb
  have hfun : (ι ∘ Ψ) ∘ (Subtype.val : W → U) = (Ξ ∘ f) ∘ jW := by
    funext w'
    have hmx := hpt w'.1 w'.2
    have hfj : f (jW w') = ⟨_, hmx.fst⟩ :=
      Subtype.ext ((hform (jW w')).trans (s16j_vec_aux _ _ _ _ _ _ (hJapp (ι3 w'))))
    exact hmx.snd.trans (congrArg Ξ hfj.symm)
  have hA : (localPullMetric (scaleMetric q hq gP) Ψ hΨ).restrictOpen W =
      localPullMetric (localPullMetric (localPullMetric (scaleMetric q hq gP') Ξ hΞ) f hf) jW
        hjW := by
    rw [localPullMetric_scaleMetric, hpost, ← localPullMetric_scaleMetric,
      ← localPullMetric_subtype_val _ W,
      localPullMetric_comp _ _ _ (isLocalDiffeomorph_comp hι hΨ) (isLocalDiffeomorph_subtype_val W)
        (isLocalDiffeomorph_comp (isLocalDiffeomorph_comp hι hΨ)
          (isLocalDiffeomorph_subtype_val W)),
      localPullMetric_comp _ _ _ hΞ hf (isLocalDiffeomorph_comp hΞ hf),
      localPullMetric_comp _ _ _ (isLocalDiffeomorph_comp hΞ hf) hjW
        (isLocalDiffeomorph_comp (isLocalDiffeomorph_comp hΞ hf) hjW)]
    exact s16j_localPull_congr _ hfun _ _
  have hC : (((cylFam_C12X τ).restrictOpen (neckBuffer δ)).restrictOpen U).restrictOpen W =
      localPullMetric ((cylFam_C12X τ).restrictOpen (cylBand_C12X L)) jW hjW := by
    have r1 : localPullMetric ((cylFam_C12X τ).restrictOpen (cylBand_C12X L)) jW hjW =
        localPullMetric (cylFam_C12X τ) (J ∘ ι3) hJι3 := by
      rw [← localPullMetric_subtype_val (cylFam_C12X τ) (cylBand_C12X L)]
      exact localPullMetric_comp (cylFam_C12X τ) Subtype.val jW
        (isLocalDiffeomorph_subtype_val (cylBand_C12X L)) hjW hJι3
    have r2 : localPullMetric (cylFam_C12X τ) (J ∘ ι3) hJι3 =
        localPullMetric (cylFam_C12X τ) ι3 hι3 := by
      rw [← localPullMetric_comp (cylFam_C12X τ) J ι3 J.isLocalDiffeomorph hι3 hJι3, hJiso]
    have r3 : (((cylFam_C12X τ).restrictOpen (neckBuffer δ)).restrictOpen U).restrictOpen W =
        localPullMetric (cylFam_C12X τ) ι3 hι3 := by
      rw [← localPullMetric_subtype_val (cylFam_C12X τ) (neckBuffer δ),
        ← localPullMetric_subtype_val _ U, ← localPullMetric_subtype_val _ W,
        localPullMetric_comp _ _ _ _ _ (isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val _)
          (isLocalDiffeomorph_subtype_val U))]
      exact localPullMetric_comp (cylFam_C12X τ)
        ((Subtype.val : neckBuffer δ → SpatialNeckCylinder) ∘ (Subtype.val : U → neckBuffer δ))
        (Subtype.val : W → U) (isLocalDiffeomorph_comp (isLocalDiffeomorph_subtype_val _)
          (isLocalDiffeomorph_subtype_val U)) (isLocalDiffeomorph_subtype_val W) hι3
    rw [r3, ← r2, ← r1]
  have h := metricDerivNorm_restrictOpen (localPullMetric (scaleMetric q hq gP) Ψ hΨ)
    (((cylFam_C12X τ).restrictOpen (neckBuffer δ)).restrictOpen U)
    (((cylFam_C12X τ).restrictOpen (neckBuffer δ)).restrictOpen U) W q' ⟨w, hwW⟩
  rw [hA, hC, metricDerivNorm_localPullMetric] at h
  have h2 := hcl q' hq' (jW ⟨w, hwW⟩)
  rw [h] at h2
  exact h2


end RetainedCoreHistory


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
