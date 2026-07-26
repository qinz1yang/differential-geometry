import DifferentialGeometry.Geometry.Exponential.IntrinsicExp
import DifferentialGeometry.Geometry.Exponential.LocalDiffeomorphism
import DifferentialGeometry.Geometry.Geodesic.LocalIsometry

set_option autoImplicit false

/-!
# Point-data rigidity for local isometries

Two metric-preserving local diffeomorphisms from a preconnected Riemannian
manifold are equal when their values and differentials agree at one point.

The proof is the normal-neighbourhood argument: a small exponential ray is a
geodesic, local isometries send it to geodesics, and geodesic uniqueness makes
the two image rays agree.  A tangent-bundle agreement locus then promotes the
local propagation statement to global equality.
-/

noncomputable section

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian

open Bundle Filter Manifold Set TopologicalSpace
open scoped Topology Manifold ContDiff
open Geodesic Exponential

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [CompleteSpace F]
  [NeZero (Module.finrank ℝ F)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J ∞ N]

private theorem small_ray_data
    [I.Boundaryless] [T2Space (TangentBundle I M)]
    (g : SmoothRiemannianMetric I M) (q : M) :
    ∃ ρ : ℝ, 0 < ρ ∧
      ∀ a : E, ‖a‖ < ρ →
        ∃ (γ : ℝ → M) (O : Set ℝ),
          IsOpen O ∧ IsPreconnected O ∧
          (0 : ℝ) ∈ O ∧ (1 : ℝ) ∈ O ∧
          ContinuousOn γ O ∧ IsGeodesicOn (I := I) g γ O ∧
          γ 0 = q ∧
          mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) =
            (show TangentSpace I q from a) ∧
          γ 1 = expMap (I := I) g q
            (show TangentSpace I q from a) := by
  classical
  obtain ⟨ρ₀, T, Φ, hρ₀, hT, hΦ_init, hΦ_target, hΦ_phase, _⟩ :=
    Exponential.exists_uniform_existence_interval (I := I) (g := g) (p := q)
  let t' : ℝ := T / 2
  have ht'_pos : 0 < t' := by
    dsimp [t']
    linarith
  have ht'_lt : t' < T := by
    dsimp [t']
    linarith
  refine ⟨t' * ρ₀, mul_pos ht'_pos hρ₀, ?_⟩
  intro a ha
  let vb : E := (1 / t') • a
  have ht'_ne : t' ≠ 0 := ne_of_gt ht'_pos
  have hvb_resc : t' • vb = a := by
    simp only [vb, smul_smul, mul_one_div, div_self ht'_ne, one_smul]
  have hvb_ball : vb ∈ Metric.ball (0 : E) ρ₀ := by
    rw [Metric.mem_ball, dist_zero_right]
    dsimp only [vb]
    rw [norm_smul]
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : (0 : ℝ) < 1 / t')]
    rw [one_div, ← div_eq_inv_mul, div_lt_iff₀ ht'_pos]
    simpa [mul_comm] using ha
  let γ : ℝ → M := fun s =>
    (Exponential.chartFlowOrbitLiftRescaled (I := I) Φ q t' vb s).proj
  let O : Set ℝ := Set.Ioo (-T / t') (T / t')
  have hratio : T / t' = 2 := by
    dsimp [t']
    field_simp
  have h0O : (0 : ℝ) ∈ O := by
    dsimp only [O]
    rw [neg_div, hratio]
    norm_num
  have h1O : (1 : ℝ) ∈ O := by
    dsimp only [O]
    rw [neg_div, hratio]
    norm_num
  have hF_int :
      IsMIntegralCurveOn
        (Exponential.chartFlowOrbitLiftRescaled (I := I) Φ q t' vb)
        (Geodesic.geodesicVectorFieldChart (I := I) g q) O := by
    exact Exponential.chartFlowOrbitLiftRescaled_isMIntegralCurveOn_Ioo
      (I := I) g q vb ht'_pos
      (hΦ_target vb hvb_ball) (hΦ_phase vb hvb_ball)
  have hF0 :
      Exponential.chartFlowOrbitLiftRescaled (I := I) Φ q t' vb 0 =
        (⟨q, a⟩ : TangentBundle I M) := by
    rw [Exponential.chartFlowOrbitLiftRescaled_zero
      (I := I) q vb t' (hΦ_init vb hvb_ball), hvb_resc]
  have hcont : ContinuousOn γ O := by
    have hproj : Continuous (Bundle.TotalSpace.proj : TangentBundle I M → M) :=
      FiberBundle.continuous_proj E (TangentSpace I)
    exact hproj.comp_continuousOn hF_int.continuousOn
  have hinit : IsGeodesicOnWithInitial (I := I) g γ O q a := by
    exact ⟨Exponential.chartFlowOrbitLiftRescaled (I := I) Φ q t' vb,
      fun _ => rfl, hF0, hF_int⟩
  have hgeo : IsGeodesicOn (I := I) g γ O := by
    intro s hs
    have hts :
        t' * s ∈ Set.Ioo (-T) T :=
      Exponential.mul_mem_Ioo_of_pos_of_lt ht'_pos hs
    have hsrc :
        γ s ∈ (chartAt H q).source := by
      exact Exponential.chartFlowOrbitLiftRescaled_proj_mem_chartAt_source
        (I := I) q vb t' s
        (hΦ_target vb hvb_ball (t' * s) (Set.Ioo_subset_Icc_self hts))
    exact (hinit.isGeodesicAt (isOpen_Ioo.mem_nhds hs) hsrc).hasGeodesicEquationAt g
  have hstart : γ 0 = q := by
    exact congrArg Bundle.TotalSpace.proj hF0
  have hvel :
      mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) =
        (show TangentSpace I q from a) := by
    have hF_at :=
      hF_int.isMIntegralCurveAt (isOpen_Ioo.mem_nhds h0O)
    have hsrc0 :
        (Exponential.chartFlowOrbitLiftRescaled (I := I) Φ q t' vb 0).proj ∈
          (chartAt H q).source := by
      rw [hF0]
      exact mem_chart_source H q
    have hmfd :=
      Geodesic.IsMIntegralCurveAt.mfderiv_proj_one (I := I) hF_at hsrc0
    change mfderiv 𝓘(ℝ, ℝ) I
        (fun s =>
          (Exponential.chartFlowOrbitLiftRescaled (I := I) Φ q t' vb s).proj)
        0 (1 : ℝ) = a
    rw [hmfd, hF0]
  have hend :
      γ 1 = expMap (I := I) g q
        (show TangentSpace I q from a) := by
    have h :=
      Exponential.chartFlowOrbitLiftRescaled_proj_at_one
        (I := I) g q vb ht'_pos ht'_lt
        (hΦ_init vb hvb_ball) (hΦ_target vb hvb_ball)
        (hΦ_phase vb hvb_ball)
    rw [hvb_resc] at h
    exact h
  exact ⟨γ, O, isOpen_Ioo, isPreconnected_Ioo, h0O, h1O,
    hcont, hgeo, hstart, hvel, hend⟩

private def agreeLocus
    (f₁ f₂ : M → N) : Set M :=
  (Bundle.TotalSpace.proj ''
    {z : TangentBundle I M |
      tangentMap I J f₁ z ≠ tangentMap I J f₂ z})ᶜ

omit [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
  [FiniteDimensional ℝ F] [CompleteSpace F]
  [NeZero (Module.finrank ℝ F)]
  [IsManifold I ∞ M] [IsManifold J ∞ N] in
private theorem mem_agree_iff
    (f₁ f₂ : M → N) (x : M) :
    x ∈ agreeLocus (I := I) (J := J) f₁ f₂ ↔
      f₁ x = f₂ x ∧
        mfderiv I J f₁ x = mfderiv I J f₂ x := by
  constructor
  · intro hx
    simp only [agreeLocus, mem_compl_iff, mem_image, not_exists, not_and] at hx
    have htan : ∀ v : TangentSpace I x,
        tangentMap I J f₁ (⟨x, v⟩ : TangentBundle I M) =
          tangentMap I J f₂ (⟨x, v⟩ : TangentBundle I M) := by
      intro v
      by_contra hne
      exact hx ⟨x, v⟩ hne rfl
    have hbase : f₁ x = f₂ x :=
      congrArg Bundle.TotalSpace.proj (htan 0)
    refine ⟨hbase, ?_⟩
    ext v
    have hv :
        (⟨f₁ x, mfderiv I J f₁ x v⟩ : TangentBundle J N) =
          ⟨f₂ x, mfderiv I J f₂ x v⟩ := htan v
    rw [Bundle.TotalSpace.mk.injEq] at hv
    exact eq_of_heq hv.2
  · rintro ⟨hbase, hderiv⟩
    simp only [agreeLocus, mem_compl_iff, mem_image, not_exists, not_and]
    rintro ⟨y, v⟩ hne rfl
    refine hne ?_
    simp only [tangentMap, hderiv]
    exact congrArg
      (fun z => (⟨z, mfderiv I J f₂ y v⟩ : TangentBundle J N))
      hbase

omit [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
  [FiniteDimensional ℝ F] [CompleteSpace F]
  [NeZero (Module.finrank ℝ F)] in
private theorem agree_closed
    [T2Space (TangentBundle J N)]
    {f₁ f₂ : M → N}
    (h₁ : ContMDiff I J 2 f₁)
    (h₂ : ContMDiff I J 2 f₂) :
    IsClosed (agreeLocus (I := I) (J := J) f₁ f₂) :=
  isClosed_compl_iff.mpr <|
    FiberBundle.isOpenMap_proj E (TangentSpace I) _
      (isClosed_eq
        (h₁.continuous_tangentMap (by norm_num))
        (h₂.continuous_tangentMap (by norm_num))).isOpen_compl

omit [FiniteDimensional ℝ E] [CompleteSpace E]
  [NeZero (Module.finrank ℝ E)]
  [FiniteDimensional ℝ F] [CompleteSpace F]
  [NeZero (Module.finrank ℝ F)] in
private theorem eq_of_point_data
    [PreconnectedSpace M] [T2Space (TangentBundle J N)]
    {f₁ f₂ : M → N}
    (h₁ : ContMDiff I J 2 f₁)
    (h₂ : ContMDiff I J 2 f₂)
    (hprop : ∀ q : M,
      f₁ q = f₂ q →
      mfderiv I J f₁ q = mfderiv I J f₂ q →
      f₁ =ᶠ[𝓝 q] f₂)
    (p : M) (hp : f₁ p = f₂ p)
    (hdp : mfderiv I J f₁ p = mfderiv I J f₂ p) :
    f₁ = f₂ := by
  have hclosed :
      IsClosed (agreeLocus (I := I) (J := J) f₁ f₂) :=
    agree_closed h₁ h₂
  have hopen :
      IsOpen (agreeLocus (I := I) (J := J) f₁ f₂) := by
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨hbase, hderiv⟩ :=
      (mem_agree_iff (I := I) (J := J) f₁ f₂ x).mp hx
    obtain ⟨U, hU, hUeq⟩ :=
      Filter.eventually_iff_exists_mem.mp (hprop x hbase hderiv)
    obtain ⟨V, hVU, hVopen, hxV⟩ := mem_nhds_iff.mp hU
    refine Filter.mem_of_superset (hVopen.mem_nhds hxV) ?_
    intro y hy
    have heq : f₁ =ᶠ[𝓝 y] f₂ :=
      Filter.eventually_iff_exists_mem.mpr
        ⟨V, hVopen.mem_nhds hy, fun z hz => hUeq z (hVU hz)⟩
    exact (mem_agree_iff (I := I) (J := J) f₁ f₂ y).mpr
      ⟨heq.eq_of_nhds, heq.mfderiv_eq⟩
  have huniv :=
    IsClopen.eq_univ ⟨hclosed, hopen⟩
      ⟨p, (mem_agree_iff (I := I) (J := J) f₁ f₂ p).mpr ⟨hp, hdp⟩⟩
  funext x
  exact ((mem_agree_iff (I := I) (J := J) f₁ f₂ x).mp
    (huniv ▸ Set.mem_univ x)).1

/-- Two metric-preserving local diffeomorphisms that agree to first order at
one point agree on a neighbourhood of that point. -/
theorem localIso_eventually
    [I.Boundaryless] [J.Boundaryless]
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold J N]
    [T2Space (TangentBundle I M)]
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold J 1 N] [IsManifold J ((∞ : WithTop ℕ∞) + 1) N]
    (g : SmoothRiemannianMetric I M)
    (g' : SmoothRiemannianMetric J N)
    {f₁ f₂ : M → N}
    (hld₁ : IsLocalDiffeomorph I J ∞ f₁)
    (hld₂ : IsLocalDiffeomorph I J ∞ f₂)
    (hpres₁ : ∀ (x : M) (v w : TangentSpace I x),
      g.inner x v w =
        g'.inner (f₁ x) (mfderiv I J f₁ x v) (mfderiv I J f₁ x w))
    (hpres₂ : ∀ (x : M) (v w : TangentSpace I x),
      g.inner x v w =
        g'.inner (f₂ x) (mfderiv I J f₂ x v) (mfderiv I J f₂ x w))
    (q : M) (hq : f₁ q = f₂ q)
    (hdq : mfderiv I J f₁ q = mfderiv I J f₂ q) :
    f₁ =ᶠ[𝓝 q] f₂ := by
  classical
  obtain ⟨ρ, hρ, hray⟩ := small_ray_data (I := I) g q
  have hkey : ∀ a : E, ‖a‖ < ρ →
      f₁ (expMap (I := I) g q (show TangentSpace I q from a)) =
        f₂ (expMap (I := I) g q (show TangentSpace I q from a)) := by
    intro a ha
    obtain ⟨γ, O, hO, hOconn, h0O, h1O, hcont, hgeo,
      hγ0, hγv, hγ1⟩ := hray a ha
    have hgeo₁ : IsGeodesicOn (I := J) g'
        (fun t => f₁ (γ t)) O :=
      Geodesic.geoOn_map_localIso (I := I) (J := J)
        g g' hld₁ hpres₁ hO hcont hgeo
    have hgeo₂ : IsGeodesicOn (I := J) g'
        (fun t => f₂ (γ t)) O :=
      Geodesic.geoOn_map_localIso (I := I) (J := J)
        g g' hld₂ hpres₂ hO hcont hgeo
    have hcont₁ : ContinuousOn (fun t => f₁ (γ t)) O :=
      hld₁.contMDiff.continuous.comp_continuousOn hcont
    have hcont₂ : ContinuousOn (fun t => f₂ (γ t)) O :=
      hld₂.contMDiff.continuous.comp_continuousOn hcont
    have hγmd : MDifferentiableAt 𝓘(ℝ, ℝ) I γ 0 :=
      (Geodesic.isGeodesicOn_contMDiffAt_infty
        (I := I) g hO h0O hgeo hcont).mdifferentiableAt (by decide)
    have hmfd₁ :
        mfderiv 𝓘(ℝ, ℝ) J (fun t => f₁ (γ t)) 0 (1 : ℝ) =
          mfderiv I J f₁ q a := by
      have hfmd : MDifferentiableAt I J f₁ (γ 0) := by
        rw [hγ0]
        exact (hld₁ q).mdifferentiableAt (by decide)
      have hcomp :=
        mfderiv_comp_apply
          (I := 𝓘(ℝ, ℝ)) (I' := I) (I'' := J)
          (g := f₁) (f := γ) (x := 0)
          hfmd hγmd (1 : ℝ)
      rw [hγ0] at hcomp
      have hγvE :
          (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) : E) = a := hγv
      calc
        mfderiv 𝓘(ℝ, ℝ) J (fun t => f₁ (γ t)) 0 (1 : ℝ) =
            mfderiv I J f₁ q
              (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ)) := by
          simpa only [Function.comp_def] using hcomp
        _ = mfderiv I J f₁ q a := congrArg (mfderiv I J f₁ q) hγvE
    have hmfd₂ :
        mfderiv 𝓘(ℝ, ℝ) J (fun t => f₂ (γ t)) 0 (1 : ℝ) =
          mfderiv I J f₂ q a := by
      have hfmd : MDifferentiableAt I J f₂ (γ 0) := by
        rw [hγ0]
        exact (hld₂ q).mdifferentiableAt (by decide)
      have hcomp :=
        mfderiv_comp_apply
          (I := 𝓘(ℝ, ℝ)) (I' := I) (I'' := J)
          (g := f₂) (f := γ) (x := 0)
          hfmd hγmd (1 : ℝ)
      rw [hγ0] at hcomp
      have hγvE :
          (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ) : E) = a := hγv
      calc
        mfderiv 𝓘(ℝ, ℝ) J (fun t => f₂ (γ t)) 0 (1 : ℝ) =
            mfderiv I J f₂ q
              (mfderiv 𝓘(ℝ, ℝ) I γ 0 (1 : ℝ)) := by
          simpa only [Function.comp_def] using hcomp
        _ = mfderiv I J f₂ q a := congrArg (mfderiv I J f₂ q) hγvE
    have hvel :
        (mfderiv 𝓘(ℝ, ℝ) J (fun t => f₁ (γ t)) 0 (1 : ℝ) : F) =
          mfderiv 𝓘(ℝ, ℝ) J (fun t => f₂ (γ t)) 0 (1 : ℝ) := by
      rw [hmfd₁, hmfd₂, hdq]
      rfl
    have hzero : f₁ (γ 0) = f₂ (γ 0) := by
      rw [hγ0]
      exact hq
    letI : RiemannianBundle (fun x : N => TangentSpace J x) :=
      ⟨g'.toRiemannianMetric⟩
    have heq :=
      Exponential.geo_eqOn_of_init (I := J) g'
        hO hOconn h0O hgeo₁ hgeo₂ hcont₁ hcont₂ hzero hvel
    have h1 := heq h1O
    simpa [hγ1] using h1
  obtain ⟨Φ, h0Φ, hΦexp⟩ :=
    Exponential.exists_open_nhds_expMap_diffeoOn (I := I) g q
  let U : Opens E :=
    ⟨Φ.source ∩ Metric.ball (0 : E) ρ,
      Φ.open_source.inter Metric.isOpen_ball⟩
  have hUΦ : (U : Set E) ⊆ Φ.source := fun _ hu => hu.1
  have hUopen :
      IsOpen ((Φ : E → M) '' (U : Set E)) :=
    image_opens_isOpen Φ hUΦ
  have hqU : q ∈ (Φ : E → M) '' (U : Set E) := by
    refine ⟨0, ⟨h0Φ, Metric.mem_ball_self hρ⟩, ?_⟩
    rw [hΦexp 0 h0Φ]
    exact expMap_zero (I := I) g q
  refine Filter.eventually_of_mem (hUopen.mem_nhds hqU) ?_
  intro x hx
  obtain ⟨a, ha, rfl⟩ := hx
  rw [hΦexp a ha.1]
  exact hkey a (by simpa using ha.2)

/-- A metric-preserving local diffeomorphism is determined by its value and
differential at one point of a preconnected source. -/
theorem localIso_rigid
    [PreconnectedSpace M]
    [I.Boundaryless] [J.Boundaryless]
    [SigmaCompactSpace M] [T2Space M] [BoundarylessManifold I M]
    [SigmaCompactSpace N] [T2Space N] [BoundarylessManifold J N]
    [T2Space (TangentBundle I M)] [T2Space (TangentBundle J N)]
    [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
    [IsManifold J 1 N] [IsManifold J ((∞ : WithTop ℕ∞) + 1) N]
    (g : SmoothRiemannianMetric I M)
    (g' : SmoothRiemannianMetric J N)
    {f₁ f₂ : M → N}
    (hld₁ : IsLocalDiffeomorph I J ∞ f₁)
    (hld₂ : IsLocalDiffeomorph I J ∞ f₂)
    (hpres₁ : ∀ (x : M) (v w : TangentSpace I x),
      g.inner x v w =
        g'.inner (f₁ x) (mfderiv I J f₁ x v) (mfderiv I J f₁ x w))
    (hpres₂ : ∀ (x : M) (v w : TangentSpace I x),
      g.inner x v w =
        g'.inner (f₂ x) (mfderiv I J f₂ x v) (mfderiv I J f₂ x w))
    (p : M) (hp : f₁ p = f₂ p)
    (hdp : mfderiv I J f₁ p = mfderiv I J f₂ p) :
    f₁ = f₂ := by
  apply eq_of_point_data
    (hld₁.contMDiff.of_le (by decide : (2 : WithTop ℕ∞) ≤ ∞))
    (hld₂.contMDiff.of_le (by decide : (2 : WithTop ℕ∞) ≤ ∞))
    (fun q hq hdq =>
      localIso_eventually (I := I) (J := J)
        g g' hld₁ hld₂ hpres₁ hpres₂ q hq hdq)
    p hp hdp

end Riemannian
end Geometry
end DifferentialGeometry
