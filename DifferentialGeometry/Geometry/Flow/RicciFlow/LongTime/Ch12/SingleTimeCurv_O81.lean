import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.ThinBarrierTransferB_O27
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CompImmersion_S60

set_option autoImplicit false

/-! # CH12-O81 G1 (part A): single-time copy of the O27 curvature transfer.

`ThinBarrierTransferA/B_O27` are stated for a FAMILY `mp t` with accuracy `acc t → 0`, but every
proof reads the family at ONE time `t` only (plus `acc t` small).  Here the same proofs for ONE map
`φ : H → M_s` at ONE time `s`, on an open `U ⊇ B(base, 2/δ)`, with `ckErr_S45 … s⁻¹ φ k < δ` for
`k ≤ 2` on `B(base, 2/δ)` and `δ ≤ 1/10000`:
`localDiffeo_single_O81` (from `InjOn` + `ckErr0_immersion_S60`), metric bounds, first-exit capture,
curvature bridge, `hUp_single_O81` (no `-1/8` lower sectional bound at `φ y`) and
`hLow_single_O81` (universal `c₀`: sectional `≥ -(c₀²)⁻¹` on `B(φ y, c₀)`). -/

noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Tensor.RSTensor
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set Filter
open Manifold GC.LongTime DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff ENNReal Topology
universe u
namespace GC.LongTime.Ch12

section Single

variable {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
  {Hm : FiniteVolumeHyperbolicModel.{u}} {s δ : ℝ} {U : TopologicalSpace.Opens Hm.Carrier}
  {φ : Hm.Carrier → (postStage F.observation s).Carrier}

/-- `φ|U` is an injective local diffeomorphism: `InjOn` + order-0 `ckErr < 1` (injective differential). -/
theorem localDiffeo_single_O81 {c : ℝ} (hsm : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ U)
    (hinj : Set.InjOn φ U)
    (h0 : ∀ p ∈ (U : Set Hm.Carrier), ckErr_S45 Hm (postMetric F.observation s) c φ 0 p < 1) :
    IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fun x : U => φ x) ∧
      Function.Injective (fun x : U => φ x) := by
  have hcm : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : U => φ x) :=
    hsm.comp_contMDiff (f := fun x : U => x.val) contMDiff_subtype_val (fun x => x.2)
  refine ⟨isLocalDiffeomorph_of_injective_mfderiv _ hcm (fun x => ?_) rfl,
    fun x y hxy => Subtype.ext (hinj x.2 y.2 hxy)⟩
  have hmdf : MDifferentiableAt (𝓡 3) (𝓡 3) φ x.val :=
    (hsm.mdifferentiableOn (by simp) _ x.2).mdifferentiableAt (U.isOpen.mem_nhds x.2)
  have hval : MDifferentiableAt (𝓡 3) (𝓡 3) (Subtype.val : U → Hm.Carrier) x :=
    (hasMFDerivAt_subtype_val (I := 𝓡 3) U x).mdifferentiableAt
  have h1 : mfderiv (𝓡 3) (𝓡 3) (φ ∘ (Subtype.val : U → Hm.Carrier)) x =
      (mfderiv (𝓡 3) (𝓡 3) φ x.val).comp
        (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → Hm.Carrier) x) :=
    mfderiv_comp x hmdf hval
  have hI := (ckErr0_immersion_S60 Hm (postMetric F.observation s) c φ x.val (h0 _ x.2)).2
  change Function.Injective (mfderiv (𝓡 3) (𝓡 3) (φ ∘ (Subtype.val : U → Hm.Carrier)) x)
  rw [h1]
  intro a b hab
  simp only [ContinuousLinearMap.comp_apply, mfderiv_subtype_val_apply] at hab
  exact hI hab

theorem metric_abs_le_single_O81 (hs : 0 < s)
    (hck : ∀ k : ℕ, k ≤ 2 → ∀ p ∈ riemannianBallOf Hm.metric Hm.basepoint (2 * δ⁻¹),
      ckErr_S45 Hm (postMetric F.observation s) s⁻¹ φ k p < δ)
    (p : Hm.Carrier) (hp : p ∈ riemannianBallOf Hm.metric Hm.basepoint (2 * δ⁻¹))
    (v : TangentSpace (𝓡 3) p) :
    |(scaleMetric s⁻¹ (inv_pos.mpr hs) (postMetric F.observation s)).inner
        (φ p) (mfderiv (𝓡 3) (𝓡 3) φ p v) (mfderiv (𝓡 3) (𝓡 3) φ p v) -
        Hm.metric.inner p v v| ≤ δ * Hm.metric.inner p v v := by
  obtain ⟨basis, hON⟩ := exists_orthonormal_basis Hm.metric p
  have herr := hck 0 (Nat.zero_le _) p hp
  set E : Tensor0SSpace 2 (𝓡 3) p :=
    ((continuousMultilinearCurryFin1 ℝ (TangentSpace (𝓡 3) p) ℝ).symm.toContinuousLinearMap.comp
          ((s⁻¹ : ℝ) • localPullInner (postMetric F.observation s) φ p -
            Hm.metric.inner p)).uncurryLeft with hE
  change Real.sqrt (normSq0S Hm.metric p 2 E) < _ at herr
  have hbound := abs_apply_le_sqrt_normSq0S Hm.metric p 2 basis hON E (fun _ => v)
  have heval : E (fun _ => v) =
      (scaleMetric s⁻¹ (inv_pos.mpr hs) (postMetric F.observation s)).inner
        (φ p) (mfderiv (𝓡 3) (𝓡 3) φ p v) (mfderiv (𝓡 3) (𝓡 3) φ p v) -
        Hm.metric.inner p v v := rfl
  have hprod : (∏ _a : Fin 2, Real.sqrt (Hm.metric.inner p v v)) = Hm.metric.inner p v v := by
    rw [Fin.prod_univ_two, Real.mul_self_sqrt (metric_inner_self_nonneg _ _ _)]
  rw [heval, hprod] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_right herr.le (metric_inner_self_nonneg _ _ _))

theorem metric_lower_single_O81 (hs : 0 < s)
    (hck : ∀ k : ℕ, k ≤ 2 → ∀ p ∈ riemannianBallOf Hm.metric Hm.basepoint (2 * δ⁻¹),
      ckErr_S45 Hm (postMetric F.observation s) s⁻¹ φ k p < δ)
    (p : Hm.Carrier) (hp : p ∈ riemannianBallOf Hm.metric Hm.basepoint (2 * δ⁻¹))
    (v : TangentSpace (𝓡 3) p) :
    (1 - δ) * Hm.metric.inner p v v ≤
      (scaleMetric s⁻¹ (inv_pos.mpr hs) (postMetric F.observation s)).inner
        (φ p) (mfderiv (𝓡 3) (𝓡 3) φ p v) (mfderiv (𝓡 3) (𝓡 3) φ p v) := by
  have h := (abs_le.mp (metric_abs_le_single_O81 hs hck p hp v)).1
  linarith

theorem metric_upper_single_O81 (hs : 0 < s)
    (hck : ∀ k : ℕ, k ≤ 2 → ∀ p ∈ riemannianBallOf Hm.metric Hm.basepoint (2 * δ⁻¹),
      ckErr_S45 Hm (postMetric F.observation s) s⁻¹ φ k p < δ)
    (p : Hm.Carrier) (hp : p ∈ riemannianBallOf Hm.metric Hm.basepoint (2 * δ⁻¹))
    (v : TangentSpace (𝓡 3) p) :
    (scaleMetric s⁻¹ (inv_pos.mpr hs) (postMetric F.observation s)).inner
        (φ p) (mfderiv (𝓡 3) (𝓡 3) φ p v) (mfderiv (𝓡 3) (𝓡 3) φ p v) ≤
      (1 + δ) * Hm.metric.inner p v v := by
  have h := (abs_le.mp (metric_abs_le_single_O81 hs hck p hp v)).2
  linarith

theorem closedBall_subset_buffer_single_O81 (hδ : 0 < δ) (y : Hm.Carrier)
    (hy : y ∈ riemannianBallOf Hm.metric Hm.basepoint δ⁻¹) {R : ℝ} (hRn : R ≤ δ⁻¹) :
    riemannianClosedBallOf Hm.metric y R ⊆
      riemannianBallOf Hm.metric Hm.basepoint (2 * δ⁻¹) := by
  intro x hx
  have hnpos : 0 < δ⁻¹ := inv_pos.mpr hδ
  have h1 : riemannianEDistOf Hm.metric Hm.basepoint y < ENNReal.ofReal δ⁻¹ := hy
  have h2 : riemannianEDistOf Hm.metric y x ≤ ENNReal.ofReal R := hx
  have h3 := (riemannianEDistOf_triangle Hm.metric Hm.basepoint y x).trans_lt
    (ENNReal.add_lt_add_of_lt_of_le (h2.trans_lt ENNReal.ofReal_lt_top).ne h1
      (h2.trans (ENNReal.ofReal_le_ofReal hRn)))
  rw [← ENNReal.ofReal_add hnpos.le hnpos.le] at h3
  have : δ⁻¹ + δ⁻¹ = 2 * δ⁻¹ := by ring
  rwa [this] at h3

theorem ambient_ball_subset_image_single_O81 (hsm : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ U)
    (hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fun x : U => φ x) ∧
      Function.Injective (fun x : U => φ x))
    (gb : SmoothRiemannianMetric (𝓡 3) (postStage F.observation s).Carrier)
    (y : Hm.Carrier) (hy : y ∈ U) {R L : ℝ} (hR : 0 < R) (hL : 0 < L)
    (hsource : riemannianClosedBallOf Hm.metric y R ⊆ (U : Set _))
    (hlower : ∀ x ∈ riemannianClosedBallOf Hm.metric y R,
      ∀ v : TangentSpace (𝓡 3) x, Hm.metric.inner x v v ≤
        L ^ 2 * gb.inner (φ x) (mfderiv (𝓡 3) (𝓡 3) φ x v) (mfderiv (𝓡 3) (𝓡 3) φ x v)) :
    riemannianBallOf gb (φ y) (R / L) ⊆ φ '' riemannianClosedBallOf Hm.metric y R := by
  obtain ⟨hf, hinj⟩ := hf
  have hcap := DifferentialGeometry.Geometry.Metric.ball_subset_image_of_metric_lower_on_opens gb
    Hm.metric U (fun x : U => φ x) hf hinj ⟨y, hy⟩ hR hL
    (Hm.complete.closedEBall_isCompact y R) hsource (fun x hx v => by
      have hmd : MDifferentiableAt (𝓡 3) (𝓡 3) φ x.val :=
        (hsm.mdifferentiableOn (by simp) x.val x.2).mdifferentiableAt (U.isOpen.mem_nhds x.2)
      have hcomp : mfderiv (𝓡 3) (𝓡 3) (fun x : U => φ x) x =
          (mfderiv (𝓡 3) (𝓡 3) φ x.val).comp (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → _) x) :=
        mfderiv_comp x hmd (hasMFDerivAt_subtype_val (I := 𝓡 3) U x).mdifferentiableAt
      rw [hcomp]
      simp only [ContinuousLinearMap.comp_apply, mfderiv_subtype_val_apply]
      exact hlower x.val hx v)
  intro z hz
  obtain ⟨x, hx, rfl⟩ := hcap hz
  exact ⟨x.val, hx, rfl⟩

theorem partialDiffeo_single_O81
    (hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fun x : U => φ x) ∧
      Function.Injective (fun x : U => φ x))
    (z : Hm.Carrier) (hz : z ∈ U) :
    ∃ Φ : PartialDiffeomorph (𝓡 3) (𝓡 3) Hm.Carrier (postStage F.observation s).Carrier ∞,
      Φ.source = (U : Set Hm.Carrier) ∧ ∀ x ∈ (U : Set Hm.Carrier), Φ x = φ x := by
  obtain ⟨hf, hinj⟩ := hf
  let p : U := ⟨z, hz⟩
  let V := hf.image
  let e : Diffeomorph (𝓡 3) (𝓡 3) U V ∞ :=
    DifferentialGeometry.Topology.diffeomorphRangeOfInjective hf hinj
  let iU := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡 3) U ⟨p⟩
  let iV := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph (𝓡 3) V ⟨e p⟩
  let Φ := (iU.symm.trans e.toPartialDiffeomorph).trans iV
  have hsrc : Φ.source = (U : Set Hm.Carrier) := by
    ext x
    change ((x ∈ iU.target ∧ iU.symm x ∈ (univ : Set U)) ∧
      e (iU.symm x) ∈ (univ : Set V)) ↔ x ∈ U
    simp only [mem_univ, and_true, iU,
      DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target]
    rfl
  refine ⟨Φ, hsrc, fun x hx => ?_⟩
  change (e (iU.symm x) : (postStage F.observation s).Carrier) = _
  rw [show iU.symm x = (⟨x, hx⟩ : U) from
    DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply (𝓡 3) U ⟨p⟩ hx]
  rfl

theorem pullbackGerm_single_O81
    (hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fun x : U => φ x) ∧
      Function.Injective (fun x : U => φ x))
    (gb : SmoothRiemannianMetric (𝓡 3) (postStage F.observation s).Carrier)
    (z : Hm.Carrier) (hz : z ∈ U) :
    ∃ q : SmoothRiemannianMetric (𝓡 3) Hm.Carrier,
      (∀ᶠ w in 𝓝 z, q.inner w = localPullInner gb φ w) ∧
      ∀ κ : ℝ, SectionalBoundedBelowAt q z κ ↔ SectionalBoundedBelowAt gb (φ z) κ := by
  obtain ⟨Φ, hsrc, hΦ⟩ := partialDiffeo_single_O81 hf z hz
  have hzΦ : z ∈ Φ.source := by rw [hsrc]; exact hz
  have hK : ({Φ z} : Set (postStage F.observation s).Carrier) ⊆ Φ.symm.source := by
    intro y hy
    rcases Set.mem_singleton_iff.mp hy with rfl
    exact Φ.map_source' hzΦ
  obtain ⟨q, O', hKU, _, hmetric, _⟩ :=
    Φ.symm.exists_metric_preserving_on_neighborhood_of_is_compact
      gb Hm.metric isCompact_singleton hK
  let O : TopologicalSpace.Opens Hm.Carrier :=
    ⟨Φ.source ∩ (Φ : Hm.Carrier → (postStage F.observation s).Carrier) ⁻¹' O',
      Φ.toOpenPartialHomeomorph.isOpen_inter_preimage O'.isOpen⟩
  have hzO : z ∈ O := ⟨hzΦ, hKU (by simp)⟩
  have hiso : ∀ x ∈ (O : Set Hm.Carrier), ∀ a b : TangentSpace (𝓡 3) x,
      q.inner x a b = gb.inner (Φ x) (mfderiv (𝓡 3) (𝓡 3) Φ x a) (mfderiv (𝓡 3) (𝓡 3) Φ x b) := by
    intro x hx a b
    have hxsource : x ∈ Φ.source := hx.1
    have hxd : MDifferentiableAt (𝓡 3) (𝓡 3) Φ x :=
      (Φ.contMDiffOn_toFun.contMDiffAt
        (Φ.open_source.mem_nhds hxsource)).mdifferentiableAt (by simp)
    have hyd : MDifferentiableAt (𝓡 3) (𝓡 3) Φ.symm (Φ x) :=
      (Φ.contMDiffOn_invFun.contMDiffAt
        (Φ.open_target.mem_nhds (Φ.map_source' hxsource))).mdifferentiableAt (by simp)
    have heq : (Φ.symm : (postStage F.observation s).Carrier → Hm.Carrier) ∘ Φ =ᶠ[𝓝 x] id := by
      filter_upwards [Φ.open_source.mem_nhds hxsource] with y hy
      exact Φ.left_inv' hy
    have hinverse (v : TangentSpace (𝓡 3) x) :
        mfderiv (𝓡 3) (𝓡 3) Φ.symm (Φ x) (mfderiv (𝓡 3) (𝓡 3) Φ x v) = v := by
      have hc := mfderiv_comp_apply x hyd hxd v
      rw [heq.mfderiv_eq, mfderiv_id] at hc
      exact hc.symm
    have hg := hmetric (Φ x) hx.2 (mfderiv (𝓡 3) (𝓡 3) Φ x a) (mfderiv (𝓡 3) (𝓡 3) Φ x b)
    rw [hinverse a, hinverse b] at hg
    exact (congrArg (fun y : Hm.Carrier => q.inner y a b)
      (Φ.left_inv' hxsource)).symm.trans hg.symm
  refine ⟨q, ?_, fun κ => ?_⟩
  · filter_upwards [O.isOpen.mem_nhds hzO, U.isOpen.mem_nhds hz] with w hwO hwU
    have hev : (Φ : Hm.Carrier → _) =ᶠ[𝓝 w] φ := by
      filter_upwards [U.isOpen.mem_nhds hwU] with y hy using hΦ y hy
    ext a b
    rw [hiso w hwO a b, localPullInner_apply, hev.mfderiv_eq, hΦ w hwU]
    rfl
  · have h := sectionalBoundedBelowAt_iff_of_isometricOnOpen_BDRY1 q gb Φ O.isOpen
      (fun _ hx => hx.1) hiso hzO (κ := κ)
    rwa [hΦ z hz] at h

theorem curvature_bridge_single_O81 (hsm : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ U)
    (hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fun x : U => φ x) ∧
      Function.Injective (fun x : U => φ x))
    (hU : riemannianBallOf Hm.metric Hm.basepoint (2 * δ⁻¹) ⊆ U)
    (hck : ∀ k : ℕ, k ≤ 2 → ∀ p ∈ riemannianBallOf Hm.metric Hm.basepoint (2 * δ⁻¹),
      ckErr_S45 Hm (postMetric F.observation s) s⁻¹ φ k p < δ)
    (gb : SmoothRiemannianMetric (𝓡 3) (postStage F.observation s).Carrier)
    (hgb : ∀ w, localPullInner (I := 𝓡 3) (J := 𝓡 3) gb φ w =
      (s⁻¹ : ℝ) • localPullInner (I := 𝓡 3) (J := 𝓡 3) (postMetric F.observation s) φ w)
    (z : Hm.Carrier) (hz : z ∈ riemannianBallOf Hm.metric Hm.basepoint (2 * δ⁻¹)) :
    ∃ q : SmoothRiemannianMetric (𝓡 3) Hm.Carrier,
      (∀ j : ℕ, j ≤ 2 → metricDerivNorm j q Hm.metric Hm.metric z < δ) ∧
      ∀ κ : ℝ, SectionalBoundedBelowAt q z κ ↔ SectionalBoundedBelowAt gb (φ z) κ := by
  have hzd : z ∈ U := hU hz
  obtain ⟨q, hgerm, hiff⟩ := pullbackGerm_single_O81 hf gb z hzd
  refine ⟨q, fun j hj => ?_, hiff⟩
  have hzint : (𝓡 3).IsInteriorPoint z := BoundarylessManifold.isInteriorPoint
  have hφ : ContMDiffAt (𝓡 3) (𝓡 3) (2 + 1 : ℕ) φ z :=
    (hsm.contMDiffAt (U.isOpen.mem_nhds hzd)).of_le (by simp)
  have key := DifferentialGeometry.Geometry.metricDerivNorm_eq_raw_pullbackError_of_map_jets
    gb Hm.metric q (f := φ) (h := φ) (p := z) (n := 2)
    hzint BoundarylessManifold.isInteriorPoint rfl hφ hφ (fun _ _ => rfl) hgerm j hj
  have herr := hck j hj z hz
  unfold ckErr_S45 at herr
  simp only [← hgb] at herr
  rw [key]
  exact herr

theorem hUp_single_O81 (hs : 0 < s) (hsm : ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ U)
    (hf : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fun x : U => φ x) ∧
      Function.Injective (fun x : U => φ x))
    (hU : riemannianBallOf Hm.metric Hm.basepoint (2 * δ⁻¹) ⊆ U)
    (hck : ∀ k : ℕ, k ≤ 2 → ∀ p ∈ riemannianBallOf Hm.metric Hm.basepoint (2 * δ⁻¹),
      ckErr_S45 Hm (postMetric F.observation s) s⁻¹ φ k p < δ)
    (hδ : 0 < δ) (hacc : δ ≤ 1 / 10000)
    (y : Hm.Carrier) (hy : y ∈ riemannianBallOf Hm.metric Hm.basepoint δ⁻¹) :
    ¬ SectionalBoundedBelowAt (scaleMetric s⁻¹ (inv_pos.mpr hs) (postMetric F.observation s))
      (φ y) (-(1 / 8 : ℝ)) := by
  have hnpos : 0 < δ⁻¹ := inv_pos.mpr hδ
  have hy2 : y ∈ riemannianBallOf Hm.metric Hm.basepoint (2 * δ⁻¹) :=
    riemannianBallOf_mono _ _ (by linarith) hy
  obtain ⟨q, hq, hiff⟩ := curvature_bridge_single_O81 hsm hf hU hck
    (scaleMetric s⁻¹ (inv_pos.mpr hs) (postMetric F.observation s))
    (fun w => by
      ext a b
      simp only [localPullInner_apply, scaleMetric_inner, smul_apply, smul_eq_mul])
    y hy2
  obtain ⟨u, v, hu, hv, huv⟩ := exists_orthonormal_pair_model_S41 Hm y
  have href : ∀ a b : TangentSpace (𝓡 3) y,
      metricRm04StandardAt Hm.metric y a b b a =
        -(1 / 4 : ℝ) * (Hm.metric.inner y a a * Hm.metric.inner y b b -
          Hm.metric.inner y a b ^ 2) := fun a b => by
    rw [metricRm_eq_neg_quarter_S26 Hm y a b]; ring
  have hcurv : metricRm04StandardAt Hm.metric y u v v u ≤ -(1 / 4 : ℝ) := by
    rw [href u v, hu, hv, huv]; norm_num
  have hmodel : Real.sqrt (Hm.metric.inner y
      (riemannOp (LeviCivita Hm.metric) y u v v)
      (riemannOp (LeviCivita Hm.metric) y u v v)) ≤ 2 :=
    (sqrt_inner_riemannOp_self_eq_abs_of_constant_sectional_numerator
      Hm.metric y (-(1 / 4 : ℝ)) href u v hu hv huv).trans_le (by norm_num)
  have hnot := not_sectionalBoundedBelowAt_neg_one_eighth_of_small_metric_derivatives q
    Hm.metric y (eps := δ) hacc (fun j hj => (hq j hj).le) u v hu hv hcurv hmodel
  exact fun hs' => hnot ((hiff _).mpr hs')

end Single

/-- Single-time `hLow` (universal `c₀`, depends on the model only). -/
theorem hLow_single_O81 (Hm : FiniteVolumeHyperbolicModel.{u}) :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ {P : OrientedThreeStage.{u}} {g : P.Metric}
      (F : GC.Interface.RawSurgery P g) (s : ℝ) (hs : 0 < s) (δ : ℝ)
      (U : TopologicalSpace.Opens Hm.Carrier) (φ : Hm.Carrier → (postStage F.observation s).Carrier),
      ContMDiffOn (𝓡 3) (𝓡 3) ∞ φ U →
      (IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fun x : U => φ x) ∧
        Function.Injective (fun x : U => φ x)) →
      riemannianBallOf Hm.metric Hm.basepoint (2 * δ⁻¹) ⊆ U →
      (∀ k : ℕ, k ≤ 2 → ∀ p ∈ riemannianBallOf Hm.metric Hm.basepoint (2 * δ⁻¹),
        ckErr_S45 Hm (postMetric F.observation s) s⁻¹ φ k p < δ) →
      0 < δ → δ ≤ 1 / 10000 →
      ∀ y ∈ riemannianBallOf Hm.metric Hm.basepoint δ⁻¹,
      ∀ q ∈ riemannianBallOf (scaleMetric s⁻¹ (inv_pos.mpr hs) (postMetric F.observation s))
          (φ y) c₀,
        SectionalBoundedBelowAt (scaleMetric s⁻¹ (inv_pos.mpr hs) (postMetric F.observation s))
          q (-(c₀ ^ 2)⁻¹) := by
  obtain ⟨C0, hCpos0, hCC⟩ :=
    DifferentialGeometry.Geometry.Curvature.exists_pos_bound_intrinsic_curvature_derivative_of_metric_error
      (I := 𝓡 3) (M := Hm.Carrier) 0 (1 / 2) 1 (by norm_num)
  set Cs : ℝ := 1 + C0 with hCs
  have hCs1 : 1 ≤ Cs := by linarith
  have hCle : C0 ≤ Cs := by linarith
  refine ⟨min 1 (1 / Cs), lt_min one_pos (by positivity),
    fun F s hs δ U φ hsm hf hU hck hδ hacc1 y hy q hq => ?_⟩
  have hnpos : 0 < δ⁻¹ := inv_pos.mpr hδ
  have hn : (10000 : ℝ) ≤ δ⁻¹ := by
    rw [le_inv_comm₀ (by norm_num) hδ]
    simpa using hacc1
  have hacc : δ ≤ 1 / 2 := by linarith
  have hyd : y ∈ U := hU (riemannianBallOf_mono _ _ (by linarith) hy)
  -- first exit
  have hsource : riemannianClosedBallOf Hm.metric y 4 ⊆ (U : Set _) :=
    fun z hz => hU (closedBall_subset_buffer_single_O81 hδ y hy (by linarith) hz)
  have hlow4 : ∀ x ∈ riemannianClosedBallOf Hm.metric y 4, ∀ v : TangentSpace (𝓡 3) x,
      Hm.metric.inner x v v ≤ (2 : ℝ) ^ 2 *
        (scaleMetric s⁻¹ (inv_pos.mpr hs) (postMetric F.observation s)).inner (φ x)
          (mfderiv (𝓡 3) (𝓡 3) φ x v) (mfderiv (𝓡 3) (𝓡 3) φ x v) := by
    intro x hx v
    have hlo := metric_lower_single_O81 hs hck x
      (closedBall_subset_buffer_single_O81 hδ y hy (by linarith) hx) v
    have hnn := metric_inner_self_nonneg Hm.metric x v
    nlinarith
  have hcap := ambient_ball_subset_image_single_O81 hsm hf
    (scaleMetric s⁻¹ (inv_pos.mpr hs) (postMetric F.observation s))
    y hyd (R := 4) (L := 2) (by norm_num) (by norm_num) hsource hlow4
  have hc1 : min 1 (1 / Cs) ≤ 4 / 2 := (min_le_left _ _).trans (by norm_num)
  obtain ⟨z, hz4, rfl⟩ := hcap (riemannianBallOf_mono _ _ hc1 hq)
  have hz2 : z ∈ riemannianBallOf Hm.metric Hm.basepoint (2 * δ⁻¹) :=
    closedBall_subset_buffer_single_O81 hδ y hy (by linarith) hz4
  obtain ⟨q', hq', hiff⟩ := curvature_bridge_single_O81 hsm hf hU hck
    (scaleMetric s⁻¹ (inv_pos.mpr hs) (postMetric F.observation s))
    (fun w => by
      ext a b
      simp only [localPullInner_apply, scaleMetric_inner, smul_apply, smul_eq_mul])
    z hz2
  -- reference norm bound
  have hsec : ∀ a b : TangentSpace (𝓡 3) z,
      metricRm04StandardAt Hm.metric z a b b a =
        -(1 / 4 : ℝ) * (Hm.metric.inner z a a * Hm.metric.inner z b b -
          Hm.metric.inner z a b ^ 2) := fun a b => by
    rw [metricRm_eq_neg_quarter_S26 Hm z a b]; ring
  have hnorm := normSq0S_metricRm04At_eq_of_constant_sectional_numerator
    Hm.metric z (-(1 / 4 : ℝ)) hsec
  have hrank : (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) : ℝ) = 3 := by simp
  rw [hrank] at hnorm
  have hRef : ∀ j ≤ 0, Real.sqrt (normSq0S Hm.metric z (4 + j)
      (iterCov Hm.metric 4 (metricRm04 Hm.metric) j z)) ≤ 1 := by
    intro j hj
    obtain rfl : j = 0 := Nat.le_zero.mp hj
    refine Real.sqrt_le_one.mpr ?_
    have h0 : normSq0S Hm.metric z (4 + 0)
        (iterCov Hm.metric 4 (metricRm04 Hm.metric) 0 z) =
        normSq0S Hm.metric z 4 (metricRm04At Hm.metric z) := rfl
    rw [h0, hnorm]; norm_num
  have hbd := hCC Hm.metric q' z (fun j hj => (hq' j (by omega)).le.trans hacc) hRef
  have hbd' : normSq0S q' z 4 (metricRm04At q' z) ≤ C0 ^ 2 := by
    have h0 : normSq0S q' z (4 + 0) (iterCov q' 4 (metricRm04 q') 0 z) =
        normSq0S q' z 4 (metricRm04At q' z) := rfl
    rw [h0] at hbd
    exact Real.sqrt_le_left hCpos0.le |>.mp hbd
  have hsecq := DifferentialGeometry.PDE.RicciFlow.sectionalBoundedBelowAt_neg_sqrt_of_normSq0S_le
    (I := 𝓡 3) q' z hbd'
  rw [Real.sqrt_sq hCpos0.le] at hsecq
  refine ((hiff _).mp hsecq).mono ?_
  -- `Cs ≤ (c₀²)⁻¹`
  have hc0 : 0 < min 1 (1 / Cs) := lt_min one_pos (by positivity)
  have hc1' : min 1 (1 / Cs) ≤ 1 := min_le_left _ _
  have hc2 : min 1 (1 / Cs) ≤ 1 / Cs := min_le_right _ _
  have hsq : (min 1 (1 / Cs)) ^ 2 ≤ 1 / Cs := by nlinarith
  have hinv : Cs ≤ ((min 1 (1 / Cs)) ^ 2)⁻¹ := by
    rw [le_inv_comm₀ (by linarith) (by positivity)]
    simpa [one_div] using hsq
  linarith [hCle]

end GC.LongTime.Ch12
