import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CoverCkErr_S90
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.PatchCore_S61
import DifferentialGeometry.Geometry.Metric.Comparison.PartialDiffeomorphDistance
import DifferentialGeometry.Geometry.Measure.LocalIsometry
import DifferentialGeometry.Geometry.Measure.OpenSubtypeVolume
import DifferentialGeometry.Geometry.Collapse.CurvatureScale

set_option autoImplicit false

/-!
# CH12-S117 / G1a: geometry of a `[1/4, 3]`-quasi-isometric injective map out of the model ball

Abstract in `(H, N, gb, f, U)`.  Given `f : H → N` smooth and injective on the open `U ⊇ B(o, 2R)` with
`(1/4) h ≤ f^*gb ≤ 3 h` on `U`:
* `edist_le_two_S117` : `d_gb(f o, f y) ≤ 2 d_h(o, y)` for `y ∈ B(o, ρ)`, `B(o, ρ) ⊆ U` (Lipschitz 2, `L² = 4 ≥ 3`);
* `volume_lower_S117` : `vol_gb(f '' S) ≥ vol_h(S) / 8` for open `S ⊆ U` (`h ≤ 4 f^*gb`, `√(4³) = 8`);
* `seed_geom_S117` : the three facts used by the LTF03 seed at `p' = f o`:
  (cover) `B_gb(f o, a) ⊆ f '' B(o, 2R)` for `a ≤ R/8`; (volume) `vol_h B(o, a/2) / 8 ≤ vol_gb B_gb(f o, a)`;
  (Lipschitz) `f '' B(o, 2R) ⊆ B_gb(f o, 4R)`.
-/

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology DifferentialGeometry.Topology.Manifold
  DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Hyperbolic DifferentialGeometry.Geometry.Collapse
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

theorem edist_le_two_S117 (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    [T2Space N] (gb : SmoothRiemannianMetric (𝓡 3) N) (f : H.Carrier → N)
    (U : TopologicalSpace.Opens H.Carrier)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (U : Set H.Carrier))
    (hinj : Set.InjOn f (U : Set H.Carrier))
    (hlow : ∀ p ∈ (U : Set H.Carrier), ∀ w : TangentSpace (𝓡 3) p,
      (1 / 4 : ℝ) * H.metric.inner p w w ≤
        gb.inner (f p) (mfderiv (𝓡 3) (𝓡 3) f p w) (mfderiv (𝓡 3) (𝓡 3) f p w))
    (hup : ∀ p ∈ (U : Set H.Carrier), ∀ w : TangentSpace (𝓡 3) p,
      gb.inner (f p) (mfderiv (𝓡 3) (𝓡 3) f p w) (mfderiv (𝓡 3) (𝓡 3) f p w) ≤
        3 * H.metric.inner p w w)
    {ρ : ℝ} (hρU : riemannianBallOf H.metric H.basepoint ρ ⊆ (U : Set H.Carrier))
    {y : H.Carrier} (hy : y ∈ riemannianBallOf H.metric H.basepoint ρ) :
    riemannianEDistOf gb (f H.basepoint) (f y) ≤
      ENNReal.ofReal 2 * riemannianEDistOf H.metric H.basepoint y := by
  obtain ⟨Φ, hs, hΦ⟩ := exists_partialDiffeomorph_of_lower_S90 H gb f U hf hinj (δ := 3 / 4)
    (by norm_num) (fun p hp w => by
      have := hlow p hp w
      norm_num
      linarith)
  have hfin : riemannianEDistOf H.metric H.basepoint y < ENNReal.ofReal ρ := hy
  have hdtop : riemannianEDistOf H.metric H.basepoint y ≠ ⊤ := ne_top_of_lt hfin
  have hρ0 : 0 < ρ := by
    by_contra hneg
    rw [not_lt] at hneg
    rw [ENNReal.ofReal_of_nonpos hneg] at hfin
    exact absurd hfin (not_lt_zero)
  have hdr : (riemannianEDistOf H.metric H.basepoint y).toReal < ρ :=
    ENNReal.toReal_lt_of_lt_ofReal hfin
  have hd0 : 0 ≤ (riemannianEDistOf H.metric H.basepoint y).toReal := ENNReal.toReal_nonneg
  set R'' : ℝ := ((riemannianEDistOf H.metric H.basepoint y).toReal + ρ) / 2 with hR''
  have hR''0 : 0 < R'' := by rw [hR'']; linarith
  have hR''ρ : R'' < ρ := by rw [hR'']; linarith
  have hsub : riemannianClosedBallOf H.metric H.basepoint R'' ⊆ riemannianBallOf H.metric H.basepoint ρ :=
    fun z hz => lt_of_le_of_lt hz ((ENNReal.ofReal_lt_ofReal_iff hρ0).mpr hR''ρ)
  have hsource : riemannianClosedBallOf H.metric H.basepoint R'' ⊆ Φ.source :=
    fun z hz => hs ▸ hρU (hsub hz)
  have hupper : ∀ z ∈ riemannianClosedBallOf H.metric H.basepoint R'', ∀ v : TangentSpace (𝓡 3) z,
      gb.inner (Φ z) (mfderiv (𝓡 3) (𝓡 3) (Φ : H.Carrier → N) z v)
        (mfderiv (𝓡 3) (𝓡 3) (Φ : H.Carrier → N) z v) ≤ 2 ^ 2 * H.metric.inner z v v := by
    intro z hz v
    rw [hΦ]
    have h1 := hup z (hρU (hsub hz)) v
    have h2 := metric_inner_self_nonneg H.metric z v
    nlinarith
  have hy' : riemannianEDistOf H.metric H.basepoint y < ENNReal.ofReal R'' :=
    lt_of_eq_of_lt (ENNReal.ofReal_toReal hdtop).symm
      ((ENNReal.ofReal_lt_ofReal_iff hR''0).mpr (by rw [hR'']; linarith))
  have key := DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.edistOf_map_le_of_metric_upper_on_ball
    H.metric gb Φ H.basepoint y hR''0 (by norm_num : (0 : ℝ) < 2) hsource hupper hy'
  rw [hΦ] at key
  exact key


theorem volume_lower_S117 (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    [T2Space N] [SigmaCompactSpace N] (gb : SmoothRiemannianMetric (𝓡 3) N) (f : H.Carrier → N)
    (U : TopologicalSpace.Opens H.Carrier)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (U : Set H.Carrier))
    (hinj : Set.InjOn f (U : Set H.Carrier))
    (hlow : ∀ p ∈ (U : Set H.Carrier), ∀ w : TangentSpace (𝓡 3) p,
      (1 / 4 : ℝ) * H.metric.inner p w w ≤
        gb.inner (f p) (mfderiv (𝓡 3) (𝓡 3) f p w) (mfderiv (𝓡 3) (𝓡 3) f p w))
    {S : Set H.Carrier} (hS : IsOpen S) (hSU : S ⊆ (U : Set H.Carrier)) :
    ENNReal.ofReal (1 / 8) *
        DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (𝓡 3) H.Carrier H.metric S ≤
      DifferentialGeometry.Integral.Measure.riemannianVolumeMeasure (𝓡 3) N gb (f '' S) := by
  classical
  let : MeasurableSpace H.Carrier := borel _
  have : BorelSpace H.Carrier := ⟨rfl⟩
  let : MeasurableSpace N := borel _
  have : BorelSpace N := ⟨rfl⟩
  let : MeasurableSpace U := borel _
  have : BorelSpace U := ⟨rfl⟩
  let : SigmaCompactSpace U := isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen (𝓡 3) U.isOpen)
  have hsm : ContMDiff (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) :=
    hf.comp_contMDiff contMDiff_subtype_val (fun x => x.2)
  have hmd : ∀ x : U, MDifferentiableAt (𝓡 3) (𝓡 3) f x.val := fun x =>
    (hf.mdifferentiableOn (by simp) x.val x.2).mdifferentiableAt (U.isOpen.mem_nhds x.2)
  have hcomp : ∀ x : U, mfderiv (𝓡 3) (𝓡 3) (fun x : U => f x) x =
      (mfderiv (𝓡 3) (𝓡 3) f x.val).comp (mfderiv (𝓡 3) (𝓡 3) (Subtype.val : U → _) x) :=
    fun x => mfderiv_comp x (hmd x) (hasMFDerivAt_subtype_val (I := 𝓡 3) U x).mdifferentiableAt
  have hfx : ∀ (x : U) (v : TangentSpace (𝓡 3) x),
      mfderiv (𝓡 3) (𝓡 3) (fun x : U => f x) x v = mfderiv (𝓡 3) (𝓡 3) f x.val v := by
    intro x v
    rw [hcomp x]
    simp only [ContinuousLinearMap.comp_apply, mfderiv_subtype_val_apply]
  have hf' : IsLocalDiffeomorph (𝓡 3) (𝓡 3) ∞ (fun x : U => f x) := by
    refine isLocalDiffeomorph_of_injective_mfderiv _ hsm (fun x v w hvw => ?_) rfl
    by_contra hne
    have hne' : v - w ≠ 0 := sub_ne_zero.mpr hne
    have h1 := hlow x.val x.2 (v - w)
    have hz : mfderiv (𝓡 3) (𝓡 3) f x.val (v - w) = 0 := by
      rw [← hfx, map_sub, hvw, sub_self]
    rw [hz] at h1
    have h2 := H.metric.pos x.val (v - w) hne'
    have h3 : gb.inner (f x.val) (0 : TangentSpace (𝓡 3) (f x.val))
        (0 : TangentSpace (𝓡 3) (f x.val)) = 0 := by simp
    rw [h3] at h1
    nlinarith
  have hinj' : Function.Injective (fun x : U => f x) := fun x y hxy =>
    Subtype.ext (hinj x.2 y.2 hxy)
  let gp := DifferentialGeometry.Geometry.Metric.pullbackMetricOfInjectiveLocalDiffeomorph gb
    (fun x : U => f x) hf' hinj'
  have hmetric : ∀ (x : U) (v w : TangentSpace (𝓡 3) x), gp.inner x v w =
      gb.inner (f x) (mfderiv (𝓡 3) (𝓡 3) (fun x : U => f x) x v)
        (mfderiv (𝓡 3) (𝓡 3) (fun x : U => f x) x w) :=
    DifferentialGeometry.Geometry.Metric.pullbackMetricOfInjectiveLocalDiffeomorph_inner gb
      (fun x : U => f x) hf' hinj'
  have hSopen : IsOpen ((Subtype.val : U → _) ⁻¹' S) := hS.preimage continuous_subtype_val
  have h1 := DifferentialGeometry.Geometry.Measure.riemannianVolumeMeasure_image_eq_of_injective_local_isometry
    gp gb (fun x : U => f x) hf' hinj' hmetric hSopen.measurableSet
  have himg : (fun x : U => f x) '' (Subtype.val ⁻¹' S) = f '' S := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x.val, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hSU hx⟩, hx, rfl⟩
  rw [← himg, ← h1]
  have hS2 := Geometry.Measure.riemannianVolumeMeasure_restrictOpen_preimage_of_subset
    H.metric U hS.measurableSet hSU
  have hcmp : ∀ x ∈ (Subtype.val ⁻¹' S : Set U), ∀ v : TangentSpace (𝓡 3) x,
      (H.metric.restrictOpen U).inner x v v ≤ (4 : ℝ) * gp.inner x v v := by
    intro x hx v
    rw [hmetric, hfx]
    have hlo := hlow x.val x.2 v
    change H.metric.inner x.val v v ≤ _
    nlinarith
  have hle := DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.riemannianVolumeMeasure_le_on gp
    (H.metric.restrictOpen U) hSopen.measurableSet (by norm_num : (0 : ℝ) < 4) hcmp
  rw [hS2] at hle
  have hc : ENNReal.ofReal (1 / 8) * ENNReal.ofReal (Real.sqrt ((4 : ℝ) ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)))) ≤ 1 := by
    rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    have : Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3 := by simp
    rw [this]
    have hs : Real.sqrt ((4 : ℝ) ^ 3) ≤ 8 := by
      rw [Real.sqrt_le_iff]
      refine ⟨by norm_num, ?_⟩
      norm_num
    nlinarith [Real.sqrt_nonneg ((4 : ℝ) ^ 3)]
  calc ENNReal.ofReal (1 / 8) * _ ≤ ENNReal.ofReal (1 / 8) * (ENNReal.ofReal (Real.sqrt ((4 : ℝ) ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))))
          * _) := mul_le_mul' le_rfl hle
    _ = (ENNReal.ofReal (1 / 8) * ENNReal.ofReal (Real.sqrt ((4 : ℝ) ^ Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))))) * _ := by rw [mul_assoc]
    _ ≤ 1 * _ := mul_le_mul' hc le_rfl
    _ = _ := one_mul _


/-- The three facts about `f` near the base point used by the seed at `p' = f o`. -/
theorem seed_geom_S117 (H : FiniteVolumeHyperbolicModel.{u}) {N : Type u}
    [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) N] [IsManifold (𝓡 3) ∞ N]
    [T3Space N] [SigmaCompactSpace N] (gb : SmoothRiemannianMetric (𝓡 3) N) (f : H.Carrier → N)
    (U : TopologicalSpace.Opens H.Carrier)
    (hf : ContMDiffOn (𝓡 3) (𝓡 3) ∞ f (U : Set H.Carrier))
    (hinj : Set.InjOn f (U : Set H.Carrier))
    (hlow : ∀ p ∈ (U : Set H.Carrier), ∀ w : TangentSpace (𝓡 3) p,
      (1 / 4 : ℝ) * H.metric.inner p w w ≤
        gb.inner (f p) (mfderiv (𝓡 3) (𝓡 3) f p w) (mfderiv (𝓡 3) (𝓡 3) f p w))
    (hup : ∀ p ∈ (U : Set H.Carrier), ∀ w : TangentSpace (𝓡 3) p,
      gb.inner (f p) (mfderiv (𝓡 3) (𝓡 3) f p w) (mfderiv (𝓡 3) (𝓡 3) f p w) ≤
        3 * H.metric.inner p w w)
    {R a : ℝ} (ha : 0 < a) (haR : a ≤ R / 8)
    (hRU : riemannianBallOf H.metric H.basepoint (2 * R) ⊆ (U : Set H.Carrier)) :
    riemannianBallOf gb (f H.basepoint) a ⊆ f '' riemannianBallOf H.metric H.basepoint (2 * R) ∧
      ENNReal.ofReal (1 / 8) * ballVolume H.metric H.basepoint (a / 2) ≤
        ballVolume gb (f H.basepoint) a ∧
      ∀ y ∈ riemannianBallOf H.metric H.basepoint (2 * R),
        f y ∈ riemannianBallOf gb (f H.basepoint) (4 * R) := by
  have hR : 0 < R := by linarith
  have hR2 : (0 : ℝ) < 2 * R := by linarith
  have hclo : riemannianClosedBallOf H.metric H.basepoint R ⊆ riemannianBallOf H.metric H.basepoint (2 * R) :=
    fun z hz => lt_of_le_of_lt hz ((ENNReal.ofReal_lt_ofReal_iff hR2).mpr (by linarith))
  have hlow' : ∀ p ∈ (U : Set H.Carrier), ∀ w : TangentSpace (𝓡 3) p,
      (1 - 3 / 4 : ℝ) * H.metric.inner p w w ≤
        gb.inner (f p) (mfderiv (𝓡 3) (𝓡 3) f p w) (mfderiv (𝓡 3) (𝓡 3) f p w) := by
    intro p hp w
    have := hlow p hp w
    norm_num
    linarith
  refine ⟨?_, ?_, ?_⟩
  · -- cover
    have hq : H.basepoint ∈ riemannianBallOf H.metric H.basepoint (R / 2) := by
      change riemannianEDistOf H.metric H.basepoint H.basepoint < _
      rw [riemannianEDistOf_self]
      exact (ENNReal.ofReal_pos.mpr (by linarith))
    have hsq : Real.sqrt (1 - 3 / 4 : ℝ) = 1 / 2 := by
      rw [show (1 - 3 / 4 : ℝ) = (1 / 2) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have hcov := ball_cover_of_lower_S90 H gb f U hf hinj (δ := 3 / 4) (by norm_num) hlow'
      (R := R) (hclo.trans hRU) hq (A := a) (by rw [hsq]; linarith)
    exact hcov.trans (Set.image_mono hclo)
  · -- volume
    have ha2 : riemannianBallOf H.metric H.basepoint (a / 2) ⊆ riemannianBallOf H.metric H.basepoint (2 * R) :=
      riemannianBallOf_mono _ _ (by linarith)
    have hv := volume_lower_S117 H gb f U hf hinj hlow (isOpen_riemannianBallOf_S61 H (a / 2))
      (ha2.trans hRU)
    refine hv.trans (MeasureTheory.measure_mono ?_)
    rintro _ ⟨y, hy, rfl⟩
    have hd := edist_le_two_S117 H gb f U hf hinj hlow hup (ha2.trans hRU) hy
    change riemannianEDistOf gb (f H.basepoint) (f y) < ENNReal.ofReal a
    refine lt_of_le_of_lt hd ?_
    have hy' : riemannianEDistOf H.metric H.basepoint y < ENNReal.ofReal (a / 2) := hy
    calc ENNReal.ofReal 2 * riemannianEDistOf H.metric H.basepoint y
        < ENNReal.ofReal 2 * ENNReal.ofReal (a / 2) :=
          (ENNReal.mul_lt_mul_iff_right (by simp) ENNReal.ofReal_ne_top).mpr hy'
      _ = ENNReal.ofReal a := by
          rw [← ENNReal.ofReal_mul (by norm_num)]
          congr 1
          ring
  · -- Lipschitz
    intro y hy
    have hd := edist_le_two_S117 H gb f U hf hinj hlow hup hRU hy
    change riemannianEDistOf gb (f H.basepoint) (f y) < ENNReal.ofReal (4 * R)
    refine lt_of_le_of_lt hd ?_
    have hy' : riemannianEDistOf H.metric H.basepoint y < ENNReal.ofReal (2 * R) := hy
    calc ENNReal.ofReal 2 * riemannianEDistOf H.metric H.basepoint y
        < ENNReal.ofReal 2 * ENNReal.ofReal (2 * R) :=
          (ENNReal.mul_lt_mul_iff_right (by simp) ENNReal.ofReal_ne_top).mpr hy'
      _ = ENNReal.ofReal (4 * R) := by
          rw [← ENNReal.ofReal_mul (by norm_num)]
          congr 1
          ring

end GC.LongTime.Ch12
