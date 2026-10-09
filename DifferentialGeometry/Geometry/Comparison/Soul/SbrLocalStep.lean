import DifferentialGeometry.Geometry.Comparison.Soul.SbrDirectional
import DifferentialGeometry.Geometry.Comparison.Soul.NormalBundleCompactness

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set
open scoped Topology ContDiff Manifold NNReal
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential

namespace DifferentialGeometry.Geometry.Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [MetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M] [CompleteSpace M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

theorem exists_local_superlevel_step_of_positive_direction
    (g : SmoothRiemannianMetric I M) (hEnorm : IsMetricNorm g)
    {F : M → ℝ} (hF : Continuous F)
    (hconc : ∀ (q : M) (w : TangentSpace I q),
      ConcaveOn ℝ univ (fun t => F (intrinsicGeodesic g hEnorm q w t)))
    (p : M) (v : TangentSpace I p) (hunit : g.inner p v v = 1)
    {a : ℝ} (ha : 0 < a) (hder : a < intrinsicRightDerivative g hEnorm F p v) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ q ∈ U, ∀ τ : ℝ, 0 < τ → τ < δ →
        ∃ y : M, F q + τ ≤ F y ∧ dist q y ≤ τ / a := by
  obtain ⟨b, hab, hbD⟩ := exists_between hder
  have hb : 0 < b := ha.trans hab
  have hlim := tendsto_intrinsicRightDerivative g hEnorm F p v (hconc p v)
  have hboth : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t ∧
      b < (F (intrinsicGeodesic g hEnorm p v t) - F p) / t := by
    filter_upwards [self_mem_nhdsWithin, hlim.eventually (lt_mem_nhds hbD)] with t ht hbt
    exact ⟨ht, hbt⟩
  obtain ⟨t₀, ht₀, hsecant⟩ := hboth.exists
  let J : TangentBundle I M → ℝ := fun z =>
    (F (intrinsicGeodesic g hEnorm z.proj z.snd t₀) - F z.proj) / t₀
  let speed : TangentBundle I M → ℝ := fun z => Real.sqrt (g.inner z.proj z.snd z.snd)
  have hJ : Continuous J :=
    ((hF.comp (continuous_intrinsicGeodesic_fixed_time g hEnorm t₀)).sub
      (hF.comp (FiberBundle.continuous_proj E (TangentSpace I)))).div_const t₀
  have hspeed : Continuous speed :=
    Real.continuous_sqrt.comp (tangentSquaredLength_contMDiff g).continuous
  let W : Set (TangentBundle I M) := {z | b < J z ∧ speed z < b / a}
  have hW : IsOpen W :=
    (isOpen_lt continuous_const hJ).inter (isOpen_lt hspeed continuous_const)
  have hvW : (⟨p, v⟩ : TangentBundle I M) ∈ W := by
    refine ⟨hsecant, ?_⟩
    change Real.sqrt (g.inner p v v) < b / a
    rw [hunit, Real.sqrt_one, lt_div_iff₀ ha, one_mul]
    exact hab
  let U : Set M := (fun z : TangentBundle I M => z.proj) '' W
  have hU : IsOpen U := (FiberBundle.isOpenMap_proj E (TangentSpace I)) W hW
  refine ⟨U, hU, ⟨⟨p, v⟩, hvW, rfl⟩, b * t₀, mul_pos hb ht₀, ?_⟩
  rintro q ⟨⟨y, w⟩, hw, rfl⟩ τ hτ hτδ
  let s : ℝ := τ / b
  have hs : 0 < s := div_pos hτ hb
  have hst : s < t₀ := by
    apply (div_lt_iff₀ hb).2
    simpa only [mul_comm] using hτδ
  have hmono := ((hconc y w).neg.monotoneOn_slope_gt (mem_univ (0 : ℝ)))
    ⟨mem_univ s, hs⟩ ⟨mem_univ t₀, ht₀⟩ hst.le
  have hslope : (F (intrinsicGeodesic g hEnorm y w t₀) - F y) / t₀ ≤
      (F (intrinsicGeodesic g hEnorm y w s) - F y) / s := by
    simp only [Pi.neg_apply, slope_def_field, intrinsicGeodesic_zero, sub_zero] at hmono
    convert! neg_le_neg hmono using 1 <;> ring
  have hgain : F y + τ ≤ F (intrinsicGeodesic g hEnorm y w s) := by
    have hquot : b < (F (intrinsicGeodesic g hEnorm y w s) - F y) / s :=
      hw.1.trans_le hslope
    have hnum := (lt_div_iff₀ hs).mp hquot
    have heq : b * s = τ := by dsimp only [s]; field_simp [hb.ne']
    linarith
  refine ⟨intrinsicGeodesic g hEnorm y w s, hgain, ?_⟩
  have hed := intrinsicGeodesic_riemannianEDist_le g hEnorm y w hs.le
  have hd := ENNReal.toReal_mono ENNReal.ofReal_ne_top hed
  rw [← IsRiemannianManifold.out (I := I), edist_dist,
    ENNReal.toReal_ofReal dist_nonneg,
    ENNReal.toReal_ofReal (mul_nonneg (Real.sqrt_nonneg _) (sub_nonneg.mpr hs.le)),
    intrinsicGeodesic_zero, sub_zero] at hd
  have hspeedBound : Real.sqrt (g.inner y w w) < b / a := hw.2
  calc
    dist y (intrinsicGeodesic g hEnorm y w s) ≤ Real.sqrt (g.inner y w w) * s := hd
    _ ≤ (b / a) * s := mul_le_mul_of_nonneg_right hspeedBound.le hs.le
    _ = τ / a := by dsimp only [s]; field_simp [ha.ne', hb.ne']

end DifferentialGeometry.Geometry.Topology
