import DifferentialGeometry.Geometry.Exponential.MinimizingGeodesic
import DifferentialGeometry.Geometry.Metric.Path.Composition
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.Algebra.LieGroup

set_option autoImplicit false

noncomputable section
open Bundle Filter Manifold MeasureTheory Set Metric
open scoped Manifold ContDiff ENNReal NNReal Topology
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.Exponential
namespace DifferentialGeometry.Geometry.Fibration
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace
variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  [MetricSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space (TangentBundle I M)] [SigmaCompactSpace M] [ConnectedSpace M]
  [CompleteSpace M] [RiemannianBundle (fun x : M => TangentSpace I x)]
  [IsRiemannianManifold I M]
  [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]

/-- A genuine smooth minimizing path remains in the SAME tested ball. -/
theorem exists_minimizing_path_in_ball
    (g : SmoothRiemannianMetric I M) (hmetric : IsMetricNorm g)
    (p : M) {L : ℝ} (hL : 0 < L) {x : M} (hx : x ∈ ball p L) :
    ∃ γ : ℝ → M, ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1) ∧
      γ 0 = p ∧ γ 1 = x ∧ MapsTo γ (Icc 0 1) (ball p L) ∧
      pathELength I γ 0 1 = edist p x := by
  by_cases hxp : x = p
  · subst x
    refine ⟨fun _t => p, contMDiff_const.contMDiffOn, rfl, rfl, ?_, ?_⟩
    · exact fun _t _ht => mem_ball_self hL
    · simp [pathELength, mfderiv_const]
  obtain ⟨v, hv, hn⟩ := hopf_rinow_expMapIntrinsic_surjective_minimizing g hmetric p x
  let γ := intrinsicGeodesic g hmetric p v
  have hγ : ContMDiffOn 𝓘(ℝ, ℝ) I 1 γ (Icc 0 1) :=
    (intrinsicGeodesic_contMDiffOn g hmetric p v).mono (subset_univ _)
  have h0 : γ 0 = p := intrinsicGeodesic_zero g hmetric p v
  have h1 : γ 1 = x := by
    change intrinsicGeodesic g hmetric p v 1 = x
    rw [← expMapIntrinsic_def]
    exact hv
  have hn' : ENNReal.ofReal (Real.sqrt (g.inner p v v)) = edist p x := by
    rw [hn, ← IsRiemannianManifold.out]
    exact ENNReal.ofReal_toReal (edist_ne_top p x)
  have hlen : pathELength I γ 0 1 = edist p x := by
    apply le_antisymm
    · rw [pathELength_eq_lintegral_mfderiv_Icc]
      calc
        _ ≤ ∫⁻ _ in Icc (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt (g.inner p v v)) :=
          setLIntegral_mono' measurableSet_Icc
            (fun t _ht => intrinsicGeodesic_velocity_enorm_le g hmetric p v t)
        _ = edist p x := by rw [setLIntegral_const, hn', Real.volume_Icc]; simp
    · rw [IsRiemannianManifold.out (I := I)]
      exact riemannianEDist_le_pathELength hγ h0 h1 zero_le_one
  refine ⟨γ, hγ, h0, h1, ?_, hlen⟩
  intro t ht
  have hd : edist p (γ t) ≤ edist p x := by
    rw [IsRiemannianManifold.out (I := I)]
    calc
      _ ≤ pathELength I γ 0 t :=
        riemannianEDist_le_pathELength (hγ.mono (Icc_subset_Icc le_rfl ht.2)) h0 rfl ht.1
      _ ≤ pathELength I γ 0 1 := pathELength_mono le_rfl ht.2
      _ = _ := hlen
  rw [mem_ball, dist_comm]
  have hh : dist p (γ t) ≤ dist p x := by
    simpa only [edist_dist, ENNReal.ofReal_le_ofReal_iff dist_nonneg] using hd
  exact hh.trans_lt (by simpa only [mem_ball, dist_comm] using hx)

/-- One-point C0 control and an actual mfderiv bound integrate on a complete manifold. -/
theorem norm_map_le_of_mfderiv_ball_bound {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (g : SmoothRiemannianMetric I M) (hmetric : IsMetricNorm g)
    (f : M → V) (p : M) {L c e : ℝ} (hL : 0 < L) (hc : 0 ≤ c)
    (hf : ContMDiffOn I 𝓘(ℝ, V) 1 f (ball p L))
    (hdf : ∀ x ∈ ball p L, ‖mvfderiv I f x‖ ≤ c)
    (hp : ‖f p‖ ≤ e) : ∀ x ∈ ball p L, ‖f x‖ ≤ e + c * dist p x := by
  intro x hx
  obtain ⟨γ, hγ, h0, h1, hmem, hlen⟩ := exists_minimizing_path_in_ball g hmetric p hL hx
  let C : ℝ≥0 := ⟨c, hc⟩
  have hγd : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
      MDifferentiableAt 𝓘(ℝ, ℝ) I γ t := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (hγ.contMDiffAt (Icc_mem_nhds ht.1 ht.2)).mdifferentiableAt one_ne_zero
  have hfd : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
      MDifferentiableAt I 𝓘(ℝ, V) f (γ t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (hf.contMDiffAt (isOpen_ball.mem_nhds (hmem (mem_Icc_of_Ioo ht)))).mdifferentiableAt
      one_ne_zero
  have hs : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) 1),
      ‖mfderiv I 𝓘(ℝ, V) f (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)‖ₑ ≤
        (C : ℝ≥0∞) * ‖mfderiv 𝓘(ℝ, ℝ) I γ t 1‖ₑ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have hn := ((mvfderiv I f (γ t)).le_opNorm
      (mfderiv 𝓘(ℝ, ℝ) I γ t 1)).trans
        (mul_le_mul_of_nonneg_right (hdf _ (hmem (mem_Icc_of_Ioo ht))) (norm_nonneg _))
    rw [enorm_tangentSpace_vectorSpace]
    change ‖mvfderiv I f (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1)‖ₑ ≤ _
    rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_coe_nnreal]
    change ENNReal.ofReal _ ≤ ENNReal.ofReal c * ENNReal.ofReal _
    rw [← ENNReal.ofReal_mul hc]
    exact
      ENNReal.ofReal_le_ofReal hn
  have hcomp := hf.comp hγ hmem
  have hd : edist (f p) (f x) ≤ (C : ℝ≥0∞) * edist p x := by
    rw [IsRiemannianManifold.out (I := 𝓘(ℝ, V))]
    calc
      _ ≤ pathELength 𝓘(ℝ, V) (f ∘ γ) 0 1 :=
        riemannianEDist_le_pathELength hcomp (by simp [h0]) (by simp [h1]) zero_le_one
      _ ≤ (C : ℝ≥0∞) * pathELength I γ 0 1 :=
        pathELength_comp_le_of_enorm_mfderiv_le f C hγd hfd hs
      _ = _ := by rw [hlen]
  have hd' : dist (f p) (f x) ≤ c * dist p x := by
    rw [edist_dist, edist_dist, ← ENNReal.ofReal_coe_nnreal] at hd
    change ENNReal.ofReal (dist (f p) (f x)) ≤
      ENNReal.ofReal c * ENNReal.ofReal (dist p x) at hd
    rw [← ENNReal.ofReal_mul hc] at hd
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hc dist_nonneg)).mp hd
  calc
    ‖f x‖ ≤ ‖f p‖ + dist (f p) (f x) := by
      have hh := norm_le_norm_add_norm_sub (f p) (f x)
      simpa only [dist_eq_norm, norm_sub_rev] using hh
    _ ≤ e + c * dist p x := add_le_add hp hd'

/-- SAME centered affine error: value and actual differential bounds on the tested ball. -/
theorem centered_affine_c1_of_mfderiv_bound {k m : ℕ}
    (g : SmoothRiemannianMetric I M) (hmetric : IsMetricNorm g)
    (F : M → EuclideanSpace ℝ (Fin k)) (G : M → EuclideanSpace ℝ (Fin m))
    (A : EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin k))
    (p : M) {L c : ℝ} (hL : 0 < L) (hc : 0 ≤ c)
    (hF : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 1 F (ball p L))
    (hG : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin m)) 1 G (ball p L))
    (hd : ∀ x ∈ ball p L, ‖mvfderiv I F x -
      A.comp (mvfderiv I G x)‖ ≤ c) :
    let b := F p - A (G p)
    ∀ x ∈ ball p L,
      ‖F x - (A (G x) + b)‖ ≤ c * dist p x ∧
      max ‖F x - (A (G x) + b)‖
        ‖mvfderiv I F x -
          A.comp (mvfderiv I G x)‖ ≤ max 1 L * c := by
  let b := F p - A (G p)
  let f : M → EuclideanSpace ℝ (Fin k) := fun x => F x - (A (G x) + b)
  have hf : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin k)) 1 f (ball p L) :=
    hF.sub ((A.contMDiff.comp_contMDiffOn hG).add contMDiffOn_const)
  have hdf (x : M) (hx : x ∈ ball p L) :
      mvfderiv I f x =
        mvfderiv I F x -
          A.comp (mvfderiv I G x) := by
    have hFd := (hF.contMDiffAt (isOpen_ball.mem_nhds hx)).mdifferentiableAt one_ne_zero
    have hGd := (hG.contMDiffAt (isOpen_ball.mem_nhds hx)).mdifferentiableAt one_ne_zero
    have hAG := A.contMDiff.mdifferentiableAt one_ne_zero |>.comp x hGd
    change mvfderiv I (F - (A ∘ G + fun _x => b)) x = _
    rw [mvfderiv_sub hFd (hAG.add mdifferentiableAt_const),
      mvfderiv_add hAG mdifferentiableAt_const, mvfderiv_const, add_zero,
      mvfderiv_comp x (A.contMDiff.mdifferentiableAt one_ne_zero) hGd,
      mvfderiv_eq_fderiv, A.fderiv]
    rfl
  have hv := norm_map_le_of_mfderiv_ball_bound g hmetric f p hL hc hf
    (fun x hx => by rw [hdf x hx]; exact hd x hx) (e := 0) (by simp [f, b])
  dsimp only
  intro x hx
  have hval : ‖F x - (A (G x) + b)‖ ≤ c * dist p x := by simpa [f] using hv x hx
  refine ⟨hval, max_le ?_ ?_⟩
  · rw [mul_comm (max 1 L)]
    exact hval.trans (mul_le_mul_of_nonneg_left
      ((le_of_lt (by simpa only [mem_ball, dist_comm] using hx)).trans (le_max_right 1 L)) hc)
  · exact (hd x hx).trans (le_mul_of_one_le_left hc (le_max_left 1 L))

end DifferentialGeometry.Geometry.Fibration
