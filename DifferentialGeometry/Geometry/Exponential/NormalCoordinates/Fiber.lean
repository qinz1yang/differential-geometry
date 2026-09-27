import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Lift
import DifferentialGeometry.Geometry.Exponential.PathLifting
import DifferentialGeometry.Geometry.Exponential.RadialPath
import DifferentialGeometry.Geometry.Metric.Distance.Basic
import DifferentialGeometry.Bundle.FiberBundleHausdorff

noncomputable section

open Bundle Function Manifold Set
open scoped ContDiff ENNReal Manifold Topology

namespace DifferentialGeometry.Geometry.Riemannian.NormalCoordinates

open Exponential

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem nonempty_embedding_fiber_framedExpMap
    (g : SmoothRiemannianMetric I M) {p q : M} {R r s : ℝ}
    (hqs : riemannianEDistOf g p q < ENNReal.ofReal s)
    (hfit : r + s < R)
    (hdom : ∀ z ∈ Metric.ball (0 : E) R,
      normalFrame g p z ∈ expDomain g p)
    (hloc : IsLocalDiffeomorphOn 𝓘(ℝ, E) I ∞
      (framedExpMap g p) (Metric.ball (0 : E) R)) :
    Nonempty
      ({u : E | u ∈ Metric.ball (0 : E) r ∧ framedExpMap g p u = p} ↪
        {u : E | u ∈ Metric.ball (0 : E) (r + s) ∧ framedExpMap g p u = q}) := by
  classical
  by_cases hr : 0 < r
  swap
  · have hempty : IsEmpty
        {u : E | u ∈ Metric.ball (0 : E) r ∧ framedExpMap g p u = p} :=
      ⟨fun u => (not_lt.mpr (le_of_not_gt hr))
        ((norm_nonneg (u : E)).trans_lt (by
          simpa only [Metric.mem_ball, dist_zero_right] using u.2.1))⟩
    exact ⟨Function.Embedding.ofIsEmpty⟩
  let : RiemannianBundle (TangentSpace I : M → Type _) :=
    ⟨g.toRiemannianMetric⟩
  let hEnorm : IsMetricNorm (I := I) g :=
    fun x v => tensor0SBundle_enorm_eq_riemannianBundle_enorm g x v
  have hs : 0 < s := ENNReal.ofReal_pos.mp (zero_le.trans_lt hqs)
  obtain ⟨c, hcFlat, hcLen⟩ :=
    Manifold.exists_path_isContMDiffWithSittingInstants_of_riemannianEDist_lt (I := I) hqs
  have hR : 0 < R := (add_pos hr hs).trans hfit
  have hrR : r < R := by linarith
  let F : E → M := framedExpMap g p
  let U : Set E := Metric.ball (0 : E) R
  let S : Set E := {u | u ∈ Metric.ball (0 : E) r ∧ F u = p}
  have huNorm (u : S) : ‖(u : E)‖ < r := by
    simpa only [Metric.mem_ball, dist_zero_right] using u.2.1
  have huU (u : S) : (u : E) ∈ U :=
    Metric.ball_subset_ball hrR.le u.2.1
  let radial (u : S) : Path p (F u) :=
    (radialPath g p (normalFrame g p u) (hdom u (huU u))).withSittingInstants
  let loop (u : S) : Path p p := (radial u).cast rfl u.2.2.symm
  let path (u : S) : Path p q := (loop u).trans c
  have hradialFlat (u : S) :
      Path.IsContMDiffWithSittingInstants (I := I) 1 (radial u) :=
    Path.isContMDiffWithSittingInstants_withSittingInstants
      (radialPath g p (normalFrame g p u) (hdom u (huU u)))
        ((contMDiffOn_extend_radialPath g p _ _).of_le (by norm_num))
  have hloopFlat (u : S) :
      Path.IsContMDiffWithSittingInstants (I := I) 1 (loop u) := by
    refine ⟨?_, ?_, ?_⟩
    · simpa only [loop, Path.extend_cast] using (hradialFlat u).contMDiff
    · simpa only [loop, Path.extend_cast] using (hradialFlat u).eventuallyEq_zero
    · simpa only [loop, Path.extend_cast, u.2.2] using
        (hradialFlat u).eventuallyEq_one
  have hloopLen (u : S) :
      Path.riemannianELength (I := I) (loop u) = ENNReal.ofReal ‖(u : E)‖ := by
    have hflatLen := Path.riemannianELength_withSittingInstants (I := I)
      (radialPath g p (normalFrame g p u) (hdom u (huU u)))
      ((contMDiffOn_extend_radialPath g p _ _).mdifferentiableOn (by simp))
    have hlen := hflatLen.trans
      (riemannianELength_radialPath g hEnorm p (normalFrame g p u) (hdom u (huU u)))
    rw [normalFrame_inner, real_inner_self_eq_norm_sq,
      Real.sqrt_sq (norm_nonneg (u : E))] at hlen
    exact hlen
  have hpathFlat (u : S) :
      Path.IsContMDiffWithSittingInstants (I := I) 1 (path u) :=
    (hloopFlat u).trans hcFlat
  have hpathSmall (u : S) :
      Path.riemannianELength (I := I) (path u) < ENNReal.ofReal (r + s) := by
    dsimp only [path]
    rw [Path.riemannianELength_trans
      ((hloopFlat u).contMDiff.contMDiffOn.mdifferentiableOn one_ne_zero)
      (hcFlat.contMDiff.contMDiffOn.mdifferentiableOn one_ne_zero), hloopLen u]
    exact (ENNReal.add_lt_add
      ((ENNReal.ofReal_lt_ofReal_iff hr).2 (huNorm u)) hcLen).trans_eq
        (ENNReal.ofReal_add hr.le hs.le).symm
  have hex (u : S) :
      ∃ η : ℝ → E, isLiftOn F (path u).extend U 0 0 1 η := by
    apply exists_isLiftOn_framedExpMap g hEnorm p zero_le_one
      (hpathFlat u).contMDiff.contMDiffOn (Path.extend_zero _)
    · exact (hpathSmall u).trans ((ENNReal.ofReal_lt_ofReal_iff hR).2 hfit)
    · exact hdom
    · exact hloc
  let lift (u : S) : ℝ → E := Classical.choose (hex u)
  have hlift (u : S) : isLiftOn F (path u).extend U 0 0 1 (lift u) :=
    Classical.choose_spec (hex u)
  have hliftNorm (u : S) : ‖lift u 1‖ < r + s := by
    have hcd := (hlift u).contDiffOn hloc (hpathFlat u).contMDiff.contMDiffOn
    have hrad := norm_le_pathELength_framedExpMap g hEnorm p zero_le_one
      (hlift u).2.1 hcd (fun t ht => hdom (lift u t) ((hlift u).mapsTo ht))
    have hlen : Manifold.pathELength I (F ∘ lift u) 0 1 =
        Path.riemannianELength (I := I) (path u) :=
      Manifold.pathELength_congr (fun t ht => (hlift u).2.2 t ht |>.2)
    exact (ENNReal.ofReal_lt_ofReal_iff (add_pos hr hs)).mp
      ((hrad.trans_eq hlen).trans_lt (hpathSmall u))
  let f : S → {u : E | u ∈ Metric.ball (0 : E) (r + s) ∧ F u = q} :=
    fun u => ⟨lift u 1, by
      constructor
      · simpa only [Metric.mem_ball, dist_zero_right] using hliftNorm u
      · simpa only [Path.extend_one] using
          ((hlift u).2.2 1 ⟨zero_le_one, le_rfl⟩).2⟩
  refine ⟨⟨f, ?_⟩⟩
  intro u v huv
  apply Subtype.ext
  let ray (w : S) : ℝ → E :=
    fun t => Real.smoothTransition (3 * t - 1) • (w : E)
  have hrayOne (w : S) : ray w 1 = (w : E) := by
    simp only [ray, show 3 * (1 : ℝ) - 1 = 2 by norm_num,
      Real.smoothTransition.one_of_one_le (by norm_num : (1 : ℝ) ≤ 2), one_smul]
  have hrayLift (w : S) : isLiftOn F (loop w).extend U 0 0 1 (ray w) := by
    refine ⟨?_, ?_, ?_⟩
    · exact ((Real.smoothTransition.continuous.comp
        ((continuous_const.mul continuous_id).sub continuous_const)).smul
          continuous_const).continuousOn
    · simp only [ray, mul_zero, zero_sub,
        Real.smoothTransition.zero_of_nonpos (by norm_num : -(1 : ℝ) ≤ 0), zero_smul]
    · intro t _
      constructor
      · change ray w t ∈ Metric.ball (0 : E) R
        rw [Metric.mem_ball, dist_zero_right]
        have ht : |Real.smoothTransition (3 * t - 1)| ≤ 1 := by
          rw [abs_of_nonneg (Real.smoothTransition.nonneg _)]
          exact Real.smoothTransition.le_one _
        have hnorm : ‖ray w t‖ ≤ ‖(w : E)‖ := by
          simpa only [ray, norm_smul, Real.norm_eq_abs, one_mul] using
            mul_le_mul_of_nonneg_right ht (norm_nonneg (w : E))
        exact hnorm.trans_lt ((huNorm w).trans hrR)
      · have heq : (loop w).extend = (radial w).extend :=
          Path.extend_cast (radial w) rfl w.2.2.symm
        rw [heq]
        change F (ray w t) =
          (radialPath g p (normalFrame g p w) (hdom w (huU w))).withSittingInstants.extend t
        rw [extend_radialPath_withSittingInstants]
        simp only [F, framedExpMap_apply, ray, map_smul]
  have hend : lift u 1 = lift v 1 := congrArg Subtype.val huv
  have hray := isLiftOn.end_eq_of_append Metric.isOpen_ball hloc
    (hrayLift u) (hrayLift v) (hlift u) (hlift v) hend
  exact (hrayOne u).symm.trans (hray.trans (hrayOne v))

theorem encard_fiber_framedExpMap_le
    (g : SmoothRiemannianMetric I M) {p q : M} {R r s : ℝ}
    (hqs : riemannianEDistOf g p q < ENNReal.ofReal s)
    (hfit : r + s < R)
    (hdom : ∀ z ∈ Metric.ball (0 : E) R,
      normalFrame g p z ∈ expDomain g p)
    (hloc : IsLocalDiffeomorphOn 𝓘(ℝ, E) I ∞
      (framedExpMap g p) (Metric.ball (0 : E) R)) :
    {u : E | u ∈ Metric.ball (0 : E) r ∧ framedExpMap g p u = p}.encard ≤
      {u : E | u ∈ Metric.ball (0 : E) (r + s) ∧ framedExpMap g p u = q}.encard := by
  obtain ⟨f⟩ := nonempty_embedding_fiber_framedExpMap g hqs hfit hdom hloc
  exact f.encard_le

end DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
