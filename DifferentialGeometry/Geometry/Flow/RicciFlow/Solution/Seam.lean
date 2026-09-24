import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.Seam
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Metric.ClosedIntervalDerivative
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.JointRegularity

noncomputable section

open Bundle Filter Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
private local instance : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)

private theorem metric_inner_hasDerivWithinAt_of_joint_ricciFlow
    (g : ℝ → SmoothRiemannianMetric I M) {a b t : ℝ} (hab : a < b)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => (⟨q.2, (g q.1).inner q.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Icc a b ×ˢ (univ : Set M)))
    (hpde : ∀ s ∈ Ioo a b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivAt (fun u => (g u).inner x v w) (-2 * ricciTensor (I := I) (g s) x v w) s)
    (ht : t ∈ Icc a b) (x : M) (v w : TangentSpace I x) :
    HasDerivWithinAt (fun s => (g s).inner x v w)
      (-2 * ricciTensor (I := I) (g t) x v w) (Icc a b) t := by
  let S : SolutionOn (I := I) (M := M) (RealTimeInterval.closed a b hab.le) :=
    { base := { metric := g } }
  have hS : IsSolutionOn S :=
    isSolutionOn_of_joint_metric (RealTimeInterval.closed a b hab.le) (uniqueDiffOn_Icc hab)
      g hg (fun s hs x v w => (hpde s hs x v w).hasDerivWithinAt)
  have hd := metric_inner_hasDerivWithinAt_on_closed_interval S hS hab subset_rfl subset_rfl ht x v w
  simpa only [S, SolutionOn.ricciAt, SolutionFamily.ricciAt,
    metricRicciAt_apply_eq_ricciTensor] using hd

variable (gL gR : ℝ → SmoothRiemannianMetric I M) {a c b : ℝ} (ha : a < c) (hb : c < b)
    (hL : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => (⟨q.2, (gL q.1).inner q.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Icc a c ×ˢ (univ : Set M)))
    (hR : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun q : ℝ × M => (⟨q.2, (gR q.1).inner q.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Icc c b ×ˢ (univ : Set M)))
    (hpdeL : ∀ t ∈ Ioo a c, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivAt (fun s => (gL s).inner x v w) (-2 * ricciTensor (I := I) (gL t) x v w) t)
    (hpdeR : ∀ t ∈ Ioo c b, ∀ x : M, ∀ v w : TangentSpace I x,
      HasDerivAt (fun s => (gR s).inner x v w) (-2 * ricciTensor (I := I) (gR t) x v w) t)
    (hmatch : gL c = gR c)

include ha hb hL hR hpdeL hpdeR hmatch in
theorem metric_inner_hasDerivAt_ite_of_ricciFlow {t : ℝ} (ht : t ∈ Ioo a b)
    (x : M) (v w : TangentSpace I x) :
    HasDerivAt (fun s => (if s ≤ c then gL s else gR s).inner x v w)
      (-2 * ricciTensor (I := I) (if t ≤ c then gL t else gR t) x v w) t := by
  rcases lt_trichotomy t c with htc | heq | hct
  · have hd := hpdeL t ⟨ht.1, htc⟩ x v w
    rw [if_pos htc.le]
    apply hd.congr_of_eventuallyEq
    filter_upwards [Iio_mem_nhds htc] with s hs
    rw [if_pos (mem_Iio.mp hs).le]
  · subst t
    have hdL := metric_inner_hasDerivWithinAt_of_joint_ricciFlow gL ha hL hpdeL
      ⟨ha.le, le_rfl⟩ x v w
    have hdR := metric_inner_hasDerivWithinAt_of_joint_ricciFlow gR hb hR hpdeR
      ⟨le_rfl, hb.le⟩ x v w
    have heqL : EqOn (fun s => (if s ≤ c then gL s else gR s).inner x v w)
        (fun s => (gL s).inner x v w) (Icc a c) := by
      intro s hs
      dsimp only
      rw [if_pos hs.2]
    have heqR : EqOn (fun s => (if s ≤ c then gL s else gR s).inner x v w)
        (fun s => (gR s).inner x v w) (Icc c b) := by
      intro s hs
      dsimp only
      by_cases hsc : s ≤ c
      · have he : s = c := le_antisymm hsc hs.1
        subst s
        rw [if_pos le_rfl, hmatch]
      · rw [if_neg hsc]
    have hdL' := hdL.congr_of_mem heqL ⟨ha.le, le_rfl⟩
    have hdR' := hdR.congr_of_mem heqR ⟨le_rfl, hb.le⟩
    rw [← hmatch] at hdR'
    have hd := hdL'.union hdR'
    rw [Icc_union_Icc_eq_Icc ha.le hb.le] at hd
    rw [if_pos le_rfl]
    exact hd.hasDerivAt (Icc_mem_nhds ha hb)
  · have hd := hpdeR t ⟨hct, ht.2⟩ x v w
    rw [if_neg (not_le.mpr hct)]
    apply hd.congr_of_eventuallyEq
    filter_upwards [Ioi_mem_nhds hct] with s hs
    rw [if_neg (not_le.mpr (mem_Ioi.mp hs))]

include ha hb hL hR hpdeL hpdeR hmatch in
theorem isSolutionOn_ite_of_ricciFlow :
    IsSolutionOn ({ base := { metric := fun t => if t ≤ c then gL t else gR t } } :
      SolutionOn (I := I) (M := M) (RealTimeInterval.closed a b (ha.trans hb).le)) := by
  apply isSolutionOn_of_joint_metric (RealTimeInterval.closed a b (ha.trans hb).le)
    (uniqueDiffOn_Icc (ha.trans hb)) (fun t => if t ≤ c then gL t else gR t)
    (metricCLMSection_jointContMDiffOn_ite_of_ricciFlow gL gR ha hb hL hR hpdeL hpdeR hmatch)
  intro t ht x v w
  exact (metric_inner_hasDerivAt_ite_of_ricciFlow gL gR ha hb hL hR hpdeL hpdeR hmatch ht x v w).hasDerivWithinAt

end DifferentialGeometry.PDE.RicciFlow
