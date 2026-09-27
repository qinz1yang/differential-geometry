import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Projection
import DifferentialGeometry.Topology.Compactness.TimeInterval
import Mathlib.Algebra.Field.Periodic
import DifferentialGeometry.Analysis.Calculus.TimeJet.SpatialDerivatives

noncomputable section

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_forall_isRampOn_Icc_of_continuousOn_deriv
    {P : Type*} [TopologicalSpace P] [CompactSpace P]
    (c : P → ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M)
    {lambda a T : ℝ} (hlambda : 0 < lambda) (haT : a < T)
    (hramp : ∀ p, (c p).IsRampOn g lambda {a})
    (hdy : ContinuousOn
      (fun q : (P × ℝ) × ℝ => deriv (fun z => (c q.1.1).y z q.2) q.1.2)
      ((univ ×ˢ Icc (0 : ℝ) 1) ×ˢ Icc a T)) :
    ∃ δ > 0, δ ≤ T - a ∧ ∀ p, (c p).IsRampOn g lambda (Icc a (a + δ)) := by
  have hpos : ∀ p x, 0 < deriv (fun z => (c p).y z a) x := by
    intro p x
    have hangle := (hramp p).2 x a (mem_singleton a)
    rw [(c p).angle_eq g lambda] at hangle
    have hsp := (c p).speed_pos_of_immersedOn g lambda hlambda
      (hramp p).1 x a (mem_singleton a)
    exact (mul_pos_iff_of_pos_left (mul_pos hlambda (inv_pos.mpr hsp))).mp hangle
  have hK : IsCompact ((univ : Set P) ×ˢ Icc (0 : ℝ) 1) :=
    isCompact_univ.prod isCompact_Icc
  obtain ⟨δ, hδ, hδT, hpositive⟩ :=
    hK.exists_Icc_mapsTo_of_continuousOn haT isOpen_Ioi hdy
      (fun q _ => hpos q.1 q.2)
  have hpositive_all : ∀ p x t, t ∈ Icc a (a + δ) →
      0 < deriv (fun z => (c p).y z t) x := by
    intro p x t ht
    have hper : Function.Periodic (deriv (fun z => (c p).y z t)) 1 :=
      (c p).deriv_y_add_period t
    obtain ⟨y, hy, hxy⟩ := hper.exists_mem_Ioc (by norm_num : (0 : ℝ) < 1) x 0
    rw [hxy]
    exact hpositive (p, y) ⟨mem_univ p, hy.1.le, by simpa using hy.2⟩ t ht
  have himm : ∀ p, (c p).ImmersedOn (I := I) (Icc a (a + δ)) := by
    intro p x t ht hzero
    have hdyzero : deriv (fun z => (c p).y z t) x = 0 := congrArg Prod.snd hzero
    exact (hpositive_all p x t ht).ne' hdyzero
  refine ⟨δ, hδ, hδT, fun p => ⟨himm p, ?_⟩⟩
  intro x t ht
  rw [(c p).angle_eq g lambda]
  exact mul_pos (mul_pos hlambda
    (inv_pos.mpr ((c p).speed_pos_of_immersedOn g lambda hlambda (himm p) x t ht)))
    (hpositive_all p x t ht)

theorem exists_isRampOn_Icc_of_smoothOn
    (c : ProductCurve M) (g : ℝ → SmoothRiemannianMetric I M)
    {lambda a T : ℝ} (hlambda : 0 < lambda) (haT : a < T)
    (hc : c.SmoothOn (I := I) (Icc a T)) (hramp : c.IsRampOn g lambda {a}) :
    ∃ δ > 0, a + δ ≤ T ∧ c.IsRampOn g lambda (Icc a (a + δ)) := by
  have hdy : ContinuousOn (fun q : ℝ × ℝ => deriv (fun z => c.y z q.2) q.1)
      (univ ×ˢ Icc a T) :=
    (DifferentialGeometry.Analysis.contDiffOn_deriv_fst isOpen_univ
      (uniqueDiffOn_Icc haT) hc.2).continuousOn
  have hfamily : ContinuousOn
      (fun q : (Unit × ℝ) × ℝ => deriv (fun z => c.y z q.2) q.1.2)
      ((univ ×ˢ Icc (0 : ℝ) 1) ×ˢ Icc a T) :=
    hdy.comp ((continuous_snd.comp continuous_fst).prodMk continuous_snd).continuousOn
      (fun q hq => ⟨mem_univ q.1.2, hq.2⟩)
  obtain ⟨δ, hδ, hδT, hpositive⟩ := exists_forall_isRampOn_Icc_of_continuousOn_deriv
    (fun _ : Unit => c) g hlambda haT (fun _ => hramp) hfamily
  exact ⟨δ, hδ, by linarith, hpositive ()⟩

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening.ProductCurve
