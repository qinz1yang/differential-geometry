import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakEvolution
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1IntegrationByParts

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal InnerProductSpace Manifold NNReal
  RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n

theorem IsWeakEvolutionSolution.integral_timeH1_test
    {q : SmoothRiemannianMetric I_hs M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric}
    {T : ℝ} {hT : 0 ≤ T} {hreg : Icc (0 : ℝ) T ⊆ D.regular}
    {X : ℝ → Cₛ^∞⟮I_hs; EuclideanSpace ℝ (Fin n),
      (TangentSpace I_hs : M → Type _)⟯}
    (hXcont : ContinuousOn
      (fun p : ℝ × M ↦
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle I_hs M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    {a : ℝ → ℝ} (hacont : ContinuousOn a (Icc (0 : ℝ) T))
    {Bx Bv : ℝ}
    {hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    {f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_hs) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv
      hX htrace f₀ u) :
    ∃ Cg : ℝ, ∃ Cv : ℝ≥0∞,
      ∃ hCg : 1 ≤ Cg,
      ∃ hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        ∀ v : TangentSpace I_hs x,
          Cg⁻¹ * q.inner x v v ≤ (G.metric t).inner x v v ∧
            (G.metric t).inner x v v ≤ Cg * q.inner x v v,
      ∃ hCv0 : Cv ≠ 0, ∃ hCvtop : Cv ≠ ⊤,
      ∃ hvol : ∀ t ∈ Icc (0 : ℝ) T,
        riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric t) ≤
          Cv • riemannianVolumeMeasure (I := I_hs) (M := M) q,
      ∀ v : timeH1 (H1ComplDirichlet q) T, v.toFun T = 0 →
        (∫ t, dirichletMassComplOnIcc G.metric hCg hequiv Cv hCv0 hCvtop hvol
          t (u t) (v.deriv t) ∂timeMeasure T) +
        (∫ t, dirichletMassVariationComplOnIco hG hreg Bv htrace
            hCg hequiv Cv hCv0 hCvtop hvol t (u t) (v.toFun t) +
          dirichletWeakFormComplOnIco G.metric X a Bx hX
            hCg hequiv Cv hCv0 hCvtop hvol t (u t) (v.toFun t) ∂timeMeasure T) =
        -dirichletMassLp (G.metric 0) Cv hCvtop (hvol 0 ⟨le_rfl, hT⟩)
          f₀ (H1ComplDirichletToLp q v.init) := by
  obtain ⟨Cg, Cv, hCg, hequiv, hCv0, hCvtop, hvol, w, hwi, hwm, hwd⟩ :=
    hu.exists_mass_timeH1 hXcont hacont
  refine ⟨Cg, Cv, hCg, hequiv, hCv0, hCvtop, hvol, ?_⟩
  intro v hv
  have h := w.integration_by_parts_integral v hT
  rw [hv, inner_zero_right, zero_sub, w.toFun_zero, v.toFun_zero, hwi,
    InnerProductSpace.toDual_symm_apply] at h
  simp only [ContinuousLinearMap.comp_apply] at h
  rw [h]
  apply congrArg₂ (fun a b : ℝ => a + b)
  · apply integral_congr_ae
    filter_upwards [hwm] with t ht
    rw [← ht]
    exact InnerProductSpace.toDual_symm_apply.symm
  · apply integral_congr_ae
    filter_upwards [hwd] with t ht
    rw [ht, real_inner_comm, InnerProductSpace.toDual_symm_apply]
    rfl

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
