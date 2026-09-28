import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakFormIntegration
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.SmoothTimeTest
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeH1IntegrationByParts
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.Steklov

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal InnerProductSpace Manifold NNReal
  RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator.WithBoundary
open DifferentialGeometry.Integral.DivergenceTheorem
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
          f₀ (H1ComplDirichletToLp q v.initial) := by
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

theorem IsWeakEvolutionSolution.integral_timeH1_test_eq_integral
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
      hX htrace f₀ u)
    (w : timeH1 (H1ComplDirichlet q) T) (v : ℝ → SmoothScalarDirichlet q)
    (v' : ℝ → M → ℝ)
    (hwv : ∀ᵐ t ∂timeMeasure T,
      H1ComplDirichletToLp q (w.toFun t) =ᵐ[
        riemannianVolumeMeasure (I := I_hs) (M := M) q] (v t).toFun)
    (hwd : ∀ᵐ t ∂timeMeasure T,
      H1ComplDirichletToLp q (w.deriv t) =ᵐ[
        riemannianVolumeMeasure (I := I_hs) (M := M) q] v' t)
    (hwi : H1ComplDirichletToLp q w.initial =ᵐ[
      riemannianVolumeMeasure (I := I_hs) (M := M) q] (v 0).toFun)
    (hwT : w.toFun T = 0) :
    (∫ t, ∫ x, H1ComplDirichletToLp q (u t) x * v' t x
      ∂(riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric t)) ∂timeMeasure T) +
    (∫ t, (∫ x, (1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric t x *
        (H1ComplDirichletToLp q (u t) x * (v t).toFun x)
        ∂(riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric t))) +
      ∫ x, H1ComplDirichletToLp q (u t) x *
        (ΔGWithBoundary (I := I_hs) (G.metric t) (v t).smooth (v t).interior_support x -
          tangentSectionAction (I := I_hs) (X t) (v t).toFun x -
          divergence (I := I_hs) (leviCivitaConnectionOfMetric (I := I_hs) (G.metric t))
            (X t) x * (v t).toFun x - a t * (v t).toFun x)
        ∂(riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric t)) ∂timeMeasure T) =
      -(∫ x, f₀ x * (v 0).toFun x
        ∂(riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric 0))) := by
  obtain ⟨Cg, Cv, hCg, hequiv, hCv0, hCvtop, hvol, htest⟩ :=
    hu.integral_timeH1_test hXcont hacont
  have hac (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric t) ≪
        riemannianVolumeMeasure (I := I_hs) (M := M) q :=
    Measure.absolutelyContinuous_of_le_smul (hvol t ht)
  have hv : ∀ᵐ t ∂timeMeasure T,
      w.toFun t = smoothToH1ComplDirichlet q (v t) := by
    filter_upwards [hwv] with t ht
    apply H1ComplDirichletToLp_injective q
    apply Lp.ext
    exact ht.trans (by
      rw [H1ComplDirichletToLp_smoothToH1ComplDirichlet]
      exact (MemLp.coeFn_toLp (v t).memLp_two).symm)
  have hmem : ∀ᵐ t ∂timeMeasure T, t ∈ Ico (0 : ℝ) T := by
    unfold timeMeasure
    rw [← restrict_Ico_eq_restrict_Icc]
    exact ae_restrict_mem measurableSet_Ico
  have hfirst :
      (∫ t, dirichletMassComplOnIcc G.metric hCg hequiv Cv hCv0 hCvtop hvol
        t (u t) (w.deriv t) ∂timeMeasure T) =
      ∫ t, ∫ x, H1ComplDirichletToLp q (u t) x * v' t x
        ∂(riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric t)) ∂timeMeasure T := by
    apply integral_congr_ae
    filter_upwards [hwd, hmem] with t ht htm
    have htc : t ∈ Icc (0 : ℝ) T := ⟨htm.1, htm.2.le⟩
    rw [dirichletMassComplOnIcc, dite_eq_left htc, dirichletMassCompl_apply_eq_integral]
    apply integral_congr_ae
    filter_upwards [(hac t htc).ae_eq ht] with x hx
    rw [hx]
  have hsecond :
      (∫ t, dirichletMassVariationComplOnIco hG hreg Bv htrace
          hCg hequiv Cv hCv0 hCvtop hvol t (u t) (w.toFun t) +
        dirichletWeakFormComplOnIco G.metric X a Bx hX
          hCg hequiv Cv hCv0 hCvtop hvol t (u t) (w.toFun t) ∂timeMeasure T) =
      (∫ t, (∫ x, (1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric t x *
          (H1ComplDirichletToLp q (u t) x * (v t).toFun x)
          ∂(riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric t))) +
        ∫ x, H1ComplDirichletToLp q (u t) x *
          (ΔGWithBoundary (I := I_hs) (G.metric t) (v t).smooth (v t).interior_support x -
            tangentSectionAction (I := I_hs) (X t) (v t).toFun x -
            divergence (I := I_hs) (leviCivitaConnectionOfMetric (I := I_hs) (G.metric t))
              (X t) x * (v t).toFun x - a t * (v t).toFun x)
          ∂(riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric t)) ∂timeMeasure T) := by
    apply integral_congr_ae
    filter_upwards [hv, hmem] with t ht htm
    rw [ht, dirichletMassVariationComplOnIco, dite_eq_left htm,
      dirichletWeakFormComplOnIco, dite_eq_left htm,
      dirichletMassVariationCompl_apply_eq_integral,
      dirichletWeakFormCompl_apply_eq_integral_adjoint]
  have hin : dirichletMassLp (G.metric 0) Cv hCvtop (hvol 0 ⟨le_rfl, hT⟩)
      f₀ (H1ComplDirichletToLp q w.initial) =
      ∫ x, f₀ x * (v 0).toFun x
        ∂(riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric 0)) := by
    rw [dirichletMassLp_apply_eq_integral]
    apply integral_congr_ae
    filter_upwards [(hac 0 ⟨le_rfl, hT⟩).ae_eq hwi] with x hx
    rw [hx]
  simpa only [hfirst, hsecond, hin] using htest w hwT

theorem IsWeakEvolutionSolution.integral_smooth_time_test
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
      hX htrace f₀ u)
    (v v' : ℝ → SmoothScalarDirichlet q)
    {J : Set ℝ} (hJ : IsOpen J)
    (hv : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (v p.1).toFun p.2) (J ×ˢ univ))
    (hv' : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × M => (v' p.1).toFun p.2) (J ×ˢ univ))
    (hd : ∀ t ∈ J, ∀ x, HasDerivAt (fun s => (v s).toFun x) ((v' t).toFun x) t)
    {K : Set M} (hK : IsClosed K) (hKi : K ⊆ (I_hs).interior M)
    (hv'K : ∀ t ∈ J, tsupport (v' t).toFun ⊆ K)
    (hTJ : Icc (0 : ℝ) T ⊆ J) (hvT : v T = 0) :
    (∫ t, ∫ x, H1ComplDirichletToLp q (u t) x * (v' t).toFun x
      ∂(riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric t)) ∂timeMeasure T) +
    (∫ t, (∫ x, (1 / 2 : ℝ) * traceTimeDerivMetric (I := I_hs) G.metric t x *
        (H1ComplDirichletToLp q (u t) x * (v t).toFun x)
        ∂(riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric t))) +
      ∫ x, H1ComplDirichletToLp q (u t) x *
        (ΔGWithBoundary (I := I_hs) (G.metric t) (v t).smooth (v t).interior_support x -
          tangentSectionAction (I := I_hs) (X t) (v t).toFun x -
          divergence (I := I_hs) (leviCivitaConnectionOfMetric (I := I_hs) (G.metric t))
            (X t) x * (v t).toFun x - a t * (v t).toFun x)
        ∂(riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric t)) ∂timeMeasure T) =
      -(∫ x, f₀ x * (v 0).toFun x
        ∂(riemannianVolumeMeasure (I := I_hs) (M := M) (G.metric 0))) := by
  obtain ⟨w, hwv, hwd, hwi, hwT⟩ :=
    exists_timeH1_smoothToH1ComplDirichlet q v v' hJ hv hv' hd hK hKi hv'K hT hTJ hvT
  apply hu.integral_timeH1_test_eq_integral hXcont hacont w v (fun t => (v' t).toFun)
    (hwT := hwT)
  · filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
    rw [hwv ht, H1ComplDirichletToLp_smoothToH1ComplDirichlet]
    exact MemLp.coeFn_toLp (v t).memLp_two
  · filter_upwards [hwd] with t ht
    rw [ht, H1ComplDirichletToLp_smoothToH1ComplDirichlet]
    exact MemLp.coeFn_toLp (v' t).memLp_two
  · rw [hwi, H1ComplDirichletToLp_smoothToH1ComplDirichlet]
    exact MemLp.coeFn_toLp (v 0).memLp_two

theorem IsWeakEvolutionSolution.integral_steklovAverage_test
    {q : SmoothRiemannianMetric I_hs M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_hs) (M := M) D}
    {hG : MetricFamilySmoothOn (I := I_hs) (M := M) D G.metric}
    {T : ℝ} {hT : 0 ≤ T} {hreg : Icc (0 : ℝ) T ⊆ D.regular}
    {X : ℝ → Cₛ^∞⟮I_hs; EuclideanSpace ℝ (Fin n),
      (TangentSpace I_hs : M → Type _)⟯}
    (hXcont : ContinuousOn
      (fun p : ℝ × M =>
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle I_hs M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    {a : ℝ → ℝ} (hacont : ContinuousOn a (Icc (0 : ℝ) T))
    {Bx Bv : ℝ}
    {hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    {f₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I_hs) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv hX htrace f₀ u)
    (v : timeL2 (H1ComplDirichlet q) T) {h : ℝ} (hh : 0 ≤ h) :
    let V := (Icc (0 : ℝ) T).indicator (fun t => v t)
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
      (∫ t, dirichletMassComplOnIcc G.metric hCg hequiv Cv hCv0 hCvtop hvol
        t (u t) (h⁻¹ • (V (t + h) - V t)) ∂timeMeasure T) +
      (∫ t, dirichletMassVariationComplOnIco hG hreg Bv htrace
          hCg hequiv Cv hCv0 hCvtop hvol t (u t) (steklovAverage h V t) +
        dirichletWeakFormComplOnIco G.metric X a Bx hX
          hCg hequiv Cv hCv0 hCvtop hvol t (u t) (steklovAverage h V t) ∂timeMeasure T) =
      -dirichletMassLp (G.metric 0) Cv hCvtop (hvol 0 ⟨le_rfl, hT⟩)
        f₀ (H1ComplDirichletToLp q (steklovAverage h V 0)) := by
  obtain ⟨w, hw, hwd, hwT⟩ := exists_timeH1_steklovAverage_timeL2_terminal_zero hT v hh
  obtain ⟨Cg, Cv, hCg, hequiv, hCv0, hCvtop, hvol, htest⟩ :=
    hu.integral_timeH1_test hXcont hacont
  refine ⟨Cg, Cv, hCg, hequiv, hCv0, hCvtop, hvol, ?_⟩
  have hid := htest w hwT
  have hinit : w.initial = steklovAverage h ((Icc (0 : ℝ) T).indicator v) 0 :=
    w.toFun_zero.symm.trans (hw 0 ⟨le_rfl, hT⟩)
  rw [hinit] at hid
  rw [← hid]
  apply congrArg₂ (fun a b : ℝ => a + b)
  · apply integral_congr_ae
    filter_upwards [hwd] with t ht
    rw [ht]
  · apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [hw t ht]

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
