import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureNullity
import DifferentialGeometry.Geometry.Flow.RicciFlow.DimensionThree.CurvatureKernel
import DifferentialGeometry.Geometry.Flow.RicciFlow.ParallelLineSplitting
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ImageLineFamily
import DifferentialGeometry.Geometry.Curvature.LocalProduct
import DifferentialGeometry.Geometry.Curvature.DimensionThree.ScalarPositivity
import DifferentialGeometry.Geometry.Curvature.DimensionTwo.SectionalCurvature
import DifferentialGeometry.Geometry.Flow.RicciFlow.Solution.JointRegularity
import DifferentialGeometry.Geometry.Metric.Family.PairSmoothness
import DifferentialGeometry.Geometry.Metric.Family.JointSmoothness

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set TopologicalSpace
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem exists_positive_surface_local_product_on_interval
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    {α β t₀ : ℝ} (ht₀ : t₀ ∈ Ioo α β) (hreg : Ioo α β ⊆ D.regular)
    (hR : ∀ t ∈ Ioo α β, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hrank : ∀ t ∈ Ioo α β, ∀ x,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) = 1)
    (x : M) :
    ∃ (e : TangentSpace I x) (K : TopologicalSpace.Opens (perpSpace (S.family.metric t₀) x e))
      (O : TopologicalSpace.Opens ℝ)
      (phi : PartialDiffeomorph ((perpModel (S.family.metric t₀) x e).prod 𝓘(ℝ, ℝ)) I
        (perpSpace (S.family.metric t₀) x e × ℝ) M ∞)
      (hPhi : IsLocalDiffeomorph ((perpModel (S.family.metric t₀) x e).prod 𝓘(ℝ, ℝ)) I ∞
        (fun y : K × O => phi (y.1.1, y.2.1)))
      (h : ℝ → SmoothRiemannianMetric (perpModel (S.family.metric t₀) x e) K),
      (0 : perpSpace (S.family.metric t₀) x e) ∈ K ∧ (0 : ℝ) ∈ O ∧
      IsPreconnected (O : Set ℝ) ∧ phi.source = (K : Set _) ×ˢ (O : Set ℝ) ∧
      phi (0, 0) = x ∧
      (S.family.metric t₀).inner x e e = 1 ∧
      Module.finrank ℝ (perpSpace (S.family.metric t₀) x e) = 2 ∧
      (∀ a ∈ Ioo α β, localPullMetric (S.family.metric a) (fun y : K × O => phi (y.1.1, y.2.1)) hPhi =
        (h a).prod ((euclideanMetric (E := ℝ)).restrictOpen O)) ∧
      (∀ a ∈ Ioo α β, ∀ (k : K) (u v : TangentSpace (perpModel (S.family.metric t₀) x e) k),
        (h a).inner k u v = (S.family.metric a).inner (phi (k.1, 0))
          (mfderiv (perpModel (S.family.metric t₀) x e) I
            (fun y : perpSpace (S.family.metric t₀) x e => phi (y, 0)) k.1 u)
          (mfderiv (perpModel (S.family.metric t₀) x e) I
            (fun y : perpSpace (S.family.metric t₀) x e => phi (y, 0)) k.1 v)) ∧
      (∀ a ∈ Ioo α β, ∀ (k : K) (u v : TangentSpace (perpModel (S.family.metric t₀) x e) k),
        HasDerivWithinAt (fun b => (h b).inner k u v)
          (-2 * ricciTensor (h a) k u v) (Ioo α β) a) ∧
      IsSolutionOn ({ base := { metric := h } } :
        SolutionOn (I := perpModel (S.family.metric t₀) x e) (M := K)
          (RealTimeInterval.openInterval α β t₀ ht₀)) ∧
      (∀ a ∈ Ioo α β, ∀ k : K, 0 < metricScalarAt (h a) k) ∧
      ∀ a ∈ Ioo α β, ∀ (k : K) (u v : TangentSpace (perpModel (S.family.metric t₀) x e) k),
        LinearIndependent ℝ ![u, v] → 0 < Geometry.Riemannian.sectionalCurvature (h a) k u v := by
  have hkernel r (hr : r ∈ Ioo α β) :
      IsParallelContinuousAlternatingSubmoduleFamily (S.family.metric r)
        (fun y => curvatureOperatorKernelAt (S.family.metric r) y
          ⟨metricRm04At (S.family.metric r) y,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) y⟩) := by
    exact curvatureOperatorKernelAt_parallel_of_constant_rank S hS hdim hr hreg hR 1 hrank
  obtain ⟨U, s, hU, hxU, hmem, hunit, hparallel, hdual⟩ :=
    exists_common_parallel_unit_section_of_curvatureOperatorImageAnnihilator_eq
      (fun r : Ioo α β => S.family.metric r.1) ⟨t₀, ht₀⟩ hdim
      (fun r => hrank r.1 r.2) (fun r => hkernel r.1 r.2)
      (fun r y => (curvatureOperatorImageAnnihilatorAt_eq_and_inner_eq_of_constant_rank
        S hS hdim r.2 ht₀ hreg hR 1 hrank y).1)
      (fun r y v hv w => (curvatureOperatorImageAnnihilatorAt_eq_and_inner_eq_of_constant_rank
        S hS hdim ht₀ r.2 hreg hR 1 hrank y).2 v hv w |>.symm) x
  obtain ⟨K, O, phi, hPhi, h, hK₀, hO₀, hOconn, hsource, hbase, htarget,
      hprod, hinner, hevol, -⟩ := exists_local_product_from_common_parallel_unit_section
    S hS (Ioo α β) t₀ ht₀ hreg x hU hxU s (hunit ⟨t₀, ht₀⟩)
      (fun r hr => hparallel ⟨r, hr⟩) (fun r hr => hdual ⟨r, hr⟩)
  let _ : (perpModel (S.family.metric t₀) x (s x)).Boundaryless := by
    constructor
    ext y
    simp only [Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨y, rfl⟩
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : CompleteSpace (perpSpace (S.family.metric t₀) x (s x)) :=
    FiniteDimensional.complete ℝ (perpSpace (S.family.metric t₀) x (s x))
  let _ : SigmaCompactSpace K := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen (perpModel (S.family.metric t₀) x (s x)) K.isOpen)
  let _ : SigmaCompactSpace O := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen 𝓘(ℝ, ℝ) O.isOpen)
  have hdimP : Module.finrank ℝ (perpSpace (S.family.metric t₀) x (s x)) = 2 := by
    rw [finrank_perpSpace _ _ _ (by
      intro hz
      have hu := hunit ⟨t₀, ht₀⟩ x hxU
      rw [hz, map_zero] at hu
      norm_num at hu), hdim]
  have hpos r (hr : r ∈ Ioo α β) (k : K) : 0 < metricScalarAt (h r) k := by
    have hn := metricScalarAt_localPull (S.family.metric r)
      (fun y : K × O => phi (y.1.1, y.2.1)) hPhi (k, ⟨0, hO₀⟩)
    rw [hprod r hr, metricScalarAt_prod,
      metricScalarAt_eq_zero_of_finrank_le_one ((euclideanMetric (E := ℝ)).restrictOpen O)
        (by simp : Module.finrank ℝ ℝ ≤ 1), add_zero] at hn
    rw [hn]
    exact DimensionThree.metricScalarAt_pos_of_mem_nonnegativeCone_of_curvatureOperator_rank_one
      hdim (S.family.metric r) _ (hR r hr _) (hrank r hr _)
  let Y : K → M := fun k => phi (k.1, 0)
  have hY : ContMDiff (perpModel (S.family.metric t₀) x (s x)) I ∞ Y :=
    hPhi.contMDiff.comp (contMDiff_id.prodMk (contMDiff_const (c := (⟨0, hO₀⟩ : O))))
  have hYder (k : K) : mfderiv (perpModel (S.family.metric t₀) x (s x)) I Y k =
      mfderiv (perpModel (S.family.metric t₀) x (s x)) I
        (fun y : perpSpace (S.family.metric t₀) x (s x) => phi (y, 0)) k.1 := by
    have hraw : MDifferentiableAt (perpModel (S.family.metric t₀) x (s x)) I
        (fun y : perpSpace (S.family.metric t₀) x (s x) => phi (y, 0)) k.1 :=
      (phi.mdifferentiableAt (by decide : (∞ : WithTop ℕ∞) ≠ 0)
        (by rw [hsource]; exact ⟨k.2, hO₀⟩)).comp k.1
        (mdifferentiableAt_id.prodMk mdifferentiableAt_const)
    have hh := mfderiv_comp k hraw
      ((contMDiff_subtype_val (I := perpModel (S.family.metric t₀) x (s x)) (U := K)).contMDiffAt.mdifferentiableAt
        (by decide : (∞ : WithTop ℕ∞) ≠ 0))
    rw [mfderiv_subtype_val] at hh
    exact hh
  have hmetric : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (S.family.metric p.1).inner p.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun y => TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)))
      (Ioo α β ×ˢ (Set.univ : Set M)) := by
    intro p hp
    exact (hS.smoothMetric.metricCLMSmoothAt
      (D.regular_isOpen.mem_nhds (hreg hp.1))).contMDiffWithinAt
  have hgram := chartGramMatrix_joint_contMDiffOn_of_pullback
    S.family.metric (Ioo α β) hmetric h Y hY (by
      intro t ht k u v
      rw [hYder]
      exact hinner t ht k u v)
  have hjoint := metricCLMSection_jointContMDiffOn_of_chartGram_Ioo h α β hgram
  have hsol : IsSolutionOn ({ base := { metric := h } } :
      SolutionOn (I := perpModel (S.family.metric t₀) x (s x)) (M := K)
        (RealTimeInterval.openInterval α β t₀ ht₀)) :=
    isSolutionOn_of_joint_metric (RealTimeInterval.openInterval α β t₀ ht₀)
      isOpen_Ioo.uniqueDiffOn h hjoint hevol
  refine ⟨s x, K, O, phi, hPhi, h, hK₀, hO₀, hOconn, hsource, hbase,
    hunit ⟨t₀, ht₀⟩ x hxU, hdimP, hprod, hinner, hevol, hsol, hpos, ?_⟩
  intro r hr k u v huv
  exact Geometry.Riemannian.sectionalCurvature_pos_of_metricScalarAt_pos_of_finrank_eq_two
    (h r) hdimP k (hpos r hr k) u v huv

end DifferentialGeometry.PDE.RicciFlow
