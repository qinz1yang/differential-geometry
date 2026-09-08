import Mathlib.Analysis.Convex.Topology
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

theorem exists_positive_surface_local_product_on_ordConnected
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    {J : Set ℝ} (hJ : J.OrdConnected) {t₀ : ℝ} (ht₀ : t₀ ∈ interior J)
    (hreg : J ⊆ D.regular)
    (hR : ∀ t ∈ J, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hrank : ∀ t ∈ J, ∀ x,
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
      (∀ a ∈ J, localPullMetric (S.family.metric a) (fun y : K × O => phi (y.1.1, y.2.1)) hPhi =
        (h a).prod ((euclideanMetric (E := ℝ)).restrictOpen O)) ∧
      (∀ a, ∀ (k : K) (u v : TangentSpace (perpModel (S.family.metric t₀) x e) k),
        (h a).inner k u v = (S.family.metric a).inner (phi (k.1, 0))
          (mfderiv (perpModel (S.family.metric t₀) x e) I
            (fun y : perpSpace (S.family.metric t₀) x e => phi (y, 0)) k.1 u)
          (mfderiv (perpModel (S.family.metric t₀) x e) I
            (fun y : perpSpace (S.family.metric t₀) x e => phi (y, 0)) k.1 v)) ∧
      (∀ a ∈ interior J, ∀ (k : K) (u v : TangentSpace (perpModel (S.family.metric t₀) x e) k),
        HasDerivWithinAt (fun b => (h b).inner k u v)
          (-2 * ricciTensor (h a) k u v) (interior J) a) ∧
      (∀ {α β a : ℝ} (ha : a ∈ Ioo α β), Ioo α β ⊆ J →
        IsSolutionOn ({ base := { metric := h } } :
          SolutionOn (I := perpModel (S.family.metric t₀) x e) (M := K)
            (RealTimeInterval.openInterval α β a ha))) ∧
      (∀ a ∈ J, ∀ k : K, 0 < metricScalarAt (h a) k) ∧
      ∀ a ∈ J, ∀ (k : K) (u v : TangentSpace (perpModel (S.family.metric t₀) x e) k),
        LinearIndependent ℝ ![u, v] → 0 < Geometry.Riemannian.sectionalCurvature (h a) k u v := by
  have hkernel r (hr : r ∈ interior J) :
      IsParallelContinuousAlternatingSubmoduleFamily (S.family.metric r)
        (fun y => curvatureOperatorKernelAt (S.family.metric r) y
          ⟨metricRm04At (S.family.metric r) y,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) y⟩) := by
    obtain ⟨α, β, hr', hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
      (mem_interior_iff_mem_nhds.mp hr)
    exact curvatureOperatorKernelAt_parallel_of_constant_rank S hS hdim hr'
      (hsub.trans hreg) (fun a ha => hR a (hsub ha)) 1 (fun a ha => hrank a (hsub ha))
  obtain ⟨U, s, hU, hxU, -, hunit, hparallel, hdual⟩ :=
    exists_common_parallel_unit_section_of_curvatureOperatorImageAnnihilator_eq
      (fun r : interior J => S.family.metric r.1) ⟨t₀, ht₀⟩ hdim
      (fun r => hrank r.1 (interior_subset r.2)) (fun r => hkernel r.1 r.2)
      (fun r y => (curvatureOperatorImageAnnihilatorAt_eq_and_inner_eq_of_rank_one_on_interval
        S hS hdim hJ hreg hR hrank (interior_subset r.2) (interior_subset ht₀) y).1)
      (fun r y v hv w => (curvatureOperatorImageAnnihilatorAt_eq_and_inner_eq_of_rank_one_on_interval
        S hS hdim hJ hreg hR hrank (interior_subset ht₀) (interior_subset r.2) y).2 v hv w |>.symm) x
  obtain ⟨K, O, phi, hPhi, h, hK₀, hO₀, hOconn, hsource, hbase, -,
      hprod, -, -, -⟩ := exists_local_product_from_common_parallel_unit_section
    S hS (interior J) t₀ ht₀ (interior_subset.trans hreg) x hU hxU s (hunit ⟨t₀, ht₀⟩)
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
  let Y : K → M := fun k => phi (k.1, 0)
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
  obtain ⟨H, hHslice, -, hHprod⟩ :=
    exists_metric_prod_eq_on_closure_of_localPullMetric S.family.metric h
      (fun _ => (euclideanMetric (E := ℝ)).restrictOpen O)
      (fun y : K × O => phi (y.1.1, y.2.1)) hPhi (⟨0, hO₀⟩ : O)
      (show J ⊆ closure (interior J) from by
        rw [(show Convex ℝ J from hJ.convex).closure_interior_eq_closure_of_nonempty_interior
          ⟨t₀, ht₀⟩]
        exact subset_closure)
      (fun a ha y u v => (metricDerivAt S hS ⟨a, hreg ha⟩ y u v).continuousAt.continuousWithinAt)
      (fun _ _ _ _ _ => continuousWithinAt_const) hprod
  have hHinner a (k : K) (u v : TangentSpace (perpModel (S.family.metric t₀) x (s x)) k) :
      (H a).inner k u v = (S.family.metric a).inner (phi (k.1, 0))
        (mfderiv (perpModel (S.family.metric t₀) x (s x)) I
          (fun y : perpSpace (S.family.metric t₀) x (s x) => phi (y, 0)) k.1 u)
        (mfderiv (perpModel (S.family.metric t₀) x (s x)) I
          (fun y : perpSpace (S.family.metric t₀) x (s x) => phi (y, 0)) k.1 v) := by
    have hh := hHslice a k u v
    change (H a).inner k u v = (S.family.metric a).inner (Y k)
      (mfderiv (perpModel (S.family.metric t₀) x (s x)) I Y k u)
      (mfderiv (perpModel (S.family.metric t₀) x (s x)) I Y k v) at hh
    rw [hYder] at hh
    exact hh
  have hHevol a (ha : a ∈ interior J) (k : K)
      (u v : TangentSpace (perpModel (S.family.metric t₀) x (s x)) k) :
      HasDerivWithinAt (fun b => (H b).inner k u v)
        (-2 * ricciTensor (H a) k u v) (interior J) a :=
    metric_hasDerivWithinAt_fst_of_local_product S hS
      (fun y : K × O => phi (y.1.1, y.2.1)) hPhi H
      (fun _ => (euclideanMetric (E := ℝ)).restrictOpen O) ha (hreg (interior_subset ha))
      (fun q hq => hHprod q (interior_subset hq)) k ⟨0, hO₀⟩ u v
  have hpos r (hr : r ∈ J) (k : K) : 0 < metricScalarAt (H r) k := by
    have hn := metricScalarAt_localPull (S.family.metric r)
      (fun y : K × O => phi (y.1.1, y.2.1)) hPhi (k, ⟨0, hO₀⟩)
    rw [hHprod r hr, metricScalarAt_prod,
      metricScalarAt_eq_zero_of_finrank_le_one ((euclideanMetric (E := ℝ)).restrictOpen O)
        (by simp : Module.finrank ℝ ℝ ≤ 1), add_zero] at hn
    rw [hn]
    exact DimensionThree.metricScalarAt_pos_of_mem_nonnegativeCone_of_curvatureOperator_rank_one
      hdim (S.family.metric r) _ (hR r hr _) (hrank r hr _)
  have hHsol {α β a : ℝ} (ha : a ∈ Ioo α β) (hsub : Ioo α β ⊆ J) :
      IsSolutionOn ({ base := { metric := H } } :
        SolutionOn (I := perpModel (S.family.metric t₀) x (s x)) (M := K)
          (RealTimeInterval.openInterval α β a ha)) :=
    isSolutionOn_fst_of_local_product S hS H
      (fun _ => (euclideanMetric (E := ℝ)).restrictOpen O)
      (fun y : K × O => phi (y.1.1, y.2.1)) hPhi (⟨0, hO₀⟩ : O) ha
      (hsub.trans hreg) (fun t ht => hHprod t (hsub ht))
  refine ⟨s x, K, O, phi, hPhi, H, hK₀, hO₀, hOconn, hsource, hbase,
    hunit ⟨t₀, ht₀⟩ x hxU, hdimP, hHprod, hHinner, hHevol, hHsol, hpos, ?_⟩
  intro r hr k u v huv
  exact Geometry.Riemannian.sectionalCurvature_pos_of_metricScalarAt_pos_of_finrank_eq_two
    (H r) hdimP k (hpos r hr k) u v huv

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
  obtain ⟨e, K, O, phi, hPhi, h, hK₀, hO₀, hOconn, hsource, hbase, hunit, hdimP,
      hprod, hinner, hevol, hsol, hpos, hsec⟩ :=
    exists_positive_surface_local_product_on_ordConnected S hS hdim ordConnected_Ioo
      (by simpa only [interior_Ioo] using ht₀) hreg hR hrank x
  refine ⟨e, K, O, phi, hPhi, h, hK₀, hO₀, hOconn, hsource, hbase, hunit, hdimP,
    hprod, (fun a _ => hinner a), ?_, hsol ht₀ Subset.rfl, hpos, hsec⟩
  simpa only [interior_Ioo] using hevol

theorem exists_positive_surface_local_product_on_interval_of_nonnegative_curvature
    [ConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    {α β : ℝ} (hreg : Ioo α β ⊆ D.regular)
    {J : Set ℝ} (hJ : J.OrdConnected) (hJsub : J ⊆ Ioo α β)
    {t₀ : ℝ} (ht₀ : t₀ ∈ J)
    (hR : ∀ t ∈ Ioo α β, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hrank : ∀ t ∈ J, ∀ x,
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
      (∀ a ∈ J, localPullMetric (S.family.metric a) (fun y : K × O => phi (y.1.1, y.2.1)) hPhi =
        (h a).prod ((euclideanMetric (E := ℝ)).restrictOpen O)) ∧
      (∀ a ∈ J, ∀ (k : K) (u v : TangentSpace (perpModel (S.family.metric t₀) x e) k),
        (h a).inner k u v = (S.family.metric a).inner (phi (k.1, 0))
          (mfderiv (perpModel (S.family.metric t₀) x e) I
            (fun y : perpSpace (S.family.metric t₀) x e => phi (y, 0)) k.1 u)
          (mfderiv (perpModel (S.family.metric t₀) x e) I
            (fun y : perpSpace (S.family.metric t₀) x e => phi (y, 0)) k.1 v)) ∧
      (∀ a ∈ J, ∀ (k : K) (u v : TangentSpace (perpModel (S.family.metric t₀) x e) k),
        HasDerivWithinAt (fun b => (h b).inner k u v)
          (-2 * ricciTensor (h a) k u v) J a) ∧
      (∀ {α β a : ℝ} (ha : a ∈ Ioo α β), Ioo α β ⊆ J →
        IsSolutionOn ({ base := { metric := h } } :
          SolutionOn (I := perpModel (S.family.metric t₀) x e) (M := K)
            (RealTimeInterval.openInterval α β a ha))) ∧
      (∀ a ∈ J, ∀ k : K, 0 < metricScalarAt (h a) k) ∧
      ∀ a ∈ J, ∀ (k : K) (u v : TangentSpace (perpModel (S.family.metric t₀) x e) k),
        LinearIndependent ℝ ![u, v] → 0 < Geometry.Riemannian.sectionalCurvature (h a) k u v := by
  have hregJ : J ⊆ D.regular := hJsub.trans hreg
  have hRJ r (hr : r ∈ J) := hR r (hJsub hr)
  have hkernel r (hr : r ∈ J) :
      IsParallelContinuousAlternatingSubmoduleFamily (S.family.metric r)
        (fun y => curvatureOperatorKernelAt (S.family.metric r) y
          ⟨metricRm04At (S.family.metric r) y,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) y⟩) := by
    obtain ⟨a, hαa, har⟩ := exists_between (hJsub hr).1
    have hsub : Icc a r ⊆ Ioo α β := fun q hq =>
      ⟨hαa.trans_le hq.1, hq.2.trans_lt (hJsub hr).2⟩
    exact curvatureOperatorKernelAt_parallel_at_later_time S hS hdim har
      (hsub.trans hreg) (fun q hq => hR q (hsub hq))
  obtain ⟨U, s, hU, hxU, -, hunit, hparallel, hdual⟩ :=
    exists_common_parallel_unit_section_of_curvatureOperatorImageAnnihilator_eq
      (fun r : J => S.family.metric r.1) ⟨t₀, ht₀⟩ hdim
      (fun r => hrank r.1 r.2) (fun r => hkernel r.1 r.2)
      (fun r y => (curvatureOperatorImageAnnihilatorAt_eq_and_inner_eq_of_rank_one_on_interval
        S hS hdim hJ hregJ hRJ hrank r.2 ht₀ y).1)
      (fun r y v hv w => (curvatureOperatorImageAnnihilatorAt_eq_and_inner_eq_of_rank_one_on_interval
        S hS hdim hJ hregJ hRJ hrank ht₀ r.2 y).2 v hv w |>.symm) x
  obtain ⟨K, O, phi, hPhi, h, hK₀, hO₀, hOconn, hsource, hbase, -,
      hprod, hinner, hevol, -⟩ := exists_local_product_from_common_parallel_unit_section
    S hS J t₀ ht₀ hregJ x hU hxU s (hunit ⟨t₀, ht₀⟩)
      (fun r hr => hparallel ⟨r, hr⟩) (fun r hr => hdual ⟨r, hr⟩)
  let _ : (perpModel (S.family.metric t₀) x (s x)).Boundaryless := by
    constructor
    ext y
    simp only [Set.mem_range, Set.mem_univ, iff_true]
    exact ⟨y, rfl⟩
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
  have hpos r (hr : r ∈ J) (k : K) : 0 < metricScalarAt (h r) k := by
    have hn := metricScalarAt_localPull (S.family.metric r)
      (fun y : K × O => phi (y.1.1, y.2.1)) hPhi (k, ⟨0, hO₀⟩)
    rw [hprod r hr, metricScalarAt_prod,
      metricScalarAt_eq_zero_of_finrank_le_one ((euclideanMetric (E := ℝ)).restrictOpen O)
        (by simp : Module.finrank ℝ ℝ ≤ 1), add_zero] at hn
    rw [hn]
    exact DimensionThree.metricScalarAt_pos_of_mem_nonnegativeCone_of_curvatureOperator_rank_one
      hdim (S.family.metric r) _ (hRJ r hr _) (hrank r hr _)
  have hsol {a b r : ℝ} (hr : r ∈ Ioo a b) (hsub : Ioo a b ⊆ J) :
      IsSolutionOn ({ base := { metric := h } } :
        SolutionOn (I := perpModel (S.family.metric t₀) x (s x)) (M := K)
          (RealTimeInterval.openInterval a b r hr)) :=
    isSolutionOn_fst_of_local_product S hS h
      (fun _ => (euclideanMetric (E := ℝ)).restrictOpen O)
      (fun y : K × O => phi (y.1.1, y.2.1)) hPhi (⟨0, hO₀⟩ : O) hr
      (hsub.trans hregJ) (fun t ht => hprod t (hsub ht))
  refine ⟨s x, K, O, phi, hPhi, h, hK₀, hO₀, hOconn, hsource, hbase,
    hunit ⟨t₀, ht₀⟩ x hxU, hdimP, hprod, hinner, hevol, hsol, hpos, ?_⟩
  intro r hr k u v huv
  exact Geometry.Riemannian.sectionalCurvature_pos_of_metricScalarAt_pos_of_finrank_eq_two
    (h r) hdimP k (hpos r hr k) u v huv

end DifferentialGeometry.PDE.RicciFlow
