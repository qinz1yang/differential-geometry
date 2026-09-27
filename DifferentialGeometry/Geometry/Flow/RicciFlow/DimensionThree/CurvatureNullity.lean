import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.CurvatureOperatorTimeInvariance
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.Nullity
import DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorImage
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Nullity
import DifferentialGeometry.Geometry.Metric.BundlePullbackSmooth
import DifferentialGeometry.Geometry.Connection.ModelNorm

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle (MetricFiberData)
open scoped Manifold ContDiff RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

private theorem curvature_nullity_fixed_of_uhlenbeck_isometry
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
    [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
    [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
    [IsContMDiffRiemannianBundle I ∞ F V]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ F = 3)
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b) (hreg : Ioo a b ⊆ D.regular)
    (ι₀ : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι₀ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι₀ x).toContinuousLinearMap))
    (h₀ : ∀ x v w, (S.family.metric t₀).inner x (ι₀ x v) (ι₀ x w) = ⟪v, w⟫)
    (hR : ∀ t ∈ Ioo a b, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (q : ℕ) (hrank : ∀ t ∈ Ioo a b, ∀ x,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) = q) :
    ∀ s ∈ Ioo a b, ∀ t ∈ Ioo a b, ∀ x,
      let L := fun r => curvatureOperatorImageAnnihilatorAt (S.family.metric r) x
        ⟨metricRm04At (S.family.metric r) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩
      L s = L t ∧ ∀ v ∈ L s, ∀ w,
        (S.family.metric s).inner x v w = (S.family.metric t).inner x v w := by
  let _ : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
  obtain ⟨ι, -, -, -, hode, hmetric, hfixed⟩ :=
    exists_uhlenbeck_isometry_with_constant_curvatureOperator_kernel_and_range
      (F := F) S hS hdim ht₀ hreg ι₀ hι₀ h₀ hR q hrank
  dsimp only at hfixed
  intro s hs t ht x
  let L := fun r => curvatureOperatorImageAnnihilatorAt (S.family.metric r) x
    ⟨metricRm04At (S.family.metric r) x,
      metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩
  let R := fun r => exteriorPower.traceNormalizedCurvatureEndomorphism
    ((S.base.rm04 r x).compContinuousLinearMap (fun _ => (ι r x).toContinuousLinearMap))
    ((mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.base.metric r) x)).compContinuousLinearMap
        (ι r x).toContinuousLinearMap)
  have hiff (r : ℝ) (hr : r ∈ Ioo a b) (v : V x) :
      ι r x v ∈ L r ↔ v ∈ ContinuousAlternatingMap.contractionAnnihilator
        (Submodule.map (exteriorPower.musicalEquiv (E := V x) 2).toLinearMap (R r).range) := by
    exact mem_curvatureOperatorImageAnnihilatorAt_pullback_musical_iff
      ((VectorBundle.finrank_eq ℝ F V x).trans hdim) (S.family.metric r) x
      ⟨metricRm04At (S.family.metric r) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩
      (ι r x) (hmetric r hr x) v
  have htransfer (u : ℝ) (hu : u ∈ Ioo a b) (v : TangentSpace I x) (hv : v ∈ L u) :
      ∀ r ∈ Ioo a b, v ∈ L r ∧ ∀ w,
        (S.family.metric u).inner x v w = (S.family.metric r).inner x v w := by
    let z := (ι u x).symm v
    have hmem (r : ℝ) (hr : r ∈ Ioo a b) : ι r x z ∈ L r := by
      apply (hiff r hr z).mpr
      have hz := (hiff u hu z).mp (by simpa [z] using hv)
      have heq : (R u).range = (R r).range := (hfixed u hu r hr x).2
      rwa [← heq]
    have hzero (r : ℝ) (hr : r ∈ Ioo a b) :
        ricciSharp (S.family.metric r) x (ι r x z) = 0 :=
      ricciSharp_eq_zero_of_mem_curvatureOperatorImageAnnihilatorAt
        (S.family.metric r) x (hmem r hr)
    have hc := uhlenbeck_section_eq_and_inner_eq_of_ricciSharp_eq_zero
      S hS ordConnected_Ioo hreg x (fun r => ι r x z)
      (fun r hr => hode r hr x z) hzero
    intro r hr
    have hvu : ι u x z = v := (ι u x).apply_symm_apply v
    have hvr : ι r x z = v := (hc.1 r hr u hu).trans hvu
    refine ⟨by simpa only [hvr] using hmem r hr, ?_⟩
    intro w
    simpa only [hvu, hvr] using hc.2 u hu r hr w
  refine ⟨le_antisymm (fun v hv => (htransfer s hs v hv t ht).1)
    (fun v hv => (htransfer t ht v hv s hs).1), ?_⟩
  intro v hv w
  exact (htransfer s hs v hv t ht).2 w

variable
  {F : Type*} [oldNorm : NormedAddCommGroup F] [oldSpace : NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

private theorem curvature_nullity_fixed_metric
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ F = 3)
    {a b t₀ : ℝ} (ht₀ : t₀ ∈ Ioo a b) (hreg : Ioo a b ⊆ D.regular)
    (h : ContMDiffRiemannianMetric I ∞ F V)
    (ι₀ : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι₀ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι₀ x).toContinuousLinearMap))
    (h₀ : ∀ x v w, (S.family.metric t₀).inner x (ι₀ x v) (ι₀ x w) = h.inner x v w)
    (hR : ∀ t ∈ Ioo a b, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (q : ℕ) (hrank : ∀ t ∈ Ioo a b, ∀ x,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) = q) :
    ∀ s ∈ Ioo a b, ∀ t ∈ Ioo a b, ∀ x,
      let L := fun r => curvatureOperatorImageAnnihilatorAt (S.family.metric r) x
        ⟨metricRm04At (S.family.metric r) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩
      L s = L t ∧ ∀ v ∈ L s, ∀ w,
        (S.family.metric s).inner x v w = (S.family.metric t).inner x v w := by
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let : RiemannianBundle V := ⟨h.toRiemannianMetric⟩
  let sourceNorm : ∀ y, NormedAddCommGroup (V y) := fun y =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal y
  let : ∀ y, NormedAddCommGroup (V y) := sourceNorm
  let : ∀ y, SeminormedAddCommGroup (V y) := fun y => (sourceNorm y).toSeminormedAddCommGroup
  let : ∀ y, InnerProductSpace ℝ (V y) := fun y => Bundle.instInnerProductSpaceReal y
  let : IsContMDiffRiemannianBundle I ∞ F V := ⟨h.inner, h.contMDiff, fun _ _ _ => rfl⟩
  let m := MetricFiberData.ofFiniteDimensional F
  have hιwithin := fun y =>
    (contMDiffWithinAt_hom_totalSpace_domain_model_metric_iff
      (IA := I) (IB := I) (F := E) (V := TangentSpace I) (W := V) m
      (n := ∞) (f := fun z => TotalSpace.mk' (F →L[ℝ] E) z (ι₀ z).toContinuousLinearMap)
      (s := Set.univ) (x := y)).mpr ((hι₀ y).contMDiffWithinAt (s := Set.univ))
  let vb := vector_bundle_model_metric (V := V) m
  let svb := contMDiffVectorBundle_model_metric (IB := I) (V := V) (n := ∞) m
  let rm := isContMDiffRiemannianBundle_model_metric (IB := I) (V := V) (n := ∞) m
  let : NormedAddCommGroup F := m.toNormedAddCommGroupOfTopology
  let : InnerProductSpace ℝ F := @MetricFiberData.toInnerProductSpaceOfTopology F oldNorm.toAddCommGroup oldSpace.toModule
      _ _ (by let : SeminormedAddCommGroup F := oldNorm.toSeminormedAddCommGroup
              let : NormedSpace ℝ F := oldSpace
              infer_instance) _ _ m
  let : VectorBundle ℝ F V := vb
  let : ContMDiffVectorBundle ∞ F V I := svb
  let : IsContMDiffRiemannianBundle I ∞ F V := rm
  have hιnew : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun y => TotalSpace.mk' (F →L[ℝ] E) y (ι₀ y).toContinuousLinearMap) :=
    fun y => contMDiffWithinAt_univ.mp (hιwithin y)
  exact curvature_nullity_fixed_of_uhlenbeck_isometry (F := F) (V := V)
    S hS hdim ht₀ hreg ι₀ hιnew h₀ hR q hrank

theorem curvatureOperatorImageAnnihilatorAt_eq_and_inner_eq_of_constant_rank
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    {a b s t : ℝ} (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b)
    (hreg : Ioo a b ⊆ D.regular)
    (hR : ∀ r ∈ Ioo a b, ∀ x,
      (⟨metricRm04At (S.family.metric r) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (q : ℕ) (hrank : ∀ r ∈ Ioo a b, ∀ x,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric r) x
        ⟨metricRm04At (S.family.metric r) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩) = q)
    (x : M) :
    let L := fun r => curvatureOperatorImageAnnihilatorAt (S.family.metric r) x
      ⟨metricRm04At (S.family.metric r) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩
    L s = L t ∧ ∀ v ∈ L s, ∀ w,
      (S.family.metric s).inner x v w = (S.family.metric t).inner x v w := by
  exact curvature_nullity_fixed_metric (F := E) (V := TangentSpace I) S hS hdim hs hreg
    (S.family.metric s) (fun y => ContinuousLinearEquiv.refl ℝ (TangentSpace I y))
    (show ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E)) ∞
      (fun y : M => TotalSpace.mk' (E →L[ℝ] E) y
        (ContinuousLinearMap.id ℝ (TangentSpace I y))) from
      (contMDiff_id : ContMDiff I I ∞ (fun y : M => y)).clm_bundle_id)
    (fun _ _ _ => rfl) hR q hrank s hs t ht x


omit [I.Boundaryless] in
private theorem tensor04StdAt_continuousAt_of_solution
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {t : ℝ} (ht : t ∈ D.regular) (x : M) (a b v w : TangentSpace I x) :
    ContinuousAt (fun r => tensor04StandardAt (metricRm04At (S.family.metric r) x) a b v w) t := by
  have hc : ContinuousOn
      (fun r => tensor04StandardAt (metricRm04At (S.family.metric r) x) a b v w) D.carrier := by
    apply continuousOn_iff_continuous_domRestrict.mpr
    exact hS.rm04Cont.eval_continuous (P := D.carrier) continuous_subtype_val
      (fun r => r.property) continuous_const (fun _ => continuous_const)
  exact (hc t (D.regular_subset ht)).continuousAt
    (Filter.mem_of_superset (D.regular_isOpen.mem_nhds ht) D.regular_subset)

private theorem curvature_nullity_fixed_between_endpoints
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    {a b : ℝ} (hab : a < b) (hreg : Icc a b ⊆ D.regular)
    (hR : ∀ r ∈ Icc a b, ∀ x,
      (⟨metricRm04At (S.family.metric r) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hrank : ∀ r ∈ Icc a b, ∀ x,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric r) x
        ⟨metricRm04At (S.family.metric r) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩) = 1)
    (x : M) :
    let L := fun r => curvatureOperatorImageAnnihilatorAt (S.family.metric r) x
      ⟨metricRm04At (S.family.metric r) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩
    L a = L b ∧ ∀ v ∈ L a, ∀ w,
      (S.family.metric a).inner x v w = (S.family.metric b).inner x v w := by
  let L := fun r => curvatureOperatorImageAnnihilatorAt (S.family.metric r) x
    ⟨metricRm04At (S.family.metric r) x,
      metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩
  obtain ⟨c, hac, hcb⟩ := exists_between hab
  have hc : c ∈ Ioo a b := ⟨hac, hcb⟩
  have hfixed (r : ℝ) (hr : r ∈ Ioo a b) : L c = L r ∧ ∀ v ∈ L c, ∀ w,
      (S.family.metric c).inner x v w = (S.family.metric r).inner x v w :=
    curvatureOperatorImageAnnihilatorAt_eq_and_inner_eq_of_constant_rank S hS hdim hc hr
      (Ioo_subset_Icc_self.trans hreg) (fun r hr => hR r (Ioo_subset_Icc_self hr))
      1 (fun r hr => hrank r (Ioo_subset_Icc_self hr)) x
  have hmem_end (r : ℝ) (hr : r ∈ Icc a b) : L c ≤ L r := by
    intro v hv
    apply (mem_curvatureOperatorImageAnnihilatorAt_iff_tensor04StandardAt_eq_zero
      (S.family.metric r) x _ v).mpr
    intro u w z
    apply (tensor04StdAt_continuousAt_of_solution S hS (hreg hr) x u w v z).continuousWithinAt.eq_const_of_mem_closure
    · rw [closure_Ioo hab.ne]
      exact hr
    · intro y hy
      exact tensor04StdAt_eq_zero_of_mem_curvatureOperatorImageAnnihilatorAt
        (S.family.metric y) x _ ((hfixed y hy).1 ▸ hv) u w z
  have heq_end (r : ℝ) (hr : r ∈ Icc a b) : L c = L r :=
    Submodule.eq_of_le_of_finrank_eq (hmem_end r hr)
      ((curvatureOperatorImageAnnihilatorAt_finrank hdim (S.family.metric c) x _
        (hrank c ⟨hac.le, hcb.le⟩ x)).trans
          (curvatureOperatorImageAnnihilatorAt_finrank hdim (S.family.metric r) x _
            (hrank r hr x)).symm)
  have ha : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
  have hb : b ∈ Icc a b := ⟨hab.le, le_rfl⟩
  refine ⟨(heq_end a ha).symm.trans (heq_end b hb), ?_⟩
  intro v hv w
  have hvc : v ∈ L c := (heq_end a ha).symm ▸ hv
  have hinner_end (r : ℝ) (hr : r ∈ Icc a b) :
      (S.family.metric r).inner x v w = (S.family.metric c).inner x v w := by
    apply (metricDerivAt S hS ⟨r, hreg hr⟩ x v w).continuousAt.continuousWithinAt.eq_const_of_mem_closure
    · rw [closure_Ioo hab.ne]
      exact hr
    · intro y hy
      exact ((hfixed y hy).2 v hvc w).symm
  exact (hinner_end a ha).trans (hinner_end b hb).symm

theorem curvatureOperatorImageAnnihilatorAt_eq_and_inner_eq_of_rank_one_on_interval
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ E = 3)
    {J : Set ℝ} (hJ : J.OrdConnected) (hreg : J ⊆ D.regular)
    (hR : ∀ r ∈ J, ∀ x,
      (⟨metricRm04At (S.family.metric r) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hrank : ∀ r ∈ J, ∀ x,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric r) x
        ⟨metricRm04At (S.family.metric r) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩) = 1)
    {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) (x : M) :
    let L := fun r => curvatureOperatorImageAnnihilatorAt (S.family.metric r) x
      ⟨metricRm04At (S.family.metric r) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩
    L s = L t ∧ ∀ v ∈ L s, ∀ w,
      (S.family.metric s).inner x v w = (S.family.metric t).inner x v w := by
  rcases lt_trichotomy s t with hst | rfl | hts
  · have hsub := hJ.out hs ht
    exact curvature_nullity_fixed_between_endpoints S hS hdim hst (hsub.trans hreg)
      (fun r hr => hR r (hsub hr)) (fun r hr => hrank r (hsub hr)) x
  · exact ⟨rfl, fun _ _ _ => rfl⟩
  · have hsub := hJ.out ht hs
    obtain ⟨heq, hinner⟩ := curvature_nullity_fixed_between_endpoints S hS hdim hts
      (hsub.trans hreg) (fun r hr => hR r (hsub hr)) (fun r hr => hrank r (hsub hr)) x
    refine ⟨heq.symm, ?_⟩
    intro v hv w
    exact (hinner v (heq.symm ▸ hv) w).symm

end DifferentialGeometry.PDE.RicciFlow
