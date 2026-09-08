import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.CurvatureOperatorSectionEvolution
import DifferentialGeometry.Analysis.Parabolic.CurvatureOperatorRank
import DifferentialGeometry.Geometry.Curvature.DimensionThree.ExteriorRank
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ExteriorPositivity

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open Bundle CovariantDerivative Set
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, InnerProductSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  [IsContMDiffRiemannianBundle I ∞ F V]

theorem traceNormalizedCurvatureEndomorphism_pullback_kernel_and_range_eq_of_constant_rank
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ F = 3)
    (ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x)
    {a b : ℝ} (hreg : Ioo a b ⊆ D.regular)
    (hι : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (F →L[ℝ] E) p.2
        (E := fun y => V y →L[ℝ] TangentSpace I y)
        (ι p.1 p.2).toContinuousLinearMap) (Ioo a b ×ˢ (univ : Set M)))
    (hmetric : ∀ t ∈ Ioo a b, ∀ x v w,
      (S.family.metric t).inner x (ι t x v) (ι t x w) = ⟪v, w⟫)
    (hode : ∀ t ∈ Ioo a b, ∀ x v, HasDerivWithinAt (fun s => ι s x v)
      (ricciSharp (S.family.metric t) x (ι t x v)) (Ioo a b) t)
    (hR : ∀ t ∈ Ioo a b, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (q : ℕ) (hrank : ∀ t ∈ Ioo a b, ∀ x,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) = q)
    {s t : ℝ} (hs : s ∈ Ioo a b) (ht : t ∈ Ioo a b) (x : M) :
    letI : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
    let R := fun r y => exteriorPower.traceNormalizedCurvatureEndomorphism
      ((S.base.rm04 r y).compContinuousLinearMap (fun _ => (ι r y).toContinuousLinearMap))
      ((mem_algebraicCurvatureTensorSubmodule.mp
        (metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.base.metric r) y)).compContinuousLinearMap
          (ι r y).toContinuousLinearMap)
    (R s x).ker = (R t x).ker ∧ (R s x).range = (R t x).range := by
  dsimp only
  classical
  let _ : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
  let _ := Bundle.ExteriorPower.totalSpaceTopology F V 2
  let _ := Bundle.ExteriorPower.fiberBundle F V 2
  let _ := Bundle.ExteriorPower.vector_bundle F V 2
  let _ := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
  let _ := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
  let R := fun r y => exteriorPower.traceNormalizedCurvatureEndomorphism
    ((S.base.rm04 r y).compContinuousLinearMap (fun _ => (ι r y).toContinuousLinearMap))
    ((mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.base.metric r) y)).compContinuousLinearMap
        (ι r y).toContinuousLinearMap)
  obtain ⟨A, hA, -, hAspace, -⟩ :=
    exists_traceNormalizedCurvatureEndomorphism_pullback_sections (F := F) S hS ι hreg hι
  have hevolution : ∀ r ∈ Ioo a b,
      ∃ cov : CovariantDerivative I (⋀[ℝ]^2 F) (fun y => ⋀[ℝ]^2 (V y)),
        ContMDiffCovariantDerivative cov ∞ ∧ cov.IsMetricCompatible ∧
        ∀ y, HasDerivAt (fun u => A u y)
          (rawBundleEndomorphismConnLap (S.family.metric r) cov (fun z => A r z) y +
            (curvatureOperatorReactionEndomorphism3 (A r y).toLinearMap).toContinuousLinearMap) r := by
    intro r hr
    have hιr := hι.comp_contMDiff (contMDiff_const.prodMk contMDiff_id)
      (fun y => ⟨hr, mem_univ y⟩)
    have hp := traceNormalizedCurvatureEndomorphism_pullback_section_hasDerivWithinAt_of_ricci_ode
      (F := F) S hS ι hreg hr hιr (hmetric r hr) hdim (hode r hr)
    refine ⟨_, hp.1, hp.2.1, ?_⟩
    intro y
    exact (hp.2.2 A hA y).hasDerivAt (isOpen_Ioo.mem_nhds hr)
  let cov := fun r => if hr : r ∈ Ioo a b then (hevolution r hr).choose
    else (hevolution s hs).choose
  have hcovsmooth : ∀ r, ContMDiffCovariantDerivative (cov r) ∞ := by
    intro r
    dsimp only [cov]
    split_ifs with hr
    · exact (hevolution r hr).choose_spec.1
    · exact (hevolution s hs).choose_spec.1
  let _ := hcovsmooth
  have hcovmetric : ∀ r, (cov r).IsMetricCompatible := by
    intro r
    dsimp only [cov]
    split_ifs with hr
    · exact (hevolution r hr).choose_spec.2.1
    · exact (hevolution s hs).choose_spec.2.1
  have hevol : ∀ r ∈ Ioo a b, ∀ y, HasDerivAt (fun u => A u y)
      (rawBundleEndomorphismConnLap (S.family.metric r) (cov r) (fun z => A r z) y +
        HomConnectionGen.homBundleCovariantDerivativeGen I M
          (⋀[ℝ]^2 F) (fun z => ⋀[ℝ]^2 (V z)) (⋀[ℝ]^2 F) (fun z => ⋀[ℝ]^2 (V z))
          (cov r) (cov r) (fun z => A r z) y 0 +
        (curvatureOperatorReactionEndomorphism3 (A r y).toLinearMap).toContinuousLinearMap) r := by
    intro r hr y
    simpa only [cov, dif_pos hr, map_zero, add_zero] using (hevolution r hr).choose_spec.2.2 y
  have hArank : ∀ r ∈ Ioo a b, ∀ y, Module.finrank ℝ (A r y).range = q := by
    intro r hr y
    rw [hA r hr y]
    exact (traceNormalizedCurvatureEndomorphism_pullback_finrank_range
      ((VectorBundle.finrank_eq ℝ F V y).trans hdim) (S.family.metric r) y
      ⟨metricRm04At (S.family.metric r) y,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) y⟩
      (ι r y) (hmetric r hr y)).trans (hrank r hr y)
  have hApos : ∀ r ∈ Ioo a b, ∀ y, (A r y).IsPositive := by
    intro r hr y
    rw [hA r hr y]
    exact traceNormalizedCurvatureEndomorphism_pullback_isPositive_of_mem_nonnegativeCone
      ⟨metricRm04At (S.family.metric r) y,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) y⟩
      (hR r hr y) (ι r y).toContinuousLinearMap
  have h := DifferentialGeometry.Analysis.Parabolic.curvatureOperator_kernel_and_range_eq_of_constant_rank
    S.family.metric cov hcovmetric A hAspace q hArank hApos (fun _ _ => 0) hevol hs ht (x := x)
  rw [hA s hs x, hA t ht x] at h
  exact h


theorem exists_uhlenbeck_isometry_with_constant_curvatureOperator_kernel_and_range
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
    ∃ ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x,
      (∀ x, ι t₀ x = ι₀ x) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
        (fun p : ℝ × M => TotalSpace.mk' (F →L[ℝ] E) p.2
          (E := fun y => V y →L[ℝ] TangentSpace I y)
          (ι p.1 p.2).toContinuousLinearMap) (Ioo a b ×ˢ (univ : Set M)) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
        (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] F) p.2
          (E := fun y => TangentSpace I y →L[ℝ] V y)
          (ι p.1 p.2).symm.toContinuousLinearMap) (Ioo a b ×ˢ (univ : Set M)) ∧
      (∀ t ∈ Ioo a b, ∀ x v, HasDerivWithinAt (fun s => ι s x v)
        (ricciSharp (S.family.metric t) x (ι t x v)) (Ioo a b) t) ∧
      (∀ t ∈ Ioo a b, ∀ x v w,
        (S.family.metric t).inner x (ι t x v) (ι t x w) = ⟪v, w⟫) ∧
      letI : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
      let R := fun r y => exteriorPower.traceNormalizedCurvatureEndomorphism
        ((S.base.rm04 r y).compContinuousLinearMap (fun _ => (ι r y).toContinuousLinearMap))
        ((mem_algebraicCurvatureTensorSubmodule.mp
          (metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.base.metric r) y)).compContinuousLinearMap
            (ι r y).toContinuousLinearMap)
      ∀ s ∈ Ioo a b, ∀ t ∈ Ioo a b, ∀ x,
        (R s x).ker = (R t x).ker ∧ (R s x).range = (R t x).range := by
  obtain ⟨ι, hinit, hι, hinv, hode, hmetric, -⟩ :=
    exists_uhlenbeck_isometry_with_traceNormalizedCurvatureEndomorphism_evolution
      (F := F) S hS hdim ordConnected_Ioo ht₀ hreg ι₀ hι₀ h₀
  refine ⟨ι, hinit, hι, hinv, (fun t ht x v => hode x v t ht), hmetric, ?_⟩
  dsimp only
  intro s hs t ht x
  exact traceNormalizedCurvatureEndomorphism_pullback_kernel_and_range_eq_of_constant_rank
    S hS hdim ι hreg hι hmetric (fun t ht x v => hode x v t ht) hR q hrank hs ht x

private theorem kernel_eq_of_continuousOn_constant_rank_and_interior
    {W Z : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    [FiniteDimensional ℝ W] [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {A : ℝ → W →L[ℝ] Z} {a b : ℝ} (hab : a < b)
    (hA : ContinuousOn A (Icc a b))
    (hrank : ∀ t ∈ Icc a b, Module.finrank ℝ (A t).range =
      Module.finrank ℝ (A a).range)
    (hinterior : ∀ s ∈ Ioo a b, ∀ t ∈ Ioo a b, (A s).ker = (A t).ker) :
    (A a).ker = (A b).ker := by
  let c := (a + b) / 2
  have hc : c ∈ Ioo a b := ⟨by dsimp [c]; linarith, by dsimp [c]; linarith⟩
  have hcle (r : ℝ) (hr : r ∈ Icc a b) : (A c).ker ≤ (A r).ker := by
    intro v hv
    apply LinearMap.mem_ker.mpr
    have hzero : (Ioo a b).EqOn (fun t => A t v) (fun _ => (0 : Z)) := by
      intro t ht
      apply LinearMap.mem_ker.mp
      rw [← hinterior c hc t ht]
      exact hv
    have hzero' := hzero.of_subset_closure (hA.clm_apply continuousOn_const)
      continuousOn_const Ioo_subset_Icc_self (by rw [closure_Ioo (ne_of_lt hab)])
    exact hzero' hr
  have hdim (r : ℝ) (hr : r ∈ Icc a b) :
      Module.finrank ℝ (A c).ker = Module.finrank ℝ (A r).ker := by
    have hcRank := hrank c ⟨hc.1.le, hc.2.le⟩
    have hrRank := hrank r hr
    have hcDim := (A c).toLinearMap.finrank_range_add_finrank_ker
    have hrDim := (A r).toLinearMap.finrank_range_add_finrank_ker
    omega
  have heq (r : ℝ) (hr : r ∈ Icc a b) : (A c).ker = (A r).ker :=
    Submodule.eq_of_le_of_finrank_eq (hcle r hr) (hdim r hr)
  exact (heq a ⟨le_rfl, hab.le⟩).symm.trans (heq b ⟨hab.le, le_rfl⟩)

theorem traceNormalizedCurvatureEndomorphism_pullback_kernel_and_range_eq_on_interval
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ F = 3)
    (ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x)
    {J : Set ℝ} (hJ : J.OrdConnected) (hreg : J ⊆ D.regular)
    (hι : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (F →L[ℝ] E) p.2
        (E := fun y => V y →L[ℝ] TangentSpace I y)
        (ι p.1 p.2).toContinuousLinearMap) (J ×ˢ (univ : Set M)))
    (hmetric : ∀ t ∈ J, ∀ x v w,
      (S.family.metric t).inner x (ι t x v) (ι t x w) = ⟪v, w⟫)
    (hode : ∀ t ∈ J, ∀ x v, HasDerivWithinAt (fun s => ι s x v)
      (ricciSharp (S.family.metric t) x (ι t x v)) J t)
    (hR : ∀ t ∈ J, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (q : ℕ) (hrank : ∀ t ∈ J, ∀ x,
      Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
        ⟨metricRm04At (S.family.metric t) x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) = q)
    {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) (x : M) :
    letI : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
    let R := fun r y => exteriorPower.traceNormalizedCurvatureEndomorphism
      ((S.base.rm04 r y).compContinuousLinearMap (fun _ => (ι r y).toContinuousLinearMap))
      ((mem_algebraicCurvatureTensorSubmodule.mp
        (metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.base.metric r) y)).compContinuousLinearMap
          (ι r y).toContinuousLinearMap)
    (R s x).ker = (R t x).ker ∧ (R s x).range = (R t x).range := by
  dsimp only
  classical
  let _ : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
  let _ := Bundle.ExteriorPower.totalSpaceTopology F V 2
  let _ := Bundle.ExteriorPower.fiberBundle F V 2
  let _ := Bundle.ExteriorPower.vector_bundle F V 2
  let R := fun r y => exteriorPower.traceNormalizedCurvatureEndomorphism
    ((S.base.rm04 r y).compContinuousLinearMap (fun _ => (ι r y).toContinuousLinearMap))
    ((mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.base.metric r) y)).compContinuousLinearMap
        (ι r y).toContinuousLinearMap)
  have hcont : ContinuousOn (fun r => R r x) J := by
    have hb := traceNormalizedCurvatureEndomorphism_pullback_continuousOn
      S hS ι (fun r hr => D.regular_subset (hreg hr)) hι.continuousOn
    have hslice := hb.comp (continuousOn_id.prodMk continuousOn_const)
      (fun r hr => ⟨hr, mem_univ x⟩)
    exact (totalSpaceMk_isInducing ((⋀[ℝ]^2 F) →L[ℝ] ⋀[ℝ]^2 F)
      (fun y => (⋀[ℝ]^2 (V y)) →L[ℝ] ⋀[ℝ]^2 (V y)) x).continuousOn_iff.mpr hslice
  have hArank : ∀ r ∈ J, Module.finrank ℝ (R r x).range = q := by
    intro r hr
    exact (traceNormalizedCurvatureEndomorphism_pullback_finrank_range
      ((VectorBundle.finrank_eq ℝ F V x).trans hdim) (S.family.metric r) x
      ⟨metricRm04At (S.family.metric r) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric r) x⟩
      (ι r x) (hmetric r hr x)).trans (hrank r hr x)
  have hordered (a b : ℝ) (ha : a ∈ J) (hb : b ∈ J) (hab : a < b) :
      (R a x).ker = (R b x).ker := by
    have hcc := hJ.out ha hb
    have hoo : Ioo a b ⊆ J := Ioo_subset_Icc_self.trans hcc
    apply kernel_eq_of_continuousOn_constant_rank_and_interior hab (hcont.mono hcc)
    · intro r hr
      exact (hArank r (hcc hr)).trans (hArank a ha).symm
    · intro u hu v hv
      exact (traceNormalizedCurvatureEndomorphism_pullback_kernel_and_range_eq_of_constant_rank
        S hS hdim ι (hoo.trans hreg) (hι.mono (Set.prod_mono hoo Set.Subset.rfl))
        (fun r hr => hmetric r (hoo hr))
        (fun r hr x v => (hode r (hoo hr) x v).mono hoo)
        (fun r hr => hR r (hoo hr)) q (fun r hr => hrank r (hoo hr)) hu hv x).1
  have hker : (R s x).ker = (R t x).ker := by
    rcases lt_trichotomy s t with hst | rfl | hts
    · exact hordered s t hs ht hst
    · rfl
    · exact (hordered t s ht hs hts).symm
  refine ⟨hker, ?_⟩
  have hsSymm := exteriorPower.traceNormalizedCurvatureEndomorphism_isSymmetric
    ((S.base.rm04 s x).compContinuousLinearMap (fun _ => (ι s x).toContinuousLinearMap))
    ((mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.base.metric s) x)).compContinuousLinearMap
        (ι s x).toContinuousLinearMap)
  have htSymm := exteriorPower.traceNormalizedCurvatureEndomorphism_isSymmetric
    ((S.base.rm04 t x).compContinuousLinearMap (fun _ => (ι t x).toContinuousLinearMap))
    ((mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.base.metric t) x)).compContinuousLinearMap
        (ι t x).toContinuousLinearMap)
  have horth : (R s x).rangeᗮ = (R t x).rangeᗮ := by
    rw [hsSymm.orthogonal_range, htSymm.orthogonal_range]
    exact hker
  have horthorth := congrArg (fun K : Submodule ℝ (⋀[ℝ]^2 (V x)) => Kᗮ) horth
  simpa using horthorth

end DifferentialGeometry.PDE.RicciFlow
