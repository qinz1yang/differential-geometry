import DifferentialGeometry.Analysis.Parabolic.CurvatureOperatorRank.ClosedInterval
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.CurvatureOperatorRegularity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.CurvatureOperatorSectionEvolution
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

theorem curvatureOperator_rank_spatially_constant_and_locally_constant_from_left_of_uhlenbeck_Icc
    [ConnectedSpace M]
    {D : RealTimeInterval} (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    (hdim : Module.finrank ℝ F = 3)
    {T : ℝ} (hT : 0 < T) (hcarrier : Icc 0 T ⊆ D.carrier)
    (hregular : Ioo 0 T ⊆ D.regular)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I)
      (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (S.family.metric p.1).inner p.2⟩ :
        TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
          (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (Icc 0 T ×ˢ (univ : Set M)))
    (ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (hι : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (F →L[ℝ] E) p.2
        (E := fun x => V x →L[ℝ] TangentSpace I x)
        (ι p.1 p.2).toContinuousLinearMap) (Icc 0 T ×ˢ (univ : Set M)))
    (hmetric : ∀ t ∈ Icc 0 T, ∀ x v w,
      (S.family.metric t).inner x (ι t x v) (ι t x w) = ⟪v, w⟫)
    (hode : ∀ x v, ∀ t ∈ Ioo 0 T, HasDerivWithinAt (fun s => ι s x v)
      (ricciSharp (S.family.metric t) x (ι t x v)) (Icc 0 T) t)
    (hR : ∀ t ∈ Icc 0 T, ∀ x,
      (⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩ :
          algebraicCurvatureTensorSubmodule (I := I) (M := M) x) ∈
            algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    let rank := fun t x => Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
      ⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩)
    (∀ t ∈ Ioc 0 T, ∀ x y, rank t x = rank t y) ∧
    (∀ x, MonotoneOn (fun t => rank t x) (Ioc 0 T)) ∧
    (∀ t ∈ Ioc 0 T, ∀ x, ∃ ε ∈ Ioc 0 t, ∀ s ∈ Ioc (t - ε) t,
      rank s x = rank t x) ∧
    ∃ δ ∈ Ioc 0 T, ∃ q : ℕ, ∀ t ∈ Ioc 0 δ, ∀ x, rank t x = q := by
  dsimp only
  classical
  let _ : ∀ y, FiniteDimensional ℝ (V y) := fun y => VectorBundle.finiteDimensional ℝ F V y
  let _ := Bundle.ExteriorPower.totalSpaceTopology F V 2
  let _ := Bundle.ExteriorPower.fiberBundle F V 2
  let _ := Bundle.ExteriorPower.vector_bundle F V 2
  let _ := Bundle.ExteriorPower.contMDiffVectorBundle (IB := I) (n := ∞) F V 2
  let _ := Bundle.ExteriorPower.isContMDiffRiemannianBundle (IB := I) (n := ∞) F V 2
  have hsub : Ioo 0 T ⊆ Icc 0 T := Ioo_subset_Icc_self
  obtain ⟨A, hA, -, -, hAcont⟩ :=
    exists_traceNormalizedCurvatureEndomorphism_pullback_sections_on_carrier
      (F := F) S hS ι hcarrier hsub hregular hι
  have hslice (t : ℝ) (ht : t ∈ Ioo 0 T) :
      ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
        (fun y => TotalSpace.mk' (F →L[ℝ] E) y (ι t y).toContinuousLinearMap) :=
    hι.comp_contMDiff (contMDiff_const.prodMk contMDiff_id)
      (fun y => ⟨hsub ht, mem_univ y⟩)
  let pull (t : ℝ) (ht : t ∈ Ioo 0 T) := CovariantDerivative.pullbackFiberwiseLinearEquiv
    (fun y => (ι t y).toLinearEquiv)
    ((hslice t ht).of_le (show (1 : ℕ∞ω) ≤ ∞ by simp)).clm_bundle_map
    (LeviCivita (S.family.metric t))
  have hp (t : ℝ) (ht : t ∈ Ioo 0 T) :=
    traceNormalizedCurvatureEndomorphism_pullback_section_hasDerivWithinAt_of_ricci_ode
      (F := F) S hS ι hregular ht (hslice t ht) (hmetric t (hsub ht)) hdim
      (fun x v => (hode x v t ht).mono hsub)
  have hmid : T / 2 ∈ Ioo 0 T := ⟨half_pos hT, half_lt_self hT⟩
  let cov := fun t => if ht : t ∈ Ioo 0 T then (pull t ht).exteriorPower 2
    else (pull (T / 2) hmid).exteriorPower 2
  have hcovsmooth : ∀ t ∈ Ioo 0 T, ContMDiffCovariantDerivative (cov t) ∞ := by
    intro t ht
    simpa only [cov, dif_pos ht, pull] using (hp t ht).1
  have hcovmetric : ∀ t ∈ Ioo 0 T, (cov t).IsMetricCompatible := by
    intro t ht
    simpa only [cov, dif_pos ht, pull] using (hp t ht).2.1
  have hApos : ∀ t ∈ Icc 0 T, ∀ x, (A t x).IsPositive := by
    intro t ht x
    rw [hA t ht x]
    exact traceNormalizedCurvatureEndomorphism_pullback_isPositive_of_mem_nonnegativeCone
      ⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩
      (hR t ht x) (ι t x).toContinuousLinearMap
  have hevolution : ∀ t ∈ Ioo 0 T, ∀ x, HasDerivAt (fun s => A s x)
      (rawBundleEndomorphismConnLap (S.family.metric t) (cov t) (fun y => A t y) x +
        (curvatureOperatorReactionEndomorphism3 (A t x).toLinearMap).toContinuousLinearMap) t := by
    intro t ht x
    have hd := (hp t ht).2.2 A (fun s hs y => hA s (hsub hs) y) x
    simpa only [cov, dif_pos ht, pull] using hd.hasDerivAt (isOpen_Ioo.mem_nhds ht)
  have hrank := DifferentialGeometry.Analysis.Parabolic.curvatureOperator_rank_spatially_constant_and_locally_constant_from_left_on_Icc
      S.family.metric cov hT hg hcovsmooth hcovmetric A hApos hAcont hevolution
  have hArank (t : ℝ) (ht : t ∈ Icc 0 T) (x : M) :
      Module.finrank ℝ (A t x).range =
        Module.finrank ℝ (curvatureOperatorImageAt (S.family.metric t) x
          ⟨metricRm04At (S.family.metric t) x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩) := by
    rw [hA t ht x]
    exact traceNormalizedCurvatureEndomorphism_pullback_finrank_range
      ((VectorBundle.finrank_eq ℝ F V x).trans hdim) (S.family.metric t) x
      ⟨metricRm04At (S.family.metric t) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (S.family.metric t) x⟩
      (ι t x) (hmetric t ht x)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t ht x y
    exact (hArank t ⟨ht.1.le, ht.2⟩ x).symm.trans
      ((hrank.1 t ht x y).trans (hArank t ⟨ht.1.le, ht.2⟩ y))
  · intro x s hs t ht hst
    dsimp only
    rw [← hArank s ⟨hs.1.le, hs.2⟩ x, ← hArank t ⟨ht.1.le, ht.2⟩ x]
    exact hrank.2.1 x hs ht hst
  · intro t ht x
    obtain ⟨ε, hε, hstable⟩ := hrank.2.2.1 t ht x
    refine ⟨ε, hε, ?_⟩
    intro s hs
    have hsT : s ∈ Icc 0 T := ⟨by linarith [hε.2, hs.1], hs.2.trans ht.2⟩
    rw [← hArank s hsT x, ← hArank t ⟨ht.1.le, ht.2⟩ x]
    exact hstable s hs
  · obtain ⟨δ, hδ, q, hq⟩ := hrank.2.2.2
    refine ⟨δ, hδ, q, ?_⟩
    intro t ht x
    rw [← hArank t ⟨ht.1.le, ht.2.trans hδ.2⟩ x]
    exact hq t ht x

end DifferentialGeometry.PDE.RicciFlow
