import DifferentialGeometry.Analysis.Parabolic.Dirichlet.CometricDifferenceFamily
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.DriftSubPotentialFamily
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.EnergyTrace
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.MaximalRegularity.Nonautonomous

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal InnerProductSpace Manifold NNReal RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Analysis.Sobolev.Hs
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.DivergenceTheorem (tangentSectionAction)
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private theorem exists_local_energy_solution
    (q : SmoothRiemannianMetric (I_half n) M)
    {T₀ : ℝ} (hT₀ : 0 < T₀)
    (A₂ : ℝ → DirichletHs q 1 →L[ℝ] DirichletHs q (-1))
    (hA₂ : ∀ v, AEStronglyMeasurable (fun t => A₂ t v) (timeMeasure T₀))
    (C₂ : NNReal) (hC₂ : ∀ᵐ t ∂timeMeasure T₀, ‖A₂ t‖ ≤ (C₂ : ℝ))
    (hsmall : (C₂ : ℝ) < 1)
    (A₁ : ℝ → DirichletHs q 0 →L[ℝ] DirichletHs q (-1))
    (hA₁ : ∀ v, AEStronglyMeasurable (fun t => A₁ t v) (timeMeasure T₀))
    (C₁ : NNReal) (hC₁ : ∀ᵐ t ∂timeMeasure T₀, ‖A₁ t‖ ≤ (C₁ : ℝ)) :
    ∃ T : ℝ, 0 < T ∧ T ≤ T₀ ∧
      ∀ (u₀ : DirichletHs q 0) (f₀ : timeL2 (DirichletHs q (-1)) T),
        ∃ (u : timeH1 (DirichletHs q (-1)) T)
          (U₂ : timeL2 (DirichletHs q 1) T) (U₁ : timeL2 (DirichletHs q 0) T),
          u.initial = dirichletHsInclusion (show (-1 : ℝ) ≤ 0 by norm_num) u₀ ∧
          (fun t => dirichletHsInclusion (show (-1 : ℝ) ≤ 1 by norm_num) (U₂ t))
            =ᵐ[timeMeasure T] u.toFun ∧
          (fun t => dirichletHsInclusion (show (-1 : ℝ) ≤ 0 by norm_num) (U₁ t))
            =ᵐ[timeMeasure T] u.toFun ∧
          u.deriv =ᵐ[timeMeasure T] fun t =>
            dirichletBilinearFormToHs q (-dirichletEnergyForm q) (U₂ t) +
              A₂ t (U₂ t) + A₁ t (U₁ t) + f₀ t := by
  let i₂ := dirichletHsInclusion (g := q) (show (1 : ℝ) ≤ -1 + 2 by norm_num)
  let i₁ := dirichletHsInclusion (g := q) (show (0 : ℝ) ≤ -1 + 1 by norm_num)
  let j₁ := dirichletHsInclusion (g := q) (show (-1 : ℝ) + 1 ≤ 0 by norm_num)
  let B₂ := fun t => (A₂ t).comp i₂
  let B₁ := fun t => (A₁ t).comp i₁
  have hB₂ : ∀ v, AEStronglyMeasurable (fun t => B₂ t v) (timeMeasure T₀) :=
    fun v => hA₂ (i₂ v)
  have hB₁ : ∀ v, AEStronglyMeasurable (fun t => B₁ t v) (timeMeasure T₀) :=
    fun v => hA₁ (i₁ v)
  have hbound₂ : ∀ᵐ t ∂timeMeasure T₀, ‖B₂ t‖ ≤ (C₂ : ℝ) := by
    filter_upwards [hC₂] with t ht
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_left
        (DirichletHs.dirichletHsInclusion_opNorm_le_one _) (norm_nonneg _)).trans
        (by simpa only [mul_one] using ht))
  have hbound₁ : ∀ᵐ t ∂timeMeasure T₀, ‖B₁ t‖ ≤ (C₁ : ℝ) := by
    filter_upwards [hC₁] with t ht
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_left
        (DirichletHs.dirichletHsInclusion_opNorm_le_one _) (norm_nonneg _)).trans
        (by simpa only [mul_one] using ht))
  obtain ⟨T, hT, hTT₀, hsol⟩ :=
    MaximalRegularity.exists_local_nonautonomous_solution (g := q) (a := (-1 : ℝ))
      hT₀ B₂ hB₂ C₂ hbound₂ hsmall B₁ hB₁ C₁ hbound₁
  refine ⟨T, hT, hTT₀, fun u₀ f₀ => ?_⟩
  obtain ⟨u, V₂, V₁, hinitial, hfield₂, hfield₁, heq⟩ := hsol (j₁ u₀) f₀
  let U₂ := i₂.compLpL 2 (timeMeasure T) V₂
  let U₁ := i₁.compLpL 2 (timeMeasure T) V₁
  have hU₂ : U₂ =ᵐ[timeMeasure T] fun t => i₂ (V₂ t) := i₂.coeFn_compLpL V₂
  have hU₁ : U₁ =ᵐ[timeMeasure T] fun t => i₁ (V₁ t) := i₁.coeFn_compLpL V₁
  refine ⟨u, U₂, U₁, ?_, ?_, ?_, ?_⟩
  · rw [hinitial]
    exact (DirichletHs.dirichletHsInclusion_trans_apply _ _ u₀).symm
  · filter_upwards [hU₂, hfield₂] with t ht hf
    rw [ht]
    exact (DirichletHs.dirichletHsInclusion_trans_apply _ _ (V₂ t)).symm.trans hf
  · filter_upwards [hU₁, hfield₁] with t ht hf
    rw [ht]
    exact (DirichletHs.dirichletHsInclusion_trans_apply _ _ (V₁ t)).symm.trans hf
  · filter_upwards [hU₂, hU₁, heq] with t ht₂ ht₁ ht
    rw [ht, ht₂, ht₁, ← dirichletBilinearFormToHs_neg_energyForm_eq_laplacian]
    rfl

theorem exists_local_dirichlet_cometric_weak_solution
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    (h0reg : (0 : ℝ) ∈ D.regular)
    (Y : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ → C^∞⟮I_half n, M; ℝ⟯)
    (hY : ContinuousOn
      (fun p : ℝ × M =>
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (Y p.1 p.2) :
          TangentBundle (I_half n) M)) (D.regular ×ˢ (Set.univ : Set M)))
    (hdiv : ContinuousOn
      (fun p : ℝ × M => divergence (I := I_half n)
        (leviCivitaConnectionOfMetric (I := I_half n) (G.metric 0)) (Y p.1) p.2)
      (D.regular ×ˢ (Set.univ : Set M)))
    (ha : ContinuousOn (fun p : ℝ × M => a p.1 p.2)
      (D.regular ×ˢ (Set.univ : Set M))) :
    let q := G.metric 0
    ∃ T : ℝ, 0 < T ∧ Icc (0 : ℝ) T ⊆ D.regular ∧
      ∀ (u₀ : DirichletHs q 0) (f₀ : timeL2 (DirichletHs q (-1)) T),
        ∃ (u : timeH1 (DirichletHs q (-1)) T)
          (U₂ : timeL2 (DirichletHs q 1) T) (U₀ : ℝ → DirichletHs q 0),
          ContinuousOn U₀ (Icc (0 : ℝ) T) ∧ U₀ 0 = u₀ ∧
          (fun t => dirichletHsInclusion (show (0 : ℝ) ≤ 1 by norm_num) (U₂ t))
            =ᵐ[timeMeasure T] U₀ ∧
          (∀ t ∈ Icc (0 : ℝ) T,
            dirichletHsInclusion (show (-1 : ℝ) ≤ 0 by norm_num) (U₀ t) = u.toFun t) ∧
          ∀ᵐ t ∂timeMeasure T, ∀ φ : SmoothScalarDirichlet q,
            dirichletHsNegOneEquivH1Dual q (u.deriv t) (smoothToH1ComplDirichlet q φ) =
              (∫ x, dirichletHsZeroEquivL2 q (U₀ t) x *
                WithBoundary.ΔGWithBoundary (I := I_half n) q φ.smooth φ.interior_support x
                ∂riemannianVolumeMeasure (I := I_half n) (M := M) q) +
              (∫ x, dirichletHsZeroEquivL2 q (U₀ t) x *
                divergence (I := I_half n) (leviCivitaConnectionOfMetric (I := I_half n) q)
                  (WithBoundary.gradGWithBoundarySection (I := I_half n)
                      (G.metric t) φ.smooth φ.interior_support -
                    WithBoundary.gradGWithBoundarySection (I := I_half n) q
                      φ.smooth φ.interior_support) x
                ∂riemannianVolumeMeasure (I := I_half n) (M := M) q) -
              (∫ x, dirichletHsZeroEquivL2 q (U₀ t) x *
                (tangentSectionAction (I := I_half n) (Y t) φ.toFun x +
                  (divergence (I := I_half n) (leviCivitaConnectionOfMetric (I := I_half n) q)
                    (Y t) x + a t x) * φ.toFun x)
                ∂riemannianVolumeMeasure (I := I_half n) (M := M) q) +
              dirichletHsNegOneEquivH1Dual q (f₀ t) (smoothToH1ComplDirichlet q φ) := by
  intro q
  obtain ⟨T₀, A₂, hT₀, hreg, hA₂, hC₂, hmetric⟩ :=
    exists_dirichletCometricDifferenceLaplacianOnIcc hG q rfl h0reg
      (eta := (1 / 2 : ℝ)) (by norm_num)
  have hY₀ := hY.mono (Set.prod_mono hreg Set.Subset.rfl)
  have hdiv₀ := hdiv.mono (Set.prod_mono hreg Set.Subset.rfl)
  have ha₀ := ha.mono (Set.prod_mono hreg Set.Subset.rfl)
  let A₁ := dirichletDriftSubPotentialOnIcc q Y a T₀
  have hA₁ : ∀ v, AEStronglyMeasurable (fun t => A₁ t v) (timeMeasure T₀) :=
    dirichletDriftSubPotentialOnIcc_apply_aestronglyMeasurable q Y a hY₀ ha₀
  obtain ⟨C, hC, hbound⟩ := exists_uniform_norm_dirichletDriftSubPotentialOnIcc
    q Y a hY₀ hdiv₀ ha₀
  obtain ⟨T, hT, hTT₀, hsol⟩ := exists_local_energy_solution q hT₀ A₂ hA₂
    ⟨1 / 2, by norm_num⟩ (Filter.Eventually.of_forall hC₂)
    (by change (1 / 2 : ℝ) < 1; norm_num)
    A₁ hA₁ ⟨C, hC⟩ (Filter.Eventually.of_forall hbound)
  have hsub : Icc (0 : ℝ) T ⊆ Icc (0 : ℝ) T₀ := Icc_subset_Icc le_rfl hTT₀
  refine ⟨T, hT, hsub.trans hreg, fun u₀ f₀ => ?_⟩
  obtain ⟨u, U₂, U₀, hinitial, hfield₂, hfield₀, heq⟩ := hsol u₀ f₀
  have hfield : (fun t => dirichletHsInclusion (show (0 : ℝ) ≤ 1 by norm_num) (U₂ t))
      =ᵐ[timeMeasure T] U₀ := by
    filter_upwards [hfield₂, hfield₀] with t ht₂ ht₀
    apply DirichletHs.dirichletHsInclusion_injective (show (-1 : ℝ) ≤ 0 by norm_num)
    rw [← DirichletHs.dirichletHsInclusion_trans_apply]
    exact ht₂.trans ht₀.symm
  obtain ⟨V, hVcont, hVae, hVpoint, hVenergy⟩ :=
    exists_continuous_dirichletHs_zero_representative q hT u U₂ hfield₂
  have hV₀ : V =ᵐ[timeMeasure T] U₀ := hVae.trans hfield
  refine ⟨u, U₂, V, hVcont, ?_, hVae.symm, hVpoint, ?_⟩
  · apply DirichletHs.dirichletHsInclusion_injective (show (-1 : ℝ) ≤ 0 by norm_num)
    rw [hVpoint 0 ⟨le_rfl, hT.le⟩, timeH1.toFun_zero, hinitial]
  filter_upwards [heq, hVae, hV₀, ae_restrict_mem measurableSet_Icc] with t ht hVt hV₀t htmem
  have hU := hVt.symm
  intro φ
  have ht₀ := hsub htmem
  have hprincipal := hmetric t ht₀ (U₂ t) φ
  rw [hU] at hprincipal
  have hbase : dirichletHsNegOneEquivH1Dual q
      (dirichletBilinearFormToHs q (-dirichletEnergyForm q) (U₂ t))
      (smoothToH1ComplDirichlet q φ) =
      ∫ x, dirichletHsZeroEquivL2 q (V t) x *
        WithBoundary.ΔGWithBoundary (I := I_half n) q φ.smooth φ.interior_support x
        ∂riemannianVolumeMeasure (I := I_half n) (M := M) q := by
    rw [dirichletHsNegOneEquivH1Dual_bilinearFormToHs]
    change -(dirichletEnergyForm q (dirichletHsOneEquivH1Compl q (U₂ t))
      (smoothToH1ComplDirichlet q φ)) = _
    rw [dirichletEnergyForm_apply_smooth_right, neg_neg,
      H1ComplDirichletToLp_dirichletHsOneEquivH1Compl, hU]
  have hlower := dirichletHsNegOneEquivH1Dual_driftSubPotential_apply_smooth_right
    q (Y t) (a t) (V t) φ
  have hA₁t : A₁ t = dirichletDriftSubPotential q (Y t) (a t) :=
    dirichletDriftSubPotentialOnIcc_eq q Y a ht₀
  rw [ht, ← hV₀t]
  simp only [map_add, add_apply]
  rw [hbase, hprincipal, hA₁t, hlower]
  rfl

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
