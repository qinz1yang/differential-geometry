import DifferentialGeometry.Analysis.Parabolic.Dirichlet.InteriorRegularity
noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped ContDiff ENNReal Manifold NNReal Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Laplacian
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure

private theorem norm_uncurry_compLpL_le
    {Z Y X : Type*} [MeasurableSpace Z] [MeasurableSpace Y]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    {μ : Measure Z} {ν : Measure Y} [SFinite ν] (A : X →L[ℝ] Lp ℝ 2 ν) (u : Lp X 2 μ) :
    ‖Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (A.compLpL 2 μ u)‖ ≤ ‖A‖ * ‖u‖ := by
  rw [LinearIsometry.norm_map]
  exact ((A.compLpL 2 μ).le_opNorm u).trans
    (mul_le_mul_of_nonneg_right (ContinuousLinearMap.norm_compLpL_le A) (norm_nonneg _))

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

local notation "I_hs" => modelWithCornersEuclideanHalfSpace n

private theorem exists_ae_hasWeakPartialDeriv_localWeakPartial_norm_le_of_diffQuot
    {q : SmoothRiemannianMetric I_hs M} {T t₀ t₁ : ℝ}
    (u : timeL2 (H1ComplDirichlet q) T)
    (α : M) {Ω : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuclideanSpace ℝ (Fin n)) '' interior (extChartAt I_hs α).target)
    {η : EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    {δ C : ℝ} (hδ : 0 < δ) (hroom : Metric.cthickening δ (tsupport η) ⊆ Ω)
    (hbound : ∀ (k : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) (h : ℝ), |h| ≤ δ →
      (∫ t in Icc t₀ t₁, (∑ i, ∫ z, (η z * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) z) ^ 2) ∂timeMeasure T) ≤
        C * ∫ t, ‖u t‖ ^ 2 ∂timeMeasure T)
    {Ω₀ : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ₀ : IsOpen Ω₀) (hηone : ∀ z ∈ Ω₀, η z = 1) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ i k : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))),
      ∃ v : Lp ℝ 2 (((timeMeasure T).restrict (Icc t₀ t₁)).prod (volume.restrict Ω₀)),
        ‖v‖ ≤ Real.sqrt (C * ∫ t, ‖u t‖ ^ 2 ∂timeMeasure T) +
          L * ‖dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i‖ * ‖u‖ ∧
        ∀ᵐ t ∂(timeMeasure T).restrict (Icc t₀ t₁), DeGiorgi.HasWeakPartialDeriv k
          (fun z => v (t, z)) (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀ := by
  let μ := (timeMeasure T).restrict (Icc t₀ t₁)
  have huμ : MemLp u 2 μ := (Lp.memLp u).mono_measure Measure.restrict_le_self
  let uμ : Lp (H1ComplDirichlet q) 2 μ := huμ.toLp u
  have huμeq : uμ =ᵐ[μ] u := huμ.coeFn_toLp
  obtain ⟨L, hL, hinverse⟩ :=
    DifferentialGeometry.Analysis.Sobolev.exists_ae_hasWeakPartialDeriv_of_integral_sq_diffQuot_cutoff_le
      (μ := μ) (hη.of_le (by simp)) hηc
  refine ⟨L, hL, ?_⟩
  intro i k
  let A := dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i
  let w := dirichletLocalSpacetimeWeakPartialLp q α hΩ hΩc hΩs μ i uμ
  have hw : MemLp w 2 (μ.prod (volume.restrict Ω)) := Lp.memLp w
  have hnorm : ∀ h : ℝ, 0 < |h| → |h| ≤ δ →
      (∫ t, (∫ z, (η z * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (fun y => w (t, y)) z) ^ 2) ∂μ) ≤ C * ∫ t, ‖u t‖ ^ 2 ∂timeMeasure T := by
    intro h hhpos hh
    have hroomh : Metric.cthickening |h| (tsupport η) ⊆ Ω :=
      (Metric.cthickening_mono hh _).trans hroom
    have heq := DifferentialGeometry.Analysis.Sobolev.integral_sq_cutoff_diffQuot_uncurry_compLpL
      hΩ.measurableSet A uμ η k h hroomh
    change (∫ t, (∫ z, (η z * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
      (fun y => Lp.uncurry ℝ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤) (A.compLpL 2 μ uμ) (t, y)) z) ^ 2) ∂μ) ≤ _
    rw [heq]
    have hcoe : (∫ t, (∫ z, (η z * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (A (uμ t)) z) ^ 2) ∂μ) =
        ∫ t, (∫ z, (η z * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (A (u t)) z) ^ 2) ∂μ := by
      apply integral_congr_ae
      filter_upwards [huμeq] with t ht
      rw [ht]
    rw [hcoe]
    have hηLp : MemLp η ∞ volume := hη.continuous.memLp_of_hasCompactSupport hηc
    have hI (j) : Integrable (fun t => ∫ z, (η z * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j (u t)) z) ^ 2) μ :=
      DifferentialGeometry.Analysis.Sobolev.integrable_integral_sq_cutoff_diffQuot_comp
        hΩ.measurableSet hηLp k h hroomh
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j) huμ
    have hmono : (∫ t, (∫ z, (η z * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (A (u t)) z) ^ 2) ∂μ) ≤ ∫ t, (∑ j, ∫ z,
          (η z * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
            (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j (u t)) z) ^ 2) ∂μ := by
      apply integral_mono (hI i) (integrable_finsetSum _ fun j _ => hI j)
      intro t
      dsimp only
      let f := fun j => ∫ z, (η z * DifferentialGeometry.Analysis.Sobolev.diffQuot k h
        (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs j (u t)) z) ^ 2
      have hf : ∀ j ∈ Finset.univ, 0 ≤ f j := fun _ _ => integral_nonneg fun z => sq_nonneg _
      exact Finset.single_le_sum (s := Finset.univ) hf (Finset.mem_univ i)
    exact hmono.trans (hbound k h hh)
  obtain ⟨v, hv, hvweak⟩ := hinverse hΩ.measurableSet hΩ₀ hηone hw k
    hδ hroom hnorm
  have hunorm : ‖uμ‖ ≤ ‖u‖ := by
    rw [Lp.norm_toLp, Lp.norm_def]
    exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top _) (eLpNorm_mono_measure _ Measure.restrict_le_self)
  have hwnorm : ‖w‖ ≤ ‖A‖ * ‖u‖ :=
    (norm_uncurry_compLpL_le A uμ).trans (mul_le_mul_of_nonneg_left hunorm (norm_nonneg _))
  refine ⟨v, ?_, ?_⟩
  · apply hv.trans
    change Real.sqrt _ + L * ‖w‖ ≤ _
    exact add_le_add_right (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hwnorm hL) _
  filter_upwards [hvweak, dirichletLocalSpacetimeWeakPartialLp_coeFn q α hΩ hΩc hΩs μ i uμ,
    huμeq] with t ht hwt hut
  have hΩ₀Ω : Ω₀ ⊆ Ω := by
    intro z hz
    apply hroom
    exact Metric.self_subset_cthickening _ (subset_tsupport η (by change η z ≠ 0; rw [hηone z hz]; norm_num))
  have hsource : (fun z => w (t, z)) =ᵐ[volume.restrict Ω₀]
      (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t) : _ → ℝ) := by
    have hm := hwt.filter_mono (ae_mono (Measure.restrict_mono hΩ₀Ω le_rfl))
    simpa only [hut] using hm
  intro ψ hψ hψc hψs
  have he := ht ψ hψ hψc hψs
  have heq : (∫ z in Ω₀, w (t, z) * fderiv ℝ ψ z (EuclideanSpace.single k 1)) =
      ∫ z in Ω₀, dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t) z *
        fderiv ℝ ψ z (EuclideanSpace.single k 1) := by
    apply integral_congr_ae
    filter_upwards [hsource] with z hz
    rw [hz]
  exact heq.symm.trans he

theorem IsWeakEvolutionSolution.exists_ae_hasWeakPartialDeriv_localWeakPartial_norm_le
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
    {hX : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx}
    {htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_hs) G.metric t x| ≤ Bv}
    {f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_hs) (M := M) q)}
    {u : timeL2 (H1ComplDirichlet q) T}
    (α : M) {Ω Ω' Ω'' : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ : IsOpen Ω) (hΩc : IsCompact (closure Ω))
    (hΩs : closure Ω ⊆ toEuclidean (E := EuclideanSpace ℝ (Fin n)) '' interior (extChartAt I_hs α).target)
    (hΩ' : IsOpen Ω') (hΩ'' : IsOpen Ω'')
    (hΩ'c : IsCompact (closure Ω')) (hΩ'Ω : closure Ω' ⊆ Ω)
    (hΩ''c : IsCompact (closure Ω''))
    {η : EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Ω'') {r : ℝ} (hr : 0 < r)
    (hroom : Metric.cthickening r (closure Ω'') ⊆ Ω')
    (φ : C^∞⟮I_hs, M; ℝ⟯)
    (hφ : ∀ z ∈ Ω, chartDensity (I := I_hs) q α
      ((extChartAt I_hs α).symm ((toEuclidean (E := EuclideanSpace ℝ (Fin n))).symm z)) *
        φ ((extChartAt I_hs α).symm ((toEuclidean (E := EuclideanSpace ℝ (Fin n))).symm z)) = 1)
    (hu : IsWeakEvolutionSolution hG hT hreg X a Bx Bv
      (fun t ht => hX t ⟨ht.1, ht.2.le⟩) htrace f₀ u)
    (hXsmooth : ContMDiffOn (𝓘(ℝ, ℝ).prod I_hs) ((I_hs).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) ∞
      (fun p : ℝ × M => Bundle.TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2))
      (D.regular ×ˢ (trivializationAt (EuclideanSpace ℝ (Fin n)) (TangentSpace I_hs) α).baseSet))
    (hηb : ∀ z, |η z| ≤ 1)
    {lam : ℝ} (hlam : 0 < lam)
    (hcoer : ∀ t ∈ Icc (0 : ℝ) T, ∀ y ∈ Ω,
      ∀ ξ : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) → ℝ,
      lam * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j,
        DifferentialGeometry.Analysis.Laplacian.MetricExtension.invGramOnEuclid (I := I_hs)
          (G.metric t) α i j y * ξ i * ξ j)
    {t₀ t₁ : ℝ} (ht₀ : 0 < t₀) (ht₁ : t₁ < T)
    {Ω₀ : Set (EuclideanSpace ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))))}
    (hΩ₀ : IsOpen Ω₀) (hηone : ∀ z ∈ Ω₀, η z = 1) :
    ∃ C L : ℝ, 0 ≤ C ∧ 0 ≤ L ∧ ∀ i k : Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))),
      ∃ v : Lp ℝ 2 (((timeMeasure T).restrict (Icc t₀ t₁)).prod (volume.restrict Ω₀)),
        ‖v‖ ≤ Real.sqrt (C * ∫ t, ‖u t‖ ^ 2 ∂timeMeasure T) +
          L * ‖dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i‖ * ‖u‖ ∧
        ∀ᵐ t ∂(timeMeasure T).restrict (Icc t₀ t₁), DeGiorgi.HasWeakPartialDeriv k
          (fun z => v (t, z)) (dirichletLocalWeakPartialLp q α hΩ hΩc hΩs i (u t)) Ω₀ := by
  obtain ⟨δ, hδ, C, hC, hbound⟩ :=
    hu.exists_integral_Icc_diffQuot_weakPartial_le hXcont hacont α hΩ hΩc hΩs
      hΩ' hΩ'' hΩ'c hΩ'Ω hΩ''c hη hηc hηs hr hroom φ hφ hXsmooth hηb hlam hcoer ht₀ ht₁
  have hroom' : Metric.cthickening (min δ r) (tsupport η) ⊆ Ω :=
    (Metric.cthickening_mono (min_le_right δ r) _).trans
      ((Metric.cthickening_subset_of_subset r (hηs.trans subset_closure)).trans
        (hroom.trans (subset_closure.trans hΩ'Ω)))
  obtain ⟨L, hL, hsecond⟩ := exists_ae_hasWeakPartialDeriv_localWeakPartial_norm_le_of_diffQuot
    u α hΩ hΩc hΩs hη hηc (lt_min hδ hr) hroom'
    (fun k h hh => hbound k h (hh.trans (min_le_left _ _))) hΩ₀ hηone
  exact ⟨C, L, hC, hL, hsecond⟩

end DifferentialGeometry.Analysis.Parabolic.Dirichlet
