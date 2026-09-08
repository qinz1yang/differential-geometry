import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.Uhlenbeck.GaugeCovariance
import DifferentialGeometry.Geometry.Connection.LeviCivita.Pullback
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.ExteriorConjugation
import DifferentialGeometry.Geometry.Curvature.AlgebraicTensorMetric
import DifferentialGeometry.Geometry.Metric.BundlePullbackSmooth

set_option autoImplicit false

noncomputable section

open Bundle CovariantDerivative
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open scoped Bundle Manifold ContDiff RealInnerProductSpace

namespace DifferentialGeometry.PDE.RicciFlow

section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [BoundarylessManifold I M]
  {F G : Type*} [normF : NormedAddCommGroup F] [spaceF : NormedSpace ℝ F]
  [FiniteDimensional ℝ F] [normG : NormedAddCommGroup G] [spaceG : NormedSpace ℝ G]
  [FiniteDimensional ℝ G]

variable {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
  [∀ x, NormedAddCommGroup (W x)] [∀ x, NormedSpace ℝ (W x)]
  [FiberBundle G W] [VectorBundle ℝ G W] [ContMDiffVectorBundle ∞ G W I]

private def fixedMetricCurvatureOperatorGauge
    (g : SmoothRiemannianMetric I M)
    (h : ContMDiffRiemannianMetric I ∞ F V) (k : ContMDiffRiemannianMetric I ∞ G W)
    (ι : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (κ : ∀ x, W x ≃L[ℝ] TangentSpace I x)
    (U : ∀ x, W x ≃L[ℝ] V x)
    (hU : ∀ x v w, h.inner x (U x v) (U x w) = k.inner x v w) : Prop :=
  let φ := h.toRiemannianMetric.toLinearIsometryEquiv k.toRiemannianMetric id U hU
  letI : RiemannianBundle V := ⟨h.toRiemannianMetric⟩
  letI vNorm : ∀ x, NormedAddCommGroup (V x) := fun x =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal x
  letI : ∀ x, SeminormedAddCommGroup (V x) := fun x => (vNorm x).toSeminormedAddCommGroup
  letI : ∀ x, InnerProductSpace ℝ (V x) := fun x => Bundle.instInnerProductSpaceReal x
  letI : IsContMDiffRiemannianBundle I ∞ F V := ⟨h.inner, h.contMDiff, fun _ _ _ => rfl⟩
  letI : RiemannianBundle W := ⟨k.toRiemannianMetric⟩
  letI wNorm : ∀ x, NormedAddCommGroup (W x) := fun x =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal x
  letI : ∀ x, SeminormedAddCommGroup (W x) := fun x => (wNorm x).toSeminormedAddCommGroup
  letI : ∀ x, InnerProductSpace ℝ (W x) := fun x => Bundle.instInnerProductSpaceReal x
  letI : IsContMDiffRiemannianBundle I ∞ G W := ⟨k.inner, k.contMDiff, fun _ _ _ => rfl⟩
  letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  letI : ∀ x, FiniteDimensional ℝ (W x) := fun x => VectorBundle.finiteDimensional ℝ G W x
  ∀ x,
    let T := metricRm04At g x
    let hT := mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule g x)
    exteriorPower.traceNormalizedCurvatureEndomorphism
        (T.compContinuousLinearMap (fun _ => (κ x).toContinuousLinearMap))
        (hT.compContinuousLinearMap (κ x).toContinuousLinearMap) =
      (exteriorPower.mapLinearIsometryEquiv 2 (φ x)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((exteriorPower.traceNormalizedCurvatureEndomorphism
          (T.compContinuousLinearMap (fun _ => (ι x).toContinuousLinearMap))
          (hT.compContinuousLinearMap (ι x).toContinuousLinearMap)).comp
          (exteriorPower.mapLinearIsometryEquiv 2 (φ x)).toContinuousLinearEquiv.toContinuousLinearMap)

omit [BoundarylessManifold I M] [ContMDiffVectorBundle ∞ F V I]
  [ContMDiffVectorBundle ∞ G W I] in
private theorem fixedMetricCurvatureOperatorGauge_of_eq
    (g : SmoothRiemannianMetric I M)
    (h : ContMDiffRiemannianMetric I ∞ F V) (k : ContMDiffRiemannianMetric I ∞ G W)
    (ι : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (κ : ∀ x, W x ≃L[ℝ] TangentSpace I x)
    (U : ∀ x, W x ≃L[ℝ] V x)
    (hU : ∀ x v w, h.inner x (U x v) (U x w) = k.inner x v w)
    (heq : ∀ x, κ x = (U x).trans (ι x)) :
    fixedMetricCurvatureOperatorGauge (F := F) (G := G) g h k ι κ U hU := by
  let φ := h.toRiemannianMetric.toLinearIsometryEquiv k.toRiemannianMetric id U hU
  let : RiemannianBundle V := ⟨h.toRiemannianMetric⟩
  let vNorm : ∀ x, NormedAddCommGroup (V x) := fun x =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal x
  let : ∀ x, SeminormedAddCommGroup (V x) := fun x => (vNorm x).toSeminormedAddCommGroup
  let : ∀ x, InnerProductSpace ℝ (V x) := fun x => Bundle.instInnerProductSpaceReal x
  let : IsContMDiffRiemannianBundle I ∞ F V := ⟨h.inner, h.contMDiff, fun _ _ _ => rfl⟩
  let : RiemannianBundle W := ⟨k.toRiemannianMetric⟩
  let wNorm : ∀ x, NormedAddCommGroup (W x) := fun x =>
    Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal x
  let : ∀ x, SeminormedAddCommGroup (W x) := fun x => (wNorm x).toSeminormedAddCommGroup
  let : ∀ x, InnerProductSpace ℝ (W x) := fun x => Bundle.instInnerProductSpaceReal x
  let : IsContMDiffRiemannianBundle I ∞ G W := ⟨k.inner, k.contMDiff, fun _ _ _ => rfl⟩
  let : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x
  let : ∀ x, FiniteDimensional ℝ (W x) := fun x => VectorBundle.finiteDimensional ℝ G W x
  intro x
  exact exteriorPower.traceNormalizedCurvatureEndomorphism_pullback_conjugate
    (metricRm04At g x) (mem_algebraicCurvatureTensorSubmodule.mp
      (metricRm04At_mem_algebraicCurvatureTensorSubmodule g x))
    (ι x) (κ x) (φ x) (heq x)

end

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  {F G : Type*} [normF : NormedAddCommGroup F] [spaceF : NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [normG : NormedAddCommGroup G] [spaceG : NormedSpace ℝ G] [FiniteDimensional ℝ G]
  {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, NormedAddCommGroup (V x)] [∀ x, NormedSpace ℝ (V x)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  {W : M → Type*} [TopologicalSpace (TotalSpace G W)]
  [∀ x, NormedAddCommGroup (W x)] [∀ x, NormedSpace ℝ (W x)]
  [FiberBundle G W] [VectorBundle ℝ G W] [ContMDiffVectorBundle ∞ G W I]

omit [ContMDiffVectorBundle ∞ F V I] [ContMDiffVectorBundle ∞ G W I] in
private theorem exists_uhlenbeck_isometries_gauge
    {J : Set ℝ} {t₀ : ℝ} (hJ : J.OrdConnected) (ht₀ : t₀ ∈ J)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (J ×ˢ (Set.univ : Set M)))
    (hflow : ∀ t ∈ J, ∀ x (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g s).inner x v w)
        (-2 * ricciTensor (I := I) (g t) x v w) J t)
    (h : RiemannianMetric V) (k : RiemannianMetric W)
    (ι₀ : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (κ₀ : ∀ x, W x ≃L[ℝ] TangentSpace I x)
    (hι₀ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι₀ x).toContinuousLinearMap))
    (hκ₀ : ContMDiff I (I.prod 𝓘(ℝ, G →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (G →L[ℝ] E) x (κ₀ x).toContinuousLinearMap))
    (h₀ : ∀ x v w, (g t₀).inner x (ι₀ x v) (ι₀ x w) = h.inner x v w)
    (k₀ : ∀ x v w, (g t₀).inner x (κ₀ x v) (κ₀ x w) = k.inner x v w) :
  let U := fun x => (κ₀ x).trans (ι₀ x).symm
  ∃ (h' : ContMDiffRiemannianMetric I ∞ F V)
    (k' : ContMDiffRiemannianMetric I ∞ G W)
    (ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (κ : ℝ → ∀ x, W x ≃L[ℝ] TangentSpace I x),
    h'.toRiemannianMetric = h ∧ k'.toRiemannianMetric = k ∧
    (∀ x, ι t₀ x = ι₀ x) ∧ (∀ x, κ t₀ x = κ₀ x) ∧
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (F →L[ℝ] E) p.2
        (E := fun x => V x →L[ℝ] TangentSpace I x)
        (ι p.1 p.2).toContinuousLinearMap) (J ×ˢ (Set.univ : Set M)) ∧
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] F) p.2
        (E := fun x => TangentSpace I x →L[ℝ] V x)
        (ι p.1 p.2).symm.toContinuousLinearMap) (J ×ˢ (Set.univ : Set M)) ∧
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, G →L[ℝ] E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (G →L[ℝ] E) p.2
        (E := fun x => W x →L[ℝ] TangentSpace I x)
        (κ p.1 p.2).toContinuousLinearMap) (J ×ˢ (Set.univ : Set M)) ∧
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] G)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] G) p.2
        (E := fun x => TangentSpace I x →L[ℝ] W x)
        (κ p.1 p.2).symm.toContinuousLinearMap) (J ×ˢ (Set.univ : Set M)) ∧
    (∀ x v, ∀ t ∈ J, HasDerivWithinAt (fun s => ι s x v)
      (ricciSharp (I := I) (g t) x (ι t x v)) J t) ∧
    (∀ x v, ∀ t ∈ J, HasDerivWithinAt (fun s => κ s x v)
      (ricciSharp (I := I) (g t) x (κ t x v)) J t) ∧
    (∀ t ∈ J, ∀ x v w, (g t).inner x (ι t x v) (ι t x w) = h.inner x v w) ∧
    (∀ t ∈ J, ∀ x v w, (g t).inner x (κ t x v) (κ t x w) = k.inner x v w) ∧
    (∀ x v w, h.inner x (U x v) (U x w) = k.inner x v w) ∧
      ∃ (hUsmooth : ContMDiff I (I.prod 𝓘(ℝ, G →L[ℝ] F)) ∞
        (fun x => TotalSpace.mk' (G →L[ℝ] F) x (U x).toContinuousLinearMap)),
      ∀ t ∈ J,
        (∀ x, κ t x = (U x).trans (ι t x)) ∧
        ∃ (hιslice : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
            (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι t x).toContinuousLinearMap))
          (hκslice : ContMDiff I (I.prod 𝓘(ℝ, G →L[ℝ] E)) ∞
            (fun x => TotalSpace.mk' (G →L[ℝ] E) x (κ t x).toContinuousLinearMap)),
          pullbackFiberwiseLinearEquiv (fun x => (κ t x).toLinearEquiv)
            (hκslice.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)).clm_bundle_map (LeviCivita (g t)) =
          pullbackFiberwiseLinearEquiv (fun x => (U x).toLinearEquiv)
            (hUsmooth.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)).clm_bundle_map
            (pullbackFiberwiseLinearEquiv (fun x => (ι t x).toLinearEquiv)
              (hιslice.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)).clm_bundle_map (LeviCivita (g t))) ∧
        ∃ (hUmetric' : ∀ x v w, h'.inner x (U x v) (U x w) = k'.inner x v w),
          fixedMetricCurvatureOperatorGauge (F := F) (G := G) (g t) h' k' (ι t) (κ t) U hUmetric'  := by
  let U := fun x => (κ₀ x).trans (ι₀ x).symm
  let h' := (g t₀).pullbackFiberwiseContinuousLinearEquiv ι₀ hι₀
  let k' := (g t₀).pullbackFiberwiseContinuousLinearEquiv κ₀ hκ₀
  have hh' : h'.toRiemannianMetric = h := by
    apply RiemannianMetric.ext
    exact h₀
  have hk' : k'.toRiemannianMetric = k := by
    apply RiemannianMetric.ext
    exact k₀
  obtain ⟨ι, hιinit, hιsmooth, hιinverse, hιderiv, hιmetric⟩ :=
    exists_uhlenbeck_isometry_on_interval_of_hasDerivWithinAt
      hJ ht₀ g hg hflow h ι₀ hι₀ h₀
  obtain ⟨κ, hκinit, hκsmooth, hκinverse, hκderiv, hκmetric⟩ :=
    exists_uhlenbeck_isometry_on_interval_of_hasDerivWithinAt
      hJ ht₀ g hg hflow k κ₀ hκ₀ k₀
  refine ⟨h', k', ι, κ, hh', hk', hιinit, hκinit, hιsmooth, hιinverse, hκsmooth, hκinverse,
    hιderiv, hκderiv, hιmetric, hκmetric, ?_⟩
  have hU : ∀ x v w, h.inner x (U x v) (U x w) = k.inner x v w := by
    intro x v w
    rw [← h₀]
    simpa only [U, ContinuousLinearEquiv.trans_apply,
      ContinuousLinearEquiv.apply_symm_apply] using k₀ x v w
  have hcompat := ricci_ode_equiv_eq_comp_initial
    hJ ht₀ g hflow ι κ hιderiv hκderiv
  have heq : ∀ t ∈ J, ∀ x, κ t x = (U x).trans (ι t x) := by
    intro t ht x
    simpa only [hιinit, hκinit] using hcompat t ht x
  have hpair (t : ℝ) : ContMDiff I (𝓘(ℝ, ℝ).prod I) ∞ (fun x : M => (t, x)) :=
    contMDiff_const.prodMk contMDiff_id
  have hiInv0 := hιinverse.comp_contMDiff (hpair t₀) (fun x => ⟨ht₀, Set.mem_univ x⟩)
  have hk0 := hκsmooth.comp_contMDiff (hpair t₀) (fun x => ⟨ht₀, Set.mem_univ x⟩)
  have hUsmooth : ContMDiff I (I.prod 𝓘(ℝ, G →L[ℝ] F)) ∞
      (fun x => TotalSpace.mk' (G →L[ℝ] F) x (U x).toContinuousLinearMap) := by
    have hc := hiInv0.clm_bundle_comp hk0
    apply hc.congr
    intro x
    simp only [hιinit, hκinit]
    rfl
  refine ⟨hU, hUsmooth, ?_⟩
  intro t ht
  refine ⟨heq t ht, ?_⟩
  have hUmetric' : ∀ x v w, h'.inner x (U x v) (U x w) = k'.inner x v w := by
    intro x v w
    exact (congrArg (fun m : RiemannianMetric V => m.inner x (U x v) (U x w)) hh').trans
      ((hU x v w).trans (congrArg (fun m : RiemannianMetric W => m.inner x v w) hk').symm)
  have hi := hιsmooth.comp_contMDiff (hpair t) (fun x => ⟨ht, Set.mem_univ x⟩)
  have hk := hκsmooth.comp_contMDiff (hpair t) (fun x => ⟨ht, Set.mem_univ x⟩)
  refine ⟨hi, hk, pullback_leviCivita_conjugate (g t) (ι t) (κ t) U
    (hi.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp))
    (hk.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp))
    (hUsmooth.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)) (heq t ht), ?_⟩
  exact ⟨hUmetric', fixedMetricCurvatureOperatorGauge_of_eq
    (g t) h' k' (ι t) (κ t) U hUmetric' (heq t ht)⟩

omit [ContMDiffVectorBundle ∞ F V I] [ContMDiffVectorBundle ∞ G W I] in
theorem exists_uhlenbeck_isometries_gauge_covariance
    {J : Set ℝ} {t₀ : ℝ} (hJ : J.OrdConnected) (ht₀ : t₀ ∈ J)
    (g : ℝ → SmoothRiemannianMetric I M)
    (hg : ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
      (fun p : ℝ × M => (⟨p.2, (g p.1).inner p.2⟩ : TotalSpace (E →L[ℝ] E →L[ℝ] ℝ)
        (fun x => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)))
      (J ×ˢ (Set.univ : Set M)))
    (hflow : ∀ t ∈ J, ∀ x (v w : TangentSpace I x),
      HasDerivWithinAt (fun s => (g s).inner x v w)
        (-2 * ricciTensor (I := I) (g t) x v w) J t)
    (h : RiemannianMetric V) (k : RiemannianMetric W)
    (ι₀ : ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (κ₀ : ∀ x, W x ≃L[ℝ] TangentSpace I x)
    (hι₀ : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι₀ x).toContinuousLinearMap))
    (hκ₀ : ContMDiff I (I.prod 𝓘(ℝ, G →L[ℝ] E)) ∞
      (fun x => TotalSpace.mk' (G →L[ℝ] E) x (κ₀ x).toContinuousLinearMap))
    (h₀ : ∀ x v w, (g t₀).inner x (ι₀ x v) (ι₀ x w) = h.inner x v w)
    (k₀ : ∀ x v w, (g t₀).inner x (κ₀ x v) (κ₀ x w) = k.inner x v w) :
  let U := fun x => (κ₀ x).trans (ι₀ x).symm
  ∃ (h' : ContMDiffRiemannianMetric I ∞ F V)
    (k' : ContMDiffRiemannianMetric I ∞ G W)
    (ι : ℝ → ∀ x, V x ≃L[ℝ] TangentSpace I x)
    (κ : ℝ → ∀ x, W x ≃L[ℝ] TangentSpace I x),
    h'.toRiemannianMetric = h ∧ k'.toRiemannianMetric = k ∧
    (∀ x, ι t₀ x = ι₀ x) ∧ (∀ x, κ t₀ x = κ₀ x) ∧
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (F →L[ℝ] E) p.2
        (E := fun x => V x →L[ℝ] TangentSpace I x)
        (ι p.1 p.2).toContinuousLinearMap) (J ×ˢ (Set.univ : Set M)) ∧
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] F)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] F) p.2
        (E := fun x => TangentSpace I x →L[ℝ] V x)
        (ι p.1 p.2).symm.toContinuousLinearMap) (J ×ˢ (Set.univ : Set M)) ∧
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, G →L[ℝ] E)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (G →L[ℝ] E) p.2
        (E := fun x => W x →L[ℝ] TangentSpace I x)
        (κ p.1 p.2).toContinuousLinearMap) (J ×ˢ (Set.univ : Set M)) ∧
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] G)) ∞
      (fun p : ℝ × M => TotalSpace.mk' (E →L[ℝ] G) p.2
        (E := fun x => TangentSpace I x →L[ℝ] W x)
        (κ p.1 p.2).symm.toContinuousLinearMap) (J ×ˢ (Set.univ : Set M)) ∧
    (∀ x v, ∀ t ∈ J, HasDerivWithinAt (fun s => ι s x v)
      (ricciSharp (I := I) (g t) x (ι t x v)) J t) ∧
    (∀ x v, ∀ t ∈ J, HasDerivWithinAt (fun s => κ s x v)
      (ricciSharp (I := I) (g t) x (κ t x v)) J t) ∧
    (∀ t ∈ J, ∀ x v w, (g t).inner x (ι t x v) (ι t x w) = h.inner x v w) ∧
    (∀ t ∈ J, ∀ x v w, (g t).inner x (κ t x v) (κ t x w) = k.inner x v w) ∧
    (∀ x v w, h.inner x (U x v) (U x w) = k.inner x v w) ∧
      ∃ (hUsmooth : ContMDiff I (I.prod 𝓘(ℝ, G →L[ℝ] F)) ∞
        (fun x => TotalSpace.mk' (G →L[ℝ] F) x (U x).toContinuousLinearMap)),
      ∀ t ∈ J,
        (∀ x, κ t x = (U x).trans (ι t x)) ∧
        ∃ (hιslice : ContMDiff I (I.prod 𝓘(ℝ, F →L[ℝ] E)) ∞
            (fun x => TotalSpace.mk' (F →L[ℝ] E) x (ι t x).toContinuousLinearMap))
          (hκslice : ContMDiff I (I.prod 𝓘(ℝ, G →L[ℝ] E)) ∞
            (fun x => TotalSpace.mk' (G →L[ℝ] E) x (κ t x).toContinuousLinearMap)),
          pullbackFiberwiseLinearEquiv (fun x => (κ t x).toLinearEquiv)
            (hκslice.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)).clm_bundle_map (LeviCivita (g t)) =
          pullbackFiberwiseLinearEquiv (fun x => (U x).toLinearEquiv)
            (hUsmooth.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)).clm_bundle_map
            (pullbackFiberwiseLinearEquiv (fun x => (ι t x).toLinearEquiv)
              (hιslice.of_le (show (1 : ℕ∞ω) ≤ ∞ from by simp)).clm_bundle_map (LeviCivita (g t))) ∧
        ∃ (hUmetric' : ∀ x v w, h'.inner x (U x v) (U x w) = k'.inner x v w),
          (let φ := h'.toRiemannianMetric.toLinearIsometryEquiv k'.toRiemannianMetric id U hUmetric';
            letI : RiemannianBundle V := ⟨h'.toRiemannianMetric⟩;
            letI vNorm : ∀ x, NormedAddCommGroup (V x) := fun x =>
              Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal x;
            letI : ∀ x, SeminormedAddCommGroup (V x) := fun x => (vNorm x).toSeminormedAddCommGroup;
            letI : ∀ x, InnerProductSpace ℝ (V x) := fun x => Bundle.instInnerProductSpaceReal x;
            letI : IsContMDiffRiemannianBundle I ∞ F V := ⟨h'.inner, h'.contMDiff, fun _ _ _ => rfl⟩;
            letI : RiemannianBundle W := ⟨k'.toRiemannianMetric⟩;
            letI wNorm : ∀ x, NormedAddCommGroup (W x) := fun x =>
              Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal x;
            letI : ∀ x, SeminormedAddCommGroup (W x) := fun x => (wNorm x).toSeminormedAddCommGroup;
            letI : ∀ x, InnerProductSpace ℝ (W x) := fun x => Bundle.instInnerProductSpaceReal x;
            letI : IsContMDiffRiemannianBundle I ∞ G W := ⟨k'.inner, k'.contMDiff, fun _ _ _ => rfl⟩;
            letI : ∀ x, FiniteDimensional ℝ (V x) := fun x => VectorBundle.finiteDimensional ℝ F V x;
            letI : ∀ x, FiniteDimensional ℝ (W x) := fun x => VectorBundle.finiteDimensional ℝ G W x;
            ∀ x,
              (let T := metricRm04At (g t) x;
                let hT := mem_algebraicCurvatureTensorSubmodule.mp
                  (metricRm04At_mem_algebraicCurvatureTensorSubmodule (g t) x);
                exteriorPower.traceNormalizedCurvatureEndomorphism
                    (T.compContinuousLinearMap (fun _ => (κ t x).toContinuousLinearMap))
                    (hT.compContinuousLinearMap (κ t x).toContinuousLinearMap) =
                  (exteriorPower.mapLinearIsometryEquiv 2 (φ x)).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
                    ((exteriorPower.traceNormalizedCurvatureEndomorphism
                      (T.compContinuousLinearMap (fun _ => (ι t x).toContinuousLinearMap))
                      (hT.compContinuousLinearMap (ι t x).toContinuousLinearMap)).comp
                      (exteriorPower.mapLinearIsometryEquiv 2 (φ x)).toContinuousLinearEquiv.toContinuousLinearMap))) := by
  exact exists_uhlenbeck_isometries_gauge hJ ht₀ g hg hflow h k ι₀ κ₀ hι₀ hκ₀ h₀ k₀

end DifferentialGeometry.PDE.RicciFlow
