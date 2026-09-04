import DifferentialGeometry.Geometry.Curvature.DimensionThree.RankTrichotomy
import DifferentialGeometry.Geometry.Curvature.DimensionThree.AlgebraicCurvatureOperatorMetric
import DifferentialGeometry.Geometry.Curvature.CoordRm04Bridge
import DifferentialGeometry.Geometry.Metric.UniversalCover.ParallelLineSplitting
import DifferentialGeometry.Geometry.Metric.UniversalCover.Curvature
import DifferentialGeometry.Geometry.Metric.UniversalCover.Flat
import DifferentialGeometry.Geometry.Metric.Product
import DifferentialGeometry.Geometry.Metric.CompactPerturbationComplete
import DifferentialGeometry.Geometry.Metric.PullbackCross
import DifferentialGeometry.Geometry.Metric.Convergence.PullbackCross

set_option autoImplicit false

noncomputable section

open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

variable {H : Type} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ
  (DifferentialGeometry.Topology.Morse.MorseModel 3) H}
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M]
variable [I.Boundaryless] [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M]
variable [SigmaCompactSpace M] [ConnectedSpace M] [Nonempty M]

noncomputable local instance completeTrichotomyTwoFormFiniteDimensional
    (x : M) :
    FiniteDimensional Real (TangentSpace I x [⋀^Fin 2]→L[Real] Real) :=
    (ContinuousAlternatingMap.elementaryCovectorBasis (k := 2)
    (Module.finBasis Real (TangentSpace I x))).finiteDimensional_of_finite

omit [SigmaCompactSpace M] [ConnectedSpace M] [Nonempty M] in
private theorem riemannOp_eq_zero_of_curvatureOperatorEndomorphismAt_eq_zero
    (g : SmoothRiemannianMetric I M) (x : M)
    (hzero : curvatureOperatorEndomorphismAt (I := I) g x
      ⟨metricRm04 (I := I) g x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩ = 0) :
    ∀ X Y Z : TangentSpace I x,
      riemannOp (LeviCivita (I := I) g) x X Y Z = 0 := by
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt (I := I) g x
    (by
      exact (show Module.finrank Real (TangentSpace I x) =
        Module.finrank Real
          (DifferentialGeometry.Topology.Morse.MorseModel 3) from rfl).trans
        (by simp [DifferentialGeometry.Topology.Morse.MorseModel]))
  have hAzero :
      (⟨metricRm04 (I := I) g x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩ :
        algebraicCurvatureTensorSubmodule (I := I) (M := M) x) = 0 := by
    apply curvatureOperatorMatrixAt_eq_zero_of_orthonormal
      (I := I) g x basis horth
    ext i j
    have hpair : curvatureOperatorPairingAt (I := I) g x
        ⟨metricRm04 (I := I) g x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩
        (curvatureTwoFormBasisAt (I := I) basis i)
        (curvatureTwoFormBasisAt (I := I) basis j) = 0 := by
      rw [← twoFormMetricData_inner_curvatureOperatorEndomorphismAt, hzero]
      simp
    rw [curvatureOperatorPairingAt_curvatureTwoFormBasisAt
      (I := I) g x basis horth] at hpair
    change 2 * curvatureOperatorMatrixAt (I := I) x basis
      ⟨metricRm04 (I := I) g x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩ i j = 0 at hpair
    have hij : curvatureOperatorMatrixAt (I := I) x basis
        ⟨metricRm04 (I := I) g x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩ i j = 0 := by
      linarith
    simpa using hij
  have hRmzero : metricRm04 (I := I) g x = 0 :=
    congrArg Subtype.val hAzero
  intro X Y Z
  let R := riemannOp (LeviCivita (I := I) g) x X Y Z
  have hinner : g.inner x R R = 0 := by
    rw [← DifferentialGeometry.rm04_eq_inner_riem (I := I) g x X Y Z R]
    have happly := congrArg
      (fun A : Tensor04At (I := I) (M := M) x => A (vec4 X Y Z R)) hRmzero
    simpa using happly
  by_contra hR
  exact (ne_of_gt (g.pos x R hR)) hinner

omit [I.Boundaryless] [SigmaCompactSpace M] [ConnectedSpace M] [Nonempty M] in
theorem metricScalarAt_pos_of_curvatureOperator_rank_one
    (hE : Module.finrank Real
      (DifferentialGeometry.Topology.Morse.MorseModel 3) = 3)
    (g : SmoothRiemannianMetric I M) (x : M)
    (hpositive : ∀ a : TangentSpace I x [⋀^Fin 2]→L[Real] Real,
      0 ≤ (twoFormMetricData (I := I) g x).inner
        (curvatureOperatorEndomorphismAt (I := I) g x
          ⟨metricRm04 (I := I) g x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩ a) a)
    (hrank : Module.finrank Real
        (curvatureOperatorImageAt (I := I) g x
          ⟨metricRm04 (I := I) g x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩) = 1) :
    0 < metricScalarAt (I := I) g x := by
  have hTangentDim : Module.finrank Real (TangentSpace I x) = 3 := by
    exact (show Module.finrank Real (TangentSpace I x) =
      Module.finrank Real (DifferentialGeometry.Topology.Morse.MorseModel 3) from rfl).trans hE
  obtain ⟨basis, horth⟩ :=
    exists_orthonormalBasisAt (I := I) g x hTangentDim
  let A := curvatureOperatorEndomorphismAt (I := I) g x
      ⟨metricRm04 (I := I) g x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩
  let b := curvatureTwoFormBasisAt (I := I) basis
  let R := traceNormalizedMetricCurvatureOperatorMatrixAt (I := I) g x basis
  have hpair : ∀ i j : Fin 3,
      R i j = (twoFormMetricData (I := I) g x).inner (A (b i)) (b j) := by
    intro i j
    rw [twoFormMetricData_inner_curvatureOperatorEndomorphismAt]
    exact (curvatureOperatorPairingAt_curvatureTwoFormBasisAt
      (I := I) g x basis horth _ i j).symm
  have hRpos : R.PosSemidef := by
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · have hherm := curvatureOperatorMatrixAt_isHermitian (I := I) x basis
        (metricAlgebraicCurvatureTensorAt (I := I) g x)
      simpa [R, traceNormalizedMetricCurvatureOperatorMatrixAt,
        traceNormalizedCurvatureOperatorMatrixAt,
        traceNormalizedCurvatureOperatorMatrix3, Matrix.IsHermitian] using
        hherm.smul (by norm_num : IsSelfAdjoint (2 : Real))
    · intro v
      let a := ∑ i : Fin 3, v i • b i
      have ha := hpositive a
      have hsym : ∀ i j : Fin 3,
          (twoFormMetricData (I := I) g x).flat (A (b i)) (b j) =
            (twoFormMetricData (I := I) g x).flat (A (b j)) (b i) := by
        intro i j
        change (twoFormMetricData (I := I) g x).inner (A (b i)) (b j) =
          (twoFormMetricData (I := I) g x).inner (A (b j)) (b i)
        calc
          (twoFormMetricData (I := I) g x).inner (A (b i)) (b j) =
              (twoFormMetricData (I := I) g x).inner (b i) (A (b j)) :=
            curvatureOperatorEndomorphismAt_isSymmetric (I := I) g x _ (b i) (b j)
          _ = (twoFormMetricData (I := I) g x).inner (A (b j)) (b i) :=
            (twoFormMetricData (I := I) g x).inner_comm _ _
      have hquad : dotProduct (star v) (Matrix.mulVec R v) =
          (twoFormMetricData (I := I) g x).inner (A a) a := by
        simp only [dotProduct, Matrix.mulVec, star_trivial, MetricFiberData.inner_apply,
          a, Finset.mul_sum, hpair]
        simp only [map_sum, map_smul, smul_eq_mul, LinearMap.sum_apply,
          LinearMap.smul_apply]
        apply Finset.sum_congr rfl
        intro i _
        rw [← Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro j _
        rw [hsym]
        ring
      rw [hquad]
      exact ha
  have hRne : R ≠ 0 := by
    intro hzero
    have hAzero : A = 0 := by
      apply ContinuousLinearMap.ext
      intro a
      rw [← b.sum_repr a]
      simp only [map_sum, map_smul]
      have hbi : ∀ i : Fin 3, A (b i) = 0 := by
        intro i
        have hk : b i ∈ curvatureOperatorKernelAt (I := I) g x
            ⟨metricRm04 (I := I) g x,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩ := by
          rw [curvatureTwoFormBasisAt_mem_curvatureOperatorKernelAt_iff
            (I := I) g x basis horth _ i]
          intro j
          change R i j = 0
          exact congrFun (congrFun hzero i) j
        apply LinearMap.mem_ker.mp
        change b i ∈
          (curvatureOperatorEndomorphismAt (I := I) g x
            ⟨metricRm04 (I := I) g x,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩).toLinearMap.ker
        rw [curvatureOperatorEndomorphismAt_ker]
        exact hk
      simp [hbi]
    have hrank' := hrank
    change Module.finrank Real A.toLinearMap.range = 1 at hrank'
    have hzeroRank : Module.finrank Real A.toLinearMap.range = 0 := by
      rw [hAzero]
      simp
    linarith
  have htrace : 0 < R.trace := by
    have hnonneg : 0 ≤ R.trace := hRpos.trace_nonneg
    have hne : R.trace ≠ 0 := by
      intro hz
      exact hRne (hRpos.trace_eq_zero_iff.mp hz)
    exact lt_of_le_of_ne' hnonneg hne
  have hscalar : R.trace = metricScalarAt (I := I) g x :=
    traceNormalizedMetricCurvatureOperatorMatrixAt_trace_eq_metricScalarAt
      (I := I) g x basis horth
  rw [← hscalar]
  exact htrace

def HasCurvatureSurfaceProductSplitting
    (g : SmoothRiemannianMetric I M) : Prop :=
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M :=
    DifferentialGeometry.Geometry.Riemannian.Topology.manifold_semilocallySimplyConnectedSpace
      (I := I)
  let _ : Inhabited M := ⟨Classical.choice (inferInstance : Nonempty M)⟩
  ∃ (S : ContMDiffVectorSubbundle
      (I := I) (F := DifferentialGeometry.Topology.Morse.MorseModel 3)
      (V := TangentSpace I) (n := (∞ : WithTop ℕ∞)))
    (P : GlobalSurfaceProductSplitting (I := I) (M := M) g),
    let _ : TopologicalSpace P.N := P.topologyN
    let _ : ChartedSpace (DifferentialGeometry.Topology.Morse.MorseModel 2) P.N := P.chartedN
    let _ : IsManifold (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2))
        (↑(⊤ : ℕ∞) : WithTop ℕ∞) P.N := P.manifoldN
    let _ : T2Space P.N := P.t2N
    let _ : SigmaCompactSpace P.N := P.sigmaN
    And (S.rank = 1)
      (And
        (∀ x, S.fiber x = curvatureOperatorImageAnnihilatorAt (I := I) g x
          ⟨metricRm04 (I := I) g x,
            metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩)
        (And
          (∀ y : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M,
            P.line.fiber y =
              (liftTangentSubbundle (I := I) (M := M) S).fiber y)
          (∀ y : P.N,
            0 < metricScalarAt
              (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2))
              P.metricN y)))

omit [Nonempty M] in
theorem _root_.DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.GlobalSurfaceProductSplitting.pullbackMetric_eq_prod
    {H : Type} [TopologicalSpace H]
    {I : ModelWithCorners ℝ
      (DifferentialGeometry.Topology.Morse.MorseModel 3) H}
    [I.Boundaryless]
    {M : Type} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (⊤ : WithTop ℕ∞) M] [T2Space M]
    [SigmaCompactSpace M] [ConnectedSpace M]
    [LocallyPathConnectedSpace M]
    [DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M]
    [Inhabited M]
    (g : SmoothRiemannianMetric I M)
    (P : DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.GlobalSurfaceProductSplitting
      (I := I) (M := M) g) :
    let _ : TopologicalSpace P.N := P.topologyN
    let _ : ChartedSpace (DifferentialGeometry.Topology.Morse.MorseModel 2) P.N := P.chartedN
    let _ : IsManifold (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2))
        (↑(⊤ : ℕ∞) : WithTop ℕ∞) P.N := P.manifoldN
    let _ : T2Space P.N := P.t2N
    let _ : SigmaCompactSpace P.N := P.sigmaN
    Diffeomorph.pullbackMetricCross
        (I := (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod 𝓘(ℝ, ℝ))
        (J := I) (liftedMetric (I := I) g) P.F =
      P.metricN.prod (flatModelMetric ℝ) := by
  let _ : TopologicalSpace P.N := P.topologyN
  let _ : ChartedSpace (DifferentialGeometry.Topology.Morse.MorseModel 2) P.N := P.chartedN
  let _ : IsManifold (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2))
      (↑(⊤ : ℕ∞) : WithTop ℕ∞) P.N := P.manifoldN
  let _ : T2Space P.N := P.t2N
  let _ : SigmaCompactSpace P.N := P.sigmaN
  apply SmoothRiemannianMetric.ext_inner
  intro z u v
  rw [Diffeomorph.pullbackMetricCross_inner]
  have h := P.isometry z.1 z.2 u.1 v.1 u.2 v.2
  have hu : u = (show TangentSpace
      (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2).prod 𝓘(ℝ, ℝ)) z
      from (u.1, u.2)) := by rfl
  have hv : v = (show TangentSpace
      (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2).prod 𝓘(ℝ, ℝ)) z
      from (v.1, v.2)) := by rfl
  rw [hu, hv]
  rw [SmoothRiemannianMetric.prod_inner]
  have hfst (w : TangentSpace
      (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2).prod 𝓘(ℝ, ℝ)) z) :
      (mfderiv (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2).prod
        𝓘(ℝ, ℝ)) 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)
        Prod.fst z) w = w.1 := by
    rw [mfderiv_fst]
    rfl
  have hsnd (w : TangentSpace
      (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2).prod 𝓘(ℝ, ℝ)) z) :
      (mfderiv (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2).prod
        𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) Prod.snd z) w = w.2 := by
    rw [mfderiv_snd]
    rfl
  rw [hfst (show TangentSpace
    (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2).prod 𝓘(ℝ, ℝ)) z
    from (u.1, u.2)),
    hfst (show TangentSpace
      (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2).prod 𝓘(ℝ, ℝ)) z
      from (v.1, v.2)),
    hsnd (show TangentSpace
      (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2).prod 𝓘(ℝ, ℝ)) z
      from (u.1, u.2)),
    hsnd (show TangentSpace
      (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2).prod 𝓘(ℝ, ℝ)) z
      from (v.1, v.2))]
  have hflat : (flatModelMetric ℝ).inner z.2 u.2 v.2 = u.2 * v.2 := by
    change inner ℝ u.2 v.2 = _
    rw [RCLike.inner_apply]
    simp
    ring
  rw [hflat]
  have hFfun : (P.F : P.N × ℝ →
      DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover M) =
    (fun z => P.F z) := by rfl
  rw [hFfun]
  exact h

variable {N : Type} [TopologicalSpace N]
  [ChartedSpace (DifferentialGeometry.Topology.Morse.MorseModel 2) N]
  [IsManifold (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2))
    (↑(⊤ : ℕ∞) : WithTop ℕ∞) N]
  [T2Space N]

theorem metricScalarAt_prod_flat
    (g : SmoothRiemannianMetric
      (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)) N)
    (y : N) (t : ℝ) :
    metricScalarAt
        (I := (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
          𝓘(ℝ, ℝ))
        (g.prod (flatModelMetric ℝ)) (y, t) =
      metricScalarAt
        (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)) g y := by
  let I₂ := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)
  let J₁ := 𝓘(ℝ, ℝ)
  obtain ⟨bN, hN⟩ := exists_gOrthonormalBasis (I := I₂) g y
  let b : Module.Basis
      (Fin (Module.finrank ℝ (TangentSpace I₂ y)) ⊕ Unit) ℝ
      (TangentSpace (I₂.prod J₁) (y, t)) :=
    bN.prod (Module.Basis.singleton Unit ℝ)
  have hB : ∀ i j,
      (g.prod (flatModelMetric ℝ)).inner (y, t) (b i) (b j) =
        if i = j then (1 : ℝ) else 0 := by
    intro i j
    rcases i with i | i <;> rcases j with j | j
    · rw [SmoothRiemannianMetric.prod_inner]
      have hfst (w : TangentSpace (I₂.prod J₁) (y, t)) :
          mfderiv (I₂.prod J₁) I₂ Prod.fst (y, t) w = w.1 := by
        rw [mfderiv_fst]
        rfl
      have hsnd (w : TangentSpace (I₂.prod J₁) (y, t)) :
          mfderiv (I₂.prod J₁) J₁ Prod.snd (y, t) w = w.2 := by
        rw [mfderiv_snd]
        rfl
      have hbi : (b (Sum.inl i)).1 = bN i := by
        change ((bN.prod (Module.Basis.singleton Unit ℝ)) (Sum.inl i)).1 = _
        exact Module.Basis.prod_apply_inl_fst bN (Module.Basis.singleton Unit ℝ) i
      have hbj : (b (Sum.inl j)).1 = bN j := by
        change ((bN.prod (Module.Basis.singleton Unit ℝ)) (Sum.inl j)).1 = _
        exact Module.Basis.prod_apply_inl_fst bN (Module.Basis.singleton Unit ℝ) j
      have hbi₂ : (b (Sum.inl i)).2 = (0 : TangentSpace J₁ t) := by
        change ((bN.prod (Module.Basis.singleton Unit ℝ)) (Sum.inl i)).2 = _
        exact Module.Basis.prod_apply_inl_snd bN (Module.Basis.singleton Unit ℝ) i
      have hbj₂ : (b (Sum.inl j)).2 = (0 : TangentSpace J₁ t) := by
        change ((bN.prod (Module.Basis.singleton Unit ℝ)) (Sum.inl j)).2 = _
        exact Module.Basis.prod_apply_inl_snd bN (Module.Basis.singleton Unit ℝ) j
      rw [hfst (b (Sum.inl i)), hfst (b (Sum.inl j)),
        hsnd (b (Sum.inl i)), hsnd (b (Sum.inl j)), hbi, hbj, hbi₂, hbj₂]
      simp only [Sum.inl.injEq]
      change g.inner y (bN i) (bN j) +
        (flatModelMetric ℝ).inner t 0 0 = if i = j then 1 else 0
      rw [hN]
      have hflat00 : (flatModelMetric ℝ).inner t 0 0 = 0 := by
        change inner ℝ (0 : ℝ) 0 = 0
        rw [RCLike.inner_apply]
        simp
      rw [hflat00, add_zero]
    · rw [SmoothRiemannianMetric.prod_inner]
      have hfst (w : TangentSpace (I₂.prod J₁) (y, t)) :
          mfderiv (I₂.prod J₁) I₂ Prod.fst (y, t) w = w.1 := by
        rw [mfderiv_fst]
        rfl
      have hsnd (w : TangentSpace (I₂.prod J₁) (y, t)) :
          mfderiv (I₂.prod J₁) J₁ Prod.snd (y, t) w = w.2 := by
        rw [mfderiv_snd]
        rfl
      have hbi : (b (Sum.inl i)).1 = bN i := by
        change ((bN.prod (Module.Basis.singleton Unit ℝ)) (Sum.inl i)).1 = _
        exact Module.Basis.prod_apply_inl_fst bN (Module.Basis.singleton Unit ℝ) i
      have hbi₂ : (b (Sum.inl i)).2 = (0 : TangentSpace J₁ t) := by
        change ((bN.prod (Module.Basis.singleton Unit ℝ)) (Sum.inl i)).2 = _
        exact Module.Basis.prod_apply_inl_snd bN (Module.Basis.singleton Unit ℝ) i
      have hbj : (b (Sum.inr j)).1 = 0 := by
        change ((bN.prod (Module.Basis.singleton Unit ℝ)) (Sum.inr j)).1 = _
        exact Module.Basis.prod_apply_inr_fst bN (Module.Basis.singleton Unit ℝ) j
      have hbj₂ : (b (Sum.inr j)).2 = (1 : TangentSpace J₁ t) := by
        change ((bN.prod (Module.Basis.singleton Unit ℝ)) (Sum.inr j)).2 = _
        rw [Module.Basis.prod_apply_inr_snd, Module.Basis.singleton_apply]
        rfl
      rw [hfst (b (Sum.inl i)), hfst (b (Sum.inr j)),
        hsnd (b (Sum.inl i)), hsnd (b (Sum.inr j)), hbi, hbj, hbi₂, hbj₂]
      simp only [Sum.inl_ne_inr]
      change g.inner y (bN i) 0 +
        (flatModelMetric ℝ).inner t 0 1 = 0
      rw [map_zero]
      have hflat01 : (flatModelMetric ℝ).inner t 0 1 = 0 := by
        change inner ℝ (0 : ℝ) 1 = 0
        rw [RCLike.inner_apply]
        simp
      simp
    · rw [SmoothRiemannianMetric.prod_inner]
      have hfst (w : TangentSpace (I₂.prod J₁) (y, t)) :
          mfderiv (I₂.prod J₁) I₂ Prod.fst (y, t) w = w.1 := by
        rw [mfderiv_fst]
        rfl
      have hsnd (w : TangentSpace (I₂.prod J₁) (y, t)) :
          mfderiv (I₂.prod J₁) J₁ Prod.snd (y, t) w = w.2 := by
        rw [mfderiv_snd]
        rfl
      have hbi : (b (Sum.inr i)).1 = 0 := by
        change ((bN.prod (Module.Basis.singleton Unit ℝ)) (Sum.inr i)).1 = _
        exact Module.Basis.prod_apply_inr_fst bN (Module.Basis.singleton Unit ℝ) i
      have hbi₂ : (b (Sum.inr i)).2 = (1 : TangentSpace J₁ t) := by
        change ((bN.prod (Module.Basis.singleton Unit ℝ)) (Sum.inr i)).2 = _
        rw [Module.Basis.prod_apply_inr_snd, Module.Basis.singleton_apply]
        rfl
      have hbj : (b (Sum.inl j)).1 = bN j := by
        change ((bN.prod (Module.Basis.singleton Unit ℝ)) (Sum.inl j)).1 = _
        exact Module.Basis.prod_apply_inl_fst bN (Module.Basis.singleton Unit ℝ) j
      have hbj₂ : (b (Sum.inl j)).2 = (0 : TangentSpace J₁ t) := by
        change ((bN.prod (Module.Basis.singleton Unit ℝ)) (Sum.inl j)).2 = _
        exact Module.Basis.prod_apply_inl_snd bN (Module.Basis.singleton Unit ℝ) j
      rw [hfst (b (Sum.inr i)), hfst (b (Sum.inl j)),
        hsnd (b (Sum.inr i)), hsnd (b (Sum.inl j)), hbi, hbj, hbi₂, hbj₂]
      simp only [Sum.inr_ne_inl]
      change g.inner y 0 (bN j) +
        (flatModelMetric ℝ).inner t 1 0 = 0
      rw [map_zero]
      have hflat10 : (flatModelMetric ℝ).inner t 1 0 = 0 := by
        change inner ℝ (1 : ℝ) 0 = 0
        rw [RCLike.inner_apply]
        simp
      simp [hflat10]
    · rw [SmoothRiemannianMetric.prod_inner]
      have hfst (w : TangentSpace (I₂.prod J₁) (y, t)) :
          mfderiv (I₂.prod J₁) I₂ Prod.fst (y, t) w = w.1 := by
        rw [mfderiv_fst]
        rfl
      have hsnd (w : TangentSpace (I₂.prod J₁) (y, t)) :
          mfderiv (I₂.prod J₁) J₁ Prod.snd (y, t) w = w.2 := by
        rw [mfderiv_snd]
        rfl
      have hbi : (b (Sum.inr i)).1 = 0 := by
        change ((bN.prod (Module.Basis.singleton Unit ℝ)) (Sum.inr i)).1 = _
        exact Module.Basis.prod_apply_inr_fst bN (Module.Basis.singleton Unit ℝ) i
      have hbi₂ : (b (Sum.inr i)).2 = (1 : TangentSpace J₁ t) := by
        change ((bN.prod (Module.Basis.singleton Unit ℝ)) (Sum.inr i)).2 = _
        rw [Module.Basis.prod_apply_inr_snd, Module.Basis.singleton_apply]
        rfl
      have hbj : (b (Sum.inr j)).1 = 0 := by
        change ((bN.prod (Module.Basis.singleton Unit ℝ)) (Sum.inr j)).1 = _
        exact Module.Basis.prod_apply_inr_fst bN (Module.Basis.singleton Unit ℝ) j
      have hbj₂ : (b (Sum.inr j)).2 = (1 : TangentSpace J₁ t) := by
        change ((bN.prod (Module.Basis.singleton Unit ℝ)) (Sum.inr j)).2 = _
        rw [Module.Basis.prod_apply_inr_snd, Module.Basis.singleton_apply]
        rfl
      have hij : i = j := Subsingleton.elim _ _
      subst j
      rw [mfderiv_fst, mfderiv_snd]
      change g.inner y (b (Sum.inr i)).1 (b (Sum.inr i)).1 +
        (flatModelMetric ℝ).inner t (b (Sum.inr i)).2 (b (Sum.inr i)).2 =
          if Sum.inr i = Sum.inr i then 1 else 0
      rw [hbi, hbi₂]
      change g.inner y 0 0 +
        (flatModelMetric ℝ).inner t 1 1 = 1
      rw [map_zero]
      have hflat11 : (flatModelMetric ℝ).inner t 1 1 = 1 := by
        change inner ℝ (1 : ℝ) 1 = 1
        rw [RCLike.inner_apply]
        simp
      simp [hflat11]
  have hiN := metricInverseInBasis_of_orthonormal (I := I₂) g bN hN
  have hiB := metricInverseInBasis_of_orthonormal
    (I := I₂.prod J₁) (g.prod (flatModelMetric ℝ)) b hB
  have hb_inl (i : Fin (Module.finrank ℝ (TangentSpace I₂ y))) :
      b (Sum.inl i) = (bN i, (0 : TangentSpace J₁ t)) := by
    apply Prod.ext
    · exact Module.Basis.prod_apply_inl_fst bN (Module.Basis.singleton Unit ℝ) i
    · exact Module.Basis.prod_apply_inl_snd bN (Module.Basis.singleton Unit ℝ) i
  have hb_inr (i : Unit) :
      b (Sum.inr i) = ((0 : TangentSpace I₂ y), (1 : TangentSpace J₁ t)) := by
    apply Prod.ext
    · exact Module.Basis.prod_apply_inr_fst bN (Module.Basis.singleton Unit ℝ) i
    · change ((bN.prod (Module.Basis.singleton Unit ℝ)) (Sum.inr i)).2 = _
      rw [Module.Basis.prod_apply_inr_snd, Module.Basis.singleton_apply]
      rfl
  have hflatRic : ∀ v : TangentSpace J₁ t,
      ricciTensor (I := J₁) (flatModelMetric ℝ) t v v = 0 := by
    intro v
    let b0 : Module.Basis (Fin (Module.finrank ℝ ℝ)) Real (TangentSpace J₁ t) :=
      DifferentialGeometry.Integral.Measure.centeredChartTangentBasis (I := J₁) t
    have hdim : Module.finrank Real (TangentSpace J₁ t) = 1 := by
      change Module.finrank Real ℝ = 1
      simp
    let b1 : Module.Basis (Fin 1) Real (TangentSpace J₁ t) := hdim ▸ b0
    have hrepr (z : TangentSpace J₁ t) : z = (b1.repr z 0) • b1 0 := by
      rw [← b1.sum_repr z]
      simp
    have hR (z : TangentSpace J₁ t) :
        riemannOp (LeviCivita (I := J₁) (flatModelMetric ℝ)) t z v v = 0 := by
      rw [hrepr z, hrepr v]
      simp only [map_smul]
      have hdiag : riemannOp (LeviCivita (I := J₁) (flatModelMetric ℝ)) t
          (b1 0) (b1 0) (b1 0) = 0 := by
        have hs := riemannOp_swap (LeviCivita (I := J₁) (flatModelMetric ℝ)) t
          (b1 0) (b1 0) (b1 0)
        let q : TangentSpace J₁ t :=
          riemannOp (LeviCivita (I := J₁) (flatModelMetric ℝ)) t
            (b1 0) (b1 0) (b1 0)
        have htwo : (2 : Real) • q = 0 := by
          rw [two_smul]
          have hsq : q = -q := hs
          nth_rewrite 2 [hsq]
          exact add_neg_cancel (q : TangentSpace J₁ t)
        rcases smul_eq_zero.mp htwo with htwo | hzero
        · norm_num at htwo
        · exact hzero
      simp only [smul_apply, hdiag, smul_zero]
    rw [ricciTensor_apply]
    have hendo : ricciEndo (I := J₁) (flatModelMetric ℝ) t v v = 0 := by
      apply LinearMap.ext
      intro z
      exact hR z
    rw [hendo]
    simp
  rw [metricScalarAt_def, metricScalarAt_def,
    metricTracePair0SAt_eq_sum_basis (I := I₂.prod J₁)
      (g.prod (flatModelMetric ℝ)) b
      (fun i j => if i = j then 1 else 0) hiB,
    metricTracePair0SAt_eq_sum_basis (I := I₂) g bN
      (fun i j => if i = j then 1 else 0) hiN]
  simp only [metricRicciAt_apply_eq_ricciTensor, Curvature.ricciTensor_prod]
  simp_rw [Fintype.sum_sum_type]
  simp_rw [hb_inl, hb_inr]
  simp [hflatRic]

theorem curvatureOperator_time_slice_rank_trichotomy_of_complete_metric
    (g : SmoothRiemannianMetric I M)
    (hg : DifferentialGeometry.RiemannianMetricComplete (I := I) g)
    (hpositive : ∀ x,
      ∀ a : TangentSpace I x [⋀^Fin 2]→L[Real] Real,
        0 ≤ (twoFormMetricData (I := I) g x).inner
          (curvatureOperatorEndomorphismAt (I := I) g x
            ⟨metricRm04 (I := I) g x,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) g x⟩ a) a)
    (hnull : ∀ x,
      ∀ a : TangentSpace I x [⋀^Fin 2]→L[Real] Real,
        curvatureOperatorEndomorphismAt (I := I) g x
            ⟨metricRm04 (I := I) g x,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) g x⟩ a = 0 →
          curvatureOperatorReactionEndomorphism3
            (curvatureOperatorEndomorphismAt (I := I) g x
              ⟨metricRm04 (I := I) g x,
                metricRm04At_mem_algebraicCurvatureTensorSubmodule
                  (I := I) g x⟩).toLinearMap a = 0)
    (hrank : ∀ x y,
      Module.finrank Real
          (curvatureOperatorImageAt (I := I) g x
            ⟨metricRm04 (I := I) g x,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) g x⟩) =
        Module.finrank Real
          (curvatureOperatorImageAt (I := I) g y
            ⟨metricRm04 (I := I) g y,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule
                (I := I) g y⟩))
    (hkernel : IsParallelContinuousAlternatingSubmoduleFamily g
      (fun x => curvatureOperatorKernelAt (I := I) g x
        ⟨metricRm04 (I := I) g x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule
            (I := I) g x⟩)) :
    (And
      (∀ x, curvatureOperatorEndomorphismAt (I := I) g x
        ⟨metricRm04 (I := I) g x,
          metricRm04At_mem_algebraicCurvatureTensorSubmodule (I := I) g x⟩ = 0)
      (HasEuclideanUniversalCover
        (E := DifferentialGeometry.Topology.Morse.MorseModel 3)
        (I := I) (M := M) g)) ∨
      (And
        (∀ x, Module.finrank Real
          (curvatureOperatorImageAt (I := I) g x
              ⟨metricRm04 (I := I) g x,
                metricRm04At_mem_algebraicCurvatureTensorSubmodule
                  (I := I) g x⟩) = 1)
        (HasCurvatureSurfaceProductSplitting (I := I) (M := M) g)) ∨
      And
        (∀ x, Module.finrank Real
          (curvatureOperatorImageAt (I := I) g x
            ⟨metricRm04 (I := I) g x,
              metricRm04At_mem_algebraicCurvatureTensorSubmodule
                  (I := I) g x⟩) = 3)
        (∀ x, ∀ a : TangentSpace I x [⋀^Fin 2]→L[Real] Real, a ≠ 0 →
          0 < (twoFormMetricData (I := I) g x).inner
            (curvatureOperatorEndomorphismAt (I := I) g x
              ⟨metricRm04 (I := I) g x,
                metricRm04At_mem_algebraicCurvatureTensorSubmodule
                  (I := I) g x⟩ a) a) := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace H M
  let _ : DifferentialGeometry.Geometry.Riemannian.Topology.SemilocallySimplyConnectedSpace M :=
    DifferentialGeometry.Geometry.Riemannian.Topology.manifold_semilocallySimplyConnectedSpace
      (I := I)
  let _ : Inhabited M := ⟨Classical.choice (inferInstance : Nonempty M)⟩
  have hE : Module.finrank Real
      (DifferentialGeometry.Topology.Morse.MorseModel 3) = 3 := by
    simp [DifferentialGeometry.Topology.Morse.MorseModel]
  have htri := curvatureOperator_time_slice_trichotomy_of_metric
    (I := I) hE g hpositive hnull hrank hkernel
  rcases htri with hzero | hline | hpositiveRank
  · refine Or.inl ⟨hzero, ?_⟩
    let : NeZero (Module.finrank Real
        (DifferentialGeometry.Topology.Morse.MorseModel 3)) :=
      ⟨by rw [hE]; norm_num⟩
    apply hasEuclideanUniversalCover_of_riemannOp_eq_zero (I := I) g hg
    intro x
    exact riemannOp_eq_zero_of_curvatureOperatorEndomorphismAt_eq_zero
      (I := I) g x (hzero x)
  · refine Or.inr (Or.inl ⟨hline.1, ?_⟩)
    obtain ⟨S, hSrank, hSfiber, hSparallel⟩ :=
      exists_smooth_parallel_curvatureOperatorImageLine
        (I := I) hE g (metricRm04 (I := I) g)
        (fun x => metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (I := I) g x) hline.1 hkernel
    obtain ⟨N, topologyN, hcs, hmanifold, ht2, hσ, h,
        hconnected, hsimplyConnected, hhcomplete, F, hF, hmetric⟩ :=
      exists_global_product_diffeomorph_of_parallel_line
        (I := I) (M := M) (m := 2) g hg S hSrank hSparallel
    let _ : TopologicalSpace N := topologyN
    let _ : ChartedSpace
        (DifferentialGeometry.Topology.Morse.MorseModel 2) N := hcs
    let _ : IsManifold
        (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2))
        (↑(⊤ : ℕ∞) : WithTop ℕ∞) N := hmanifold
    let _ : T2Space N := ht2
    let _ : SigmaCompactSpace N := hσ
    have hS' := liftTangentSubbundle_isParallel_of_rank_eq_one
      (I := I) (M := M) g S hSrank hSparallel
    let P : GlobalSurfaceProductSplitting (I := I) (M := M) g := {
      N := N
      metricN := h
      connectedN := hconnected
      simplyConnectedN := hsimplyConnected
      completeN := hhcomplete
      F := F
      line := liftTangentSubbundle (I := I) (M := M) S
      line_rank := by simpa using hSrank
      line_parallel := hS'
      line_compatibility := hF
      isometry := hmetric
    }
    have hfactor : ∀ y : P.N,
        metricScalarAt
            (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2))
            P.metricN y =
          metricScalarAt (I := I) (liftedMetric (I := I) g) (P.F (y, 0)) := by
      intro y
      have hprod := metricScalarAt_prod_flat P.metricN y (0 : ℝ)
      have hpull := DifferentialGeometry.HCGCompactness.metricScalar_cross
        (I := (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
          𝓘(ℝ, ℝ))
        (J := I) (g := liftedMetric (I := I) g) (Phi := P.F) (x := (y, 0))
      have heq := P.pullbackMetric_eq_prod g
      have heqscalar := congrArg
          (fun q : SmoothRiemannianMetric
            ((𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod 𝓘(ℝ, ℝ))
            (P.N × ℝ) => metricScalarAt
              (I := (𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2)).prod
                𝓘(ℝ, ℝ)) q (y, 0)) heq
      rw [hprod] at heqscalar
      exact heqscalar.symm.trans hpull
    refine ⟨S, P, hSrank, ?_, ?_, ?_⟩
    · intro x
      exact hSfiber x
    · intro y
      rw [liftTangentSubbundle_fiber]
    · intro y
      calc
        metricScalarAt
            (I := 𝓘(ℝ, DifferentialGeometry.Topology.Morse.MorseModel 2))
            P.metricN y =
            metricScalarAt (I := I) (liftedMetric (I := I) g) (P.F (y, 0)) :=
          hfactor y
        _ = metricScalarAt (I := I) g (proj (P.F (y, 0))) :=
          DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover.metricScalarAt_lifted
            (I := I) g (P.F (y, 0))
        _ > 0 := metricScalarAt_pos_of_curvatureOperator_rank_one
          (I := I) hE g (proj (P.F (y, 0)))
          (hpositive (proj (P.F (y, 0)))) (hline.1 (proj (P.F (y, 0))))
  · exact Or.inr (Or.inr hpositiveRank)

end DifferentialGeometry.Geometry.Curvature.DimensionThree
