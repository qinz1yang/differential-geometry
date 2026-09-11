import DifferentialGeometry.Analysis.Parabolic.Dirichlet.FormMeasurability
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.GalerkinTimeL2
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.GalerkinWeakIdentity
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.WeakCompactness

noncomputable section

open Bundle Filter Manifold MeasureTheory Set
open scoped BigOperators ContDiff ENNReal InnerProductSpace Manifold NNReal
  RealInnerProductSpace Topology

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Analysis.Parabolic.TimeSobolev
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Integral.Measure

variable {n : ℕ} [NeZero n]
variable {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace n) M]
  [IsManifold (modelWithCornersEuclideanHalfSpace n) ∞ M]
  [T2Space M] [CompactSpace M]

private abbrev I_half (n : ℕ) [NeZero n] :
    ModelWithCorners ℝ (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace n) :=
  modelWithCornersEuclideanHalfSpace n

def IsIntegratedWeakSolution
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {T : ℝ} (hT : 0 ≤ T) (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (X : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ → ℝ) (Bx Bv : ℝ)
    (hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx)
    (htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ Bv)
    (f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) q))
    (u : timeL2 (H1ComplDirichlet q) T) : Prop :=
  ∃ Cg : ℝ, ∃ Cv : ℝ≥0∞,
    ∃ hCg : 1 ≤ Cg,
    ∃ hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      ∀ v : TangentSpace (I_half n) x,
        Cg⁻¹ * q.inner x v v ≤ (G.metric t).inner x v v ∧
          (G.metric t).inner x v v ≤ Cg * q.inner x v v,
    ∃ hCv0 : Cv ≠ 0, ∃ hCvtop : Cv ≠ ⊤,
    ∃ hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t) ≤
        Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q,
    ∀ (η dη : ℝ → ℝ),
      ContinuousOn η (Icc (0 : ℝ) T) →
      ContinuousOn dη (Icc (0 : ℝ) T) →
      (∀ t ∈ Ioo (0 : ℝ) T,
        HasDerivWithinAt η (dη t) (Ioi t) t) →
      η T = 0 →
      ∀ v : H1ComplDirichlet q,
        -(∫ t in Icc (0 : ℝ) T,
            dη t * dirichletMassComplOnIcc G.metric hCg hequiv
              Cv hCv0 hCvtop hvol t (u t) v) -
          (∫ t in Icc (0 : ℝ) T,
            η t * dirichletMassVariationComplOnIco hG hreg Bv htrace
              hCg hequiv Cv hCv0 hCvtop hvol t (u t) v) -
          η 0 * dirichletMassLp (G.metric 0) Cv hCvtop
            (hvol 0 ⟨le_rfl, hT⟩) f₀ (H1ComplDirichletToLp q v) =
          ∫ t in Icc (0 : ℝ) T,
            η t * dirichletWeakFormComplOnIco G.metric X a Bx hX
              hCg hequiv Cv hCv0 hCvtop hvol t (u t) v

private theorem smoothDirichletBasisFinIncl_single
    {q : SmoothRiemannianMetric (I_half n) M}
    (s : Finset (SmoothDirichletBasisIndex q))
    (i : SmoothDirichletBasisIndex q) (hi : i ∈ s) :
    smoothDirichletBasisFinIncl s
        (EuclideanSpace.single (⟨i, hi⟩ : s) 1) =
      smoothDirichletBasisFunction q i := by
  rw [smoothDirichletBasisFinIncl_apply]
  simp

private theorem eventually_mem_smoothDirichletBasisFinset_comp
    {q : SmoothRiemannianMetric (I_half n) M}
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (i : SmoothDirichletBasisIndex q) :
    ∀ᶠ m in atTop, i ∈ smoothDirichletBasisFinset q (φ m) := by
  filter_upwards [hφ.tendsto_atTop.eventually
    (eventually_ge_atTop i.1.succ)] with m hm
  rw [mem_smoothDirichletBasisFinset_iff]
  exact Nat.lt_of_succ_le hm

private theorem norm_integral_weighted_bilinear_le
    {Y Z : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [CompleteSpace Y] [TopologicalSpace.SeparableSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {T : ℝ} (u : timeL2 Y T)
    (B : ℝ → Y →L[ℝ] Z →L[ℝ] ℝ)
    (hB : ∀ y z, AEStronglyMeasurable (fun t ↦ B t y z) (timeMeasure T))
    {C : ℝ} (hC : ∀ᵐ t ∂(timeMeasure T), ‖B t‖ ≤ C)
    (c : ℝ → ℝ) (hc : AEStronglyMeasurable c (timeMeasure T))
    {K : ℝ} (hK : ∀ᵐ t ∂(timeMeasure T), ‖c t‖ ≤ K)
    (z : Z) :
    ‖∫ t in Icc (0 : ℝ) T, c t * B t (u t) z‖ ≤
      max 0 K * max 0 C * Real.sqrt T * ‖u‖ * ‖z‖ := by
  have hint := integrable_weighted_bilinear_of_apply_aestronglyMeasurable
    u B hB hC c hc hK z
  have hmajor : Integrable
      (fun t ↦ max 0 K * max 0 C * ‖u t‖ * ‖z‖) (timeMeasure T) :=
    (((TimeSobolev.integrable u).norm.const_mul
      (max 0 K * max 0 C)).mul_const ‖z‖)
  have hpoint : ∀ᵐ t ∂(timeMeasure T),
      ‖c t * B t (u t) z‖ ≤
        max 0 K * max 0 C * ‖u t‖ * ‖z‖ := by
    filter_upwards [hC, hK] with t hBt hct
    calc
      ‖c t * B t (u t) z‖ = ‖c t‖ * ‖B t (u t) z‖ := norm_mul _ _
      _ ≤ ‖c t‖ * (‖B t‖ * (‖u t‖ * ‖z‖)) := by
        gcongr
        calc
          ‖B t (u t) z‖ ≤ ‖B t (u t)‖ * ‖z‖ := (B t (u t)).le_opNorm z
          _ ≤ (‖B t‖ * ‖u t‖) * ‖z‖ := by
            gcongr
            exact (B t).le_opNorm (u t)
          _ = ‖B t‖ * (‖u t‖ * ‖z‖) := by ring
      _ ≤ max 0 K * (max 0 C * (‖u t‖ * ‖z‖)) := by
        gcongr
        · exact hct.trans (le_max_right 0 K)
        · exact hBt.trans (le_max_right 0 C)
      _ = max 0 K * max 0 C * ‖u t‖ * ‖z‖ := by ring
  change ‖∫ t, c t * B t (u t) z ∂(timeMeasure T)‖ ≤ _
  calc
    ‖∫ t, c t * B t (u t) z ∂(timeMeasure T)‖ ≤
        ∫ t, ‖c t * B t (u t) z‖ ∂(timeMeasure T) :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t, max 0 K * max 0 C * ‖u t‖ * ‖z‖ ∂(timeMeasure T) :=
      integral_mono_ae hint.norm hmajor hpoint
    _ = max 0 K * max 0 C * (∫ t, ‖u t‖ ∂(timeMeasure T)) * ‖z‖ := by
      rw [integral_mul_const, integral_const_mul]
    _ ≤ max 0 K * max 0 C * (Real.sqrt T * ‖u‖) * ‖z‖ := by
      gcongr
      exact TimeSobolev.integral_norm_le u
    _ = max 0 K * max 0 C * Real.sqrt T * ‖u‖ * ‖z‖ := by ring

private noncomputable def integralWeightedBilinearRight
    {Y Z : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [CompleteSpace Y] [TopologicalSpace.SeparableSpace Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    {T : ℝ} (u : timeL2 Y T)
    (B : ℝ → Y →L[ℝ] Z →L[ℝ] ℝ)
    (hB : ∀ y z, AEStronglyMeasurable (fun t ↦ B t y z) (timeMeasure T))
    {C : ℝ} (hC : ∀ᵐ t ∂(timeMeasure T), ‖B t‖ ≤ C)
    (c : ℝ → ℝ) (hc : AEStronglyMeasurable c (timeMeasure T))
    {K : ℝ} (hK : ∀ᵐ t ∂(timeMeasure T), ‖c t‖ ≤ K) :
    Z →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun z ↦ ∫ t in Icc (0 : ℝ) T, c t * B t (u t) z
      map_add' := fun z w ↦ by
        change (∫ t, c t * B t (u t) (z + w) ∂(timeMeasure T)) =
          (∫ t, c t * B t (u t) z ∂(timeMeasure T)) +
            ∫ t, c t * B t (u t) w ∂(timeMeasure T)
        rw [← integral_add
          (integrable_weighted_bilinear_of_apply_aestronglyMeasurable
            u B hB hC c hc hK z)
          (integrable_weighted_bilinear_of_apply_aestronglyMeasurable
            u B hB hC c hc hK w)]
        refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
        simp only [map_add, mul_add]
      map_smul' := fun r z ↦ by
        change (∫ t, c t * B t (u t) (r • z) ∂(timeMeasure T)) =
          r • ∫ t, c t * B t (u t) z ∂(timeMeasure T)
        rw [← integral_smul]
        refine integral_congr_ae (Eventually.of_forall fun t ↦ ?_)
        simp only [map_smul, smul_eq_mul]
        ring }
    (max 0 K * max 0 C * Real.sqrt T * ‖u‖)
    (fun z ↦ norm_integral_weighted_bilinear_le u B hB hC c hc hK z)

private theorem weighted_bilinear_identity_of_dense_span
    {Y : Type*} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
    [CompleteSpace Y] [TopologicalSpace.SeparableSpace Y]
    {ι : Type*} (e : ι → Y)
    (he : Dense (Submodule.span ℝ (Set.range e) : Set Y))
    {T : ℝ} (u : timeL2 Y T)
    (B₁ B₂ B₃ : ℝ → Y →L[ℝ] Y →L[ℝ] ℝ)
    (hB₁ : ∀ y z, AEStronglyMeasurable (fun t ↦ B₁ t y z) (timeMeasure T))
    (hB₂ : ∀ y z, AEStronglyMeasurable (fun t ↦ B₂ t y z) (timeMeasure T))
    (hB₃ : ∀ y z, AEStronglyMeasurable (fun t ↦ B₃ t y z) (timeMeasure T))
    {C₁ C₂ C₃ : ℝ}
    (hC₁ : ∀ᵐ t ∂(timeMeasure T), ‖B₁ t‖ ≤ C₁)
    (hC₂ : ∀ᵐ t ∂(timeMeasure T), ‖B₂ t‖ ≤ C₂)
    (hC₃ : ∀ᵐ t ∂(timeMeasure T), ‖B₃ t‖ ≤ C₃)
    (c₁ c₂ : ℝ → ℝ)
    (hc₁ : AEStronglyMeasurable c₁ (timeMeasure T))
    (hc₂ : AEStronglyMeasurable c₂ (timeMeasure T))
    {K₁ K₂ : ℝ}
    (hK₁ : ∀ᵐ t ∂(timeMeasure T), ‖c₁ t‖ ≤ K₁)
    (hK₂ : ∀ᵐ t ∂(timeMeasure T), ‖c₂ t‖ ≤ K₂)
    (initial : Y →L[ℝ] ℝ)
    (hbasis : ∀ i,
      -(∫ t in Icc (0 : ℝ) T, c₁ t * B₁ t (u t) (e i)) -
        (∫ t in Icc (0 : ℝ) T, c₂ t * B₂ t (u t) (e i)) -
        initial (e i) =
        ∫ t in Icc (0 : ℝ) T, c₂ t * B₃ t (u t) (e i))
    (z : Y) :
    -(∫ t in Icc (0 : ℝ) T, c₁ t * B₁ t (u t) z) -
      (∫ t in Icc (0 : ℝ) T, c₂ t * B₂ t (u t) z) - initial z =
      ∫ t in Icc (0 : ℝ) T, c₂ t * B₃ t (u t) z := by
  let F₁ := integralWeightedBilinearRight u B₁ hB₁ hC₁ c₁ hc₁ hK₁
  let F₂ := integralWeightedBilinearRight u B₂ hB₂ hC₂ c₂ hc₂ hK₂
  let F₃ := integralWeightedBilinearRight u B₃ hB₃ hC₃ c₂ hc₂ hK₂
  let F : Y →L[ℝ] ℝ := -F₁ - F₂ - initial - F₃
  have hOnRange : Set.EqOn F 0 (Set.range e) := by
    rintro _ ⟨i, rfl⟩
    change -F₁ (e i) - F₂ (e i) - initial (e i) - F₃ (e i) = 0
    have hi := hbasis i
    change -F₁ (e i) - F₂ (e i) - initial (e i) = F₃ (e i) at hi
    linarith
  have hFzero : F = (0 : Y →L[ℝ] ℝ) :=
    ContinuousLinearMap.ext_on he hOnRange
  have hFz := congrArg (fun L : Y →L[ℝ] ℝ ↦ L z) hFzero
  change -F₁ z - F₂ z - initial z - F₃ z = 0 at hFz
  change -F₁ z - F₂ z - initial z = F₃ z
  linarith

private theorem dirichlet_weak_limit_identity_basis
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {T : ℝ} (hT : 0 < T) (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (X : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (hXcont : ContinuousOn
      (fun p : ℝ × M ↦
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle (I_half n) M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (a : ℝ → ℝ) (hacont : ContinuousOn a (Icc (0 : ℝ) T))
    (Bx Bv A : ℝ) (hA : 0 ≤ A)
    (haBound : ∀ t ∈ Ico (0 : ℝ) T, |a t| ≤ A)
    (hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx)
    (htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ Bv)
    (f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) q))
    {Cg : ℝ} (hCg : 1 ≤ Cg)
    (hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
      ∀ v : TangentSpace (I_half n) x,
        Cg⁻¹ * q.inner x v v ≤ (G.metric t).inner x v v ∧
          (G.metric t).inner x v v ≤ Cg * q.inner x v v)
    (Cv : ℝ≥0∞) (hCv0 : Cv ≠ 0) (hCvtop : Cv ≠ ⊤)
    (hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t) ≤
        Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q)
    (γ : (m : ℕ) → ℝ →
      EuclideanSpace ℝ (smoothDirichletBasisFinset q m))
    (U : ℕ → timeL2 (H1ComplDirichlet q) T)
    (φ : ℕ → ℕ) (u : timeL2 (H1ComplDirichlet q) T)
    (hφ : StrictMono φ)
    (hUweak : ∀ z, Tendsto (fun m ↦ inner ℝ (U (φ m)) z) atTop
      (𝓝 (inner ℝ u z)))
    (hγ0 : ∀ m, γ m 0 = smoothDirichletBasisCoordinates
      (smoothDirichletBasisFinset q m) f₀)
    (hγcont : ∀ m, ContinuousOn (γ m) (Icc (0 : ℝ) T))
    (hγweak : ∀ m t, (ht : t ∈ Ico (0 : ℝ) T) →
      ∃ v : EuclideanSpace ℝ (smoothDirichletBasisFinset q m),
        HasDerivWithinAt (γ m) v (Ici (0 : ℝ)) t ∧
          dirichletFinMass (G.metric t)
              (smoothDirichletBasisFinIncl
                (smoothDirichletBasisFinset q m)) v =
            dirichletFinWeakForm (G.metric t) (X t) (a t)
              (smoothDirichletBasisFinIncl
                (smoothDirichletBasisFinset q m)) (γ m t))
    (hUtie : ∀ m, U m =ᵐ[timeMeasure T]
      (fun t ↦ smoothToH1ComplDirichlet q
        (smoothDirichletBasisFinIncl
          (smoothDirichletBasisFinset q m) (γ m t))))
    (i : SmoothDirichletBasisIndex q)
    (η dη : ℝ → ℝ)
    (hηcont : ContinuousOn η (Icc (0 : ℝ) T))
    (hdηcont : ContinuousOn dη (Icc (0 : ℝ) T))
    (hηderiv : ∀ t ∈ Ioo (0 : ℝ) T,
      HasDerivWithinAt η (dη t) (Ioi t) t)
    (hηT : η T = 0) :
    -(∫ t in Icc (0 : ℝ) T,
        dη t * dirichletMassComplOnIcc G.metric hCg hequiv
          Cv hCv0 hCvtop hvol t (u t)
          (smoothToH1ComplDirichlet q (smoothDirichletBasisFunction q i))) -
      (∫ t in Icc (0 : ℝ) T,
        η t * dirichletMassVariationComplOnIco hG hreg Bv htrace
          hCg hequiv Cv hCv0 hCvtop hvol t (u t)
          (smoothToH1ComplDirichlet q (smoothDirichletBasisFunction q i))) -
      η 0 * dirichletMassLp (G.metric 0) Cv hCvtop
        (hvol 0 ⟨le_rfl, hT.le⟩) f₀
        (H1ComplDirichletToLp q
          (smoothToH1ComplDirichlet q (smoothDirichletBasisFunction q i))) =
      ∫ t in Icc (0 : ℝ) T,
        η t * dirichletWeakFormComplOnIco G.metric X a Bx hX
          hCg hequiv Cv hCv0 hCvtop hvol t (u t)
          (smoothToH1ComplDirichlet q (smoothDirichletBasisFunction q i)) := by
  let v := smoothToH1ComplDirichlet q (smoothDirichletBasisFunction q i)
  let massForm := dirichletMassComplOnIcc G.metric hCg hequiv
    Cv hCv0 hCvtop hvol
  let variationForm := dirichletMassVariationComplOnIco hG hreg Bv htrace
    hCg hequiv Cv hCv0 hCvtop hvol
  let weakForm := dirichletWeakFormComplOnIco G.metric X a Bx hX
    hCg hequiv Cv hCv0 hCvtop hvol
  obtain ⟨Kη, hKη⟩ := isCompact_Icc.exists_bound_of_continuousOn hηcont
  obtain ⟨Kdη, hKdη⟩ := isCompact_Icc.exists_bound_of_continuousOn hdηcont
  have hηMeas : AEStronglyMeasurable η (timeMeasure T) := by
    unfold timeMeasure
    exact hηcont.aestronglyMeasurable measurableSet_Icc
  have hdηMeas : AEStronglyMeasurable dη (timeMeasure T) := by
    unfold timeMeasure
    exact hdηcont.aestronglyMeasurable measurableSet_Icc
  have hηBound : ∀ᵐ t ∂(timeMeasure T), ‖η t‖ ≤ Kη := by
    unfold timeMeasure
    exact (ae_restrict_iff' measurableSet_Icc).2
      (Eventually.of_forall fun t ht ↦ hKη t ht)
  have hdηBound : ∀ᵐ t ∂(timeMeasure T), ‖dη t‖ ≤ Kdη := by
    unfold timeMeasure
    exact (ae_restrict_iff' measurableSet_Icc).2
      (Eventually.of_forall fun t ht ↦ hKdη t ht)
  have hmassMeas : ∀ y z, AEStronglyMeasurable
      (fun t ↦ massForm t y z) (timeMeasure T) := by
    intro y z
    exact dirichletMassComplOnIcc_aestronglyMeasurable hG hreg hCg
      hequiv Cv hCv0 hCvtop hvol y z
  have hvariationMeas : ∀ y z, AEStronglyMeasurable
      (fun t ↦ variationForm t y z) (timeMeasure T) := by
    intro y z
    exact dirichletMassVariationComplOnIco_aestronglyMeasurable hG hreg
      Bv htrace hCg hequiv Cv hCv0 hCvtop hvol y z
  have hweakMeas : ∀ y z, AEStronglyMeasurable
      (fun t ↦ weakForm t y z) (timeMeasure T) := by
    intro y z
    exact dirichletWeakFormComplOnIco_aestronglyMeasurable hG hreg X
      hXcont a hacont Bx hX hCg hequiv Cv hCv0 hCvtop hvol y z
  have hmassBound :=
    Eventually.of_forall (f := MeasureTheory.ae (timeMeasure T)) fun t ↦
      norm_dirichletMassComplOnIcc_le
      G.metric hCg hequiv Cv hCv0 hCvtop hvol t
  have hvariationBound :=
    Eventually.of_forall (f := MeasureTheory.ae (timeMeasure T)) fun t ↦
      norm_dirichletMassVariationComplOnIco_le
      hG hreg Bv htrace hCg hequiv Cv hCv0 hCvtop hvol t
  have hweakBound :=
    Eventually.of_forall (f := MeasureTheory.ae (timeMeasure T)) fun t ↦
      norm_dirichletWeakFormComplOnIco_le
      G.metric X a A Bx hA haBound hX hCg hequiv Cv hCv0 hCvtop hvol t
  have hmassLimit :=
    tendsto_integral_weighted_bilinear_of_weakly_tendsto_of_apply_aestronglyMeasurable
      hUweak massForm hmassMeas hmassBound dη hdηMeas hdηBound v
  have hvariationLimit :=
    tendsto_integral_weighted_bilinear_of_weakly_tendsto_of_apply_aestronglyMeasurable
      hUweak variationForm hvariationMeas hvariationBound η hηMeas hηBound v
  have hweakLimit :=
    tendsto_integral_weighted_bilinear_of_weakly_tendsto_of_apply_aestronglyMeasurable
      hUweak weakForm hweakMeas hweakBound η hηMeas hηBound v
  have happroxLimit : Tendsto
      (fun m ↦ smoothToLpDirichlet q
        (smoothDirichletBasisApproximation q (φ m) f₀)) atTop (𝓝 f₀) :=
    (tendsto_smoothToLpDirichlet_smoothDirichletBasisApproximation q f₀).comp
      hφ.tendsto_atTop
  let initialForm := (dirichletMassLp (G.metric 0) Cv hCvtop
    (hvol 0 ⟨le_rfl, hT.le⟩)).flip
      (H1ComplDirichletToLp q v)
  have hinitialLimit : Tendsto
      (fun m ↦ η 0 * initialForm
        (smoothToLpDirichlet q
          (smoothDirichletBasisApproximation q (φ m) f₀))) atTop
      (𝓝 (η 0 * initialForm f₀)) :=
    (continuous_const.mul initialForm.continuous).continuousAt.tendsto.comp happroxLimit
  have hIco : ∀ᵐ t ∂(timeMeasure T), t ∈ Ico (0 : ℝ) T := by
    unfold timeMeasure
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards [(Ico_ae_eq_Icc :
      Ico (0 : ℝ) T =ᵐ[volume] Icc (0 : ℝ) T)] with t ht
    intro htIcc
    exact Eq.mpr ht htIcc
  have hsequenceIdentity : ∀ᶠ m in atTop,
      -(∫ t in Icc (0 : ℝ) T,
          dη t * massForm t (U (φ m) t) v) -
        (∫ t in Icc (0 : ℝ) T,
          η t * variationForm t (U (φ m) t) v) -
        η 0 * initialForm
          (smoothToLpDirichlet q
            (smoothDirichletBasisApproximation q (φ m) f₀)) =
        ∫ t in Icc (0 : ℝ) T,
          η t * weakForm t (U (φ m) t) v := by
    filter_upwards [eventually_mem_smoothDirichletBasisFinset_comp hφ i] with m him
    let s := smoothDirichletBasisFinset q (φ m)
    let j : s := ⟨i, him⟩
    let w : EuclideanSpace ℝ s := EuclideanSpace.single j 1
    let J := smoothDirichletBasisFinIncl s
    have hw : J w = smoothDirichletBasisFunction q i := by
      simpa only [s, j, w, J] using
        smoothDirichletBasisFinIncl_single s i him
    have hv : smoothToH1ComplDirichlet q (J w) = v := by
      rw [hw]
    have hmassIntegrable :=
      integrable_weighted_bilinear_of_apply_aestronglyMeasurable
        (U (φ m)) massForm hmassMeas hmassBound dη hdηMeas hdηBound v
    have hvariationIntegrable :=
      integrable_weighted_bilinear_of_apply_aestronglyMeasurable
        (U (φ m)) variationForm hvariationMeas hvariationBound
        η hηMeas hηBound v
    have hweakIntegrable :=
      integrable_weighted_bilinear_of_apply_aestronglyMeasurable
        (U (φ m)) weakForm hweakMeas hweakBound η hηMeas hηBound v
    have hmassEq :
        (fun t ↦ dη t * massForm t (U (φ m) t) v) =ᵐ[timeMeasure T]
          (fun t ↦ dη t * dirichletMass (G.metric t)
            (J (γ (φ m) t)) (J w)) := by
      filter_upwards [hUtie (φ m), ae_restrict_mem measurableSet_Icc] with t hU ht
      rw [hU, ← hv]
      exact congrArg (dη t * ·)
        (dirichletMassComplOnIcc_apply_smooth G.metric hCg hequiv
          Cv hCv0 hCvtop hvol ht (J (γ (φ m) t)) (J w))
    have hvariationEq :
        (fun t ↦ η t * variationForm t (U (φ m) t) v) =ᵐ[timeMeasure T]
          (fun t ↦ η t * dirichletMassVariation G.metric t
            (J (γ (φ m) t)) (J w)) := by
      filter_upwards [hUtie (φ m), hIco] with t hU ht
      rw [hU, ← hv]
      exact congrArg (η t * ·)
        (dirichletMassVariationComplOnIco_apply_smooth hG hreg Bv htrace
          hCg hequiv Cv hCv0 hCvtop hvol ht (J (γ (φ m) t)) (J w))
    have hweakEq :
        (fun t ↦ η t * weakForm t (U (φ m) t) v) =ᵐ[timeMeasure T]
          (fun t ↦ η t * dirichletWeakForm (G.metric t) (X t) (a t)
            (J (γ (φ m) t)) (J w)) := by
      filter_upwards [hUtie (φ m), hIco] with t hU ht
      rw [hU, ← hv]
      exact congrArg (η t * ·)
        (dirichletWeakFormComplOnIco_apply_smooth G.metric X a Bx hX
          hCg hequiv Cv hCv0 hCvtop hvol ht (J (γ (φ m) t)) (J w))
    have hmassInt : IntervalIntegrable
        (fun t ↦ dη t * dirichletMass (G.metric t)
          (J (γ (φ m) t)) (J w)) volume 0 T := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT.le]
      change Integrable (fun t ↦ dη t * dirichletMass (G.metric t)
        (J (γ (φ m) t)) (J w)) (volume.restrict (Icc (0 : ℝ) T))
      simpa only [timeMeasure] using hmassIntegrable.congr hmassEq
    have hvariationInt : IntervalIntegrable
        (fun t ↦ η t * dirichletMassVariation G.metric t
          (J (γ (φ m) t)) (J w)) volume 0 T := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT.le]
      change Integrable (fun t ↦ η t * dirichletMassVariation G.metric t
        (J (γ (φ m) t)) (J w)) (volume.restrict (Icc (0 : ℝ) T))
      simpa only [timeMeasure] using hvariationIntegrable.congr hvariationEq
    have hweakInt : IntervalIntegrable
        (fun t ↦ η t * dirichletWeakForm (G.metric t) (X t) (a t)
          (J (γ (φ m) t)) (J w)) volume 0 T := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hT.le]
      change Integrable (fun t ↦ η t *
        dirichletWeakForm (G.metric t) (X t) (a t)
          (J (γ (φ m) t)) (J w)) (volume.restrict (Icc (0 : ℝ) T))
      simpa only [timeMeasure] using hweakIntegrable.congr hweakEq
    have hgalerkin := dirichletGalerkin_integrated_weak_identity hG hT.le hreg
      (fun k : s ↦ smoothDirichletBasisFunction q k) X a
      (hγcont (φ m)) (hγweak (φ m)) w η dη hηcont hηderiv hηT
      (by simpa only [J, s, smoothDirichletBasisFinIncl] using hmassInt)
      (by simpa only [J, s, smoothDirichletBasisFinIncl] using hvariationInt)
      (by simpa only [J, s, smoothDirichletBasisFinIncl] using hweakInt)
    have hgalerkin' :
        -(∫ t in (0 : ℝ)..T, dη t * dirichletMass (G.metric t)
            (J (γ (φ m) t)) (J w)) -
          (∫ t in (0 : ℝ)..T, η t * dirichletMassVariation G.metric t
            (J (γ (φ m) t)) (J w)) -
          η 0 * dirichletMass (G.metric 0)
            (J (γ (φ m) 0)) (J w) =
          ∫ t in (0 : ℝ)..T, η t *
            dirichletWeakForm (G.metric t) (X t) (a t)
              (J (γ (φ m) t)) (J w) := by
      simpa only [J, s, smoothDirichletBasisFinIncl] using hgalerkin
    have hmassIntegral :
        (∫ t in (0 : ℝ)..T, dη t * dirichletMass (G.metric t)
          (J (γ (φ m) t)) (J w)) =
        ∫ t in Icc (0 : ℝ) T, dη t * massForm t (U (φ m) t) v := by
      rw [intervalIntegral.integral_of_le hT.le,
        ← MeasureTheory.integral_Icc_eq_integral_Ioc]
      simpa only [timeMeasure] using integral_congr_ae hmassEq.symm
    have hvariationIntegral :
        (∫ t in (0 : ℝ)..T, η t * dirichletMassVariation G.metric t
          (J (γ (φ m) t)) (J w)) =
        ∫ t in Icc (0 : ℝ) T, η t * variationForm t (U (φ m) t) v := by
      rw [intervalIntegral.integral_of_le hT.le,
        ← MeasureTheory.integral_Icc_eq_integral_Ioc]
      simpa only [timeMeasure] using integral_congr_ae hvariationEq.symm
    have hweakIntegral :
        (∫ t in (0 : ℝ)..T, η t * dirichletWeakForm (G.metric t) (X t) (a t)
          (J (γ (φ m) t)) (J w)) =
        ∫ t in Icc (0 : ℝ) T, η t * weakForm t (U (φ m) t) v := by
      rw [intervalIntegral.integral_of_le hT.le,
        ← MeasureTheory.integral_Icc_eq_integral_Ioc]
      simpa only [timeMeasure] using integral_congr_ae hweakEq.symm
    have hinitial : dirichletMass (G.metric 0)
        (J (γ (φ m) 0)) (J w) =
        initialForm (smoothToLpDirichlet q
          (smoothDirichletBasisApproximation q (φ m) f₀)) := by
      rw [hγ0 (φ m)]
      change dirichletMass (G.metric 0)
        (smoothDirichletBasisFinIncl s
          (smoothDirichletBasisCoordinates s f₀)) (J w) = _
      rw [show smoothDirichletBasisFinIncl s
          (smoothDirichletBasisCoordinates s f₀) =
          smoothDirichletBasisApproximation q (φ m) f₀ by
        simpa only [s] using smoothDirichletBasisFinIncl_coordinates (φ m) f₀]
      rw [hw]
      simpa only [initialForm, v, ContinuousLinearMap.flip_apply,
        H1ComplDirichletToLp_smoothToH1ComplDirichlet] using
        (dirichletMassLp_apply_smooth (G.metric 0) Cv hCvtop
        (hvol 0 ⟨le_rfl, hT.le⟩)
        (smoothDirichletBasisApproximation q (φ m) f₀)
        (smoothDirichletBasisFunction q i)).symm
    rw [hmassIntegral, hvariationIntegral, hweakIntegral, hinitial] at hgalerkin'
    exact hgalerkin'
  have hleftLimit := (hmassLimit.neg.sub hvariationLimit).sub hinitialLimit
  have hleftAsRight := hleftLimit.congr' hsequenceIdentity
  have hidentity := tendsto_nhds_unique hleftAsRight hweakLimit
  simpa only [massForm, variationForm, weakForm, initialForm, v,
    ContinuousLinearMap.flip_apply] using hidentity

private theorem exists_uniform_dirichlet_integrated_weak_solution_aux
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {T : ℝ} (hT : 0 < T) (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (X : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (hXcont : ContinuousOn
      (fun p : ℝ × M ↦
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle (I_half n) M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (a : ℝ → ℝ) (hacont : ContinuousOn a (Icc (0 : ℝ) T))
    (Bx Bv : ℝ)
    (hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx)
    (htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ Bv)
    (ha : ∀ t ∈ Ico (0 : ℝ) T, 0 ≤ a t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀
      (f₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q)),
    ∃ Cg : ℝ, ∃ Cv : ℝ≥0∞,
      ∃ hCg : 1 ≤ Cg,
      ∃ hequiv : ∀ t ∈ Icc (0 : ℝ) T, ∀ x : M,
        ∀ v : TangentSpace (I_half n) x,
          Cg⁻¹ * q.inner x v v ≤ (G.metric t).inner x v v ∧
            (G.metric t).inner x v v ≤ Cg * q.inner x v v,
      ∃ hCv0 : Cv ≠ 0, ∃ hCvtop : Cv ≠ ⊤,
      ∃ hvol : ∀ t ∈ Icc (0 : ℝ) T,
        riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t) ≤
          Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q,
      ∃ u : timeL2 (H1ComplDirichlet q) T, ‖u‖ ^ 2 ≤ C * ‖f₀‖ ^ 2 ∧
      ∀ (η dη : ℝ → ℝ),
        ContinuousOn η (Icc (0 : ℝ) T) →
        ContinuousOn dη (Icc (0 : ℝ) T) →
        (∀ t ∈ Ioo (0 : ℝ) T,
          HasDerivWithinAt η (dη t) (Ioi t) t) →
        η T = 0 →
        ∀ v : H1ComplDirichlet q,
          -(∫ t in Icc (0 : ℝ) T,
              dη t * dirichletMassComplOnIcc G.metric hCg hequiv
                Cv hCv0 hCvtop hvol t (u t) v) -
            (∫ t in Icc (0 : ℝ) T,
              η t * dirichletMassVariationComplOnIco hG hreg Bv htrace
                hCg hequiv Cv hCv0 hCvtop hvol t (u t) v) -
            η 0 * dirichletMassLp (G.metric 0) Cv hCvtop
              (hvol 0 ⟨le_rfl, hT.le⟩) f₀ (H1ComplDirichletToLp q v) =
            ∫ t in Icc (0 : ℝ) T,
              η t * dirichletWeakFormComplOnIco G.metric X a Bx hX
                hCg hequiv Cv hCv0 hCvtop hvol t (u t) v := by
  obtain ⟨C, hC, hsequence⟩ := exists_uniform_dirichletGalerkin_timeL2_sequence
    hG hT hreg X hXcont a hacont Bx Bv hX htrace ha
  refine ⟨C, hC, ?_⟩
  intro f₀
  obtain ⟨Cg, hCg, hequiv⟩ :=
    exists_metric_equivalence_bound_on_icc_of_metricFamilySmoothOn
      G.metric hG (fun _ ht ↦ D.regular_subset (hreg ht)) q
  obtain ⟨Cv, hCv0, hCvtop, hvolBoth⟩ := volume_uniform_equiv
    (I := I_half n) (M := M) q G.metric isCompact_Icc
    (fun x₀ i j ↦ hG.chartGramMatrix_continuousOn hreg x₀ i j)
  let hvol : ∀ t ∈ Icc (0 : ℝ) T,
      riemannianVolumeMeasure (I := I_half n) (M := M) (G.metric t) ≤
        Cv • riemannianVolumeMeasure (I := I_half n) (M := M) q :=
    fun t ht ↦ (hvolBoth t ht).1
  obtain ⟨γ, U, hseq⟩ := hsequence f₀
  have hUnorm : ∀ m, ‖U m‖ ≤ Real.sqrt (C * ‖f₀‖ ^ 2) := by
    intro m
    rw [← Real.sqrt_sq (norm_nonneg (U m))]
    exact Real.sqrt_le_sqrt (hseq m).2.2.2.2
  obtain ⟨φ, u, hφ, hUweak⟩ :=
    exists_weakly_convergent_subsequence_timeL2_H1ComplDirichlet q U hUnorm
  have hunorm : ‖u‖ ^ 2 ≤ C * ‖f₀‖ ^ 2 := by
    have hs : ‖u‖ ^ 2 ≤ Real.sqrt (C * ‖f₀‖ ^ 2) * ‖u‖ := by
      have hlim : Tendsto (fun m => inner ℝ (U (φ m)) u) atTop (𝓝 (‖u‖ ^ 2)) := by
        simpa only [real_inner_self_eq_norm_sq] using hUweak u
      apply le_of_tendsto hlim
      exact Filter.Eventually.of_forall fun m => (real_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_right (hUnorm (φ m)) (norm_nonneg _))
    have hr : 0 ≤ Real.sqrt (C * ‖f₀‖ ^ 2) := Real.sqrt_nonneg _
    have hle : ‖u‖ ≤ Real.sqrt (C * ‖f₀‖ ^ 2) := by nlinarith [norm_nonneg u]
    have hsq := (sq_le_sq₀ (norm_nonneg _) hr).2 hle
    rwa [Real.sq_sqrt (mul_nonneg hC (sq_nonneg _))] at hsq
  obtain ⟨A, hAbound⟩ := isCompact_Icc.exists_bound_of_continuousOn hacont
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT.le⟩
  have hA : 0 ≤ A := (norm_nonneg (a 0)).trans (hAbound 0 hzero)
  have haBound : ∀ t ∈ Ico (0 : ℝ) T, |a t| ≤ A := by
    intro t ht
    rw [← Real.norm_eq_abs]
    exact hAbound t ⟨ht.1, ht.2.le⟩
  refine ⟨Cg, Cv, hCg, hequiv, hCv0, hCvtop, hvol, u, hunorm, ?_⟩
  intro η dη hηcont hdηcont hηderiv hηT v
  let massForm := dirichletMassComplOnIcc G.metric hCg hequiv
    Cv hCv0 hCvtop hvol
  let variationForm := dirichletMassVariationComplOnIco hG hreg Bv htrace
    hCg hequiv Cv hCv0 hCvtop hvol
  let weakForm := dirichletWeakFormComplOnIco G.metric X a Bx hX
    hCg hequiv Cv hCv0 hCvtop hvol
  obtain ⟨Kη, hKη⟩ := isCompact_Icc.exists_bound_of_continuousOn hηcont
  obtain ⟨Kdη, hKdη⟩ := isCompact_Icc.exists_bound_of_continuousOn hdηcont
  have hηMeas : AEStronglyMeasurable η (timeMeasure T) := by
    unfold timeMeasure
    exact hηcont.aestronglyMeasurable measurableSet_Icc
  have hdηMeas : AEStronglyMeasurable dη (timeMeasure T) := by
    unfold timeMeasure
    exact hdηcont.aestronglyMeasurable measurableSet_Icc
  have hηBound : ∀ᵐ t ∂(timeMeasure T), ‖η t‖ ≤ Kη := by
    unfold timeMeasure
    exact (ae_restrict_iff' measurableSet_Icc).2
      (Eventually.of_forall fun t ht ↦ hKη t ht)
  have hdηBound : ∀ᵐ t ∂(timeMeasure T), ‖dη t‖ ≤ Kdη := by
    unfold timeMeasure
    exact (ae_restrict_iff' measurableSet_Icc).2
      (Eventually.of_forall fun t ht ↦ hKdη t ht)
  have hmassMeas : ∀ y z, AEStronglyMeasurable
      (fun t ↦ massForm t y z) (timeMeasure T) := by
    intro y z
    exact dirichletMassComplOnIcc_aestronglyMeasurable hG hreg hCg
      hequiv Cv hCv0 hCvtop hvol y z
  have hvariationMeas : ∀ y z, AEStronglyMeasurable
      (fun t ↦ variationForm t y z) (timeMeasure T) := by
    intro y z
    exact dirichletMassVariationComplOnIco_aestronglyMeasurable hG hreg
      Bv htrace hCg hequiv Cv hCv0 hCvtop hvol y z
  have hweakMeas : ∀ y z, AEStronglyMeasurable
      (fun t ↦ weakForm t y z) (timeMeasure T) := by
    intro y z
    exact dirichletWeakFormComplOnIco_aestronglyMeasurable hG hreg X
      hXcont a hacont Bx hX hCg hequiv Cv hCv0 hCvtop hvol y z
  have hmassBound :=
    Eventually.of_forall (f := MeasureTheory.ae (timeMeasure T)) fun t ↦
      norm_dirichletMassComplOnIcc_le
        G.metric hCg hequiv Cv hCv0 hCvtop hvol t
  have hvariationBound :=
    Eventually.of_forall (f := MeasureTheory.ae (timeMeasure T)) fun t ↦
      norm_dirichletMassVariationComplOnIco_le
        hG hreg Bv htrace hCg hequiv Cv hCv0 hCvtop hvol t
  have hweakBound :=
    Eventually.of_forall (f := MeasureTheory.ae (timeMeasure T)) fun t ↦
      norm_dirichletWeakFormComplOnIco_le
        G.metric X a A Bx hA haBound hX hCg hequiv Cv hCv0 hCvtop hvol t
  let initial : H1ComplDirichlet q →L[ℝ] ℝ :=
    η 0 • ((dirichletMassLp (G.metric 0) Cv hCvtop (hvol 0 hzero) f₀).comp
      (H1ComplDirichletToLp q))
  have hbasis : ∀ i : SmoothDirichletBasisIndex q,
      -(∫ t in Icc (0 : ℝ) T,
          dη t * massForm t (u t)
            (smoothToH1ComplDirichlet q (smoothDirichletBasisFunction q i))) -
        (∫ t in Icc (0 : ℝ) T,
          η t * variationForm t (u t)
            (smoothToH1ComplDirichlet q (smoothDirichletBasisFunction q i))) -
        initial (smoothToH1ComplDirichlet q (smoothDirichletBasisFunction q i)) =
        ∫ t in Icc (0 : ℝ) T,
          η t * weakForm t (u t)
            (smoothToH1ComplDirichlet q (smoothDirichletBasisFunction q i)) := by
    intro i
    have hi := dirichlet_weak_limit_identity_basis hG hT hreg X hXcont
      a hacont Bx Bv A hA haBound hX htrace f₀ hCg hequiv Cv hCv0 hCvtop
      hvol γ U φ u hφ hUweak
      (fun m ↦ (hseq m).1) (fun m ↦ (hseq m).2.1)
      (fun m ↦ (hseq m).2.2.1) (fun m ↦ (hseq m).2.2.2.1)
      i η dη hηcont hdηcont hηderiv hηT
    simpa only [massForm, variationForm, weakForm, initial,
      smul_apply, ContinuousLinearMap.comp_apply,
      smul_eq_mul] using hi
  have hall := weighted_bilinear_identity_of_dense_span
    (fun i ↦ smoothToH1ComplDirichlet q (smoothDirichletBasisFunction q i))
    (dense_span_smoothToH1ComplDirichlet_smoothDirichletBasisFunction q)
    u massForm variationForm weakForm hmassMeas hvariationMeas hweakMeas
    hmassBound hvariationBound hweakBound dη η hdηMeas hηMeas
    hdηBound hηBound initial hbasis v
  simpa only [massForm, variationForm, weakForm, initial,
    smul_apply, ContinuousLinearMap.comp_apply,
    smul_eq_mul] using hall

theorem exists_uniform_dirichlet_integrated_weak_solution_norm_sq_le
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {T : ℝ} (hT : 0 < T) (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (X : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (hXcont : ContinuousOn
      (fun p : ℝ × M ↦
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle (I_half n) M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (a : ℝ → ℝ) (hacont : ContinuousOn a (Icc (0 : ℝ) T))
    (Bx Bv : ℝ)
    (hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx)
    (htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ Bv)
    (ha : ∀ t ∈ Ico (0 : ℝ) T, 0 ≤ a t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀
      (f₀ : Lp ℝ 2 (riemannianVolumeMeasure (I := I_half n) (M := M) q)),
    ∃ u : timeL2 (H1ComplDirichlet q) T,
      IsIntegratedWeakSolution hG hT.le hreg X a Bx Bv hX htrace f₀ u ∧
      ‖u‖ ^ 2 ≤ C * ‖f₀‖ ^ 2 := by
  obtain ⟨C, hC, hsolution⟩ := exists_uniform_dirichlet_integrated_weak_solution_aux
    hG hT hreg X hXcont a hacont Bx Bv hX htrace ha
  refine ⟨C, hC, ?_⟩
  intro f₀
  obtain ⟨Cg, Cv, hCg, hequiv, hCv0, hCvtop, hvol, u, hubound, hu⟩ := hsolution f₀
  exact ⟨u, ⟨Cg, Cv, hCg, hequiv, hCv0, hCvtop, hvol, hu⟩, hubound⟩

theorem exists_dirichlet_integrated_weak_solution
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : RealTimeInterval}
    {G : MetricConnectionFamilyOn (I := I_half n) (M := M) D}
    (hG : MetricFamilySmoothOn (I := I_half n) (M := M) D G.metric)
    {T : ℝ} (hT : 0 < T) (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    (X : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (hXcont : ContinuousOn
      (fun p : ℝ × M ↦
        (TotalSpace.mk' (EuclideanSpace ℝ (Fin n)) p.2 (X p.1 p.2) :
          TangentBundle (I_half n) M))
      (Icc (0 : ℝ) T ×ˢ (Set.univ : Set M)))
    (a : ℝ → ℝ) (hacont : ContinuousOn a (Icc (0 : ℝ) T))
    (Bx Bv : ℝ)
    (hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx)
    (htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ Bv)
    (ha : ∀ t ∈ Ico (0 : ℝ) T, 0 ≤ a t)
    (f₀ : Lp ℝ 2
      (riemannianVolumeMeasure (I := I_half n) (M := M) q)) :
    ∃ u : timeL2 (H1ComplDirichlet q) T,
      IsIntegratedWeakSolution hG hT.le hreg X a Bx Bv hX htrace f₀ u := by
  obtain ⟨C, hC, hsolution⟩ := exists_uniform_dirichlet_integrated_weak_solution_norm_sq_le
    hG hT hreg X hXcont a hacont Bx Bv hX htrace ha
  obtain ⟨u, hu, _⟩ := hsolution f₀
  exact ⟨u, hu⟩

end DifferentialGeometry.Analysis.Parabolic.Dirichlet

end
