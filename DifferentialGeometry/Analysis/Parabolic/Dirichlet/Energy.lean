import DifferentialGeometry.Analysis.Elliptic.WithBoundary.DirichletSmoothMul
import DifferentialGeometry.Analysis.Elliptic.MetricBounds
import DifferentialGeometry.Analysis.Integration.Measure.FamilyLocal
import DifferentialGeometry.Analysis.Parabolic.Dirichlet.Galerkin

noncomputable section

open Bundle Manifold MeasureTheory Set
open scoped Manifold Topology ContDiff ENNReal NNReal
  RealInnerProductSpace InnerProductSpace BigOperators

namespace DifferentialGeometry.Analysis.Parabolic.Dirichlet

open DifferentialGeometry.Analysis.Laplacian.WithBoundary.Dirichlet
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Operator

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

def dirichletMassVariation
    {q : SmoothRiemannianMetric (I_half n) M}
    (g : ℝ → SmoothRiemannianMetric (I_half n) M) (t : ℝ)
    (u v : SmoothScalarDirichlet q) : ℝ :=
  ∫ x, (1 / 2 : ℝ) * traceTimeDerivMetric (I := I_half n) g t x *
      (u.toFun x * v.toFun x)
    ∂(riemannianVolumeMeasure (I := I_half n) (M := M) (g t))

theorem hasDerivAt_dirichletMass
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn
      (I := I_half n) (M := M) D}
    (hG : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn
      (I := I_half n) (M := M) D G.metric)
    {t : ℝ} (ht : t ∈ D.regular)
    (u v : SmoothScalarDirichlet q) :
    HasDerivAt (fun s => dirichletMass (G.metric s) u v)
      (dirichletMassVariation G.metric t u v) t := by
  have hfun : ContMDiff
      ((modelWithCornersSelf ℝ ℝ).prod (I_half n))
      (modelWithCornersSelf ℝ ℝ) ∞
      (fun p : ℝ × M => u.toFun p.2 * v.toFun p.2) :=
    (u.smooth.comp contMDiff_snd).mul (v.smooth.comp contMDiff_snd)
  have hbase := first_var_joint (I := I_half n) (M := M)
    (f := fun _ x => u.toFun x * v.toFun x)
    D.regular_isOpen ht
    (fun x₀ i j => hG.chartGramMatrix_contDiffOn (Set.Subset.rfl) x₀ i j)
    hfun.contMDiffOn
  change HasDerivAt
    (fun s => ∫ x, u.toFun x * v.toFun x
      ∂(riemannianMeasureFamily (I := I_half n) (M := M) G.metric s)) _ t
  refine hbase.congr_deriv ?_
  unfold dirichletMassVariation
  apply integral_congr_ae
  filter_upwards with x
  rw [show deriv (fun _ : ℝ => u.toFun x * v.toFun x) t = 0 by
    exact (hasDerivAt_const t (u.toFun x * v.toFun x)).deriv]
  ring

theorem dirichletMassVariation_add_left
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn
      (I := I_half n) (M := M) D}
    (hG : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn
      (I := I_half n) (M := M) D G.metric)
    {t : ℝ} (ht : t ∈ D.regular)
    (u₁ u₂ v : SmoothScalarDirichlet q) :
    dirichletMassVariation G.metric t (u₁ + u₂) v =
      dirichletMassVariation G.metric t u₁ v +
        dirichletMassVariation G.metric t u₂ v := by
  have hleft := hasDerivAt_dirichletMass hG ht (u₁ + u₂) v
  have hright : HasDerivAt
      (fun s => dirichletMass (G.metric s) u₁ v +
        dirichletMass (G.metric s) u₂ v)
      (dirichletMassVariation G.metric t u₁ v +
        dirichletMassVariation G.metric t u₂ v) t := by
    exact ((hasDerivAt_dirichletMass hG ht u₁ v).add
      (hasDerivAt_dirichletMass hG ht u₂ v)).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun _ => rfl)
  have hfun : (fun s => dirichletMass (G.metric s) (u₁ + u₂) v) =
      fun s => dirichletMass (G.metric s) u₁ v +
        dirichletMass (G.metric s) u₂ v := by
    funext s
    exact dirichletMass_add_left (G.metric s) u₁ u₂ v
  rw [← hleft.deriv, ← hright.deriv, hfun]

theorem dirichletMassVariation_smul_left
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn
      (I := I_half n) (M := M) D}
    (hG : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn
      (I := I_half n) (M := M) D G.metric)
    {t : ℝ} (ht : t ∈ D.regular)
    (c : ℝ) (u v : SmoothScalarDirichlet q) :
    dirichletMassVariation G.metric t (c • u) v =
      c * dirichletMassVariation G.metric t u v := by
  have hleft := hasDerivAt_dirichletMass hG ht (c • u) v
  have hright : HasDerivAt
      (fun s => c * dirichletMass (G.metric s) u v)
      (c * dirichletMassVariation G.metric t u v) t := by
    simpa only using (hasDerivAt_dirichletMass hG ht u v).const_mul c
  have hfun : (fun s => dirichletMass (G.metric s) (c • u) v) =
      fun s => c * dirichletMass (G.metric s) u v := by
    funext s
    exact dirichletMass_smul_left (G.metric s) c u v
  rw [← hleft.deriv, ← hright.deriv, hfun]

theorem dirichletMassVariation_symm
    {q : SmoothRiemannianMetric (I_half n) M}
    (g : ℝ → SmoothRiemannianMetric (I_half n) M) (t : ℝ)
    (u v : SmoothScalarDirichlet q) :
    dirichletMassVariation g t u v = dirichletMassVariation g t v u := by
  unfold dirichletMassVariation
  apply integral_congr_ae
  filter_upwards with x
  rw [mul_comm (u.toFun x)]

theorem dirichletMassVariation_add_right
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn
      (I := I_half n) (M := M) D}
    (hG : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn
      (I := I_half n) (M := M) D G.metric)
    {t : ℝ} (ht : t ∈ D.regular)
    (u v₁ v₂ : SmoothScalarDirichlet q) :
    dirichletMassVariation G.metric t u (v₁ + v₂) =
      dirichletMassVariation G.metric t u v₁ +
        dirichletMassVariation G.metric t u v₂ := by
  rw [dirichletMassVariation_symm,
    dirichletMassVariation_add_left hG ht,
    dirichletMassVariation_symm G.metric t v₁ u,
    dirichletMassVariation_symm G.metric t v₂ u]

theorem dirichletMassVariation_smul_right
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn
      (I := I_half n) (M := M) D}
    (hG : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn
      (I := I_half n) (M := M) D G.metric)
    {t : ℝ} (ht : t ∈ D.regular)
    (c : ℝ) (u v : SmoothScalarDirichlet q) :
    dirichletMassVariation G.metric t u (c • v) =
      c * dirichletMassVariation G.metric t u v := by
  rw [dirichletMassVariation_symm,
    dirichletMassVariation_smul_left hG ht,
    dirichletMassVariation_symm G.metric t v u]

private theorem dirichletMass_sum_left
    {q : SmoothRiemannianMetric (I_half n) M}
    {h : SmoothRiemannianMetric (I_half n) M}
    {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) (u : ι → SmoothScalarDirichlet q)
    (v : SmoothScalarDirichlet q) :
    dirichletMass h (∑ i ∈ s, c i • u i) v =
      ∑ i ∈ s, c i * dirichletMass h (u i) v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      unfold dirichletMass
      simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        dirichletMass_add_left, dirichletMass_smul_left, ih]

private theorem dirichletMass_sum_right
    {q : SmoothRiemannianMetric (I_half n) M}
    {h : SmoothRiemannianMetric (I_half n) M}
    {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) (u : SmoothScalarDirichlet q)
    (v : ι → SmoothScalarDirichlet q) :
    dirichletMass h u (∑ i ∈ s, c i • v i) =
      ∑ i ∈ s, c i * dirichletMass h u (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      unfold dirichletMass
      simp
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha,
        dirichletMass_add_right, dirichletMass_smul_right, ih]

private theorem dirichletMass_finIncl
    {q : SmoothRiemannianMetric (I_half n) M}
    {h : SmoothRiemannianMetric (I_half n) M}
    {ι : Type*} [Fintype ι]
    (φ : ι → SmoothScalarDirichlet q) (u v : EuclideanSpace ℝ ι) :
    dirichletMass h (dirichletFinIncl φ u) (dirichletFinIncl φ v) =
      ∑ i, ∑ j, u.ofLp i * v.ofLp j * dirichletMass h (φ i) (φ j) := by
  classical
  rw [dirichletFinIncl_apply, dirichletFinIncl_apply,
    dirichletMass_sum_left Finset.univ]
  apply Finset.sum_congr rfl
  intro i _
  rw [dirichletMass_sum_right Finset.univ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem dirichletMassVariation_sum_left
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn
      (I := I_half n) (M := M) D}
    (hG : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn
      (I := I_half n) (M := M) D G.metric)
    {t : ℝ} (ht : t ∈ D.regular)
    {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) (u : ι → SmoothScalarDirichlet q)
    (v : SmoothScalarDirichlet q) :
    dirichletMassVariation G.metric t (∑ i ∈ s, c i • u i) v =
      ∑ i ∈ s, c i * dirichletMassVariation G.metric t (u i) v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      unfold dirichletMassVariation
      simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        dirichletMassVariation_add_left hG ht,
        dirichletMassVariation_smul_left hG ht, ih]

private theorem dirichletMassVariation_sum_right
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn
      (I := I_half n) (M := M) D}
    (hG : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn
      (I := I_half n) (M := M) D G.metric)
    {t : ℝ} (ht : t ∈ D.regular)
    {ι : Type*}
    (s : Finset ι) (c : ι → ℝ) (u : SmoothScalarDirichlet q)
    (v : ι → SmoothScalarDirichlet q) :
    dirichletMassVariation G.metric t u (∑ i ∈ s, c i • v i) =
      ∑ i ∈ s, c i * dirichletMassVariation G.metric t u (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp only [Finset.sum_empty]
      unfold dirichletMassVariation
      simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        dirichletMassVariation_add_right hG ht,
        dirichletMassVariation_smul_right hG ht, ih]

private theorem dirichletMassVariation_finIncl
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn
      (I := I_half n) (M := M) D}
    (hG : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn
      (I := I_half n) (M := M) D G.metric)
    {t : ℝ} (ht : t ∈ D.regular)
    {ι : Type*} [Fintype ι]
    (φ : ι → SmoothScalarDirichlet q) (u v : EuclideanSpace ℝ ι) :
    dirichletMassVariation G.metric t
        (dirichletFinIncl φ u) (dirichletFinIncl φ v) =
      ∑ i, ∑ j, u.ofLp i * v.ofLp j *
        dirichletMassVariation G.metric t (φ i) (φ j) := by
  classical
  rw [dirichletFinIncl_apply, dirichletFinIncl_apply,
    dirichletMassVariation_sum_left hG ht Finset.univ]
  apply Finset.sum_congr rfl
  intro i _
  rw [dirichletMassVariation_sum_right hG ht Finset.univ, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem dirichletMass_finIncl_left
    {q : SmoothRiemannianMetric (I_half n) M}
    {h : SmoothRiemannianMetric (I_half n) M}
    {ι : Type*} [Fintype ι]
    (φ : ι → SmoothScalarDirichlet q) (u : EuclideanSpace ℝ ι)
    (ψ : SmoothScalarDirichlet q) :
    dirichletMass h (dirichletFinIncl φ u) ψ =
      ∑ i, u.ofLp i * dirichletMass h (φ i) ψ := by
  classical
  rw [dirichletFinIncl_apply, dirichletMass_sum_left Finset.univ]

private theorem dirichletMassVariation_finIncl_left
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn
      (I := I_half n) (M := M) D}
    (hG : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn
      (I := I_half n) (M := M) D G.metric)
    {t : ℝ} (ht : t ∈ D.regular)
    {ι : Type*} [Fintype ι]
    (φ : ι → SmoothScalarDirichlet q) (u : EuclideanSpace ℝ ι)
    (ψ : SmoothScalarDirichlet q) :
    dirichletMassVariation G.metric t (dirichletFinIncl φ u) ψ =
      ∑ i, u.ofLp i * dirichletMassVariation G.metric t (φ i) ψ := by
  classical
  rw [dirichletFinIncl_apply,
    dirichletMassVariation_sum_left hG ht Finset.univ]

theorem hasDerivWithinAt_dirichletFinIncl_mass_left
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn
      (I := I_half n) (M := M) D}
    (hG : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn
      (I := I_half n) (M := M) D G.metric)
    {t : ℝ} (ht : t ∈ D.regular)
    {ι : Type*} [Fintype ι]
    (φ : ι → SmoothScalarDirichlet q) (ψ : SmoothScalarDirichlet q)
    {γ : ℝ → EuclideanSpace ℝ ι} {v : EuclideanSpace ℝ ι}
    {S : Set ℝ} (hγ : HasDerivWithinAt γ v S t) :
    HasDerivWithinAt
      (fun s => dirichletMass (G.metric s) (dirichletFinIncl φ (γ s)) ψ)
      (dirichletMass (G.metric t) (dirichletFinIncl φ v) ψ +
        dirichletMassVariation G.metric t (dirichletFinIncl φ (γ t)) ψ) S t := by
  classical
  have hcoord (i : ι) : HasDerivWithinAt
      (fun s => (γ s).ofLp i) (v.ofLp i) S t := by
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivWithinAt t hγ
  have hterm (i : ι) : HasDerivWithinAt
      (fun s => (γ s).ofLp i * dirichletMass (G.metric s) (φ i) ψ)
      (v.ofLp i * dirichletMass (G.metric t) (φ i) ψ +
        (γ t).ofLp i * dirichletMassVariation G.metric t (φ i) ψ) S t := by
    have hmass := (hasDerivAt_dirichletMass hG ht (φ i) ψ).hasDerivWithinAt
      (s := S)
    exact (hcoord i).mul hmass
  have hsum₀ := HasDerivWithinAt.sum (u := Finset.univ) fun i _ => hterm i
  have hsum : HasDerivWithinAt
      (fun s => ∑ i, (γ s).ofLp i * dirichletMass (G.metric s) (φ i) ψ)
      (∑ i, (v.ofLp i * dirichletMass (G.metric t) (φ i) ψ +
        (γ t).ofLp i * dirichletMassVariation G.metric t (φ i) ψ)) S t := by
    exact hsum₀.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => by
        simp only [Finset.sum_apply]) (by simp only [Finset.sum_apply])
  refine (hsum.congr_of_eventuallyEq ?_ ?_).congr_deriv ?_
  · filter_upwards with s
    exact dirichletMass_finIncl_left φ (γ s) ψ
  · exact dirichletMass_finIncl_left φ (γ t) ψ
  · rw [dirichletMass_finIncl_left φ v ψ,
      dirichletMassVariation_finIncl_left hG ht φ (γ t) ψ,
      Finset.sum_add_distrib]

theorem hasDerivWithinAt_dirichletFinIncl_mass
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn
      (I := I_half n) (M := M) D}
    (hG : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn
      (I := I_half n) (M := M) D G.metric)
    {t : ℝ} (ht : t ∈ D.regular)
    {ι : Type*} [Fintype ι]
    (φ : ι → SmoothScalarDirichlet q)
    {γ : ℝ → EuclideanSpace ℝ ι} {v : EuclideanSpace ℝ ι}
    {S : Set ℝ} (hγ : HasDerivWithinAt γ v S t) :
    HasDerivWithinAt
      (fun s => dirichletMass (G.metric s)
        (dirichletFinIncl φ (γ s)) (dirichletFinIncl φ (γ s)))
      (2 * dirichletMass (G.metric t)
          (dirichletFinIncl φ v) (dirichletFinIncl φ (γ t)) +
        dirichletMassVariation G.metric t
          (dirichletFinIncl φ (γ t)) (dirichletFinIncl φ (γ t))) S t := by
  classical
  have hcoord (i : ι) : HasDerivWithinAt
      (fun s => (γ s).ofLp i) (v.ofLp i) S t := by
    exact (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp_hasDerivWithinAt t hγ
  have hterm (i j : ι) : HasDerivWithinAt
      (fun s => (γ s).ofLp i * (γ s).ofLp j *
        dirichletMass (G.metric s) (φ i) (φ j))
      ((v.ofLp i * (γ t).ofLp j + (γ t).ofLp i * v.ofLp j) *
          dirichletMass (G.metric t) (φ i) (φ j) +
        (γ t).ofLp i * (γ t).ofLp j *
          dirichletMassVariation G.metric t (φ i) (φ j)) S t := by
    have hcoeff := (hcoord i).mul (hcoord j)
    have hmass := (hasDerivAt_dirichletMass hG ht (φ i) (φ j)).hasDerivWithinAt
      (s := S)
    exact (hcoeff.mul hmass).congr_deriv (by
      simp only [Pi.mul_apply])
  have hsum₀ := HasDerivWithinAt.sum (u := Finset.univ) fun i _ =>
    HasDerivWithinAt.sum (u := Finset.univ) fun j _ => hterm i j
  have hsum : HasDerivWithinAt
      (fun s => ∑ i, ∑ j, (γ s).ofLp i * (γ s).ofLp j *
        dirichletMass (G.metric s) (φ i) (φ j))
      (∑ i, ∑ j,
        ((v.ofLp i * (γ t).ofLp j + (γ t).ofLp i * v.ofLp j) *
            dirichletMass (G.metric t) (φ i) (φ j) +
          (γ t).ofLp i * (γ t).ofLp j *
            dirichletMassVariation G.metric t (φ i) (φ j))) S t := by
    exact hsum₀.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun _ => by
        simp only [Finset.sum_apply]) (by simp only [Finset.sum_apply])
  refine (hsum.congr_of_eventuallyEq ?_ ?_).congr_deriv ?_
  · filter_upwards with s
    exact dirichletMass_finIncl φ (γ s) (γ s)
  · exact dirichletMass_finIncl φ (γ t) (γ t)
  · rw [dirichletMass_finIncl φ v (γ t),
      dirichletMassVariation_finIncl hG ht φ (γ t) (γ t)]
    have hcross :
        (∑ i, ∑ j, (γ t).ofLp i * v.ofLp j *
          dirichletMass (G.metric t) (φ i) (φ j)) =
        ∑ i, ∑ j, v.ofLp i * (γ t).ofLp j *
          dirichletMass (G.metric t) (φ i) (φ j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [dirichletMass_symm (G.metric t) (φ j) (φ i)]
      ring
    simp_rw [add_mul, Finset.sum_add_distrib]
    rw [hcross]
    ring

theorem hasDerivWithinAt_dirichletGalerkin_mass
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn
      (I := I_half n) (M := M) D}
    (hG : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn
      (I := I_half n) (M := M) D G.metric)
    {t : ℝ} (ht : t ∈ D.regular)
    {ι : Type*} [Fintype ι]
    (φ : ι → SmoothScalarDirichlet q)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ)
    {γ : ℝ → EuclideanSpace ℝ ι} {v : EuclideanSpace ℝ ι}
    {S : Set ℝ} (hγ : HasDerivWithinAt γ v S t)
    (hweak : dirichletFinMass (G.metric t) (dirichletFinIncl φ) v =
      dirichletFinWeakForm (G.metric t) X a (dirichletFinIncl φ) (γ t)) :
    HasDerivWithinAt
      (fun s => dirichletMass (G.metric s)
        (dirichletFinIncl φ (γ s)) (dirichletFinIncl φ (γ s)))
      (2 * dirichletWeakForm (G.metric t) X a
          (dirichletFinIncl φ (γ t)) (dirichletFinIncl φ (γ t)) +
        dirichletMassVariation G.metric t
          (dirichletFinIncl φ (γ t)) (dirichletFinIncl φ (γ t))) S t := by
  have hderiv := hasDerivWithinAt_dirichletFinIncl_mass hG ht φ hγ
  apply hderiv.congr_deriv
  have heval := congrArg (fun L : EuclideanSpace ℝ ι →L[ℝ] ℝ => L (γ t)) hweak
  have heval' : dirichletMass (G.metric t)
      (dirichletFinIncl φ v) (dirichletFinIncl φ (γ t)) =
    dirichletWeakForm (G.metric t) X a
      (dirichletFinIncl φ (γ t)) (dirichletFinIncl φ (γ t)) := by
    simpa only [dirichletFinMass_apply, dirichletFinWeakForm_apply] using heval
  rw [heval']

theorem abs_dirichletMassVariation_smoothScalarDirichletMul_le
    {q : SmoothRiemannianMetric (I_half n) M}
    (g : ℝ → SmoothRiemannianMetric (I_half n) M) (t B : ℝ)
    (htrace : ∀ x : M, |traceTimeDerivMetric (I := I_half n) g t x| ≤ B)
    (φ : C^∞⟮I_half n, M; ℝ⟯) {Cφ : ℝ}
    (hφ : ∀ x : M, |φ x| ≤ Cφ)
    (u : SmoothScalarDirichlet q) :
    |dirichletMassVariation g t u (smoothScalarDirichletMul q φ u)| ≤
      ((1 / 2) * B * Cφ) * dirichletMass (g t) u u := by
  let μ := riemannianVolumeMeasure (I := I_half n) (M := M) (g t)
  have hright : Integrable
      (fun x : M => ((1 / 2) * B * Cφ) * (u.toFun x * u.toFun x)) μ :=
    (dirichletMass_integrable (g t) u u).const_mul _
  have hpoint (x : M) :
      |(1 / 2 : ℝ) * traceTimeDerivMetric (I := I_half n) g t x *
          (u.toFun x * (smoothScalarDirichletMul q φ u).toFun x)| ≤
        ((1 / 2) * B * Cφ) * (u.toFun x * u.toFun x) := by
    rw [smoothScalarDirichletMul_toFun]
    rw [show u.toFun x * (φ x * u.toFun x) =
      φ x * (u.toFun x * u.toFun x) by ring]
    rw [abs_mul, abs_mul, abs_mul, abs_mul_self,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have hB := (abs_nonneg _).trans (htrace x)
    have hbound := mul_le_mul (htrace x) (hφ x) (abs_nonneg _) hB
    have hmul := mul_le_mul_of_nonneg_right hbound (mul_self_nonneg (u.toFun x))
    nlinarith
  unfold dirichletMassVariation dirichletMass
  change |∫ x, (1 / 2 : ℝ) * traceTimeDerivMetric (I := I_half n) g t x *
      (u.toFun x * (smoothScalarDirichletMul q φ u).toFun x) ∂μ| ≤
    ((1 / 2) * B * Cφ) * ∫ x, u.toFun x * u.toFun x ∂μ
  calc
    _ ≤ ∫ x, |(1 / 2 : ℝ) * traceTimeDerivMetric (I := I_half n) g t x *
        (u.toFun x * (smoothScalarDirichletMul q φ u).toFun x)| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, ((1 / 2) * B * Cφ) * (u.toFun x * u.toFun x) ∂μ :=
      integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun _ => abs_nonneg _)
        hright (Filter.Eventually.of_forall hpoint)
    _ = _ := by rw [integral_const_mul]

theorem abs_dirichletMassVariation_self_le
    {q : SmoothRiemannianMetric (I_half n) M}
    (g : ℝ → SmoothRiemannianMetric (I_half n) M) (t B : ℝ)
    (htrace : ∀ x : M, |traceTimeDerivMetric (I := I_half n) g t x| ≤ B)
    (u : SmoothScalarDirichlet q) :
    |dirichletMassVariation g t u u| ≤
      (1 / 2) * B * dirichletMass (g t) u u := by
  have hmul : smoothScalarDirichletMul q (1 : C^∞⟮I_half n, M; ℝ⟯) u = u := by
    ext x
    change (1 : ℝ) * u.toFun x = u.toFun x
    exact one_mul _
  have hbound := abs_dirichletMassVariation_smoothScalarDirichletMul_le
    g t B htrace (1 : C^∞⟮I_half n, M; ℝ⟯) (Cφ := 1)
      (fun x => by change |(1 : ℝ)| ≤ 1; norm_num) u
  simpa only [hmul, mul_one] using hbound

omit [T2Space M] [CompactSpace M] in
private theorem abs_two_mul_metric_inner_le
    (h : SmoothRiemannianMetric (I_half n) M) (x : M)
    (A B : TangentSpace (I_half n) x) :
    |2 * h.inner x A B| ≤ h.inner x A A + h.inner x B B := by
  have hsub := DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg
    (I := I_half n) (M := M) h x (A - B)
  have hadd := DifferentialGeometry.Analysis.Laplacian.metric_inner_self_nonneg
    (I := I_half n) (M := M) h x (A + B)
  simp only [map_sub, sub_apply, map_add, add_apply] at hsub hadd
  rw [h.symm x B A] at hsub hadd
  rw [abs_le]
  constructor <;> linarith

private theorem two_mul_abs_dirichletDrift_le_add
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (C : ℝ)
    (hX : ∀ x : M, h.inner x (X x) (X x) ≤ C)
    (u v : SmoothScalarDirichlet q) :
    2 * |dirichletDrift h X u v| ≤
      dirichletEnergy h u u + C * dirichletMass h v v := by
  let μ := riemannianVolumeMeasure (I := I_half n) (M := M) h
  have henergy := dirichletEnergy_integrable h u u
  have hmass := (dirichletMass_integrable h v v).const_mul C
  have hright := henergy.add hmass
  have hpoint : ∀ x : M,
      |2 * (h.inner x (X x) (gradFun (I := I_half n) h u.toFun x) * v.toFun x)| ≤
        h.inner x
          (gradFun (I := I_half n) h u.toFun x)
          (gradFun (I := I_half n) h u.toFun x) +
        C * (v.toFun x * v.toFun x) := by
    intro x
    let A := gradFun (I := I_half n) h u.toFun x
    let B := v.toFun x • X x
    have hab := abs_two_mul_metric_inner_le h x A B
    have hBB : h.inner x B B =
        (v.toFun x * v.toFun x) * h.inner x (X x) (X x) := by
      simp only [B, map_smul, smul_apply, smul_eq_mul]
      ring
    have hbound : h.inner x B B ≤ C * (v.toFun x * v.toFun x) := by
      rw [hBB]
      have hmul := mul_le_mul_of_nonneg_left (hX x)
        (mul_self_nonneg (v.toFun x))
      nlinarith
    have heq : 2 * (h.inner x (X x) A * v.toFun x) =
        2 * h.inner x A B := by
      simp only [B, map_smul, smul_eq_mul]
      rw [h.symm x (X x) A]
      ring
    rw [heq]
    have hsum : h.inner x A A + h.inner x B B ≤
        h.inner x A A + C * (v.toFun x * v.toFun x) := by
      linarith
    exact hab.trans hsum
  unfold dirichletDrift dirichletEnergy dirichletMass
  change 2 * |∫ x, h.inner x (X x)
      (gradFun (I := I_half n) h u.toFun x) * v.toFun x ∂μ| ≤
    (∫ x, h.inner x
        (gradFun (I := I_half n) h u.toFun x)
        (gradFun (I := I_half n) h u.toFun x) ∂μ) +
      C * ∫ x, v.toFun x * v.toFun x ∂μ
  rw [← abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), ← abs_mul, ← integral_const_mul]
  calc
    _ ≤ ∫ x, |2 * (h.inner x (X x)
        (gradFun (I := I_half n) h u.toFun x) * v.toFun x)| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x, h.inner x
          (gradFun (I := I_half n) h u.toFun x)
          (gradFun (I := I_half n) h u.toFun x) +
        C * (v.toFun x * v.toFun x) ∂μ :=
      integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun _ => abs_nonneg _)
        hright (Filter.Eventually.of_forall hpoint)
    _ = _ := by
      rw [integral_add henergy hmass, integral_const_mul]


theorem two_mul_abs_dirichletDrift_le
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (C : ℝ) (hX : ∀ x : M, h.inner x (X x) (X x) ≤ C)
    {ε : ℝ} (hε : 0 < ε) (u v : SmoothScalarDirichlet q) :
    2 * |dirichletDrift h X u v| ≤
      ε * dirichletEnergy h u u + (C / ε) * dirichletMass h v v := by
  let r := Real.sqrt ε
  have hrpos : 0 < r := Real.sqrt_pos.mpr hε
  have hrr : r * r = ε := by simpa only [r, ← sq] using Real.sq_sqrt hε.le
  have h := two_mul_abs_dirichletDrift_le_add h X C hX (r • u) (r⁻¹ • v)
  rw [dirichletDrift_smul_left, dirichletDrift_smul_right,
    ← mul_assoc, mul_inv_cancel₀ hrpos.ne', one_mul,
    dirichletEnergy_smul_left, dirichletEnergy_smul_right,
    dirichletMass_smul_left, dirichletMass_smul_right] at h
  convert h using 1
  rw [← hrr]
  field_simp [hrpos.ne']


theorem two_mul_abs_dirichletMass_le
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    {ε : ℝ} (hε : 0 < ε) (u v : SmoothScalarDirichlet q) :
    2 * |dirichletMass h u v| ≤
      ε * dirichletMass h u u + ε⁻¹ * dirichletMass h v v := by
  have hu := (dirichletMass_integrable h u u).const_mul ε
  have hv := (dirichletMass_integrable h v v).const_mul ε⁻¹
  have hp : ∀ x : M, ‖2 * (u.toFun x * v.toFun x)‖ ≤
      ε * (u.toFun x * u.toFun x) + ε⁻¹ * (v.toFun x * v.toFun x) := by
    intro x
    have h := two_mul_le_add_mul_sq (a := |u.toFun x|) (b := |v.toFun x|) hε
    rw [sq_abs, sq_abs] at h
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
      sq_abs, pow_two, mul_assoc] using h
  have hb := norm_integral_le_of_norm_le (hu.add hv) (Filter.Eventually.of_forall hp)
  simp only [Pi.add_apply] at hb
  rw [Real.norm_eq_abs, integral_const_mul, abs_mul,
    abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), integral_add hu hv,
    integral_const_mul, integral_const_mul] at hb
  exact hb

theorem two_mul_dirichletDrift_self_le
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (C : ℝ)
    (hX : ∀ x : M, h.inner x (X x) (X x) ≤ C)
    (u : SmoothScalarDirichlet q) :
    2 * dirichletDrift h X u u ≤
      dirichletEnergy h u u + C * dirichletMass h u u := by
  have h := two_mul_abs_dirichletDrift_le h X C hX (by norm_num : (0 : ℝ) < 1) u u
  simp only [one_mul, div_one] at h
  exact (mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num : (0 : ℝ) ≤ 2)).trans h

theorem dirichletMass_self_nonneg
    {q : SmoothRiemannianMetric (I_half n) M}
    (h : SmoothRiemannianMetric (I_half n) M)
    (u : SmoothScalarDirichlet q) :
    0 ≤ dirichletMass h u u := by
  unfold dirichletMass
  exact integral_nonneg fun x => mul_self_nonneg (u.toFun x)

theorem dirichletGalerkinMassRate_le
    {q : SmoothRiemannianMetric (I_half n) M}
    (g : ℝ → SmoothRiemannianMetric (I_half n) M) (t : ℝ)
    (X : Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a Bx Bv : ℝ)
    (hX : ∀ x : M, (g t).inner x (X x) (X x) ≤ Bx)
    (htrace : ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) g t x| ≤ Bv)
    (ha : 0 ≤ a) (u : SmoothScalarDirichlet q) :
    2 * dirichletWeakForm (g t) X a u u +
        dirichletMassVariation g t u u ≤
      -dirichletEnergy (g t) u u +
        (Bx + (1 / 2) * Bv) * dirichletMass (g t) u u := by
  have hmass := dirichletMass_self_nonneg (g t) u
  have henergy := dirichletEnergy_self_nonneg (g t) u
  have hdrift := two_mul_dirichletDrift_self_le (g t) X Bx hX u
  have hvariation := (le_abs_self (dirichletMassVariation g t u u)).trans
    (abs_dirichletMassVariation_self_le g t Bv htrace u)
  unfold dirichletWeakForm
  nlinarith [mul_nonneg ha hmass]

theorem dirichletFinEnergy_cont
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn
      (I := I_half n) (M := M) D}
    (hG : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn
      (I := I_half n) (M := M) D G.metric)
    {K : Set ℝ} (hK : IsCompact K) (hKreg : K ⊆ D.regular)
    {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
      [FiniteDimensional ℝ V]
    (J : V →ₗ[ℝ] SmoothScalarDirichlet q) :
    ContinuousOn (fun t => dirichletFinEnergy (G.metric t) J) K := by
  rw [continuousOn_clm_apply]
  intro u
  rw [continuousOn_clm_apply]
  intro v
  simpa only [dirichletFinEnergy_apply] using
    dirichletEnergy_time_cont hG hK hKreg (J u) (J v)

theorem dirichletGalerkin_mass_uniform_bound
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn
      (I := I_half n) (M := M) D}
    (hG : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn
      (I := I_half n) (M := M) D G.metric)
    {T : ℝ} (hT : 0 ≤ T) (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    {ι : Type*} [Fintype ι]
    (φ : ι → SmoothScalarDirichlet q)
    (γ : ℝ → EuclideanSpace ℝ ι)
    (hγcont : ContinuousOn γ (Icc (0 : ℝ) T))
    (X : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ → ℝ) (Bx Bv : ℝ)
    (hsol : ∀ t, (ht : t ∈ Ico (0 : ℝ) T) →
      ∃ v : EuclideanSpace ℝ ι,
        HasDerivWithinAt γ v (Ici (0 : ℝ)) t ∧
        dirichletFinMass (G.metric t) (dirichletFinIncl φ) v =
          dirichletFinWeakForm (G.metric t) (X t) (a t)
            (dirichletFinIncl φ) (γ t))
    (hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx)
    (htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ Bv)
    (ha : ∀ t ∈ Ico (0 : ℝ) T, 0 ≤ a t) :
    ∀ t ∈ Icc (0 : ℝ) T,
      dirichletMass (G.metric t)
          (dirichletFinIncl φ (γ t)) (dirichletFinIncl φ (γ t)) ≤
        dirichletMass (G.metric 0)
            (dirichletFinIncl φ (γ 0)) (dirichletFinIncl φ (γ 0)) *
          Real.exp (max (Bx + (1 / 2) * Bv) 0 * T) := by
  let J := dirichletFinIncl φ
  let Y : ℝ → ℝ := fun t =>
    dirichletMass (G.metric t) (J (γ t)) (J (γ t))
  let Y' : ℝ → ℝ := fun t =>
    2 * dirichletWeakForm (G.metric t) (X t) (a t) (J (γ t)) (J (γ t)) +
      dirichletMassVariation G.metric t (J (γ t)) (J (γ t))
  let K := max (Bx + (1 / 2) * Bv) 0
  have hK : 0 ≤ K := le_max_right _ _
  have hYcont : ContinuousOn Y (Icc (0 : ℝ) T) := by
    have hmass := dirichletFinMass_cont G.metric isCompact_Icc
      (fun x₀ i j => hG.chartGramMatrix_continuousOn hreg x₀ i j) J
    have hfirst := hmass.clm_apply hγcont
    have hsecond := hfirst.clm_apply hγcont
    simpa only [Y, J, dirichletFinMass_apply] using hsecond
  have hYderiv : ∀ t ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt Y (Y' t) (Ici t) t := by
    intro t ht
    obtain ⟨v, hv, hweak⟩ := hsol t ht
    have hv' := DifferentialGeometry.Analysis.ODE.hasDerivWithinAt_Ici_of_Ici_zero
      hv ht.1
    simpa only [Y, Y', J] using
      hasDerivWithinAt_dirichletGalerkin_mass hG
        (hreg ⟨ht.1, ht.2.le⟩) φ (X t) (a t) hv' hweak
  have hYnonneg : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ Y t := by
    intro t _
    exact dirichletMass_self_nonneg (G.metric t) (J (γ t))
  have hYbound : ∀ t ∈ Ico (0 : ℝ) T, Y' t ≤ K * Y t := by
    intro t ht
    have hdiss := dirichletGalerkinMassRate_le G.metric t (X t) (a t) Bx Bv
      (hX t ht) (htrace t ht) (ha t ht) (J (γ t))
    have henergy := dirichletEnergy_self_nonneg (G.metric t) (J (γ t))
    have hmass := hYnonneg t ⟨ht.1, ht.2.le⟩
    have hcoeff : Bx + (1 / 2) * Bv ≤ K := le_max_left _ _
    dsimp only [Y', Y, J] at hdiss ⊢
    nlinarith
  have hslope : ∀ t ∈ Ico (0 : ℝ) T, ∀ b, Y' t < b →
      ∃ᶠ z in 𝓝[>] t, (z - t)⁻¹ * (Y z - Y t) < b := by
    intro t ht b hb
    refine ((hYderiv t ht).liminf_right_slope_le hb).mono ?_
    intro z hz
    rwa [slope_def_field, div_eq_inv_mul] at hz
  have hgron := le_gronwallBound_of_liminf_deriv_right_le
    (a := 0) (b := T) (δ := Y 0) (K := K) (ε := 0)
      hYcont hslope (le_refl (Y 0))
      (fun t ht => by simpa only [add_zero] using hYbound t ht)
  intro t ht
  have hraw := hgron t ht
  rw [gronwallBound_ε0, sub_zero] at hraw
  have hexp : Real.exp (K * t) ≤ Real.exp (K * T) := by
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hK)
  have hY0 := hYnonneg 0 ⟨le_rfl, hT⟩
  change Y t ≤ Y 0 * Real.exp (K * T)
  exact hraw.trans (mul_le_mul_of_nonneg_left hexp hY0)

theorem dirichletGalerkin_energy_integral_bound
    {q : SmoothRiemannianMetric (I_half n) M}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {G : DifferentialGeometry.Geometry.Curvature.MetricConnectionFamilyOn
      (I := I_half n) (M := M) D}
    (hG : DifferentialGeometry.Geometry.Curvature.MetricFamilySmoothOn
      (I := I_half n) (M := M) D G.metric)
    {T : ℝ} (hT : 0 ≤ T) (hreg : Icc (0 : ℝ) T ⊆ D.regular)
    {ι : Type*} [Fintype ι]
    (φ : ι → SmoothScalarDirichlet q)
    (γ : ℝ → EuclideanSpace ℝ ι)
    (hγcont : ContinuousOn γ (Icc (0 : ℝ) T))
    (X : ℝ → Cₛ^∞⟮I_half n; EuclideanSpace ℝ (Fin n),
      (TangentSpace (I_half n) : M → Type _)⟯)
    (a : ℝ → ℝ) (Bx Bv : ℝ)
    (hsol : ∀ t, (ht : t ∈ Ico (0 : ℝ) T) →
      ∃ v : EuclideanSpace ℝ ι,
        HasDerivWithinAt γ v (Ici (0 : ℝ)) t ∧
        dirichletFinMass (G.metric t) (dirichletFinIncl φ) v =
          dirichletFinWeakForm (G.metric t) (X t) (a t)
            (dirichletFinIncl φ) (γ t))
    (hX : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      (G.metric t).inner x (X t x) (X t x) ≤ Bx)
    (htrace : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : M,
      |traceTimeDerivMetric (I := I_half n) G.metric t x| ≤ Bv)
    (ha : ∀ t ∈ Ico (0 : ℝ) T, 0 ≤ a t) :
    ∀ t ∈ Icc (0 : ℝ) T,
      (∫ s in (0 : ℝ)..t, dirichletEnergy (G.metric s)
        (dirichletFinIncl φ (γ s)) (dirichletFinIncl φ (γ s))) ≤
        dirichletMass (G.metric 0)
          (dirichletFinIncl φ (γ 0)) (dirichletFinIncl φ (γ 0)) *
          (1 + max (Bx + (1 / 2) * Bv) 0 * T *
            Real.exp (max (Bx + (1 / 2) * Bv) 0 * T)) := by
  let J := dirichletFinIncl φ
  let Y : ℝ → ℝ := fun t =>
    dirichletMass (G.metric t) (J (γ t)) (J (γ t))
  let E : ℝ → ℝ := fun t =>
    dirichletEnergy (G.metric t) (J (γ t)) (J (γ t))
  let Y' : ℝ → ℝ := fun t =>
    2 * dirichletWeakForm (G.metric t) (X t) (a t) (J (γ t)) (J (γ t)) +
      dirichletMassVariation G.metric t (J (γ t)) (J (γ t))
  let K := max (Bx + (1 / 2) * Bv) 0
  have hK : 0 ≤ K := le_max_right _ _
  have hYcont : ContinuousOn Y (Icc (0 : ℝ) T) := by
    have hmass := dirichletFinMass_cont G.metric isCompact_Icc
      (fun x₀ i j => hG.chartGramMatrix_continuousOn hreg x₀ i j) J
    have hfirst := hmass.clm_apply hγcont
    have hsecond := hfirst.clm_apply hγcont
    simpa only [Y, J, dirichletFinMass_apply] using hsecond
  have hEcont : ContinuousOn E (Icc (0 : ℝ) T) := by
    have henergy := dirichletFinEnergy_cont hG isCompact_Icc hreg J
    have hfirst := henergy.clm_apply hγcont
    have hsecond := hfirst.clm_apply hγcont
    simpa only [E, J, dirichletFinEnergy_apply] using hsecond
  have hYderiv : ∀ t ∈ Ico (0 : ℝ) T,
      HasDerivWithinAt Y (Y' t) (Ici t) t := by
    intro t ht
    obtain ⟨v, hv, hweak⟩ := hsol t ht
    have hv' := DifferentialGeometry.Analysis.ODE.hasDerivWithinAt_Ici_of_Ici_zero
      hv ht.1
    simpa only [Y, Y', J] using
      hasDerivWithinAt_dirichletGalerkin_mass hG
        (hreg ⟨ht.1, ht.2.le⟩) φ (X t) (a t) hv' hweak
  have hYnonneg : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ Y t := by
    intro t _
    exact dirichletMass_self_nonneg (G.metric t) (J (γ t))
  have hYdiss : ∀ t ∈ Ico (0 : ℝ) T, Y' t + E t ≤ K * Y t := by
    intro t ht
    have hdiss := dirichletGalerkinMassRate_le G.metric t (X t) (a t) Bx Bv
      (hX t ht) (htrace t ht) (ha t ht) (J (γ t))
    have henergy := dirichletEnergy_self_nonneg (G.metric t) (J (γ t))
    have hmass := hYnonneg t ⟨ht.1, ht.2.le⟩
    have hcoeff : Bx + (1 / 2) * Bv ≤ K := le_max_left _ _
    dsimp only [Y', E, Y, J] at hdiss ⊢
    nlinarith
  have hmassbound : ∀ t ∈ Icc (0 : ℝ) T, Y t ≤ Y 0 * Real.exp (K * T) := by
    intro t ht
    simpa only [Y, J, K] using
      (dirichletGalerkin_mass_uniform_bound hG hT hreg φ γ hγcont X a Bx Bv
        hsol hX htrace ha t ht)
  intro t ht
  have htreg : t ≤ T := ht.2
  have hIcc : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T :=
    Icc_subset_Icc le_rfl htreg
  have hKYcont : ContinuousOn (fun s : ℝ => K * Y s) (Icc (0 : ℝ) t) :=
    (continuousOn_const : ContinuousOn (fun _ : ℝ => K) (Icc (0 : ℝ) t)).mul
      (hYcont.mono hIcc)
  have hphi_cont : ContinuousOn (fun s => E s - K * Y s) (Icc (0 : ℝ) t) := by
    exact (hEcont.mono hIcc).sub hKYcont
  have hphi_int : IntegrableOn (fun s => E s - K * Y s) (Icc (0 : ℝ) t) :=
    hphi_cont.integrableOn_Icc
  have hneg_deriv : ∀ s ∈ Ioo (0 : ℝ) t,
      HasDerivWithinAt (fun z => -Y z) (-Y' s) (Ioi s) s := by
    intro s hs
    have hsT : s ∈ Ico (0 : ℝ) T := ⟨hs.1.le, lt_of_lt_of_le hs.2 htreg⟩
    have h := (hYderiv s hsT).neg
    exact h.mono (Ioi_subset_Ici_self)
  have hphi_le : ∀ s ∈ Ioo (0 : ℝ) t, E s - K * Y s ≤ -Y' s := by
    intro s hs
    have hsT : s ∈ Ico (0 : ℝ) T := ⟨hs.1.le, lt_of_lt_of_le hs.2 htreg⟩
    have h := hYdiss s hsT
    nlinarith
  have hint := intervalIntegral.integral_le_sub_of_hasDeriv_right_of_le
    (a := (0 : ℝ)) (b := t) (g := fun s => -Y s) (g' := fun s => -Y' s)
      (φ := fun s => E s - K * Y s) ht.1
      (hYcont.neg.mono hIcc) hneg_deriv hphi_int hphi_le
  have hYint : IntervalIntegrable Y volume 0 t := by
    have hcont : ContinuousOn Y (uIcc (0 : ℝ) t) := by
      simpa only [uIcc_of_le ht.1] using hYcont.mono hIcc
    exact hcont.intervalIntegrable
  have hconstint : IntervalIntegrable (fun _ : ℝ => Y 0 * Real.exp (K * T)) volume 0 t :=
    intervalIntegrable_const
  have hY_integral : (∫ s in (0 : ℝ)..t, Y s) ≤ t * (Y 0 * Real.exp (K * T)) := by
    have hmono : (∫ s in (0 : ℝ)..t, Y s) ≤
        ∫ s in (0 : ℝ)..t, (Y 0 * Real.exp (K * T)) := by
      refine intervalIntegral.integral_mono_on (f := Y)
        (g := fun _ : ℝ => Y 0 * Real.exp (K * T)) ht.1 hYint hconstint ?_
      intro s hs
      exact hmassbound s ⟨hs.1, hs.2.trans htreg⟩
    rw [intervalIntegral.integral_const] at hmono
    simpa [sub_zero, one_mul] using hmono
  have hE_integral : (∫ s in (0 : ℝ)..t, E s) ≤
      Y 0 + K * (∫ s in (0 : ℝ)..t, Y s) := by
    have hEint : IntervalIntegrable E volume 0 t := by
      have hcont : ContinuousOn E (uIcc (0 : ℝ) t) := by
        simpa only [uIcc_of_le ht.1] using hEcont.mono hIcc
      exact hcont.intervalIntegrable
    have hKYint : IntervalIntegrable (fun s : ℝ => K * Y s) volume 0 t := by
      have hcont : ContinuousOn (fun s : ℝ => K * Y s) (uIcc (0 : ℝ) t) := by
        simpa only [uIcc_of_le ht.1] using hKYcont
      exact hcont.intervalIntegrable
    rw [intervalIntegral.integral_sub hEint hKYint,
      intervalIntegral.integral_const_mul] at hint
    have hYt : 0 ≤ Y t := hYnonneg t ⟨ht.1, ht.2⟩
    linarith
  calc
    _ ≤ Y 0 + K * (∫ s in (0 : ℝ)..t, Y s) := hE_integral
    _ ≤ Y 0 + K * (t * (Y 0 * Real.exp (K * T))) := by
      gcongr
    _ ≤ Y 0 * (1 + K * T * Real.exp (K * T)) := by
      have hY0 : 0 ≤ Y 0 := hYnonneg 0 ⟨le_rfl, hT⟩
      have hC : 0 ≤ Y 0 * Real.exp (K * T) :=
        mul_nonneg hY0 (Real.exp_nonneg _)
      have hprod : t * (Y 0 * Real.exp (K * T)) ≤
          T * (Y 0 * Real.exp (K * T)) :=
        mul_le_mul_of_nonneg_right htreg hC
      have hKprod := mul_le_mul_of_nonneg_left hprod hK
      dsimp only [K] at hK hKprod ⊢
      nlinarith

end DifferentialGeometry.Analysis.Parabolic.Dirichlet

end
