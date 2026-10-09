import DifferentialGeometry.Geometry.Collapse.FiniteCategory.FiniteModelSplitting
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.OrientedSplittingLimitMerge
import DifferentialGeometry.Geometry.Collapse.FiniteCategory.ExactSplitting.SplittingOrientation
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SurfaceOrientation

/-!
# LFR15 in the oriented case

LFR15's last sentence (A:26103): "When the source manifolds are oriented, so is `Z` with the
ordered Euclidean normal factor." `exists_finite_model_exact_splitting_oriented`: for oriented
sources, the SAME limit of LFR15 (the oriented limit of LFR14, with orientation `oN` preserved
eventually by the actual maps `jᵢ`) carries all clauses of `exists_finite_model_exact_splitting`
and, in addition, the zero factor `Z` has a compatible smooth carrier `S` (`C^K`-diffeomorphic
to `Z`) oriented by `oN` and the ordered basis `bF` of the Euclidean factor:
`(X_{bF a})_a, (dι dψ b'_i)_i` is positive for `oN` exactly when `b'` is positive.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric WithLp Manifold Module
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse.FiniteCategory

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.ExactSplitting
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Integral.Measure GC.MetricGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Collapse

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

universe u v w

/-- **LFR15, oriented case (row).** -/
theorem exists_finite_model_exact_splitting_oriented
    (n K : ℕ) (hn : 2 ≤ n) (hK : 4 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
    (A : ℝ → ℝ) (hA : ∀ R > 0, 0 < A R)
    {X : ℕ → Type u} [∀ i, MetricSpace (X i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin n)) (X i)]
    [∀ i, IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ (X i)]
    [∀ i, SigmaCompactSpace (X i)]
    [∀ i, T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (X i))]
    [∀ i, CompleteSpace (X i)] [∀ i, ConnectedSpace (X i)]
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i)
    (o : ∀ i, ManifoldOrientation 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (X i) n)
    (hvol : ∀ i, ENNReal.ofReal v ≤ riemannianVolumeMeasure 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      (X i) (g i) (riemannianBallOf (g i) (p i) r))
    (hcurv : ∀ R > 0, ∀ i, ∀ k ≤ K, ∀ y ∈ riemannianBallOf (g i) (p i) R,
      curvDerivNorm k (g i) y ≤ A R)
    {η L : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0)) (hL : Tendsto L atTop atTop)
    (hsec : ∀ i, ∀ y ∈ riemannianBallOf (g i) (p i) (L i),
      SectionalBoundedBelowAt (g i) y (-η i))
    {F : Type v} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    {a : F} {Z : ℕ → Type w} [∀ i, MetricSpace (Z i)] {b : ∀ i, Z i} {δ : ℕ → ℝ}
    (Φ : ∀ i, KleinerLottApprox (p i) (WithLp.toLp 2 (a, b i)) (δ i))
    (hδ : Tendsto δ atTop (𝓝 0)) {ιF : Type*} (bF : Basis ιF ℝ F)
    (σ : ιF ⊕ Fin (Module.finrank ℝ (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) -
      Module.finrank ℝ F) → ℝ)) ≃ Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)))) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∃ (N : Type) (mN : MetricSpace N) (cN : ChartedSpace (EuclideanSpace ℝ (Fin n)) N),
      letI := mN
      letI := cN
      ∃ (_ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ N)
        (G : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((K - 1 : ℕ) : ℕ∞ω)
          (EuclideanSpace ℝ (Fin n))
          (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) : N → Type _))
        (q : N)
        (j : ∀ i, PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
          𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N (X (φ i)) K)
        (oN : ManifoldOrientation 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N n)
        (_ : ProperSpace N)
        (hRiem : letI : RiemannianBundle (fun x : N =>
            TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) := ⟨G.toRiemannianMetric⟩
          IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N),
        ConnectedSpace N ∧
        PointedGHConverges (fun i => p (φ i)) q ∧
        (∀ i, q ∈ (j i).source ∧ j i q = p (φ i)) ∧
        (∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source) ∧
        (∀ (x : N) (L' : Set (EuclideanSpace ℝ (Fin n))), IsCompact L' →
          L' ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).target →
          MapCPConvergenceOn L' (K - 1)
            (fun i => pullbackMetricCoefficients (g (φ i))
              ((j i : N → X (φ i)) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).symm))
            (chartCoeff G x)) ∧
        (∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
          |dist (j i x) (j i y) - dist x y| < ε) ∧
        (∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
          ball (p (φ i)) a ⊆ (j i : N → X (φ i)) '' ball q b) ∧
        (∀ᶠ i in atTop, ∀ (x : N) (hx : x ∈ (j i).source),
          Orientation.map (Fin n)
            (((j i).isLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
                𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (K : ℕ∞ω) hx).mfderivToContinuousLinearEquiv
              (by exact_mod_cast (show K ≠ 0 by omega))).toLinearEquiv (oN.orientation x) =
            (o (φ i)).orientation (j i x)) ∧
        (∀ (x : N) (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x),
          0 ≤ G.sectionalCurvature x v w) ∧
        ∃ (W : Type) (m : MetricSpace W), letI := m
          ∃ (w : W), ProperSpace W ∧ CompleteSpace W ∧
            PointedGHConverges (fun i => b (φ i)) w ∧
            ∃ e : N ≃ᵢ WithLp 2 (F × W), e q = WithLp.toLp 2 (a, w) ∧
              (∀ C : Set N, Bornology.IsBounded C →
                TendstoUniformlyOn (fun i x => ((Φ (φ i)).toFun (j i x)).fst)
                  (fun x => (e x).fst) atTop C) ∧
              (letI : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :=
                 ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
               letI : RiemannianBundle (fun x : N =>
                   TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) := ⟨G.toRiemannianMetric⟩
               letI : IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N := hRiem
               letI := splittingFactorChartedSpace (finiteOrderMetricReindex K hK G)
                 (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e
               letI := splittingFactor_isManifold_one (finiteOrderMetricReindex K hK G)
                 (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e
               ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ, F)
                 ((((K - 2 : ℕ) : ℕ∞) : ℕ∞ω) + 2) (fun x => (e x).fst) ∧
               IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) -
                   Module.finrank ℝ F) → ℝ)
                 ((((K - 2 : ℕ) : ℕ∞) : ℕ∞ω) + 2) {x : N // (e x).fst = 0} ∧
               (letI : RiemannianBundle (TangentSpace 𝓘(ℝ, Fin (Module.finrank ℝ
                     (EuclideanSpace ℝ (Fin n)) - Module.finrank ℝ F) → ℝ) :
                   {x : N // (e x).fst = 0} → Type _) :=
                 ⟨(inducedMetric (finiteOrderMetricReindex K hK G) (two_le_finiteOrderReindex K hK)
                   (finiteOrderMetricReindex_enorm K hK G) e).toRiemannianMetric⟩
                IsRiemannianManifold 𝓘(ℝ, Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) -
                   Module.finrank ℝ F) → ℝ) {x : N // (e x).fst = 0}) ∧
               CompleteSpace {x : N // (e x).fst = 0} ∧
               (∀ (z : {x : N // (e x).fst = 0})
                 (v w : TangentSpace 𝓘(ℝ, Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) -
                   Module.finrank ℝ F) → ℝ) z),
                 0 ≤ (inducedMetric (finiteOrderMetricReindex K hK G)
                   (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G)
                   e).sectionalCurvature z v w) ∧
               ContMDiff ((𝓘(ℝ, F)).prod 𝓘(ℝ, Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) -
                   Module.finrank ℝ F) → ℝ)) 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
                 ((((K - 2 : ℕ) : ℕ∞) : ℕ∞ω) + 2)
                 (splittingProductDiffeomorph (finiteOrderMetricReindex K hK G)
                   (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e) ∧
               ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
                 ((𝓘(ℝ, F)).prod 𝓘(ℝ, Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) -
                   Module.finrank ℝ F) → ℝ))
                 ((((K - 2 : ℕ) : ℕ∞) : ℕ∞ω) + 2)
                 (splittingProductDiffeomorph (finiteOrderMetricReindex K hK G)
                   (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e).symm ∧
               (∀ p : F × {x : N // (e x).fst = 0},
                 splittingProductDiffeomorph (finiteOrderMetricReindex K hK G)
                   (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e p =
                   e.symm (toLp 2 (p.1, (e p.2.val).snd))) ∧
               (∀ (p : F × {x : N // (e x).fst = 0})
                 (v w : TangentSpace ((𝓘(ℝ, F)).prod 𝓘(ℝ, Fin (Module.finrank ℝ
                   (EuclideanSpace ℝ (Fin n)) - Module.finrank ℝ F) → ℝ)) p),
                 G.inner (splittingProductDiffeomorph (finiteOrderMetricReindex K hK G)
                     (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e p)
                   (mfderiv ((𝓘(ℝ, F)).prod 𝓘(ℝ, Fin (Module.finrank ℝ
                       (EuclideanSpace ℝ (Fin n)) - Module.finrank ℝ F) → ℝ))
                     𝓘(ℝ, EuclideanSpace ℝ (Fin n))
                     (splittingProductDiffeomorph (finiteOrderMetricReindex K hK G)
                       (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e)
                     p v)
                   (mfderiv ((𝓘(ℝ, F)).prod 𝓘(ℝ, Fin (Module.finrank ℝ
                       (EuclideanSpace ℝ (Fin n)) - Module.finrank ℝ F) → ℝ))
                     𝓘(ℝ, EuclideanSpace ℝ (Fin n))
                     (splittingProductDiffeomorph (finiteOrderMetricReindex K hK G)
                       (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e)
                     p w) =
                 inner ℝ v.1 w.1 + (inducedMetric (finiteOrderMetricReindex K hK G)
                   (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G)
                   e).inner p.2 v.2 w.2) ∧
               ∃ (S : Type) (_ : MetricSpace S)
                 (_ : ChartedSpace (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) -
                   Module.finrank ℝ F) → ℝ) S)
                 (_ : IsManifold 𝓘(ℝ, Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) -
                   Module.finrank ℝ F) → ℝ) ∞ S)
                 (ψ : S ≃ₜ {x : N // (e x).fst = 0}),
                 ContMDiff 𝓘(ℝ, Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) -
                     Module.finrank ℝ F) → ℝ)
                   𝓘(ℝ, Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) -
                     Module.finrank ℝ F) → ℝ) ((K - 2 + 2 : ℕ) : ℕ∞ω) ψ ∧
                 ContMDiff 𝓘(ℝ, Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) -
                     Module.finrank ℝ F) → ℝ)
                   𝓘(ℝ, Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) -
                     Module.finrank ℝ F) → ℝ) ((K - 2 + 2 : ℕ) : ℕ∞ω) ψ.symm ∧
                 ∃ (hbij : ∀ s, Function.Bijective (ambientSplitFrame
                     𝓘(ℝ, EuclideanSpace ℝ (Fin n))
                     𝓘(ℝ, Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) -
                       Module.finrank ℝ F) → ℝ) (Subtype.val ∘ ψ)
                     (fun s => splittingFrame (finiteOrderMetricReindex K hK G) e (ψ s).val) s))
                   (oS : SmoothOrientation 𝓘(ℝ, Fin (Module.finrank ℝ
                     (EuclideanSpace ℝ (Fin n)) - Module.finrank ℝ F) → ℝ) S),
                   ∀ (s : S) (b' : Basis (Fin (Module.finrank ℝ (Fin (Module.finrank ℝ
                       (EuclideanSpace ℝ (Fin n)) - Module.finrank ℝ F) → ℝ))) ℝ
                       (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) -
                         Module.finrank ℝ F) → ℝ)),
                     b'.orientation = oS.val s ↔
                       (splitFrameBasis bF b' σ (ambientSplitFrameEquiv
                         𝓘(ℝ, EuclideanSpace ℝ (Fin n))
                         𝓘(ℝ, Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) -
                           Module.finrank ℝ F) → ℝ) (Subtype.val ∘ ψ)
                         (fun s => splittingFrame (finiteOrderMetricReindex K hK G) e (ψ s).val)
                         hbij s).toLinearEquiv).orientation =
                       (smoothOrientationOfManifoldOrientation 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
                         (manifoldOrientationCast (finrank_euclideanSpace_fin).symm oN)).val
                         (ψ s).val) := by
  have hne : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin n))) :=
    ⟨by rw [finrank_euclideanSpace_fin]; omega⟩
  obtain ⟨φ, hφ, N, mN, cN, hMN, G, q, j, oN, hprop, hconn, hRiem, hGH, hpt, hexh, hconv, hdist,
      hcov, hor, hsecG, W, m, w, hWp, hWc, hzW, e, he, hcoord⟩ :=
    exists_finite_cheeger_gromov_limit_oriented_with_nonneg_splitting n K hn (by omega) hr hv A
      hA g hmetric p o hvol hcurv hη hL hsec Φ hδ
  let := mN
  let := cN
  let := m
  obtain ⟨hT, hZ, hRZ, hcZ, hsecZ, hΨ, hΨs, hΨe, hΨm⟩ :=
    exactSplitting_of_finite_limit K hK G hRiem e
  let _ : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
    ⟨G.toRiemannianMetric⟩
  let _ : IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) N := hRiem
  let _ := splittingFactorChartedSpace (finiteOrderMetricReindex K hK G)
    (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e
  let _ := splittingFactor_isManifold_one (finiteOrderMetricReindex K hK G)
    (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e
  have hcar :=
    exists_oriented_smoothCarrier_splittingFactor (k := K - 2)
      (V := Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - Module.finrank ℝ F) → ℝ)
      (finiteOrderMetricReindex K hK G)
      (two_le_finiteOrderReindex K hK) (finiteOrderMetricReindex_enorm K hK G) e
      (ContinuousLinearEquiv.refl ℝ
        (Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) - Module.finrank ℝ F) → ℝ)) bF σ
      (smoothOrientationOfManifoldOrientation 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
        (manifoldOrientationCast (finrank_euclideanSpace_fin).symm oN))
  exact ⟨φ, hφ, N, mN, cN, hMN, G, q, j, oN, hprop, hRiem, hconn, hGH, hpt, hexh, hconv, hdist,
    hcov, hor, hsecG, W, m, w, hWp, hWc, hzW, e, he, hcoord, hT, hZ, hRZ, hcZ, hsecZ hsecG, hΨ,
    hΨs, hΨe, hΨm, hcar⟩

end DifferentialGeometry.Geometry.Collapse.FiniteCategory
