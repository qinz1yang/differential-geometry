import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Finite.OrientedSplittingLimitMerge
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SurfaceOrientationNoncompact
import DifferentialGeometry.Geometry.Collapse.FiniteSurface.SurfaceFactor

/-!
# LFR16: eventual ballwise bounds and a compact factor (the row)

Chapter 13, row LFR16 (`lem:collapse-finite-compact-factor`, A:26159), the three-dimensional
oriented case. Sources: complete connected smooth oriented 3-manifolds with the basepoint volume
bound, EVENTUAL ballwise curvature-derivative bounds of orders `0..K` (`K ≥ 4`), expanding-ball
sectional lower bounds `-ηᵢ → 0`, and normalized `(1, δᵢ)`-splittings `Φᵢ` (`δᵢ → 0`) whose
residual factors have diameter `≤ D`. Along ONE subsequence, the SAME oriented finite limit
`(N, G, q, jᵢ, oN)` (LFR14's conclusions, orientation preserved eventually by the actual maps)
has `sec_G ≥ 0`, an exact line splitting `e : N ≃ᵢ ℝ × W` with `W` compact of diameter `≤ D`
tracked by the actual maps, and its zero factor `Z = t⁻¹(0)` is a compact connected boundaryless
`C^K` surface of diameter `≤ D` with nonnegatively curved `C^{K-1}` induced metric and `C^K`
product map (`surfaceFactor_of_finite_limit`), ORIENTED on a compatible smooth carrier by `oN`
and the ordered normal factor `∂_t` (`surfaceFactor_oriented_smoothCarrier`):
`exists_finite_model_compact_surface_factor`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Metric WithLp Manifold Function Module
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.ExactSplitting
open DifferentialGeometry.Geometry DifferentialGeometry.Geometry.MetricSmoothing
open DifferentialGeometry.Integral.Measure GC.MetricGeometry
open DifferentialGeometry.Topology DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Topology.Manifold

attribute [-instance] DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedAddCommGroup
  DifferentialGeometry.Tensor0SBundle.tangentSpaceNormedSpace

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "P" => Fin (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) - Module.finrank ℝ ℝ) → ℝ

local instance nezero_finrank_euclidean_three_row16_F7LFR11c :
    NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))) :=
  ⟨by rw [finrank_euclideanSpace_fin]; decide⟩

universe u w

/-- **LFR16 (row), three-dimensional oriented case.** -/
theorem exists_finite_model_compact_surface_factor
    (K : ℕ) (hK : 4 ≤ K) {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
    (A : ℝ → ℝ)
    {X : ℕ → Type u} [∀ i, MetricSpace (X i)]
    [∀ i, ChartedSpace (EuclideanSpace ℝ (Fin 3)) (X i)]
    [∀ i, IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ (X i)]
    [∀ i, SigmaCompactSpace (X i)]
    [∀ i, T2Space (TangentBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (X i))]
    [∀ i, CompleteSpace (X i)] [∀ i, ConnectedSpace (X i)]
    (g : ∀ i, SmoothRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (X i))
    (hmetric : ∀ i a b, riemannianEDistOf (g i) a b = ENNReal.ofReal (dist a b))
    (p : ∀ i, X i)
    (o : ∀ i, ManifoldOrientation 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (X i) 3)
    (hvol : ∀ i, ENNReal.ofReal v ≤ riemannianVolumeMeasure 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
      (X i) (g i) (riemannianBallOf (g i) (p i) r))
    (hcurv : ∀ R > 0, ∀ᶠ i in atTop, ∀ k ≤ K, ∀ y ∈ riemannianBallOf (g i) (p i) R,
      curvDerivNorm k (g i) y ≤ A R)
    {η L : ℕ → ℝ} (hη : Tendsto η atTop (𝓝 0)) (hL : Tendsto L atTop atTop)
    (hsec : ∀ i, ∀ y ∈ riemannianBallOf (g i) (p i) (L i),
      SectionalBoundedBelowAt (g i) y (-η i))
    {a : ℝ} {Z : ℕ → Type w}
    [∀ i, MetricSpace (Z i)] {b : ∀ i, Z i} {δ : ℕ → ℝ}
    (Φ : ∀ i, KleinerLottApprox (p i) (WithLp.toLp 2 (a, b i)) (δ i))
    (hδ : Tendsto δ atTop (𝓝 0)) {D : ℝ} (hD : ∀ i, ∀ x y : Z i, dist x y ≤ D) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ∃ (N : Type) (mN : MetricSpace N) (cN : ChartedSpace (EuclideanSpace ℝ (Fin 3)) N),
      letI := mN
      letI := cN
      ∃ (_ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ∞ N)
        (G : ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) ((K - 1 : ℕ) : ℕ∞ω)
          (EuclideanSpace ℝ (Fin 3))
          (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) : N → Type _))
        (q : N)
        (j : ∀ i, PartialDiffeomorph 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
          𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) N (X (φ i)) K)
        (oN : ManifoldOrientation 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) N 3) (_ : ProperSpace N)
        (hRiem : letI : RiemannianBundle (fun x : N =>
            TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) x) := ⟨G.toRiemannianMetric⟩
          IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) N),
        ConnectedSpace N ∧
        PointedGHConverges (fun i => p (φ i)) q ∧
        (∀ i, q ∈ (j i).source ∧ j i q = p (φ i)) ∧
        (∀ C : Set N, IsCompact C → ∀ᶠ i in atTop, C ⊆ (j i).source) ∧
        (∀ (x : N) (L' : Set (EuclideanSpace ℝ (Fin 3))), IsCompact L' →
          L' ⊆ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) x).target →
          MapCPConvergenceOn L' (K - 1)
            (fun i => pullbackMetricCoefficients (g (φ i))
              ((j i : N → X (φ i)) ∘ (extChartAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) x).symm))
            (chartCoeff G x)) ∧
        (∀ R ε : ℝ, 0 < ε → ∀ᶠ i in atTop, ∀ x ∈ ball q R, ∀ y ∈ ball q R,
          |dist (j i x) (j i y) - dist x y| < ε) ∧
        (∀ a b : ℝ, 0 < a → a < b → ∀ᶠ i in atTop,
          ball (p (φ i)) a ⊆ (j i : N → X (φ i)) '' ball q b) ∧
        (∀ᶠ i in atTop, ∀ (x : N) (hx : x ∈ (j i).source),
          Orientation.map (Fin 3)
            (((j i).isLocalDiffeomorphAt 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
                𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) (K : ℕ∞ω) hx).mfderivToContinuousLinearEquiv
              (by exact_mod_cast (show K ≠ 0 by omega))).toLinearEquiv (oN.orientation x) =
            (o (φ i)).orientation (j i x)) ∧
        (∀ (x : N) (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) x),
          0 ≤ G.sectionalCurvature x v w) ∧
        ∃ (W : Type) (m : MetricSpace W), letI := m
          ∃ (w : W), CompactSpace W ∧ (∀ x y : W, dist x y ≤ D) ∧
            PointedGHConverges (fun i => b (φ i)) w ∧
            ∃ e : N ≃ᵢ WithLp 2 (ℝ × W), e q = WithLp.toLp 2 (a, w) ∧
              (∀ C : Set N, Bornology.IsBounded C →
                TendstoUniformlyOn (fun i x => ((Φ (φ i)).toFun (j i x)).fst)
                  (fun x => (e x).fst) atTop C) ∧
              (letI : RiemannianBundle (fun x : N =>
                 TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) x) := ⟨G.toRiemannianMetric⟩
               letI : IsRiemannianManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) N := hRiem
               letI := splittingFactorChartedSpace (finiteMetricReindex K hK G)
                 (two_le_reindex K hK) (finiteMetricReindex_enorm K hK G) e
               letI := splittingFactor_isManifold_one (finiteMetricReindex K hK G)
                 (two_le_reindex K hK) (finiteMetricReindex_enorm K hK G) e
               (CompactSpace {x : N // (e x).fst = 0} ∧ ConnectedSpace {x : N // (e x).fst = 0} ∧
                (∀ z z' : {x : N // (e x).fst = 0}, dist z z' ≤ D) ∧
                IsManifold 𝓘(ℝ, P) ((((K - 2 : ℕ) : ℕ∞) : ℕ∞ω) + 2) {x : N // (e x).fst = 0} ∧
                (∀ (z : {x : N // (e x).fst = 0}) (v w : TangentSpace 𝓘(ℝ, P) z),
                  0 ≤ (inducedMetric (finiteMetricReindex K hK G) (two_le_reindex K hK)
                    (finiteMetricReindex_enorm K hK G) e).sectionalCurvature z v w) ∧
                ContMDiff (𝓘(ℝ, ℝ).prod 𝓘(ℝ, P)) 𝓘(ℝ, E3) ((((K - 2 : ℕ) : ℕ∞) : ℕ∞ω) + 2)
                  (splittingProductDiffeomorph (finiteMetricReindex K hK G) (two_le_reindex K hK)
                    (finiteMetricReindex_enorm K hK G) e)) ∧
               (∃ (S : Type) (_ : MetricSpace S) (_ : ChartedSpace E2 S) (_ : IsManifold (𝓡 2) ∞ S)
                  (φ : S ≃ₜ {x : N // (e x).fst = 0}),
                  ContMDiff (𝓡 2) 𝓘(ℝ, P) ((K - 2 + 2 : ℕ) : ℕ∞ω) φ ∧
                  ContMDiff 𝓘(ℝ, P) (𝓡 2) ((K - 2 + 2 : ℕ) : ℕ∞ω) φ.symm ∧
                  ∃ (hbij : ∀ s, Bijective (ambientSplitFrame 𝓘(ℝ, E3) (𝓡 2) (Subtype.val ∘ φ)
                      (fun s => splittingFrame (finiteMetricReindex K hK G) e (φ s).val) s))
                    (oS : SmoothOrientation (𝓡 2) S),
                    (∀ (s : S) (b : Basis (Fin (finrank ℝ E2)) ℝ E2), b.orientation = oS.val s ↔
                      (splitFrameBasis (Basis.singleton (Fin 1) ℝ) b lineSurfaceIndex
                        (ambientSplitFrameEquiv 𝓘(ℝ, E3) (𝓡 2) (Subtype.val ∘ φ)
                          (fun s => splittingFrame (finiteMetricReindex K hK G) e (φ s).val) hbij s).toLinearEquiv).orientation =
                        (smoothOrientationOfManifoldOrientation (𝓡 3)
                          (manifoldOrientationCast (by simp) oN)).val (φ s).val) ∧
                    ∃ O : ManifoldOrientation (𝓡 2) S 2,
                      O = manifoldOrientationCast (by simp)
                        (Classical.choose (exists_manifoldOrientation_eq_of_smoothOrientation (𝓡 2) oS)))) := by
  obtain ⟨φ, hφ, N, mN, cN, hMN, G, q, j, oN, hprop, hconn, hRiem, hGH, hpt, hexh, hconv, hdist,
      hcov, hor, hsecG, W, m, w, -, hcpt, hdiam, hzW, e, he, hcoord⟩ :=
    exists_finite_cheeger_gromov_limit_oriented_with_compact_splitting 3 K (by norm_num)
      (by omega) hr hv A g hmetric p o hvol hcurv hη hL hsec Φ hδ hD
  let := mN
  let := cN
  let := m
  have hsurf := surfaceFactor_of_finite_limit K hK G hRiem hsecG hdiam e
  let _ : RiemannianBundle (fun x : N => TangentSpace 𝓘(ℝ, E3) x) := ⟨G.toRiemannianMetric⟩
  let _ : IsRiemannianManifold 𝓘(ℝ, E3) N := hRiem
  have hor2 := surfaceFactor_oriented_smoothCarrier (k := K - 2) (finiteMetricReindex K hK G)
    (two_le_reindex K hK) (finiteMetricReindex_enorm K hK G) oN e
  exact ⟨φ, hφ, N, mN, cN, hMN, G, q, j, oN, hprop, hRiem, hconn, hGH, hpt, hexh, hconv, hdist,
    hcov, hor, hsecG, W, m, w, hcpt, hdiam, hzW, e, he, hcoord, hsurf, hor2⟩

end DifferentialGeometry.Geometry.Collapse
