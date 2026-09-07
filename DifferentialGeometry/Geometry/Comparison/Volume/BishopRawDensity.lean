import DifferentialGeometry.Geometry.Exponential.Radial
import DifferentialGeometry.Geometry.Exponential.ConjugatePoint.MinimizingGeodesic
import DifferentialGeometry.Geometry.Comparison.Variation.NoConjugatePoints.MinimalGeodesic
import DifferentialGeometry.Geometry.Comparison.Volume.Bishop.JacobiLocal
import DifferentialGeometry.Geometry.Comparison.Volume.Intrinsic.Ratio
import DifferentialGeometry.Geometry.Comparison.Volume.Radial.Gram
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Polar.Gauss
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Polar.Pole
import DifferentialGeometry.Geometry.Comparison.Variation.Jacobi.Orthogonality

open DifferentialGeometry.Geometry.Curvature

noncomputable section

open Filter Set Bundle Manifold
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry
namespace Geometry
namespace Riemannian
namespace VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
  [T2Space (TangentBundle I M)]

attribute [instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace

private local instance tangentSpaceNormedAddCommGroup
    [RiemannianBundle (fun x : M => TangentSpace I x)] (x : M) :
    NormedAddCommGroup (TangentSpace I x) :=
  Bundle.instNormedAddCommGroupOfRiemannianBundleOfIsTopologicalAddGroupOfContinuousConstSMulReal
    (E := fun y : M => TangentSpace I y) x

private local instance tangentSpaceInnerProductSpace
    [RiemannianBundle (fun x : M => TangentSpace I x)] (x : M) :
    InnerProductSpace ℝ (TangentSpace I x) :=
  Bundle.instInnerProductSpaceReal (E := fun y : M => TangentSpace I y) x

private local instance tangentSpaceNormedSpace
    [RiemannianBundle (fun x : M => TangentSpace I x)] (x : M) :
    NormedSpace ℝ (TangentSpace I x) := inferInstance

omit [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)] [CompleteSpace E]
  [I.Boundaryless] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] in
private lemma gON_linearIndep
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M)
    {v : Fin (Module.finrank ℝ E - 1) → E}
    (hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0) :
    LinearIndependent ℝ v := by
  let vT : Fin (Module.finrank ℝ E - 1) → TangentSpace I p :=
    fun i => show TangentSpace I p from v i
  have hONT : ∀ i j, g.inner p (vT i) (vT j) = if i = j then 1 else 0 := by
    intro i j
    exact hON i j
  have hliT := linIndep_of_ortho (I := I) g p vT hONT
  let e := tangentSpaceModelContinuousLinearEquiv (I := I) p
  have hliE := hliT.map' e.toLinearMap (LinearMap.ker_eq_bot.mpr e.injective)
  have hliE' : LinearIndependent ℝ (e.toLinearMap ∘ vT) := hliE
  have hev : (fun i => e (vT i)) = v := by
    funext i
    exact tangentSpaceModelContinuousLinearEquiv_apply (I := I) p (vT i)
  change LinearIndependent ℝ (e.toLinearMap ∘ vT) at hliE'
  rw [show e.toLinearMap ∘ vT = v by
    funext i
    exact congrFun hev i] at hliE'
  exact hliE'

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [T2Space M]
  [SigmaCompactSpace M] in
private lemma rawRadJac_eq_vel
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    (hx : (show TangentSpace I p from x) ∈ expDomain (I := I) g p) :
    radialJacobiField (I := I) g p x x 1 =
      curveVelocity (I := I) (radialCurve (I := I) g p x) 1 := by
  simpa only [one_smul] using
    radialJacobiField_self (I := I) g p x
      (t := (1 : ℝ)) (by simpa only [one_smul] using hx)

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [T2Space M]
  [SigmaCompactSpace M] in
theorem rawSpeed_sq
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) (x : E) (s : ℝ) (hs : 0 ≤ s)
    (hdom : ∀ t ∈ Icc (0 : ℝ) s,
      (show TangentSpace I p from t • x) ∈ expDomain (I := I) g p) :
    g.inner (radialCurve (I := I) g p x s)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) s)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) s) =
      g.inner p x x := by
  have h := inner_curveVelocity_expMap_smul (I := I) g p x
    (t := s) (hdom s ⟨hs, le_rfl⟩)
  dsimp only at h
  have hcurve : radialCurve (I := I) g p x =
      fun t : ℝ => expMap (I := I) g p (show TangentSpace I p from t • x) := by
    funext t
    rfl
  rw [hcurve]
  exact h

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [T2Space M]
  [SigmaCompactSpace M] in
private lemma rawJac_perp_one
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) (x w : E)
    (hdom : ∀ t ∈ Icc (0 : ℝ) 1,
      (show TangentSpace I p from t • x) ∈ expDomain (I := I) g p)
    (hperp : g.inner p x w = 0) :
    g.inner (radialCurve (I := I) g p x 1)
      (curveVelocity (I := I) (radialCurve (I := I) g p x) 1)
      (radialJacobiField (I := I) g p x w 1) = 0 := by
  have h := inner_curveVelocity_radialJacobiField (I := I) g p x w
    (t := (1 : ℝ)) (by
      have hxdom := hdom 1 ⟨by norm_num, le_rfl⟩
      simpa only [one_smul] using hxdom)
  dsimp only at h
  have hcurve : radialCurve (I := I) g p x =
      fun t : ℝ => expMap (I := I) g p (show TangentSpace I p from t • x) := by
    funext t
    rfl
  rw [hcurve]
  simpa only [one_mul, hperp, mul_zero] using h

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [T2Space M]
  [SigmaCompactSpace M] in
private lemma rawGram_split
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    {d : ℕ} (w : Fin d → E)
    (hdom : ∀ t ∈ Icc (0 : ℝ) 1,
      (show TangentSpace I p from t • x) ∈ expDomain (I := I) g p)
    (hperp : ∀ i, g.inner p x (w i) = 0) :
    (curveGram (I := I) g (radialCurve (I := I) g p x)
      (fun o t => match o with
        | none => radialJacobiField (I := I) g p x x t
        | some i => radialJacobiField (I := I) g p x (w i) t) 1).det =
      g.inner p x x *
        (curveGram (I := I) g (radialCurve (I := I) g p x)
          (fun i => radialJacobiField (I := I) g p x (w i)) 1).det := by
  classical
  let γ := radialCurve (I := I) g p x
  let W : Option (Fin d) → ∀ t, TangentSpace I (γ t) := fun o t =>
    match o with
    | none => radialJacobiField (I := I) g p x x t
    | some i => radialJacobiField (I := I) g p x (w i) t
  let T : Matrix (Fin d) (Fin d) ℝ :=
    curveGram (I := I) g γ
      (fun i => radialJacobiField (I := I) g p x (w i)) 1
  have hxdom : (show TangentSpace I p from x) ∈ expDomain (I := I) g p := by
    simpa only [one_smul] using hdom 1 ⟨by norm_num, le_rfl⟩
  have hdiag : g.inner (γ 1) (W none 1) (W none 1) = g.inner p x x := by
    change g.inner (γ 1) (radialJacobiField (I := I) g p x x 1)
      (radialJacobiField (I := I) g p x x 1) = g.inner p x x
    rw [rawRadJac_eq_vel (I := I) g p x hxdom]
    exact rawSpeed_sq (I := I) g p x 1 (by norm_num) hdom
  have hcross : ∀ i, g.inner (γ 1) (W none 1) (W (some i) 1) = 0 := by
    intro i
    change g.inner (γ 1) (radialJacobiField (I := I) g p x x 1)
      (radialJacobiField (I := I) g p x (w i) 1) = 0
    rw [rawRadJac_eq_vel (I := I) g p x hxdom]
    exact rawJac_perp_one (I := I) g p x (w i) hdom (hperp i)
  let e : Option (Fin d) ≃ Fin d ⊕ PUnit.{1} :=
    Equiv.optionEquivSumPUnit (Fin d)
  let D : Matrix PUnit.{1} PUnit.{1} ℝ :=
    Matrix.of fun _ _ => g.inner p x x
  have hblock : Matrix.reindex e e (curveGram (I := I) g γ W 1) =
      Matrix.fromBlocks T 0 0 D := by
    ext a b
    rcases a with i | a
    · rcases b with j | b
      · simp only [e, Matrix.reindex_apply, Matrix.submatrix_apply,
          Equiv.optionEquivSumPUnit_symm_inl, Matrix.fromBlocks_apply₁₁,
          curveGram, Matrix.of_apply, W, T]
      · cases b
        simp only [e, Matrix.reindex_apply, Matrix.submatrix_apply,
          Equiv.optionEquivSumPUnit_symm_inl,
          Equiv.optionEquivSumPUnit_symm_inr, Matrix.fromBlocks_apply₁₂,
          curveGram, Matrix.of_apply, W]
        change g.inner (γ 1) (W (some i) 1) (W none 1) = 0
        calc
          g.inner (γ 1) (W (some i) 1) (W none 1) =
              g.inner (γ 1) (W none 1) (W (some i) 1) := g.symm _ _ _
          _ = 0 := hcross i
    · cases a
      rcases b with j | b
      · simp only [e, Matrix.reindex_apply, Matrix.submatrix_apply,
          Equiv.optionEquivSumPUnit_symm_inr,
          Equiv.optionEquivSumPUnit_symm_inl, Matrix.fromBlocks_apply₂₁,
          curveGram, Matrix.of_apply, W]
        exact hcross j
      · cases b
        simp only [e, Matrix.reindex_apply, Matrix.submatrix_apply,
          Equiv.optionEquivSumPUnit_symm_inr, Matrix.fromBlocks_apply₂₂,
          curveGram, Matrix.of_apply, W, D]
        exact hdiag
  have hreindex :
      (Matrix.reindex e e (curveGram (I := I) g γ W 1)).det =
        (curveGram (I := I) g γ W 1).det :=
    Matrix.det_reindex_self e _
  have hDdet : D.det = g.inner p x x := by
    rw [Matrix.det_unique]
    rfl
  have hdet : (curveGram (I := I) g γ W 1).det = T.det * D.det := by
    rw [← hreindex, hblock, Matrix.det_fromBlocks_zero₂₁]
  calc
    (curveGram (I := I) g (radialCurve (I := I) g p x)
      (fun o t => match o with
        | none => radialJacobiField (I := I) g p x x t
        | some i => radialJacobiField (I := I) g p x (w i) t) 1).det =
        T.det * D.det := by
          change (curveGram (I := I) g γ W 1).det = T.det * D.det
          exact hdet
    _ = g.inner p x x *
        (curveGram (I := I) g (radialCurve (I := I) g p x)
          (fun i => radialJacobiField (I := I) g p x (w i)) 1).det := by
      change T.det * D.det = g.inner p x x * T.det
      rw [hDdet, mul_comm]

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
private lemma rawDens_split
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) {x : E} (hx : x ≠ 0)
    (hdom : ∀ t ∈ Icc (0 : ℝ) 1,
      (show TangentSpace I p from t • x) ∈ expDomain (I := I) g p)
    (w : Fin (Module.finrank ℝ E - 1) → E)
    (hON : ∀ i j, g.inner p (w i) (w j) = if i = j then 1 else 0)
    (hperp : ∀ i, g.inner p x (w i) = 0) :
    curveDensity (I := I) g (radialCurve (I := I) g p x)
        (fun i : Fin (Module.finrank ℝ E) =>
          radialJacobiField (I := I) g p x (chartModelBasis E i)) 1 =
      normalChartDensity (I := I) g p 0 *
        curveDensity (I := I) g (radialCurve (I := I) g p x)
          (fun i => radialJacobiField (I := I) g p x (w i)) 1 := by
  classical
  let d : ℕ := Module.finrank ℝ E - 1
  have hw_li : LinearIndependent ℝ w := gON_linearIndep (I := I) g p hON
  obtain ⟨B, hBnone, hBsome⟩ :=
    exists_perp_basis (I := I) g p x w hw_li hperp (g.pos p x hx)
  let a : Option (Fin d) → E := fun o => (B o : E)
  let e : Option (Fin d) ≃ Fin (Module.finrank ℝ E) := basisIndexEquiv B
  let γ := radialCurve (I := I) g p x
  let V : Option (Fin d) → ∀ t, TangentSpace I (γ t) := fun o t =>
    radialJacobiField (I := I) g p x (chartModelBasis E (e o)) t
  let W : Option (Fin d) → ∀ t, TangentSpace I (γ t) := fun o t =>
    match o with
    | none => radialJacobiField (I := I) g p x x t
    | some i => radialJacobiField (I := I) g p x (w i) t
  let C : Matrix (Option (Fin d)) (Option (Fin d)) ℝ :=
    (modelBasisFor B).toMatrix a
  have hC : ∀ o o', C o o' = (modelBasisFor B).repr (a o') o := by
    intro o o'
    rfl
  have hb : ∀ o, (modelBasisFor B) o = chartModelBasis E (e o) := by
    intro o
    simp [modelBasisFor, e, Module.Basis.reindex_apply]
  let L : E →L[ℝ] TangentSpace I (γ 1) :=
    mfderiv 𝓘(ℝ, E) I
      (fun z : E => expMap (I := I) g p (show TangentSpace I p from z)) x
  have hxdom : (show TangentSpace I p from x) ∈ expDomain (I := I) g p := by
    simpa only [one_smul] using hdom 1 ⟨by norm_num, le_rfl⟩
  have hjac (z : E) :
      radialJacobiField (I := I) g p x z 1 = L z := by
    have h := radialJacobiField_one (I := I) g p x z hxdom
    change radialJacobiField (I := I) g p x z 1 = L z
    exact h
  have hlin : ∀ o : Option (Fin d),
      L (a o) = ∑ o', C o' o • L (chartModelBasis E (e o')) := by
    intro o
    have hsum := (modelBasisFor B).sum_repr (a o)
    calc
      L (a o) = L (∑ o', (modelBasisFor B).repr (a o) o' •
          (modelBasisFor B) o') := congrArg L hsum.symm
      _ = ∑ o', (modelBasisFor B).repr (a o) o' •
          L ((modelBasisFor B) o') := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun o' _ => L.map_smul _ _
      _ = ∑ o', C o' o • L (chartModelBasis E (e o')) := by
        refine Finset.sum_congr rfl fun o' _ => ?_
        rw [hC o' o, hb o']
  have hrecomb : ∀ o : Option (Fin d), W o 1 = ∑ o', C o' o • V o' 1 := by
    intro o
    have hW : W o 1 = radialJacobiField (I := I) g p x (a o) 1 := by
      rcases o with _ | i
      · simp only [W, a, hBnone]
        rfl
      · simp only [W, a, hBsome]
        rfl
    calc
      W o 1 = L (a o) := hW.trans (hjac (a o))
      _ = ∑ o', C o' o • L (chartModelBasis E (e o')) := hlin o
      _ = ∑ o', C o' o • V o' 1 := by
        refine Finset.sum_congr rfl fun o' _ => ?_
        rw [← hjac (chartModelBasis E (e o'))]
  have hrecomb' := curveDensity_recomb (I := I) g γ V W 1 C hrecomb
  have hnn : 0 ≤ g.inner p x x := (g.pos p x hx).le
  have hsplit : curveDensity (I := I) g γ W 1 =
      Real.sqrt (g.inner p x x) *
        curveDensity (I := I) g γ
          (fun i => radialJacobiField (I := I) g p x (w i)) 1 := by
    unfold curveDensity
    rw [show (curveGram (I := I) g γ W 1).det =
        g.inner p x x *
          (curveGram (I := I) g γ
            (fun i => radialJacobiField (I := I) g p x (w i)) 1).det by
      have hrg := rawGram_split (I := I) g p x w hdom hperp
      change (curveGram (I := I) g γ W 1).det =
        g.inner p x x *
          (curveGram (I := I) g γ
            (fun i => radialJacobiField (I := I) g p x (w i)) 1).det
      exact hrg]
    rw [Real.sqrt_mul hnn]
  have hfull :
      curveDensity (I := I) g γ
          (fun i : Fin (Module.finrank ℝ E) =>
            radialJacobiField (I := I) g p x (chartModelBasis E i)) 1 =
        curveDensity (I := I) g γ V 1 := by
    exact (curveDensity_reindex (I := I) g γ
      (fun i : Fin (Module.finrank ℝ E) =>
        radialJacobiField (I := I) g p x (chartModelBasis E i)) 1 e).symm
  have hBperp : ∀ i, g.inner p x (B (some i)) = 0 := by
    intro i
    rw [hBsome i]
    exact hperp i
  have hONB : ∀ i j,
      g.inner p (B (some i)) (B (some j)) = if i = j then 1 else 0 := by
    intro i j
    rw [hBsome i, hBsome j]
    exact hON i j
  have hncd := normalChartDensity_zero_of_perpOrthonormal
    (I := I) g p x B hBnone hBperp hONB
  have hdetC : |C.det| = |(modelBasisFor B).det B| := by
    change |((modelBasisFor B).toMatrix a).det| = |(modelBasisFor B).det B|
    rw [Module.Basis.det_apply]
  have hV : curveDensity (I := I) g γ V 1 =
      (Real.sqrt (g.inner p x x) / |C.det|) *
        curveDensity (I := I) g γ
          (fun i => radialJacobiField (I := I) g p x (w i)) 1 := by
    have hdet_ne : |C.det| ≠ 0 := by
      rw [hdetC]
      exact abs_ne_zero.mpr ((modelBasisFor B).isUnit_det B).ne_zero
    have hquot : curveDensity (I := I) g γ V 1 =
        curveDensity (I := I) g γ W 1 / |C.det| := by
      exact (eq_div_iff hdet_ne).mpr (by rw [mul_comm]; exact hrecomb'.symm)
    rw [hquot, hsplit]
    field_simp [hdet_ne]
  rw [show radialCurve (I := I) g p x = γ by rfl, hfull, hV, hncd, ← hdetC]

omit [NeZero (Module.finrank ℝ E)] [CompleteSpace E] [T2Space M]
  [SigmaCompactSpace M] in
private lemma rawTrans_scale
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) (u : E)
    (w : Fin (Module.finrank ℝ E - 1) → E) (r : ℝ) (hr : 0 < r)
    (hrdom : (show TangentSpace I p from r • u) ∈ expDomain (I := I) g p) :
    curveDensity (I := I) g (radialCurve (I := I) g p u)
        (fun i => radialJacobiField (I := I) g p u (w i)) r =
      r ^ (Module.finrank ℝ E - 1) *
        curveDensity (I := I) g (radialCurve (I := I) g p (r • u))
          (fun i => radialJacobiField (I := I) g p (r • u) (w i)) 1 := by
  classical
  let d : ℕ := Module.finrank ℝ E - 1
  let γ := radialCurve (I := I) g p (r • u)
  let V : Fin d → ∀ t, TangentSpace I (γ t) := fun i t =>
    radialJacobiField (I := I) g p (r • u) (w i) t
  let V' : Fin d → ∀ t, TangentSpace I (γ t) := fun i _ =>
    (radialJacobiField (I := I) g p u (w i) r : E)
  let C : Matrix (Fin d) (Fin d) ℝ := Matrix.diagonal fun _ => r
  let L : E →L[ℝ] TangentSpace I (γ 1) :=
    mfderiv 𝓘(ℝ, E) I
      (fun z : E => expMap (I := I) g p (show TangentSpace I p from z))
      (r • u)
  have hJ (z : E) :
      (radialJacobiField (I := I) g p (r • u) z 1 : E) = (L z : E) := by
    have h := radialJacobiField_one (I := I) g p (r • u) z hrdom
    change (radialJacobiField (I := I) g p (r • u) z 1 : E) = (L z : E)
    exact h
  have hscale (i : Fin d) :
      (radialJacobiField (I := I) g p u (w i) r : E) =
        r • (radialJacobiField (I := I) g p (r • u) (w i) 1 : E) := by
    rw [radialJacobi_scale (I := I)]
    rw [hJ (r • w i)]
    change L (r • w i) = r •
      (radialJacobiField (I := I) g p (r • u) (w i) 1)
    rw [L.map_smul, hJ (w i)]
    rfl
  have hrecomb : ∀ i : Fin d, V' i 1 = ∑ k, C k i • V k 1 := by
    intro i
    change (radialJacobiField (I := I) g p u (w i) r : E) =
      ∑ k, (Matrix.diagonal (fun _ : Fin d => r)) k i •
        (radialJacobiField (I := I) g p (r • u) (w k) 1 : E)
    rw [hscale i]
    rw [Finset.sum_eq_single i]
    · rw [Matrix.diagonal_apply_eq]
    · intro k _ hki
      rw [show Matrix.diagonal (fun _ : Fin d => r) k i = 0 by simp [hki]]
      change (0 : ℝ) •
        (radialJacobiField (I := I) g p (r • u) (w k) 1 : E) = 0
      exact zero_smul ℝ _
    · simp
  have hrec := curveDensity_recomb (I := I) g γ V V' 1 C hrecomb
  have hdet : |C.det| = r ^ d := by
    simp only [C, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, abs_pow, abs_of_pos hr]
  have hbridge : curveDensity (I := I) g γ V' 1 =
      curveDensity (I := I) g (radialCurve (I := I) g p u)
        (fun i => radialJacobiField (I := I) g p u (w i)) r := by
    unfold curveDensity curveGram
    apply congrArg Real.sqrt
    apply congrArg Matrix.det
    ext i j
    have hpt : γ 1 = radialCurve (I := I) g p u r := by
      simp only [γ, radialCurve, one_smul]
    simp only [Matrix.of_apply, V']
    rw [hpt]
  exact hbridge.symm.trans <| by
    simpa only [hdet, d, V, γ] using hrec

omit [NeZero (Module.finrank ℝ E)] [T2Space M] [SigmaCompactSpace M] in
theorem rawDens_eq_trans
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) {u : E} (hu : u ≠ 0)
    (r : ℝ) (hr : 0 < r)
    (hdom : ∀ t ∈ Icc (0 : ℝ) r,
      (show TangentSpace I p from t • u) ∈ expDomain (I := I) g p)
    (w : Fin (Module.finrank ℝ E - 1) → E)
    (hON : ∀ i j, g.inner p (w i) (w j) = if i = j then 1 else 0)
    (hperp : ∀ i, g.inner p u (w i) = 0) :
    curveDensity (I := I) g (radialCurve (I := I) g p (r • u))
        (fun i : Fin (Module.finrank ℝ E) =>
          radialJacobiField (I := I) g p (r • u) (chartModelBasis E i)) 1 *
        r ^ (Module.finrank ℝ E - 1) =
      normalChartDensity (I := I) g p 0 *
        curveDensity (I := I) g (radialCurve (I := I) g p u)
          (fun i => radialJacobiField (I := I) g p u (w i)) r := by
  classical
  have hru : r • u ≠ 0 := smul_ne_zero hr.ne' hu
  have hdom_one : ∀ t ∈ Icc (0 : ℝ) 1,
      (show TangentSpace I p from t • (r • u)) ∈ expDomain (I := I) g p := by
    intro t ht
    have htr : t * r ∈ Icc (0 : ℝ) r := by
      constructor
      · exact mul_nonneg ht.1 hr.le
      · nlinarith [ht.2, hr]
    simpa only [smul_smul, mul_comm] using hdom (t * r) htr
  have hperp' : ∀ i, g.inner p (r • u) (w i) = 0 := by
    intro i
    have hs := congrArg (fun A : E →L[ℝ] ℝ => A (w i))
      ((g.inner p).map_smul r u)
    calc
      g.inner p (r • u) (w i) = r * g.inner p u (w i) := by
        calc
          g.inner p (r • u) (w i) = (r • (g.inner p u)) (w i) := hs
          _ = r • g.inner p u (w i) := smul_apply _ _ _
          _ = r * g.inner p u (w i) := by rfl
      _ = 0 := by rw [hperp i, mul_zero]
  have hfac := rawDens_split (I := I) g p hru hdom_one w hON hperp'
  have hrdom : (show TangentSpace I p from r • u) ∈ expDomain (I := I) g p :=
    hdom r ⟨hr.le, le_rfl⟩
  have hscale := rawTrans_scale (I := I) g p u w r hr hrdom
  calc
    curveDensity (I := I) g (radialCurve (I := I) g p (r • u))
          (fun i : Fin (Module.finrank ℝ E) =>
            radialJacobiField (I := I) g p (r • u) (chartModelBasis E i)) 1 *
        r ^ (Module.finrank ℝ E - 1) =
      (normalChartDensity (I := I) g p 0 *
        curveDensity (I := I) g (radialCurve (I := I) g p (r • u))
          (fun i => radialJacobiField (I := I) g p (r • u) (w i)) 1) *
        r ^ (Module.finrank ℝ E - 1) := by rw [hfac]
    _ = normalChartDensity (I := I) g p 0 *
        (r ^ (Module.finrank ℝ E - 1) *
          curveDensity (I := I) g (radialCurve (I := I) g p (r • u))
            (fun i => radialJacobiField (I := I) g p (r • u) (w i)) 1) := by
          ring
    _ = normalChartDensity (I := I) g p 0 *
        curveDensity (I := I) g (radialCurve (I := I) g p u)
          (fun i => radialJacobiField (I := I) g p u (w i)) r := by rw [← hscale]

omit [CompleteSpace E] [SigmaCompactSpace M] in
private lemma raw_ratio_inj
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) (u : E)
    (a : ℝ) (ha : 0 < a)
    (L : ℝ) (_hL : 0 < L)
    (hdom : ∀ t ∈ Icc (0 : ℝ) L,
      (show TangentSpace I p from t • u) ∈ expDomain (I := I) g p)
    (hspeed : ∀ t ∈ Ioo (0 : ℝ) L,
      g.inner (radialCurve (I := I) g p u t)
        (curveVelocity (I := I) (radialCurve (I := I) g p u) t)
        (curveVelocity (I := I) (radialCurve (I := I) g p u) t) = a ^ 2)
    (hinj : ∀ t ∈ Ioo (0 : ℝ) L,
      Function.Injective (mfderiv 𝓘(ℝ, E) I
        (fun b : E => (expMap (I := I) g p
          (show TangentSpace I p from b) : M)) (t • u)))
    (v : Fin (Module.finrank ℝ E - 1) → E)
    (hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0)
    (hperp : ∀ i, g.inner p u (v i) = 0)
    (hd : 0 < Module.finrank ℝ E - 1)
    (hRic : ∀ t ∈ Ioo (0 : ℝ) L,
      0 ≤ ricciTensor (I := I) g (radialCurve (I := I) g p u t)
        (curveVelocity (I := I) (radialCurve (I := I) g p u) t)
        (curveVelocity (I := I) (radialCurve (I := I) g p u) t)) :
    AntitoneOn
      (fun t => curveDensity (I := I) g (radialCurve (I := I) g p u)
          (fun i => radialJacobiField (I := I) g p u (v i)) t /
        hyperbolicDensity 0 (Module.finrank ℝ E - 1) t)
      (Ioo (0 : ℝ) L) := by
  classical
  let γ := radialCurve (I := I) g p u
  let V : Fin (Module.finrank ℝ E - 1) → ∀ t, TangentSpace I (γ t) :=
    fun i => radialJacobiField (I := I) g p u (v i)
  have hcurve : γ = fun t : ℝ =>
      expMap (I := I) g p (show TangentSpace I p from t • u) := by
    funext t
    rfl
  have hv : LinearIndependent ℝ v := gON_linearIndep (I := I) g p hON
  have hγcc : ∀ t ∈ Icc (0 : ℝ) L,
      ContMDiffAt 𝓘(ℝ, ℝ) I (2 : WithTop ℕ∞) γ t := by
    intro t ht
    have hline : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ (fun s : ℝ => s • u) t :=
      (contMDiff_id.smul contMDiff_const).contMDiffAt
    have hexp := contMDiffAt_expMap (I := I) g p (hdom t ht)
    rw [hcurve]
    exact (hexp.comp t hline).of_le
      (by decide : (2 : WithTop ℕ∞) ≤ ∞)
  have hγ : ∀ t ∈ Ioo (0 : ℝ) L,
      ContMDiffAt 𝓘(ℝ, ℝ) I (2 : WithTop ℕ∞) γ t :=
    fun t ht => hγcc t ⟨ht.1.le, ht.2.le⟩
  have hspeed' : ∀ t ∈ Ioo (0 : ℝ) L,
      g.inner (γ t) (curveVelocity (I := I) γ t)
        (curveVelocity (I := I) γ t) = a ^ 2 := by
    simpa only [γ] using hspeed
  have hgeo : IsGeodesicOn (I := I) g γ (Icc (0 : ℝ) L) := by
    intro t ht
    rw [hcurve]
    exact hasGeodesicEquationAt_expMap_smul (I := I) g p
      (show TangentSpace I p from u) (hdom t ht)
  have hJac : ∀ t ∈ Ioo (0 : ℝ) L, ∀ i,
      IsJacobiAt (I := I) g γ (V i) t := by
    intro t ht i
    rw [hcurve]
    exact isJacobiAt_radialJacobiField (I := I) g p u (v i)
      (hdom t ⟨ht.1.le, ht.2.le⟩)
  have hVperp : ∀ t ∈ Ioo (0 : ℝ) L, ∀ i,
      g.inner (γ t) (curveVelocity (I := I) γ t) (V i t) = 0 := by
    intro t ht i
    have h := inner_curveVelocity_radialJacobiField (I := I) g p u (v i)
      (t := t) (hdom t ⟨ht.1.le, ht.2.le⟩)
    dsimp only at h
    rw [hcurve]
    simpa only [V, hperp i, mul_zero] using h
  have hDVperp : ∀ t ∈ Ioo (0 : ℝ) L, ∀ i,
      g.inner (γ t) (curveVelocity (I := I) γ t)
        (covDerivAlong (I := I) g γ (V i) t) = 0 := by
    intro t ht i
    have h := inner_curveVelocity_covDerivAlong_radialJacobiField (I := I) g p u (v i)
      (t := t) (hdom t ⟨ht.1.le, ht.2.le⟩)
    dsimp only at h
    rw [hcurve]
    simpa only [V, hperp i] using h
  have hVdiff : ∀ t ∈ Ioo (0 : ℝ) L, ∀ i,
      DifferentiableAt ℝ (chartRepAt (I := I) γ (V i) t) t :=
    fun t ht i => by
      rw [hcurve]
      exact differentiableAt_chartRep_radialJacobiField (I := I) g p u (v i)
        (hdom t ⟨ht.1.le, ht.2.le⟩)
  have hDVdiff : ∀ t ∈ Ioo (0 : ℝ) L, ∀ i,
      DifferentiableAt ℝ
        (chartRepAt (I := I) γ
          (fun s => covDerivAlong (I := I) g γ (V i) s) t) t :=
    fun t ht i => by
      rw [hcurve]
      simpa only [V] using
        differentiableAt_chartRep_covDerivAlong_radialJacobiField (I := I) g p u (v i)
          (hdom t ⟨ht.1.le, ht.2.le⟩)
  have hLI : ∀ t ∈ Ioo (0 : ℝ) L,
      LinearIndependent ℝ fun i => V i t := by
    intro t ht
    rw [hcurve]
    simpa only [V] using
      linearIndependent_radialJacobiField (I := I) g p u hv ht.1.ne'
        (hdom t ⟨ht.1.le, ht.2.le⟩) (hinj t ht)
  have hW : ∀ t ∈ Ioo (0 : ℝ) L, ∀ i j,
      jacobiWronskian g γ (V i) (V j) t = 0 := by
    intro t ht i j
    rw [hcurve]
    exact jacobiWronskian_radialJacobiField_eq_zero (I := I) g p u (v i) (v j)
      (hdom t ⟨ht.1.le, ht.2.le⟩)
  have hRatioLower : ∃ C : ℝ, 0 < C ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ),
        C ≤ curveDensity (I := I) g γ V t /
          hyperbolicDensity 0 (Module.finrank ℝ E - 1) t := by
    refine ⟨1 / 2, by norm_num, ?_⟩
    have hpole : Tendsto
        (fun t => curveDensity (I := I) g γ V t /
          hyperbolicDensity 0 (Module.finrank ℝ E - 1) t)
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      simpa only [γ, V, Fintype.card_fin] using
        tendsto_curveDensity_radialJacobiField_div_hyperbolicDensity_of_orthonormal
          (I := I) g p u v 0 hON
    have hev := (tendsto_order.1 hpole).1 (1 / 2) (by norm_num)
    exact hev.mono fun _ h => h.le
  have hmean := curveMean_le_on (I := I) (n := (2 : WithTop ℕ∞)) (by norm_num)
    g γ V 0 a L (by norm_num) ha (by simp) hd hγ hspeed' hVperp hDVperp
    hVdiff hDVdiff hLI hW hJac (by
      intro t ht
      simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, neg_zero,
        zero_mul] using hRic t ht) (by simpa only [zero_mul] using hRatioLower)
  simpa only [γ, V, zero_mul] using
    curveRatio_anti (I := I) (n := (2 : WithTop ℕ∞)) (by norm_num)
      g γ V 0 L (Module.finrank ℝ E - 1) (by norm_num)
      hγ hVdiff hLI hW (by simpa only [zero_mul] using hmean)

omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem raw_ratio_anti
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) (u : E)
    (hunit : g.inner p u u = 1)
    (L : ℝ) (hL : 0 < L)
    (hdom : ∀ t ∈ Icc (0 : ℝ) L,
      (show TangentSpace I p from t • u) ∈ expDomain (I := I) g p)
    (hmin : ∀ η : ℝ → M,
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Icc 0 L) →
      η 0 = p →
      η L = expMap (I := I) g p (show TangentSpace I p from L • u) →
      arcLength (I := I) g (radialCurve (I := I) g p u) 0 L ≤
        arcLength (I := I) g η 0 L)
    (v : Fin (Module.finrank ℝ E - 1) → E)
    (hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0)
    (hperp : ∀ i, g.inner p u (v i) = 0)
    (hd : 0 < Module.finrank ℝ E - 1)
    (hRic : ∀ t ∈ Ioo (0 : ℝ) L,
      0 ≤ ricciTensor (I := I) g (radialCurve (I := I) g p u t)
        (curveVelocity (I := I) (radialCurve (I := I) g p u) t)
        (curveVelocity (I := I) (radialCurve (I := I) g p u) t)) :
    AntitoneOn
      (fun t => curveDensity (I := I) g (radialCurve (I := I) g p u)
          (fun i => radialJacobiField (I := I) g p u (v i)) t /
        hyperbolicDensity 0 (Module.finrank ℝ E - 1) t)
      (Ioo (0 : ℝ) L) := by
  apply raw_ratio_inj (I := I) g p u 1 (by norm_num) L hL hdom
  · intro t ht
    rw [rawSpeed_sq (I := I) g p u t ht.1.le (fun s hs =>
      hdom s ⟨hs.1, hs.2.trans ht.2.le⟩), hunit]
    norm_num
  · intro t ht
    exact DifferentialGeometry.Geometry.Riemannian.Exponential.injective_mfderiv_expMap_of_minimising_geodesic
      (I := I) g p u hunit (hdom L ⟨hL.le, le_rfl⟩) (by
        intro η hη hη0 hηL
        have hrad : radialCurve (I := I) g p u = fun t : ℝ =>
            expMap (I := I) g p (show TangentSpace I p from t • u) := by
          funext t
          rfl
        rw [← hrad]
        exact hmin η hη hη0 hηL) ht
  · exact hON
  · exact hperp
  · exact hd
  · exact hRic

omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem raw_density_le
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) (u : E)
    (hunit : g.inner p u u = 1)
    (L : ℝ) (hL : 0 < L)
    (hdom : ∀ t ∈ Icc (0 : ℝ) L,
      (show TangentSpace I p from t • u) ∈ expDomain (I := I) g p)
    (hmin : ∀ η : ℝ → M,
      ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Icc 0 L) →
      η 0 = p →
      η L = expMap (I := I) g p (show TangentSpace I p from L • u) →
      arcLength (I := I) g (radialCurve (I := I) g p u) 0 L ≤
        arcLength (I := I) g η 0 L)
    (v : Fin (Module.finrank ℝ E - 1) → E)
    (hON : ∀ i j, g.inner p (v i) (v j) = if i = j then 1 else 0)
    (hperp : ∀ i, g.inner p u (v i) = 0)
    (hd : 0 < Module.finrank ℝ E - 1)
    (hRic : ∀ t ∈ Ioo (0 : ℝ) L,
      0 ≤ ricciTensor (I := I) g (radialCurve (I := I) g p u t)
        (curveVelocity (I := I) (radialCurve (I := I) g p u) t)
        (curveVelocity (I := I) (radialCurve (I := I) g p u) t)) :
    ∀ t ∈ Ioo (0 : ℝ) L,
      curveDensity (I := I) g (radialCurve (I := I) g p u)
          (fun i => radialJacobiField (I := I) g p u (v i)) t ≤
        hyperbolicDensity 0 (Module.finrank ℝ E - 1) t := by
  have hanti := raw_ratio_anti (I := I) g p u hunit L hL hdom hmin v hON
    hperp hd hRic
  have hpole : Tendsto
      (fun t => curveDensity (I := I) g (radialCurve (I := I) g p u)
          (fun i => radialJacobiField (I := I) g p u (v i)) t /
        hyperbolicDensity 0 (Module.finrank ℝ E - 1) t)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa only [Fintype.card_fin] using
      tendsto_curveDensity_radialJacobiField_div_hyperbolicDensity_of_orthonormal
        (I := I) g p u v 0 hON
  intro t ht
  have hpos : 0 < hyperbolicDensity 0 (Module.finrank ℝ E - 1) t :=
    hyperbolicDensity_pos (by norm_num) ht.1
  have hRatioLE :
      curveDensity (I := I) g (radialCurve (I := I) g p u)
          (fun i => radialJacobiField (I := I) g p u (v i)) t /
        hyperbolicDensity 0 (Module.finrank ℝ E - 1) t ≤ 1 := by
    have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ),
        curveDensity (I := I) g (radialCurve (I := I) g p u)
            (fun i => radialJacobiField (I := I) g p u (v i)) t /
          hyperbolicDensity 0 (Module.finrank ℝ E - 1) t ≤
        curveDensity (I := I) g (radialCurve (I := I) g p u)
            (fun i => radialJacobiField (I := I) g p u (v i)) s /
          hyperbolicDensity 0 (Module.finrank ℝ E - 1) s := by
      filter_upwards [Ioo_mem_nhdsGT ht.1] with s hs
      have hsL : s ∈ Ioo (0 : ℝ) L := ⟨hs.1, hs.2.trans ht.2⟩
      exact hanti hsL ht hs.2.le
    exact ge_of_tendsto hpole hev
  rwa [div_le_one hpos] at hRatioLE

omit [SigmaCompactSpace M] in
theorem rawDens_le_of_inj
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M) (p : M) (x : E)
    (hdom : ∀ t ∈ Icc (0 : ℝ) 1,
      (show TangentSpace I p from t • x) ∈ expDomain (I := I) g p)
    (hinj : ∀ t ∈ Ioo (0 : ℝ) 1,
      Function.Injective (mfderiv 𝓘(ℝ, E) I
        (fun b : E => (expMap (I := I) g p
          (show TangentSpace I p from b) : M)) (t • x)))
    (hRic : ∀ t ∈ Ioo (0 : ℝ) 1,
      0 ≤ ricciTensor (I := I) g (radialCurve (I := I) g p x t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)) :
    curveDensity (I := I) g (radialCurve (I := I) g p x)
        (fun i : Fin (Module.finrank ℝ E) =>
          radialJacobiField (I := I) g p x (chartModelBasis E i)) 1 ≤
      normalChartDensity (I := I) g p 0 := by
  classical
  by_cases hx : x = 0
  · subst x
    have hsrc := NormalCoordinates.zero_mem_expMapDiffeo_source (I := I) g p
    have hrad : ‖(0 : E)‖ < expMapC2Radius (I := I) g p := by
      simpa only [norm_zero] using expMapC2Radius_pos (I := I) g p
    rw [normalDensity_radial (I := I) g p hsrc hrad]
    apply le_of_eq
    unfold curveDensity curveGram radialJacobiGram
    congr 2
    ext i j
    simp only [Matrix.of_apply, radialCurve]
    rw [one_smul]
    rfl
  · let d : ℕ := Module.finrank ℝ E - 1
    obtain ⟨w, hON, hperp'⟩ :=
      exists_perp_pos (I := I) g p (show TangentSpace I p from x)
        (g.pos p x hx)
    have hperp : ∀ i, g.inner p x (w i) = 0 := by
      intro i
      exact (g.symm p (show TangentSpace I p from x) (w i)).trans (hperp' i)
    have hsplit := rawDens_split (I := I) g p hx hdom w hON hperp
    by_cases hd0 : d = 0
    · have hgram : curveGram (I := I) g
          (radialCurve (I := I) g p x)
          (fun i : Fin d => radialJacobiField (I := I) g p x (w i)) 1 = 1 := by
        ext i
        exact isEmptyElim (hd0 ▸ i)
      have htrans : curveDensity (I := I) g
          (radialCurve (I := I) g p x)
          (fun i : Fin d => radialJacobiField (I := I) g p x (w i)) 1 = 1 := by
        unfold curveDensity
        rw [hgram, Matrix.det_one, Real.sqrt_one]
      rw [hsplit]
      simp only [d, htrans, mul_one]
      exact le_rfl
    · have hd : 0 < d := Nat.pos_of_ne_zero hd0
      let a : ℝ := Real.sqrt (g.inner p x x)
      have ha : 0 < a := by
        simpa only [a] using Real.sqrt_pos.mpr (g.pos p x hx)
      have hspeed : ∀ t ∈ Ioo (0 : ℝ) 1,
          g.inner (radialCurve (I := I) g p x t)
            (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
            (curveVelocity (I := I) (radialCurve (I := I) g p x) t) = a ^ 2 := by
        intro t ht
        rw [rawSpeed_sq (I := I) g p x t ht.1.le (fun s hs =>
          hdom s ⟨hs.1, hs.2.trans ht.2.le⟩)]
        simpa only [a] using (Real.sq_sqrt (g.pos p x hx).le).symm
      have hanti := raw_ratio_inj (I := I) g p x a ha 1 (by norm_num)
        hdom hspeed hinj w hON hperp (by simpa only [d] using hd) hRic
      have hpole : Tendsto
          (fun t => curveDensity (I := I) g (radialCurve (I := I) g p x)
              (fun i => radialJacobiField (I := I) g p x (w i)) t /
            hyperbolicDensity 0 d t)
          (𝓝[>] (0 : ℝ)) (𝓝 1) := by
        simpa only [d, Fintype.card_fin] using
          tendsto_curveDensity_radialJacobiField_div_hyperbolicDensity_of_orthonormal
            (I := I) g p x w 0 hON
      have hbound : ∀ t ∈ Ioo (0 : ℝ) 1,
          curveDensity (I := I) g (radialCurve (I := I) g p x)
              (fun i => radialJacobiField (I := I) g p x (w i)) t ≤
            hyperbolicDensity 0 d t := by
        intro t ht
        have hpos : 0 < hyperbolicDensity 0 d t := hyperbolicDensity_pos (by norm_num) ht.1
        have hRatioLE :
            curveDensity (I := I) g (radialCurve (I := I) g p x)
                (fun i => radialJacobiField (I := I) g p x (w i)) t /
              hyperbolicDensity 0 d t ≤ 1 := by
          have hev : ∀ᶠ s in 𝓝[>] (0 : ℝ),
              curveDensity (I := I) g (radialCurve (I := I) g p x)
                  (fun i => radialJacobiField (I := I) g p x (w i)) t /
                hyperbolicDensity 0 d t ≤
              curveDensity (I := I) g (radialCurve (I := I) g p x)
                  (fun i => radialJacobiField (I := I) g p x (w i)) s /
                hyperbolicDensity 0 d s := by
            filter_upwards [Ioo_mem_nhdsGT ht.1] with s hs
            have hs1 : s ∈ Ioo (0 : ℝ) 1 := ⟨hs.1, hs.2.trans ht.2⟩
            exact hanti hs1 ht hs.2.le
          exact ge_of_tendsto hpole hev
        rwa [div_le_one hpos] at hRatioLE
      let γ := radialCurve (I := I) g p x
      let V : Fin d → ∀ t, TangentSpace I (γ t) :=
        fun i => radialJacobiField (I := I) g p x (w i)
      have hline : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
          (fun z : ℝ => z • x) 1 :=
        (contMDiff_id.smul contMDiff_const).contMDiffAt
      have hγ : ContMDiffAt 𝓘(ℝ, ℝ) I (1 : WithTop ℕ∞) γ 1 := by
        have hcurveExp : γ = fun t : ℝ =>
            expMap (I := I) g p (show TangentSpace I p from t • x) := by
          funext t
          rfl
        rw [hcurveExp]
        exact ((contMDiffAt_expMap (I := I) g p
          (hdom 1 ⟨zero_le_one, le_rfl⟩)).comp 1 hline).of_le
            (by decide : (1 : WithTop ℕ∞) ≤ ∞)
      have hVdiff : ∀ i,
          DifferentiableAt ℝ (chartRepAt (I := I) γ (V i) 1) 1 := by
        intro i
        have hcurveExp : γ = fun t : ℝ =>
            expMap (I := I) g p (show TangentSpace I p from t • x) := by
          funext t
          rfl
        rw [hcurveExp]
        exact differentiableAt_chartRep_radialJacobiField (I := I) g p x (w i)
          (hdom 1 ⟨zero_le_one, le_rfl⟩)
      have hcurveLim : Tendsto (curveDensity (I := I) g γ V)
          (𝓝[<] (1 : ℝ)) (𝓝 (curveDensity (I := I) g γ V 1)) :=
        (curveDensity_cont (I := I) (n := (1 : WithTop ℕ∞)) le_rfl
          g γ V 1 hγ hVdiff).tendsto.mono_left inf_le_left
      have hmodelLim : Tendsto (hyperbolicDensity 0 d) (𝓝[<] (1 : ℝ))
          (𝓝 (hyperbolicDensity 0 d 1)) :=
        (hyperbolicDen_continuous 0 d).continuousAt.tendsto.mono_left inf_le_left
      have htransModel : curveDensity (I := I) g γ V 1 ≤
          hyperbolicDensity 0 d 1 := by
        apply le_of_tendsto_of_tendsto hcurveLim hmodelLim
        filter_upwards [Ioo_mem_nhdsLT (by norm_num : (0 : ℝ) < 1)] with t ht
        simpa only [γ, V] using hbound t ht
      have htrans : curveDensity (I := I) g γ V 1 ≤ 1 := by
        simpa [hyperbolicDensity, hyperbolicSn] using htransModel
      have hncd : 0 ≤ normalChartDensity (I := I) g p 0 := by
        unfold normalChartDensity paramDensity
        exact Real.sqrt_nonneg _
      rw [hsplit]
      simpa only [γ, V, d, mul_one] using
        (mul_le_mul_of_nonneg_left htrans hncd)

omit [SigmaCompactSpace M] in
theorem rawDens_le_zero
    [PseudoEMetricSpace M]
    [RiemannianBundle (fun x : M => TangentSpace I x)]
    [IsRiemannianManifold I M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : IsMetricNorm (I := I) (M := M) g)
    (p : M) (x : E)
    (hdom : ∀ t ∈ Icc (0 : ℝ) 1,
      (show TangentSpace I p from t • x) ∈ expDomain (I := I) g p)
    (hminDist : ENNReal.ofReal (Real.sqrt (g.inner p x x)) ≤
      riemannianEDist I p
        (expMap (I := I) g p (show TangentSpace I p from x)))
    (hRic : ∀ t ∈ Ioo (0 : ℝ) 1,
      0 ≤ ricciTensor (I := I) g (radialCurve (I := I) g p x t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)
        (curveVelocity (I := I) (radialCurve (I := I) g p x) t)) :
    curveDensity (I := I) g (radialCurve (I := I) g p x)
        (fun i : Fin (Module.finrank ℝ E) =>
          radialJacobiField (I := I) g p x (chartModelBasis E i)) 1 ≤
      normalChartDensity (I := I) g p 0 := by
  classical
  by_cases hx : x = 0
  · subst x
    have hsrc := NormalCoordinates.zero_mem_expMapDiffeo_source (I := I) g p
    have hrad : ‖(0 : E)‖ < expMapC2Radius (I := I) g p := by
      simpa only [norm_zero] using expMapC2Radius_pos (I := I) g p
    rw [normalDensity_radial (I := I) g p hsrc hrad]
    apply le_of_eq
    unfold curveDensity curveGram radialJacobiGram
    congr 2
    ext i j
    simp only [Matrix.of_apply, radialCurve]
    rw [one_smul]
    rfl
  · let ℓ : ℝ := Real.sqrt (g.inner p x x)
    have hinner : 0 < g.inner p x x := g.pos p x hx
    have hℓ : 0 < ℓ := by
      simpa only [ℓ] using Real.sqrt_pos.mpr hinner
    have hℓne : ℓ ≠ 0 := hℓ.ne'
    have hsq : g.inner p x x = ℓ ^ 2 := by
      simpa only [ℓ] using (Real.sq_sqrt hinner.le).symm
    let u : E := ℓ⁻¹ • x
    have hunit : g.inner p u u = 1 := by
      dsimp only [u]
      change g.inner p (ℓ⁻¹ • (show TangentSpace I p from x))
        (ℓ⁻¹ • (show TangentSpace I p from x)) = 1
      rw [gInner_smul_self (I := I) g p ℓ⁻¹
        (show TangentSpace I p from x), hsq]
      rw [← mul_pow, inv_mul_cancel₀ hℓne, one_pow]
    have hlu : ℓ • u = x := by
      dsimp only [u]
      rw [smul_smul, mul_inv_cancel₀ hℓne, one_smul]
    have hu : u ≠ 0 := by
      intro hu0
      apply hx
      rw [← hlu, hu0, smul_zero]
    have hdomU : ∀ t ∈ Icc (0 : ℝ) ℓ,
        (show TangentSpace I p from t • u) ∈ expDomain (I := I) g p := by
      intro t ht
      have hinv : 0 ≤ ℓ⁻¹ := inv_nonneg.mpr hℓ.le
      have ht0 : 0 ≤ ℓ⁻¹ * t := mul_nonneg hinv ht.1
      have ht1 : ℓ⁻¹ * t ≤ 1 := by
        have hm := mul_le_mul_of_nonneg_left ht.2 hinv
        simpa only [inv_mul_cancel₀ hℓne] using hm
      simpa only [u, smul_smul, mul_comm] using
        hdom (ℓ⁻¹ * t) ⟨ht0, ht1⟩
    have hcurve : radialCurve (I := I) g p u =
        fun t => radialCurve (I := I) g p x (ℓ⁻¹ * t + 0) := by
      funext t
      unfold radialCurve
      congr 1
      simp only [u, smul_smul, add_zero]
      rw [mul_comm]
    have hmin : ∀ η : ℝ → M,
        ContMDiffOn 𝓘(ℝ, ℝ) I 1 η (Icc 0 ℓ) →
        η 0 = p →
        η ℓ = expMap (I := I) g p (show TangentSpace I p from ℓ • u) →
        arcLength (I := I) g (radialCurve (I := I) g p u) 0 ℓ ≤
          arcLength (I := I) g η 0 ℓ := by
      intro η hη hη0 hηℓ
      have hradLen : arcLength (I := I) g
          (radialCurve (I := I) g p u) 0 ℓ = ℓ := by
        unfold arcLength
        calc
          ∫ t in (0 : ℝ)..ℓ, Real.sqrt
              (g.inner (radialCurve (I := I) g p u t)
                (curveVelocity (I := I) (radialCurve (I := I) g p u) t)
                (curveVelocity (I := I) (radialCurve (I := I) g p u) t)) =
              ∫ _t in (0 : ℝ)..ℓ, (1 : ℝ) := by
                apply intervalIntegral.integral_congr
                intro t ht
                have ht' : t ∈ Icc (0 : ℝ) ℓ := by
                  simpa only [uIcc_of_le hℓ.le] using ht
                have hspeed := rawSpeed_sq (I := I) g p u t ht'.1
                  (fun s hs => hdomU s ⟨hs.1, hs.2.trans ht'.2⟩)
                change Real.sqrt
                    (g.inner (radialCurve (I := I) g p u t)
                      (curveVelocity (I := I) (radialCurve (I := I) g p u) t)
                      (curveVelocity (I := I) (radialCurve (I := I) g p u) t)) = 1
                rw [hspeed, hunit, Real.sqrt_one]
          _ = ℓ := by simp
      have hdist := Geodesic.riemannianEDist_le_arcLength
        (I := I) g hℓ.le hη (fun t _ =>
          hEnorm (η t) (mfderiv 𝓘(ℝ, ℝ) I η t (1 : ℝ)))
      have hdist' : riemannianEDist I p
          (expMap (I := I) g p (show TangentSpace I p from x)) ≤
          ENNReal.ofReal (arcLength (I := I) g η 0 ℓ) := by
        simpa only [hη0, hηℓ, hlu] using hdist
      have hof : ENNReal.ofReal ℓ ≤
          ENNReal.ofReal (arcLength (I := I) g η 0 ℓ) := by
        exact hminDist.trans hdist'
      have harc : 0 ≤ arcLength (I := I) g η 0 ℓ := by
        unfold arcLength
        apply intervalIntegral.integral_nonneg hℓ.le
        intro t _
        exact Real.sqrt_nonneg _
      have hle : ℓ ≤ arcLength (I := I) g η 0 ℓ :=
        (ENNReal.ofReal_le_ofReal_iff harc).mp hof
      rw [hradLen]
      exact hle
    obtain ⟨w, hON, hperp'⟩ :=
      exists_perp_pos (I := I) g p (show TangentSpace I p from u) (by
        simpa only [hunit] using (show (0 : ℝ) < 1 by norm_num))
    have hperp : ∀ i, g.inner p u (w i) = 0 := by
      intro i
      exact (g.symm p (show TangentSpace I p from u) (w i)).trans (hperp' i)
    have hRicU : ∀ t ∈ Ioo (0 : ℝ) ℓ,
        0 ≤ ricciTensor (I := I) g (radialCurve (I := I) g p u t)
          (curveVelocity (I := I) (radialCurve (I := I) g p u) t)
          (curveVelocity (I := I) (radialCurve (I := I) g p u) t) := by
      intro t ht
      let s : ℝ := ℓ⁻¹ * t + 0
      have hinv : 0 < ℓ⁻¹ := inv_pos.mpr hℓ
      have hs : s ∈ Ioo (0 : ℝ) 1 := by
        constructor
        · simpa only [s, add_zero] using mul_pos hinv ht.1
        · have hm := mul_lt_mul_of_pos_left ht.2 hinv
          simpa only [s, add_zero, inv_mul_cancel₀ hℓne] using hm
      have hline : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
          (fun z : ℝ => z • x) s :=
        (contMDiff_id.smul contMDiff_const).contMDiffAt
      have hγx : MDifferentiableAt 𝓘(ℝ, ℝ) I
          (radialCurve (I := I) g p x) (ℓ⁻¹ * t + 0) := by
        have hcurveExp : radialCurve (I := I) g p x = fun z : ℝ =>
            expMap (I := I) g p (show TangentSpace I p from z • x) := by
          funext z
          rfl
        rw [hcurveExp]
        simpa only [Function.comp_def, s, add_zero] using
          ((contMDiffAt_expMap (I := I) g p
            (hdom s ⟨hs.1.le, hs.2.le⟩)).comp s hline).mdifferentiableAt
              (by decide)
      have hvel := curveVelocity_comp_affine (I := I)
        (radialCurve (I := I) g p x) ℓ⁻¹ 0 t hγx
      have hvel' : curveVelocity (I := I) (radialCurve (I := I) g p u) t =
          ℓ⁻¹ • curveVelocity (I := I) (radialCurve (I := I) g p x) s := by
        rw [hcurve]
        simpa only [s] using hvel
      have hbase : radialCurve (I := I) g p u t =
          radialCurve (I := I) g p x s := by
        simpa only [s, add_zero] using congrFun hcurve t
      rw [hbase, hvel']
      have hbil : ricciTensor (I := I) g (radialCurve (I := I) g p x s)
          (ℓ⁻¹ • curveVelocity (I := I) (radialCurve (I := I) g p x) s)
          (ℓ⁻¹ • curveVelocity (I := I) (radialCurve (I := I) g p x) s) =
          ℓ⁻¹ ^ 2 * ricciTensor (I := I) g
            (radialCurve (I := I) g p x s)
            (curveVelocity (I := I) (radialCurve (I := I) g p x) s)
            (curveVelocity (I := I) (radialCurve (I := I) g p x) s) := by
        rw [(ricciTensor (I := I) g
          (radialCurve (I := I) g p x s)).map_smul]
        rw [smul_apply, smul_eq_mul]
        rw [(ricciTensor (I := I) g (radialCurve (I := I) g p x s)
          (curveVelocity (I := I) (radialCurve (I := I) g p x) s)).map_smul]
        simp only [smul_eq_mul]
        ring
      rw [hbil]
      exact mul_nonneg (sq_nonneg ℓ⁻¹) (hRic s hs)
    have hfac := rawDens_eq_trans (I := I) g p hu ℓ hℓ hdomU w hON hperp
    let d := Module.finrank ℝ E - 1
    by_cases hd0 : d = 0
    · have hgram : curveGram (I := I) g
          (radialCurve (I := I) g p u)
          (fun i : Fin d => radialJacobiField (I := I) g p u (w i)) ℓ = 1 := by
        ext i
        exact isEmptyElim (hd0 ▸ i)
      have htrans : curveDensity (I := I) g
          (radialCurve (I := I) g p u)
          (fun i : Fin d => radialJacobiField (I := I) g p u (w i)) ℓ = 1 := by
        unfold curveDensity
        rw [hgram, Matrix.det_one, Real.sqrt_one]
      have heq := hfac
      rw [← hlu]
      simpa only [d, hd0, pow_zero, mul_one, htrans] using heq.le
    · have hd : 0 < d := Nat.pos_of_ne_zero hd0
      have hbound := raw_density_le (I := I) g p u hunit ℓ hℓ hdomU hmin
        w hON hperp (by simpa only [d] using hd) hRicU
      let γ := radialCurve (I := I) g p u
      let V : Fin d → ∀ t, TangentSpace I (γ t) :=
        fun i => radialJacobiField (I := I) g p u (w i)
      have hline : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞
          (fun z : ℝ => z • u) ℓ :=
        (contMDiff_id.smul contMDiff_const).contMDiffAt
      have hγ : ContMDiffAt 𝓘(ℝ, ℝ) I (1 : WithTop ℕ∞) γ ℓ := by
        have hcurveExp : γ = fun t : ℝ =>
            expMap (I := I) g p (show TangentSpace I p from t • u) := by
          funext t
          rfl
        rw [hcurveExp]
        exact ((contMDiffAt_expMap (I := I) g p
          (hdomU ℓ ⟨hℓ.le, le_rfl⟩)).comp ℓ hline).of_le
            (by decide : (1 : WithTop ℕ∞) ≤ ∞)
      have hVdiff : ∀ i,
          DifferentiableAt ℝ (chartRepAt (I := I) γ (V i) ℓ) ℓ := by
        intro i
        have hcurveExp : γ = fun t : ℝ =>
            expMap (I := I) g p (show TangentSpace I p from t • u) := by
          funext t
          rfl
        rw [hcurveExp]
        exact differentiableAt_chartRep_radialJacobiField (I := I) g p u (w i)
          (hdomU ℓ ⟨hℓ.le, le_rfl⟩)
      have hcurveLim : Tendsto (curveDensity (I := I) g γ V)
          (𝓝[<] ℓ) (𝓝 (curveDensity (I := I) g γ V ℓ)) :=
        (curveDensity_cont (I := I) (n := (1 : WithTop ℕ∞)) le_rfl
          g γ V ℓ hγ hVdiff).tendsto.mono_left inf_le_left
      have hmodelLim : Tendsto (hyperbolicDensity 0 d) (𝓝[<] ℓ)
          (𝓝 (hyperbolicDensity 0 d ℓ)) :=
        (hyperbolicDen_continuous 0 d).continuousAt.tendsto.mono_left inf_le_left
      have htransModel : curveDensity (I := I) g γ V ℓ ≤
          hyperbolicDensity 0 d ℓ := by
        apply le_of_tendsto_of_tendsto hcurveLim hmodelLim
        filter_upwards [Ioo_mem_nhdsLT hℓ] with t ht
        simpa only [γ, V, d] using hbound t ht
      have htrans : curveDensity (I := I) g γ V ℓ ≤ ℓ ^ d := by
        simpa [hyperbolicDensity, hyperbolicSn] using htransModel
      have hp : 0 < ℓ ^ d := pow_pos hℓ d
      have hncd : 0 ≤ normalChartDensity (I := I) g p 0 := by
        unfold normalChartDensity paramDensity
        exact Real.sqrt_nonneg _
      have hmul : curveDensity (I := I) g (radialCurve (I := I) g p x)
              (fun i : Fin (Module.finrank ℝ E) =>
                radialJacobiField (I := I) g p x (chartModelBasis E i)) 1 *
            ℓ ^ d ≤ normalChartDensity (I := I) g p 0 * ℓ ^ d := by
        calc
          curveDensity (I := I) g (radialCurve (I := I) g p x)
                (fun i : Fin (Module.finrank ℝ E) =>
                  radialJacobiField (I := I) g p x (chartModelBasis E i)) 1 *
              ℓ ^ d = normalChartDensity (I := I) g p 0 *
              curveDensity (I := I) g γ V ℓ := by
                rw [← hlu]
                simpa only [d, γ, V] using hfac
          _ ≤ normalChartDensity (I := I) g p 0 * ℓ ^ d :=
            mul_le_mul_of_nonneg_left htrans hncd
      exact le_of_mul_le_mul_right hmul hp

end VolumeComparison
end Riemannian
end Geometry
end DifferentialGeometry
