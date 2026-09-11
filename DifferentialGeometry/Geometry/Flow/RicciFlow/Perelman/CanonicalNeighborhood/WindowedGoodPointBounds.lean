import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.WindowedShiTerminal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Evolution.Scalar.TerminalSlope
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.ScalarLaplacianJet
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientKappaModelCurvatureWindow


set_option autoImplicit false
noncomputable section
open Bundle Manifold Filter Set
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian DifferentialGeometry.Integral.Measure

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle


def windowedGoodPointConstant (K : ℝ) : ℝ :=
  max (9 * |windowedShiConstant K 1|)
    (3 ^ 6 * |windowedShiConstant K 2| + 2 * 3 ^ 4 * windowedShiConstant K 0 ^ 2) + 1


theorem windowedGoodPointConstant_pos (K : ℝ) : 0 < windowedGoodPointConstant K := by
  have hh := le_max_left (9 * |windowedShiConstant K 1|)
    (3 ^ 6 * |windowedShiConstant K 2| + 2 * 3 ^ 4 * windowedShiConstant K 0 ^ 2)
  have ha := abs_nonneg (windowedShiConstant K 1)
  dsimp [windowedGoodPointConstant]
  linarith

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}

private local instance goodPointC1 : IsManifold I3 1 M :=
  IsManifold.of_le (n := ∞) (by decide)


theorem WindowedModelWitness.scalar_gradient_bound
    (hS : IsSolutionOn S) {eps kappa K : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness eps kappa S x t) (heps4 : eps ≤ 1 / 4) (hK : 0 ≤ K)
    (hregular : interior D.carrier ⊆ D.regular)
    (hmodel : ∀ s ∈ Icc (-(4 : ℝ)) 0, ∀ y ∈
      riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint 2,
        W.model.rmNormSq s y ≤ K ^ 2) (v : TangentSpace I3 x) :
    |scalarDifferential S t x v| ≤
      2 * windowedGoodPointConstant K * S.scalar t x * Real.sqrt (S.scalar t x) *
        Real.sqrt ((S.base.metric t).inner x v v) := by
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let Q := S.scalar t x
  have hQ : 0 < Q := W.scalar_pos
  let B := windowedShiConstant K 1
  have hjet := W.terminal_curvature_derivative_bound hS heps4 hK hregular hmodel 1
  have hroot : Real.sqrt (nablaKRm04NormSqIntrinsic S 1 t x) ≤ Q * Real.sqrt Q * |B| := by
    have hh := Real.sqrt_le_sqrt hjet
    have hsq : Q ^ (2 + 1) * B ^ 2 = (Q * Real.sqrt Q * |B|) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt W.scalar_pos.le, sq_abs]
      ring
    rw [hsq, Real.sqrt_sq (by positivity)] at hh
    exact hh
  have hc : 9 * |B| ≤ 2 * windowedGoodPointConstant K := by
    have hh := le_max_left (9 * |B|)
      (3 ^ 6 * |windowedShiConstant K 2| + 2 * 3 ^ 4 * windowedShiConstant K 0 ^ 2)
    have hp := windowedGoodPointConstant_pos K
    dsimp [windowedGoodPointConstant, B] at *
    linarith
  have hg := abs_scalarDifferential_le S t x v
  have hdim : (Module.finrank ℝ ThreeSpace : ℝ) ^ 2 = 9 := by norm_num [ThreeSpace]
  rw [hdim] at hg
  calc
    _ ≤ 9 * Real.sqrt (nablaKRm04NormSqIntrinsic S 1 t x) *
        Real.sqrt ((S.base.metric t).inner x v v) := hg
    _ ≤ 9 * (Q * Real.sqrt Q * |B|) * Real.sqrt ((S.base.metric t).inner x v v) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hroot (by norm_num))
        (Real.sqrt_nonneg _)
    _ = (9 * |B|) * (Q * Real.sqrt Q) * Real.sqrt ((S.base.metric t).inner x v v) := by ring
    _ ≤ (2 * windowedGoodPointConstant K) * (Q * Real.sqrt Q) *
        Real.sqrt ((S.base.metric t).inner x v v) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity))
        (Real.sqrt_nonneg _)
    _ = _ := by ring


theorem WindowedModelWitness.normalized_interior_scalar_derivative_bound
    (hS : IsSolutionOn S) {eps kappa K : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness eps kappa S x t) (heps4 : eps ≤ 1 / 4) (hK : 0 ≤ K)
    (hregular : interior D.carrier ⊆ D.regular)
    (hmodel : ∀ s ∈ Icc (-(4 : ℝ)) 0, ∀ y ∈
      riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint 2,
        W.model.rmNormSq s y ≤ K ^ 2) {r : ℝ} (hr : r ∈ Ioo (-1 : ℝ) 0) :
    |deriv (fun s => (parabolicSolution S t (S.scalar t x) W.scalar_pos W.time_mem).scalar s x) r| ≤
      windowedGoodPointConstant K := by
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  let P := parabolicSolution S t (S.scalar t x) W.scalar_pos W.time_mem
  have hP : IsSolutionOn P := parabolicSolution_isSolutionOn S hS t _ W.scalar_pos W.time_mem
  have hreg : r ∈ (parabolicInterval D t (S.scalar t x) W.time_mem).regular :=
    (W.normalized_fixed_window heps4 hregular).2 ⟨by linarith [hr.1], hr.2⟩
  have hd := (scalar_curvature_evolution P hP ⟨r, hreg⟩ x).hasDerivAt
    ((parabolicInterval D t (S.scalar t x) W.time_mem).regular_mem_nhds hreg)
  have h2 := W.normalized_interior_curvature_derivative_bound hS heps4 hK hregular hmodel 2 hr
  have h0 := le_sq_of_sqrt_le (normSq0S_nonneg (I := I3) _ _ _ _)
    (W.normalized_interior_curvature_derivative_bound hS heps4 hK hregular hmodel 0 hr)
  have hlap := abs_laplacian_scalar_le_second_curvature P r x
  have hric := ricciSq_le_rm04 (I := I3) (P.base.metric r) (P.base.metric r) x
  have hric0 := normSq0S_nonneg (I := I3) (P.family.metric r) x 2 (P.ricci r x)
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  rw [hdim] at hlap hric
  have hlap' : |laplacianAt (I := I3) (flowG P) r (P.scalar r) x| ≤
      3 ^ 6 * |windowedShiConstant K 2| :=
    hlap.trans (mul_le_mul_of_nonneg_left (h2.trans (le_abs_self _)) (by norm_num))
  have hric' : normSq0S (I := I3) (P.family.metric r) x 2 (P.ricci r x) ≤
      3 ^ 4 * windowedShiConstant K 0 ^ 2 :=
    hric.trans (mul_le_mul_of_nonneg_left h0 (by norm_num))
  have hc := le_max_right (9 * |windowedShiConstant K 1|)
    (3 ^ 6 * |windowedShiConstant K 2| + 2 * 3 ^ 4 * windowedShiConstant K 0 ^ 2)
  rw [hd.deriv]
  calc
    _ ≤ |laplacianAt (I := I3) (flowG P) r (P.scalar r) x| +
        |2 * normSq0S (I := I3) (P.family.metric r) x 2 (P.ricci r x)| := abs_add_le _ _
    _ ≤ 3 ^ 6 * |windowedShiConstant K 2| + 2 * 3 ^ 4 * windowedShiConstant K 0 ^ 2 := by
      rw [abs_of_nonneg (mul_nonneg (by norm_num) hric0)]
      linarith
    _ ≤ windowedGoodPointConstant K := by
      dsimp [windowedGoodPointConstant]
      linarith


theorem WindowedModelWitness.scalar_left_derivative_bound
    (hS : IsSolutionOn S) {eps kappa K : ℝ} {x : M} {t : ℝ}
    (W : WindowedModelWitness eps kappa S x t) (heps4 : eps ≤ 1 / 4) (hK : 0 ≤ K)
    (hregular : interior D.carrier ⊆ D.regular)
    (hmodel : ∀ s ∈ Icc (-(4 : ℝ)) 0, ∀ y ∈
      riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint 2,
        W.model.rmNormSq s y ≤ K ^ 2) :
    |derivWithin (fun s => S.scalar s x) (Iic t) t| ≤
      windowedGoodPointConstant K * S.scalar t x ^ 2 := by
  let P := parabolicSolution S t (S.scalar t x) W.scalar_pos W.time_mem
  have hP : IsSolutionOn P := parabolicSolution_isSolutionOn S hS t _ W.scalar_pos W.time_mem
  obtain ⟨hslab, hreg⟩ := W.normalized_fixed_window heps4 hregular
  have hcont : ContinuousOn (fun s => P.scalar s x) (Icc (-1 : ℝ) 0) := by
    have hmap : Continuous (fun s : ℝ => (s, x)) := continuous_id.prodMk continuous_const
    have hmaps : MapsTo (fun s : ℝ => (s, x)) (Icc (-1 : ℝ) 0)
        ((parabolicInterval D t (S.scalar t x) W.time_mem).carrier ×ˢ (univ : Set M)) :=
      fun s hs => ⟨hslab ⟨by linarith [hs.1], hs.2⟩, mem_univ x⟩
    exact ContinuousOn.comp (f := fun s : ℝ => (s, x))
      (g := fun q : ℝ × M => P.scalar q.1 q.2) hP.scalarCont hmap.continuousOn hmaps
  have hdiff : ∀ r ∈ Ioo (-1 : ℝ) 0, DifferentiableAt ℝ (fun s => P.scalar s x) r := by
    intro r hr
    have hrt := hreg ⟨by linarith [hr.1], hr.2⟩
    exact (hP.scalarTime ((parabolicInterval D t (S.scalar t x) W.time_mem).regular_subset hrt) Subset.rfl x).differentiableAt
      ((parabolicInterval D t (S.scalar t x) W.time_mem).regular_mem_nhds hrt)
  have hb := abs_derivWithin_Iic_le_of_interior_bound (fun s => P.scalar s x)
    (a := -1) (b := 0) (by norm_num) (windowedGoodPointConstant_pos K).le hcont hdiff
    (fun _ hr => W.normalized_interior_scalar_derivative_bound hS heps4 hK hregular hmodel hr)
  have hlo : t - (eps * S.scalar t x)⁻¹ < t := by
    have hp : 0 < (eps * S.scalar t x)⁻¹ := inv_pos.mpr (mul_pos W.eps_pos W.scalar_pos)
    linarith
  have hf : DifferentiableWithinAt ℝ (fun s => S.scalar s x) (Iic t) t :=
    ((hS.scalarTime (K := Icc (t - (eps * S.scalar t x)⁻¹) t)
      ⟨hlo.le, le_rfl⟩ W.window_mem x).hasDerivWithinAt.mono_of_mem_nhdsWithin
        (Icc_mem_nhdsLE hlo)).differentiableWithinAt
  have hscale := derivWithin_parabolic_scalar_Iic (fun s => S.scalar s x) t
    (S.scalar t x) W.scalar_pos hf
  have heq : derivWithin (fun s => P.scalar s x) (Iic 0) 0 =
      (S.scalar t x)⁻¹ ^ 2 * derivWithin (fun s => S.scalar s x) (Iic t) t := by
    simpa only [P, parabolicSolution_scalar, parabolicTime] using hscale
  rw [heq, abs_mul, abs_of_nonneg (sq_nonneg _)] at hb
  have hh := mul_le_mul_of_nonneg_left hb (sq_nonneg (S.scalar t x))
  have hc : S.scalar t x ^ 2 * ((S.scalar t x)⁻¹ ^ 2 *
      |derivWithin (fun s => S.scalar s x) (Iic t) t|) =
      |derivWithin (fun s => S.scalar s x) (Iic t) t| := by
    rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ W.scalar_pos.ne', one_pow, one_mul]
  rw [hc] at hh
  simpa only [mul_comm] using hh


theorem good_point_derivatives_of_modelCurvatureBound
    {kappa : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar C : ℝ, 0 < epsStar ∧ 0 < C ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (D : RealTimeInterval) (S : SolutionOn (I := I3) (M := M) D),
        IsSolutionOn S → interior D.carrier ⊆ D.regular →
          ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
            ∀ x t, Nonempty (WindowedModelWitness eps kappa S x t) →
              (∀ v : TangentSpace I3 x, |scalarDifferential S t x v| ≤
                2 * C * S.scalar t x * Real.sqrt (S.scalar t x) *
                  Real.sqrt ((S.base.metric t).inner x v v)) ∧
              |derivWithin (fun s => S.scalar s x) (Iic t) t| ≤ C * S.scalar t x ^ 2 := by
  obtain ⟨K, hK, hmodel⟩ := hmod
  refine ⟨1 / 4, windowedGoodPointConstant K, by norm_num,
    windowedGoodPointConstant_pos K, ?_⟩
  intro M _ _ _ _ _ D S hS hregular eps _ heps x t hW
  obtain ⟨W⟩ := hW
  have hmodel' : ∀ s ∈ Icc (-(4 : ℝ)) 0, ∀ y ∈
      riemannianClosedBallOf (W.model.S.base.metric 0) W.model.basepoint 2,
        W.model.rmNormSq s y ≤ K ^ 2 := by
    intro s hs y hy
    exact hmodel W.model W.model_ancient W.model_scalar_base s hs y
      (riemannianClosedBallOf_mono (W.model.S.base.metric 0) W.model.basepoint
        (by norm_num : (2 : ℝ) ≤ 3) hy)
  exact ⟨fun v => W.scalar_gradient_bound hS heps hK hregular hmodel' v,
    W.scalar_left_derivative_bound hS heps hK hregular hmodel'⟩


theorem good_point_derivatives_closed_interval
    {kappa : ℝ} (hmod : ModelCurvatureBoundNearBase.{u, 0, 0} I3 kappa) :
    ∃ epsStar C : ℝ, 0 < epsStar ∧ 0 < C ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (a b : ℝ) (hab : a ≤ b)
        (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closed a b hab)),
        IsSolutionOn S → ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
          ∀ x t, Nonempty (WindowedModelWitness eps kappa S x t) →
            (∀ v : TangentSpace I3 x, |scalarDifferential S t x v| ≤
              2 * C * S.scalar t x * Real.sqrt (S.scalar t x) *
                Real.sqrt ((S.base.metric t).inner x v v)) ∧
            |derivWithin (fun s => S.scalar s x) (Iic t) t| ≤ C * S.scalar t x ^ 2 := by
  obtain ⟨epsStar, C, heps, hC, hbound⟩ := good_point_derivatives_of_modelCurvatureBound hmod
  refine ⟨epsStar, C, heps, hC, ?_⟩
  intro M _ _ _ _ _ a b hab S hS
  exact hbound M (RealTimeInterval.closed a b hab) S hS
    (by simp only [RealTimeInterval.closed, interior_Icc, Subset.rfl])


theorem canonical_neighborhood_good_point_derivatives {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar C : ℝ, 0 < epsStar ∧ 0 < C ∧
      ∀ (M : Type u) [TopologicalSpace M] [ChartedSpace ThreeSpace M]
        [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
        (a b : ℝ) (hab : a ≤ b)
        (S : SolutionOn (I := I3) (M := M) (RealTimeInterval.closed a b hab)),
        IsSolutionOn S → ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
          ∀ x t, Nonempty (WindowedModelWitness eps kappa S x t) →
            (∀ v : TangentSpace I3 x, |scalarDifferential S t x v| ≤
              2 * C * S.scalar t x * Real.sqrt (S.scalar t x) *
                Real.sqrt ((S.base.metric t).inner x v v)) ∧
            |derivWithin (fun s => S.scalar s x) (Iic t) t| ≤ C * S.scalar t x ^ 2 := by
  exact good_point_derivatives_closed_interval
    (KappaSolutions.ancientKappa_modelCurvatureBoundNearBase
      (I := I3) (by simp [ThreeSpace]) hkappa)

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
