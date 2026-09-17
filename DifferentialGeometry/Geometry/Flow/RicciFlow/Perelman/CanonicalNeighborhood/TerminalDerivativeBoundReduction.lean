import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalShiDerivativeBounds
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BoundedCurvatureAtDistanceProducer
import DifferentialGeometry.Geometry.Curvature.ScalarControlsRm

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact

theorem terminalDerivativeBoundProducer_iff_boundedCurvatureAtDistanceConjunct
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} :
    TerminalDerivativeBoundProducer.{u} kappa sigma Phi ↔
      (∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
          BoundedAtDistance X ∧ TerminalDerivativeBounds X) :=
  (bounded_curvature_at_distance_iff_terminalDerivativeBoundProducer).symm

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

namespace DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.Tensor0SBundle
open scoped _root_.Manifold ContDiff BigOperators

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem normSq_metricRm04_le_scalar_sq_of_ricci_nonnegative
    (g : SmoothRiemannianMetric I M) (x : M) (hdim : Module.finrank ℝ E = 3)
    (hRic : RicciNonnegAt (I := I) (metricRicciAt (I := I) (M := M) g x)) :
    normSq0S (I := I) g x 4 (metricRm04 (I := I) (M := M) g x) ≤
      100 ^ 2 * (metricScalarAt (I := I) (M := M) g x) ^ 2 := by
  have hdimx : Module.finrank ℝ (TangentSpace I x) = 3 := hdim
  obtain ⟨B, hB⟩ := exists_orthonormalBasisAt (I := I) g x hdimx
  have hinv : MetricInverseInBasis (I := I) g x B delta3 :=
    orthonormal_invBasis3 (I := I) g B hB
  have hsymm : RicciSymAt (I := I) (metricRicciAt (I := I) (M := M) g x) :=
    ricciSym_of_basis (I := I) B _ (fun i j => metricRicciSymm (I := I) g B delta3 hinv i j)
  have hbound := normSqLeOfFirstTrace (I := I) (g := g)
    (Ric := metricRicciAt (I := I) (M := M) g x)
    (scalar := metricScalarAt (I := I) (M := M) g x)
    (Rm04 := metricRm04At (I := I) (M := M) g x) hdimx hsymm hRic
    (fun basis horth => metricRiemannFromRicci3DTraceDataAt (I := I) g x basis horth)
  simpa only [metricRm04_apply] using hbound

omit [T2Space M] in
theorem metricRicciAt_le_scalar_of_unit_of_ricci_nonnegative
    (g : SmoothRiemannianMetric I M) (x : M) (hdim : Module.finrank ℝ E = 3)
    (hRic : RicciNonnegAt (I := I) (metricRicciAt (I := I) (M := M) g x))
    (u : TangentSpace I x) (hu : g.inner x u u = 1) :
    metricRicciAt (I := I) (M := M) g x (vec2 u u) ≤
      metricScalarAt (I := I) (M := M) g x := by
  classical
  have hdimx : Module.finrank ℝ (TangentSpace I x) = 3 := hdim
  let D := (tangentMetricData (I := I) g x).metric
  let : InnerProductSpace.Core ℝ (TangentSpace I x) := D.toCore
  let : NormedAddCommGroup (TangentSpace I x) :=
    @InnerProductSpace.Core.toNormedAddCommGroup ℝ (TangentSpace I x) _ _ _ D.toCore
  let : InnerProductSpace ℝ (TangentSpace I x) :=
    @InnerProductSpace.ofCore ℝ (TangentSpace I x) _ _ _ D.toCore.toCore
  have huInner : Inner.inner ℝ u u = 1 := by
    calc Inner.inner ℝ u u = D.inner u u := MetricFiberData.toCore_inner D u u
      _ = g.inner x u u := TangentMetricData.inner_eq (tangentMetricData (I := I) g x) u u
      _ = 1 := hu
  have huON : Orthonormal ℝ ((↑) : ({u} : Set (TangentSpace I x)) → TangentSpace I x) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi : (i : TangentSpace I x) = u := i.2
    have hj : (j : TangentSpace I x) = u := j.2
    have hij : i = j := Subtype.ext (hi.trans hj.symm)
    rw [hi, hj, huInner, if_pos hij]
  obtain ⟨s, orthBasis, hus, horthBasis⟩ := huON.exists_orthonormalBasis_extension
  let basis := orthBasis.toBasis
  let iu : s := ⟨u, hus (Set.mem_singleton u)⟩
  have hbasis (i : s) : basis i = (i : TangentSpace I x) := congrFun horthBasis i
  have hbu : basis iu = u := by rw [hbasis]
  have hON : ∀ i j, g.inner x (basis i) (basis j) = if i = j then (1 : ℝ) else 0 := by
    intro i j
    rw [← TangentMetricData.inner_eq (tangentMetricData (I := I) g x)]
    change D.inner (basis i) (basis j) = _
    rw [← MetricFiberData.toCore_inner D]
    exact orthonormal_iff_ite.mp orthBasis.orthonormal i j
  have hinv : MetricInverseInBasis (I := I) g x basis (identityInvMetric (Idx := s)) := by
    have h := metricInverseInBasis_of_orthonormal (I := I) g basis hON
    intro i j
    simpa [identityInvMetric, diagonalInvMetric] using h i j
  have hscalar : metricScalarAt (I := I) (M := M) g x =
      ∑ i, metricRicciAt (I := I) (M := M) g x (vec2 (basis i) (basis i)) := by
    calc metricScalarAt (I := I) (M := M) g x =
        DifferentialGeometry.Geometry.Operator.metricTracePair0SAt (I := I) g
          (metricRicciAt (I := I) (M := M) g x) := metricScalarAt_def (I := I) g x
      _ = ∑ i, metricRicciAt (I := I) (M := M) g x (vec2 (basis i) (basis i)) := by
        rw [DifferentialGeometry.Geometry.Operator.metricTracePair0SAt_eq_sum_basis
          (I := I) g basis (identityInvMetric (Idx := s)) hinv]
        simp [identityInvMetric, diagonalInvMetric]
  have hrow : metricRicciAt (I := I) (M := M) g x (vec2 (basis iu) (basis iu)) ≤
      ∑ i, metricRicciAt (I := I) (M := M) g x (vec2 (basis i) (basis i)) :=
    Finset.single_le_sum
      (s := (Finset.univ : Finset s))
      (f := fun i => metricRicciAt (I := I) (M := M) g x (vec2 (basis i) (basis i)))
      (fun i _ => hRic (basis i)) (Finset.mem_univ iu)
  rw [← hscalar] at hrow
  rwa [hbu] at hrow

omit [T2Space M] in
theorem metricRicciAt_le_scalar_mul_inner_of_ricci_nonnegative
    (g : SmoothRiemannianMetric I M) (x : M) (hdim : Module.finrank ℝ E = 3)
    (hRic : RicciNonnegAt (I := I) (metricRicciAt (I := I) (M := M) g x))
    (v : TangentSpace I x) :
    metricRicciAt (I := I) (M := M) g x (vec2 v v) ≤
      metricScalarAt (I := I) (M := M) g x * g.inner x v v := by
  by_cases hv : v = 0
  · subst hv
    have hzero : metricRicciAt (I := I) (M := M) g x
        (vec2 (0 : TangentSpace I x) 0) = 0 :=
      (metricRicciAt (I := I) (M := M) g x).map_coord_zero (i := 0) (by simp [vec2])
    rw [hzero, (g.inner x).map_zero, zero_apply, mul_zero]
  · have hpos : 0 < g.inner x v v := g.pos x v hv
    let r := Real.sqrt (g.inner x v v)
    let u := r⁻¹ • v
    have hr : 0 < r := Real.sqrt_pos.mpr hpos
    have hu : g.inner x u u = 1 := by
      dsimp only [u]
      rw [(g.inner x).map_smul]
      change r⁻¹ * ((g.inner x v) (r⁻¹ • v)) = 1
      rw [(g.inner x v).map_smul]
      simp only [smul_eq_mul]
      have hrSq : r ^ 2 = g.inner x v v := by
        dsimp only [r]
        exact Real.sq_sqrt hpos.le
      rw [← hrSq]
      field_simp [ne_of_gt hr]
    have hunit := metricRicciAt_le_scalar_of_unit_of_ricci_nonnegative
      (I := I) g x hdim hRic u hu
    have hvEq : v = r • u := by
      dsimp only [u]
      rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hr), one_smul]
    rw [hvEq]
    have hricScale := tensor02_smul2 (I := I) (M := M)
      (metricRicciAt (I := I) (M := M) g x) r u
    have hricScale' : metricRicciAt (I := I) (M := M) g x
        (vec2 (r • u) (r • u)) =
        r * r * metricRicciAt (I := I) (M := M) g x (vec2 u u) := by
      have hru : vec2 (I := I) (r • u) (r • u) = fun _ : Fin 2 => r • u := by
        funext i
        fin_cases i <;> rfl
      have hu' : vec2 (I := I) u u = fun _ : Fin 2 => u := by
        funext i
        fin_cases i <;> rfl
      rw [hru, hu']
      simpa [quad02] using hricScale
    rw [hricScale']
    have hinnerScale : g.inner x (r • u) (r • u) = r ^ 2 := by
      rw [(g.inner x).map_smul]
      change r * ((g.inner x u) (r • u)) = r ^ 2
      rw [(g.inner x u).map_smul]
      simp [smul_eq_mul, hu, pow_two]
    rw [hinnerScale]
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hunit (sq_nonneg r)

theorem sqrt_normSq_metricRm04_le_hundred_mul_scalar_of_ricci_nonnegative
    (g : SmoothRiemannianMetric I M) (x : M) (hdim : Module.finrank ℝ E = 3)
    (hRic : RicciNonnegAt (I := I) (metricRicciAt (I := I) (M := M) g x))
    (hscal : 0 ≤ metricScalarAt (I := I) (M := M) g x) :
    Real.sqrt (normSq0S (I := I) g x 4 (metricRm04 (I := I) (M := M) g x)) ≤
      100 * metricScalarAt (I := I) (M := M) g x := by
  have h := normSq_metricRm04_le_scalar_sq_of_ricci_nonnegative (I := I) g x hdim hRic
  have hsq : 100 ^ 2 * (metricScalarAt (I := I) (M := M) g x) ^ 2 =
      (100 * metricScalarAt (I := I) (M := M) g x) ^ 2 := by ring
  calc Real.sqrt (normSq0S (I := I) g x 4 (metricRm04 (I := I) (M := M) g x))
      ≤ Real.sqrt (100 ^ 2 * (metricScalarAt (I := I) (M := M) g x) ^ 2) :=
        Real.sqrt_le_sqrt h
    _ = Real.sqrt ((100 * metricScalarAt (I := I) (M := M) g x) ^ 2) := by rw [hsq]
    _ = |100 * metricScalarAt (I := I) (M := M) g x| := Real.sqrt_sq_eq_abs _
    _ = 100 * metricScalarAt (I := I) (M := M) g x :=
        abs_of_nonneg (by linarith)

end DifferentialGeometry.Geometry.Curvature

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

universe u uE uH

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Tensor0SBundle

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact

theorem pointedFlowRmNormLeScalar_hundred_of_ricciNonnegative
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E] {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    (hdim : Module.finrank ℝ E = 3)
    (F : PointedFlowData.{u, uE, uH} (I := I) D)
    (hric : ∀ t ∈ D.carrier, ∀ x : F.M, ∀ v : TangentSpace I x,
      0 ≤ F.S.ricciAt t x (vec2 v v))
    (hscal : ∀ t ∈ D.carrier, ∀ x : F.M, 0 ≤ F.S.scalar t x) :
    PointedFlowRmNormLeScalar (I := I) F 100 := by
  intro t ht x
  have h := sqrt_normSq_metricRm04_le_hundred_mul_scalar_of_ricci_nonnegative (I := I)
    (F.S.base.metric t) x hdim (fun v => hric t ht x v) (hscal t ht x)
  simpa only [PointedFlowData.rmNormSq, SolutionOn.family, SolutionFamily.rm04,
    metricRm04_apply, SolutionOn.scalar, SolutionFamily.scalar] using h

theorem uniformRmNormSqBound_of_uniformScalarBound_and_ricciNonnegative
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    {C : ℝ} (hscal : ∀ i : ℕ, PointedFlowScalarBounded (X.term i) C)
    (hric : ∀ i : ℕ, ∀ t ∈ (X.interval i).carrier, ∀ x : (X.term i).M,
      ∀ v : TangentSpace I3 x, 0 ≤ (X.term i).S.ricciAt t x (vec2 v v)) :
    UniformRmNormSqBound X :=
  uniformRmNormSqBound_of_uniformScalarBound X (by norm_num : (0 : ℝ) ≤ 100) hscal fun i =>
    pointedFlowRmNormLeScalar_hundred_of_ricciNonnegative (I := I3) (by simp [ThreeSpace])
      (X.term i) (hric i) fun t ht x => (hscal i t ht x).1

theorem ricciTensorBoundProducer_of_uniformScalarBound_and_ricciNonnegative
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} {C epsStar : ℝ} (hC : 0 < C) (hepsStar : 0 < epsStar)
    (hscal : ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ i : ℕ,
        ∀ s ∈ Set.Icc (-(modelDepth eps)) 0, ∀ x : (X.term i).M,
          (X.term i).S.scalar s x ≤ C)
    (hric : ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ i : ℕ,
        ∀ s ∈ Set.Icc (-(modelDepth eps)) 0, ∀ x : (X.term i).M,
          ∀ v : TangentSpace I3 x, 0 ≤ (X.term i).S.ricciAt s x (vec2 v v)) :
    RicciTensorBoundProducer.{u} kappa sigma Phi := by
  refine ⟨C / 2, by linarith, epsStar, hepsStar, ?_⟩
  intro eps heps hle X i s hs x v
  have hv : 0 ≤ ((X.term i).S.base.metric s).inner x v v := by
    by_cases hv0 : v = 0
    · simp [hv0]
    · exact (((X.term i).S.base.metric s).pos x v hv0).le
  have hscal' : metricScalarAt (I := I3) ((X.term i).S.base.metric s) x ≤ C :=
    hscal eps heps hle X i s hs x
  have hric' : 0 ≤ metricRicciAt (I := I3) ((X.term i).S.base.metric s) x (vec2 v v) :=
    hric eps heps hle X i s hs x v
  have hup := metricRicciAt_le_scalar_mul_inner_of_ricci_nonnegative (I := I3)
    ((X.term i).S.base.metric s) x (by simp [ThreeSpace])
    (fun w => hric eps heps hle X i s hs x w) v
  have hdim : ((Module.finrank ℝ ThreeSpace : ℝ) - 1) * (C / 2) = C := by
    have h3 : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
    rw [h3]
    ring
  refine ⟨hric', ?_⟩
  have hchain : metricRicciAt (I := I3) ((X.term i).S.base.metric s) x (vec2 v v)
      ≤ ((Module.finrank ℝ ThreeSpace : ℝ) - 1) * (C / 2) *
          ((X.term i).S.base.metric s).inner x v v := by
    calc metricRicciAt (I := I3) ((X.term i).S.base.metric s) x (vec2 v v)
        ≤ metricScalarAt (I := I3) ((X.term i).S.base.metric s) x *
            ((X.term i).S.base.metric s).inner x v v := hup
      _ ≤ C * ((X.term i).S.base.metric s).inner x v v :=
          mul_le_mul_of_nonneg_right hscal' hv
      _ = ((Module.finrank ℝ ThreeSpace : ℝ) - 1) * (C / 2) *
            ((X.term i).S.base.metric s).inner x v v := by rw [hdim]
  exact hchain

theorem terminalDerivativeBoundProducer_of_uniformScalarBounded_and_ricciNonnegative
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} {C epsStar : ℝ}
    (hC : 0 < C) (hepsStar : 0 < epsStar)
    (hscal : ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        ∀ i : ℕ, PointedFlowScalarBounded (X.term i) C)
    (hric : ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ i : ℕ,
        ∀ t ∈ (X.interval i).carrier, ∀ x : (X.term i).M,
          ∀ v : TangentSpace I3 x, 0 ≤ (X.term i).S.ricciAt t x (vec2 v v)) :
    TerminalDerivativeBoundProducer.{u} kappa sigma Phi :=
  terminalDerivativeBoundProducer_of_uniformRmNormSqBoundProducer_and_ricciTensorBoundProducer
    ⟨epsStar, hepsStar, fun eps hp hle X =>
      uniformRmNormSqBound_of_uniformScalarBound_and_ricciNonnegative X
        (hscal eps hp hle X) (hric eps hp hle X)⟩
    (ricciTensorBoundProducer_of_uniformScalarBound_and_ricciNonnegative hC hepsStar
      (fun eps hp hle X i s hs x =>
        (hscal eps hp hle X i s ((normalizedSequence_modelDepth_window X hp i).1 hs) x).2)
      (fun eps hp hle X i s hs x v =>
        hric eps hp hle X i s ((normalizedSequence_modelDepth_window X hp i).1 hs) x v))

abbrev UniformScalarRicciNonnegativeProducer.{v} (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∃ C : ℝ, 0 < C ∧
    (∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{v} eps kappa sigma Phi,
        ∀ i : ℕ, PointedFlowScalarBounded (X.term i) C) ∧
    (∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{v} eps kappa sigma Phi, ∀ i : ℕ,
        ∀ t ∈ (X.interval i).carrier, ∀ x : (X.term i).M,
          ∀ v : TangentSpace I3 x, 0 ≤ (X.term i).S.ricciAt t x (vec2 v v))

theorem terminalDerivativeBoundProducer_of_uniformScalarRicciNonnegativeProducer
    {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : UniformScalarRicciNonnegativeProducer.{u} kappa sigma Phi) :
    TerminalDerivativeBoundProducer.{u} kappa sigma Phi := by
  obtain ⟨epsStar, hepsStar, C, hC, hscal, hric⟩ := h
  exact terminalDerivativeBoundProducer_of_uniformScalarBounded_and_ricciNonnegative
    hC hepsStar hscal hric

theorem uniformScalarRicciNonnegativeProducer_of_curvatureOperatorNonnegative
    {kappa sigma : ℝ} {Phi : ℝ → ℝ} {C epsStar : ℝ} (hC : 0 < C) (hepsStar : 0 < epsStar)
    (hscal : ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        ∀ i : ℕ, PointedFlowScalarBounded (X.term i) C)
    (hcone : ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ∀ i : ℕ,
        ∀ t ∈ (X.interval i).carrier, ∀ x : (X.term i).M,
          metricAlgebraicCurvatureTensorAt (I := I3) (M := (X.term i).M)
            ((X.term i).S.base.metric t) x ∈
              algebraicCurvatureOperatorNonnegativeCone (I := I3) (M := (X.term i).M)) :
    UniformScalarRicciNonnegativeProducer.{u} kappa sigma Phi :=
  ⟨epsStar, hepsStar, C, hC, hscal, fun eps hp hle X i t ht x v =>
    metricRicciAt_nonnegative_of_curvatureOperator_nonnegative (I := I3)
      ((X.term i).S.base.metric t) x (hcone eps hp hle X i t ht x) v⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
