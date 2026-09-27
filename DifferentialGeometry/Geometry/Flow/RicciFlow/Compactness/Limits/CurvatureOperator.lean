import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperator.LeastEigenvalue
import DifferentialGeometry.Geometry.Curvature.DimensionThree.RicciReaction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Foundations.PointedMaps

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle Filter
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Curvature.DimensionThree
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [FiniteDimensional Real E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

def RmPullbackTendsto
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat → Nat}
    (Φ : PointedCGHMaps (I := I) X (L.atTime 0) subseq) : Prop :=
  letI : TopologicalSpace L.M := L.topology
  letI : ChartedSpace H L.M := L.charted
  letI : IsManifold I ∞ L.M := L.smooth
  letI : TopologicalSpace (L.atTime 0).M := L.topology
  letI : ChartedSpace H (L.atTime 0).M := L.charted
  letI : IsManifold I ∞ (L.atTime 0).M := L.smooth
  ∀ t ∈ X.D.carrier, ∀ x : L.M, ∀ U V W Z : TangentSpace I x,
    Tendsto
      (fun k =>
        letI : TopologicalSpace (X.term (subseq k)).M :=
          (X.term (subseq k)).topology
        letI : ChartedSpace H (X.term (subseq k)).M :=
          (X.term (subseq k)).charted
        letI : IsManifold I ∞ (X.term (subseq k)).M :=
          (X.term (subseq k)).smooth
        metricRm04StandardAt (I := I) ((X.term (subseq k)).S.family.metric t)
          (Φ.map k x)
          (mfderiv I I (Φ.map k) x U)
          (mfderiv I I (Φ.map k) x V)
          (mfderiv I I (Φ.map k) x W)
          (mfderiv I I (Φ.map k) x Z))
      atTop
      (nhds (metricRm04StandardAt (I := I) (L.S.family.metric t) x U V W Z))

namespace SmoothCGHConverges

theorem rm_converges
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat → Nat}
    (h : SmoothCGHConverges (I := I) X L subseq)
    (hdim : Module.finrank Real E = 3) :
    RmPullbackTendsto (I := I) h.spatial.maps := by
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : IsManifold I ∞ L.M := L.smooth
  let : TopologicalSpace (L.atTime 0).M := L.topology
  let : ChartedSpace H (L.atTime 0).M := L.charted
  let : IsManifold I ∞ (L.atTime 0).M := L.smooth
  intro t ht x U V W Z
  let : IsManifold I 1 L.M :=
    IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
  let : IsManifold I 2 L.M :=
    IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
  let : IsManifold I 3 L.M :=
    IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
  let : SigmaCompactSpace L.M := L.sigmaCompact
  let : T2Space L.M := L.t2
  have hmetricUW := h.metric_converges t ht x U W
  have hmetricVZ := h.metric_converges t ht x V Z
  have hmetricVW := h.metric_converges t ht x V W
  have hmetricUZ := h.metric_converges t ht x U Z
  have hricciUW := h.ricci_converges t ht x U W
  have hricciVW := h.ricci_converges t ht x V W
  have hricciUZ := h.ricci_converges t ht x U Z
  have hricciVZ := h.ricci_converges t ht x V Z
  have hscalar := h.scalar_converges t ht x
  have hformula :=
    (((hricciUW.neg.mul hmetricVZ).add (hricciVW.mul hmetricUZ)).add
        (hricciUZ.mul hmetricVW)).sub (hricciVZ.mul hmetricUW) |>.add
      ((hscalar.div_const 2).mul
        ((hmetricUW.mul hmetricVZ).sub (hmetricVW.mul hmetricUZ)))
  convert hformula using 1
  · funext k
    let : TopologicalSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).topology
    let : ChartedSpace H (X.term (subseq k)).M :=
      (X.term (subseq k)).charted
    let : IsManifold I ∞ (X.term (subseq k)).M :=
      (X.term (subseq k)).smooth
    let : IsManifold I 1 (X.term (subseq k)).M :=
      IsManifold.of_le (I := I) (M := (X.term (subseq k)).M) (n := ∞) (by decide)
    let : IsManifold I 2 (X.term (subseq k)).M :=
      IsManifold.of_le (I := I) (M := (X.term (subseq k)).M) (n := ∞) (by decide)
    let : IsManifold I 3 (X.term (subseq k)).M :=
      IsManifold.of_le (I := I) (M := (X.term (subseq k)).M) (n := ∞) (by decide)
    let : SigmaCompactSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).sigmaCompact
    let : T2Space (X.term (subseq k)).M :=
      (X.term (subseq k)).t2
    rw [metricRm04StdAt_eq_ricci3 (I := I)
      ((X.term (subseq k)).S.family.metric t) (h.spatial.maps.map k x)
      (by change Module.finrank Real E = 3; exact hdim)]
    simp [DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar,
      DifferentialGeometry.PDE.RicciFlow.SolutionFamily.scalar]
    rfl
  · rw [metricRm04StdAt_eq_ricci3 (I := I) (L.S.family.metric t) x
      (by change Module.finrank Real E = 3; exact hdim)]
    simp [DifferentialGeometry.PDE.RicciFlow.SolutionOn.scalar,
      DifferentialGeometry.PDE.RicciFlow.SolutionFamily.scalar]
    rfl

theorem algebraicCurvatureIdentityQuadraticEval_converges
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat → Nat}
    (h : SmoothCGHConverges (I := I) X L subseq) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : IsManifold I ∞ L.M := L.smooth
    letI : TopologicalSpace (L.atTime 0).M := L.topology
    letI : ChartedSpace H (L.atTime 0).M := L.charted
    letI : IsManifold I ∞ (L.atTime 0).M := L.smooth
    ∀ t ∈ X.D.carrier, ∀ (x : L.M) {n : Nat} (c : Fin n → Real)
      (v w : Fin n → TangentSpace I x),
    Tendsto
      (fun k =>
        letI : TopologicalSpace (X.term (subseq k)).M :=
          (X.term (subseq k)).topology
        letI : ChartedSpace H (X.term (subseq k)).M :=
          (X.term (subseq k)).charted
        letI : IsManifold I ∞ (X.term (subseq k)).M :=
          (X.term (subseq k)).smooth
        algebraicCurvatureIdentityQuadraticEval (I := I)
          ((X.term (subseq k)).S.family.metric t) c
          (fun i => mfderiv I I (h.spatial.maps.map k) x (v i))
          (fun i => mfderiv I I (h.spatial.maps.map k) x (w i)))
      atTop
      (nhds (algebraicCurvatureIdentityQuadraticEval (I := I)
        (L.S.family.metric t) c v w)) := by
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : IsManifold I ∞ L.M := L.smooth
  let : TopologicalSpace (L.atTime 0).M := L.topology
  let : ChartedSpace H (L.atTime 0).M := L.charted
  let : IsManifold I ∞ (L.atTime 0).M := L.smooth
  intro t ht x n c v w
  unfold algebraicCurvatureIdentityQuadraticEval
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  exact (tendsto_const_nhds.mul tendsto_const_nhds).mul
    (((h.metric_converges t ht x (v i) (v j)).mul
        (h.metric_converges t ht x (w i) (w j))).sub
      ((h.metric_converges t ht x (v i) (w j)).mul
        (h.metric_converges t ht x (w i) (v j))))

theorem algebraicCurvatureOperatorQuadraticEval_converges
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat → Nat}
    (h : SmoothCGHConverges (I := I) X L subseq)
    (hdim : Module.finrank Real E = 3) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : IsManifold I ∞ L.M := L.smooth
    letI : IsManifold I 1 L.M :=
      IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
    letI : IsManifold I 2 L.M :=
      IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
    letI : IsManifold I 3 L.M :=
      IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace L.M := L.sigmaCompact
    letI : T2Space L.M := L.t2
    letI : TopologicalSpace (L.atTime 0).M := L.topology
    letI : ChartedSpace H (L.atTime 0).M := L.charted
    letI : IsManifold I ∞ (L.atTime 0).M := L.smooth
    ∀ t ∈ X.D.carrier, ∀ (x : L.M) {n : Nat} (c : Fin n → Real)
      (v w : Fin n → TangentSpace I x),
    Tendsto
      (fun k =>
        letI : TopologicalSpace (X.term (subseq k)).M :=
          (X.term (subseq k)).topology
        letI : ChartedSpace H (X.term (subseq k)).M :=
          (X.term (subseq k)).charted
        letI : IsManifold I ∞ (X.term (subseq k)).M :=
          (X.term (subseq k)).smooth
        letI : IsManifold I 1 (X.term (subseq k)).M :=
          IsManifold.of_le (I := I) (M := (X.term (subseq k)).M) (n := ∞) (by decide)
        letI : IsManifold I 2 (X.term (subseq k)).M :=
          IsManifold.of_le (I := I) (M := (X.term (subseq k)).M) (n := ∞) (by decide)
        letI : IsManifold I 3 (X.term (subseq k)).M :=
          IsManifold.of_le (I := I) (M := (X.term (subseq k)).M) (n := ∞) (by decide)
        letI : SigmaCompactSpace (X.term (subseq k)).M :=
          (X.term (subseq k)).sigmaCompact
        letI : T2Space (X.term (subseq k)).M :=
          (X.term (subseq k)).t2
        algebraicCurvatureOperatorQuadraticEval (I := I)
          (metricAlgebraicCurvatureTensorAt (I := I)
            ((X.term (subseq k)).S.family.metric t) (h.spatial.maps.map k x)) c
          (fun i => mfderiv I I (h.spatial.maps.map k) x (v i))
          (fun i => mfderiv I I (h.spatial.maps.map k) x (w i)))
      atTop
      (nhds (algebraicCurvatureOperatorQuadraticEval (I := I)
        (metricAlgebraicCurvatureTensorAt (I := I) (L.S.family.metric t) x) c v w)) := by
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : IsManifold I ∞ L.M := L.smooth
  let : IsManifold I 1 L.M :=
    IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
  let : IsManifold I 2 L.M :=
    IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
  let : IsManifold I 3 L.M :=
    IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
  let : SigmaCompactSpace L.M := L.sigmaCompact
  let : T2Space L.M := L.t2
  let : TopologicalSpace (L.atTime 0).M := L.topology
  let : ChartedSpace H (L.atTime 0).M := L.charted
  let : IsManifold I ∞ (L.atTime 0).M := L.smooth
  intro t ht x n c v w
  unfold algebraicCurvatureOperatorQuadraticEval
  apply tendsto_finsetSum
  intro i _
  apply tendsto_finsetSum
  intro j _
  exact (tendsto_const_nhds.mul tendsto_const_nhds).mul
    (h.rm_converges hdim t ht x (v i) (w i) (w j) (v j))

theorem leastCurvatureOperatorEigenvalueAt_eventually_lt_add
    {X : PointedFlowSeq (I := I)}
    {L : PointedFlowData (I := I) X.D}
    {subseq : Nat → Nat}
    (h : SmoothCGHConverges (I := I) X L subseq)
    (hdim : Module.finrank Real E = 3) :
    letI : TopologicalSpace L.M := L.topology
    letI : ChartedSpace H L.M := L.charted
    letI : IsManifold I ∞ L.M := L.smooth
    letI : IsManifold I 1 L.M :=
      IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
    letI : IsManifold I 2 L.M :=
      IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
    letI : IsManifold I 3 L.M :=
      IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
    letI : SigmaCompactSpace L.M := L.sigmaCompact
    letI : T2Space L.M := L.t2
    letI : TopologicalSpace (L.atTime 0).M := L.topology
    letI : ChartedSpace H (L.atTime 0).M := L.charted
    letI : IsManifold I ∞ (L.atTime 0).M := L.smooth
    ∀ t ∈ X.D.carrier, ∀ (x : L.M) (ε : Real), 0 < ε →
      ∀ᶠ k in atTop,
        letI : TopologicalSpace (X.term (subseq k)).M :=
          (X.term (subseq k)).topology
        letI : ChartedSpace H (X.term (subseq k)).M :=
          (X.term (subseq k)).charted
        letI : IsManifold I ∞ (X.term (subseq k)).M :=
          (X.term (subseq k)).smooth
        letI : IsManifold I 1 (X.term (subseq k)).M :=
          IsManifold.of_le (I := I) (M := (X.term (subseq k)).M) (n := ∞) (by decide)
        letI : IsManifold I 2 (X.term (subseq k)).M :=
          IsManifold.of_le (I := I) (M := (X.term (subseq k)).M) (n := ∞) (by decide)
        letI : IsManifold I 3 (X.term (subseq k)).M :=
          IsManifold.of_le (I := I) (M := (X.term (subseq k)).M) (n := ∞) (by decide)
        letI : SigmaCompactSpace (X.term (subseq k)).M :=
          (X.term (subseq k)).sigmaCompact
        letI : T2Space (X.term (subseq k)).M :=
          (X.term (subseq k)).t2
        leastCurvatureOperatorEigenvalueAt (I := I)
            ((X.term (subseq k)).S.family.metric t) (h.spatial.maps.map k x)
            (metricAlgebraicCurvatureTensorAt (I := I)
              ((X.term (subseq k)).S.family.metric t) (h.spatial.maps.map k x)) <
          leastCurvatureOperatorEigenvalueAt (I := I) (L.S.family.metric t) x
            (metricAlgebraicCurvatureTensorAt (I := I) (L.S.family.metric t) x) + ε := by
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : IsManifold I ∞ L.M := L.smooth
  let : IsManifold I 1 L.M :=
    IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
  let : IsManifold I 2 L.M :=
    IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
  let : IsManifold I 3 L.M :=
    IsManifold.of_le (I := I) (M := L.M) (n := ∞) (by decide)
  let : SigmaCompactSpace L.M := L.sigmaCompact
  let : T2Space L.M := L.t2
  let : TopologicalSpace (L.atTime 0).M := L.topology
  let : ChartedSpace H (L.atTime 0).M := L.charted
  let : IsManifold I ∞ (L.atTime 0).M := L.smooth
  intro t ht x ε hε
  let g := L.S.family.metric t
  let A := metricAlgebraicCurvatureTensorAt (I := I) g x
  obtain ⟨basis, horth⟩ := exists_orthonormalBasisAt (I := I) g x
    (by change Module.finrank Real E = 3; exact hdim)
  obtain ⟨c, hidentity, hoperator⟩ :=
    exists_leastCurvatureOperatorEigenvalueAt_rayleigh_minimizer
      (I := I) g x basis horth A
  let v : Fin 3 → TangentSpace I x := fun i => basis (bivectorIndex3 i).1
  let w : Fin 3 → TangentSpace I x := fun i => basis (bivectorIndex3 i).2
  have hidentity' : algebraicCurvatureIdentityQuadraticEval (I := I) g c v w = 1 := by
    simpa [v, w] using hidentity
  have hoperator' : algebraicCurvatureOperatorQuadraticEval (I := I) A c v w =
      leastCurvatureOperatorEigenvalueAt (I := I) g x A := by
    simpa [v, w] using hoperator
  let identitySeq : Nat → Real := fun k =>
    letI : TopologicalSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).topology
    letI : ChartedSpace H (X.term (subseq k)).M :=
      (X.term (subseq k)).charted
    letI : IsManifold I ∞ (X.term (subseq k)).M :=
      (X.term (subseq k)).smooth
    algebraicCurvatureIdentityQuadraticEval (I := I)
      ((X.term (subseq k)).S.family.metric t) c
      (fun i => mfderiv I I (h.spatial.maps.map k) x (v i))
      (fun i => mfderiv I I (h.spatial.maps.map k) x (w i))
  let operatorSeq : Nat → Real := fun k =>
    letI : TopologicalSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).topology
    letI : ChartedSpace H (X.term (subseq k)).M :=
      (X.term (subseq k)).charted
    letI : IsManifold I ∞ (X.term (subseq k)).M :=
      (X.term (subseq k)).smooth
    letI : IsManifold I 1 (X.term (subseq k)).M :=
      IsManifold.of_le (I := I) (M := (X.term (subseq k)).M) (n := ∞) (by decide)
    letI : IsManifold I 2 (X.term (subseq k)).M :=
      IsManifold.of_le (I := I) (M := (X.term (subseq k)).M) (n := ∞) (by decide)
    letI : IsManifold I 3 (X.term (subseq k)).M :=
      IsManifold.of_le (I := I) (M := (X.term (subseq k)).M) (n := ∞) (by decide)
    letI : SigmaCompactSpace (X.term (subseq k)).M :=
      (X.term (subseq k)).sigmaCompact
    letI : T2Space (X.term (subseq k)).M :=
      (X.term (subseq k)).t2
    algebraicCurvatureOperatorQuadraticEval (I := I)
      (metricAlgebraicCurvatureTensorAt (I := I)
        ((X.term (subseq k)).S.family.metric t) (h.spatial.maps.map k x)) c
      (fun i => mfderiv I I (h.spatial.maps.map k) x (v i))
      (fun i => mfderiv I I (h.spatial.maps.map k) x (w i))
  have hidentityTendsto : Tendsto identitySeq atTop
      (nhds (algebraicCurvatureIdentityQuadraticEval (I := I) g c v w)) := by
    exact h.algebraicCurvatureIdentityQuadraticEval_converges t ht x c v w
  have hoperatorTendsto : Tendsto operatorSeq atTop
      (nhds (algebraicCurvatureOperatorQuadraticEval (I := I) A c v w)) := by
    exact h.algebraicCurvatureOperatorQuadraticEval_converges hdim t ht x c v w
  have hquotientTendsto : Tendsto (fun k => operatorSeq k / identitySeq k) atTop
      (nhds (leastCurvatureOperatorEigenvalueAt (I := I) g x A)) := by
    have hquotient := hoperatorTendsto.div hidentityTendsto (by
      rw [hidentity']
      norm_num)
    rw [hidentity', hoperator', div_one] at hquotient
    exact hquotient
  have hidentityPositive : ∀ᶠ k in atTop, 0 < identitySeq k :=
    hidentityTendsto (Ioi_mem_nhds (by rw [hidentity']; norm_num))
  have hquotientLt : ∀ᶠ k in atTop,
      operatorSeq k / identitySeq k <
        leastCurvatureOperatorEigenvalueAt (I := I) g x A + ε :=
    hquotientTendsto (Iio_mem_nhds (lt_add_of_pos_right _ hε))
  filter_upwards [hidentityPositive, hquotientLt] with k hkIdentity hkQuotient
  let : TopologicalSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).topology
  let : ChartedSpace H (X.term (subseq k)).M :=
    (X.term (subseq k)).charted
  let : IsManifold I ∞ (X.term (subseq k)).M :=
    (X.term (subseq k)).smooth
  let : IsManifold I 1 (X.term (subseq k)).M :=
    IsManifold.of_le (I := I) (M := (X.term (subseq k)).M) (n := ∞) (by decide)
  let : IsManifold I 2 (X.term (subseq k)).M :=
    IsManifold.of_le (I := I) (M := (X.term (subseq k)).M) (n := ∞) (by decide)
  let : IsManifold I 3 (X.term (subseq k)).M :=
    IsManifold.of_le (I := I) (M := (X.term (subseq k)).M) (n := ∞) (by decide)
  let : SigmaCompactSpace (X.term (subseq k)).M :=
    (X.term (subseq k)).sigmaCompact
  let : T2Space (X.term (subseq k)).M :=
    (X.term (subseq k)).t2
  let gk := (X.term (subseq k)).S.family.metric t
  let xk := h.spatial.maps.map k x
  let Ak := metricAlgebraicCurvatureTensorAt (I := I) gk xk
  let vk : Fin 3 → TangentSpace I xk :=
    fun i => mfderiv I I (h.spatial.maps.map k) x (v i)
  let wk : Fin 3 → TangentSpace I xk :=
    fun i => mfderiv I I (h.spatial.maps.map k) x (w i)
  change 0 < algebraicCurvatureIdentityQuadraticEval (I := I) gk c vk wk at hkIdentity
  change algebraicCurvatureOperatorQuadraticEval (I := I) Ak c vk wk /
      algebraicCurvatureIdentityQuadraticEval (I := I) gk c vk wk <
    leastCurvatureOperatorEigenvalueAt (I := I) g x A + ε at hkQuotient
  obtain ⟨basisk, horthk⟩ := exists_orthonormalBasisAt (I := I) gk xk
    (by change Module.finrank Real E = 3; exact hdim)
  have hrayleigh := leastCurvatureOperatorEigenvalueAt_mul_identity_le
    (I := I) gk xk basisk horthk Ak c vk wk
  have hleastLe : leastCurvatureOperatorEigenvalueAt (I := I) gk xk Ak ≤
      algebraicCurvatureOperatorQuadraticEval (I := I) Ak c vk wk /
        algebraicCurvatureIdentityQuadraticEval (I := I) gk c vk wk :=
    (le_div_iff₀ hkIdentity).2 hrayleigh
  exact hleastLe.trans_lt hkQuotient

end SmoothCGHConverges

end DifferentialGeometry.CheegerGromovCompactness
