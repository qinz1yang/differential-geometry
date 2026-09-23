import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.CanonicalStrictBounds

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

variable {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval}


structure BufferedCanonical (S : SolutionOn (I := I3) (M := M) D)
    (alpha C H : ℝ) (x : M) (t : ℝ) where
  tolerance : ℝ
  tolerance_pos : 0 < tolerance
  tolerance_lt : tolerance < alpha
  witness : CanonicalWitness S tolerance C C x t
  a : ℝ
  b : ℝ
  margin : ℝ
  a_pos : 0 < a
  margin_pos : 0 < margin
  radial_margin : b ≤ (2 - margin) * a
  inner_ball : riemannianBallOf (I := I3) (S.base.metric t) x a ⊆ witness.domain.carrier
  outer_ball : witness.domain.carrier ⊆ riemannianBallOf (I := I3) (S.base.metric t) x b
  scalar_reserve : ∀ y ∈ witness.domain.carrier,
    C⁻¹ * S.scalar t x < S.scalar t y ∧ S.scalar t y < C * S.scalar t x
  rm_reserve : ∀ y ∈ witness.domain.carrier,
    Real.sqrt (FlowMetricBall.rmNormSq S t y) < C * S.scalar t x
  volume_reserve : witness.alternative.requiresVolume →
    ENNReal.ofReal (C⁻¹ / (S.scalar t x * Real.sqrt (S.scalar t x))) <
      riemannianVolumeMeasure I3 M (S.base.metric t) witness.domain.carrier
  cap_collar : ∀ cap : LocalCap S tolerance x t witness.domain.carrier,
    (∃ hdepth : ∀ y ∈ cap.tube,
        10000 / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x y,
      witness.alternative = CanonicalAlternative.cap cap hdepth) →
    ∃ (v : M) (neck : StrongNeck S alpha v t),
      v ∈ cap.tube ∧ C⁻¹ * S.scalar t x ≤ S.scalar t v ∧ S.scalar t v ≤ C * S.scalar t x ∧
      (∀ z ∈ neck.map '' (Set.univ ×ˢ ({0} : Set ℝ)),
        H / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x z) ∧
      (∀ y ∈ neck.map '' (Set.univ ×ˢ ({0} : Set ℝ)),
        ∀ z ∈ neck.map '' (Set.univ ×ˢ ({0} : Set ℝ)),
          metricDistance (S.base.metric t) y z ≤ C / Real.sqrt (S.scalar t x))

theorem CanonicalWitness.exists_bufferedCanonical_with_witness
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
    {x : M} {t : ℝ} {tolerance C1 C2 alpha H : ℝ}
    (W : CanonicalWitness S tolerance C1 C2 x t) (htol : tolerance < alpha)
    (hcap : ∀ cap : LocalCap S tolerance x t W.domain.carrier,
      (∃ hdepth : ∀ y ∈ cap.tube,
          10000 / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x y,
        W.alternative = CanonicalAlternative.cap cap hdepth) →
      ∃ (v : M) (neck : StrongNeck S alpha v t),
        v ∈ cap.tube ∧
        (max C1 C2 + 1)⁻¹ * S.scalar t x ≤ S.scalar t v ∧
        S.scalar t v ≤ (max C1 C2 + 1) * S.scalar t x ∧
        (∀ z ∈ neck.map '' (Set.univ ×ˢ ({0} : Set ℝ)),
          H / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x z) ∧
        (∀ y ∈ neck.map '' (Set.univ ×ˢ ({0} : Set ℝ)),
          ∀ z ∈ neck.map '' (Set.univ ×ˢ ({0} : Set ℝ)),
            metricDistance (S.base.metric t) y z ≤
              (max C1 C2 + 1) / Real.sqrt (S.scalar t x))) :
    ∃ B : BufferedCanonical S alpha (max C1 C2 + 1) H x t,
      B.tolerance = tolerance ∧ HEq B.witness
        (W.enlarge_constants
          (show C1 ≤ max C1 C2 + 1 by linarith [le_max_left C1 C2])
          (show C2 ≤ max C1 C2 + 1 by linarith [le_max_right C1 C2])) := by
  obtain ⟨hC, hC1, hC2, hscalar, hrm, hvolume⟩ := W.strict_curvature_volume_reserves
  let W' : CanonicalWitness S tolerance (max C1 C2 + 1) (max C1 C2 + 1) x t :=
    W.enlarge_constants hC1.le hC2.le
  obtain ⟨a, b, margin, ha, har, hm, hbm, hinner, houter⟩ := W'.exists_radial_reserve
  refine ⟨{ tolerance := tolerance
            tolerance_pos := W.eps_pos
            tolerance_lt := htol
            witness := W'
            a := a
            b := b
            margin := margin
            a_pos := ha
            margin_pos := hm
            radial_margin := hbm.le
            inner_ball := hinner
            outer_ball := houter
            scalar_reserve := hscalar
            rm_reserve := hrm
            volume_reserve := fun hv => hvolume (by
              simpa only [W', CanonicalWitness.enlarge_constants_requiresVolume] using hv)
            cap_collar := fun cap hc => ?_ }, rfl, HEq.rfl⟩
  obtain ⟨hdepth, halteq⟩ := hc
  simp only [W', CanonicalWitness.enlarge_constants] at halteq
  have halteq' : W.alternative = CanonicalAlternative.cap cap hdepth := by
    cases hW : W.alternative with
    | neck data =>
        rw [hW] at halteq
        simp only [CanonicalAlternative.mono_constant] at halteq
        exact absurd halteq (by simp)
    | cap data deep =>
        rw [hW] at halteq
        simp only [CanonicalAlternative.mono_constant] at halteq
        cases halteq
        rfl
    | positive whole data hsec =>
        rw [hW] at halteq
        simp only [CanonicalAlternative.mono_constant] at halteq
        exact absurd halteq (by simp)
    | round whole data =>
        rw [hW] at halteq
        simp only [CanonicalAlternative.mono_constant] at halteq
        exact absurd halteq (by simp)
  exact hcap cap ⟨hdepth, halteq'⟩


theorem CanonicalWitness.exists_bufferedCanonical
    {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
    {x : M} {t : ℝ} {tolerance C1 C2 alpha H : ℝ}
    (W : CanonicalWitness S tolerance C1 C2 x t) (htol : tolerance < alpha)
    (hcap : ∀ cap : LocalCap S tolerance x t W.domain.carrier,
      (∃ hdepth : ∀ y ∈ cap.tube,
          10000 / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x y,
        W.alternative = CanonicalAlternative.cap cap hdepth) →
      ∃ (v : M) (neck : StrongNeck S alpha v t),
        v ∈ cap.tube ∧
        (max C1 C2 + 1)⁻¹ * S.scalar t x ≤ S.scalar t v ∧
        S.scalar t v ≤ (max C1 C2 + 1) * S.scalar t x ∧
        (∀ z ∈ neck.map '' (Set.univ ×ˢ ({0} : Set ℝ)),
          H / Real.sqrt (S.scalar t x) ≤ metricDistance (S.base.metric t) x z) ∧
        (∀ y ∈ neck.map '' (Set.univ ×ˢ ({0} : Set ℝ)),
          ∀ z ∈ neck.map '' (Set.univ ×ˢ ({0} : Set ℝ)),
            metricDistance (S.base.metric t) y z ≤
              (max C1 C2 + 1) / Real.sqrt (S.scalar t x))) :
    Nonempty (BufferedCanonical S alpha (max C1 C2 + 1) H x t) := by
  obtain ⟨B, _, _⟩ := W.exists_bufferedCanonical_with_witness htol hcap
  exact ⟨B⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

noncomputable section

open Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

variable {M : Type*} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
  [IsManifold I3 ∞ M] [T2Space M] [SigmaCompactSpace M]
  {D : RealTimeInterval} {S : SolutionOn (I := I3) (M := M) D}
  {eps A C alpha H : ℝ} {p : M} {t : ℝ}

theorem CanonicalWitness.exists_bufferedCanonical_of_neck
    (K : CanonicalWitness S eps A C p t) (heps : eps < alpha)
    (nk : LocalNeck S eps p t K.domain.carrier) (hneck : K.alternative = CanonicalAlternative.neck nk) :
    ∃ B : BufferedCanonical S alpha (max A C + 1) H p t,
      B.tolerance = eps ∧ B.witness.domain = K.domain ∧ B.witness.radius = K.radius ∧
      ∃ nk' : LocalNeck S B.tolerance p t B.witness.domain.carrier,
        B.witness.alternative = CanonicalAlternative.neck nk' ∧ HEq nk' nk := by
  obtain ⟨_hC, hA, hC', hscalar, hrm, hvolume⟩ := K.strict_curvature_volume_reserves
  let K' := K.enlarge_constants hA.le hC'.le
  have halt : K'.alternative = CanonicalAlternative.neck nk := by
    change K.alternative.mono_constant (zero_lt_one.trans_le K.one_le_comparison_constant) hC'.le K.Q_pos.le = _
    rw [hneck]
    rfl
  obtain ⟨a, b, margin, ha, _har, hm, hab, hinner, houter⟩ := K'.exists_radial_reserve
  let B : BufferedCanonical S alpha (max A C + 1) H p t := {
    tolerance := eps
    tolerance_pos := K.eps_pos
    tolerance_lt := heps
    witness := K'
    a := a
    b := b
    margin := margin
    a_pos := ha
    margin_pos := hm
    radial_margin := hab.le
    inner_ball := hinner
    outer_ball := houter
    scalar_reserve := hscalar
    rm_reserve := hrm
    volume_reserve := fun hv => hvolume (by
      simpa only [K', CanonicalWitness.enlarge_constants_requiresVolume] using hv)
    cap_collar := by
      intro cap hc
      obtain ⟨depth, heq⟩ := hc
      rw [halt] at heq
      cases heq }
  exact ⟨B, rfl, rfl, rfl, nk, halt, HEq.rfl⟩

theorem CanonicalWitness.exists_bufferedCanonical_of_positive
    (K : CanonicalWitness S eps A C p t) (heps : eps < alpha)
    (hpositive : ∃ whole data sec,
      K.alternative = CanonicalAlternative.positive whole data sec) :
    ∃ B : BufferedCanonical S alpha (max A C + 1) H p t,
      B.tolerance = eps ∧ B.witness.domain = K.domain ∧ B.witness.radius = K.radius ∧
      ∃ whole data sec,
        B.witness.alternative = CanonicalAlternative.positive whole data sec := by
  obtain ⟨_hC, hA, hC', hscalar, hrm, hvolume⟩ := K.strict_curvature_volume_reserves
  let K' := K.enlarge_constants hA.le hC'.le
  obtain ⟨whole, data, sec, hpositive⟩ := hpositive
  have hpositive' : ∃ whole data sec,
      K'.alternative = CanonicalAlternative.positive whole data sec := by
    dsimp only [K', CanonicalWitness.enlarge_constants]
    rw [hpositive]
    exact ⟨whole, data, _, rfl⟩
  obtain ⟨whole', data', sec', halt⟩ := hpositive'
  obtain ⟨a, b, margin, ha, _har, hm, hab, hinner, houter⟩ := K'.exists_radial_reserve
  let B : BufferedCanonical S alpha (max A C + 1) H p t := {
    tolerance := eps
    tolerance_pos := K.eps_pos
    tolerance_lt := heps
    witness := K'
    a := a
    b := b
    margin := margin
    a_pos := ha
    margin_pos := hm
    radial_margin := hab.le
    inner_ball := hinner
    outer_ball := houter
    scalar_reserve := hscalar
    rm_reserve := hrm
    volume_reserve := fun hv => hvolume (by
      simpa only [K', CanonicalWitness.enlarge_constants_requiresVolume] using hv)
    cap_collar := by
      intro cap hc
      obtain ⟨depth, heq⟩ := hc
      rw [halt] at heq
      cases heq }
  exact ⟨B, rfl, rfl, rfl, whole', data', sec', halt⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

end
