import DifferentialGeometry.Geometry.Curvature.Metric.ConstantSectional
import DifferentialGeometry.Geometry.Curvature.Sphere.ConstCurvature
import DifferentialGeometry.Geometry.Metric.Pullback.Basic
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHornGeometry
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Contract.PoincareStandardControl
import DifferentialGeometry.Topology.ThreeManifold.PoincareStandardDiscardedModels

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn (RoundComponent)

universe u v

private instance roundSphereFourFact :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) :=
  ⟨by norm_num [finrank_euclideanSpace_fin]⟩

theorem constantPositiveSectionalCurvatureMetric_roundMetric_sphereThree :
    constantPositiveSectionalCurvatureMetric
      (M := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
      (roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3)) := by
  apply (constantPositiveSectionalCurvatureMetric_iff _).2
  refine ⟨1, one_pos, fun x v w hLI => ?_⟩
  have hden : 0 < (roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3)).inner x v v *
      (roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3)).inner x w w -
      ((roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3)).inner x v w) ^ 2 := by
    simpa only [DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_def]
      using Riemannian.sectionalCurvatureDenominator_pos_of_linearIndependent
        (I := ThreeModel) (M := Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)
        (roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3)) x v w hLI
  rw [DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_eq_metricRm04StandardAt_div,
    DifferentialGeometry.Geometry.roundMetric_sec_value]
  field_simp [ne_of_gt hden]

theorem constantPositiveSectionalCurvatureMetric_pullback
    {M : Type u} [TopologicalSpace M] [ChartedSpace ThreeSpace M]
    [IsManifold ThreeModel ∞ M] [T2Space M]
    {N : Type v} [TopologicalSpace N] [ChartedSpace ThreeSpace N] [IsManifold ThreeModel ∞ N]
    [T2Space N]
    (g : SmoothRiemannianMetric ThreeModel N)
    (hg : constantPositiveSectionalCurvatureMetric g)
    (Φ : Diffeomorph ThreeModel ThreeModel M N ∞) :
    constantPositiveSectionalCurvatureMetric (Diffeomorph.pullbackMetric g Φ) := by
  obtain ⟨κ, hκ, hsec⟩ := (constantPositiveSectionalCurvatureMetric_iff g).1 hg
  apply (constantPositiveSectionalCurvatureMetric_iff _).2
  refine ⟨κ, hκ, fun x v w hLI => ?_⟩
  rw [DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_pullback
    (I := ThreeModel) (g := g) (Φ := Φ) (x := x) (v := v) (w := w)]
  refine hsec (Φ x) _ _ ?_
  let e := Φ.mfderivToContinuousLinearEquiv (by decide : (∞ : WithTop ℕ∞) ≠ 0) x
  have hcle : (e : TangentSpace ThreeModel x →L[ℝ] TangentSpace ThreeModel (Φ x)) =
      mfderiv ThreeModel ThreeModel (Φ : M → N) x :=
    Diffeomorph.mfderivToContinuousLinearEquiv_coe (Φ := Φ) _
  have hA : LinearIndependent ℝ ![e v, e w] := by
    have h := hLI.map' e.toLinearMap (by
      rw [LinearMap.ker_eq_bot]
      exact e.injective)
    have hfun : (fun i : Fin 2 =>
        (e : TangentSpace ThreeModel x → TangentSpace ThreeModel (Φ x)) (![v, w] i)) =
        ![e v, e w] := by
      funext i
      fin_cases i <;> rfl
    have h' : LinearIndependent ℝ (fun i : Fin 2 =>
        (e : TangentSpace ThreeModel x → TangentSpace ThreeModel (Φ x)) (![v, w] i)) := h
    rwa [hfun] at h'
  have hv : e v = mfderiv ThreeModel ThreeModel (Φ : M → N) x v :=
    congrArg (fun f : TangentSpace ThreeModel x →L[ℝ] TangentSpace ThreeModel (Φ x) => f v) hcle
  have hw : e w = mfderiv ThreeModel ThreeModel (Φ : M → N) x w :=
    congrArg (fun f : TangentSpace ThreeModel x →L[ℝ] TangentSpace ThreeModel (Φ x) => f w) hcle
  rwa [show ![e v, e w] = ![(mfderiv ThreeModel ThreeModel (Φ : M → N) x) v,
      (mfderiv ThreeModel ThreeModel (Φ : M → N) x) w] by rw [hv, hw]] at hA

theorem admitsConstantPositiveSectionalCurvature_of_diffeomorph_sphereThree
    (M : ConnectedClosedOrientedManifold.{u} 3)
    (e : Diffeomorph ThreeModel ThreeModel M.Carrier
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ∞) :
    admitsConstantPositiveSectionalCurvature (I := ThreeModel) (M := M.Carrier) :=
  ⟨Diffeomorph.pullbackMetric
      (roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3)) e,
    constantPositiveSectionalCurvatureMetric_pullback
      (roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3))
      constantPositiveSectionalCurvatureMetric_roundMetric_sphereThree e⟩

private noncomputable def diffeomorphOfPartialDiffeomorphUniv
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    {N : Type*} [TopologicalSpace N] [ChartedSpace H N]
    (Φ : PartialDiffeomorph I I M N ∞)
    (hs : Φ.source = Set.univ) (ht : Φ.target = Set.univ) :
    Diffeomorph I I M N ∞ where
  toEquiv :=
    { toFun := Φ
      invFun := Φ.symm
      left_inv := fun x => Φ.left_inv' (by rw [hs]; exact Set.mem_univ x)
      right_inv := fun y => Φ.right_inv' (by rw [ht]; exact Set.mem_univ y) }
  contMDiff_toFun := by
    have h : ContMDiff I I ∞ (⇑Φ) := by
      rw [← contMDiffOn_univ, ← hs]
      exact Φ.contMDiffOn_toFun
    simpa using h
  contMDiff_invFun := by
    have h : ContMDiff I I ∞ (⇑Φ.symm) := by
      rw [← contMDiffOn_univ, ← ht]
      exact Φ.contMDiffOn_invFun
    simpa using h

theorem admitsConstantPositiveSectionalCurvature_of_roundComponent
    (M : ConnectedClosedOrientedManifold.{u} 3)
    {D : DifferentialGeometry.Geometry.Curvature.RealTimeInterval}
    {S : SolutionOn (I := ThreeModel) (M := M.Carrier) D}
    {eps : ℝ} {x : M.Carrier} {t : ℝ}
    (R : RoundComponent
      S eps x t Set.univ) :
    admitsConstantPositiveSectionalCurvature (I := ThreeModel) (M := M.Carrier) := by
  let _ : TopologicalSpace R.Z := R.topology
  let _ : ChartedSpace ThreeSpace R.Z := R.charted
  let _ : IsManifold ThreeModel ∞ R.Z := R.smooth
  let _ : T2Space R.Z := R.t2
  let _ : CompactSpace R.Z := R.compact
  let _ : ConnectedSpace R.Z := R.connected
  have hZ : constantPositiveSectionalCurvatureMetric R.metric := by
    apply (constantPositiveSectionalCurvatureMetric_iff _).2
    refine ⟨1 / 6, by norm_num, fun z v w hLI => ?_⟩
    have hvec : (fun i : Fin 4 => ![v, w, w, v] i) = vec4 v w w v := by
      funext i
      fin_cases i <;> rfl
    rw [DifferentialGeometry.Geometry.Riemannian.sectionalCurvature_eq_metricRm04StandardAt_div,
      DifferentialGeometry.Geometry.Curvature.metricRm04StandardAt_apply, ← hvec,
      R.constant_curvature z v w]
    have hden : 0 < R.metric.inner z v v * R.metric.inner z w w - (R.metric.inner z v w) ^ 2 := by
      simpa only [DifferentialGeometry.Geometry.Riemannian.sectionalCurvatureDenominator_def]
        using Riemannian.sectionalCurvatureDenominator_pos_of_linearIndependent
          (I := ThreeModel) (M := R.Z) R.metric z v w hLI
    field_simp [ne_of_gt hden]
  exact ⟨Diffeomorph.pullbackMetric R.metric
      (diffeomorphOfPartialDiffeomorphUniv R.map R.source_eq R.target_eq).symm,
    constantPositiveSectionalCurvatureMetric_pullback R.metric hZ
      (diffeomorphOfPartialDiffeomorphUniv R.map R.source_eq R.target_eq).symm⟩

theorem admitsConstantPositiveSectionalCurvature_of_positiveComponent_sphere
    (M : ConnectedClosedOrientedManifold.{u} 3)
    {F : PartialDiffeomorph (𝓡 3) ThreeModel
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) M.Carrier ∞}
    (source_eq : F.source = Set.univ) (target_eq : F.target = Set.univ) :
    admitsConstantPositiveSectionalCurvature (I := ThreeModel) (M := M.Carrier) :=
  admitsConstantPositiveSectionalCurvature_of_diffeomorph_sphereThree M
    (diffeomorphOfPartialDiffeomorphUniv F source_eq target_eq).symm

theorem componentwisePositiveCurvatureOrSphereProduct_of_componentwiseRoundOrSphereProduct
    (D : ClosedOrientedManifold.{u} 3)
    (h : ∀ C : ConnectedComponents D.Carrier,
      (∃ (D' : DifferentialGeometry.Geometry.Curvature.RealTimeInterval)
          (S : SolutionOn (I := ThreeModel) (M := (D.component C).Carrier) D')
          (eps : ℝ) (x : (D.component C).Carrier) (t : ℝ),
        Nonempty (RoundComponent S eps x t Set.univ)) ∨
      isSphereTwoTimesCircleFactor (D.component C)) :
    componentwisePositiveCurvatureOrSphereProduct D := by
  intro C
  refine ⟨[D.component C], ?_, ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩⟩
  intro F hF
  rw [List.mem_singleton] at hF
  subst hF
  rcases h C with ⟨D', S, eps, x, t, ⟨R⟩⟩ | hs
  · exact Or.inl (admitsConstantPositiveSectionalCurvature_of_roundComponent (D.component C) R)
  · exact Or.inr hs

theorem
    componentwiseStandardFactorOrProjectiveThreeSpaceSum_of_positive_space_form_or_product_or_sum
    (D : ClosedOrientedManifold.{u} 3)
    (h : ∀ C : ConnectedComponents D.Carrier,
      admitsConstantPositiveSectionalCurvature (I := ThreeModel) (M := (D.component C).Carrier) ∨
        isSphereTwoTimesCircleFactor (D.component C) ∨
        isProjectiveThreeSpaceConnectedSum (D.component C)) :
    D.componentwiseStandardFactorOrProjectiveThreeSpaceSum := by
  intro C
  rcases h C with hp | hs | hproj
  · exact Or.inl (isStandardFactor_of_admitsConstantPositiveSectionalCurvature
    (M := D.component C) hp)
  · exact Or.inl (isStandardFactor_of_isSphereTwoTimesCircleFactor hs)
  · exact Or.inr hproj

theorem MetricCutCapEvent.poincareStandardDiscarded_of_componentwiseRoundOrSphereProduct
    {P Q : OrientedThreeStage.{u}} {a s : ℝ} (E : MetricCutCapEvent P Q a s)
    (h : ∀ C : ConnectedComponents E.discarded.Carrier,
      (∃ (D' : DifferentialGeometry.Geometry.Curvature.RealTimeInterval)
          (S : SolutionOn (I := ThreeModel)
            (M := (E.discarded.toClosedOrientedManifold.component C).Carrier) D')
          (eps : ℝ) (x : (E.discarded.toClosedOrientedManifold.component C).Carrier) (t : ℝ),
        Nonempty (RoundComponent S eps x t Set.univ)) ∨
      isSphereTwoTimesCircleFactor (E.discarded.toClosedOrientedManifold.component C)) :
    E.poincareStandardDiscarded :=
  MetricCutCapEvent.poincareStandardDiscarded_of_componentwisePositiveCurvatureOrSphereProduct
    E
    (componentwisePositiveCurvatureOrSphereProduct_of_componentwiseRoundOrSphereProduct
      E.discarded.toClosedOrientedManifold h)

theorem admitsConstantPositiveSectionalCurvature_of_diffeomorph
    {M N : ConnectedClosedOrientedManifold.{u} 3}
    (e : Diffeomorph ThreeModel ThreeModel M.Carrier N.Carrier ∞)
    (h : admitsConstantPositiveSectionalCurvature (I := ThreeModel) (M := N.Carrier)) :
    admitsConstantPositiveSectionalCurvature (I := ThreeModel) (M := M.Carrier) :=
  h.elim fun g hg =>
    ⟨Diffeomorph.pullbackMetric g e,
      constantPositiveSectionalCurvatureMetric_pullback g hg e⟩

theorem admitsConstantPositiveSectionalCurvature_standardThreeSphereLift :
    admitsConstantPositiveSectionalCurvature (I := ThreeModel)
      (M := standardThreeSphereLift.{u}.Carrier) :=
  admitsConstantPositiveSectionalCurvature_of_diffeomorph_sphereThree standardThreeSphereLift.{u}
    ((standardThreeSphereLiftDiffeomorph.{u}).symm)

theorem isProjectiveThreeSpaceConnectedSum_of_orientedDiffeomorph
    {M N : ConnectedClosedOrientedManifold.{u} 3}
    (e : ClosedOrientedManifold.OrientedDiffeomorph M.toClosedOrientedManifold
      N.toClosedOrientedManifold)
    (h : isProjectiveThreeSpaceConnectedSum N) : isProjectiveThreeSpaceConnectedSum M :=
  h.elim fun ρ => ⟨e.trans ρ⟩

theorem componentwisePositiveCurvatureOrSphereProduct_standardThreeSphereLift :
    componentwisePositiveCurvatureOrSphereProduct
      standardThreeSphereLift.{u}.toClosedOrientedManifold :=
  fun C => ⟨[standardThreeSphereLift.{u}.toClosedOrientedManifold.component C], by
    intro F hF
    rw [List.mem_singleton] at hF
    subst hF
    exact Or.inl (admitsConstantPositiveSectionalCurvature_of_diffeomorph
      (M := standardThreeSphereLift.toClosedOrientedManifold.component C)
      (N := standardThreeSphereLift)
      ((standardThreeSphereLift.toClosedOrientedManifold.componentOrientedDiffeomorph C).1)
      admitsConstantPositiveSectionalCurvature_standardThreeSphereLift),
    ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩⟩

theorem componentwisePositiveCurvatureOrSphereProduct_sphereTwoTimesCircleLift :
    componentwisePositiveCurvatureOrSphereProduct
      sphereTwoTimesCircleLift.toClosedOrientedManifold :=
  fun C => ⟨[sphereTwoTimesCircleLift.toClosedOrientedManifold.component C], by
    intro F hF
    rw [List.mem_singleton] at hF
    subst hF
    exact Or.inr (isSphereTwoTimesCircleFactor_of_orientedDiffeomorph
      ⟨sphereTwoTimesCircleLift.toClosedOrientedManifold.componentOrientedDiffeomorph C⟩
      isSphereTwoTimesCircleFactor_sphereTwoTimesCircleLift),
    ⟨ClosedOrientedManifold.OrientedDiffeomorph.refl _⟩⟩

theorem componentwiseStandardFactorOrProjectiveThreeSpaceSum_projectiveThreeSpaceSum :
    ClosedOrientedManifold.componentwiseStandardFactorOrProjectiveThreeSpaceSum
      (connectedSum projectiveThreeSpaceLift.{u}
        projectiveThreeSpaceLift.{u}).toClosedOrientedManifold :=
  fun C => Or.inr (isProjectiveThreeSpaceConnectedSum_of_orientedDiffeomorph
    (ClosedOrientedManifold.componentOrientedDiffeomorph
      (connectedSum projectiveThreeSpaceLift.{u}
        projectiveThreeSpaceLift.{u}).toClosedOrientedManifold C)
    isProjectiveThreeSpaceConnectedSum_self)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
