import DifferentialGeometry.Analysis.Integration.Measure.Chart.HaarBasis
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Area
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Domain
import DifferentialGeometry.Geometry.Comparison.Volume.Segment.Gauss
import DifferentialGeometry.Geometry.Exponential.NormalCoordinates.Frame

set_option autoImplicit false

noncomputable section

open Bundle Function Manifold MeasureTheory Metric Set
open scoped ENNReal Manifold

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.NormalCoordinates
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
  [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (↑(⊤ : ℕ∞) : WithTop ℕ∞) M]

omit [NeZero (Module.finrank Real E)] [I.Boundaryless] in
theorem preimage_gBall
    (g : SmoothRiemannianMetric I M) (x : M) (R : Real) :
    (normalFrame (I := I) (E := E) g x) ⁻¹'
        gBall (I := I) g x R =
      ball (0 : E) R := by
  ext w
  simp only [mem_preimage, gBall, mem_ofPred_eq, mem_ball, dist_zero_right]
  rw [normalFrame_sqrt]

section Measure

variable [T2Space M] [T2Space (TangentBundle I M)] [SigmaCompactSpace M]
variable [RiemannianBundle (fun x : M => TangentSpace I x)]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

omit [T2Space (TangentBundle I M)] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem expJac_normal_int
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (v : TangentSpace I y),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y v v)))
    (x : M) (K : Set E) :
    (∫⁻ v in K,
        ENNReal.ofReal (expJacDensity (I := I) g hEnorm x v)
        ∂(modelHaar (E := E))) =
      ∫⁻ w in (normalFrame (I := I) (E := E) g x) ⁻¹' K,
        ENNReal.ofReal
          (curveDensity (I := I) g
            (intrinsicGeodesic (I := I) g hEnorm x
              (normalFrame (I := I) (E := E) g x w))
            (fun i t =>
              intrinsicJacobi (I := I) g hEnorm x
                (normalFrame (I := I) (E := E) g x w)
                ((normalBasis (I := I) g x) i) t)
            1)
        ∂(volume : Measure E) := by
  classical
  let b : Module.Basis (Fin (Module.finrank Real E)) Real E :=
    DifferentialGeometry.Tensor.Coordinates.chartModelBasis E
  let b' : Module.Basis (Fin (Module.finrank Real E)) Real E :=
    normalBasis (I := I) g x
  let L : E ≃L[Real] E := normalFrame (I := I) (E := E) g x
  let Dn : E → Real := fun v =>
    curveDensity (I := I) g
      (intrinsicGeodesic (I := I) g hEnorm x v)
      (fun i t => intrinsicJacobi (I := I) g hEnorm x v (b' i) t) 1
  have hD (v : E) :
      ENNReal.ofReal |b.det b'| *
          ENNReal.ofReal (expJacDensity (I := I) g hEnorm x v) =
        ENNReal.ofReal (Dn v) := by
    rw [← ENNReal.ofReal_mul (abs_nonneg (b.det b'))]
    congr 1
    change |b.det b'| * expJacDensity (I := I) g hEnorm x v =
      curveDensity (I := I) g
        (intrinsicGeodesic (I := I) g hEnorm x v)
        (fun i t => intrinsicJacobi (I := I) g hEnorm x v (b' i) t) 1
    exact (jacDens_basis (I := I) g hEnorm x v b b').symm
  have hbasis :
      (∫⁻ v in K,
          ENNReal.ofReal (expJacDensity (I := I) g hEnorm x v)
          ∂(modelHaar (E := E))) =
        ∫⁻ v in K, ENNReal.ofReal (Dn v) ∂b'.addHaar := by
    calc
      _ = ∫⁻ v in K,
          ENNReal.ofReal (expJacDensity (I := I) g hEnorm x v)
          ∂b.addHaar := by rfl
      _ = ∫⁻ v in K,
          ENNReal.ofReal |b.det b'| *
            ENNReal.ofReal (expJacDensity (I := I) g hEnorm x v)
          ∂b'.addHaar := by
            rw [← Module.Basis.det_smul_addHaar b b',
              setLIntegral_smul_measure]
            exact
              (lintegral_const_mul' _ _ ENNReal.ofReal_ne_top).symm
      _ = ∫⁻ v in K, ENNReal.ofReal (Dn v) ∂b'.addHaar := by
            apply lintegral_congr
            exact hD
  have hbmap :
      (stdOrthonormalBasis Real E).toBasis.map L.toLinearEquiv = b' := by
    ext i
    change normalFrame (I := I) (E := E) g x
        ((stdOrthonormalBasis Real E) i) =
      normalBasis (I := I) g x i
    exact normalFrame_basis (I := I) g x i
  have hmap :
      Measure.map L (volume : Measure E) = b'.addHaar := by
    calc
      _ = Measure.map L (stdOrthonormalBasis Real E).toBasis.addHaar := by
            rw [(stdOrthonormalBasis Real E).addHaar_eq_volume]
      _ = ((stdOrthonormalBasis Real E).toBasis.map
          L.toLinearEquiv).addHaar :=
            Module.Basis.map_addHaar _ _
      _ = b'.addHaar := congrArg Module.Basis.addHaar hbmap
  have hmp : MeasurePreserving L (volume : Measure E) b'.addHaar :=
    ⟨L.continuous.measurable, hmap⟩
  rw [hbasis]
  change (∫⁻ v in K, ENNReal.ofReal (Dn v) ∂b'.addHaar) =
    ∫⁻ w in L ⁻¹' K, ENNReal.ofReal (Dn (L w)) ∂(volume : Measure E)
  exact (hmp.setLIntegral_comp_preimage_emb
    L.toHomeomorph.toMeasurableEquiv.measurableEmbedding
    (fun v => ENNReal.ofReal (Dn v)) K).symm

omit [T2Space (TangentBundle I M)] in
attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem framed_mul_le_area
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun y : M => TangentSpace I y)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : ∀ (y : M) (v : TangentSpace I y),
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner y v v)))
    (x : M) {U : Set E} (hU : MeasurableSet U)
    {S : Set M} (hS : MeasurableSet S) {m : ENat}
    (hloc : IsLocalHomeomorphOn
      (intrinsicFramedExp (I := I) g hEnorm x) U)
    (hcount : ∀ y ∈ S, m ≤
      {w : E | w ∈ U ∧
        intrinsicFramedExp (I := I) g hEnorm x w = y}.encard) :
    m.toENNReal *
        riemannianVolumeMeasure (I := I) (M := M) g S
      ≤ ∫⁻ w in U,
          ENNReal.ofReal
            (curveDensity (I := I) g
              (intrinsicGeodesic (I := I) g hEnorm x
                (normalFrame (I := I) (E := E) g x w))
              (fun i t =>
                intrinsicJacobi (I := I) g hEnorm x
                  (normalFrame (I := I) (E := E) g x w)
                  ((normalBasis (I := I) g x) i) t)
              1)
        ∂(volume : Measure E) := by
  classical
  let L : E ≃L[Real] E :=
    (normalFrame (I := I) (E := E) g x).trans
      (tangentSpaceModelContinuousLinearEquiv (I := I) x)
  have hL (w : E) :
      (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (L w) =
        normalFrame (I := I) g x w := by
    change (tangentSpaceModelContinuousLinearEquiv (I := I) x).symm
        (tangentSpaceModelContinuousLinearEquiv (I := I) x
          (normalFrame (I := I) g x w)) = normalFrame (I := I) g x w
    exact ContinuousLinearEquiv.symm_apply_apply _ _
  let K : Set E := L '' U
  have hK : MeasurableSet K := by
    exact
      L.toHomeomorph.toMeasurableEquiv.measurableSet_image.mpr hU
  have hLloc :
      IsLocalHomeomorphOn (fun w : E => L w) U :=
    L.toHomeomorph.isLocalHomeomorph.isLocalHomeomorphOn.mono
      (Set.subset_univ U)
  have hcomp :
      IsLocalHomeomorphOn
        ((fun v : E =>
          expMapIntrinsic (I := I) g hEnorm x
            (show TangentSpace I x from v)) ∘
          fun w : E => L w) U := by
    rw [show ((fun v : E =>
        expMapIntrinsic (I := I) g hEnorm x
          (show TangentSpace I x from v)) ∘ fun w : E => L w) =
      intrinsicFramedExp (I := I) g hEnorm x by
        funext w
        change expMapIntrinsic (I := I) g hEnorm x
            ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (L w)) =
          intrinsicFramedExp (I := I) g hEnorm x w
        calc
          _ = expMapIntrinsic (I := I) g hEnorm x
              (normalFrame (I := I) g x w) :=
            congrArg (expMapIntrinsic (I := I) g hEnorm x) (hL w)
          _ = intrinsicFramedExp (I := I) g hEnorm x w :=
            (intrFrame_apply (I := I) g hEnorm x w).symm]
    exact hloc
  have hraw :
      IsLocalHomeomorphOn
        (fun v : E =>
          expMapIntrinsic (I := I) g hEnorm x
            (show TangentSpace I x from v)) K := by
    simpa only [K] using hcomp.of_comp_right hLloc
  have hcountRaw :
      ∀ y ∈ S, m ≤
        {v : E | v ∈ K ∧
          expMapIntrinsic (I := I) g hEnorm x
            (show TangentSpace I x from v) = y}.encard := by
    intro y hy
    let A : Set E := {w : E | w ∈ U ∧
      intrinsicFramedExp (I := I) g hEnorm x w = y}
    let B : Set E := {v : E | v ∈ K ∧
      expMapIntrinsic (I := I) g hEnorm x
        (show TangentSpace I x from v) = y}
    let emb : A ↪ B :=
      { toFun := fun w =>
          ⟨L w.1, ⟨⟨w.1, w.2.1, rfl⟩, by
            change expMapIntrinsic (I := I) g hEnorm x
                ((tangentSpaceModelContinuousLinearEquiv (I := I) x).symm (L w.1)) = y
            calc
              _ = expMapIntrinsic (I := I) g hEnorm x
                  (normalFrame (I := I) g x w.1) :=
                congrArg (expMapIntrinsic (I := I) g hEnorm x) (hL w.1)
              _ = y := by simpa only [intrFrame_apply] using w.2.2⟩⟩
        inj' := by
          intro w z hwz
          apply Subtype.ext
          apply L.injective
          exact congrArg Subtype.val hwz }
    exact
      (hcount y hy).trans (by
        simpa only [A, B] using emb.encard_le)
  have harea :=
    riemVol_mul_le_area (I := I) g hEnorm x hK hS
      hraw hcountRaw
  have hpre : L ⁻¹' K = U := by
    exact Set.preimage_image_eq U L.injective
  have hpreRaw : (normalFrame (I := I) (E := E) g x) ⁻¹' K = U := by
    change L ⁻¹' K = U
    exact hpre
  rw [expJac_normal_int (I := I) g hEnorm x K, hpreRaw] at harea
  simpa only [L] using harea

end Measure

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison

end
