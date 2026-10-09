import DifferentialGeometry.Geometry.Thurston.SphericalProductIsometry
import DifferentialGeometry.Geometry.Thurston.SphericalProductParallelLine
import DifferentialGeometry.Geometry.Metric.UniversalCover.ParallelLineSplitting
import DifferentialGeometry.Geometry.Metric.UniversalCover.Curvature
import DifferentialGeometry.Geometry.Metric.RicciSoliton.UniversalCover
import DifferentialGeometry.Geometry.Curvature.DimensionTwo.RicciScalar
import DifferentialGeometry.Geometry.Curvature.DimensionOne.Flat
import DifferentialGeometry.Geometry.Comparison.BonnetMyers.Compactness
import DifferentialGeometry.Geometry.Metric.Sphere.Quotient.SimplyConnectedSpaceForm
import DifferentialGeometry.Geometry.Metric.ModelChange
import DifferentialGeometry.Geometry.Curvature.ModelChange
import DifferentialGeometry.Geometry.Metric.PullbackCompleteness
import DifferentialGeometry.Geometry.Metric.Pullback.Product
import DifferentialGeometry.Geometry.Metric.Convergence.Naturality.PullbackCross
import DifferentialGeometry.Topology.Manifold.MFDeriv.ModelTransport
import DifferentialGeometry.Geometry.Thurston.Atlas
import DifferentialGeometry.Geometry.Curvature.RicciRestriction
import DifferentialGeometry.Geometry.Curvature.Naturality.Pullback.LocalCross
import DifferentialGeometry.Geometry.Curvature.ScalarSectional
import DifferentialGeometry.Geometry.Curvature.Sphere.ConstCurvature
import DifferentialGeometry.Topology.Manifold.ClosedOriented

/-!
# Developing maps for `S² × ℝ` structures

Chapter 7, packet P8b, tier 2. A closed connected `3`-manifold `M` with a complete metric `g` and
a model atlas of `sphericalProductModelMetric` admits a local isometry `f : S² × ℝ → M`
(`exists_developing_of_modelAtlas`).

The Ricci kernel of `g` is a parallel line field (`isParallelSubmoduleFamily_ricciLine`), so the
universal cover splits isometrically as `N × ℝ`
(`exists_global_product_diffeomorph_of_parallel_line`, after changing the model to
`MorseModel 3`). The scalar curvature of `g` is `2`
(`metricScalarAt_eq_two_of_modelAtlas`), hence the complete simply connected surface `N` has
curvature `1`, is compact by Bonnet–Myers and isometric to the round sphere
(`exists_isometry_round_sphere_of_constant_positive_sectional_curvature`); composing with the
covering projection gives `f` (`exists_developing_of_parallelLine`).
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Geometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Topology.UniversalCover
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff

namespace GC.Geometry.SphericalProduct

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "CI" => SpatialNeckCylinderModel
local notation "MM2" => DifferentialGeometry.Topology.Morse.MorseModel 2
local notation "MM3" => DifferentialGeometry.Topology.Morse.MorseModel 3

def morseEquivThree : E3 ≃L[ℝ] MM3 := EuclideanSpace.equiv (Fin 3) ℝ

abbrev morseModelThree : ModelWithCorners ℝ MM3 E3 :=
  (𝓡 3).transContinuousLinearEquiv morseEquivThree

private local instance developingSphereDimension :
    Fact (Module.finrank ℝ E3 = 2 + 1) := ⟨by simp⟩

universe u

variable {M : Type u} [TopologicalSpace M] [ChartedSpace E3 M] [IsManifold (𝓡 3) ∞ M]
  [T2Space M] [CompactSpace M] [ConnectedSpace M]

theorem exists_developing_of_parallelLine (g : SmoothRiemannianMetric (𝓡 3) M)
    (hg : DifferentialGeometry.RiemannianMetricComplete g) (hscal : ∀ x, metricScalarAt g x = 2)
    (S : ContMDiffVectorSubbundle (I := morseModelThree) (F := MM3)
      (V := TangentSpace morseModelThree) (n := (∞ : WithTop ℕ∞)))
    (hS : S.rank = 1)
    (hpar : Connection.IsParallelSubmoduleFamily
      (g.transContinuousLinearEquiv morseEquivThree) S.fiber) :
    ∃ f : SpatialNeckCylinder → M, IsLocalDiffeomorph CI (𝓡 3) ∞ f ∧
      ∀ (x : SpatialNeckCylinder) (v w : TangentSpace CI x),
        g.inner (f x) (mfderiv CI (𝓡 3) f x v) (mfderiv CI (𝓡 3) f x w) =
          sphericalProductModelMetric.inner x v w := by
  let J := morseModelThree
  let gJ := g.transContinuousLinearEquiv morseEquivThree
  let idJ : M ≃ₘ⟮𝓡 3, J⟯ M := ContinuousLinearEquiv.toTransContinuousLinearEquiv (𝓡 3) M
    morseEquivThree
  have hgJ : DifferentialGeometry.RiemannianMetricComplete gJ :=
    DifferentialGeometry.RiemannianMetricComplete.pullbackCross g idJ.symm hg
  let : LocallyPathConnectedSpace E3 := J.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace E3 M
  let : Riemannian.Topology.SemilocallySimplyConnectedSpace M :=
    Riemannian.Topology.manifold_semilocallySimplyConnectedSpace (I := J)
  let : Inhabited M := ⟨Classical.choice (inferInstance : Nonempty M)⟩
  obtain ⟨N, topN, csN, mfdN, t2N, σN, h, hconn, hsc, hcompl, F, -, hiso⟩ :=
    exists_global_product_diffeomorph_of_parallel_line (I := J) (M := M) (m := 2) gJ hgJ S hS
      hpar
  let : TopologicalSpace N := topN
  let : ChartedSpace MM2 N := csN
  let : IsManifold 𝓘(ℝ, MM2) ∞ N := mfdN
  let : T2Space N := t2N
  let : SigmaCompactSpace N := σN
  let : ConnectedSpace N := hconn
  let : SimplyConnectedSpace N := hsc
  have hprod : Diffeomorph.pullbackMetricCross (liftedMetric (I := J) gJ) F =
      h.prod (euclideanMetric (E := ℝ)) := by
    apply SmoothRiemannianMetric.ext_inner
    intro z u v
    rw [Diffeomorph.pullbackMetricCross_inner, SmoothRiemannianMetric.prod_inner]
    have hflat : (euclideanMetric (E := ℝ)).inner z.2 u.2 v.2 = u.2 * v.2 := by
      change inner ℝ u.2 v.2 = _
      rw [RCLike.inner_apply]
      simp only [conj_trivial]
      ring
    rw [hflat]
    exact hiso z.1 z.2 u.1 v.1 u.2 v.2
  have hdim2 : Module.finrank ℝ MM2 = 2 := by
    simp [DifferentialGeometry.Topology.Morse.MorseModel]
  have hscalN : ∀ y : N, metricScalarAt h y = 2 := by
    intro y
    have h1 := metricScalarAt_productMetric h (euclideanMetric (E := ℝ)) (y, (0 : ℝ))
    have h2 := metricScalarAt_eq_zero_of_finrank_le_one (euclideanMetric (E := ℝ))
      (by simp) (0 : ℝ)
    have h3 := CheegerGromovCompactness.metricScalar_cross (liftedMetric (I := J) gJ) F
      (y, (0 : ℝ))
    rw [hprod] at h3
    have h4 := metricScalarAt_lifted (I := J) gJ (F (y, 0))
    have h5 := metricScalarAt_transContinuousLinearEquiv g morseEquivThree (proj (F (y, 0)))
    have h6 := hscal (proj (F (y, 0)))
    change metricScalarAt (h.prod (euclideanMetric (E := ℝ))) (y, (0 : ℝ)) =
      metricScalarAt h y + metricScalarAt (euclideanMetric (E := ℝ)) (0 : ℝ) at h1
    linarith
  have hsecN : ∀ (x : N) (X Y : TangentSpace 𝓘(ℝ, MM2) x),
      metricRm04StandardAt h x X Y Y X =
        1 * (h.inner x X X * h.inner x Y Y - h.inner x X Y * h.inner x X Y) := by
    intro x X Y
    rw [metricRm04StdAt_eq_scalar_div_two_of_finrank_eq_two h hdim2 x X Y Y X, hscalN,
      h.symm x Y X]
    ring
  have hRic : Riemannian.BonnetMyers.RicciBoundedBelow h
      (((Module.finrank ℝ MM2 : ℝ) - 1) * 1) := by
    intro x v
    rw [ricciTensor_eq_half_metricScalarAt_mul_inner_of_finrank_eq_two h hdim2, hscalN, hdim2]
    norm_num
  let : NeZero (Module.finrank ℝ MM2) := ⟨by rw [hdim2]; norm_num⟩
  let : CompactSpace N := Riemannian.BonnetMyers.bonnet_myers_compactSpace_of_complete_metric h
    hcompl (by rw [hdim2]) one_pos hRic
  obtain ⟨Φ, hΦ⟩ := exists_isometry_round_sphere_of_constant_positive_sectional_curvature
    (I := 𝓘(ℝ, MM2)) (M := N) (n := 2) (by norm_num) hdim2 h 1 one_pos hsecN
  let Φ' : N ≃ₘ⟮𝓘(ℝ, MM2), 𝓡 2⟯ SpatialNeckSphere := Φ
  have hΦ' : Diffeomorph.pullbackMetricCross (roundMetric (E := E3) (n := 2)) Φ' = h := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [Diffeomorph.pullbackMetricCross_inner]
    have hx := hΦ x v w
    rw [one_mul] at hx
    exact hx
  have hround : Diffeomorph.pullbackMetricCross h Φ'.symm = roundMetric (E := E3) (n := 2) :=
    Diffeomorph.pullbackMetricCross_symm_eq_iff.mp hΦ'
  let A : SpatialNeckCylinder ≃ₘ⟮CI, 𝓘(ℝ, MM2).prod 𝓘(ℝ, ℝ)⟯ (N × ℝ) :=
    Φ'.symm.prodCongr (Diffeomorph.refl 𝓘(ℝ, ℝ) ℝ ∞)
  let Ψ := A.trans F
  have hΨ : Diffeomorph.pullbackMetricCross (liftedMetric (I := J) gJ) Ψ =
      sphericalProductModelMetric := by
    rw [← Diffeomorph.pullbackMetricCross_trans, hprod, Diffeomorph.pullbackMetricCross_prodCongr,
      hround, Diffeomorph.pullbackMetricCross_refl, sphericalProductModelMetric_eq_prod]
  let f : SpatialNeckCylinder → M := fun x => proj (Ψ x)
  have hf0 : IsLocalDiffeomorph CI J ∞ f :=
    isLocalDiffeomorph_comp (proj_localDiffeo (I := J)) Ψ.isLocalDiffeomorph
  have hf : IsLocalDiffeomorph CI (𝓡 3) ∞ f := by
    have hf' := isLocalDiffeomorph_comp idJ.symm.isLocalDiffeomorph hf0
    exact hf'
  refine ⟨f, hf, fun x v w => ?_⟩
  have hcomp : mfderiv CI (𝓡 3) f x =
      (mfderiv J (𝓡 3) (id : M → M) (f x)).comp (mfderiv CI J f x) :=
    mfderiv_comp x (idJ.symm.mdifferentiable (by simp) (f x)) ((hf0 x).mdifferentiableAt (by simp))
  have hcompΨ : mfderiv CI J f x =
      (mfderiv J J (proj : Riemannian.Topology.UniversalCover M → M) (Ψ x)).comp
        (mfderiv CI J Ψ x) :=
    mfderiv_comp x (hasMFDerivAt_proj (I := J) (Ψ x)).mdifferentiableAt
      (Ψ.mdifferentiable (by simp) x)
  rw [(hasMFDerivAt_proj (I := J) (Ψ x)).mfderiv] at hcompΨ
  rw [hcomp, DifferentialGeometry.Manifold.mfderiv_id_transContinuousLinearEquiv]
  have hJ := SmoothRiemannianMetric.transContinuousLinearEquiv_inner g morseEquivThree (f x)
    (mfderiv CI J f x v) (mfderiv CI J f x w)
  change g.inner (f x) (morseEquivThree.symm (mfderiv CI J f x v))
    (morseEquivThree.symm (mfderiv CI J f x w)) = _
  rw [← hJ, hcompΨ, ← hΨ, Diffeomorph.pullbackMetricCross_inner]
  rfl

theorem metricScalarAt_roundMetric_two (x : SpatialNeckSphere) :
    metricScalarAt (roundMetric (E := E3) (n := 2)) x = 2 := by
  let : NeZero (Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))) := ⟨by simp⟩
  have hsec : ∀ u v : TangentSpace (𝓡 2) x,
      metricRm04StandardAt (roundMetric (E := E3) (n := 2)) x u v v u =
        1 * ((roundMetric (E := E3) (n := 2)).inner x u u *
            (roundMetric (E := E3) (n := 2)).inner x v v -
          ((roundMetric (E := E3) (n := 2)).inner x u v) ^ 2) := by
    intro u v
    simpa only [one_mul, pow_two] using roundMetric_sec_value (E := E3) (n := 2) x u v
  have h := Riemannian.metricScalarAt_of_constant_sectional
    (I := 𝓡 2) (M := SpatialNeckSphere) (roundMetric (E := E3) (n := 2)) x 1 hsec
  rw [finrank_euclideanSpace_fin, mul_one] at h
  rw [h]
  norm_num

theorem metricScalarAt_sphericalProductModelMetric (p : SpatialNeckCylinder) :
    metricScalarAt sphericalProductModelMetric p = 2 := by
  rw [sphericalProductModelMetric_eq_prod, metricScalarAt_productMetric,
    metricScalarAt_roundMetric_two, metricScalarAt_eq_zero_of_finrank_le_one _ (by simp)]
  norm_num

omit [CompactSpace M] [ConnectedSpace M] in
theorem metricScalarAt_eq_two_of_modelAtlas (g : SmoothRiemannianMetric (𝓡 3) M)
    (hA : GC.Geometry.ModelAtlas g sphericalProductModelMetric) (x : M) :
    metricScalarAt g x = 2 := by
  obtain ⟨e, hx, he⟩ := hA x
  let O : TopologicalSpace.Opens SpatialNeckCylinder := ⟨e.source, e.open_source⟩
  let Phi : O → M := fun y => e y
  have hPhi : IsLocalDiffeomorph CI (𝓡 3) ∞ Phi :=
    isLocalDiffeomorph_restrict_open O (fun y => ⟨e, y.2, Set.eqOn_refl _ _⟩)
  have hpull : localPullMetric g Phi hPhi = sphericalProductModelMetric.restrictOpen O := by
    apply SmoothRiemannianMetric.ext_inner
    intro y v w
    rw [localPullMetric_inner, SmoothRiemannianMetric.restrictOpen_inner]
    rw [show Phi = fun y : O => e (y : SpatialNeckCylinder) from rfl,
      DifferentialGeometry.mfderiv_restrict_open]
    exact he y y.2 v w
  have hy : e.symm x ∈ e.source := e.map_target hx
  have hex : e (e.symm x) = x := e.right_inv hx
  have h1 := metricScalarAt_localPull g Phi hPhi ⟨e.symm x, hy⟩
  rw [hpull, CheegerGromovCompactness.metricScalarAt_restrictOpen] at h1
  change _ = metricScalarAt g (e (e.symm x)) at h1
  rw [hex] at h1
  rw [← h1]
  exact metricScalarAt_sphericalProductModelMetric _

theorem exists_developing_of_modelAtlas (g : SmoothRiemannianMetric (𝓡 3) M)
    (hg : DifferentialGeometry.RiemannianMetricComplete g)
    (hA : GC.Geometry.ModelAtlas g sphericalProductModelMetric) :
    ∃ f : SpatialNeckCylinder → M, IsLocalDiffeomorph CI (𝓡 3) ∞ f ∧
      ∀ (x : SpatialNeckCylinder) (v w : TangentSpace CI x),
        g.inner (f x) (mfderiv CI (𝓡 3) f x v) (mfderiv CI (𝓡 3) f x w) =
          sphericalProductModelMetric.inner x v w := by
  let idJ : M ≃ₘ⟮𝓡 3, morseModelThree⟯ M :=
    ContinuousLinearEquiv.toTransContinuousLinearEquiv (𝓡 3) M morseEquivThree
  have hAJ : GC.Geometry.ModelAtlas (g.transContinuousLinearEquiv morseEquivThree)
      sphericalProductModelMetric := hA.pullback idJ.symm
  let : NeZero (Module.finrank ℝ MM3) :=
    ⟨by simp [DifferentialGeometry.Topology.Morse.MorseModel]⟩
  exact exists_developing_of_parallelLine g hg (metricScalarAt_eq_two_of_modelAtlas g hA)
    (ricciLine _ hAJ) rfl (isParallelSubmoduleFamily_ricciLine _ hAJ)

end GC.Geometry.SphericalProduct
