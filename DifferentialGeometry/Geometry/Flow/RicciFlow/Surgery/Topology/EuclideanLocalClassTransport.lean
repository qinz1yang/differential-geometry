import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.LocalClassRealizationTransport
import DifferentialGeometry.Topology.Manifold.SmoothOrientationCompatible
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

private theorem euclideanTangentChartEquiv_eq_refl (p y : ThreeSpace)
    (hy : y ∈ (trivializationAt ThreeSpace (TangentSpace ThreeModel) p).baseSet) :
    tangentChartEquiv ThreeSpace p y hy = LinearEquiv.refl ℝ (TangentSpace ThreeModel y) := by
  have hyS : y ∈ (chartAt ThreeSpace p).source := hy
  rw [show tangentChartEquiv ThreeSpace p y hy =
      DifferentialGeometry.tangentChartEquiv ThreeModel ThreeSpace p y hyS from rfl]
  rw [DifferentialGeometry.Topology.Manifold.tangentChartEquiv_eq_preferredChartTangentEquiv
      ThreeModel p y hyS,
    DifferentialGeometry.Topology.Manifold.preferredChartTangentEquiv_model ThreeSpace p y hyS]
  ext w
  rfl

private def euclideanOrientationFun (o : TangentOrientationSection ThreeSpace) :
    ThreeSpace → Orientation ℝ ThreeSpace (Fin 3) :=
  fun y => o.orientation y

private theorem euclideanTangentOrientation_eq_near (o : TangentOrientationSection ThreeSpace)
    (z : ThreeSpace) :
    ∃ U : Set ThreeSpace, IsOpen U ∧ z ∈ U ∧
      ∀ w ∈ U, o.orientation w = o.orientation z := by
  have hz : z ∈ (trivializationAt ThreeSpace (TangentSpace ThreeModel) z).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]
    exact mem_chart_source ThreeSpace z
  obtain ⟨U, hU, hzU, hUsub, hconst⟩ := o.locally_constant z z hz
  refine ⟨U, hU, hzU, fun w hw => ?_⟩
  have hw' := hconst w hw
  rw [euclideanTangentChartEquiv_eq_refl z w (hUsub hw),
    euclideanTangentChartEquiv_eq_refl z z hz] at hw'
  have hw1 : Orientation.map (Fin 3) (LinearEquiv.refl ℝ (TangentSpace ThreeModel w))
      (o.orientation w) = o.orientation w :=
    congrArg (fun e : Orientation ℝ (TangentSpace ThreeModel w) (Fin 3) ≃
        Orientation ℝ (TangentSpace ThreeModel w) (Fin 3) => e (o.orientation w))
      (Orientation.map_refl (R := ℝ) (M := TangentSpace ThreeModel w) (Fin 3))
  have hz1 : Orientation.map (Fin 3) (LinearEquiv.refl ℝ (TangentSpace ThreeModel z))
      (o.orientation z) = o.orientation z :=
    congrArg (fun e : Orientation ℝ (TangentSpace ThreeModel z) (Fin 3) ≃
        Orientation ℝ (TangentSpace ThreeModel z) (Fin 3) => e (o.orientation z))
      (Orientation.map_refl (R := ℝ) (M := TangentSpace ThreeModel z) (Fin 3))
  exact hw1.symm.trans (hw'.trans hz1)

private theorem isLocallyConstant_euclideanOrientationFun
    (o : TangentOrientationSection ThreeSpace) :
    IsLocallyConstant (euclideanOrientationFun o) :=
  (IsLocallyConstant.iff_exists_open _).2 fun z => euclideanTangentOrientation_eq_near o z

theorem tangentOrientationSection_orientation_eq_threeSpace
    (o : TangentOrientationSection ThreeSpace) (x y : ThreeSpace) :
    o.orientation x = o.orientation y :=
  (isLocallyConstant_euclideanOrientationFun o).apply_eq_of_isPreconnected
    isPreconnected_univ (mem_univ x) (mem_univ y)

private def euclideanTranslationFun (v : ThreeSpace) : ThreeSpace → ThreeSpace :=
  fun z => z + v

private def euclideanTranslationInvFun (v : ThreeSpace) : ThreeSpace → ThreeSpace :=
  fun z => z - v

private theorem euclideanTranslationFun_leftInverse (v : ThreeSpace) :
    Function.LeftInverse (euclideanTranslationInvFun v) (euclideanTranslationFun v) :=
  fun z => add_sub_cancel_right z v

private theorem euclideanTranslationFun_rightInverse (v : ThreeSpace) :
    Function.RightInverse (euclideanTranslationInvFun v) (euclideanTranslationFun v) :=
  fun z => sub_add_cancel z v

private theorem contMDiff_add_const_fun (v : ThreeSpace) :
    ContMDiff ThreeModel ThreeModel ∞ (fun z : ThreeSpace => z + v) := by
  rw [contMDiff_iff_contDiff]
  exact contDiff_id.add contDiff_const

private theorem contMDiff_sub_const_fun (v : ThreeSpace) :
    ContMDiff ThreeModel ThreeModel ∞ (fun z : ThreeSpace => z - v) := by
  rw [contMDiff_iff_contDiff]
  exact contDiff_id.sub contDiff_const

def euclideanTranslationDiffeomorph (v : ThreeSpace) :
    ThreeSpace ≃ₘ⟮ThreeModel, ThreeModel⟯ ThreeSpace where
  toEquiv :=
    { toFun := euclideanTranslationFun v
      invFun := euclideanTranslationInvFun v
      left_inv := euclideanTranslationFun_leftInverse v
      right_inv := euclideanTranslationFun_rightInverse v }
  contMDiff_toFun := contMDiff_add_const_fun v
  contMDiff_invFun := contMDiff_sub_const_fun v

@[simp] theorem euclideanTranslationDiffeomorph_apply (v z : ThreeSpace) :
    euclideanTranslationDiffeomorph v z = z + v := rfl

private theorem fderiv_id_threeSpace (x : ThreeSpace) :
    fderiv ℝ (fun z : ThreeSpace => z) x = ContinuousLinearMap.id ℝ ThreeSpace :=
  (hasFDerivAt_id (𝕜 := ℝ) (x := x)).fderiv

private theorem euclidean_mfderiv_add_const (v x : ThreeSpace) :
    mfderiv ThreeModel ThreeModel (fun z : ThreeSpace => z + v) x =
      ContinuousLinearMap.id ℝ (TangentSpace ThreeModel x) := by
  have h : mfderiv ThreeModel ThreeModel (fun z : ThreeSpace => z + v) x =
      ContinuousLinearMap.id ℝ ThreeSpace := by
    rw [mfderiv_eq_fderiv, fderiv_add_const]
    exact fderiv_id_threeSpace x
  exact h

private theorem euclidean_mfderiv_translationDiffeomorph (v x : ThreeSpace) :
    mfderiv ThreeModel ThreeModel (⇑(euclideanTranslationDiffeomorph v)) x =
      ContinuousLinearMap.id ℝ (TangentSpace ThreeModel x) :=
  euclidean_mfderiv_add_const v x

private def euclideanTranslationHomotopy (v : ThreeSpace) :
    ContinuousMap.Homotopy
      (⟨⇑(euclideanTranslationDiffeomorph v),
        (euclideanTranslationDiffeomorph v).continuous⟩ : C(ThreeSpace, ThreeSpace))
      (ContinuousMap.id ThreeSpace) where
  toFun := fun p => p.2 + ((1 : ℝ) - (p.1 : ℝ)) • v
  continuous_toFun :=
    continuous_snd.add ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      continuous_const)
  map_zero_left := fun z => by simp
  map_one_left := fun z => by simp

private theorem euclideanTranslation_homotopic_id (v : ThreeSpace) :
    (⟨⇑(euclideanTranslationDiffeomorph v),
      (euclideanTranslationDiffeomorph v).continuous⟩ : C(ThreeSpace, ThreeSpace)).Homotopic
        (ContinuousMap.id ThreeSpace) :=
  ⟨euclideanTranslationHomotopy v⟩

theorem preservesTangentOrientation_euclideanTranslationDiffeomorph
    (o : TangentOrientationSection ThreeSpace) (v : ThreeSpace) :
    PreservesTangentOrientation o o (euclideanTranslationDiffeomorph v) := by
  refine ⟨(euclideanTranslationDiffeomorph v).contMDiff_toFun, fun x => ?_⟩
  have hderiv := euclidean_mfderiv_translationDiffeomorph v x
  refine ⟨hderiv.symm ▸ Function.bijective_id, ?_⟩
  have hL : LinearEquiv.ofBijective
      (mfderiv ThreeModel ThreeModel (⇑(euclideanTranslationDiffeomorph v)) x).toLinearMap
      (hderiv.symm ▸ Function.bijective_id) = LinearEquiv.refl ℝ (TangentSpace ThreeModel x) :=
    LinearEquiv.ext (fun w => by
      rw [LinearEquiv.ofBijective_apply, hderiv]
      rfl)
  unfold PreservesTangentOrientationAt
  refine (congrArg (fun e => Orientation.map (Fin 3) e (o.orientation x)) hL).trans ?_
  refine (congrArg (fun e : Orientation ℝ (TangentSpace ThreeModel x) (Fin 3) ≃
      Orientation ℝ (TangentSpace ThreeModel x) (Fin 3) => e (o.orientation x))
    (Orientation.map_refl (R := ℝ) (M := TangentSpace ThreeModel x) (Fin 3))).trans ?_
  exact tangentOrientationSection_orientation_eq_threeSpace o x
    (euclideanTranslationDiffeomorph v x)

theorem localClassTransport_threeSpace (o : TangentOrientationSection ThreeSpace) :
    localClassTransport o := by
  intro x
  refine ⟨univ, isOpen_univ, mem_univ x, fun y _ => ?_⟩
  refine ⟨euclideanTranslationDiffeomorph (y - x), ?_, ?_, ?_⟩
  · rw [euclideanTranslationDiffeomorph_apply, add_sub_cancel]
  · exact euclideanTranslation_homotopic_id (y - x)
  · exact localOrientationClass_natural_diffeomorph o o (euclideanTranslationDiffeomorph (y - x))
      (preservesTangentOrientation_euclideanTranslationDiffeomorph o (y - x)) x

theorem localClassRealizationLocallyConstant_threeSpace (o : TangentOrientationSection ThreeSpace) :
    localClassRealizationLocallyConstant o :=
  localClassRealizationLocallyConstant_of_localClassTransport o (localClassTransport_threeSpace o)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
