import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import DifferentialGeometry.Topology.VectorField.Linearization

set_option autoImplicit false

open Bundle Set
open scoped Manifold ContDiff Topology

noncomputable section

namespace DifferentialGeometry.VectorField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

section BundleMap

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

theorem mfderiv_tangentBundle {f : N → TangentBundle I M} {x : N}
    (hf : MDifferentiableAt J I.tangent f x) :
    mfderiv J I.tangent f x =
      (mfderiv J I (fun y => (f y).proj) x).prod
        (mfderiv J 𝓘(𝕜, E)
          (fun y => (trivializationAt E (TangentSpace I) (f x).proj (f y)).2) x) := by
  obtain ⟨hb, hv⟩ := (mdifferentiableAt_totalSpace I f).mp hf
  rw [← mfderiv_prodMk hb hv, hf.mfderiv, (hb.prodMk hv).mfderiv]
  congr 1

end BundleMap

theorem mfderiv_tangentBundle_proj_apply (p : TangentBundle I M)
    (w : TangentSpace I.tangent p) :
    mfderiv I.tangent I (Bundle.TotalSpace.proj : TangentBundle I M → M) p w = w.1 := by
  have hh := mfderiv_tangentBundle (I := I) (J := I.tangent)
    (f := id) (x := p) mdifferentiableAt_id
  rw [mfderiv_id] at hh
  have hval := congrArg (fun L : TangentSpace I.tangent p →L[𝕜]
      TangentSpace I.tangent p => (L w).1) hh
  exact hval.symm

def verticalLift (x : M) : TangentSpace I x →L[𝕜]
    TangentSpace I.tangent (zeroSection E (TangentSpace I) x) :=
  ContinuousLinearMap.inr 𝕜 (TangentSpace I x) (TangentSpace I x)

@[simp]
theorem verticalLift_apply (x : M) (v : TangentSpace I x) :
    verticalLift (I := I) x v = (0, v) := rfl

theorem mfderiv_tangentBundle_proj_verticalLift (x : M) (v : TangentSpace I x) :
    mfderiv I.tangent I (Bundle.TotalSpace.proj : TangentBundle I M → M)
      (zeroSection E (TangentSpace I) x) (verticalLift x v) = 0 := by
  rw [mfderiv_tangentBundle_proj_apply]
  rfl

theorem verticalLift_eq_mfderiv_fiberCurve (x : M) (v : TangentSpace I x) :
    verticalLift (I := I) x v =
      mfderiv 𝓘(𝕜, 𝕜) I.tangent
        (fun t : 𝕜 => (⟨x, t • v⟩ : TangentBundle I M)) 0 (1 : 𝕜) := by
  symm
  have heq : (fun t : 𝕜 =>
      (trivializationAt E (TangentSpace I) x (⟨x, t • v⟩ : TangentBundle I M)).2) =
      (fun t : 𝕜 => t • v) := by
    funext t
    change tangentCoordChange I x x x (t • v) = t • v
    exact tangentCoordChange_self (mem_extChartAt_source x)
  have hd : MDifferentiableAt 𝓘(𝕜, 𝕜) I.tangent
      (fun t : 𝕜 => (⟨x, t • v⟩ : TangentBundle I M)) 0 := by
    rw [mdifferentiableAt_totalSpace]
    refine ⟨mdifferentiableAt_const, ?_⟩
    rw [heq]
    exact mdifferentiableAt_id.smul mdifferentiableAt_const
  rw [mfderiv_tangentBundle hd]
  change ((mfderiv 𝓘(𝕜, 𝕜) I (fun _ : 𝕜 => x) 0) (1 : 𝕜),
    (mfderiv 𝓘(𝕜, 𝕜) 𝓘(𝕜, E) _ 0) (1 : 𝕜)) = _
  rw [heq]
  change ((mfderiv 𝓘(𝕜, 𝕜) I (fun _ : 𝕜 => x) 0) (1 : 𝕜),
    (mfderiv (M' := E) 𝓘(𝕜, 𝕜) 𝓘(𝕜, E) (fun t : 𝕜 => t • v : 𝕜 → E) 0) (1 : 𝕜)) = _
  rw [mfderiv_const]
  erw [mfderiv_eq_fderiv]
  let w : E := v
  change ((0 : E), (fderiv 𝕜 (fun t : 𝕜 => t • w) 0) 1) = (0, w)
  simp [fderiv_fun_smul]


theorem mfderiv_zeroSection_apply (x : M) (v : TangentSpace I x) :
    mfderiv I I.tangent (zeroSection E (TangentSpace I)) x v = (v, 0) := by
  exact congrArg (fun p : TangentBundle I.tangent (TangentBundle I M) => p.2)
    (TangentBundle.tangentMap_tangentBundle_pure (I := I) (⟨x, v⟩ : TangentBundle I M))

theorem mfderiv_section {V : ∀ x : M, TangentSpace I x} {x : M}
    (hV : MDifferentiableAt I I.tangent (fun y => (⟨y, V y⟩ : TangentBundle I M)) x) :
    mfderiv I I.tangent (fun y => (⟨y, V y⟩ : TangentBundle I M)) x =
      (ContinuousLinearMap.id 𝕜 (TangentSpace I x)).prod
        (mfderiv I 𝓘(𝕜, E)
          (fun y => (trivializationAt E (TangentSpace I) x ⟨y, V y⟩).2) x) := by
  rw [mfderiv_tangentBundle hV]
  congr 1
  exact mfderiv_id

theorem existsUnique_vertical_linearization {V : ∀ x : M, TangentSpace I x} {x : M}
    (hV : MDifferentiableAt I I.tangent (fun y => (⟨y, V y⟩ : TangentBundle I M)) x)
    (hzero : V x = 0) :
    ∃! L : TangentSpace I x →L[𝕜] TangentSpace I x,
      ∀ v : TangentSpace I x,
        tangentMap I I.tangent (fun y => (⟨y, V y⟩ : TangentBundle I M)) ⟨x, v⟩ =
          ⟨zeroSection E (TangentSpace I) x,
            mfderiv I I.tangent (zeroSection E (TangentSpace I)) x v + verticalLift x (L v)⟩ := by
  let L : TangentSpace I x →L[𝕜] TangentSpace I x :=
    mfderiv I 𝓘(𝕜, E) (fun y => (trivializationAt E (TangentSpace I) x ⟨y, V y⟩).2) x
  refine ⟨L, ?_, ?_⟩
  · intro v
    rw [tangentMap, mfderiv_section hV, mfderiv_zeroSection_apply]
    simp only [hzero, zeroSection, TotalSpace.mk.injEq, true_and]
    apply heq_of_eq
    change (v, L v) = (v + 0, 0 + L v)
    simp only [add_zero, zero_add]
  · intro K hK
    ext v
    have hh := congrArg (fun p : TangentBundle I.tangent (TangentBundle I M) => p.2.2) (hK v)
    rw [tangentMap, mfderiv_section hV, mfderiv_zeroSection_apply] at hh
    change L v = 0 + K v at hh
    simpa only [zero_add] using hh.symm

def linearizationAtZero {V : ∀ x : M, TangentSpace I x} {x : M}
    (hV : MDifferentiableAt I I.tangent (fun y => (⟨y, V y⟩ : TangentBundle I M)) x)
    (hzero : V x = 0) : TangentSpace I x →L[𝕜] TangentSpace I x :=
  (existsUnique_vertical_linearization hV hzero).exists.choose


theorem tangentMap_section_eq_linearizationAtZero
    {V : ∀ x : M, TangentSpace I x} {x : M}
    (hV : MDifferentiableAt I I.tangent (fun y => (⟨y, V y⟩ : TangentBundle I M)) x)
    (hzero : V x = 0) (v : TangentSpace I x) :
    tangentMap I I.tangent (fun y => (⟨y, V y⟩ : TangentBundle I M)) ⟨x, v⟩ =
      ⟨zeroSection E (TangentSpace I) x,
        mfderiv I I.tangent (zeroSection E (TangentSpace I)) x v +
          verticalLift x (linearizationAtZero hV hzero v)⟩ :=
  (existsUnique_vertical_linearization hV hzero).exists.choose_spec v

theorem linearizationAtZero_eq_mfderiv
    {V : ∀ x : M, TangentSpace I x} {x : M}
    (hV : MDifferentiableAt I I.tangent (fun y => (⟨y, V y⟩ : TangentBundle I M)) x)
    (hzero : V x = 0) :
    linearizationAtZero hV hzero =
      mfderiv I 𝓘(𝕜, E)
        (fun y => (trivializationAt E (TangentSpace I) x ⟨y, V y⟩).2) x := by
  ext v
  have hh := congrArg (fun p : TangentBundle I.tangent (TangentBundle I M) => p.2.2)
    (tangentMap_section_eq_linearizationAtZero hV hzero v)
  rw [tangentMap, mfderiv_section hV, mfderiv_zeroSection_apply] at hh
  change (mfderiv I 𝓘(𝕜, E)
    (fun y => (trivializationAt E (TangentSpace I) x ⟨y, V y⟩).2) x) v =
      (0 : TangentSpace I x) + linearizationAtZero hV hzero v at hh
  rw [zero_add] at hh
  exact hh.symm

theorem linearizationAtZero_congr_of_eventuallyEq
    {V W : ∀ x : M, TangentSpace I x} {x : M}
    (hV : MDifferentiableAt I I.tangent (fun y => (⟨y, V y⟩ : TangentBundle I M)) x)
    (hW : MDifferentiableAt I I.tangent (fun y => (⟨y, W y⟩ : TangentBundle I M)) x)
    (hVzero : V x = 0) (hWzero : W x = 0)
    (heq : (fun y => (⟨y, V y⟩ : TangentBundle I M)) =ᶠ[𝓝 x]
      (fun y => (⟨y, W y⟩ : TangentBundle I M))) :
    linearizationAtZero hV hVzero = linearizationAtZero hW hWzero := by
  rw [linearizationAtZero_eq_mfderiv, linearizationAtZero_eq_mfderiv]
  apply Filter.EventuallyEq.mfderiv_eq
  filter_upwards [heq] with y hy
  exact congrArg (fun p : TangentBundle I M =>
    (trivializationAt E (TangentSpace I) x p).2) hy

theorem linearizationAtZero_eq_fderivWithin
    {V : ∀ x : M, TangentSpace I x} {x : M}
    (hV : MDifferentiableAt I I.tangent (fun y => (⟨y, V y⟩ : TangentBundle I M)) x)
    (hzero : V x = 0) :
    linearizationAtZero hV hzero =
      fderivWithin 𝕜
        (fun z : E => (trivializationAt E (TangentSpace I) x
          (⟨(extChartAt I x).symm z, V ((extChartAt I x).symm z)⟩ : TangentBundle I M)).2)
        (range I) (extChartAt I x x) := by
  rw [linearizationAtZero_eq_mfderiv hV hzero]
  exact ((mdifferentiableAt_section I V).mp hV).mfderiv

theorem linearizationAtZero_modelSpace_eq_fderiv {V : E → E} {x : E}
    (hV : MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, E).tangent
      (fun y => (⟨y, V y⟩ : TangentBundle 𝓘(𝕜, E) E)) x) (hzero : V x = 0) :
    linearizationAtZero hV hzero = fderiv 𝕜 V x := by
  rw [linearizationAtZero_eq_fderivWithin hV hzero]
  simp only [mfld_simps, fderivWithin_univ]
  rfl

theorem fromTangentSpace_linearizationAtZero {V : E → E} {x : E}
    (hV : MDifferentiableAt 𝓘(𝕜, E) 𝓘(𝕜, E).tangent
      (fun y => (⟨y, V y⟩ : TangentBundle 𝓘(𝕜, E) E)) x) (hzero : V x = 0) :
    (NormedSpace.fromTangentSpace x).toContinuousLinearMap ∘L
      linearizationAtZero hV hzero ∘L
        (NormedSpace.fromTangentSpace x).symm.toContinuousLinearMap = fderiv 𝕜 V x := by
  rw [linearizationAtZero_modelSpace_eq_fderiv]
  ext v
  rfl

end DifferentialGeometry.VectorField
