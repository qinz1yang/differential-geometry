import DifferentialGeometry.Geometry.Connection.Realization.Basic
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.VectorBundle.Hom
import Mathlib.RingTheory.Derivation.Lie

namespace DifferentialGeometry.Geometry.Connection.Realization


noncomputable section



open scoped Manifold ContDiff Topology
open _root_.Bundle

section Embedding

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H]
  (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

noncomputable def vectorFieldAction
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (f : C^∞⟮I, M; ℝ⟯) : M → ℝ :=
  fun x => mvfderiv (I := I) f x (X x)

noncomputable def vectorFieldActionSmooth
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) (f : C^∞⟮I, M; ℝ⟯) : C^∞⟮I, M; ℝ⟯ :=
  ⟨vectorFieldAction I M X f, show ContMDiff I 𝓘(ℝ, ℝ) ∞
      (vectorFieldAction I M X f) from by
    intro x₀
    have hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := f.2
    have htangent : ContMDiff (I.prod 𝓘(ℝ, E)) (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (tangentMap I 𝓘(ℝ, ℝ) f) := by
      apply ContMDiff.contMDiff_tangentMap hf
      simp
    have hcomp : ContMDiffAt I (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ℝ)) ∞
        (fun x => tangentMap I 𝓘(ℝ, ℝ) f ⟨x, X x⟩) x₀ :=
      (htangent.contMDiffAt).comp x₀ (X.contMDiff.contMDiffAt)
    rw [contMDiffAt_totalSpace] at hcomp
    obtain ⟨_, hfiber⟩ := hcomp
    convert hfiber using 1
    ext x
    simp only [vectorFieldAction, mvfderiv, tangentMap,
      trivializationAt_model_space_apply]
    rfl⟩

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [T2Space M] in
theorem contMDiffMap_mdifferentiableAt (f : C^∞⟮I, M; ℝ⟯) (x : M) :
    MDifferentiableAt I 𝓘(ℝ, ℝ) f x :=
  f.contMDiff.contMDiffAt.mdifferentiableAt (by simp)

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem vectorFieldActionSmooth_add
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (f g : C^∞⟮I, M; ℝ⟯) :
    vectorFieldActionSmooth I M X (f + g) =
      vectorFieldActionSmooth I M X f + vectorFieldActionSmooth I M X g := by
  ext x
  change vectorFieldAction I M X (f + g) x =
    vectorFieldAction I M X f x + vectorFieldAction I M X g x
  unfold vectorFieldAction
  rw [show ((f + g : C^∞⟮I, M; ℝ⟯) : M → ℝ) = (f : M → ℝ) + (g : M → ℝ) from rfl]
  rw [mvfderiv_add (contMDiffMap_mdifferentiableAt I M f x)
    (contMDiffMap_mdifferentiableAt I M g x)]
  simp [add_apply]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem vectorFieldActionSmooth_smul
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (c : ℝ) (f : C^∞⟮I, M; ℝ⟯) :
    vectorFieldActionSmooth I M X (c • f) =
      c • vectorFieldActionSmooth I M X f := by
  ext x
  change vectorFieldAction I M X (c • f) x = c * vectorFieldAction I M X f x
  unfold vectorFieldAction
  rw [show ((c • f : C^∞⟮I, M; ℝ⟯) : M → ℝ) = c • (f : M → ℝ) from by
    ext y; simp [Pi.smul_apply, smul_eq_mul]]
  have hf := contMDiffMap_mdifferentiableAt I M f x
  have hmfderiv : mfderiv I 𝓘(ℝ, ℝ) (c • (f : M → ℝ)) x = c • mfderiv I 𝓘(ℝ, ℝ) f x :=
    (hf.hasMFDerivAt.const_smul c).mfderiv
  simp only [mvfderiv, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    hmfderiv]
  change (NormedSpace.fromTangentSpace _) ((c • mfderiv I 𝓘(ℝ, ℝ) (f : M → ℝ) x) (X x)) =
    c * (NormedSpace.fromTangentSpace _) ((mfderiv I 𝓘(ℝ, ℝ) (f : M → ℝ) x) (X x))
  simp only [NormedSpace.fromTangentSpace, ContinuousLinearEquiv.coe_mk]
  exact smul_eq_mul c _

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem vectorFieldActionSmooth_leibniz
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (f g : C^∞⟮I, M; ℝ⟯) :
    vectorFieldActionSmooth I M X (f * g) =
      f * vectorFieldActionSmooth I M X g + g * vectorFieldActionSmooth I M X f := by
  ext x
  change vectorFieldAction I M X (f * g) x =
    (f : M → ℝ) x * vectorFieldAction I M X g x +
    (g : M → ℝ) x * vectorFieldAction I M X f x
  unfold vectorFieldAction
  have hf := contMDiffMap_mdifferentiableAt I M f x
  have hg := contMDiffMap_mdifferentiableAt I M g x
  rw [show ((f * g : C^∞⟮I, M; ℝ⟯) : M → ℝ) = (f : M → ℝ) • (g : M → ℝ) from by
    ext y; simp [Pi.mul_apply, smul_eq_mul]]
  change (mvfderiv (I := I) ((f : M → ℝ) • (g : M → ℝ)) x) (X x) =
    (f : M → ℝ) x * (mvfderiv (I := I) (g : M → ℝ) x) (X x) +
    (g : M → ℝ) x * (mvfderiv (I := I) (f : M → ℝ) x) (X x)
  rw [mvfderiv_smul hf hg]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem vectorFieldActionSmooth_map_one_eq_zero
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    vectorFieldActionSmooth I M X 1 = 0 := by
  ext x
  change vectorFieldAction I M X 1 x = 0
  unfold vectorFieldAction
  rw [show ((1 : C^∞⟮I, M; ℝ⟯) : M → ℝ) = fun (_ : M) => (1 : ℝ) from by ext; simp]
  rw [show mvfderiv (I := I) (fun (_ : M) => (1 : ℝ)) x (X x) =
    ((NormedSpace.fromTangentSpace (1 : ℝ)).toContinuousLinearMap ∘L
      mfderiv I 𝓘(ℝ, ℝ) (fun (_ : M) => (1 : ℝ)) x) (X x) from rfl]
  simp [mfderiv_const]

noncomputable def embedDeriv
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ where
  toLinearMap :=
    { toFun := vectorFieldActionSmooth I M X
      map_add' := vectorFieldActionSmooth_add I M X
      map_smul' := fun c f => by
        simp only [RingHom.id_apply]
        exact vectorFieldActionSmooth_smul I M X c f }
  leibniz' f g := by
    change vectorFieldActionSmooth I M X (f * g) =
      f • vectorFieldActionSmooth I M X g + g • vectorFieldActionSmooth I M X f
    rw [vectorFieldActionSmooth_leibniz I M X f g]
    simp [smul_eq_mul]
  map_one_eq_zero' := by
    change vectorFieldActionSmooth I M X 1 = 0
    exact vectorFieldActionSmooth_map_one_eq_zero I M X

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem embedDeriv_add
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    embedDeriv I M (X + Y) = embedDeriv I M X + embedDeriv I M Y := by
  ext f x
  change vectorFieldAction I M (X + Y) f x =
    vectorFieldAction I M X f x + vectorFieldAction I M Y f x
  simp only [vectorFieldAction, ContMDiffSection.coe_add, Pi.add_apply,
    ContinuousLinearMap.map_add]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
theorem embedDeriv_smul
    (φ : C^∞⟮I, M; ℝ⟯)
    (X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    embedDeriv I M (φ • X) = φ • embedDeriv I M X := by
  ext f x
  change vectorFieldAction I M (φ • X) f x =
    ((φ • embedDeriv I M X) f : M → ℝ) x
  simp only [vectorFieldAction]
  rw [show (φ • X : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x = φ x • X x from by
    simp [ContMDiffSection.coe_smulContMDiffMap]]
  rw [ContinuousLinearMap.map_smul]
  change φ x • mvfderiv (I := I) f x (X x) =
    ((φ • embedDeriv I M X) f : M → ℝ) x
  simp only [Derivation.coe_smul, Pi.smul_apply, smul_eq_mul]
  rfl

noncomputable def embedLinearMap :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ →ₗ[C^∞⟮I, M; ℝ⟯]
      Derivation ℝ C^∞⟮I, M; ℝ⟯ C^∞⟮I, M; ℝ⟯ where
  toFun := embedDeriv I M
  map_add' := embedDeriv_add I M
  map_smul' := embedDeriv_smul I M

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem mfderiv_extChartAt_ne_zero
    {x₀ : M} (v : TangentSpace I x₀) (hv : v ≠ 0) :
    mfderiv I 𝓘(ℝ, E) (extChartAt I x₀) x₀ v ≠ 0 := by
  have hmem : x₀ ∈ (extChartAt I x₀).source := mem_extChartAt_source x₀
  have hinv := isInvertible_mfderiv_extChartAt (I := I) hmem
  intro h
  apply hv
  apply hinv.injective
  rw [h, map_zero]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
    [T2Space M] in
private theorem mvfderiv_continuousLinearMap_self
    (L : E →L[ℝ] ℝ) (x : E) (v : TangentSpace 𝓘(ℝ, E) x) :
    mvfderiv (I := 𝓘(ℝ, E)) L x v =
      L (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) x v) := by
  rw [L.mdifferentiableAt.mvfderiv]
  rw [writtenInExtChartAt_model_space, modelWithCornersSelf_coe,
    Set.range_id, fderivWithin_univ]
  rw [L.fderiv]
  rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
    [IsManifold I ∞ M] in
private theorem mvfderiv_eq_chartFDeriv
    (h : M → ℝ) (x : M) (hh : MDifferentiableAt I 𝓘(ℝ, ℝ) h x) :
    mvfderiv (I := I) h x =
      (fderivWithin ℝ (h ∘ (extChartAt I x).symm) (Set.range I)
        (extChartAt I x x)).comp
          (tangentSpaceModelContinuousLinearEquiv (I := I) x).toContinuousLinearMap := by
  ext v
  rw [hh.mvfderiv]
  rw [show writtenInExtChartAt I 𝓘(ℝ, ℝ) x h =
      h ∘ (extChartAt I x).symm from by
    unfold writtenInExtChartAt
    rw [extChartAt_model_space_eq_id]
    rfl]
  rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem mfderiv_extChartAt_inverse_model
    (x : M) (z : E) :
    tangentSpaceModelContinuousLinearEquiv (I := I) x
        ((mfderiv I 𝓘(ℝ, E) (extChartAt I x) x).inverse
          ((tangentSpaceModelContinuousLinearEquiv
            (I := 𝓘(ℝ, E)) (extChartAt I x x)).symm z)) = z := by
  let d := mfderiv I 𝓘(ℝ, E) (extChartAt I x) x
  have hd : d.IsInvertible := isInvertible_mfderiv_extChartAt (mem_extChartAt_source x)
  have hcoord :
      (tangentSpaceModelContinuousLinearEquiv
          (I := 𝓘(ℝ, E)) (extChartAt I x x)).toContinuousLinearMap.comp d =
        (tangentSpaceModelContinuousLinearEquiv (I := I) x).toContinuousLinearMap := by
    rw [show d = mfderiv I 𝓘(ℝ, E) (extChartAt I x) x from rfl,
      mfderiv_extChartAt_self]
    ext v
    rfl
  have hright (w : TangentSpace 𝓘(ℝ, E) (extChartAt I x x)) :
      d (d.inverse w) = w :=
    ((hd.inverse_apply_eq).mp rfl).symm
  calc
    tangentSpaceModelContinuousLinearEquiv (I := I) x
        (d.inverse ((tangentSpaceModelContinuousLinearEquiv
          (I := 𝓘(ℝ, E)) (extChartAt I x x)).symm z)) =
      tangentSpaceModelContinuousLinearEquiv
        (I := 𝓘(ℝ, E)) (extChartAt I x x)
          (d (d.inverse ((tangentSpaceModelContinuousLinearEquiv
            (I := 𝓘(ℝ, E)) (extChartAt I x x)).symm z))) := by
              exact (DFunLike.congr_fun hcoord _).symm
    _ = z := by
      rw [hright]
      exact (tangentSpaceModelContinuousLinearEquiv
        (I := 𝓘(ℝ, E)) (extChartAt I x x)).apply_symm_apply z

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem mfderivWithin_extChartAt_symm_inverse_model
    (x : M) (v : TangentSpace I x) :
    tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) (extChartAt I x x)
        ((mfderivWithin 𝓘(ℝ, E) I (extChartAt I x).symm (Set.range I)
          (extChartAt I x x)).inverse v) =
      tangentSpaceModelContinuousLinearEquiv (I := I) x v := by
  rw [mfderivWithin_extChartAt_symm_inverse_apply]
  rfl

omit [FiniteDimensional ℝ E] [CompleteSpace E] [SigmaCompactSpace M] [T2Space M] in
private theorem mlieBracket_model
    (X Y : (x : M) → TangentSpace I x) (x : M) :
    let φ := extChartAt I x
    let s := Set.range I
    let V' := VectorField.mpullbackWithin 𝓘(ℝ, E) I φ.symm X s
    let W' := VectorField.mpullbackWithin 𝓘(ℝ, E) I φ.symm Y s
    let V : E → E := fun y =>
      tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) y (V' y)
    let W : E → E := fun y =>
      tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) y (W' y)
    tangentSpaceModelContinuousLinearEquiv (I := I) x
        (VectorField.mlieBracket I X Y x) =
      VectorField.lieBracketWithin ℝ V W s (φ x) := by
  dsimp only
  change tangentSpaceModelContinuousLinearEquiv (I := I) x
      (VectorField.mlieBracketWithin I X Y Set.univ x) = _
  rw [VectorField.mlieBracketWithin_apply]
  change tangentSpaceModelContinuousLinearEquiv (I := I) x
      ((mfderiv I 𝓘(ℝ, E) (extChartAt I x) x).inverse
        ((tangentSpaceModelContinuousLinearEquiv
          (I := 𝓘(ℝ, E)) (extChartAt I x x)).symm
        (VectorField.lieBracketWithin ℝ
          (fun y : E => tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) y
            (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm X
              (Set.range I) y))
          (fun y : E => tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) y
            (VectorField.mpullbackWithin 𝓘(ℝ, E) I (extChartAt I x).symm Y
              (Set.range I) y))
          ((extChartAt I x).symm ⁻¹' Set.univ ∩ Set.range I) (extChartAt I x x)))) = _
  rw [mfderiv_extChartAt_inverse_model]
  congr 2
  ext y
  simp only [Set.preimage_univ, Set.univ_inter]

omit [CompleteSpace E] [SigmaCompactSpace M] in
theorem embedLinearMap_injective :
    Function.Injective (embedLinearMap I M) := by
  intro X Y hXY
  apply ContMDiffSection.ext
  intro x₀
  by_contra hne
  have hD : embedLinearMap I M (X - Y) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact hXY
  have hD_action : ∀ (f : C^∞⟮I, M; ℝ⟯) (x : M),
      vectorFieldAction I M (X - Y) f x = 0 := by
    intro f x
    have h := DFunLike.congr_fun (Derivation.ext_iff.mp hD f) x
    change vectorFieldAction I M (X - Y) f x = 0 at h
    exact h
  set v := (X - Y) x₀ with hv_def
  have hv : v ≠ 0 := by
    intro heq
    apply hne
    have : X x₀ - Y x₀ = 0 := heq
    exact sub_eq_zero.mp this
  have hmem : x₀ ∈ (extChartAt I x₀).source := mem_extChartAt_source x₀
  have hinv := isInvertible_mfderiv_extChartAt (I := I) hmem
  set w := mvfderiv (I := I) (extChartAt I x₀) x₀ v
  have hw : w ≠ 0 := by
    intro heq
    apply mfderiv_extChartAt_ne_zero I M v hv
    apply (tangentSpaceModelContinuousLinearEquiv
      (I := 𝓘(ℝ, E)) (extChartAt I x₀ x₀)).injective
    rw [map_zero]
    exact heq
  have : ∃ i, (Module.finBasis ℝ E).coord i w ≠ 0 := by
    by_contra h
    apply hw
    simp only [not_exists, not_not] at h
    exact (Module.finBasis ℝ E).forall_coord_eq_zero_iff.mp h
  obtain ⟨i, hi⟩ := this
  set ℓ := (Module.finBasis ℝ E).coord i
  set ℓ_clm := LinearMap.toContinuousLinearMap ℓ
  obtain ⟨ψ⟩ : Nonempty (SmoothBumpFunction I x₀) := inferInstance
  set g : M → ℝ := fun x => ℓ_clm (extChartAt I x₀ x - extChartAt I x₀ x₀)
  have hg_smooth : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ g (chartAt H x₀).source := by
    apply ContinuousLinearMap.contMDiff (𝕜 := ℝ) (ℓ_clm) |>.comp_contMDiffOn
    exact (contMDiffOn_extChartAt (I := I)).sub contMDiffOn_const
  have hf_smooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => ψ x • g x) :=
    ψ.contMDiff_smul hg_smooth
  set f : C^∞⟮I, M; ℝ⟯ := ⟨fun x => ψ x • g x, fun x => hf_smooth.contMDiffAt⟩
  have hψ_eq_one : ψ =ᶠ[𝓝 x₀] 1 := ψ.eventuallyEq_one
  have hf_eq_g : (fun x => ψ x • g x) =ᶠ[𝓝 x₀] g := by
    filter_upwards [hψ_eq_one] with x hx
    simp [hx]
  have hf_mfderiv : mfderiv I 𝓘(ℝ, ℝ) (fun x => ψ x • g x) x₀ = mfderiv I 𝓘(ℝ, ℝ) g x₀ :=
    hf_eq_g.mfderiv_eq
  have h_ext_diff : MDifferentiableAt I 𝓘(ℝ, E) (extChartAt I x₀) x₀ :=
    mdifferentiableAt_extChartAt (mem_chart_source H x₀)
  have h_comp_diff : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (fun x => ℓ_clm (extChartAt I x₀ x)) x₀ :=
    ℓ_clm.mdifferentiableAt.comp x₀ h_ext_diff
  have h_mvfderiv_g : mvfderiv (I := I) g x₀ v = ℓ_clm w := by
    have hg_eq : g =
        ((fun x => ℓ_clm (extChartAt I x₀ x)) - fun _ => ℓ_clm (extChartAt I x₀ x₀)) := by
      funext x
      simp [g, map_sub]
    rw [hg_eq, mvfderiv_sub h_comp_diff mdifferentiableAt_const,
      sub_apply, mvfderiv_const, zero_apply, sub_zero]
    rw [show (fun x => ℓ_clm (extChartAt I x₀ x)) =
      ℓ_clm ∘ (extChartAt I x₀) from rfl]
    rw [mvfderiv_comp_apply x₀ ℓ_clm.mdifferentiableAt h_ext_diff]
    rw [mvfderiv_continuousLinearMap_self]
    rfl
  have h_zero := hD_action f x₀
  have hf_mvfderiv : mvfderiv (I := I) (f : M → ℝ) x₀ =
      mvfderiv (I := I) g x₀ := by
    change mvfderiv (I := I) (fun x => ψ x • g x) x₀ =
      mvfderiv (I := I) g x₀
    unfold mvfderiv
    rw [hf_eq_g.self_of_nhds, hf_mfderiv]
  change mvfderiv (I := I) (f : M → ℝ) x₀ ((X - Y) x₀) = 0 at h_zero
  rw [hf_mvfderiv, h_mvfderiv_g] at h_zero
  exact hi h_zero

noncomputable def mlieBracketSection
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
  ⟨VectorField.mlieBracket I X Y, by
    have hX := X.contMDiff
    have hY := Y.contMDiff
    have : IsManifold I (minSmoothness ℝ 2) M := by
      rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
    have : IsManifold I (minSmoothness ℝ 3) M := by
      rw [minSmoothness_of_isRCLikeNormedField]; infer_instance
    have : IsManifold I ((⊤ : ℕ∞) + 1) M := by
      have : ((⊤ : ℕ∞) + 1 : WithTop ℕ∞) = ∞ := by
        show ((⊤ : ℕ∞) + 1 : WithTop ℕ∞) = ∞
        simp
      exact this ▸ ‹IsManifold I ∞ M›
    exact ContDiff.mlieBracket_vectorField (I := I) (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞))
      hX hY (by
        rw [minSmoothness_of_isRCLikeNormedField]
        show ((⊤ : ℕ∞) + 1 : WithTop ℕ∞) ≤ ∞
        simp)⟩

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
theorem embedDeriv_mlieBracket
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯)
    (f : C^∞⟮I, M; ℝ⟯) :
    embedDeriv I M (mlieBracketSection I M X Y) f =
      embedDeriv I M X (embedDeriv I M Y f) -
      embedDeriv I M Y (embedDeriv I M X f) := by
  ext x₀
  change vectorFieldAction I M (mlieBracketSection I M X Y) f x₀ =
    vectorFieldAction I M X (vectorFieldActionSmooth I M Y f) x₀ -
    vectorFieldAction I M Y (vectorFieldActionSmooth I M X f) x₀
  simp only [vectorFieldAction, mlieBracketSection, ContMDiffSection.coeFn_mk]
  set φ := extChartAt I x₀ with hφ
  set y₀ := φ x₀ with hy₀
  set s := Set.range I with hs
  have hmem : x₀ ∈ φ.source := mem_extChartAt_source x₀
  have hmem_tgt : y₀ ∈ φ.target := φ.map_source hmem
  have huniq : UniqueDiffOn ℝ s := I.uniqueDiffOn
  have hy₀s : y₀ ∈ s := ⟨_, rfl⟩
  set g := (f : M → ℝ) ∘ φ.symm
  set V' := VectorField.mpullbackWithin 𝓘(ℝ, E) I φ.symm (fun x => X x) s
  set W' := VectorField.mpullbackWithin 𝓘(ℝ, E) I φ.symm (fun x => Y x) s
  set V : E → E := fun y =>
    tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) y (V' y)
  set W : E → E := fun y =>
    tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) y (W' y)
  have mvfderiv_eq : ∀ (h : M → ℝ), MDifferentiableAt I 𝓘(ℝ, ℝ) h x₀ →
      mvfderiv (I := I) h x₀ =
        (fderivWithin ℝ (h ∘ φ.symm) s y₀).comp
          (tangentSpaceModelContinuousLinearEquiv (I := I) x₀).toContinuousLinearMap := by
    intro h hh
    simpa only [φ, s, y₀] using mvfderiv_eq_chartFDeriv I M h x₀ hh
  have hf_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) (f : M → ℝ) x₀ :=
    f.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  rw [mvfderiv_eq _ hf_diff]
  rw [ContinuousLinearMap.comp_apply]
  have bracket_eq :
      tangentSpaceModelContinuousLinearEquiv (I := I) x₀
          (VectorField.mlieBracket I X Y x₀) =
        VectorField.lieBracketWithin ℝ V W s y₀ := by
    simpa only [φ, s, V', W', V, W, y₀] using
      mlieBracket_model I M X Y x₀
  change fderivWithin ℝ ((f : M → ℝ) ∘ φ.symm) s y₀
      (tangentSpaceModelContinuousLinearEquiv (I := I) x₀
        (VectorField.mlieBracket I X Y x₀)) = _
  rw [bracket_eq]
  have hV_y₀ : V y₀ =
      tangentSpaceModelContinuousLinearEquiv (I := I) x₀ (X x₀) := by
    simp only [V, V', VectorField.mpullbackWithin]
    rw [φ.left_inv hmem]
    convert mfderivWithin_extChartAt_symm_inverse_model I M x₀ (X x₀) using 1 ; rfl
  have hW_y₀ : W y₀ =
      tangentSpaceModelContinuousLinearEquiv (I := I) x₀ (Y x₀) := by
    simp only [W, W', VectorField.mpullbackWithin]
    rw [φ.left_inv hmem]
    convert mfderivWithin_extChartAt_symm_inverse_model I M x₀ (Y x₀) using 1 ; rfl
  have hg_smooth : ContDiffWithinAt ℝ ∞ g s y₀ :=
    (contMDiffAt_iff.mp (f.contMDiff.contMDiffAt (x := x₀))).2
  have hy₀_closure : y₀ ∈ closure (interior s) := I.range_subset_closure_interior hy₀s
  have hV_diff : DifferentiableWithinAt ℝ V s y₀ := by
    have hX_mdiff : MDifferentiableWithinAt _ _
        (fun x => (⟨x, X x⟩ : TangentBundle I M)) Set.univ x₀ :=
      X.contMDiff.contMDiffAt.mdifferentiableAt (by simp) |>.mdifferentiableWithinAt
    have h := hX_mdiff.differentiableWithinAt_mpullbackWithin_vectorField (I := I)
    simp only [Set.preimage_univ, Set.univ_inter] at h
    exact h
  have hW_diff : DifferentiableWithinAt ℝ W s y₀ := by
    have hY_mdiff : MDifferentiableWithinAt _ _
        (fun x => (⟨x, Y x⟩ : TangentBundle I M)) Set.univ x₀ :=
      Y.contMDiff.contMDiffAt.mdifferentiableAt (by simp) |>.mdifferentiableWithinAt
    have h := hY_mdiff.differentiableWithinAt_mpullbackWithin_vectorField (I := I)
    simp only [Set.preimage_univ, Set.univ_inter] at h
    exact h
  have hYf_diff : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (vectorFieldActionSmooth I M Y f : M → ℝ) x₀ :=
    (vectorFieldActionSmooth I M Y f).contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  have hXf_diff : MDifferentiableAt I 𝓘(ℝ, ℝ)
      (vectorFieldActionSmooth I M X f : M → ℝ) x₀ :=
    (vectorFieldActionSmooth I M X f).contMDiff.contMDiffAt.mdifferentiableAt (by simp)
  suffices hsuff : fderivWithin ℝ g s y₀ (VectorField.lieBracketWithin ℝ V W s y₀) =
    fderivWithin ℝ (↑(vectorFieldActionSmooth I M Y f) ∘ ↑φ.symm) s y₀
        (tangentSpaceModelContinuousLinearEquiv (I := I) x₀ (X x₀)) -
    fderivWithin ℝ (↑(vectorFieldActionSmooth I M X f) ∘ ↑φ.symm) s y₀
        (tangentSpaceModelContinuousLinearEquiv (I := I) x₀ (Y x₀)) by
    rw [mvfderiv_eq _ hYf_diff, mvfderiv_eq _ hXf_diff]
    exact hsuff
  have hmfderiv_chain : ∀ z ∈ φ.source,
      mfderiv I 𝓘(ℝ, ℝ) (f : M → ℝ) z =
        (fderivWithin ℝ g s (φ z)).comp (mfderiv I 𝓘(ℝ, E) φ z) := by
    intro z hz
    have hφ_open : IsOpen φ.source := isOpen_extChartAt_source x₀
    have hz_chart : z ∈ (chartAt H x₀).source := by
      rwa [extChartAt_source (I := I)] at hz
    have hφz_tgt : φ z ∈ φ.target := φ.map_source hz
    have hf_eq : (f : M → ℝ) =ᶠ[𝓝 z] g ∘ φ := by
      filter_upwards [hφ_open.mem_nhds hz] with w hw
      simp only [Function.comp_def, g, φ.left_inv hw]
    rw [hf_eq.mfderiv_eq]
    have hφ_diff : MDifferentiableAt I 𝓘(ℝ, E) φ z :=
      mdifferentiableAt_extChartAt hz_chart
    have hφ_diffWithin : MDifferentiableWithinAt I 𝓘(ℝ, E) φ φ.source z :=
      hφ_diff.mdifferentiableWithinAt
    have hg_diffWithin : DifferentiableWithinAt ℝ g s (φ z) := by
      have hf_at_z := f.contMDiff.contMDiffAt (x := z)
      have hφsymm : ContMDiffWithinAt 𝓘(ℝ, E) I ∞ φ.symm s (φ z) :=
        contMDiffWithinAt_extChartAt_symm_range x₀ hφz_tgt
      have hg_cmd : ContMDiffWithinAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g s (φ z) := by
        have h_eq : φ.symm (φ z) = z := φ.left_inv hz
        exact hf_at_z.comp_contMDiffWithinAt_of_eq hφsymm h_eq
      exact (contMDiffWithinAt_iff_contDiffWithinAt.mp hg_cmd).differentiableWithinAt
        (by simp : (∞ : WithTop ℕ∞) ≠ 0)
    have hg_mdiffWithin : MDifferentiableWithinAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) g s (φ z) :=
      mdifferentiableWithinAt_iff_differentiableWithinAt.mpr hg_diffWithin
    have h_maps : φ.source ⊆ φ ⁻¹' s := fun w hw =>
      extChartAt_target_subset_range x₀ (φ.map_source hw)
    have hUniq : UniqueMDiffWithinAt I φ.source z :=
      hφ_open.uniqueMDiffWithinAt hz
    have hchain := mfderivWithin_comp z hg_mdiffWithin hφ_diffWithin h_maps hUniq
    rw [mfderivWithin_eq_mfderiv hUniq hφ_diff] at hchain
    have hgφ_diff : MDifferentiableAt I 𝓘(ℝ, ℝ) (g ∘ φ) z := by
      have hf_mdiff : MDifferentiableAt I 𝓘(ℝ, ℝ) (f : M → ℝ) z :=
        f.contMDiff.contMDiffAt.mdifferentiableAt (by simp)
      exact hf_eq.mdifferentiableAt_iff.mp hf_mdiff
    rw [mfderivWithin_eq_mfderiv hUniq hgφ_diff] at hchain
    rw [mfderivWithin_eq_fderivWithin] at hchain
    exact hchain
  have mvfderiv_fderivWithin_chain : ∀ z ∈ φ.source,
      mvfderiv (I := I) (f : M → ℝ) z =
        (fderivWithin ℝ g s (φ z)).comp (mvfderiv (I := I) φ z) := by
    intro z hz
    ext v
    unfold mvfderiv
    rw [hmfderiv_chain z hz]
    rfl
  have W'_eq : ∀ y ∈ φ.target,
      W' y = mfderiv I 𝓘(ℝ, E) φ (φ.symm y) (Y (φ.symm y)) := by
    intro y hy
    simp only [W', VectorField.mpullbackWithin_apply]
    congr 1
    exact ContinuousLinearMap.inverse_eq
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := I) hy)
      (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) hy)
  have V'_eq : ∀ y ∈ φ.target,
      V' y = mfderiv I 𝓘(ℝ, E) φ (φ.symm y) (X (φ.symm y)) := by
    intro y hy
    change (mfderivWithin 𝓘(ℝ, E) I φ.symm s y).inverse (X (φ.symm y)) =
      mfderiv I 𝓘(ℝ, E) φ (φ.symm y) (X (φ.symm y))
    congr 1
    exact ContinuousLinearMap.inverse_eq
      (mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt (I := I) hy)
      (mfderiv_extChartAt_comp_mfderivWithin_extChartAt_symm (I := I) hy)
  have W_eq : ∀ y ∈ φ.target,
      W y = mvfderiv (I := I) φ (φ.symm y) (Y (φ.symm y)) := by
    intro y hy
    simp only [W]
    rw [W'_eq y hy]
    unfold mvfderiv
    rw [φ.right_inv hy]
    rfl
  have V_eq : ∀ y ∈ φ.target,
      V y = mvfderiv (I := I) φ (φ.symm y) (X (φ.symm y)) := by
    intro y hy
    simp only [V]
    rw [V'_eq y hy]
    unfold mvfderiv
    rw [φ.right_inv hy]
    rfl
  have hYf_eq : (↑(vectorFieldActionSmooth I M Y f) ∘ ↑φ.symm) =ᶠ[𝓝[s] y₀]
      (fun y => fderivWithin ℝ g s y (W y)) := by
    filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem hmem_tgt] with y hy
    simp only [Function.comp_def, vectorFieldActionSmooth, ContMDiffMap.coeFn_mk,
      vectorFieldAction]
    have hy_src : φ.symm y ∈ φ.source := φ.map_target hy
    rw [mvfderiv_fderivWithin_chain (φ.symm y) hy_src,
      ContinuousLinearMap.comp_apply, φ.right_inv hy, ← W_eq y hy]
  have hXf_eq : (↑(vectorFieldActionSmooth I M X f) ∘ ↑φ.symm) =ᶠ[𝓝[s] y₀]
      (fun y => fderivWithin ℝ g s y (V y)) := by
    filter_upwards [extChartAt_target_mem_nhdsWithin_of_mem hmem_tgt] with y hy
    simp only [Function.comp_def, vectorFieldActionSmooth, ContMDiffMap.coeFn_mk,
      vectorFieldAction]
    have hy_src : φ.symm y ∈ φ.source := φ.map_target hy
    rw [mvfderiv_fderivWithin_chain (φ.symm y) hy_src,
      ContinuousLinearMap.comp_apply, φ.right_inv hy, ← V_eq y hy]
  rw [hYf_eq.fderivWithin_eq (hYf_eq.self_of_nhdsWithin hy₀s),
      hXf_eq.fderivWithin_eq (hXf_eq.self_of_nhdsWithin hy₀s)]
  rw [← hV_y₀, ← hW_y₀]
  exact VectorField.fderivWithin_apply_lieBracket hg_smooth
    (by rw [minSmoothness_of_isRCLikeNormedField]; norm_cast)
    huniq hy₀_closure hy₀s hW_diff hV_diff

omit [FiniteDimensional ℝ E] [SigmaCompactSpace M] [T2Space M] in
theorem embed_bracket_closed
    (X Y : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) :
    ∃ Z : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯,
      embedLinearMap I M Z = ⁅embedLinearMap I M X, embedLinearMap I M Y⁆ := by
  refine ⟨mlieBracketSection I M X Y, ?_⟩
  apply Derivation.ext; intro f
  rw [Derivation.commutator_apply]
  exact embedDeriv_mlieBracket I M X Y f

end Embedding

end

end DifferentialGeometry.Geometry.Connection.Realization
