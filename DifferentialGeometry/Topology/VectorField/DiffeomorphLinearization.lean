import DifferentialGeometry.Topology.VectorField.VerticalLinearization
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.VectorField.Pullback

open Bundle Set
open scoped Manifold ContDiff Topology
set_option autoImplicit false
noncomputable section
namespace DifferentialGeometry.VectorField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 2 N]

private theorem mdifferentiableAt_fiberCurve (x : M) (v : TangentSpace I x) :
    MDifferentiableAt 𝓘(𝕜, 𝕜) I.tangent
      (fun t : 𝕜 => (⟨x, t • v⟩ : TangentBundle I M)) 0 := by
  rw [mdifferentiableAt_totalSpace]
  refine ⟨mdifferentiableAt_const, ?_⟩
  have heq : (fun t : 𝕜 =>
      (trivializationAt E (TangentSpace I) x (⟨x, t • v⟩ : TangentBundle I M)).2) =
      (fun t : 𝕜 => t • v) := by
    funext t
    change tangentCoordChange I x x x (t • v) = t • v
    exact tangentCoordChange_self (mem_extChartAt_source x)
  rw [heq]
  exact mdifferentiableAt_id.smul mdifferentiableAt_const

theorem mfderiv_tangentMap_verticalLift {f : M → N} (hf : ContMDiff I J 2 f) (x : M) (v : TangentSpace I x) :
    mfderiv I.tangent J.tangent (tangentMap I J f)
      (zeroSection E (TangentSpace I) x) (verticalLift x v) =
      verticalLift (f x) (mfderiv I J f x v) := by
  have hTf : MDifferentiable I.tangent J.tangent (tangentMap I J f) :=
    (hf.contMDiff_tangentMap (m := 1) (by norm_num)).mdifferentiable one_ne_zero
  have heq : (tangentMap I J f ∘ (fun t : 𝕜 => (⟨x, t • v⟩ : TangentBundle I M))) =
      (fun t : 𝕜 => (⟨f x, t • mfderiv I J f x v⟩ : TangentBundle J N)) := by
    funext t
    simp [tangentMap, map_smul]
  have hh := mfderiv_comp_apply (I := 𝓘(𝕜, 𝕜)) (I' := I.tangent)
    (I'' := J.tangent) (x := (0 : 𝕜))
    (hTf (⟨x, 0 • v⟩ : TangentBundle I M)) (mdifferentiableAt_fiberCurve x v) (1 : 𝕜)
  rw [heq, ← verticalLift_eq_mfderiv_fiberCurve, ← verticalLift_eq_mfderiv_fiberCurve] at hh
  have hbase : (⟨x, (0 : 𝕜) • v⟩ : TangentBundle I M) = zeroSection E (TangentSpace I) x :=
    congrArg (fun w : TangentSpace I x => (⟨x, w⟩ : TangentBundle I M)) (zero_smul 𝕜 v)
  rw [hbase] at hh
  exact hh.symm

theorem mfderiv_tangentMap_zeroSection {f : M → N} (hf : ContMDiff I J 2 f) (x : M) (v : TangentSpace I x) :
    mfderiv I.tangent J.tangent (tangentMap I J f)
      (zeroSection E (TangentSpace I) x)
      (mfderiv I I.tangent (zeroSection E (TangentSpace I)) x v) =
    mfderiv J J.tangent (zeroSection F (TangentSpace J)) (f x) (mfderiv I J f x v) := by
  have hTf : MDifferentiable I.tangent J.tangent (tangentMap I J f) :=
    (hf.contMDiff_tangentMap (m := 1) (by norm_num)).mdifferentiable one_ne_zero
  have heq : tangentMap I J f ∘ zeroSection E (TangentSpace I) =
      zeroSection F (TangentSpace J) ∘ f := by
    funext y
    simp only [Function.comp_apply, tangentMap, zeroSection, TotalSpace.mk.injEq, heq_eq_eq, true_and]
    exact map_zero (mfderiv I J f y)
  have hh := mfderiv_comp_apply (I := I) (I' := I.tangent) (I'' := J.tangent)
    (x := x) (hTf _) (Bundle.mdifferentiableAt_zeroSection 𝕜 (TangentSpace I)) v
  rw [heq, mfderiv_comp_apply _ (Bundle.mdifferentiableAt_zeroSection 𝕜 (TangentSpace J))
    (hf.mdifferentiableAt (by norm_num))] at hh
  exact hh.symm

private theorem mfderiv_section_at_zero
    {V : ∀ x : M, TangentSpace I x} {x : M}
    (hV : MDifferentiableAt I I.tangent (fun y => (⟨y, V y⟩ : TangentBundle I M)) x)
    (hzero : V x = 0) (v : TangentSpace I x) :
    mfderiv I I.tangent (fun y => (⟨y, V y⟩ : TangentBundle I M)) x v =
      mfderiv I I.tangent (zeroSection E (TangentSpace I)) x v +
        verticalLift x (linearizationAtZero hV hzero v) :=
  congrArg (fun p : TangentBundle I.tangent (TangentBundle I M) => p.2)
    (tangentMap_section_eq_linearizationAtZero hV hzero v)

theorem linearizationAtZero_intertwining {f : M → N} (hf : ContMDiff I J 2 f)
    {V : ∀ x : M, TangentSpace I x} {W : ∀ y : N, TangentSpace J y} {x : M}
    (hV : MDifferentiableAt I I.tangent (fun y => (⟨y, V y⟩ : TangentBundle I M)) x)
    (hW : MDifferentiableAt J J.tangent (fun y => (⟨y, W y⟩ : TangentBundle J N)) (f x))
    (hVzero : V x = 0) (hWzero : W (f x) = 0)
    (hrelated : tangentMap I J f ∘ (fun y => (⟨y, V y⟩ : TangentBundle I M)) =
      (fun y => (⟨y, W y⟩ : TangentBundle J N)) ∘ f) :
    mfderiv I J f x ∘L linearizationAtZero hV hVzero =
      linearizationAtZero hW hWzero ∘L mfderiv I J f x := by
  have hTf : MDifferentiable I.tangent J.tangent (tangentMap I J f) :=
    (hf.contMDiff_tangentMap (m := 1) (by norm_num)).mdifferentiable one_ne_zero
  ext v
  have hh := mfderiv_comp_apply (I := I) (I' := I.tangent) (I'' := J.tangent)
    (x := x) (hTf _) hV v
  rw [hrelated, mfderiv_comp_apply _ hW (hf.mdifferentiableAt (by norm_num)),
    mfderiv_section_at_zero hW hWzero,
    mfderiv_section_at_zero hV hVzero] at hh
  have hbase : (⟨x, V x⟩ : TangentBundle I M) = zeroSection E (TangentSpace I) x :=
    congrArg (fun w : TangentSpace I x => (⟨x, w⟩ : TangentBundle I M)) hVzero
  rw [hbase, map_add, mfderiv_tangentMap_zeroSection hf,
    mfderiv_tangentMap_verticalLift hf] at hh
  rw [mfderiv_zeroSection_apply] at hh
  have hh' := congrArg (fun w : TangentSpace J.tangent
    (zeroSection F (TangentSpace J) (f x)) => w.2) hh
  change (0 : TangentSpace J (f x)) + linearizationAtZero hW hWzero (mfderiv I J f x v) =
    (0 : TangentSpace J (f x)) + mfderiv I J f x (linearizationAtZero hV hVzero v) at hh'
  rw [zero_add, zero_add] at hh'
  exact hh'.symm

omit [IsManifold I 2 M] [IsManifold J 2 N] in
private theorem mfderiv_diffeomorph_inverse_identities {n : ℕ∞ω}
    (f : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) (x : M) :
    (mfderiv J I f.symm (f x) ∘L mfderiv I J f x =
      ContinuousLinearMap.id 𝕜 (TangentSpace I x)) ∧
    (mfderiv I J f x ∘L mfderiv J I f.symm (f x) =
      ContinuousLinearMap.id 𝕜 (TangentSpace J (f x))) := by
  have hleft : mfderiv J I f.symm (f x) ∘L mfderiv I J f x =
      ContinuousLinearMap.id 𝕜 (TangentSpace I x) := by
    rw [← mfderiv_comp _ (f.symm.mdifferentiable hn _) (f.mdifferentiable hn _)]
    have hh : (f.symm ∘ f : M → M) = id := by ext y; exact f.symm_apply_apply y
    rw [hh]
    exact mfderiv_id
  have hright : mfderiv I J f x ∘L mfderiv J I f.symm (f x) =
      ContinuousLinearMap.id 𝕜 (TangentSpace J (f x)) := by
    have hh := mfderiv_comp (f x) (f.mdifferentiable hn _) (f.symm.mdifferentiable hn _)
    have heq : (f ∘ f.symm : N → N) = id := by ext y; exact f.apply_symm_apply y
    rw [heq, mfderiv_id, f.symm_apply_apply] at hh
    exact hh.symm
  exact ⟨hleft, hright⟩

omit [IsManifold I 2 M] [IsManifold J 2 N] in
theorem isInvertible_mfderiv_diffeomorph {n : ℕ∞ω}
    (f : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) (x : M) :
    (mfderiv I J f x).IsInvertible := by
  obtain ⟨hleft, hright⟩ := mfderiv_diffeomorph_inverse_identities f hn x
  exact ContinuousLinearMap.IsInvertible.of_inverse hright hleft

omit [IsManifold I 2 M] [IsManifold J 2 N] in
theorem inverse_mfderiv_diffeomorph {n : ℕ∞ω}
    (f : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) (x : M) :
    (mfderiv I J f x).inverse = mfderiv J I f.symm (f x) := by
  obtain ⟨hleft, hright⟩ := mfderiv_diffeomorph_inverse_identities f hn x
  exact ContinuousLinearMap.inverse_eq hright hleft

omit [IsManifold I 2 M] [IsManifold J 2 N] in
theorem mpullback_diffeomorph_graph {n : ℕ∞ω}
    (f : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) (V : ∀ y : N, TangentSpace J y) :
    (fun x => (⟨x, _root_.VectorField.mpullback I J f V x⟩ : TangentBundle I M)) =
      tangentMap J I f.symm ∘ (fun y => (⟨y, V y⟩ : TangentBundle J N)) ∘ f := by
  funext x
  simp only [Function.comp_apply, tangentMap, _root_.VectorField.mpullback,
    inverse_mfderiv_diffeomorph f hn x]
  apply TotalSpace.ext
  · exact (f.symm_apply_apply x).symm
  · rfl

theorem mdifferentiableAt_mpullback_diffeomorph {n : ℕ∞ω}
    (f : M ≃ₘ^n⟮I, J⟯ N) (hmn : 2 ≤ n)
    {V : ∀ y : N, TangentSpace J y} {x : M}
    (hV : MDifferentiableAt J J.tangent (fun y => (⟨y, V y⟩ : TangentBundle J N)) (f x)) :
    MDifferentiableAt I I.tangent
      (fun y => (⟨y, _root_.VectorField.mpullback I J f V y⟩ : TangentBundle I M)) x := by
  rw [mpullback_diffeomorph_graph f (ne_of_gt (lt_of_lt_of_le (by norm_num) hmn))]
  exact (((f.symm.contMDiff.of_le hmn).contMDiff_tangentMap (m := 1) (by norm_num)).mdifferentiableAt
    one_ne_zero).comp x (hV.comp x (f.mdifferentiable (ne_of_gt (lt_of_lt_of_le (by norm_num) hmn)) x))

omit [IsManifold I 2 M] [IsManifold J 2 N] in
theorem tangentMap_mpullback_diffeomorph {n : ℕ∞ω}
    (f : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) (V : ∀ y : N, TangentSpace J y) :
    tangentMap I J f ∘
      (fun x => (⟨x, _root_.VectorField.mpullback I J f V x⟩ : TangentBundle I M)) =
      (fun y => (⟨y, V y⟩ : TangentBundle J N)) ∘ f := by
  funext x
  simp only [Function.comp_apply, tangentMap, _root_.VectorField.mpullback,
    TotalSpace.mk.injEq, heq_eq_eq, true_and]
  exact (isInvertible_mfderiv_diffeomorph f hn x).self_apply_inverse (V (f x))

omit [IsManifold I 2 M] [IsManifold J 2 N] in
theorem mpullback_diffeomorph_eq_zero_iff {n : ℕ∞ω}
    (f : M ≃ₘ^n⟮I, J⟯ N) (hn : n ≠ 0) (V : ∀ y : N, TangentSpace J y) (x : M) :
    _root_.VectorField.mpullback I J f V x = 0 ↔ V (f x) = 0 := by
  change (mfderiv I J f x).inverse (V (f x)) = 0 ↔ V (f x) = 0
  constructor
  · intro hp
    have hh := (isInvertible_mfderiv_diffeomorph f hn x).self_apply_inverse (V (f x))
    rw [hp, map_zero] at hh
    exact hh.symm
  · intro hz
    rw [hz]
    exact map_zero _

theorem linearizationAtZero_mpullback_diffeomorph {n : ℕ∞ω}
    (f : M ≃ₘ^n⟮I, J⟯ N) (hmn : 2 ≤ n)
    {V : ∀ y : N, TangentSpace J y} {x : M}
    (hV : MDifferentiableAt J J.tangent (fun y => (⟨y, V y⟩ : TangentBundle J N)) (f x))
    (hzero : V (f x) = 0) :
    linearizationAtZero (mdifferentiableAt_mpullback_diffeomorph f hmn hV)
      ((mpullback_diffeomorph_eq_zero_iff f (ne_of_gt (lt_of_lt_of_le (by norm_num) hmn)) V x).mpr hzero) =
    (mfderiv I J f x).inverse ∘L linearizationAtZero hV hzero ∘L mfderiv I J f x := by
  have hP := mdifferentiableAt_mpullback_diffeomorph f hmn hV
  have hPzero := (mpullback_diffeomorph_eq_zero_iff f (ne_of_gt (lt_of_lt_of_le (by norm_num) hmn)) V x).mpr hzero
  have hh := linearizationAtZero_intertwining (f.contMDiff.of_le hmn) hP hV hPzero hzero
    (tangentMap_mpullback_diffeomorph f (ne_of_gt (lt_of_lt_of_le (by norm_num) hmn)) V)
  ext v
  have hh' := congrArg (fun A : TangentSpace I x →L[𝕜] TangentSpace J (f x) =>
    (mfderiv I J f x).inverse (A v)) hh
  change (mfderiv I J f x).inverse (mfderiv I J f x (linearizationAtZero hP hPzero v)) =
    (mfderiv I J f x).inverse (linearizationAtZero hV hzero (mfderiv I J f x v)) at hh'
  rw [(isInvertible_mfderiv_diffeomorph f (ne_of_gt (lt_of_lt_of_le (by norm_num) hmn)) x).inverse_apply_self] at hh'
  exact hh'

theorem det_linearizationAtZero_mpullback_diffeomorph {n : ℕ∞ω}
    (f : M ≃ₘ^n⟮I, J⟯ N) (hmn : 2 ≤ n)
    {V : ∀ y : N, TangentSpace J y} {x : M}
    (hV : MDifferentiableAt J J.tangent (fun y => (⟨y, V y⟩ : TangentBundle J N)) (f x))
    (hzero : V (f x) = 0) :
    LinearMap.det (linearizationAtZero (mdifferentiableAt_mpullback_diffeomorph f hmn hV)
      ((mpullback_diffeomorph_eq_zero_iff f (ne_of_gt (lt_of_lt_of_le (by norm_num) hmn)) V x).mpr hzero)).toLinearMap =
    LinearMap.det (linearizationAtZero hV hzero).toLinearMap := by
  rw [linearizationAtZero_mpullback_diffeomorph f hmn hV hzero]
  obtain ⟨e, he⟩ := isInvertible_mfderiv_diffeomorph f (ne_of_gt (lt_of_lt_of_le (by norm_num) hmn)) x
  rw [← he, ContinuousLinearMap.inverse_equiv]
  exact LinearMap.det_conj (linearizationAtZero hV hzero).toLinearMap e.symm.toLinearEquiv

end DifferentialGeometry.VectorField
