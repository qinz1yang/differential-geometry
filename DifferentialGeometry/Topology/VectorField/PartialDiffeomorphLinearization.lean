import DifferentialGeometry.Topology.VectorField.DiffeomorphLinearization
import Mathlib.Geometry.Manifold.LocalDiffeomorph

open Bundle Set
open scoped Manifold ContDiff Topology
set_option autoImplicit false
noncomputable section
namespace Poincare.VectorField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]


theorem contMDiffAt_tangentMap {f : M → N} {m n : ℕ∞ω} {p : TangentBundle I M}
    (hf : ContMDiffAt I J n f p.proj) (hmn : m + 1 ≤ n) :
    ContMDiffAt I.tangent J.tangent m (tangentMap I J f) p := by
  let b₁ : TangentBundle I M → M := fun q => q.proj
  let b₂ : TangentBundle I M → N := f ∘ b₁
  let v : ∀ q : TangentBundle I M, TangentSpace I (b₁ q) := fun q => q.2
  let φ : ∀ q : TangentBundle I M, TangentSpace I (b₁ q) →L[𝕜] TangentSpace J (b₂ q) :=
    fun q => mfderiv I J f (b₁ q)
  have hb₂ : ContMDiffAt I.tangent J m b₂ p :=
    (hf.of_le (le_self_add.trans hmn)).comp p (contMDiffAt_proj (TangentSpace I))
  have hφ : ContMDiffAt I.tangent
      𝓘(𝕜, E →L[𝕜] F) m
      (fun q => ContinuousLinearMap.inCoordinates E (TangentSpace I) F (TangentSpace J)
        (b₁ p) (b₁ q) (b₂ p) (b₂ q) (φ q)) p :=
    (hf.mfderiv_const hmn).comp p (contMDiffAt_proj (TangentSpace I))
  exact ContMDiffAt.clm_apply_of_inCoordinates hφ
    (show ContMDiffAt I.tangent I.tangent m (fun q => (⟨b₁ q,v q⟩ : TangentBundle I M)) p from
      contMDiffAt_id) hb₂

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

private theorem mfderiv_tangentMap_verticalLift_local {f : M → N} {x : M} (hf : ContMDiffAt I J 2 f x) (v : TangentSpace I x) :
    mfderiv I.tangent J.tangent (tangentMap I J f)
      (zeroSection E (TangentSpace I) x) (verticalLift x v) =
      verticalLift (f x) (mfderiv I J f x v) := by
  have hTf (w : TangentSpace I x) : MDifferentiableAt I.tangent J.tangent
      (tangentMap I J f) (⟨x, w⟩ : TangentBundle I M) :=
    (contMDiffAt_tangentMap (p := ⟨x, w⟩) hf (m := 1) le_rfl).mdifferentiableAt one_ne_zero
  have heq : (tangentMap I J f ∘ (fun t : 𝕜 => (⟨x, t • v⟩ : TangentBundle I M))) =
      (fun t : 𝕜 => (⟨f x, t • mfderiv I J f x v⟩ : TangentBundle J N)) := by
    funext t
    simp [tangentMap, map_smul]
  have hh := mfderiv_comp_apply (I := 𝓘(𝕜, 𝕜)) (I' := I.tangent)
    (I'' := J.tangent) (x := (0 : 𝕜))
    (hTf (0 • v)) (mdifferentiableAt_fiberCurve x v) (1 : 𝕜)
  rw [heq, ← verticalLift_eq_mfderiv_fiberCurve, ← verticalLift_eq_mfderiv_fiberCurve] at hh
  have hbase : (⟨x, (0 : 𝕜) • v⟩ : TangentBundle I M) = zeroSection E (TangentSpace I) x :=
    congrArg (fun w : TangentSpace I x => (⟨x, w⟩ : TangentBundle I M)) (zero_smul 𝕜 v)
  rw [hbase] at hh
  exact hh.symm

private theorem mfderiv_tangentMap_zeroSection_local {f : M → N} {x : M} (hf : ContMDiffAt I J 2 f x) (v : TangentSpace I x) :
    mfderiv I.tangent J.tangent (tangentMap I J f)
      (zeroSection E (TangentSpace I) x)
      (mfderiv I I.tangent (zeroSection E (TangentSpace I)) x v) =
    mfderiv J J.tangent (zeroSection F (TangentSpace J)) (f x) (mfderiv I J f x v) := by
  have hTf (w : TangentSpace I x) : MDifferentiableAt I.tangent J.tangent
      (tangentMap I J f) (⟨x, w⟩ : TangentBundle I M) :=
    (contMDiffAt_tangentMap (p := ⟨x, w⟩) hf (m := 1) le_rfl).mdifferentiableAt one_ne_zero
  have heq : tangentMap I J f ∘ zeroSection E (TangentSpace I) =
      zeroSection F (TangentSpace J) ∘ f := by
    funext y
    simp only [Function.comp_apply, tangentMap, zeroSection, TotalSpace.mk.injEq, heq_eq_eq, true_and]
    exact map_zero (mfderiv I J f y)
  have hh := mfderiv_comp_apply (I := I) (I' := I.tangent) (I'' := J.tangent)
    (x := x) (hTf 0) (Bundle.mdifferentiableAt_zeroSection 𝕜 (TangentSpace I)) v
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

theorem linearizationAtZero_intertwining_of_eventuallyEq {f : M → N}
    {V : ∀ x : M, TangentSpace I x} {W : ∀ y : N, TangentSpace J y} {x : M}
    (hf : ContMDiffAt I J 2 f x)
    (hV : MDifferentiableAt I I.tangent (fun y => (⟨y, V y⟩ : TangentBundle I M)) x)
    (hW : MDifferentiableAt J J.tangent (fun y => (⟨y, W y⟩ : TangentBundle J N)) (f x))
    (hVzero : V x = 0) (hWzero : W (f x) = 0)
    (hrelated : tangentMap I J f ∘ (fun y => (⟨y, V y⟩ : TangentBundle I M)) =ᶠ[𝓝 x]
      (fun y => (⟨y, W y⟩ : TangentBundle J N)) ∘ f) :
    mfderiv I J f x ∘L linearizationAtZero hV hVzero =
      linearizationAtZero hW hWzero ∘L mfderiv I J f x := by
  have hTf : MDifferentiableAt I.tangent J.tangent
      (tangentMap I J f) (⟨x, V x⟩ : TangentBundle I M) :=
    (contMDiffAt_tangentMap (p := ⟨x, V x⟩) hf (m := 1) le_rfl).mdifferentiableAt one_ne_zero
  ext v
  have hh := mfderiv_comp_apply (I := I) (I' := I.tangent) (I'' := J.tangent)
    (x := x) hTf hV v
  erw [hrelated.mfderiv_eq, mfderiv_comp_apply _ hW (hf.mdifferentiableAt (by norm_num)),
    mfderiv_section_at_zero hW hWzero,
    mfderiv_section_at_zero hV hVzero] at hh
  have hbase : (⟨x, V x⟩ : TangentBundle I M) = zeroSection E (TangentSpace I) x :=
    congrArg (fun w : TangentSpace I x => (⟨x, w⟩ : TangentBundle I M)) hVzero
  rw [hbase, map_add, mfderiv_tangentMap_zeroSection_local hf,
    mfderiv_tangentMap_verticalLift_local hf] at hh
  rw [mfderiv_zeroSection_apply] at hh
  have hh' := congrArg (fun w : TangentSpace J.tangent
    (zeroSection F (TangentSpace J) (f x)) => w.2) hh
  change (0 : TangentSpace J (f x)) + linearizationAtZero hW hWzero (mfderiv I J f x v) =
    (0 : TangentSpace J (f x)) + mfderiv I J f x (linearizationAtZero hV hVzero v) at hh'
  rw [zero_add, zero_add] at hh'
  exact hh'.symm

omit [IsManifold I 1 M] [IsManifold J 1 N] in
private theorem mfderiv_partialDiffeomorph_inverse_identities {n : ℕ∞ω}
    (f : PartialDiffeomorph I J M N n) (hn : n ≠ 0) {x : M} (hx : x ∈ f.source) :
    (mfderiv J I f.symm (f x) ∘L mfderiv I J f x =
      ContinuousLinearMap.id 𝕜 (TangentSpace I x)) ∧
    (mfderiv I J f x ∘L mfderiv J I f.symm (f x) =
      ContinuousLinearMap.id 𝕜 (TangentSpace J (f x))) := by
  have hleft : mfderiv J I f.symm (f x) ∘L mfderiv I J f x =
      ContinuousLinearMap.id 𝕜 (TangentSpace I x) := by
    rw [← mfderiv_comp _ (f.symm.mdifferentiableAt hn (f.map_source hx))
      (f.mdifferentiableAt hn hx)]
    have heq : (f.symm ∘ f : M → M) =ᶠ[𝓝 x] id :=
      Filter.eventuallyEq_of_mem (f.open_source.mem_nhds hx) (fun y hy => f.left_inv hy)
    erw [heq.mfderiv_eq]
    exact mfderiv_id
  have hright : mfderiv I J f x ∘L mfderiv J I f.symm (f x) =
      ContinuousLinearMap.id 𝕜 (TangentSpace J (f x)) := by
    have hh := mfderiv_comp (f x) (f.mdifferentiableAt hn (f.map_target (f.map_source hx)))
      (f.symm.mdifferentiableAt hn (f.map_source hx))
    have heq : (f ∘ f.symm : N → N) =ᶠ[𝓝 (f x)] id :=
      Filter.eventuallyEq_of_mem (f.open_target.mem_nhds (f.map_source hx))
        (fun y hy => f.right_inv hy)
    erw [heq.mfderiv_eq, mfderiv_id, f.left_inv hx] at hh
    exact hh.symm
  exact ⟨hleft, hright⟩

omit [IsManifold I 1 M] [IsManifold J 1 N] in
theorem isInvertible_mfderiv_partialDiffeomorph {n : ℕ∞ω}
    (f : PartialDiffeomorph I J M N n) (hn : n ≠ 0) {x : M} (hx : x ∈ f.source) :
    (mfderiv I J f x).IsInvertible := by
  obtain ⟨hleft, hright⟩ := mfderiv_partialDiffeomorph_inverse_identities f hn hx
  exact ContinuousLinearMap.IsInvertible.of_inverse hright hleft

omit [IsManifold I 1 M] [IsManifold J 1 N] in
theorem inverse_mfderiv_partialDiffeomorph {n : ℕ∞ω}
    (f : PartialDiffeomorph I J M N n) (hn : n ≠ 0) {x : M} (hx : x ∈ f.source) :
    (mfderiv I J f x).inverse = mfderiv J I f.symm (f x) := by
  obtain ⟨hleft, hright⟩ := mfderiv_partialDiffeomorph_inverse_identities f hn hx
  exact ContinuousLinearMap.inverse_eq hright hleft

omit [IsManifold I 1 M] [IsManifold J 1 N] in
theorem mpullback_partialDiffeomorph_graph {n : ℕ∞ω}
    (f : PartialDiffeomorph I J M N n) (hn : n ≠ 0)
    (V : ∀ y : N, TangentSpace J y) {x : M} (hx : x ∈ f.source) :
    (fun y => (⟨y, _root_.VectorField.mpullback I J f V y⟩ : TangentBundle I M)) =ᶠ[𝓝 x]
      tangentMap J I f.symm ∘ (fun y => (⟨y, V y⟩ : TangentBundle J N)) ∘ f := by
  filter_upwards [f.open_source.mem_nhds hx] with y hy
  simp only [Function.comp_apply, tangentMap, _root_.VectorField.mpullback,
    inverse_mfderiv_partialDiffeomorph f hn hy]
  apply TotalSpace.ext
  · exact (f.left_inv hy).symm
  · rfl

theorem mdifferentiableAt_mpullback_partialDiffeomorph {n : ℕ∞ω}
    (f : PartialDiffeomorph I J M N n) (hmn : 2 ≤ n)
    {V : ∀ y : N, TangentSpace J y} {x : M} (hx : x ∈ f.source)
    (hV : MDifferentiableAt J J.tangent (fun y => (⟨y, V y⟩ : TangentBundle J N)) (f x)) :
    MDifferentiableAt I I.tangent
      (fun y => (⟨y, _root_.VectorField.mpullback I J f V y⟩ : TangentBundle I M)) x := by
  have hn : n ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hmn)
  have hg : ContMDiffAt J I 2 f.symm (f x) :=
    ((f.symm.contMDiffOn).contMDiffAt (f.open_target.mem_nhds (f.map_source hx))).of_le hmn
  have hTg : MDifferentiableAt J.tangent I.tangent (tangentMap J I f.symm)
      (⟨f x, V (f x)⟩ : TangentBundle J N) :=
    (contMDiffAt_tangentMap (p := ⟨f x, V (f x)⟩) hg (m := 1) le_rfl).mdifferentiableAt one_ne_zero
  exact (hTg.comp x (hV.comp x (f.mdifferentiableAt hn hx))).congr_of_eventuallyEq
    (mpullback_partialDiffeomorph_graph f hn V hx)

omit [IsManifold I 1 M] [IsManifold J 1 N] in
theorem tangentMap_mpullback_partialDiffeomorph {n : ℕ∞ω}
    (f : PartialDiffeomorph I J M N n) (hn : n ≠ 0)
    (V : ∀ y : N, TangentSpace J y) {x : M} (hx : x ∈ f.source) :
    tangentMap I J f ∘
      (fun y => (⟨y, _root_.VectorField.mpullback I J f V y⟩ : TangentBundle I M)) =ᶠ[𝓝 x]
      (fun y => (⟨y, V y⟩ : TangentBundle J N)) ∘ f := by
  filter_upwards [f.open_source.mem_nhds hx] with y hy
  simp only [Function.comp_apply, tangentMap, _root_.VectorField.mpullback,
    TotalSpace.mk.injEq, heq_eq_eq, true_and]
  exact (isInvertible_mfderiv_partialDiffeomorph f hn hy).self_apply_inverse (V (f y))

omit [IsManifold I 1 M] [IsManifold J 1 N] in
theorem mpullback_partialDiffeomorph_eq_zero_iff {n : ℕ∞ω}
    (f : PartialDiffeomorph I J M N n) (hn : n ≠ 0)
    (V : ∀ y : N, TangentSpace J y) {x : M} (hx : x ∈ f.source) :
    _root_.VectorField.mpullback I J f V x = 0 ↔ V (f x) = 0 := by
  change (mfderiv I J f x).inverse (V (f x)) = 0 ↔ V (f x) = 0
  constructor
  · intro hp
    have hh := (isInvertible_mfderiv_partialDiffeomorph f hn hx).self_apply_inverse (V (f x))
    rw [hp, map_zero] at hh
    exact hh.symm
  · intro hz
    rw [hz]
    exact map_zero _

theorem linearizationAtZero_mpullback_partialDiffeomorph {n : ℕ∞ω}
    (f : PartialDiffeomorph I J M N n) (hmn : 2 ≤ n)
    {V : ∀ y : N, TangentSpace J y} {x : M} (hx : x ∈ f.source)
    (hV : MDifferentiableAt J J.tangent (fun y => (⟨y, V y⟩ : TangentBundle J N)) (f x))
    (hzero : V (f x) = 0) :
    linearizationAtZero (mdifferentiableAt_mpullback_partialDiffeomorph f hmn hx hV)
      ((mpullback_partialDiffeomorph_eq_zero_iff f
        (ne_of_gt (lt_of_lt_of_le (by norm_num) hmn)) V hx).mpr hzero) =
    (mfderiv I J f x).inverse ∘L linearizationAtZero hV hzero ∘L mfderiv I J f x := by
  have hn : n ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hmn)
  have hP := mdifferentiableAt_mpullback_partialDiffeomorph f hmn hx hV
  have hPzero := (mpullback_partialDiffeomorph_eq_zero_iff f hn V hx).mpr hzero
  have hf : ContMDiffAt I J 2 f x :=
    (f.contMDiffOn.contMDiffAt (f.open_source.mem_nhds hx)).of_le hmn
  have hh := linearizationAtZero_intertwining_of_eventuallyEq hf hP hV hPzero hzero
    (tangentMap_mpullback_partialDiffeomorph f hn V hx)
  ext v
  have hh' := congrArg (fun A : TangentSpace I x →L[𝕜] TangentSpace J (f x) =>
    (mfderiv I J f x).inverse (A v)) hh
  change (mfderiv I J f x).inverse (mfderiv I J f x (linearizationAtZero hP hPzero v)) =
    (mfderiv I J f x).inverse (linearizationAtZero hV hzero (mfderiv I J f x v)) at hh'
  rw [(isInvertible_mfderiv_partialDiffeomorph f hn hx).inverse_apply_self] at hh'
  exact hh'

theorem det_linearizationAtZero_mpullback_partialDiffeomorph {n : ℕ∞ω}
    (f : PartialDiffeomorph I J M N n) (hmn : 2 ≤ n)
    {V : ∀ y : N, TangentSpace J y} {x : M} (hx : x ∈ f.source)
    (hV : MDifferentiableAt J J.tangent (fun y => (⟨y, V y⟩ : TangentBundle J N)) (f x))
    (hzero : V (f x) = 0) :
    LinearMap.det (linearizationAtZero
      (mdifferentiableAt_mpullback_partialDiffeomorph f hmn hx hV)
      ((mpullback_partialDiffeomorph_eq_zero_iff f
        (ne_of_gt (lt_of_lt_of_le (by norm_num) hmn)) V hx).mpr hzero)).toLinearMap =
    LinearMap.det (linearizationAtZero hV hzero).toLinearMap := by
  rw [linearizationAtZero_mpullback_partialDiffeomorph f hmn hx hV hzero]
  obtain ⟨e, he⟩ := isInvertible_mfderiv_partialDiffeomorph f
    (ne_of_gt (lt_of_lt_of_le (by norm_num) hmn)) hx
  rw [← he, ContinuousLinearMap.inverse_equiv]
  exact LinearMap.det_conj (linearizationAtZero hV hzero).toLinearMap e.symm.toLinearEquiv

end Poincare.VectorField
