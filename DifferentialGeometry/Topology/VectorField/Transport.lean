import DifferentialGeometry.Topology.VectorField.PartialDiffeomorphLinearization

set_option autoImplicit false
open Bundle Set
open scoped Manifold ContDiff Topology
noncomputable section
namespace Poincare.VectorField

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners 𝕜 F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]

theorem contMDiffAt_mpullback_partialDiffeomorph
    [IsManifold I 1 M] [IsManifold J 1 N] {m n : ℕ∞ω}
    (f : PartialDiffeomorph I J M N n) (hmn : m + 1 ≤ n)
    {V : ∀ y : N, TangentSpace J y} {x : M} (hx : x ∈ f.source)
    (hV : ContMDiffAt J J.tangent m (fun y ↦ (⟨y, V y⟩ : TangentBundle J N)) (f x)) :
    ContMDiffAt I I.tangent m
      (fun y ↦ (⟨y, _root_.VectorField.mpullback I J f V y⟩ : TangentBundle I M)) x := by
  have hone : 1 ≤ m + 1 := le_add_of_nonneg_left zero_le
  have hn : n ≠ 0 := ne_of_gt (zero_lt_one.trans_le (hone.trans hmn))
  have hf := f.contMDiffOn.contMDiffAt (f.open_source.mem_nhds hx)
  have hg := f.symm.contMDiffOn.contMDiffAt (f.open_target.mem_nhds (f.map_source hx))
  have hTg := contMDiffAt_tangentMap (p := (⟨f x, V (f x)⟩ : TangentBundle J N)) hg hmn
  exact (hTg.comp x (hV.comp x (hf.of_le (le_self_add.trans hmn)))).congr_of_eventuallyEq
    (mpullback_partialDiffeomorph_graph f hn V hx)


theorem contMDiffOn_mpullback_partialDiffeomorph
    [IsManifold I 1 M] [IsManifold J 1 N] {m n : ℕ∞ω}
    (f : PartialDiffeomorph I J M N n) (hmn : m + 1 ≤ n)
    {V : ∀ y : N, TangentSpace J y}
    (hV : ContMDiffOn J J.tangent m (fun y ↦ (⟨y, V y⟩ : TangentBundle J N)) f.target) :
    ContMDiffOn I I.tangent m
      (fun y ↦ (⟨y, _root_.VectorField.mpullback I J f V y⟩ : TangentBundle I M)) f.source := by
  intro x hx
  exact (contMDiffAt_mpullback_partialDiffeomorph f hmn hx
    (hV.contMDiffAt (f.open_target.mem_nhds (f.map_source hx)))).contMDiffWithinAt

theorem mpullback_partialDiffeomorph_zeroSet_bijOn {n : ℕ∞ω}
    (f : PartialDiffeomorph I J M N n) (hn : n ≠ 0)
    (V : ∀ y : N, TangentSpace J y) :
    BijOn f {x | x ∈ f.source ∧ _root_.VectorField.mpullback I J f V x = 0}
      {y | y ∈ f.target ∧ V y = 0} := by
  refine ⟨?_, f.injOn.mono (fun _ h ↦ h.1), ?_⟩
  · rintro x ⟨hx, hz⟩
    exact ⟨f.map_source hx, (mpullback_partialDiffeomorph_eq_zero_iff f hn V hx).mp hz⟩
  · rintro y ⟨hy, hz⟩
    refine ⟨f.symm y, ⟨f.map_target hy, ?_⟩, f.right_inv hy⟩
    apply (mpullback_partialDiffeomorph_eq_zero_iff f hn V (f.map_target hy)).mpr
    change (V (f (f.symm y)) : F) = 0
    erw [f.right_inv hy]
    exact hz

theorem mpullback_partialDiffeomorph_isolated_iff {n : ℕ∞ω}
    (f : PartialDiffeomorph I J M N n) (hn : n ≠ 0)
    (V : ∀ y : N, TangentSpace J y) {x : M} (hx : x ∈ f.source) :
    (∀ᶠ y in 𝓝 x, _root_.VectorField.mpullback I J f V y = 0 → y = x) ↔
      ∀ᶠ z in 𝓝 (f x), V z = 0 → z = f x := by
  constructor
  · intro hiso
    filter_upwards [(f.toOpenPartialHomeomorph.tendsto_symm hx).eventually hiso,
      f.open_target.mem_nhds (f.map_source hx)] with z hz hzt
    intro hzV
    have hzP : _root_.VectorField.mpullback I J f V (f.symm z) = 0 := by
      apply (mpullback_partialDiffeomorph_eq_zero_iff f hn V (f.map_target hzt)).mpr
      change (V (f (f.symm z)) : F) = 0
      erw [f.right_inv hzt]
      exact hzV
    have hh := congrArg f (hz hzP)
    exact (f.right_inv hzt).symm.trans hh
  · intro hiso
    filter_upwards [(f.toOpenPartialHomeomorph.continuousAt hx).eventually hiso,
      f.open_source.mem_nhds hx] with y hy hys
    intro hz
    exact f.injOn hys hx
      (hy ((mpullback_partialDiffeomorph_eq_zero_iff f hn V hys).mp hz))


theorem mpullback_partialDiffeomorph_congr_germ {n : ℕ∞ω}
    (f : PartialDiffeomorph I J M N n)
    {V W : ∀ y : N, TangentSpace J y} {x : M} (hx : x ∈ f.source)
    (hVW : (fun y ↦ (⟨y, V y⟩ : TangentBundle J N)) =ᶠ[𝓝 (f x)]
      (fun y ↦ (⟨y, W y⟩ : TangentBundle J N))) :
    (fun y ↦ (⟨y, _root_.VectorField.mpullback I J f V y⟩ : TangentBundle I M)) =ᶠ[𝓝 x]
      (fun y ↦ (⟨y, _root_.VectorField.mpullback I J f W y⟩ : TangentBundle I M)) := by
  filter_upwards [(f.toOpenPartialHomeomorph.continuousAt hx).eventually hVW] with y hy
  have hvw := TotalSpace.mk_injective (f y) hy
  change V (f y) = W (f y) at hvw
  exact congrArg (fun v : TangentSpace J (f y) ↦
    (⟨y, (mfderiv I J f y).inverse v⟩ : TangentBundle I M)) hvw

end Poincare.VectorField
