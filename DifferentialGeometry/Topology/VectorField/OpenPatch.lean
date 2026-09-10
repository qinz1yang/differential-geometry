import DifferentialGeometry.Topology.VectorField.OpenSubtypePullback
import DifferentialGeometry.Topology.VectorField.Transport

set_option autoImplicit false
open Bundle Set
open scoped Manifold ContDiff Topology
noncomputable section
namespace Poincare.VectorField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]


def patchOnOpen (U : TopologicalSpace.Opens M) (V : ∀ x : M, TangentSpace I x)
    (W : ∀ x : U, TangentSpace I x) (x : M) : TangentSpace I x := by
  classical
  exact if hx : x ∈ U then W ⟨x, hx⟩ else V x


theorem patchOnOpen_of_mem (U : TopologicalSpace.Opens M)
    (V : ∀ x : M, TangentSpace I x) (W : ∀ x : U, TangentSpace I x)
    {x : M} (hx : x ∈ U) : patchOnOpen U V W x = W ⟨x, hx⟩ := dif_pos hx


theorem patchOnOpen_of_not_mem (U : TopologicalSpace.Opens M)
    (V : ∀ x : M, TangentSpace I x) (W : ∀ x : U, TangentSpace I x)
    {x : M} (hx : x ∉ U) : patchOnOpen U V W x = V x := dif_neg hx


theorem patchOnOpen_eq_self_off (U : TopologicalSpace.Opens M)
    (V : ∀ x : M, TangentSpace I x) (W : ∀ x : U, TangentSpace I x) {K : Set M}
    (hW : ∀ x : U, x.val ∉ K → W x = V x.val) {x : M} (hx : x ∉ K) :
    patchOnOpen U V W x = V x := by
  by_cases hxU : x ∈ U
  · exact (patchOnOpen_of_mem U V W hxU).trans (hW ⟨x, hxU⟩ hx)
  · exact patchOnOpen_of_not_mem U V W hxU


theorem patchOnOpen_eventuallyEq_self (U : TopologicalSpace.Opens M)
    (V : ∀ x : M, TangentSpace I x) (W : ∀ x : U, TangentSpace I x) {K : Set M}
    (hK : IsClosed K) (hW : ∀ x : U, x.val ∉ K → W x = V x.val)
    {x : M} (hx : x ∉ K) :
    (fun y ↦ (⟨y, patchOnOpen U V W y⟩ : TangentBundle I M)) =ᶠ[𝓝 x]
      (fun y ↦ (⟨y, V y⟩ : TangentBundle I M)) := by
  filter_upwards [hK.isOpen_compl.mem_nhds hx] with y hy
  exact congrArg (fun v : TangentSpace I y ↦ (⟨y, v⟩ : TangentBundle I M))
    (patchOnOpen_eq_self_off U V W hW hy)

theorem patchOnOpen_eventuallyEq_mpullback (U : TopologicalSpace.Opens M)
    (V : ∀ x : M, TangentSpace I x) (W : ∀ x : U, TangentSpace I x)
    {x : M} (hx : x ∈ U) :
    (fun y ↦ (⟨y, patchOnOpen U V W y⟩ : TangentBundle I M)) =ᶠ[𝓝 x]
      (fun y ↦ (⟨y, _root_.VectorField.mpullback I I
        (Poincare.Manifold.openSubtypePartialDiffeomorph I U ⟨⟨x, hx⟩⟩).symm W y⟩ :
          TangentBundle I M)) := by
  filter_upwards [U.isOpen.mem_nhds hx] with y hy
  exact congrArg (fun v : TangentSpace I y ↦ (⟨y, v⟩ : TangentBundle I M))
    ((patchOnOpen_of_mem U V W hy).trans
      (Poincare.Manifold.mpullback_openSubtype_symm I U ⟨⟨x, hx⟩⟩ W hy).symm)

theorem contMDiffAt_patchOnOpen_of_mem [IsManifold I 1 M]
    (U : TopologicalSpace.Opens M) (V : ∀ x : M, TangentSpace I x)
    {W : ∀ x : U, TangentSpace I x}
    (hW : ContMDiff I I.tangent ∞ (fun y ↦ (⟨y, W y⟩ : TangentBundle I U)))
    {x : M} (hx : x ∈ U) :
    ContMDiffAt I I.tangent ∞
      (fun y ↦ (⟨y, patchOnOpen U V W y⟩ : TangentBundle I M)) x := by
  let f := Poincare.Manifold.openSubtypePartialDiffeomorph I U ⟨⟨x, hx⟩⟩
  have hxf : x ∈ f.symm.source := by simpa [f] using hx
  exact (contMDiffAt_mpullback_partialDiffeomorph f.symm (by simp) hxf hW.contMDiffAt).congr_of_eventuallyEq
    (patchOnOpen_eventuallyEq_mpullback U V W hx)

theorem contMDiff_patchOnOpen [IsManifold I 1 M]
    (U : TopologicalSpace.Opens M) {V : ∀ x : M, TangentSpace I x}
    {W : ∀ x : U, TangentSpace I x}
    (hV : ContMDiff I I.tangent ∞ (fun y ↦ (⟨y, V y⟩ : TangentBundle I M)))
    (hW : ContMDiff I I.tangent ∞ (fun y ↦ (⟨y, W y⟩ : TangentBundle I U)))
    {K : Set M} (hK : IsClosed K) (hKU : K ⊆ U)
    (hagree : ∀ x : U, x.val ∉ K → W x = V x.val) :
    ContMDiff I I.tangent ∞
      (fun y ↦ (⟨y, patchOnOpen U V W y⟩ : TangentBundle I M)) := by
  intro x
  by_cases hx : x ∈ U
  · exact contMDiffAt_patchOnOpen_of_mem U V hW hx
  · exact hV.contMDiffAt.congr_of_eventuallyEq
      (patchOnOpen_eventuallyEq_self U V W hK hagree (fun h ↦ hx (hKU h)))

theorem patchOnOpen_zeroSet (U : TopologicalSpace.Opens M)
    (V : ∀ x : M, TangentSpace I x) (W : ∀ x : U, TangentSpace I x) :
    {x : M | patchOnOpen U V W x = 0} =
      Subtype.val '' {x : U | W x = 0} ∪ ({x : M | V x = 0} \ U) := by
  ext x
  constructor
  · intro hz
    by_cases hx : x ∈ U
    · exact Or.inl ⟨⟨x, hx⟩, (patchOnOpen_of_mem U V W hx).symm.trans hz, rfl⟩
    · exact Or.inr ⟨(patchOnOpen_of_not_mem U V W hx).symm.trans hz, hx⟩
  · rintro (⟨y, hy, rfl⟩ | ⟨hz, hx⟩)
    · exact (patchOnOpen_of_mem U V W y.property).trans hy
    · exact (patchOnOpen_of_not_mem U V W hx).trans hz

theorem patchOnOpen_isolated_off (U : TopologicalSpace.Opens M)
    (V : ∀ x : M, TangentSpace I x) (W : ∀ x : U, TangentSpace I x) {K : Set M}
    (hK : IsClosed K) (hW : ∀ x : U, x.val ∉ K → W x = V x.val)
    {x : M} (hx : x ∉ K) (hiso : ∀ᶠ y in 𝓝 x, V y = 0 → y = x) :
    ∀ᶠ y in 𝓝 x, patchOnOpen U V W y = 0 → y = x := by
  filter_upwards [patchOnOpen_eventuallyEq_self U V W hK hW hx, hiso] with y heq hy
  intro hz
  exact hy ((TotalSpace.mk_injective y heq).symm.trans hz)

theorem patchOnOpen_isolated_iff (U : TopologicalSpace.Opens M)
    (V : ∀ x : M, TangentSpace I x) (W : ∀ x : U, TangentSpace I x)
    {x : M} (hx : x ∈ U) :
    (∀ᶠ y in 𝓝 x, patchOnOpen U V W y = 0 → y = x) ↔
      ∀ᶠ y : U in 𝓝 (⟨x, hx⟩ : U), W y = 0 → y = ⟨x, hx⟩ := by
  let f := Poincare.Manifold.openSubtypePartialDiffeomorph I U ⟨⟨x, hx⟩⟩
  have hxf : x ∈ f.symm.source := by simpa [f] using hx
  have heq : (∀ᶠ y in 𝓝 x, patchOnOpen U V W y = 0 → y = x) ↔
      ∀ᶠ y in 𝓝 x, _root_.VectorField.mpullback I I f.symm W y = 0 → y = x := by
    apply Filter.eventually_congr
    filter_upwards [patchOnOpen_eventuallyEq_mpullback U V W hx] with y hy
    have hh := TotalSpace.mk_injective y hy
    change patchOnOpen U V W y = _root_.VectorField.mpullback I I f.symm W y at hh
    rw [hh]
  have ht := mpullback_partialDiffeomorph_isolated_iff f.symm (by simp) W hxf
  have hv : f.symm x = (⟨x, hx⟩ : U) :=
    Poincare.Manifold.openSubtypePartialDiffeomorph_symm_apply I U ⟨⟨x, hx⟩⟩ hx
  rw [hv] at ht
  exact heq.trans ht

end Poincare.VectorField
