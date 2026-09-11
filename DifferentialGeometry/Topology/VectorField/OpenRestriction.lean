import DifferentialGeometry.Topology.VectorField.OpenSubtypePullback
import DifferentialGeometry.Topology.VectorField.Transport

set_option autoImplicit false
open Set Bundle
open scoped Manifold ContDiff Topology
noncomputable section
namespace DifferentialGeometry.VectorField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

private theorem contMDiff_restrict
    (U : TopologicalSpace.Opens M) {V : ∀ x : M, TangentSpace I x}
    (hV : ContMDiffOn I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) U) :
    ContMDiff I I.tangent ∞ (fun x : U => (⟨x, V x.val⟩ : TangentBundle I U)) := by
  intro x
  let f := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph I U ⟨x⟩
  have h := contMDiffAt_mpullback_partialDiffeomorph f (by simp)
    (x := x) (by simp [f]) (hV.contMDiffAt (U.isOpen.mem_nhds x.property))
  apply h.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun y => congrArg
    (fun v : TangentSpace I y => (⟨y, v⟩ : TangentBundle I U))
    (DifferentialGeometry.Manifold.mpullback_openSubtype I U ⟨x⟩ V y).symm

theorem contMDiff_tangentSection_opens_iff
    (U : TopologicalSpace.Opens M) (W : ∀ x : U, TangentSpace I x) :
    ContMDiff I I.tangent ∞ (fun x : U => (⟨x, W x⟩ : TangentBundle I U)) ↔
      ContMDiff I I.tangent ∞ (fun x : U => (⟨x.val, W x⟩ : TangentBundle I M)) := by
  constructor
  · intro hW
    have hh := (contMDiff_subtype_val (I := I) (U := U) (n := ∞)).contMDiff_tangentMap (m := ∞) (by simp)
    have hgraph := hh.comp hW
    apply hgraph.congr
    intro x
    change (⟨x.val, W x⟩ : TangentBundle I M) =
      ⟨x.val, mfderiv I I (Subtype.val : U → M) x (W x)⟩
    rw [DifferentialGeometry.mfderiv_subtype_val]
    rfl
  · intro hW
    classical
    let V : ∀ x : M, TangentSpace I x := fun x => if hx : x ∈ U then W ⟨x, hx⟩ else 0
    have hVeq (x : U) : V x.val = W x := by
      exact dif_pos x.property
    have hV : ContMDiffOn I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) U := by
      have hh := hW.congr (fun x => congrArg
        (fun v : TangentSpace I x.val => (⟨x.val, v⟩ : TangentBundle I M)) (hVeq x))
      intro x hx
      exact ((contMDiffAt_subtype_iff (x := (⟨x, hx⟩ : U))).mp (hh ⟨x, hx⟩)).contMDiffWithinAt
    exact (contMDiff_restrict U hV).congr (fun x => congrArg
      (fun v : TangentSpace I x => (⟨x, v⟩ : TangentBundle I U)) (hVeq x).symm)

theorem contMDiff_tangentSection_restrict_opens_iff
    (U : TopologicalSpace.Opens M) (V : ∀ x : M, TangentSpace I x) :
    ContMDiff I I.tangent ∞ (fun x : U => (⟨x, V x.val⟩ : TangentBundle I U)) ↔
      ContMDiffOn I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) U := by
  constructor
  · intro hV x hx
    have hh := (contMDiff_tangentSection_opens_iff U _).mp hV
    exact ((contMDiffAt_subtype_iff (x := (⟨x, hx⟩ : U))).mp (hh ⟨x, hx⟩)).contMDiffWithinAt
  · exact contMDiff_restrict U

theorem contMDiff_tangentSection_restrict_opens
    (U : TopologicalSpace.Opens M) {V : ∀ x : M, TangentSpace I x}
    (hV : ContMDiffOn I I.tangent ∞ (fun x => (⟨x, V x⟩ : TangentBundle I M)) U) :
    ContMDiff I I.tangent ∞ (fun x : U => (⟨x, V x.val⟩ : TangentBundle I U)) :=
  (contMDiff_tangentSection_restrict_opens_iff U V).mpr hV

end DifferentialGeometry.VectorField
