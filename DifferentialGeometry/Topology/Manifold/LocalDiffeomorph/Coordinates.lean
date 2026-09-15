import Mathlib.Geometry.Manifold.LocalDiffeomorph
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict

section

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E₁ E₂ E₃ : Type*}
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃]
  {H₁ H₂ H₃ : Type*} [TopologicalSpace H₁] [TopologicalSpace H₂]
  [TopologicalSpace H₃]
  {I₁ : ModelWithCorners 𝕜 E₁ H₁} {I₂ : ModelWithCorners 𝕜 E₂ H₂}
  {I₃ : ModelWithCorners 𝕜 E₃ H₃}
  {M₁ M₂ M₃ : Type*}
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
  [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  [TopologicalSpace M₃] [ChartedSpace H₃ M₃]
  {n : WithTop ℕ∞}

theorem PartialDiffeomorph.contMDiffOn_of_symm_comp
    (c : PartialDiffeomorph I₁ I₂ M₁ M₂ n) {f : M₃ → M₂} {s : Set M₃}
    (hf : ContMDiffOn I₃ I₁ n (fun x => c.symm (f x)) s)
    (hmap : MapsTo f s c.target) : ContMDiffOn I₃ I₂ n f s := by
  apply (c.contMDiffOn.comp hf (fun x hx => c.toPartialEquiv.map_target (hmap hx))).congr
  intro x hx
  exact (c.toPartialEquiv.right_inv (hmap hx)).symm

theorem IsLocalDiffeomorphAt.contMDiffAt_of_comp
    {q : M₁ → M₂} {x : M₁} (hq : IsLocalDiffeomorphAt I₁ I₂ n q x)
    {f : M₂ → M₃} (hf : ContMDiffAt I₁ I₃ n (f ∘ q) x) :
    ContMDiffAt I₂ I₃ n f (q x) := by
  have hinverse : hq.localInverse (q x) = x :=
    hq.localInverse_left_inv hq.localInverse_mem_target
  have hf' : ContMDiffAt I₁ I₃ n (f ∘ q) (hq.localInverse (q x)) := by
    rwa [hinverse]
  apply (hf'.comp (q x) hq.localInverse_contMDiffAt).congr_of_eventuallyEq
  filter_upwards [hq.localInverse.open_source.mem_nhds hq.localInverse_mem_source] with z hz
  change f z = f (q (hq.localInverse z))
  rw [hq.localInverse_right_inv hz]

end

end

section

noncomputable section
open Set Function
open scoped ContDiff Manifold Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E₁ E₂ E₃ : Type*}
  [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
  [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂]
  [NormedAddCommGroup E₃] [NormedSpace 𝕜 E₃]
  {H₁ H₂ H₃ : Type*} [TopologicalSpace H₁] [TopologicalSpace H₂]
  [TopologicalSpace H₃]
  {I₁ : ModelWithCorners 𝕜 E₁ H₁} {I₂ : ModelWithCorners 𝕜 E₂ H₂}
  {I₃ : ModelWithCorners 𝕜 E₃ H₃}
  {M₁ M₂ M₃ : Type*}
  [TopologicalSpace M₁] [ChartedSpace H₁ M₁]
  [TopologicalSpace M₂] [ChartedSpace H₂ M₂]
  [TopologicalSpace M₃] [ChartedSpace H₃ M₃]
  {n : WithTop ℕ∞}

theorem IsLocalDiffeomorph.contMDiffOn_of_comp
    {e : M₁ → M₂} (he : IsLocalDiffeomorph I₁ I₂ n e)
    {W : Set M₁} (hW : IsOpen W) {f : M₂ → M₃}
    (hf : ContMDiffOn I₁ I₃ n (f ∘ e) W) :
    ContMDiffOn I₂ I₃ n f (e '' W) := by
  rintro y ⟨z, hz, rfl⟩
  exact ((he z).contMDiffAt_of_comp
    (hf.contMDiffAt (hW.mem_nhds hz))).contMDiffWithinAt

theorem IsLocalDiffeomorph.contMDiffOn_extend
    {e : M₁ → M₂} (he : IsLocalDiffeomorph I₁ I₂ n e)
    (hinj : Injective e) (d : M₂ → M₃)
    {W : Set M₁} (hW : IsOpen W) {f : M₁ → M₃}
    (hf : ContMDiffOn I₁ I₃ n f W) :
    ContMDiffOn I₂ I₃ n (Function.extend e f d) (e '' W) := by
  apply he.contMDiffOn_of_comp hW
  rwa [Function.extend_comp hinj]

theorem IsLocalDiffeomorph.contMDiffOn_comp_invFun [Nonempty M₁]
    {e : M₁ → M₂} (he : IsLocalDiffeomorph I₁ I₂ n e)
    (hinj : Injective e) {W : Set M₁} (hW : IsOpen W) {f : M₁ → M₃}
    (hf : ContMDiffOn I₁ I₃ n f W) :
    ContMDiffOn I₂ I₃ n (f ∘ Function.invFun e) (e '' W) := by
  apply he.contMDiffOn_of_comp hW
  simpa only [Function.comp_assoc, Function.invFun_comp hinj, Function.comp_id] using hf

namespace DifferentialGeometry.Topology.Manifold

omit [TopologicalSpace H₁] [TopologicalSpace M₁] [ChartedSpace H₁ M₁] in
theorem contMDiffOn_extend_from_open_coordinates
    (U : TopologicalSpace.Opens E₁) {e : U → M₂}
    (he : IsLocalDiffeomorph (modelWithCornersSelf 𝕜 E₁) I₂ n e)
    (hinj : Injective e) (d : M₂ → M₃)
    {W : Set E₁} (hW : IsOpen W) {f : E₁ → M₃}
    (hf : ContMDiffOn (modelWithCornersSelf 𝕜 E₁) I₃ n f W) :
    ContMDiffOn I₂ I₃ n (Function.extend e (fun z : U => f z) d)
      (e '' (Subtype.val ⁻¹' W)) := by
  apply he.contMDiffOn_extend hinj d (hW.preimage continuous_subtype_val)
  exact hf.comp contMDiff_subtype_val.contMDiffOn (fun _ hz => hz)

end DifferentialGeometry.Topology.Manifold

end

end

section

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Topology.Manifold

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ F H} {J : ModelWithCorners ℝ G H'}
  {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace H' N]

theorem contDiffOn_of_open_coordinate_map
    (U : TopologicalSpace.Opens E) {V : Set M} (hV : IsOpen V)
    {f : M → N} {e : U → M}
    (he : ContMDiff (modelWithCornersSelf ℝ E) I ∞ e)
    (hf : ContMDiffOn I J ∞ f V)
    (d : PartialDiffeomorph (modelWithCornersSelf ℝ E) J E N ∞)
    {W : Set E} (hWU : W ⊆ U)
    (hWV : ∀ (z : E) (hz : z ∈ W), e ⟨z, hWU hz⟩ ∈ V)
    (hWd : ∀ (z : E) (hz : z ∈ W), f (e ⟨z, hWU hz⟩) ∈ d.target)
    {C : E → E}
    (hC : ∀ z : U, C z = d.symm (f (e z))) :
    ContDiffOn ℝ ∞ C W := by
  intro z hz
  let u : U := ⟨z, hWU hz⟩
  have hez : ContMDiffAt (modelWithCornersSelf ℝ E) I ∞ e u := he u
  have hfz := hf.contMDiffAt (hV.mem_nhds (hWV z hz))
  have hdz := d.contMDiffOn_invFun.contMDiffAt (d.open_target.mem_nhds (hWd z hz))
  have hcomp : ContMDiffAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) ∞
      (fun w : U => d.symm (f (e w))) u :=
    hdz.comp u (hfz.comp u hez)
  have hCs : ContMDiffAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) ∞
      (fun w : U => C w) u :=
    hcomp.congr_of_eventuallyEq (Filter.Eventually.of_forall hC)
  exact ((contMDiffAt_subtype_iff.mp hCs).contDiffAt).contDiffWithinAt

end DifferentialGeometry.Topology.Manifold

end

end

section

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace IsLocalDiffeomorphAt

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {H H' H'' : Type*} [TopologicalSpace H] [TopologicalSpace H'] [TopologicalSpace H'']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'} {K : ModelWithCorners ℝ G H''}
  {M N P : Type*} [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
  [ChartedSpace H M] [ChartedSpace H' N] [ChartedSpace H'' P] {n : ℕ∞ω}

theorem of_comp_left {f : M → N} {e : N → P} {x : M}
    (he : IsLocalDiffeomorphAt J K n e (f x))
    (hef : IsLocalDiffeomorphAt I K n (e ∘ f) x)
    (hf : ContinuousAt f x) :
    IsLocalDiffeomorphAt I J n f x := by
  apply DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq
    (hg := IsLocalDiffeomorphAt.comp (I := I) (J := K) (P := N) J hef he.localInverse_isLocalDiffeomorphAt)
  filter_upwards [hf.tendsto.eventually he.localInverse_eventuallyEq_left] with z hz
  exact hz.symm


theorem of_coordinate_map
    {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {HA HB : Type*} [TopologicalSpace HA] [TopologicalSpace HB]
    {IA : ModelWithCorners ℝ A HA} {IB : ModelWithCorners ℝ B HB}
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [ChartedSpace HA X] [ChartedSpace HB Y]
    {f : M → N} {x : X} {e : X → M}
    (he : IsLocalDiffeomorphAt IA I n e x)
    (d : PartialDiffeomorph IB J Y N n)
    (hd : f (e x) ∈ d.target) (hf : ContinuousAt (f ∘ e) x)
    (hcoord : IsLocalDiffeomorphAt IA IB n (d.symm ∘ f ∘ e) x) :
    IsLocalDiffeomorphAt I J n f (e x) := by
  have hdloc : IsLocalDiffeomorphAt J IB n d.symm (f (e x)) :=
    d.symm.isLocalDiffeomorphAt J IB n hd
  have hcomp : IsLocalDiffeomorphAt IA J n (f ∘ e) x :=
    IsLocalDiffeomorphAt.of_comp_left hdloc hcoord hf
  exact DifferentialGeometry.isLocalDiffeomorphAt_of_comp hcomp he

end IsLocalDiffeomorphAt

end

end

section

noncomputable section
open Set Filter
open scoped Topology ContDiff

namespace IsLocalDiffeomorphAt

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  {H H' : Type*} [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ F H} {J : ModelWithCorners ℝ G H'}
  {M N : Type*} [TopologicalSpace M] [TopologicalSpace N]
  [ChartedSpace H M] [ChartedSpace H' N]

theorem of_open_coordinate_map
    (U : TopologicalSpace.Opens E) {f : M → N} {e : U → M} {z : U}
    (he : IsLocalDiffeomorphAt (modelWithCornersSelf ℝ E) I ∞ e z)
    (d : PartialDiffeomorph (modelWithCornersSelf ℝ E) J E N ∞)
    (hd : f (e z) ∈ d.target) (hf : ContinuousAt f (e z))
    {C : E → E}
    (heq : (fun w : U => C w) =ᶠ[𝓝 z] (d.symm ∘ f ∘ e))
    (hC : IsLocalDiffeomorphAt (modelWithCornersSelf ℝ E) (modelWithCornersSelf ℝ E) ∞ C z) :
    IsLocalDiffeomorphAt I J ∞ f (e z) := by
  have hval := DifferentialGeometry.isLocalDiffeomorph_subtype_val
    (I := modelWithCornersSelf ℝ E) U z
  have hrestrict : IsLocalDiffeomorphAt (modelWithCornersSelf ℝ E)
      (modelWithCornersSelf ℝ E) ∞ (fun w : U => C w) z :=
    IsLocalDiffeomorphAt.comp (modelWithCornersSelf ℝ E) (P := E) hval hC
  exact IsLocalDiffeomorphAt.of_coordinate_map he d hd
    (hf.comp he.contMDiffAt.continuousAt)
    (DifferentialGeometry.IsLocalDiffeomorphAt.of_eventuallyEq heq.symm hrestrict)

end IsLocalDiffeomorphAt

end

end
