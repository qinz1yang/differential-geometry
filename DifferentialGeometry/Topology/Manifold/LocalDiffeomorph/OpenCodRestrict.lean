import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.Open
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.PartialDiffeomorph
import DifferentialGeometry.Topology.Manifold.PartialDiffeomorph.Opens

set_option autoImplicit false
noncomputable section
open Set Function Topology TopologicalSpace Filter
open scoped Manifold ContDiff

namespace DifferentialGeometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real E H}
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F]
variable {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners Real F H'}
variable {G : Type*} [NormedAddCommGroup G] [NormedSpace Real G]
variable {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners Real G H''}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
variable {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P]
variable {n : WithTop ℕ∞}

theorem isLocalDiffeomorphAt_of_comp {f : M → N} {g : N → P} {x : M}
    (hgf : IsLocalDiffeomorphAt I K n (g ∘ f) x) (hf : IsLocalDiffeomorphAt I J n f x) :
    IsLocalDiffeomorphAt J K n g (f x) := by
  have hx : hf.localInverse (f x) = x := hf.localInverse_left_inv hf.localInverse_mem_target
  have h1 : IsLocalDiffeomorphAt I K n (g ∘ f) (hf.localInverse (f x)) := by
    rw [hx]
    exact hgf
  have h2 : IsLocalDiffeomorphAt J K n ((g ∘ f) ∘ hf.localInverse) (f x) :=
    (hf.localInverse_isLocalDiffeomorphAt).comp (K := K) (P := P) h1
  refine IsLocalDiffeomorphAt.of_eventuallyEq ?_ h2
  filter_upwards [hf.localInverse_eventuallyEq_right] with y hy
  exact (congrArg g hy).symm

theorem isLocalDiffeomorphAt_subtypeCodRestrict {V : Opens N} {f : M → N} (hfV : ∀ y, f y ∈ V)
    {x : M} (hf : IsLocalDiffeomorphAt I J ∞ f x) :
    IsLocalDiffeomorphAt I J ∞ (fun y => (⟨f y, hfV y⟩ : V)) x := by
  classical
  obtain ⟨Φ, hx, heq⟩ := hf
  have hxV : Φ x ∈ V := by
    rw [← heq.eq_of_mem hx]
    exact hfV x
  let W : Opens M :=
    ⟨Φ.source ∩ (Φ : M → N) ⁻¹' (V : Set N),
      Φ.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage Φ.open_source V.2⟩
  have hxW : x ∈ W := ⟨hx, hxV⟩
  have hWsub : (W : Set M) ⊆ Φ.source := fun y hy => hy.1
  let toFun : M → V :=
    fun y => if hy : y ∈ W then (⟨Φ y, hy.2⟩ : V) else (⟨f y, hfV y⟩ : V)
  have htoFun_of_mem : ∀ y (hy : y ∈ W), toFun y = (⟨Φ y, hy.2⟩ : V) :=
    fun y hy => dif_pos hy
  have hcoe : ∀ y (hy : y ∈ W), (toFun y : N) = Φ y :=
    fun y hy => congrArg Subtype.val (htoFun_of_mem y hy)
  have himage : ((toFun : M → V) '' (W : Set M))
      = (Subtype.val ⁻¹' ((Φ : M → N) '' (W : Set M)) : Set V) := by
    ext v
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, (hcoe y hy).symm⟩
    · rintro ⟨y, hy, hyv⟩
      exact ⟨y, hy, Subtype.ext ((hcoe y hy).symm ▸ hyv)⟩
  let V' : Opens V :=
    ⟨(Subtype.val ⁻¹' ((Φ : M → N) '' (W : Set M)) : Set V),
      (image_opens_isOpen Φ (U := W) hWsub).preimage continuous_subtype_val⟩
  refine ⟨{ toFun := toFun
            invFun := fun v => Φ.symm (v : N)
            source := (W : Set M)
            target := (V' : Set V)
            map_source' := fun y hy => by
              change toFun y ∈ (Subtype.val ⁻¹' ((Φ : M → N) '' (W : Set M)) : Set V)
              rw [← himage]
              exact ⟨y, hy, rfl⟩
            map_target' := fun v hv => by
              obtain ⟨y, hy, hyv⟩ : (v : N) ∈ (Φ : M → N) '' (W : Set M) := hv
              have hsy : Φ.symm (v : N) = y := by
                rw [← hyv]
                exact Φ.left_inv' hy.1
              rw [hsy]
              exact hy
            left_inv' := fun y hy => by
              rw [hcoe y hy]
              exact Φ.left_inv' hy.1
            right_inv' := fun v hv => by
              obtain ⟨y, hy, hyv⟩ : (v : N) ∈ (Φ : M → N) '' (W : Set M) := hv
              have hmem : Φ.symm (v : N) ∈ W := by
                have hsy : Φ.symm (v : N) = y := by
                  rw [← hyv]
                  exact Φ.left_inv' hy.1
                rw [hsy]
                exact hy
              change toFun (Φ.symm (v : N)) = v
              rw [htoFun_of_mem (Φ.symm (v : N)) hmem]
              refine Subtype.ext ?_
              change Φ (Φ.symm (v : N)) = (v : N)
              rw [← hyv]
              exact Φ.right_inv' (Φ.map_source' hy.1)
            open_source := W.2
            open_target := V'.2
            contMDiffOn_toFun := by
              have hamb : ContMDiffOn I J ∞ (fun z : M => (toFun z : N)) (W : Set M) :=
                (Φ.contMDiffOn_toFun.mono hWsub).congr (fun y hy => (hcoe y hy))
              intro y hy
              rw [← ContMDiffWithinAt.subtypeVal_comp_iff V toFun (W : Set M) y]
              exact hamb y hy
            contMDiffOn_invFun := by
              intro v hv
              obtain ⟨y, hy, hyv⟩ : (v : N) ∈ (Φ : M → N) '' (W : Set M) := hv
              have hvt : (v : N) ∈ Φ.target := by
                rw [← hyv]
                exact Φ.map_source' hy.1
              have hbase : ContMDiffAt J I ∞ (fun w : V => Φ.symm (w : N)) v := by
                rw [contMDiffAt_subtype_iff]
                exact Φ.symm.contMDiffOn_toFun.contMDiffAt (Φ.open_target.mem_nhds hvt)
              exact hbase.contMDiffWithinAt },
    hxW, fun y hy => by
      change (⟨f y, hfV y⟩ : V) = toFun y
      rw [htoFun_of_mem y hy]
      exact Subtype.ext (heq.eq_of_mem hy.1)⟩

end DifferentialGeometry
