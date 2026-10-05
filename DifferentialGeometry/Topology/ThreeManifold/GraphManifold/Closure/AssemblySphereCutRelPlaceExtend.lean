import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Geometry.Manifold.ContMDiff.Basic
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.Instances.Real

/-!
# Chapter-14 assembly, relative COMPARE G2: extension by the identity, ball complements

Lane ASM-L2e, group G2 (last part), used for the second placement of the non-separating case.

* `exists_extend_of_isCompact`: a diffeomorphism of an open subset which is the identity off a
  compact set extends by the identity to the whole manifold.
* `isConnected_normAnnulus`: the open annulus `a < ‖x‖ < b` of a real normed space of dimension at
  least two is connected.
* `connectedSpace_compl_ballImage`: in a connected manifold, the complement of the closed
  radius-two ball of a chart (whose source contains that closed ball) is connected — a separation
  of the complement would make the side not containing the outer shell clopen in the manifold.
-/

set_option autoImplicit false

noncomputable section

open Set Function Manifold Metric Filter
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

section Extend

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

/-- The extension by the identity of a self-map of an open subset. -/
def extendOpens (U : TopologicalSpace.Opens M) (f : U → U) (y : M) : M :=
  haveI := Classical.propDecidable
  if h : y ∈ U then (f ⟨y, h⟩).val else y

omit [IsManifold I ∞ M] [T2Space M] in
theorem extendOpens_of_mem (U : TopologicalSpace.Opens M) (f : U → U) (x : U) :
    extendOpens U f x = (f x).val := by
  rw [extendOpens, dite_eq_left_of_eq_true (eq_true x.property)]

omit [IsManifold I ∞ M] [T2Space M] in
theorem extendOpens_of_not_mem (U : TopologicalSpace.Opens M) (f : U → U) {y : M} (hy : y ∉ U) :
    extendOpens U f y = y := by
  rw [extendOpens, dite_eq_right_of_eq_false (eq_false hy)]

omit [IsManifold I ∞ M] [T2Space M] in
theorem extendOpens_of_mem' (U : TopologicalSpace.Opens M) (f : U → U) {y : M} (hy : y ∈ U) :
    extendOpens U f y = (f ⟨y, hy⟩).val :=
  extendOpens_of_mem U f ⟨y, hy⟩

omit [IsManifold I ∞ M] in
theorem contMDiff_extendOpens (U : TopologicalSpace.Opens M) {f : U → U}
    (hf : ContMDiff I I ∞ f) {K : Set U} (hK : IsCompact K) (hfix : ∀ x, x ∉ K → f x = x) :
    ContMDiff I I ∞ (extendOpens U f) := by
  intro y
  by_cases hy : y ∈ U
  · have h : ContMDiffAt I I ∞ (fun x : U => extendOpens U f x) ⟨y, hy⟩ := by
      have he : (fun x : U => extendOpens U f x) = fun x => (f x).val :=
        funext (extendOpens_of_mem U f)
      rw [he]
      exact (contMDiff_subtype_val.comp hf).contMDiffAt
    exact contMDiffAt_subtype_iff.mp h
  · have hKc : IsClosed (Subtype.val '' K : Set M) :=
      (hK.image continuous_subtype_val).isClosed
    have hyK : y ∉ Subtype.val '' K := by
      rintro ⟨x, -, rfl⟩
      exact hy x.property
    have hev : extendOpens U f =ᶠ[𝓝 y] id := by
      filter_upwards [hKc.isOpen_compl.mem_nhds hyK] with z hz
      by_cases hzU : z ∈ U
      · rw [extendOpens_of_mem' U f hzU, hfix ⟨z, hzU⟩ (fun h => hz ⟨_, h, rfl⟩)]
        rfl
      · exact extendOpens_of_not_mem U f hzU
    exact contMDiffAt_id.congr_of_eventuallyEq hev

omit [IsManifold I ∞ M] in
/-- **G2 (extension).** A diffeomorphism of an open subset fixed off a compact set extends by the
identity. -/
theorem exists_extend_of_isCompact (U : TopologicalSpace.Opens M) (Ψ : U ≃ₘ⟮I, I⟯ U) (K : Set U)
    (hK : IsCompact K) (hfix : ∀ x, x ∉ K → Ψ x = x) :
    ∃ Ψ' : M ≃ₘ⟮I, I⟯ M, (∀ x : U, Ψ' x = Ψ x) ∧ ∀ y, y ∉ Subtype.val '' K → Ψ' y = y := by
  have hfix' : ∀ x, x ∉ K → Ψ.symm x = x := by
    intro x hx
    have h := hfix x hx
    conv_lhs => rw [← h]
    exact Ψ.symm_apply_apply x
  have hleft : ∀ y, extendOpens U Ψ.symm (extendOpens U Ψ y) = y := by
    intro y
    by_cases hy : y ∈ U
    · rw [extendOpens_of_mem' U _ hy, extendOpens_of_mem U Ψ.symm (Ψ ⟨y, hy⟩),
        Ψ.symm_apply_apply]
    · rw [extendOpens_of_not_mem U _ hy, extendOpens_of_not_mem U _ hy]
  have hright : ∀ y, extendOpens U Ψ (extendOpens U Ψ.symm y) = y := by
    intro y
    by_cases hy : y ∈ U
    · rw [extendOpens_of_mem' U _ hy, extendOpens_of_mem U Ψ (Ψ.symm ⟨y, hy⟩),
        Ψ.apply_symm_apply]
    · rw [extendOpens_of_not_mem U _ hy, extendOpens_of_not_mem U _ hy]
  refine ⟨{ toFun := extendOpens U Ψ
            invFun := extendOpens U Ψ.symm
            left_inv := hleft
            right_inv := hright
            contMDiff_toFun := contMDiff_extendOpens U Ψ.contMDiff hK hfix
            contMDiff_invFun := contMDiff_extendOpens U Ψ.symm.contMDiff hK hfix' },
    fun x => extendOpens_of_mem U Ψ x, fun y hy => ?_⟩
  change extendOpens U Ψ y = y
  by_cases hyU : y ∈ U
  · rw [extendOpens_of_mem' U _ hyU, hfix ⟨y, hyU⟩ (fun h => hy ⟨_, h, rfl⟩)]
  · exact extendOpens_of_not_mem U _ hyU

end Extend

/-- The open annulus `a < ‖x‖ < b` in a real normed space of dimension at least two is
connected. -/
theorem isConnected_normAnnulus {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (hrank : 1 < Module.rank ℝ E) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    IsConnected (ball (0 : E) b \ closedBall (0 : E) a) := by
  have hsphere : IsConnected (sphere (0 : E) 1) :=
    (isPathConnected_sphere hrank 0 zero_le_one).isConnected
  have hIoo : IsConnected (Ioo a b) := isConnected_Ioo hab
  have heq : (fun p : E × ℝ => p.2 • p.1) '' (sphere (0 : E) 1 ×ˢ Ioo a b) =
      ball (0 : E) b \ closedBall (0 : E) a := by
    ext y
    constructor
    · rintro ⟨⟨v, t⟩, ⟨hv, ht⟩, rfl⟩
      have hv1 : ‖v‖ = 1 := by simpa [mem_sphere_iff_norm] using hv
      have ht0 : 0 < t := lt_trans ha ht.1
      refine ⟨?_, ?_⟩
      · rw [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht0, hv1, mul_one]
        exact ht.2
      · rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos ht0, hv1,
          mul_one]
        exact not_le.mpr ht.1
    · intro hy
      have hd1 : dist y 0 < b := mem_ball.mp hy.1
      have hd2 : a < dist y 0 := by
        have := hy.2
        rw [mem_closedBall] at this
        exact not_le.mp this
      rw [dist_zero_right] at hd1 hd2
      have hpos : 0 < ‖y‖ := lt_trans ha hd2
      refine ⟨(‖y‖⁻¹ • y, ‖y‖), ⟨?_, ⟨hd2, hd1⟩⟩, ?_⟩
      · rw [mem_sphere_iff_norm]
        simp only [sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hpos),
          inv_mul_cancel₀ hpos.ne']
      · simp only [smul_smul, mul_inv_cancel₀ hpos.ne', one_smul]
  rw [← heq]
  exact (hsphere.prod hIoo).image _ (by fun_prop)

section Complement

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {H M : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E3 H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem exists_ball_subset_source (c : PartialDiffeomorph (𝓡 3) I E3 M ∞)
    (hc : closedBall 0 2 ⊆ c.source) : ∃ ε > (0 : ℝ), ball (0 : E3) (2 + ε) ⊆ c.source := by
  obtain ⟨δ, hδ, hδs⟩ := (isCompact_closedBall (0 : E3) 2).exists_cthickening_subset_open
    c.open_source hc
  refine ⟨δ, hδ, fun x hx => hδs ?_⟩
  rw [cthickening_closedBall hδ.le (by norm_num), add_comm]
  exact ball_subset_closedBall hx

/-- **G2 (ball complement).** The complement of the closed radius-two ball of a chart in a
connected three-manifold is connected. -/
theorem connectedSpace_compl_ballImage [ConnectedSpace M] [T2Space M]
    (c : PartialDiffeomorph (𝓡 3) I E3 M ∞) (hc : closedBall 0 2 ⊆ c.source) :
    ConnectedSpace ((c '' closedBall 0 2)ᶜ : Set M) := by
  obtain ⟨ε, hε, hεs⟩ := exists_ball_subset_source c hc
  set K : Set M := c '' closedBall 0 2
  have hKc : IsClosed K :=
    ((isCompact_closedBall (0 : E3) 2).image_of_continuousOn
      (c.contMDiffOn_toFun.continuousOn.mono hc)).isClosed
  have hrank : 1 < Module.rank ℝ E3 := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    norm_num
  -- the outer shell
  set A : Set E3 := ball 0 (2 + ε) \ closedBall 0 2
  have hA : IsConnected A := isConnected_normAnnulus hrank (by norm_num) (by linarith)
  have hAs : A ⊆ c.source := fun x hx => hεs hx.1
  have hS : IsPreconnected (c '' A) :=
    hA.isPreconnected.image _ (c.contMDiffOn_toFun.continuousOn.mono hAs)
  have hSK : c '' A ⊆ Kᶜ := by
    rintro _ ⟨x, hx, rfl⟩ ⟨y, hy, hxy⟩
    exact hx.2 ((c.injOn (hc hy) (hAs hx) hxy) ▸ hy)
  have hopen : IsOpen (c '' ball 0 (2 + ε)) :=
    c.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_ball hεs
  have hcover : c '' ball 0 (2 + ε) ⊆ K ∪ c '' A := by
    rintro _ ⟨x, hx, rfl⟩
    by_cases hx2 : x ∈ closedBall (0 : E3) 2
    · exact Or.inl ⟨x, hx2, rfl⟩
    · exact Or.inr ⟨x, ⟨hx, hx2⟩, rfl⟩
  have hne : (Kᶜ : Set M).Nonempty := by
    obtain ⟨x, hx⟩ : A.Nonempty := hA.nonempty
    exact ⟨c x, hSK ⟨x, hx, rfl⟩⟩
  -- a clopen side not containing the shell would be clopen in `M`
  have key : ∀ u v : Set M, IsOpen u → IsOpen v → Kᶜ ⊆ u ∪ v → Kᶜ ∩ (u ∩ v) = ∅ →
      c '' A ⊆ u → (Kᶜ ∩ v) = ∅ := by
    intro u v hu hv hcov hdisj hSu
    by_contra hvne
    have hvne' : (Kᶜ ∩ v).Nonempty := nonempty_iff_ne_empty.mpr hvne
    have hB : IsClopen (Kᶜ ∩ v) := by
      refine ⟨?_, hKc.isOpen_compl.inter hv⟩
      have hcompl : (Kᶜ ∩ v)ᶜ = (Kᶜ ∩ u) ∪ c '' ball 0 (2 + ε) := by
        ext y
        constructor
        · intro hy
          by_cases hyK : y ∈ K
          · obtain ⟨x, hx, rfl⟩ := hyK
            exact Or.inr ⟨x, mem_ball_zero_iff.mpr
              (lt_of_le_of_lt (mem_closedBall_zero_iff.mp hx) (by linarith)), rfl⟩
          · rcases hcov hyK with hu' | hv'
            · exact Or.inl ⟨hyK, hu'⟩
            · exact (hy ⟨hyK, hv'⟩).elim
        · rintro (⟨hyK, hyu⟩ | hy) ⟨hyK', hyv⟩
          · exact (Set.eq_empty_iff_forall_notMem.mp hdisj) y ⟨hyK, hyu, hyv⟩
          · rcases hcover hy with hK' | hS'
            · exact hyK' hK'
            · exact (Set.eq_empty_iff_forall_notMem.mp hdisj) y ⟨hyK', hSu hS', hyv⟩
      rw [← isOpen_compl_iff, hcompl]
      exact (hKc.isOpen_compl.inter hu).union hopen
    rcases isClopen_iff.mp hB with h | h
    · exact (nonempty_iff_ne_empty.mp hvne') h
    · obtain ⟨x, hx⟩ : (closedBall (0 : E3) 2).Nonempty := nonempty_closedBall.mpr (by norm_num)
      have hmem : c x ∈ Kᶜ ∩ v := h ▸ mem_univ _
      exact hmem.1 ⟨x, hx, rfl⟩
  apply isConnected_iff_connectedSpace.mp
  refine ⟨hne, ?_⟩
  intro u v hu hv hcov hu' hv'
  by_contra hempty
  rw [not_nonempty_iff_eq_empty] at hempty
  have hdisj' : Disjoint (u ∩ Kᶜ) (v ∩ Kᶜ) := by
    rw [Set.disjoint_iff_inter_eq_empty]
    apply Set.eq_empty_of_subset_empty
    rintro y ⟨⟨hyu, hyK⟩, hyv, -⟩
    exact (Set.eq_empty_iff_forall_notMem.mp hempty) y ⟨hyK, hyu, hyv⟩
  have hsub : c '' A ⊆ (u ∩ Kᶜ) ∪ (v ∩ Kᶜ) := by
    intro y hy
    rcases hcov (hSK hy) with h | h
    · exact Or.inl ⟨h, hSK hy⟩
    · exact Or.inr ⟨h, hSK hy⟩
  rcases hS.subset_or_subset (hu.inter hKc.isOpen_compl) (hv.inter hKc.isOpen_compl) hdisj'
      hsub with hSu | hSv
  · have := key u v hu hv hcov hempty (hSu.trans inter_subset_left)
    exact (nonempty_iff_ne_empty.mp hv') this
  · have := key v u hv hu (by rw [union_comm]; exact hcov) (by rw [inter_comm v u]; exact hempty)
      (hSv.trans inter_subset_left)
    exact (nonempty_iff_ne_empty.mp hu') this

end Complement

end GC.GraphManifold.Assembly
