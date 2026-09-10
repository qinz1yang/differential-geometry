import DifferentialGeometry.Geometry.Comparison.Soul.SmoothLocalInverse
import Mathlib.Dynamics.Flow
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

set_option autoImplicit false
noncomputable section

open Filter Function Manifold Set
open scoped Topology ContDiff Manifold

namespace DifferentialGeometry.Geometry.Topology

section ScalarInverse

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem scalar_linear_decompose (D : E × ℝ →L[ℝ] ℝ) (z : E × ℝ) :
    D z = D (z.1, 0) + z.2 * D (0, 1) := by
  have hs : D ((0 : E), z.2) = z.2 * D (0, 1) := by
    simpa using D.map_smul z.2 ((0 : E), (1 : ℝ))
  calc
    D z = D ((z.1, 0) + ((0 : E), z.2)) := by congr 1; ext <;> simp
    _ = D (z.1, 0) + D (0, z.2) := D.map_add _ _
    _ = D (z.1, 0) + z.2 * D (0, 1) := by rw [hs]

private def scalarGraphEquiv (D : E × ℝ →L[ℝ] ℝ) (hD : D (0, 1) ≠ 0) :
    (E × ℝ) ≃L[ℝ] (E × ℝ) where
  toFun z := (z.1, D z)
  invFun z := (z.1, (z.2 - D (z.1, 0)) / D (0, 1))
  left_inv z := by
    apply Prod.ext
    · rfl
    · change (D z - D (z.1, 0)) / D (0, 1) = z.2
      rw [scalar_linear_decompose D z, add_sub_cancel_left, mul_div_cancel_right₀ _ hD]
  right_inv z := by
    apply Prod.ext
    · rfl
    · change D (z.1, (z.2 - D (z.1, 0)) / D (0, 1)) = z.2
      rw [scalar_linear_decompose]
      dsimp only
      rw [div_mul_cancel₀ _ hD]
      ring
  map_add' z w := Prod.ext rfl (D.map_add z w)
  map_smul' r z := Prod.ext rfl (D.map_smul r z)
  continuous_toFun := continuous_fst.prodMk D.continuous
  continuous_invFun := continuous_fst.prodMk
    ((continuous_snd.sub (D.continuous.comp
      (continuous_fst.prodMk continuous_const))).div_const _)

variable [CompleteSpace E]

private theorem exists_smooth_scalar_root
    {F : E × ℝ → ℝ} {U : Set (E × ℝ)} (hU : IsOpen U) {u : E × ℝ} (hu : u ∈ U)
    (hF : ContDiffOn ℝ ∞ F U) {a : ℝ}
    (htime : HasDerivAt (fun t => F (u.1, t)) a u.2) (ha : a ≠ 0) :
    ∃ ψ : E → ℝ, ∃ W : Set E, IsOpen W ∧ u.1 ∈ W ∧
      ContDiffOn ℝ ∞ ψ W ∧ ψ u.1 = u.2 ∧
      ∀ x ∈ W, (x, ψ x) ∈ U ∧ F (x, ψ x) = F u := by
  have hFd := (hF.contDiffAt (hU.mem_nhds hu)).differentiableAt (by simp)
  let D : E × ℝ →L[ℝ] ℝ := fderiv ℝ F u
  have hd : HasFDerivAt F D u := hFd.hasFDerivAt
  have hpartial : HasDerivAt (fun t => F (u.1, t)) (D (0, 1)) u.2 :=
    hd.comp_hasDerivAt u.2 ((hasDerivAt_const u.2 u.1).prodMk (hasDerivAt_id u.2))
  have hD : D (0, 1) ≠ 0 := by
    rw [hpartial.unique htime]
    exact ha
  let G : E × ℝ → E × ℝ := fun z => (z.1, F z)
  have hG : ContDiffOn ℝ ∞ G U := contDiffOn_fst.prodMk hF
  have hdG : HasFDerivAt G ((ContinuousLinearMap.fst ℝ E ℝ).prod D) u :=
    (hasFDerivAt_fst (p := u)).prodMk hd
  have hinv : (fderiv ℝ G u).IsInvertible := by
    rw [hdG.fderiv]
    exact ⟨scalarGraphEquiv D hD, rfl⟩
  have hl : IsLocalDiffeomorphAt 𝓘(ℝ, E × ℝ) 𝓘(ℝ, E × ℝ) ∞ G u := by
    apply isLocalDiffeomorphAt_of_contMDiffOn_of_isInvertible hU hu hG.contMDiffOn
    simpa only [writtenInExtChartAt_model_space, extChartAt_self_apply,
      modelWithCornersSelf_coe, Function.id_def] using hinv
  let e := hl.localInverse
  let ψ : E → ℝ := fun x => (e (x, F u)).2
  let W : Set E := (fun x => (x, F u)) ⁻¹' (e.source ∩ e ⁻¹' U)
  have hW : IsOpen W :=
    (e.contMDiffOn_toFun.continuousOn.isOpen_inter_preimage e.open_source hU).preimage
      (continuous_id.prodMk continuous_const)
  have heSelf : e (u.1, F u) = u := hl.localInverse_left_inv hl.localInverse_mem_target
  have huW : u.1 ∈ W := by
    refine ⟨hl.localInverse_mem_source, ?_⟩
    change e (u.1, F u) ∈ U
    rwa [heSelf]
  have hψ : ContDiffOn ℝ ∞ ψ W :=
    (e.contMDiffOn_toFun.contDiffOn.comp
      (contDiff_id.prodMk contDiff_const).contDiffOn (fun _ hx => hx.1)).snd
  refine ⟨ψ, W, hW, huW, hψ, congrArg Prod.snd heSelf, ?_⟩
  intro x hx
  have hh : G (e (x, F u)) = (x, F u) := hl.localInverse_right_inv hx.1
  have hfst := congrArg Prod.fst hh
  change (e (x, F u)).1 = x at hfst
  have heq : e (x, F u) = (x, ψ x) := Prod.ext hfst rfl
  refine ⟨heq ▸ hx.2, ?_⟩
  have hheight := congrArg Prod.snd hh
  change F (e (x, F u)) = F u at hheight
  rwa [heq] at hheight

end ScalarInverse

section Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

private theorem exists_smooth_scalar_root_manifold
    {F : M × ℝ → ℝ} {U : Set (M × ℝ)} (hU : IsOpen U)
    (hF : ContMDiffOn (I.prod 𝓘(ℝ, ℝ)) 𝓘(ℝ, ℝ) ∞ F U)
    {q : M} {t : ℝ} (hqt : (q, t) ∈ U) {a : ℝ}
    (htime : HasDerivAt (fun s => F (q, s)) a t) (ha : a ≠ 0) :
    ∃ τ : M → ℝ, ∃ W : Set M, IsOpen W ∧ q ∈ W ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ τ W ∧ τ q = t ∧
      ∀ x ∈ W, (x, τ x) ∈ U ∧ F (x, τ x) = F (q, t) := by
  let c : PartialEquiv M E := extChartAt I q
  let C : E × ℝ → M × ℝ := fun z => (c.symm z.1, z.2)
  let A : Set (E × ℝ) := c.target ×ˢ (univ : Set ℝ)
  have hA : IsOpen A := (isOpen_extChartAt_target q).prod isOpen_univ
  have hC : ContMDiffOn 𝓘(ℝ, E × ℝ) (I.prod 𝓘(ℝ, ℝ)) ∞ C A :=
    ((contMDiffOn_extChartAt_symm q).comp contDiffOn_fst.contMDiffOn
      (fun _ hz => hz.1)).prodMk contDiffOn_snd.contMDiffOn
  let D : Set (E × ℝ) := A ∩ C ⁻¹' U
  let K : E × ℝ → ℝ := fun z => F (C z)
  have hD : IsOpen D := hC.continuousOn.isOpen_inter_preimage hA hU
  have hK : ContDiffOn ℝ ∞ K D :=
    (hF.comp (hC.mono inter_subset_left) (fun _ hz => hz.2)).contDiffOn
  have hcq : c.symm (c q) = q := c.left_inv (mem_extChartAt_source q)
  have hCt (s : ℝ) : C (c q, s) = (q, s) := Prod.ext hcq rfl
  have hqtD : (c q, t) ∈ D := by
    refine ⟨⟨mem_extChartAt_target q, mem_univ t⟩, ?_⟩
    change C (c q, t) ∈ U
    rwa [hCt]
  have htimeK : HasDerivAt (fun s => K (c q, s)) a t := by
    simpa only [K, hCt] using htime
  obtain ⟨ψ, V, hV, hqV, hψ, hψq, hroot⟩ := exists_smooth_scalar_root hD hqtD hK htimeK ha
  have hcs : ContMDiffOn I 𝓘(ℝ, E) ∞ c c.source := by
    simpa only [c, extChartAt_source] using (contMDiffOn_extChartAt (I := I) (x := q))
  let W : Set M := c.source ∩ c ⁻¹' V
  have hW : IsOpen W :=
    hcs.continuousOn.isOpen_inter_preimage (isOpen_extChartAt_source q) hV
  have hqW : q ∈ W := ⟨mem_extChartAt_source q, hqV⟩
  have hτ : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ (fun x => ψ (c x)) W :=
    hψ.contMDiffOn.comp (hcs.mono inter_subset_left) (fun _ hx => hx.2)
  refine ⟨fun x => ψ (c x), W, hW, hqW, hτ, hψq, ?_⟩
  intro x hx
  have hr := hroot (c x) hx.2
  have hCx : C (c x, ψ (c x)) = (x, ψ (c x)) := Prod.ext (c.left_inv hx.1) rfl
  constructor
  · have hh := hr.1.2
    change C (c x, ψ (c x)) ∈ U at hh
    rwa [hCx] at hh
  · have hh := hr.2
    change F (C (c x, ψ (c x))) = F (C (c q, t)) at hh
    rwa [hCx, hCt] at hh

theorem exists_smooth_flow_levelTime
    (ϕ : Flow ℝ M)
    (hϕ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun z : ℝ × M => ϕ z.1 z.2))
    {f : M → ℝ} {U : Set M} (hU : IsOpen U) (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U)
    {q : M} {t : ℝ} (hcross : ϕ t q ∈ U) {a : ℝ}
    (htime : HasDerivAt (fun s => f (ϕ s q)) a t) (ha : a ≠ 0) :
    ∃ τ : M → ℝ, ∃ W : Set M, IsOpen W ∧ q ∈ W ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ τ W ∧ τ q = t ∧
      ∀ x ∈ W, ϕ (τ x) x ∈ U ∧ f (ϕ (τ x) x) = f (ϕ t q) := by
  let P : M × ℝ → M := fun z => ϕ z.2 z.1
  have hP : ContMDiff (I.prod 𝓘(ℝ, ℝ)) I ∞ P :=
    hϕ.comp (contMDiff_snd.prodMk contMDiff_fst)
  exact exists_smooth_scalar_root_manifold (hU.preimage hP.continuous)
    (hf.comp hP.contMDiffOn (fun _ hx => hx)) hcross htime ha

theorem exists_smooth_extension_unique_flow_levelTime
    (ϕ : Flow ℝ M)
    (hϕ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun z : ℝ × M => ϕ z.1 z.2))
    {f : M → ℝ} {U : Set M} (hU : IsOpen U) (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U)
    (τ : M → ℝ) (S : Set M) (r : ℝ) {q : M}
    (hcross : ϕ (τ q) q ∈ U) (hlevel : f (ϕ (τ q) q) = r)
    {a : ℝ} (htime : HasDerivAt (fun s => f (ϕ s q)) a (τ q)) (ha : a ≠ 0)
    (hunique : ∀ x ∈ S, ∀ s : ℝ, f (ϕ s x) = r → s = τ x) :
    ∃ σ : M → ℝ, ∃ W : Set M, IsOpen W ∧ q ∈ W ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ σ W ∧ σ q = τ q ∧ EqOn τ σ (W ∩ S) ∧
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ τ (W ∩ S) ∧
      ∀ x ∈ W, ϕ (σ x) x ∈ U ∧ f (ϕ (σ x) x) = r := by
  obtain ⟨σ, W, hW, hqW, hσ, hσq, hroot⟩ := exists_smooth_flow_levelTime ϕ hϕ hU hf hcross htime ha
  have heq : EqOn τ σ (W ∩ S) := by
    intro x hx
    exact (hunique x hx.2 (σ x) ((hroot x hx.1).2.trans hlevel)).symm
  refine ⟨σ, W, hW, hqW, hσ, hσq, heq, (hσ.mono inter_subset_left).congr heq, ?_⟩
  intro x hx
  exact ⟨(hroot x hx).1, (hroot x hx).2.trans hlevel⟩

theorem contMDiffWithinAt_unique_flow_levelTime
    (ϕ : Flow ℝ M)
    (hϕ : ContMDiff (𝓘(ℝ, ℝ).prod I) I ∞ (fun z : ℝ × M => ϕ z.1 z.2))
    {f : M → ℝ} {U : Set M} (hU : IsOpen U) (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U)
    (τ : M → ℝ) (S : Set M) (r : ℝ) {q : M}
    (hcross : ϕ (τ q) q ∈ U) (hlevel : f (ϕ (τ q) q) = r)
    {a : ℝ} (htime : HasDerivAt (fun s => f (ϕ s q)) a (τ q)) (ha : a ≠ 0)
    (hunique : ∀ x ∈ S, ∀ s : ℝ, f (ϕ s x) = r → s = τ x) :
    ContMDiffWithinAt I 𝓘(ℝ, ℝ) ∞ τ S q := by
  obtain ⟨σ, W, hW, hqW, hσ, hσq, heq, _, _⟩ :=
    exists_smooth_extension_unique_flow_levelTime ϕ hϕ hU hf τ S r hcross hlevel htime ha hunique
  have hev : τ =ᶠ[𝓝[S] q] σ := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (hW.mem_nhds hqW)] with x hxS hxW
    exact heq ⟨hxW, hxS⟩
  exact (hσ.contMDiffAt (hW.mem_nhds hqW)).contMDiffWithinAt.congr_of_eventuallyEq hev hσq.symm

end Manifold

end DifferentialGeometry.Geometry.Topology
