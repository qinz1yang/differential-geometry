import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.LocalDiffeomorph
import DifferentialGeometry.Topology.DirectLimit
import DifferentialGeometry.Topology.FiberBundleT2

set_option autoImplicit false

noncomputable section

universe u uE uH

namespace DifferentialGeometry

open Set Topology
open scoped Manifold ContDiff

namespace SeqSystem

section Charted

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {A : ℕ → Type u} [∀ k, TopologicalSpace (A k)] [∀ k, ChartedSpace H (A k)]
  [∀ k, Nonempty (A k)]
variable (S : SeqSystem A)

def inclHomeo (k : ℕ) : OpenPartialHomeomorph (A k) S.Lim :=
  (S.incl_isOpenEmb k).toOpenPartialHomeomorph (S.incl k)

@[simp] theorem inclHomeo_apply (k : ℕ) (x : A k) : S.inclHomeo k x = S.incl k x := rfl

@[simp] theorem inclHomeo_source (k : ℕ) : (S.inclHomeo k).source = univ :=
  (S.incl_isOpenEmb k).toOpenPartialHomeomorph_source (S.incl k)

@[simp] theorem inclHomeo_target (k : ℕ) : (S.inclHomeo k).target = range (S.incl k) :=
  (S.incl_isOpenEmb k).toOpenPartialHomeomorph_target (S.incl k)

theorem inclHomeo_symm_apply (k : ℕ) (x : A k) :
    (S.inclHomeo k).symm (S.incl k x) = x :=
  (S.incl_isOpenEmb k).toOpenPartialHomeomorph_left_inv (S.incl k)

def limChart (k : ℕ) (a : A k) : OpenPartialHomeomorph S.Lim H :=
  (S.inclHomeo k).symm.trans (chartAt H a)

theorem mem_limChart_source (k : ℕ) (a : A k) :
    S.incl k a ∈ (S.limChart (H := H) k a).source := by
  rw [limChart, OpenPartialHomeomorph.trans_source]
  refine ⟨?_, ?_⟩
  · rw [OpenPartialHomeomorph.symm_source, inclHomeo_target]
    exact ⟨a, rfl⟩
  · change (S.inclHomeo k).symm (S.incl k a) ∈ (chartAt H a).source
    rw [inclHomeo_symm_apply]
    exact mem_chart_source H a


omit [∀ (k : ℕ), Nonempty (A k)] in
theorem exists_sigma_incl (z : S.Lim) : ∃ p : Σ k, A k, S.incl p.1 p.2 = z := by
  obtain ⟨k, x, hx⟩ := S.exists_incl_eq z
  exact ⟨⟨k, x⟩, hx⟩


def rep (z : S.Lim) : Σ k, A k := (S.exists_sigma_incl z).choose

omit [∀ (k : ℕ), Nonempty (A k)] in
theorem incl_rep (z : S.Lim) : S.incl (S.rep z).1 (S.rep z).2 = z :=
  (S.exists_sigma_incl z).choose_spec

instance instChartedSpaceLim : ChartedSpace H S.Lim where
  atlas := ⋃ (k : ℕ), ⋃ (a : A k), {S.limChart k a}
  chartAt z := S.limChart (S.rep z).1 (S.rep z).2
  mem_chart_source z := by
    have hz : S.incl (S.rep z).1 (S.rep z).2 = z := S.incl_rep z
    have hmem := S.mem_limChart_source (H := H) (S.rep z).1 (S.rep z).2
    rwa [hz] at hmem
  chart_mem_atlas z := by
    simp only [mem_iUnion, mem_singleton_iff]
    exact ⟨(S.rep z).1, (S.rep z).2, rfl⟩

theorem chartAt_lim (z : S.Lim) :
    chartAt H z = S.limChart (S.rep z).1 (S.rep z).2 := rfl

theorem limChart_mem_atlas (k : ℕ) (a : A k) : S.limChart k a ∈ atlas H S.Lim := by
  change S.limChart k a ∈ ⋃ (k : ℕ) (a : A k), {S.limChart k a}
  simp only [mem_iUnion, mem_singleton_iff]
  exact ⟨k, a, rfl⟩

theorem mem_atlas_iff {e : OpenPartialHomeomorph S.Lim H} :
    e ∈ atlas H S.Lim ↔ ∃ (k : ℕ) (a : A k), e = S.limChart k a := by
  change e ∈ ⋃ (k : ℕ) (a : A k), {S.limChart k a} ↔ _
  simp only [mem_iUnion, mem_singleton_iff]


instance instSigmaCompactSpaceLim [∀ k, SigmaCompactSpace (A k)] :
    SigmaCompactSpace S.Lim := S.sigmaCompact


instance instT2SpaceLim [∀ k, T2Space (A k)] : T2Space S.Lim := S.t2Space

instance instNonemptyLim : Nonempty S.Lim :=
  ⟨S.incl 0 (Classical.arbitrary (A 0))⟩

instance instPreconnectedLim [∀ k, PreconnectedSpace (A k)] :
    PreconnectedSpace S.Lim := by
  constructor
  rw [← S.iUnion_range_incl]
  refine isPreconnected_iUnion ⟨S.incl 0 (Classical.arbitrary (A 0)), ?_⟩ fun k => ?_
  · simp only [mem_iInter]
    intro k
    exact S.range_incl_mono (Nat.zero_le k) ⟨Classical.arbitrary (A 0), rfl⟩
  · have h := (isPreconnected_univ (α := A k)).image (S.incl k)
      (S.continuous_incl k).continuousOn
    rwa [Set.image_univ] at h

instance instConnectedSpaceLim [∀ k, PreconnectedSpace (A k)] :
    ConnectedSpace S.Lim where
  toPreconnectedSpace := S.instPreconnectedLim
  toNonempty := S.instNonemptyLim

def transitionHomeo (k ℓ : ℕ) : OpenPartialHomeomorph (A k) (A ℓ) :=
  (S.inclHomeo k).trans (S.inclHomeo ℓ).symm

theorem mem_transitionHomeo_source {k ℓ : ℕ} {w : A k} :
    w ∈ (S.transitionHomeo k ℓ).source ↔ S.incl k w ∈ range (S.incl ℓ) := by
  rw [transitionHomeo, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    inclHomeo_source, inclHomeo_target, univ_inter, mem_preimage, inclHomeo_apply]

theorem transitionHomeo_apply {k ℓ : ℕ} (w : A k) :
    S.transitionHomeo k ℓ w = (S.inclHomeo ℓ).symm (S.incl k w) := by
  rw [transitionHomeo, OpenPartialHomeomorph.trans_apply, inclHomeo_apply]

theorem incl_transitionHomeo {k ℓ : ℕ} {w : A k} (hw : w ∈ (S.transitionHomeo k ℓ).source) :
    S.incl ℓ (S.transitionHomeo k ℓ w) = S.incl k w := by
  have hmem : S.incl k w ∈ (S.inclHomeo ℓ).target := by
    rw [inclHomeo_target]; exact (S.mem_transitionHomeo_source).mp hw
  rw [transitionHomeo_apply, ← inclHomeo_apply, OpenPartialHomeomorph.right_inv _ hmem]

theorem limChart_symm_trans (k ℓ : ℕ) (a : A k) (b : A ℓ) :
    (S.limChart k a).symm.trans (S.limChart ℓ b)
      = ((chartAt H a).symm.trans (S.transitionHomeo k ℓ)).trans (chartAt H b) := by
  simp only [limChart, transitionHomeo, OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm, OpenPartialHomeomorph.trans_assoc]

end Charted

end SeqSystem

structure SmoothSeqSystem
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    (A : ℕ → Type u) [∀ k, TopologicalSpace (A k)] [∀ k, ChartedSpace H (A k)]
    [∀ k, IsManifold I ∞ (A k)] [∀ k, Nonempty (A k)]
    extends SeqSystem A where
  contMDiff_F : ∀ {k ℓ : ℕ} (h : k ≤ ℓ), ContMDiff I I ∞ (toSeqSystem.F h)
  contMDiffOn_invFun_F : ∀ {k ℓ : ℕ} (h : k ≤ ℓ),
    ContMDiffOn I I ∞ (Function.invFun (toSeqSystem.F h)) (Set.range (toSeqSystem.F h))

theorem modelSpace_contDiffOn
    {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type uH} [TopologicalSpace H] [Nonempty H] {I : ModelWithCorners ℝ E H}
    {f : H → H} {s : Set H} (hf : ContMDiffOn I I ∞ f s) :
    ContDiffOn ℝ ∞ (↑I ∘ f ∘ ↑I.symm) (↑I.symm ⁻¹' s ∩ range ↑I) := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty H)
  have hs : s ⊆ (extChartAt I x₀).source := by
    simp only [extChartAt_source, chartAt_self_eq, OpenPartialHomeomorph.refl_source,
      subset_univ]
  have h2s : MapsTo f s (extChartAt I x₀).source := by
    simp only [extChartAt_source, chartAt_self_eq, OpenPartialHomeomorph.refl_source]
    exact mapsTo_univ _ _
  have h := (contMDiffOn_iff_of_subset_source' hs h2s).mp hf
  have hset : extChartAt I x₀ '' s = ↑I.symm ⁻¹' s ∩ range ↑I := by
    rw [← I.image_eq]
    apply Set.image_congr'
    intro z
    simp only [extChartAt_coe, chartAt_self_eq, OpenPartialHomeomorph.refl_apply,
      Function.comp_apply, id_eq]
  rw [hset] at h
  refine h.congr (fun z _ => ?_)
  simp only [Function.comp_apply, extChartAt_coe, extChartAt_coe_symm, chartAt_self_eq,
    OpenPartialHomeomorph.refl_symm, OpenPartialHomeomorph.refl_apply, id_eq]

namespace SmoothSeqSystem

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {A : ℕ → Type u} [∀ k, TopologicalSpace (A k)] [∀ k, ChartedSpace H (A k)]
  [∀ k, IsManifold I ∞ (A k)] [∀ k, Nonempty (A k)]
variable (S : SmoothSeqSystem I A)


omit [∀ (k : ℕ), IsManifold I ∞ (A k)] [∀ (k : ℕ), Nonempty (A k)] in
theorem succMap_contMDiff (f : ∀ k, A k → A (k + 1))
    (hf : ∀ k, ContMDiff I I ∞ (f k)) {k ℓ : ℕ} (h : k ≤ ℓ) :
    ContMDiff I I ∞ (SeqSystem.succMap f h) := by
  induction ℓ, h using Nat.le_induction with
  | base =>
      change ContMDiff I I ∞ (SeqSystem.succMap f (Nat.le_refl k))
      have hfun : SeqSystem.succMap f (Nat.le_refl k) = id := by
        funext x
        exact Nat.leRecOn_self x
      rw [hfun]
      exact contMDiff_id
  | succ ℓ hkℓ ih =>
      have hfun : SeqSystem.succMap f (Nat.le.step hkℓ) =
          f ℓ ∘ SeqSystem.succMap f hkℓ := by
        funext x
        exact Nat.leRecOn_succ hkℓ x
      rw [hfun]
      exact (hf ℓ).comp ih

omit [∀ (k : ℕ), IsManifold I ∞ (A k)] in
theorem succMap_inv_mdiff (f : ∀ k, A k → A (k + 1))
    (hemb : ∀ k, IsOpenEmbedding (f k))
    (hfInv : ∀ k, ContMDiffOn I I ∞ (Function.invFun (f k)) (Set.range (f k)))
    {k ℓ : ℕ} (h : k ≤ ℓ) :
    ContMDiffOn I I ∞ (Function.invFun (SeqSystem.succMap f h))
      (Set.range (SeqSystem.succMap f h)) := by
  induction ℓ, h using Nat.le_induction with
  | base =>
      change ContMDiffOn I I ∞
        (Function.invFun (SeqSystem.succMap f (Nat.le_refl k)))
        (Set.range (SeqSystem.succMap f (Nat.le_refl k)))
      have hfun : SeqSystem.succMap f (Nat.le_refl k) = id := by
        funext x
        exact Nat.leRecOn_self x
      rw [hfun]
      have hinvId : Function.invFun (id : A k → A k) = id := by
        funext x
        exact Function.leftInverse_invFun Function.injective_id x
      rw [hinvId]
      simpa using
        (contMDiff_id : ContMDiff I I ∞ (id : A k → A k)).contMDiffOn
  | succ ℓ hkℓ ih =>
      let prev : A k → A ℓ := SeqSystem.succMap f hkℓ
      have hfun : SeqSystem.succMap f (Nat.le.step hkℓ) = f ℓ ∘ prev := by
        funext x
        exact Nat.leRecOn_succ hkℓ x
      rw [hfun]
      have hprev : Function.Injective prev :=
        (SeqSystem.succMap_isOpenEmb f hemb hkℓ).injective
      have htotal : Function.Injective (f ℓ ∘ prev) := (hemb ℓ).injective.comp hprev
      have hinvTotal : ContMDiffOn I I ∞ (Function.invFun (f ℓ))
          (Set.range (f ℓ ∘ prev)) := by
        refine (hfInv ℓ).mono ?_
        rintro y ⟨x, rfl⟩
        exact ⟨prev x, rfl⟩
      have hmaps : Set.MapsTo (Function.invFun (f ℓ)) (Set.range (f ℓ ∘ prev))
          (Set.range prev) := by
        rintro y ⟨x, rfl⟩
        simp only [Function.comp_apply]
        rw [Function.leftInverse_invFun (hemb ℓ).injective]
        exact ⟨x, rfl⟩
      have hiPrev : ContMDiffOn I I ∞ (Function.invFun prev) (Set.range prev) := by
        simpa only [prev] using ih
      have hsmooth := hiPrev.comp hinvTotal hmaps
      refine hsmooth.congr (fun y hy => ?_)
      obtain ⟨x, rfl⟩ := hy
      simp only [Function.comp_apply]
      rw [Function.leftInverse_invFun (hemb ℓ).injective,
        Function.leftInverse_invFun hprev]
      change Function.invFun (f ℓ ∘ prev) ((f ℓ ∘ prev) x) = x
      exact Function.leftInverse_invFun htotal x

def ofSucc (f : ∀ k, A k → A (k + 1))
    (hemb : ∀ k, IsOpenEmbedding (f k))
    (hf : ∀ k, ContMDiff I I ∞ (f k))
    (hfInv : ∀ k, ContMDiffOn I I ∞ (Function.invFun (f k)) (Set.range (f k))) :
    SmoothSeqSystem I A where
  toSeqSystem := SeqSystem.ofSucc f hemb
  contMDiff_F h := succMap_contMDiff f hf h
  contMDiffOn_invFun_F h := succMap_inv_mdiff f hemb hfInv h


@[simp] theorem ofSucc_F_succ (f : ∀ k, A k → A (k + 1))
    (hemb : ∀ k, IsOpenEmbedding (f k))
    (hf : ∀ k, ContMDiff I I ∞ (f k))
    (hfInv : ∀ k, ContMDiffOn I I ∞ (Function.invFun (f k)) (Set.range (f k)))
    (k : ℕ) :
    (ofSucc (I := I) f hemb hf hfInv).toSeqSystem.F (Nat.le_succ k) = f k := by
  funext x
  change SeqSystem.succMap f (Nat.le_succ k) x = f k x
  unfold SeqSystem.succMap
  rw [show Nat.le_succ k = Nat.le.step (Nat.le_refl k) by rfl,
    Nat.leRecOn_succ (Nat.le_refl k) x, Nat.leRecOn_self]

theorem transitionHomeo_contMDiffOn (k ℓ : ℕ) :
    ContMDiffOn I I ∞ (S.toSeqSystem.transitionHomeo k ℓ)
      (S.toSeqSystem.transitionHomeo k ℓ).source := by
  set m := max k ℓ with hm
  have hkm : k ≤ m := le_max_left k ℓ
  have hℓm : ℓ ≤ m := le_max_right k ℓ
  have hFeq : ∀ w ∈ (S.toSeqSystem.transitionHomeo k ℓ).source,
      S.toSeqSystem.F hℓm (S.toSeqSystem.transitionHomeo k ℓ w) = S.toSeqSystem.F hkm w := by
    intro w hw
    apply S.toSeqSystem.incl_injective m
    rw [S.toSeqSystem.incl_comp hℓm, S.toSeqSystem.incl_comp hkm,
      S.toSeqSystem.incl_transitionHomeo hw]
  have hpt : ∀ w ∈ (S.toSeqSystem.transitionHomeo k ℓ).source,
      S.toSeqSystem.transitionHomeo k ℓ w
        = (Function.invFun (S.toSeqSystem.F hℓm) ∘ S.toSeqSystem.F hkm) w := by
    intro w hw
    change S.toSeqSystem.transitionHomeo k ℓ w = Function.invFun (S.toSeqSystem.F hℓm)
      (S.toSeqSystem.F hkm w)
    rw [← hFeq w hw,
      Function.leftInverse_invFun (S.toSeqSystem.isOpenEmb hℓm).injective]
  have hrange : (S.toSeqSystem.transitionHomeo k ℓ).source ⊆
      S.toSeqSystem.F hkm ⁻¹' range (S.toSeqSystem.F hℓm) := by
    intro w hw
    exact ⟨S.toSeqSystem.transitionHomeo k ℓ w, hFeq w hw⟩
  refine ContMDiffOn.congr ?_ (fun w hw => hpt w hw)
  exact (S.contMDiffOn_invFun_F hℓm).comp ((S.contMDiff_F hkm).contMDiffOn) hrange

instance instIsManifoldLim : IsManifold I ∞ S.toSeqSystem.Lim := by
  haveI : Nonempty H :=
    ⟨chartAt H (Classical.arbitrary (A 0)) (Classical.arbitrary (A 0))⟩
  apply isManifold_of_contDiffOn I ∞ S.toSeqSystem.Lim
  intro e₁ e₂ h₁ h₂
  obtain ⟨k, a, rfl⟩ := (S.toSeqSystem.mem_atlas_iff).mp h₁
  obtain ⟨ℓ, b, rfl⟩ := (S.toSeqSystem.mem_atlas_iff).mp h₂
  rw [S.toSeqSystem.limChart_symm_trans]
  set T' := ((chartAt H a).symm.trans (S.toSeqSystem.transitionHomeo k ℓ)).trans (chartAt H b)
    with hT'
  apply modelSpace_contDiffOn
  have key : ContMDiffOn I I ∞
      (⇑(chartAt H b) ∘ ⇑(S.toSeqSystem.transitionHomeo k ℓ) ∘ ⇑(chartAt H a).symm)
      (((chartAt H a).target ∩ (chartAt H a).symm ⁻¹' (S.toSeqSystem.transitionHomeo k ℓ).source) ∩
        (⇑(S.toSeqSystem.transitionHomeo k ℓ) ∘ ⇑(chartAt H a).symm) ⁻¹' (chartAt H b).source) :=
    (contMDiffOn_chart).comp' ((S.transitionHomeo_contMDiffOn k ℓ).comp' contMDiffOn_chart_symm)
  have hsrc : T'.source =
      ((chartAt H a).target ∩ (chartAt H a).symm ⁻¹' (S.toSeqSystem.transitionHomeo k ℓ).source) ∩
        (⇑(S.toSeqSystem.transitionHomeo k ℓ) ∘ ⇑(chartAt H a).symm) ⁻¹' (chartAt H b).source := by
    simp only [hT', OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      OpenPartialHomeomorph.coe_trans]
  rw [hsrc]
  refine key.congr (fun z _ => ?_)
  rw [hT']
  simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply]

theorem contMDiff_incl (k : ℕ) : ContMDiff I I ∞ (S.toSeqSystem.incl k) := by
  intro a
  have hchart : ContMDiffAt I I ∞ (chartAt H a) a :=
    contMDiffOn_chart.contMDiffAt ((chartAt H a).open_source.mem_nhds (mem_chart_source H a))
  have hlim_max : S.toSeqSystem.limChart k a ∈ IsManifold.maximalAtlas I ∞ S.toSeqSystem.Lim :=
    IsManifold.subset_maximalAtlas (S.toSeqSystem.limChart_mem_atlas k a)
  have htarget : chartAt H a a ∈ (S.toSeqSystem.limChart k a).target := by
    have hmem : S.toSeqSystem.incl k a ∈ (S.toSeqSystem.limChart k a).source :=
      S.toSeqSystem.mem_limChart_source (H := H) k a
    have hval0 : S.toSeqSystem.limChart k a (S.toSeqSystem.incl k a) = chartAt H a a := by
      unfold SeqSystem.limChart
      rw [OpenPartialHomeomorph.trans_apply, SeqSystem.inclHomeo_symm_apply]
    rw [← hval0]
    exact (S.toSeqSystem.limChart k a).map_source hmem
  have hsymm : ContMDiffAt I I ∞ (S.toSeqSystem.limChart k a).symm (chartAt H a a) :=
    contMDiffAt_symm_of_mem_maximalAtlas hlim_max htarget
  refine (hsymm.comp a hchart).congr_of_eventuallyEq ?_
  filter_upwards [(chartAt H a).open_source.mem_nhds (mem_chart_source H a)] with a' ha'
  have hmem : S.toSeqSystem.incl k a' ∈ (S.toSeqSystem.limChart (H := H) k a).source := by
    unfold SeqSystem.limChart
    rw [OpenPartialHomeomorph.trans_source]
    refine ⟨?_, ?_⟩
    · rw [OpenPartialHomeomorph.symm_source, SeqSystem.inclHomeo_target]; exact ⟨a', rfl⟩
    · change (S.toSeqSystem.inclHomeo k).symm (S.toSeqSystem.incl k a') ∈ (chartAt H a).source
      rw [SeqSystem.inclHomeo_symm_apply]; exact ha'
  have hval : S.toSeqSystem.limChart k a (S.toSeqSystem.incl k a') = chartAt H a a' := by
    unfold SeqSystem.limChart
    rw [OpenPartialHomeomorph.trans_apply, SeqSystem.inclHomeo_symm_apply]
  change S.toSeqSystem.incl k a' = (S.toSeqSystem.limChart k a).symm (chartAt H a a')
  rw [← hval, (S.toSeqSystem.limChart k a).left_inv hmem]

theorem contMDiffAt_invIncl (k : ℕ) {z : S.toSeqSystem.Lim}
    (hz : z ∈ Set.range (S.toSeqSystem.incl k)) :
    ContMDiffAt I I ∞ (Function.invFun (S.toSeqSystem.incl k)) z := by
  obtain ⟨a, rfl⟩ := hz
  have hchart : ContMDiffAt I I ∞ (S.toSeqSystem.limChart k a) (S.toSeqSystem.incl k a) :=
    contMDiffAt_of_mem_maximalAtlas
      (IsManifold.subset_maximalAtlas (S.toSeqSystem.limChart_mem_atlas k a))
      (S.toSeqSystem.mem_limChart_source (H := H) k a)
  have hval0 : S.toSeqSystem.limChart k a (S.toSeqSystem.incl k a) = chartAt H a a := by
    unfold SeqSystem.limChart
    rw [OpenPartialHomeomorph.trans_apply, SeqSystem.inclHomeo_symm_apply]
  have hsymm : ContMDiffAt I I ∞ (chartAt H a).symm
      (S.toSeqSystem.limChart k a (S.toSeqSystem.incl k a)) := by
    rw [hval0]
    exact contMDiffAt_symm_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas a)
      ((chartAt H a).map_source (mem_chart_source H a))
  refine (hsymm.comp _ hchart).congr_of_eventuallyEq ?_
  filter_upwards [(S.toSeqSystem.limChart (H := H) k a).open_source.mem_nhds
    (S.toSeqSystem.mem_limChart_source (H := H) k a)] with z' hz'
  rw [SeqSystem.limChart, OpenPartialHomeomorph.trans_source] at hz'
  obtain ⟨hz'r, hz'c⟩ := hz'
  rw [OpenPartialHomeomorph.symm_source, S.toSeqSystem.inclHomeo_target] at hz'r
  have hz'eq : S.toSeqSystem.incl k ((S.toSeqSystem.inclHomeo k).symm z') = z' := by
    have := (S.toSeqSystem.inclHomeo k).right_inv
      (by rw [S.toSeqSystem.inclHomeo_target]; exact hz'r)
    rwa [← S.toSeqSystem.inclHomeo_apply]
  have hmem_c : (S.toSeqSystem.inclHomeo k).symm z' ∈ (chartAt H a).source := hz'c
  rw [← hz'eq, Function.leftInverse_invFun (S.toSeqSystem.incl_injective k)]
  change (S.toSeqSystem.inclHomeo k).symm z'
    = ((chartAt H a).symm ∘ (S.toSeqSystem.limChart k a)) (S.toSeqSystem.incl k _)
  have hval : S.toSeqSystem.limChart k a
      (S.toSeqSystem.incl k ((S.toSeqSystem.inclHomeo k).symm z'))
        = chartAt H a ((S.toSeqSystem.inclHomeo k).symm z') := by
    unfold SeqSystem.limChart
    rw [OpenPartialHomeomorph.trans_apply, SeqSystem.inclHomeo_symm_apply]
  simp only [Function.comp_apply, hval, (chartAt H a).left_inv hmem_c]

noncomputable def inclPartialDiffeo (k : ℕ) :
    PartialDiffeomorph I I S.toSeqSystem.Lim (A k) (∞ : WithTop ℕ∞) where
  toFun := Function.invFun (S.toSeqSystem.incl k)
  invFun := S.toSeqSystem.incl k
  source := Set.range (S.toSeqSystem.incl k)
  target := Set.univ
  map_source' := fun _ _ => Set.mem_univ _
  map_target' := fun a _ => ⟨a, rfl⟩
  left_inv' := fun _ hz => Function.invFun_eq hz
  right_inv' := fun a _ => Function.leftInverse_invFun (S.toSeqSystem.incl_injective k) a
  open_source := (S.toSeqSystem.incl_isOpenEmb k).isOpen_range
  open_target := isOpen_univ
  contMDiffOn_toFun := fun _ hz => (S.contMDiffAt_invIncl k hz).contMDiffWithinAt
  contMDiffOn_invFun := fun a _ => ((S.contMDiff_incl k) a).contMDiffWithinAt

@[simp] theorem inclPartialDiffeo_source (k : ℕ) :
    (S.inclPartialDiffeo k).source = Set.range (S.toSeqSystem.incl k) := rfl

@[simp] theorem inclPartialDiffeo_apply (k : ℕ) (z : S.toSeqSystem.Lim) :
    S.inclPartialDiffeo k z = Function.invFun (S.toSeqSystem.incl k) z := rfl

theorem invIncl_incl_le {j k : ℕ} (hjk : j ≤ k) (a : A j) :
    Function.invFun (S.toSeqSystem.incl k) (S.toSeqSystem.incl j a)
      = S.toSeqSystem.F hjk a := by
  conv_lhs => rw [← S.toSeqSystem.incl_comp hjk a]
  exact Function.leftInverse_invFun (S.toSeqSystem.incl_injective k) _

instance instT2SpaceTangentBundleLim [∀ k, T2Space (A k)] :
    T2Space (TangentBundle I S.toSeqSystem.Lim) := by
  haveI : IsManifold I 1 S.toSeqSystem.Lim :=
    IsManifold.of_le (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  infer_instance

end SmoothSeqSystem

end DifferentialGeometry
