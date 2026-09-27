import DifferentialGeometry.Topology.CollarSeparator
import DifferentialGeometry.Topology.Manifold.CollarStep
import DifferentialGeometry.Topology.Manifold.OpenFunctionExtension
import DifferentialGeometry.Analysis.Calculus.Cutoff.IntervalCutoffEstimate
import Mathlib.Geometry.Manifold.Diffeomorph

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.Manifold

theorem exists_uniform_smooth_step_of_product_collar :
    ∃ C : ℝ, 0 < C ∧ ∀
    {E F H G N M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] [TopologicalSpace G]
    (I : ModelWithCorners ℝ E H) (J : ModelWithCorners ℝ F G)
    [TopologicalSpace N] [ChartedSpace H N] [CompactSpace N]
    [TopologicalSpace M] [ChartedSpace G M] [T2Space M],
    ∀ (O : TopologicalSpace.Opens (N × ℝ)) (V : TopologicalSpace.Opens M)
    (Φ : O ≃ₘ⟮I.prod 𝓘(ℝ), J⟯ V)
    (l r : ℝ) (hlr : l < r) (hcollar : (univ : Set N) ×ˢ Icc l r ⊆ O)
    (P Q : Set M), IsClosed P → IsClosed Q → Disjoint P Q →
    let e : N × Icc l r → M := fun x ↦
      Φ ⟨(x.1, (x.2 : ℝ)), hcollar ⟨mem_univ _, x.2.property⟩⟩
    let q : M → ℝ := Subtype.val.extend
      (fun x : V ↦ ((Φ.symm x : O) : N × ℝ).2) (fun _ ↦ 0)
    P ∪ range e ∪ Q = univ →
    P ∩ range e ⊆ range (fun p : N ↦ e (p, ⟨l, le_rfl, hlr.le⟩)) →
    Q ∩ range e ⊆ range (fun p : N ↦ e (p, ⟨r, hlr.le, le_rfl⟩)) →
    ∀ a b : ℝ, l < a → a < b → b < r →
      let K := e '' {x | a ≤ (x.2 : ℝ) ∧ (x.2 : ℝ) ≤ b}
      ∃ (β : ℝ → ℝ) (θM : M → ℝ),
        ContDiff ℝ ∞ β ∧ Monotone β ∧ ContMDiff J 𝓘(ℝ) ∞ θM ∧
        (∀ x, θM x ∈ Icc (0 : ℝ) 1) ∧
        (∀ x ∈ P, θM x = 0) ∧ (∀ x ∈ Q, θM x = 1) ∧
        (∀ x, θM (e x) = β (x.2 : ℝ)) ∧
        (∀ t, t ≤ a → β t = 0) ∧ (∀ t, b ≤ t → β t = 1) ∧
        IsCompact K ∧ (∀ x ∉ K, θM x = 0 ∨ θM x = 1) ∧
        (∀ x ∉ K, mvfderiv J θM x = 0) ∧
        ∀ x (v : TangentSpace J x),
          |mvfderiv J θM x v| ≤ (C / (b - a)) * |mvfderiv J q x v| := by
  classical
  obtain ⟨C, hC, hsteps⟩ := DifferentialGeometry.Analysis.exists_uniform_smooth_interval_step
  refine ⟨C, hC, ?_⟩
  intro E F H G N M _ _ _ _ _ _ I J _ _ _ _ _ _
    O V Φ l r hlr hcollar P Q hP hQ hPQ e q hcover hleft hright
  let ι : N × Icc l r → O := fun x ↦
    ⟨(x.1, (x.2 : ℝ)), hcollar ⟨mem_univ _, x.2.property⟩⟩
  let f : V → ℝ := fun x ↦ ((Φ.symm x : O) : N × ℝ).2
  let F : O → M := fun x ↦ Φ x
  let A : Set O := {x | l < (x : N × ℝ).2 ∧ (x : N × ℝ).2 < r}
  let U : Set M := F '' A
  have hι : Continuous ι :=
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  have he : Continuous e := continuous_subtype_val.comp (Φ.continuous.comp hι)
  have hinj : Function.Injective e := by
    intro x y h
    have hΦ : Φ (ι x) = Φ (ι y) := Subtype.ext h
    have hi := congrArg (fun z : O ↦ (z : N × ℝ)) (Φ.injective hΦ)
    have hfst := congrArg Prod.fst hi
    have hsnd := congrArg Prod.snd hi
    exact Prod.ext hfst (Subtype.ext hsnd)
  have hA : IsOpen A := isOpen_Ioo.preimage (continuous_snd.comp continuous_subtype_val)
  have hU : IsOpen U := (V.isOpenEmbedding'.isOpenMap.comp Φ.toHomeomorph.isOpenMap) A hA
  have hf : ContMDiff J 𝓘(ℝ) ∞ f :=
    contMDiff_snd.comp (contMDiff_subtype_val.comp Φ.symm.contMDiff)
  have hqV : ContMDiffOn J 𝓘(ℝ) ∞ q (V : Set M) := by
    have h := contMDiffOn_extend_from_open V f (fun _ ↦ 0) isOpen_univ hf.contMDiffOn
    have hr : (Subtype.val : V → M) '' univ = (V : Set M) := by
      ext x
      exact ⟨fun ⟨y, _, hy⟩ ↦ hy ▸ y.property, fun hx ↦ ⟨⟨x, hx⟩, mem_univ _, rfl⟩⟩
    rw [hr] at h
    exact h
  have hUV : U ⊆ V := by
    rintro x ⟨y, _, rfl⟩
    exact (Φ y).property
  have hq : ContMDiffOn J 𝓘(ℝ) ∞ q U := hqV.mono hUV
  have hqF (x : O) : q (F x) = (x : N × ℝ).2 := by
    dsimp only [q, F]
    rw [Subtype.val_injective.extend_apply]
    simp only [Φ.symm_apply_apply]
  have hqe (x : N × Icc l r) : q (e x) = (x.2 : ℝ) := hqF (ι x)
  intro a b hla hab hbr K
  let c := (a + b) / 2
  have hac : a < c := by dsimp only [c]; linarith only [hab]
  have hcb : c < b := by dsimp only [c]; linarith only [hab]
  have hlc : l < c := hla.trans hac
  have hcr : c < r := hcb.trans hbr
  let L := P ∪ e '' {x | (x.2 : ℝ) ≤ c}
  obtain ⟨hL, _, _, _, hfront, _, hpre, _⟩ :=
    DifferentialGeometry.Topology.closed_sides_of_embedded_collar l c r hlc hcr e he hinj
      P Q hP hQ hPQ hcover hleft hright
  have heU (x : N × Icc l r) (hx : l < (x.2 : ℝ) ∧ (x.2 : ℝ) < r) : e x ∈ U :=
    ⟨ι x, hx, rfl⟩
  have hband : U ∩ q ⁻¹' Icc a b = K := by
    ext x
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hxy⟩
      have ht : a ≤ (y : N × ℝ).2 ∧ (y : N × ℝ).2 ≤ b := by
        simpa only [mem_preimage, mem_Icc, hqF] using hxy
      refine ⟨((y : N × ℝ).1, ⟨(y : N × ℝ).2, hy.1.le, hy.2.le⟩), ht, ?_⟩
      apply congrArg F
      exact Subtype.ext rfl
    · rintro ⟨y, hy, rfl⟩
      exact ⟨heU y ⟨hla.trans_le hy.1, hy.2.trans_lt hbr⟩,
        by simpa only [mem_preimage, mem_Icc, mem_ofPred_eq, hqe] using hy⟩
  have hK : IsCompact K :=
    ((isClosed_Icc.preimage (continuous_subtype_val.comp continuous_snd)).isCompact).image he
  have hside : ∀ x ∈ U, x ∈ L ↔ q x ≤ c := by
    rintro x ⟨y, hy, rfl⟩
    let z : N × Icc l r := ((y : N × ℝ).1, ⟨(y : N × ℝ).2, hy.1.le, hy.2.le⟩)
    have hez : e z = F y := congrArg F (Subtype.ext rfl)
    rw [← hez, hqe]
    exact Set.ext_iff.mp hpre z
  have hfrontier : frontier L ⊆ U ∩ q ⁻¹' Icc a b := by
    rw [hband]
    intro x hx
    obtain ⟨p, rfl⟩ := hfront hx
    exact ⟨(p, ⟨c, hlc.le, hcr.le⟩), ⟨hac.le, hcb.le⟩, rfl⟩
  have hclosed : IsClosed (U ∩ q ⁻¹' Icc a b) := hband ▸ hK.isClosed
  obtain ⟨β, hβ, hmono, hrange, hzero, hone, hbound⟩ := hsteps a b hab
  let θM := collarStep U L q β
  have hθ : ContMDiff J 𝓘(ℝ) ∞ θM :=
    contMDiff_collarStep hU hL q hq β hβ a c b hac.le hcb.le hside
      hzero hone hclosed hfrontier
  have hPheight (x : N × Icc l r) (hx : e x ∈ P) : (x.2 : ℝ) = l := by
    obtain ⟨p, hp⟩ := hleft ⟨hx, mem_range_self x⟩
    have heq := hinj hp
    have ht := congrArg (fun y : N × Icc l r ↦ (y.2 : ℝ)) heq
    exact ht.symm
  have hQheight (x : N × Icc l r) (hx : e x ∈ Q) : (x.2 : ℝ) = r := by
    obtain ⟨p, hp⟩ := hright ⟨hx, mem_range_self x⟩
    have heq := hinj hp
    have ht := congrArg (fun y : N × Icc l r ↦ (y.2 : ℝ)) heq
    exact ht.symm
  have hPoff : Disjoint P U := by
    apply Set.disjoint_left.mpr
    rintro x hp ⟨y, hy, rfl⟩
    let z : N × Icc l r := ((y : N × ℝ).1, ⟨(y : N × ℝ).2, hy.1.le, hy.2.le⟩)
    have hez : e z = F y := congrArg F (Subtype.ext rfl)
    have hz := hPheight z (hez.symm ▸ hp)
    exact (ne_of_gt hy.1) hz
  have hQoff : Disjoint Q U := by
    apply Set.disjoint_left.mpr
    rintro x hq ⟨y, hy, rfl⟩
    let z : N × Icc l r := ((y : N × ℝ).1, ⟨(y : N × ℝ).2, hy.1.le, hy.2.le⟩)
    have hez : e z = F y := congrArg F (Subtype.ext rfl)
    have hz := hQheight z (hez.symm ▸ hq)
    exact (ne_of_lt hy.2) hz
  have hQL : Disjoint Q L := by
    apply Set.disjoint_left.mpr
    rintro x hqx (hpx | ⟨y, hy, rfl⟩)
    · exact Set.disjoint_left.mp hPQ hpx hqx
    · have ht := hQheight y hqx
      exact (not_le_of_gt hcr) (ht ▸ hy)
  refine ⟨β, θM, hβ, hmono, hθ, collarStep_mem_Icc U L q β hrange,
    ?_, ?_, ?_, hzero, hone, hK, ?_, ?_, ?_⟩
  · intro x hx
    change collarStep U L q β x = 0
    have hxL : x ∈ L := Or.inl hx
    rw [collarStep, if_neg (fun hu ↦ Set.disjoint_left.mp hPoff hx hu),
      if_pos hxL]
  · intro x hx
    change collarStep U L q β x = 1
    rw [collarStep, if_neg (fun hu ↦ Set.disjoint_left.mp hQoff hx hu),
      if_neg (fun hl ↦ Set.disjoint_left.mp hQL hx hl)]
  · intro x
    change collarStep U L q β (e x) = β (x.2 : ℝ)
    by_cases hu : e x ∈ U
    · rw [collarStep, if_pos hu, hqe]
    · by_cases hl : (x.2 : ℝ) ≤ c
      · have hxl : (x.2 : ℝ) ≤ l := by
          by_contra h
          exact hu (heU x ⟨lt_of_not_ge h, hl.trans_lt hcr⟩)
        have hxL : e x ∈ L := Or.inr ⟨x, hl, rfl⟩
        rw [collarStep, if_neg hu, if_pos hxL,
          hzero _ (hxl.trans hla.le)]
      · have hxr : r ≤ (x.2 : ℝ) := by
          by_contra h
          exact hu (heU x ⟨hlc.trans (lt_of_not_ge hl), lt_of_not_ge h⟩)
        have hnL : e x ∉ L := fun h ↦ hl ((Set.ext_iff.mp hpre x).mp h)
        rw [collarStep, if_neg hu, if_neg hnL, hone _ (hbr.le.trans hxr)]
  · intro x hx
    have hout : x ∉ U ∩ q ⁻¹' Icc a b := by rwa [hband]
    by_cases hu : x ∈ U
    · have hqout : ¬ (a ≤ q x ∧ q x ≤ b) := fun h ↦ hout ⟨hu, h⟩
      rcases not_and_or.mp hqout with hlo | hhi
      · left
        change collarStep U L q β x = 0
        rw [collarStep, if_pos hu, hzero _ (lt_of_not_ge hlo).le]
      · right
        change collarStep U L q β x = 1
        rw [collarStep, if_pos hu, hone _ (lt_of_not_ge hhi).le]
    · by_cases hl : x ∈ L
      · left
        change collarStep U L q β x = 0
        rw [collarStep, if_neg hu, if_pos hl]
      · right
        change collarStep U L q β x = 1
        rw [collarStep, if_neg hu, if_neg hl]
  · intro x hx
    apply mvfderiv_collarStep_eq_zero_off_band U L hL q β a c b hac.le hcb.le
      hside hzero hone hclosed hfrontier
    exact hband ▸ hx
  · intro x v
    by_cases hu : x ∈ U
    · rw [mvfderiv_collarStep_of_mem hU L q β hu
        (((hq x hu).contMDiffAt (hU.mem_nhds hu)).mdifferentiableAt (by decide))
        ((hβ.differentiable (by decide)).differentiableAt), abs_mul]
      exact mul_le_mul_of_nonneg_right (hbound _) (abs_nonneg _)
    · have hz := mvfderiv_collarStep_eq_zero_off_band (I := J) U L hL q β a c b hac.le hcb.le
        hside hzero hone hclosed hfrontier (fun h ↦ hu h.1)
      rw [hz]
      simp only [zero_apply, abs_zero]
      exact mul_nonneg (div_nonneg hC.le (sub_pos.mpr hab).le) (abs_nonneg _)

end DifferentialGeometry.Topology.Manifold
