import DifferentialGeometry.Geometry.Boundary.EmbeddedCollarStep
import DifferentialGeometry.Topology.Manifold.OrderedStepPartitionSupport
import Mathlib.Data.Fin.Tuple.Basic

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Boundary

open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary
open DifferentialGeometry.Topology.Manifold

private def pad {n : ℕ} {α : Type*} (first last : α) (f : Fin n → α) : Fin (n + 2) → α :=
  Fin.cons first (Fin.snoc f last)

private theorem pad_zero {n : ℕ} {α : Type*} (first last : α) (f : Fin n → α) :
    pad first last f 0 = first := by simp [pad]

private theorem pad_internal {n : ℕ} {α : Type*} (first last : α) (f : Fin n → α) (j : Fin n) :
    pad first last f j.succ.castSucc = f j := by
  rw [pad, Fin.castSucc_succ, Fin.cons_succ, Fin.snoc_castSucc]

private theorem pad_last {n : ℕ} {α : Type*} (first last : α) (f : Fin n → α) :
    pad first last f (Fin.last (n + 1)) = last := by
  rw [← Fin.succ_last, pad, Fin.cons_succ, Fin.snoc_last]

private theorem pad_forall {n : ℕ} {α : Type*} (R : α → Prop)
    (first last : α) (f : Fin n → α) (hfirst : R first) (hlast : R last)
    (hf : ∀ j, R (f j)) : ∀ i, R (pad first last f i) := by
  intro i
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · simpa only [pad_zero] using hfirst
  · refine Fin.lastCases ?_ (fun i ↦ ?_) i
    · simpa only [Fin.succ_last, pad_last] using hlast
    · exact (pad_internal first last f i).symm ▸ hf i

private theorem pad_relation {n : ℕ} {α β : Type*} (R : α → β → Prop)
    (a₀ a₁ : α) (b₀ b₁ : β) (f : Fin n → α) (g : Fin n → β)
    (hfirst : R a₀ b₀) (hlast : R a₁ b₁) (hfg : ∀ j, R (f j) (g j)) :
    ∀ i, R (pad a₀ a₁ f i) (pad b₀ b₁ g i) := by
  intro i
  refine Fin.cases ?_ (fun i ↦ ?_) i
  · simpa only [pad_zero] using hfirst
  · refine Fin.lastCases ?_ (fun i ↦ ?_) i
    · simpa only [Fin.succ_last, pad_last] using hlast
    · change R (pad a₀ a₁ f i.succ.castSucc) (pad b₀ b₁ g i.succ.castSucc)
      rw [pad_internal, pad_internal]
      exact hfg i

private theorem pad_exterior_cover {n : ℕ} {X : Type*} [TopologicalSpace X]
    (P Q : Fin n → Set X)
    (hsep : ∀ i j, i < j → interior (Q i) ∪ interior (P j) = univ) :
    ∀ i j : Fin (n + 2), i < j →
      interior (pad univ ∅ Q i) ∪ interior (pad ∅ univ P j) = univ := by
  intro i j hij
  by_cases hi : i = 0
  · rw [hi, pad_zero, interior_univ, univ_union]
  by_cases hj : j = Fin.last (n + 1)
  · rw [hj, pad_last, interior_univ, union_univ]
  have hi₀ : i.val ≠ 0 := fun h ↦ hi (Fin.ext h)
  have hjlast : j.val ≠ n + 1 := fun h ↦ hj (Fin.ext h)
  have hijv : i.val < j.val := hij
  let i' : Fin n := ⟨i.val - 1, by have := i.isLt; have := j.isLt; omega⟩
  let j' : Fin n := ⟨j.val - 1, by have := j.isLt; omega⟩
  have hi' : i = i'.succ.castSucc := Fin.ext (by change i.val = (i.val - 1) + 1; omega)
  have hj' : j = j'.succ.castSucc := Fin.ext (by change j.val = (j.val - 1) + 1; omega)
  have hij' : i' < j' := by change i.val - 1 < j.val - 1; omega
  rw [hi', hj', pad_internal, pad_internal]
  exact hsep i' j' hij'

theorem exists_uniform_ordered_partition_of_embedded_product_collars :
    ∃ C : ℝ, 0 < C ∧ ∀
    {E H W F G M E' H' N : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace W] [ChartedSpace H W] [HasSmoothBoundary E H I]
    [IsManifold I ∞ W] [T2Space W]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace G] (J : ModelWithCorners ℝ F G)
    [TopologicalSpace M] [ChartedSpace G M] [IsManifold J ∞ M]
    [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [TopologicalSpace H'] (L : ModelWithCorners ℝ E' H')
    [TopologicalSpace N] [ChartedSpace H' N] [CompactSpace N],
    ∀ ι : W → M, ContMDiff I J ∞ ι →
    IsEmbedding ι → (∀ w, Function.Injective (mfderiv I J ι w)) →
    Module.finrank ℝ E = Module.finrank ℝ F → ∀ (n : ℕ)
      (O : Fin n → TopologicalSpace.Opens (N × ℝ)) (V : Fin n → TopologicalSpace.Opens M)
      (Φ : ∀ j, O j ≃ₘ⟮L.prod 𝓘(ℝ), J⟯ V j)
      (l r : Fin n → ℝ) (hlr : ∀ j, l j < r j)
      (hcollar : ∀ j, (univ : Set N) ×ˢ Icc (l j) (r j) ⊆ O j),
      let e := fun j (x : N × Icc (l j) (r j)) ↦
        (Φ j ⟨(x.1, (x.2 : ℝ)), hcollar j ⟨mem_univ _, x.2.property⟩⟩ : M)
      let q := fun j ↦ Subtype.val.extend
        (fun x : V j ↦ ((Φ j).symm x : N × ℝ).2) (fun _ ↦ 0)
      (∀ j x, e j x ∈ interior (range ι)) →
      ∀ P Q : Fin n → Set W,
      (∀ j, IsClosed (P j)) → (∀ j, IsClosed (Q j)) → (∀ j, Disjoint (P j) (Q j)) →
      (∀ j, P j ∪ ι ⁻¹' range (e j) ∪ Q j = univ) →
      (∀ j, P j ∩ ι ⁻¹' range (e j) ⊆
        ι ⁻¹' range (fun p : N ↦ e j (p, ⟨l j, le_rfl, (hlr j).le⟩))) →
      (∀ j, Q j ∩ ι ⁻¹' range (e j) ⊆
        ι ⁻¹' range (fun p : N ↦ e j (p, ⟨r j, (hlr j).le, le_rfl⟩))) →
      (∀ i j, i < j → interior (Q i) ∪ interior (P j) = univ) →
      ∀ (a b : Fin n → ℝ), (∀ j, l j < a j) → (∀ j, a j < b j) → (∀ j, b j < r j) →
      let K := fun j ↦ ι ⁻¹' (e j '' {x | a j ≤ (x.2 : ℝ) ∧ (x.2 : ℝ) ≤ b j})
      ∃ (β : Fin n → ℝ → ℝ) (θ : Fin (n + 2) → C^∞⟮I, W; 𝓘(ℝ), ℝ⟯),
        (∀ i w, θ i w ∈ Icc (0 : ℝ) 1) ∧
        (∀ j, ContDiff ℝ ∞ (β j) ∧ Monotone (β j) ∧
          (∀ w ∈ P j, θ j.succ.castSucc w = 0) ∧
          (∀ w ∈ Q j, θ j.succ.castSucc w = 1) ∧
          (∀ w x, ι w = e j x → θ j.succ.castSucc w = β j (x.2 : ℝ)) ∧
          (∀ t, t ≤ a j → β j t = 0) ∧ (∀ t, b j ≤ t → β j t = 1) ∧
          IsCompact (K j) ∧
          (∀ w ∉ K j, θ j.succ.castSucc w = 0 ∨ θ j.succ.castSucc w = 1) ∧
          (∀ w ∉ K j, mvfderiv I (θ j.succ.castSucc) w = 0) ∧
          ∀ w (v : TangentSpace I w),
            |mvfderiv I (θ j.succ.castSucc) w v| ≤
              (C / (b j - a j)) * |mvfderiv I (q j ∘ ι) w v|) ∧
        ∃ (horder : ∀ w, Antitone (fun i ↦ θ i w))
          (hfirst : ∀ w, θ 0 w = 1) (hlast : ∀ w, θ (Fin.last (n + 1)) w = 0),
          let χ := orderedStepPartition θ horder hfirst hlast
          Pairwise (fun i j ↦ Disjoint (K i) (K j)) ∧
          (∀ j : Fin n, tsupport (χ j.castSucc) ∩ tsupport (χ j.succ) ⊆ K j) ∧
          (∀ i j : Fin (n + 1), i.val + 1 < j.val →
            Disjoint (tsupport (χ i)) (tsupport (χ j))) ∧
          (∀ j : Fin n, tsupport (χ j.castSucc) ⊆ (interior (Q j))ᶜ ∧
            tsupport (χ j.succ) ⊆ (interior (P j))ᶜ) ∧
          ∀ j w, w ∈ K j → ∀ i : Fin (n + 1), χ i w ≠ 0 →
            i = j.castSucc ∨ i = j.succ := by
  classical
  obtain ⟨C, hC, hsteps⟩ :=
    exists_uniform_smooth_step_of_embedded_product_collar
  refine ⟨C, hC, ?_⟩
  intro E H W F G M E' H' N _ _ _ _ I _ _ _ _ _ _ _ _ _ J _ _ _ _ _ _ L _ _ _
  specialize hsteps (W := W) (M := M) (N := N) I J L
  intro ι hι hemb hfull hdim n O V Φ l r hlr hcollar e q hinternal
    P Q hP hQ hPQ hcover hleft hright hsep a b hla hab hbr K
  choose β t hβ hmono ht hrange hzero hone hformula hβzero hβone hK hbinary hoff hbound using
    fun j ↦ hsteps ι hι hemb hfull hdim (O j) (V j) (Φ j) (l j) (r j) (hlr j)
      (hcollar j) (hinternal j) (P j) (Q j) (hP j) (hQ j) (hPQ j)
      (hcover j) (hleft j) (hright j) (a j) (b j) (hla j) (hab j) (hbr j)
  let f : Fin n → C^∞⟮I, W; 𝓘(ℝ), ℝ⟯ := fun j ↦ ⟨t j, ht j⟩
  let one : C^∞⟮I, W; 𝓘(ℝ), ℝ⟯ := ⟨fun _ ↦ 1, contMDiff_const⟩
  let zero : C^∞⟮I, W; 𝓘(ℝ), ℝ⟯ := ⟨fun _ ↦ 0, contMDiff_const⟩
  let θ := pad one zero f
  let PP := pad ∅ univ P
  let QQ := pad univ ∅ Q
  have hinternal (j : Fin n) : θ j.succ.castSucc = f j := pad_internal one zero f j
  have hfirst (w : W) : θ 0 w = 1 := congrArg (fun g ↦ g w) (pad_zero one zero f)
  have hlast (w : W) : θ (Fin.last (n + 1)) w = 0 :=
    congrArg (fun g ↦ g w) (pad_last one zero f)
  have h01 : ∀ i w, θ i w ∈ Icc (0 : ℝ) 1 :=
    pad_forall (fun g : C^∞⟮I, W; 𝓘(ℝ), ℝ⟯ ↦ ∀ w, g w ∈ Icc (0 : ℝ) 1)
      one zero f (fun _ ↦ ⟨zero_le_one, le_rfl⟩) (fun _ ↦ ⟨le_rfl, zero_le_one⟩) hrange
  have hz : ∀ i w, w ∈ PP i → θ i w = 0 :=
    pad_relation (fun (g : C^∞⟮I, W; 𝓘(ℝ), ℝ⟯) (A : Set W) ↦ ∀ w ∈ A, g w = 0)
      one zero ∅ univ f P (by simp) (by intros; rfl) hzero
  have ho : ∀ i w, w ∈ QQ i → θ i w = 1 :=
    pad_relation (fun (g : C^∞⟮I, W; 𝓘(ℝ), ℝ⟯) (A : Set W) ↦ ∀ w ∈ A, g w = 1)
      one zero univ ∅ f Q (by intros; rfl) (by simp) hone
  have hsep' : ∀ i j, i < j → interior (QQ i) ∪ interior (PP j) = univ :=
    pad_exterior_cover P Q hsep
  have horder (w : W) : Antitone (fun i ↦ θ i w) :=
    DifferentialGeometry.Topology.antitone_of_separated_steps (fun i w ↦ θ i w) PP QQ h01 hz ho
      (fun i j hij ↦ eq_univ_of_forall (fun y ↦ by
        have hy : y ∈ interior (QQ i) ∪ interior (PP j) := (hsep' i j hij).symm ▸ mem_univ y
        exact hy.elim (fun h ↦ Or.inl (interior_subset h)) (fun h ↦ Or.inr (interior_subset h)))) w
  have hinj (j : Fin n) : Function.Injective (e j) := by
    intro x y hxy
    have hΦ := (Φ j).injective (Subtype.ext hxy)
    have hv := congrArg (fun z : O j ↦ (z : N × ℝ)) hΦ
    exact Prod.ext (congrArg (fun z : N × ℝ ↦ z.1) hv)
      (Subtype.ext (congrArg (fun z : N × ℝ ↦ z.2) hv))
  have hKP (j : Fin n) : Disjoint (K j) (P j) := by
    apply Set.disjoint_left.mpr
    rintro w ⟨y, hy, hey⟩ hw
    obtain ⟨p, hp⟩ := hleft j ⟨hw, ⟨y, hey⟩⟩
    have hh := congrArg (fun z : N × Icc (l j) (r j) ↦ (z.2 : ℝ))
      (hinj j (hp.trans hey.symm))
    have hlow := hy.1
    change l j = (y.2 : ℝ) at hh
    exact (not_le_of_gt (hla j)) (hh.symm ▸ hlow)
  have hKQ (j : Fin n) : Disjoint (K j) (Q j) := by
    apply Set.disjoint_left.mpr
    rintro w ⟨y, hy, hey⟩ hw
    obtain ⟨p, hp⟩ := hright j ⟨hw, ⟨y, hey⟩⟩
    have hh := congrArg (fun z : N × Icc (l j) (r j) ↦ (z.2 : ℝ))
      (hinj j (hp.trans hey.symm))
    have hupp := hy.2
    change r j = (y.2 : ℝ) at hh
    exact (not_le_of_gt (hbr j)) (hh.symm ▸ hupp)
  have hdisj (i j : Fin n) (hij : i < j) : Disjoint (K i) (K j) := by
    apply Set.disjoint_left.mpr
    intro w hwi hwj
    have hw : w ∈ interior (Q i) ∪ interior (P j) := (hsep i j hij).symm ▸ mem_univ w
    exact hw.elim (fun h ↦ Set.disjoint_left.mp (hKQ i) hwi (interior_subset h))
      (fun h ↦ Set.disjoint_left.mp (hKP j) hwj (interior_subset h))
  let χ := orderedStepPartition θ horder hfirst hlast
  have hwedges (j : Fin n) : tsupport (χ j.castSucc) ⊆ (interior (Q j))ᶜ ∧
      tsupport (χ j.succ) ⊆ (interior (P j))ᶜ := by
    constructor
    · intro w hw
      have h := (tsupport_orderedStepPartition_subset θ horder hfirst hlast
        PP QQ hz ho j.castSucc hw).2
      have hQQ : QQ j.castSucc.succ = Q j := by
        rw [← Fin.castSucc_succ]
        exact pad_internal univ ∅ Q j
      rwa [hQQ] at h
    · intro w hw
      have h := (tsupport_orderedStepPartition_subset θ horder hfirst hlast
        PP QQ hz ho j.succ hw).1
      have hPP : PP j.succ.castSucc = P j := pad_internal ∅ univ P j
      rwa [hPP] at h
  refine ⟨β, θ, h01, ?_, horder, hfirst, hlast, ?_, ?_, ?_, hwedges, ?_⟩
  · intro j
    rw [hinternal]
    exact ⟨hβ j, hmono j, hzero j, hone j, hformula j, hβzero j, hβone j,
      hK j, hbinary j, hoff j, hbound j⟩
  · intro i j hij
    rcases lt_or_gt_of_ne hij with hij | hij
    · exact hdisj i j hij
    · exact (hdisj j i hij).symm
  · intro j
    apply inter_tsupport_orderedStepPartition_subset_of_binary_off_band θ horder hfirst hlast j
      (hK j).isClosed
    rw [hinternal]
    exact hbinary j
  · exact disjoint_tsupport_orderedStepPartition_of_separated_exteriors θ horder hfirst hlast
      PP QQ hz ho hsep'
  · intro j w hw i hχ
    by_contra hn
    have hi₀ : i.val ≠ j.val := fun h ↦ hn (Or.inl (Fin.ext h))
    have hi₁ : i.val ≠ j.val + 1 := fun h ↦ hn (Or.inr (Fin.ext h))
    have hwχ : w ∈ tsupport (χ i) := subset_closure hχ
    by_cases hij : i.val < j.val
    · let k : Fin n := ⟨i.val, by have := j.isLt; omega⟩
      have hik : i = k.castSucc := Fin.ext rfl
      have hkj : k < j := hij
      have hex : w ∈ interior (Q k) ∪ interior (P j) :=
        (hsep k j hkj).symm ▸ mem_univ w
      rcases hex with hq | hp
      · exact (hwedges k).1 (hik ▸ hwχ) hq
      · exact Set.disjoint_left.mp (hKP j) hw (interior_subset hp)
    · let k : Fin n := ⟨i.val - 1, by have := i.isLt; omega⟩
      have hik : i = k.succ := Fin.ext (by change i.val = (i.val - 1) + 1; omega)
      have hjk : j < k := by change j.val < i.val - 1; omega
      have hex : w ∈ interior (Q j) ∪ interior (P k) :=
        (hsep j k hjk).symm ▸ mem_univ w
      rcases hex with hq | hp
      · exact Set.disjoint_left.mp (hKQ j) hw (interior_subset hq)
      · exact (hwedges k).2 (hik ▸ hwχ) hp

end DifferentialGeometry.Geometry.Boundary
