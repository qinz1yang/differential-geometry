/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ArrangementGeneralPosition
import DifferentialGeometry.Topology.PiecewiseLinear.SingularGeneralPosition

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Classical in
theorem exists_small_affineIndependent_subsets_relative_in_halfSpace_with_collar
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {ι : Type*}
    (V B Z : Finset ι) (hZB : Z ⊆ B) (hBV : B ⊆ V)
    (ℓ : F →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (φ₀ : ι → F)
    (hZ : ∀ v ∈ Z, ℓ (φ₀ v) = 0)
    (hpositive : ∀ v ∈ V \ Z, 0 < ℓ (φ₀ v))
    (hfixedAI : ∀ u : Finset ι, u ⊆ B →
      u.card ≤ Module.finrank ℝ F + 1 →
        (u ∩ B).card ≤ Module.finrank ℝ (LinearMap.ker ℓ) + 1 →
          AffineIndependent ℝ (fun v : u => φ₀ (v : ι)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : ι → F, EqOn φ φ₀ (V : Set ι)ᶜ ∧ EqOn φ φ₀ (B : Set ι) ∧
      (∀ v, dist (φ v) (φ₀ v) < ε) ∧
        (∀ v ∈ Z, ℓ (φ v) = 0) ∧ (∀ v ∈ V \ Z, 0 < ℓ (φ v)) ∧
          ∀ s : Finset ι, s ⊆ V → s.card ≤ Module.finrank ℝ F + 1 →
            (s ∩ B).card ≤ Module.finrank ℝ (LinearMap.ker ℓ) + 1 →
              AffineIndependent ℝ (fun v : s => φ (v : ι)) := by
  let A := V \ B
  have hAB : Disjoint A B := Finset.disjoint_left.mpr (fun v hvA hvB =>
    (Finset.mem_sdiff.mp hvA).2 hvB)
  have hAunion : A ∪ B = V := by
    exact Finset.sdiff_union_of_subset hBV
  have hkerRank : Module.finrank ℝ (LinearMap.ker ℓ) + 1 = Module.finrank ℝ F := by
    have hrange : LinearMap.range ℓ = ⊤ := LinearMap.range_eq_top.mpr fun c => by
      obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp hℓ
      rw [LinearMap.zero_apply] at hv
      exact ⟨(c / ℓ v) • v, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]⟩
    have h := LinearMap.finrank_range_add_finrank_ker ℓ
    rw [hrange, finrank_top, Module.finrank_self] at h
    omega
  have hfixed : ∀ u : Finset ι, u ⊆ B → u.card ≤ Module.finrank ℝ F + 1 →
      (u ∩ B).card ≤ Module.finrank ℝ (LinearMap.ker ℓ) + 1 →
        AffineIndependent ℝ (fun v : u => φ₀ (v : ι)) := by
    intro u hu hcard hz
    exact hfixedAI u hu hcard hz
  have hmain_aux : ∀ A : Finset ι, A ⊆ V → Disjoint A B →
      ∃ φ : ι → F, EqOn φ φ₀ (A : Set ι)ᶜ ∧ EqOn φ φ₀ (B : Set ι) ∧
        (∀ v, dist (φ v) (φ₀ v) < ε) ∧ (∀ v ∈ A, 0 < ℓ (φ v)) ∧
          ∀ s : Finset ι, s ⊆ A ∪ B → s.card ≤ Module.finrank ℝ F + 1 →
            (s ∩ B).card ≤ Module.finrank ℝ (LinearMap.ker ℓ) + 1 →
              AffineIndependent ℝ (fun v : s => φ (v : ι)) := by
    intro A
    induction A using Finset.induction_on with
    | empty =>
      intro hAV hAB'
      refine ⟨φ₀, fun _ _ => rfl, fun _ _ => rfl,
        fun _ => by simpa only [dist_self] using hε, ?_, ?_⟩
      · intro v hv
        simp at hv
      · intro s hs hcard hz
        have hsB : s ⊆ B := by simpa only [Finset.empty_union] using hs
        exact hfixed s hsB hcard hz
    | @insert v A hvA ih =>
      intro hAV hAB'
      have hA_sub : A ⊆ V := fun w hw => hAV (Finset.mem_insert_of_mem hw)
      have hvB : v ∉ B := by
        intro hvB
        exact Finset.disjoint_left.mp hAB' (Finset.mem_insert_self v A) hvB
      have hAB'' : Disjoint A B := hAB'.mono_left (Finset.subset_insert v A)
      obtain ⟨φ, hfix, hfixB, hclose, hposA, hgood⟩ := ih hA_sub hAB''
      let I := {s : Finset ι // s ⊆ A ∪ B ∧ s.card ≤ Module.finrank ℝ F ∧
        (s ∩ B).card ≤ Module.finrank ℝ (LinearMap.ker ℓ) + 1 ∧
          AffineIndependent ℝ (fun w : (s ∩ B : Finset ι) => φ (w : ι))}
      have : Finite I := (((A ∪ B).powerset.finite_toSet).subset
        (fun s hs => Finset.mem_powerset.mpr hs.1)).to_subtype
      let layers : I → AffineSubspace ℝ F := fun s => affineSpan ℝ (s.val.image φ : Set F)
      have hlayers : ∀ s, layers s ≠ ⊤ := by
        intro s htop
        have hsAI := ((affineIndependent_image_iff s.val φ).mp
          (hgood s.val s.property.1 (Nat.le_succ_of_le s.property.2.1)
            s.property.2.2.1)).2
        have hrange : range ((↑) : ↥(s.val.image φ : Set F) → F) =
            (s.val.image φ : Set F) := by ext y; simp
        have htop' : affineSpan ℝ (range ((↑) : ↥(s.val.image φ : Set F) → F)) = ⊤ := by
          rwa [hrange]
        have hc := hsAI.affineSpan_eq_top_iff_card_eq_finrank_add_one.mp htop'
        rw [Fintype.card_coe] at hc
        have hle := (Finset.card_image_le (s := s.val) (f := φ)).trans s.property.2.1
        omega
      let l : Unit → F →ᵃ[ℝ] ℝ := fun _ => ℓ.toAffineMap
      have hlayer : arrangementLayer l (φ₀ v) = ⊤ := by
        apply top_unique
        intro y _
        rw [mem_arrangementLayer_iff]
        intro k hk
        have hk0 : ℓ (φ₀ v) = 0 := by simpa [l] using hk
        exact ((ne_of_gt (hpositive v (Finset.mem_sdiff.mpr
          ⟨hAV (Finset.mem_insert_self v A), fun hvZ => hvB (hZB hvZ)⟩))) hk0).elim
      have hroom : ∀ s, ¬arrangementLayer l (φ₀ v) ≤ layers s := by
        intro s hs
        apply hlayers s
        exact top_unique (hlayer ▸ hs)
      obtain ⟨p, hpCell, hpClose, hpAvoid⟩ :=
        exists_mem_openCell_notMem_affineSubspaces l layers (φ₀ v) hroom hε
      let ψ := Function.update φ v p
      have hsame : ∀ w ≠ v, ψ w = φ w := fun w hw => Function.update_of_ne hw p φ
      have hψv : ψ v = p := Function.update_self v p φ
      have hψpos : 0 < ℓ (ψ v) := by
        have hs := congrFun hpCell ()
        have hs' : SignType.sign (ℓ (ψ v)) = SignType.sign (ℓ (φ₀ v)) := by
          simpa [ψ, signVec, l] using hs
        exact sign_eq_one_iff.mp (hs'.trans (sign_eq_one_iff.mpr
          (hpositive v (Finset.mem_sdiff.mpr
            ⟨hAV (Finset.mem_insert_self v A), fun hvZ => hvB (hZB hvZ)⟩))))
      refine ⟨ψ, ?_, ?_, ?_, ?_, ?_⟩
      · intro w hw
        have hwv : w ≠ v := fun heq => hw (heq ▸ Finset.mem_insert_self v A)
        exact (hsame w hwv).trans (hfix (fun hwA => hw (Finset.mem_insert_of_mem hwA)))
      · intro w hw
        exact (hsame w (ne_of_mem_of_not_mem hw hvB)).trans (hfixB hw)
      · intro w
        by_cases hwv : w = v
        · rw [hwv, hψv]
          exact hpClose
        · rw [hsame w hwv]
          exact hclose w
      · intro w hw
        by_cases hwv : w = v
        · rw [hwv]
          exact hψpos
        · rw [hsame w hwv]
          exact hposA w (Finset.mem_of_mem_insert_of_ne hw hwv)
      · intro s hs hcard hz
        by_cases hvs : v ∈ s
        · have hsub : s.erase v ⊆ A ∪ B := by
            intro w hw
            rcases Finset.mem_union.mp (hs (Finset.mem_of_mem_erase hw)) with hwA | hwB
            · exact Finset.mem_union_left B ((Finset.mem_insert.mp hwA).resolve_left
                (Finset.ne_of_mem_erase hw))
            · exact Finset.mem_union_right A hwB
          have herase : (s.erase v).card ≤ Module.finrank ℝ F := by
            have h := Finset.card_erase_of_mem hvs
            omega
          have hz' : (s.erase v ∩ B).card ≤ Module.finrank ℝ (LinearMap.ker ℓ) + 1 := by
            exact (Finset.card_le_card (show s.erase v ∩ B ⊆ s ∩ B from fun w hw =>
              Finset.mem_inter.mpr ⟨Finset.mem_of_mem_erase (Finset.mem_inter.mp hw).1,
                (Finset.mem_inter.mp hw).2⟩)).trans hz
          have hfixed' : AffineIndependent ℝ
              (fun w : (s.erase v ∩ B : Finset ι) => φ (w : ι)) := by
            have hcardB : (s.erase v ∩ B).card ≤ Module.finrank ℝ F :=
              (Finset.card_le_card Finset.inter_subset_left).trans herase
            exact hgood (s.erase v ∩ B)
              (Finset.inter_subset_left.trans hsub)
              (Nat.le_succ_of_le hcardB) (by
                have hinter : s.erase v ∩ B ∩ B = s.erase v ∩ B := by
                  ext w
                  simp
                rw [hinter]
                exact hz')
          have h := affineIndependent_update_insert (φ := φ) (Finset.notMem_erase v s)
            (hgood (s.erase v) hsub (Nat.le_succ_of_le herase) hz')
            (hpAvoid ⟨s.erase v, hsub, herase, hz', hfixed'⟩)
          rwa [Finset.insert_erase hvs] at h
        · have hsub : s ⊆ A ∪ B := by
            intro w hw
            rcases Finset.mem_union.mp (hs hw) with hwA | hwB
            · exact Finset.mem_union_left B ((Finset.mem_insert.mp hwA).resolve_left
                (by intro h; exact hvs (h ▸ hw)))
            · exact Finset.mem_union_right A hwB
          have heq : (fun w : s => ψ (w : ι)) = (fun w : s => φ (w : ι)) :=
            funext fun w => hsame w (ne_of_mem_of_not_mem w.property hvs)
          rw [heq]
          exact hgood s hsub hcard hz
  obtain ⟨φ, hfixA, hfixB, hclose, hposA, hgood⟩ :=
    hmain_aux A (fun v hv => (Finset.mem_sdiff.mp hv).1) hAB
  refine ⟨φ, ?_, hfixB, hclose, ?_, ?_, ?_⟩
  · intro v hv
    apply hfixA
    intro hvA
    exact hv (Finset.mem_sdiff.mp hvA).1
  · intro v hv
    change v ∈ Z at hv
    rw [hfixB (hZB hv)]
    exact hZ v hv
  · intro v hv
    change v ∈ V \ Z at hv
    have hv' : v ∈ V \ Z := by simpa using hv
    by_cases hvB : v ∈ B
    · rw [hfixB hvB]
      exact hpositive v hv'
    · exact hposA v (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hv').1, hvB⟩)
  · intro s hs hcard hz
    exact hgood s (hAunion.symm ▸ hs) hcard hz

open Classical in
theorem vectorSpan_sup_eq_top_of_affineIndependent_subsets_relative_in_halfSpace
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {ι : Type*}
    (V B : Finset ι) (ℓ : F →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (φ : ι → F)
    (hφ : ∀ u : Finset ι, u ⊆ V → u.card ≤ Module.finrank ℝ F + 1 →
      (u ∩ B).card ≤ Module.finrank ℝ (LinearMap.ker ℓ) + 1 →
        AffineIndependent ℝ (fun v : u => φ (v : ι)))
    {s t : Finset ι} (hs : s ⊆ V) (ht : t ⊆ V) (hst : Disjoint s t)
    (hnotB : ¬s ∪ t ⊆ B)
    (hinter : (convexHull ℝ (s.image φ : Set F) ∩
      convexHull ℝ (t.image φ : Set F)).Nonempty) :
    vectorSpan ℝ (s.image φ : Set F) ⊔ vectorSpan ℝ (t.image φ : Set F) = ⊤ := by
  have hkerRank : Module.finrank ℝ (LinearMap.ker ℓ) + 1 = Module.finrank ℝ F := by
    have hrange : LinearMap.range ℓ = ⊤ := LinearMap.range_eq_top.mpr fun c => by
      obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp hℓ
      rw [LinearMap.zero_apply] at hv
      exact ⟨(c / ℓ v) • v, by rw [map_smul, smul_eq_mul, div_mul_cancel₀ _ hv]⟩
    have h := LinearMap.finrank_range_add_finrank_ker ℓ
    rw [hrange, finrank_top, Module.finrank_self] at h
    omega
  obtain ⟨v, hv, hvB⟩ := Finset.not_subset.mp hnotB
  have hBbound : ∀ u : Finset ι, v ∈ u → u.card ≤ Module.finrank ℝ F + 1 →
      (u ∩ B).card ≤ Module.finrank ℝ (LinearMap.ker ℓ) + 1 := by
    intro u hvu hcard
    have hle : u ∩ B ⊆ u.erase v := by
      intro w hw
      exact Finset.mem_erase.mpr ⟨ne_of_mem_of_not_mem (Finset.mem_inter.mp hw).2 hvB,
        (Finset.mem_inter.mp hw).1⟩
    calc
      (u ∩ B).card ≤ (u.erase v).card := Finset.card_le_card hle
      _ = u.card - 1 := Finset.card_erase_of_mem hvu
      _ ≤ Module.finrank ℝ F := by omega
      _ = Module.finrank ℝ (LinearMap.ker ℓ) + 1 := hkerRank.symm
  have hsub : s ∪ t ⊆ V := Finset.union_subset hs ht
  by_cases hcard : (s ∪ t).card ≤ Module.finrank ℝ F + 1
  · have hAI := (affineIndependent_image_iff (s ∪ t) φ).mp
      (hφ _ hsub hcard (hBbound _ hv hcard))
    have hdisj : Disjoint (s.image φ) (t.image φ) := by
      rw [Finset.disjoint_left]
      intro y hys hyt
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hys
      obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp hyt
      have heq : b = a := hAI.1 (Finset.mem_union_right s hb) (Finset.mem_union_left t ha) hba
      exact Finset.disjoint_left.mp hst ha (heq ▸ hb)
    obtain ⟨y, hys, hyt⟩ := hinter
    have hmem := convexHull_inter_subset_of_affineIndependent hAI.2
      (Finset.image_subset_image Finset.subset_union_left)
      (Finset.image_subset_image Finset.subset_union_right) ⟨hys, hyt⟩
    rw [← Finset.coe_inter, Finset.disjoint_iff_inter_eq_empty.mp hdisj, Finset.coe_empty,
      convexHull_empty] at hmem
    exact False.elim hmem
  · have herase := Finset.card_erase_of_mem hv
    obtain ⟨u, hu, hucard⟩ := Finset.exists_subset_card_eq
      (show Module.finrank ℝ F ≤ ((s ∪ t).erase v).card by omega)
    have hvu : v ∉ u := fun h => Finset.notMem_erase v (s ∪ t) (hu h)
    have hins : insert v u ⊆ s ∪ t := Finset.insert_subset_iff.mpr
      ⟨hv, hu.trans (Finset.erase_subset v (s ∪ t))⟩
    have hinscard : (insert v u).card = Module.finrank ℝ F + 1 := by
      rw [Finset.card_insert_of_notMem hvu, hucard]
    have huAI := hφ (insert v u) (hins.trans hsub) hinscard.le
      (hBbound _ (Finset.mem_insert_self v u) hinscard.le)
    have huSpan : affineSpan ℝ ((insert v u).image φ : Set F) = ⊤ := by
      have hrange : range (fun w : (insert v u : Finset ι) => φ (w : ι)) =
          ((insert v u).image φ : Set F) := by ext y; simp [eq_comm]
      rw [← hrange, huAI.affineSpan_eq_top_iff_card_eq_finrank_add_one, Fintype.card_coe]
      exact hinscard
    have hspan : affineSpan ℝ ((s.image φ : Set F) ∪ (t.image φ : Set F)) = ⊤ := by
      apply top_unique
      rw [← huSpan]
      apply affineSpan_mono ℝ
      intro y hy
      obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hy
      rcases Finset.mem_union.mp (hins ha) with has | hat
      · exact Or.inl (Finset.mem_image_of_mem φ has)
      · exact Or.inr (Finset.mem_image_of_mem φ hat)
    obtain ⟨y, hys, hyt⟩ := hinter
    have hdir := congrArg AffineSubspace.direction hspan
    rw [AffineSubspace.span_union, AffineSubspace.direction_sup
      (convexHull_subset_affineSpan _ hys) (convexHull_subset_affineSpan _ hyt),
      direction_affineSpan, direction_affineSpan, vsub_self, Submodule.span_singleton_eq_bot.mpr
        rfl, sup_bot_eq, AffineSubspace.direction_top] at hdir
    exact hdir

end DifferentialGeometry.Topology.PiecewiseLinear
