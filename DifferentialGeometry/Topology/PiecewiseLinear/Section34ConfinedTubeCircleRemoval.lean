/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DisjointSupportedMotionComposition
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CarrierSingleTraceRemoval
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ConfinedTubePiercingConditions
import DifferentialGeometry.Topology.PiecewiseLinear.Section34IncidentEdgeFinite
import DifferentialGeometry.Topology.PiecewiseLinear.Section34ProtectedSupportIsolation
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SingleTraceMotion

open Function Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

section Edges

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  {U : Set M₁} {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}

theorem section34_edge_eq_of_ends_eq
    (hends : ∀ e, (e.1 : Set Ea) = ((ends e).1.1 : Set Ea) ∪ ((ends e).2.1 : Set Ea))
    {e d : Section34EdgeIndex 𝒦 𝒦'} (h₁ : (ends e).1 = (ends d).1)
    (h₂ : (ends e).2 = (ends d).2) : e = d := by
  apply Subtype.ext
  apply Finset.coe_injective
  rw [hends e, hends d, h₁, h₂]

theorem section34_edge_eq_of_ends_swap
    (hends : ∀ e, (e.1 : Set Ea) = ((ends e).1.1 : Set Ea) ∪ ((ends e).2.1 : Set Ea))
    {e d : Section34EdgeIndex 𝒦 𝒦'} (h₁ : (ends e).1 = (ends d).2)
    (h₂ : (ends e).2 = (ends d).1) : e = d := by
  apply Subtype.ext
  apply Finset.coe_injective
  rw [hends e, hends d, h₁, h₂, union_comm]

variable {M₂ : Type u} [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂]

theorem exists_section34_vertex_supported_motions
    (hends : ∀ e, (e.1 : Set Ea) = ((ends e).1.1 : Set Ea) ∪ ((ends e).2.1 : Set Ea))
    (K O : Section34EdgeIndex 𝒦 𝒦' → Set M₂) (ψ : Section34EdgeIndex 𝒦 𝒦' → M₂ ≃ₜ M₂)
    (hdis : Pairwise (Disjoint on K)) (hfix : ∀ e, EqOn (ψ e) id (K e)ᶜ)
    (hK : ∀ e, IsClosed (K e)) (hO : ∀ e, IsOpen (O e)) (hKO : ∀ e, K e ⊆ O e)
    (hψ : ∀ e, IsPLOn 3 3 (ψ e) (O e)) :
    ∃ Ψ : Section34VertexIndex 𝒦 𝒦' → M₂ ≃ₜ M₂,
      (∀ e, EqOn (Ψ (ends e).2) (ψ e) (K e)) ∧
      (∀ w, EqOn (Ψ w) id (⋃ e, ⋃ (_ : (ends e).2 = w), K e)ᶜ) ∧
      ∀ w, ∀ {d : ℕ} {D Bd : Set M₁} (f : M₁ → M₂), IsPLHomeomorphInto 3 f D →
        IsPLCellOn d D Bd → IsPLHomeomorphInto 3 (Ψ w ∘ f) D := by
  classical
  have hfinite (w : Section34VertexIndex 𝒦 𝒦') :
      {e : Section34EdgeIndex 𝒦 𝒦' | (ends e).2 = w}.Finite := by
    have hi : {e : Section34EdgeIndex 𝒦 𝒦' | w = (ends e).1 ∨ w = (ends e).2}.Finite :=
      Set.finite_coe_iff.mp (section34_incident_edges_finite hends w)
    exact hi.subset fun _ he => Or.inr he.symm
  have hw (w : Section34VertexIndex 𝒦 𝒦') :=
    exists_homeomorph_of_finite_disjoint_supported_isPLOn (M := M₁) (hfinite w).toFinset K O ψ
      hdis (fun e _ => hfix e) (fun e _ => hK e) (fun e _ => hO e) (fun e _ => hKO e)
      (fun e _ => hψ e)
  choose Ψ hΨeq hΨfix hΨpl using hw
  refine ⟨Ψ, fun e => hΨeq _ e ((hfinite _).mem_toFinset.mpr (by simp)), fun w => ?_, hΨpl⟩
  intro y hy
  refine hΨfix w ?_
  intro hmem
  obtain ⟨e, he, hye⟩ := mem_iUnion₂.mp hmem
  exact hy (mem_iUnion₂.mpr ⟨e, (hfinite w).mem_toFinset.mp he, hye⟩)

end Edges

section Removal

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₁]
  [MetricSpace M₂] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M₂] {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂} {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ}
  {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}

theorem section34ConfinedTubePiercingConditions_of_single_trace_motions
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G)
    (k : ∀ e, Fin (cnt e)) (K : Section34EdgeIndex 𝒦 𝒦' → Set M₂)
    (ψ : Section34EdgeIndex 𝒦 𝒦' → M₂ ≃ₜ M₂)
    (hK : ∀ e, IsCompact (K e)) (hKS : ∀ e, K e ⊆ interior (Sp e))
    (hfix : ∀ e, EqOn (ψ e) id (K e)ᶜ)
    (hψ : ∀ e, IsPLOn 3 3 (ψ e) (interior (G (ends e).1 '' Cc (ends e).1)))
    (hrimA : ∀ e, Disjoint (K e) (G (ends e).1 '' (Ab₀ e ∪ Ab₁ e)))
    (hrimB : ∀ e, Disjoint (K e) (G (ends e).2 '' (Bb₀ e ∪ Bb₁ e)))
    (hkeep : ∀ e, Disjoint (K e) (Pg e (k e).val))
    (hcancel : ∀ e, G (ends e).1 '' CpBd (ends e).1 ∩
      ψ e '' (G (ends e).2 '' CpBd (ends e).2) = Pg e (k e).val)
    (Ψ : Section34VertexIndex 𝒦 𝒦' → M₂ ≃ₜ M₂)
    (hΨeq : ∀ e, EqOn (Ψ (ends e).2) (ψ e) (K e))
    (hΨfix : ∀ w, EqOn (Ψ w) id (⋃ e, ⋃ (_ : (ends e).2 = w), K e)ᶜ)
    (hΨpl : ∀ w, IsPLHomeomorphInto 3 (Ψ w ∘ G w) (Cc w))
    (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (hG' : ∀ w, G' w = Ψ w ∘ G w)
    (cnt' : Section34EdgeIndex 𝒦 𝒦' → ℕ) (hcnt' : ∀ e, cnt' e = 1)
    (Pg' : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂) (hPg' : ∀ e i, Pg' e i = Pg e (k e).val) :
    Section34ConfinedTubePiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
        Bb₁ Sp Tp cnt' Pg' G' ∧
      (∀ w, EqOn (G' w) (G w) {x ∈ Cc w | ∀ e, G w x ∉ interior (Sp e)}) ∧
      ∀ w, EqOn (G' w) (G w) (simplexBody 𝒦' w.1) := by
  classical
  obtain ⟨-, -, hsub, -, hCp, -, -, -, hends, -, -, htor, hSnCc, -, hAa, hBbP, -⟩ := id hprep
  obtain ⟨-, hQ, hSn, htube, hlf, hdisj, hmeet, hside, hBbSp, hgraph, hGp, hmark, hbd, hsep,
    -, -, -, -, -, -, hlens, hbodysep⟩ := id hpack
  have hends' : ∀ e, (e.1 : Set Ea) = ((ends e).1.1 : Set Ea) ∪ ((ends e).2.1 : Set Ea) :=
    fun e => (hends e).2.1
  have hne : ∀ e, (ends e).1 ≠ (ends e).2 := fun e => (hends e).1
  have hKSp : ∀ e, K e ⊆ Sp e := fun e => (hKS e).trans interior_subset
  have hKdisjSp : ∀ d e, d ≠ e → Disjoint (K d) (Sp e) :=
    fun d e hde => (hdisj d e hde).mono_left (hKSp d)
  have hKK : ∀ d e, d ≠ e → Disjoint (K d) (K e) :=
    fun d e hde => (hKdisjSp d e hde).mono_right (hKSp e)
  have hCpCc : ∀ w, Cp w ⊆ Cc w := fun w => (hsub w).2.1
  have hTnSn : ∀ e, Tn e ⊆ Sn e := fun e => (htor e).1.trans interior_subset
  have hTpSp : ∀ e, Tp e ⊆ Sp e := by
    intro e
    rw [(htube e).1, (htube e).2]
    exact image_mono (hTnSn e)
  have hAaTn : ∀ e, Aa e ⊆ Tn e := fun e => (hAa e).1 ▸ inter_subset_right
  have hAaSp : ∀ e, G (ends e).1 '' Aa e ⊆ Sp e := by
    intro e
    rw [(htube e).1]
    exact image_mono ((hAaTn e).trans (hTnSn e))
  have hBbSp' : ∀ e, G (ends e).2 '' Bb e ⊆ Sp e := fun e => (hBbSp e).1.trans interior_subset
  have hAaBd : ∀ e, Aa e ⊆ CpBd (ends e).1 := fun e => (hAa e).1 ▸ inter_subset_left
  have hAaCp : ∀ e, Aa e ⊆ Cp (ends e).1 := fun e => (hAaBd e).trans (hCp _).boundary_subset
  have hBbCp : ∀ e, Bb e ⊆ Cp (ends e).2 := fun e => (hBbP e).1.trans (hCp _).boundary_subset
  have hSpQ : ∀ e, Sp e ⊆ Q (ends e).1 ∩ Q (ends e).2 := by
    intro e
    rw [(htube e).1]
    exact subset_inter ((image_mono (hSnCc e _ (Or.inl rfl))).trans (hQ _)) (hSn e).2
  have hincFin : ∀ w, {d : Section34EdgeIndex 𝒦 𝒦' | (ends d).2 = w}.Finite := by
    intro w
    have hi : {d : Section34EdgeIndex 𝒦 𝒦' | w = (ends d).1 ∨ w = (ends d).2}.Finite :=
      Set.finite_coe_iff.mp (section34_incident_edges_finite hends' w)
    exact hi.subset fun _ hd => Or.inr hd.symm
  have hnotEnd₂ : ∀ e d, (ends d).2 = (ends e).1 →
      (ends e).2 ≠ (ends d).1 ∧ (ends e).2 ≠ (ends d).2 := by
    intro e d hd
    have hde : d ≠ e := fun h => by
      subst h
      exact hne _ hd.symm
    exact ⟨fun h => hde (section34_edge_eq_of_ends_swap hends' hd.symm h).symm,
      fun h => hne e (h.trans hd).symm⟩
  have hnotEnd₁ : ∀ e d, (ends d).2 = (ends e).2 → d ≠ e →
      (ends e).1 ≠ (ends d).1 ∧ (ends e).1 ≠ (ends d).2 := by
    intro e d hd hde
    exact ⟨fun h => hde (section34_edge_eq_of_ends_eq hends' h hd.symm).symm,
      fun h => hne e (h.trans hd)⟩
  have hΨid : ∀ w y, (∀ d, (ends d).2 = w → y ∉ K d) → Ψ w y = y :=
    fun w y hy => SupportedHomeomorphFamily.apply_of_forall_notMem
      (tgt := fun e => (ends e).2) hΨfix hy
  have hΨK : ∀ w d y, (ends d).2 = w → y ∈ K d → Ψ w y = ψ d y :=
    fun w d y hd hy => SupportedHomeomorphFamily.apply_of_mem_support
      (tgt := fun e => (ends e).2) hΨeq hd hy
  have hΨψ : ∀ e y, (∀ d, (ends d).2 = (ends e).2 → d ≠ e → y ∉ K d) →
      Ψ (ends e).2 y = ψ e y :=
    fun e y hy => SupportedHomeomorphFamily.apply_of_forall_notMem_other
      (tgt := fun e => (ends e).2) hfix hΨeq hΨfix hy
  have hΨmem : ∀ w (T : Set M₂), (∀ d, (ends d).2 = w → K d ⊆ T ∨ Disjoint (K d) T) →
      ∀ y, Ψ w y ∈ T ↔ y ∈ T :=
    fun w T hT y => SupportedHomeomorphFamily.apply_mem_iff (tgt := fun e => (ends e).2) hfix
      hΨeq hΨfix hT y
  have hΨinter₁ : ∀ w (T A : Set M₂), (∀ d, (ends d).2 = w → Disjoint (K d) T) →
      Ψ w '' A ∩ T = A ∩ T :=
    fun w T A hT => SupportedHomeomorphFamily.image_inter_eq (tgt := fun e => (ends e).2) hfix
      hΨeq hΨfix hT A
  have hΨinter₂ : ∀ e (T A : Set M₂),
      (∀ d, (ends d).2 = (ends e).2 → d ≠ e → Disjoint (K d) T) →
      Ψ (ends e).2 '' A ∩ T = ψ e '' A ∩ T :=
    fun e T A hT => SupportedHomeomorphFamily.image_inter_eq_image_inter
      (tgt := fun e => (ends e).2) hfix hKK hΨeq hΨfix hT A
  have hΨsub : ∀ w (A : Set M₂), Ψ w '' A ⊆ A ∪ ⋃ d, ⋃ (_ : (ends d).2 = w), K d :=
    fun w A => SupportedHomeomorphFamily.image_subset_union (tgt := fun e => (ends e).2) hfix
      hΨeq hΨfix w A
  have hfixSp : ∀ e w, w ≠ (ends e).2 → ∀ y ∈ Sp e, Ψ w y = y :=
    fun e w hw y hy => hΨid w y fun d hd hyd =>
      disjoint_left.mp (hKdisjSp d e fun h => hw (by subst h; exact hd.symm)) hyd hy
  have hmoveSp : ∀ e, ∀ y ∈ Sp e, Ψ (ends e).2 y = ψ e y :=
    fun e y hy => hΨψ e y fun d _ hde hyd => disjoint_left.mp (hKdisjSp d e hde) hyd hy
  have hAfix : ∀ e (X : Set M₂), X ⊆ Sp e → Ψ (ends e).1 '' X = X := by
    intro e X hX
    have hEq : EqOn (Ψ (ends e).1) id X := fun y hy => hfixSp e _ (hne e) y (hX hy)
    rw [hEq.image_eq, image_id]
  have hBmove : ∀ e (X : Set M₂), X ⊆ Sp e → Ψ (ends e).2 '' X = ψ e '' X := by
    intro e X hX
    have hEq : EqOn (Ψ (ends e).2) (ψ e) X := fun y hy => hmoveSp e y (hX hy)
    exact hEq.image_eq
  have hψSp : ∀ e y, ψ e y ∈ Sp e ↔ y ∈ Sp e :=
    fun e y => homeomorph_apply_mem_iff_of_eqOn_id_compl (ψ e) (hfix e) (hKSp e) y
  have hlensA : ∀ e (X : Set M₂), X ⊆ Sp e →
      X ∩ Ψ (ends e).1 '' (G (ends e).1 '' Cp (ends e).1) =
        X ∩ G (ends e).1 '' Cp (ends e).1 := by
    intro e X hX
    have hI := hΨinter₁ (ends e).1 (Sp e) (G (ends e).1 '' Cp (ends e).1)
      fun d hd => hKdisjSp d e fun h => hne e (by subst h; exact hd.symm)
    ext y
    constructor
    · rintro ⟨hy1, hy2⟩
      exact ⟨hy1, (hI.subset ⟨hy2, hX hy1⟩).1⟩
    · rintro ⟨hy1, hy2⟩
      exact ⟨hy1, (hI.symm.subset ⟨hy2, hX hy1⟩).1⟩
  have hlensA' : ∀ e (X : Set M₂), X ⊆ Sp e →
      X \ Ψ (ends e).1 '' (G (ends e).1 '' Cp (ends e).1) =
        X \ G (ends e).1 '' Cp (ends e).1 := by
    intro e X hX
    have hI := hΨinter₁ (ends e).1 (Sp e) (G (ends e).1 '' Cp (ends e).1)
      fun d hd => hKdisjSp d e fun h => hne e (by subst h; exact hd.symm)
    ext y
    constructor
    · rintro ⟨hy1, hy2⟩
      exact ⟨hy1, fun hy => hy2 (hI.symm.subset ⟨hy, hX hy1⟩).1⟩
    · rintro ⟨hy1, hy2⟩
      exact ⟨hy1, fun hy => hy2 (hI.subset ⟨hy, hX hy1⟩).1⟩
  have hout := fun e => section34_single_trace_carrier_motion_conditions hprep hpack e (k e)
    (ψ e) (hK e) (hKS e) (hfix e) (hψ e) (hrimA e) (hrimB e) (hkeep e) (hcancel e)
  have hsphereInter : ∀ e, Ψ (ends e).1 '' (G (ends e).1 '' CpBd (ends e).1) ∩
      Ψ (ends e).2 '' (G (ends e).2 '' CpBd (ends e).2) =
      G (ends e).1 '' CpBd (ends e).1 ∩ ψ e '' (G (ends e).2 '' CpBd (ends e).2) := by
    intro e
    apply Subset.antisymm
    · rintro y ⟨⟨u, hu, rfl⟩, ⟨v, hv, hvy⟩⟩
      by_cases hu' : ∃ d, (ends d).2 = (ends e).1 ∧ u ∈ K d
      · obtain ⟨d, hd, hud⟩ := hu'
        exfalso
        have hyd : Ψ (ends e).1 u ∈ K d := by
          rw [hΨK _ d u hd hud]
          exact (homeomorph_apply_mem_iff_of_eqOn_id_compl (ψ d) (hfix d) Subset.rfl u).mpr hud
        have hvSp : v ∈ Sp d := by
          have hyv : Ψ (ends e).2 v ∈ Sp d := by
            rw [hvy]
            exact hKSp d hyd
          exact (hΨmem (ends e).2 (Sp d) (fun d' hd' => Or.inr
            (hKdisjSp d' d fun h => by
              subst h
              exact hne e (hd.symm.trans hd'))) v).mp hyv
        exact disjoint_left.mp (hbd d (ends e).2 (hnotEnd₂ e d hd).1 (hnotEnd₂ e d hd).2) hvSp hv
      · have hΨu : Ψ (ends e).1 u = u := hΨid _ u fun d hd hud => hu' ⟨d, hd, hud⟩
        rw [hΨu] at hvy ⊢
        by_cases hv' : ∃ d, (ends d).2 = (ends e).2 ∧ d ≠ e ∧ v ∈ K d
        · obtain ⟨d, hd, hde, hvd⟩ := hv'
          exfalso
          have hud : u ∈ K d := by
            rw [← hvy, hΨK _ d v hd hvd]
            exact (homeomorph_apply_mem_iff_of_eqOn_id_compl (ψ d) (hfix d) Subset.rfl v).mpr hvd
          exact disjoint_left.mp (hbd d (ends e).1 (hnotEnd₁ e d hd hde).1
            (hnotEnd₁ e d hd hde).2) (hKSp d hud) hu
        · rw [hΨψ e v fun d hd hde hvd => hv' ⟨d, hd, hde, hvd⟩] at hvy
          exact ⟨hu, ⟨v, hv, hvy⟩⟩
    · rintro y ⟨hy, ⟨v, hv, rfl⟩⟩
      have hySp : ψ e v ∈ Sp e :=
        hTpSp e (interior_subset ((hout e).1 ⟨hy, ⟨v, hv, rfl⟩⟩).2)
      have hvSp : v ∈ Sp e := (hψSp e v).mp hySp
      exact ⟨⟨ψ e v, hy, hfixSp e _ (hne e) _ hySp⟩, ⟨v, hv, hmoveSp e v hvSp⟩⟩
  have hmarkerFix : ∀ w, Ψ w '' (G w '' simplexBody 𝒦' w.1) = G w '' simplexBody 𝒦' w.1 := by
    intro w
    have hEq : EqOn (Ψ w) id (G w '' simplexBody 𝒦' w.1) := fun y hy =>
      hΨid w y fun d _ hyd => disjoint_left.mp (hmark w d) hy (hKSp d hyd)
    rw [hEq.image_eq, image_id]
  have htraceNonempty : ∀ d, (G (ends d).1 '' Aa d ∩ G (ends d).2 '' Bb d).Nonempty :=
    fun d => section34_piercing_trace_nonempty_of_sides hprep hGp d
      (fun _ hx => image_mono sdiff_subset (hmeet d hx).1.2)
      ⟨fun _ hx => interior_subset ((hside d).1 hx), (hside d).2⟩
  refine ⟨⟨fun w => ?_, fun w => ?_, hSpQ, fun e => ?_, hlf, hdisj, fun e => ?_, fun e => ?_,
    fun e => ?_, hgraph, fun w => ?_, fun w e => ?_, fun e w hw₁ hw₂ => ?_, fun w w' hww => ?_,
    fun e => ?_, fun e => ?_, fun e => ?_, fun e i _ => ?_, fun e i hi j hj hij => ?_,
    fun e => ?_, fun e d hed => ?_, fun w w' hww => ?_⟩, fun w x hx => ?_, fun w x hx => ?_⟩
  · rw [hG' w]
    exact hΨpl w
  · rw [hG' w, image_comp]
    rintro _ ⟨y, hy, rfl⟩
    by_cases hyK : ∃ d, (ends d).2 = w ∧ y ∈ K d
    · obtain ⟨d, hd, hyd⟩ := hyK
      rw [hΨK w d y hd hyd]
      have hQd : Sp d ⊆ Q (ends d).2 := (hSpQ d).trans inter_subset_right
      rw [hd] at hQd
      exact hQd (hKSp d
        ((homeomorph_apply_mem_iff_of_eqOn_id_compl (ψ d) (hfix d) Subset.rfl y).mpr hyd))
    · rw [hΨid w y fun d hd hyd => hyK ⟨d, hd, hyd⟩]
      exact hQ w hy
  · simp only [hG', image_comp]
    rw [hAfix e _ (htube e).1.ge, hAfix e _ ((htube e).2.ge.trans (hTpSp e))]
    exact htube e
  · simp only [hG', image_comp]
    rw [hsphereInter e, hAfix e _ ((image_mono sdiff_subset).trans (hAaSp e)),
      hBmove e _ ((image_mono sdiff_subset).trans (hBbSp' e))]
    exact (hout e).1
  · simp only [hG', image_comp]
    rw [hAfix e _ ((image_mono (hAa e).2.first_subset).trans (hAaSp e)),
      hAfix e _ ((image_mono (hAa e).2.second_subset).trans (hAaSp e))]
    obtain ⟨hside1, hside2⟩ := (hout e).2.1
    have hfinite : {d : Section34EdgeIndex 𝒦 𝒦' | (ends d).2 = (ends e).2 ∧ d ≠ e}.Finite :=
      (hincFin (ends e).2).subset fun _ hd => hd.1
    have hclosed : IsClosed (⋃ d ∈ {d : Section34EdgeIndex 𝒦 𝒦' | (ends d).2 = (ends e).2 ∧
        d ≠ e}, K d) :=
      hfinite.isClosed_biUnion fun d _ => (hK d).isClosed
    have hinter := hΨinter₂ e (⋃ d ∈ {d : Section34EdgeIndex 𝒦 𝒦' | (ends d).2 = (ends e).2 ∧
        d ≠ e}, K d)ᶜ (G (ends e).2 '' Cp (ends e).2) fun d hd hde =>
      disjoint_left.mpr fun y hyK hyV => hyV (subset_biUnion_of_mem (u := K) (show d ∈ {d |
        (ends d).2 = (ends e).2 ∧ d ≠ e} from ⟨hd, hde⟩) hyK)
    have hSpV : Sp e ⊆ (⋃ d ∈ {d : Section34EdgeIndex 𝒦 𝒦' | (ends d).2 = (ends e).2 ∧
        d ≠ e}, K d)ᶜ := by
      intro y hy hyK
      obtain ⟨d, ⟨-, hde⟩, hyd⟩ := mem_iUnion₂.mp hyK
      exact disjoint_left.mp (hKdisjSp d e hde) hyd hy
    constructor
    · intro y hy
      have hyV := hSpV (hAaSp e (image_mono (hAa e).2.first_subset hy))
      rw [mem_interior_iff_mem_nhds]
      refine Filter.mem_of_superset (Filter.inter_mem (mem_interior_iff_mem_nhds.mp (hside1 hy))
        (hclosed.isOpen_compl.mem_nhds hyV)) ?_
      rw [← hinter]
      exact inter_subset_left
    · refine disjoint_left.mpr fun y hy hy' => ?_
      have hyV := hSpV (hAaSp e (image_mono (hAa e).2.second_subset hy))
      have hmem : y ∈ Ψ (ends e).2 '' (G (ends e).2 '' Cp (ends e).2) ∩ (⋃ d ∈ {d :
          Section34EdgeIndex 𝒦 𝒦' | (ends d).2 = (ends e).2 ∧ d ≠ e}, K d)ᶜ := ⟨hy', hyV⟩
      rw [hinter] at hmem
      exact disjoint_left.mp hside2 hy hmem.1
  · simp only [hG', image_comp]
    rw [hBmove e _ (hBbSp' e), hBmove e _ ((image_mono (union_subset (hBbP e).2.first_subset
      (hBbP e).2.second_subset)).trans (hBbSp' e))]
    exact (hout e).2.2.1
  · rw [hG' w]
    exact (hΨpl w).mono_of_isPLCellOn (hCp w) (hCpCc w)
  · rw [hG' w, image_comp, hmarkerFix w]
    exact hmark w e
  · rw [hG' w, image_comp, disjoint_iff_inter_eq_empty, inter_comm,
      hΨinter₁ w (Sp e) _ fun d hd => hKdisjSp d e fun h => hw₂ (by subst h; exact hd.symm),
      inter_comm,
      ← disjoint_iff_inter_eq_empty]
    exact hbd e w hw₁ hw₂
  · rw [hG' w, hG' w', image_comp, image_comp]
    by_cases hww' : w = w'
    · subst hww'
      have hempty : Cp w = ∅ :=
        Set.eq_empty_of_forall_notMem fun x hx => disjoint_left.mp hww hx hx
      simp only [hempty, image_empty]
      exact Set.empty_disjoint _
    · have hnoedge : ∀ d, ¬ ((w = (ends d).1 ∧ w' = (ends d).2) ∨
          (w = (ends d).2 ∧ w' = (ends d).1)) := by
        rintro d (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
        · obtain ⟨y, hy⟩ := htraceNonempty d
          exact disjoint_left.mp (hsep _ _ hww) (image_mono (hAaCp d) hy.1)
            (image_mono (hBbCp d) hy.2)
        · obtain ⟨y, hy⟩ := htraceNonempty d
          exact disjoint_left.mp (hsep _ _ hww) (image_mono (hBbCp d) hy.2)
            (image_mono (hAaCp d) hy.1)
      refine disjoint_of_subset (hΨsub w _) (hΨsub w' _) (disjoint_left.mpr ?_)
      rintro y (hy | hy) (hy' | hy')
      · exact disjoint_left.mp (hsep w w' hww) hy hy'
      · obtain ⟨d', hd', hyd'⟩ := mem_iUnion₂.mp hy'
        have h1 : w ≠ (ends d').1 := fun h => hnoedge d' (Or.inl ⟨h, hd'.symm⟩)
        have h2 : w ≠ (ends d').2 := fun h => hww' (h.trans hd')
        exact disjoint_left.mp (section34_support_disjoint_other_cell hprep hpack d' w h1 h2)
          (hKSp d' hyd') hy
      · obtain ⟨d, hd, hyd⟩ := mem_iUnion₂.mp hy
        have h1 : w' ≠ (ends d).1 := fun h => hnoedge d (Or.inr ⟨hd.symm, h⟩)
        have h2 : w' ≠ (ends d).2 := fun h => hww' (hd.symm.trans h.symm)
        exact disjoint_left.mp (section34_support_disjoint_other_cell hprep hpack d w' h1 h2)
          (hKSp d hyd) hy'
      · obtain ⟨d, hd, hyd⟩ := mem_iUnion₂.mp hy
        obtain ⟨d', hd', hyd'⟩ := mem_iUnion₂.mp hy'
        have hdd : d ≠ d' := fun h => by
          subst h
          exact hww' (hd.symm.trans hd')
        exact disjoint_left.mp (hKK d d' hdd) hyd hyd'
  · simp only [hG', image_comp]
    rw [hBmove e _ (hBbSp' e), hlensA e (ψ e '' (G (ends e).2 '' Bb e)) (by
      rintro _ ⟨y, hy, rfl⟩
      exact (hψSp e y).mpr (hBbSp' e hy))]
    exact (hout e).2.2.2.1
  · simp only [hG', image_comp]
    rw [hBmove e _ (hBbSp' e), hlensA' e (ψ e '' (G (ends e).2 '' Bb e)) (by
      rintro _ ⟨y, hy, rfl⟩
      exact (hψSp e y).mpr (hBbSp' e hy))]
    exact (hout e).2.2.2.2.1
  · refine ⟨by rw [hcnt' e]; exact Nat.one_pos, ?_⟩
    rw [hG' (ends e).1, hG' (ends e).2, image_comp, image_comp, hAfix e _ (hAaSp e),
      hBmove e _ (hBbSp' e), (hout e).2.2.2.2.2.1]
    ext y
    simp only [mem_iUnion, exists_prop, hPg', hcnt']
    exact ⟨fun hy => ⟨0, Nat.one_pos, hy⟩, fun ⟨_, _, hy⟩ => hy⟩
  · rw [hPg' e i, hG' (ends e).1, hG' (ends e).2, image_comp, image_comp,
      hAfix e _ ((image_mono sdiff_subset).trans (hAaSp e)),
      hBmove e _ ((image_mono sdiff_subset).trans (hBbSp' e))]
    refine ⟨(hout e).2.2.2.2.2.2.1, fun y hy => ?_⟩
    have hy' : y ∈ G (ends e).1 '' CpBd (ends e).1 ∩ ψ e '' (G (ends e).2 '' CpBd (ends e).2) := by
      rw [hcancel e]
      exact hy
    exact ((hout e).1 hy').1
  · rw [hcnt'] at hi hj
    exact absurd (by omega : i = j) hij
  · simp only [hG', image_comp]
    rw [hAfix e _ (hAaSp e), hBmove e _ (hBbSp' e)]
    exact (hout e).2.2.2.2.2.2.2
  · simp only [hG', image_comp]
    have hL : ∀ e, Ψ (ends e).1 '' (G (ends e).1 '' Cp (ends e).1) ∩
        Ψ (ends e).2 '' (G (ends e).2 '' Cp (ends e).2) ⊆
        (G (ends e).1 '' Cp (ends e).1 ∩ G (ends e).2 '' Cp (ends e).2) ∪ Sp e := by
      intro e y hy
      rcases hΨsub (ends e).1 _ hy.1 with hy1 | hy1 <;>
        rcases hΨsub (ends e).2 _ hy.2 with hy2 | hy2
      · exact Or.inl ⟨hy1, hy2⟩
      · obtain ⟨d', hd', hyd'⟩ := mem_iUnion₂.mp hy2
        rcases eq_or_ne d' e with hde | hde
        · subst hde
          exact Or.inr (hKSp _ hyd')
        · exact (disjoint_left.mp (section34_support_disjoint_other_cell hprep hpack d'
            (ends e).1 (hnotEnd₁ e d' hd' hde).1 (hnotEnd₁ e d' hd' hde).2) (hKSp d' hyd')
            hy1).elim
      · obtain ⟨d', hd', hyd'⟩ := mem_iUnion₂.mp hy1
        exact (disjoint_left.mp (section34_support_disjoint_other_cell hprep hpack d'
          (ends e).2 (hnotEnd₂ e d' hd').1 (hnotEnd₂ e d' hd').2) (hKSp d' hyd') hy2).elim
      · obtain ⟨d₁, hd₁, hyd₁⟩ := mem_iUnion₂.mp hy1
        obtain ⟨d₂, hd₂, hyd₂⟩ := mem_iUnion₂.mp hy2
        have h12 : d₁ ≠ d₂ := fun h => by
          subst h
          exact hne e (hd₁.symm.trans hd₂)
        exact (disjoint_left.mp (hKK d₁ d₂ h12) hyd₁ hyd₂).elim
    refine disjoint_of_subset (hL e) (hL d) ?_
    rw [Set.disjoint_union_left, Set.disjoint_union_right, Set.disjoint_union_right]
    exact ⟨⟨hlens e d hed, (section34_support_disjoint_other_lens hprep hpack d e hed.symm).symm⟩,
      ⟨section34_support_disjoint_other_lens hprep hpack e d hed, hdisj e d hed⟩⟩
  · rw [hG' w', image_comp]
    refine Disjoint.mono_right (hΨsub w' _) ?_
    rw [Set.disjoint_union_right]
    refine ⟨hbodysep w w' hww, disjoint_left.mpr fun y hy hyK => ?_⟩
    obtain ⟨d, -, hyd⟩ := mem_iUnion₂.mp hyK
    exact disjoint_left.mp (hgraph d) (hKSp d hyd) (image_mono w.2.2.2 hy)
  · rw [hG' w, Function.comp_apply]
    exact hΨid w (G w x) fun d _ hxd => hx.2 d (hKS d hxd)
  · rw [hG' w, Function.comp_apply]
    exact hΨid w (G w x) fun d _ hxd => disjoint_left.mp (hmark w d) ⟨x, hx, rfl⟩ (hKSp d hxd)

theorem exists_section34ConfinedTubePiercingConditions_count_eq_one
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁
      Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34PiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
      Bb₁ Sp Tp cnt Pg G) :
    ∃ (G' : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂) (cnt' : Section34EdgeIndex 𝒦 𝒦' → ℕ)
      (Pg' : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂),
      Section34ConfinedTubePiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀ Ab₁ Bb Bb₀
          Bb₁ Sp Tp cnt' Pg' G' ∧
        (∀ e, cnt' e = 1) ∧
        (∀ w, EqOn (G' w) (G w) {x ∈ Cc w | ∀ e, G w x ∉ interior (Sp e)}) ∧
        ∀ w, EqOn (G' w) (G w) (simplexBody 𝒦' w.1) := by
  classical
  choose k K ψ hK hKS hfix hψ hrimA hrimB _hout hkeep hcancel using
    fun e => exists_section34_single_trace_motion hprep hpack e
  obtain ⟨-, hCc, -, -, -, -, -, -, hends, -, -, -, hSnCc, -⟩ := id hprep
  obtain ⟨hG, -, -, htube, -, hdisj, -⟩ := id hpack
  have hends' : ∀ e, (e.1 : Set Ea) = ((ends e).1.1 : Set Ea) ∪ ((ends e).2.1 : Set Ea) :=
    fun e => (hends e).2.1
  have hKdis : Pairwise (Disjoint on K) := fun e d hed =>
    (hdisj e d hed).mono ((hKS e).trans interior_subset) ((hKS d).trans interior_subset)
  have hKO : ∀ e, K e ⊆ interior (G (ends e).1 '' Cc (ends e).1) := by
    intro e
    refine (hKS e).trans (interior_mono ?_)
    rw [(htube e).1]
    exact image_mono (hSnCc e _ (Or.inl rfl))
  obtain ⟨Ψ, hΨeq, hΨfix, hΨpl⟩ := exists_section34_vertex_supported_motions hends' K
    (fun e => interior (G (ends e).1 '' Cc (ends e).1)) ψ hKdis hfix (fun e => (hK e).isClosed)
    (fun _ => isOpen_interior) hKO hψ
  obtain ⟨hP, hoff, hmarker⟩ := section34ConfinedTubePiercingConditions_of_single_trace_motions
    hprep hpack k K ψ hK hKS hfix hψ hrimA hrimB hkeep hcancel Ψ hΨeq hΨfix
    (fun w => hΨpl w (G w) (hG w) (hCc w)) (fun w => Ψ w ∘ G w) (fun _ => rfl) (fun _ => 1)
    (fun _ => rfl) (fun e _ => Pg e (k e).val) (fun _ _ => rfl)
  exact ⟨fun w => Ψ w ∘ G w, fun _ => 1, fun e _ => Pg e (k e).val, hP, fun _ => rfl, hoff,
    hmarker⟩

end Removal

end DifferentialGeometry.Topology.PiecewiseLinear
