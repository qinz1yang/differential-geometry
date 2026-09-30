/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PositiveReferenceMaps
import DifferentialGeometry.Topology.PiecewiseLinear.MarkedCellPositiveExtension
import DifferentialGeometry.Topology.PiecewiseLinear.Section34SourceVertexAdjacency

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {Ea : Type} [NormedAddCommGroup Ea] [NormedSpace ℝ Ea] [FiniteDimensional ℝ Ea]
  {M₁ M₂ : Type u} [TopologicalSpace M₁] [T2Space M₁] [ChartedSpace E3 M₁]
  [MetricSpace M₂] [ChartedSpace E3 M₂]
  [HasGroupoid M₁ (plGroupoid 3)] [HasGroupoid M₂ (plGroupoid 3)]
  {U : Set M₁} {h : M₁ → M₂}
  {𝒦 𝒦' : LocallyFinitePLPieceIn Ea 3 M₁ U}
  {src srcBd : Section34CutLabelOf 𝒦 𝒦' → Set M₁}
  {Q Dv DvBd : Section34VertexIndex 𝒦 𝒦' → Set M₂}
  {Dd DdBd : Section34EdgeIndex 𝒦 𝒦' → Set M₂}
  {Cp CpBd Cc CcBd Kcore : Section34VertexIndex 𝒦 𝒦' → Set M₁}
  {ends : Section34EdgeIndex 𝒦 𝒦' →
    Section34VertexIndex 𝒦 𝒦' × Section34VertexIndex 𝒦 𝒦'}
  {Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ : Section34EdgeIndex 𝒦 𝒦' → Set M₁}
  {ε : Section34VertexIndex 𝒦 𝒦' → ℝ}
  {G : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂}
  {ct : Section34SimplexIndex 𝒦 3 → OpenPartialHomeomorph M₂ E3}
  {Sd : Section34SimplexIndex 𝒦 3 → Set E3}
  {Sp Tp : Section34EdgeIndex 𝒦 𝒦' → Set M₂} {cnt : Section34EdgeIndex 𝒦 𝒦' → ℕ}
  {Pg : Section34EdgeIndex 𝒦 𝒦' → ℕ → Set M₂}

private theorem isPLHomeomorphInto_id_of_cell {M : Type*} [TopologicalSpace M]
    [ChartedSpace E3 M] {d : ℕ} {D J : Set M} (hD : IsPLCellOn d D J) :
    IsPLHomeomorphInto 3 (id : M → M) D := by
  obtain ⟨P, r, u, hr, hu, hDP, -⟩ := hD
  have hi := hu.invFunOn
  have him : Function.invFunOn u P '' (u '' P) = P :=
    hu.injOn.invFunOn_image (Subset.refl P)
  have hself := hi.comp_of_image_eq (by rw [him]; exact hu)
  have heq : EqOn (u ∘ Function.invFunOn u P) id (u '' P) :=
    hu.injOn.bijOn_image.invOn_invFunOn.2
  have hid : IsPLOn 3 3 (id : M → M) (u '' P) := hself.isPLOn.congr heq.symm
  rw [hDP]
  refine ⟨hid, injOn_id _, fun y hy => ⟨id, ?_, fun _ _ => rfl⟩⟩
  have hy' : y ∈ u '' P := by simpa only [image_id] using hy
  rw [image_id]
  change ChartedSpace.LiftPropWithinAt (piecewiseAffineProperty 3 3) id (u '' P) y
  exact hid y hy'

theorem exists_section34_joint_cell_matching
    (hU : IsOpen U) (hh : Topology.IsEmbedding (U.domRestrict h))
    (hframe : Section34CutFrame U 𝒦 𝒦' src srcBd)
    (htor : Section34OuterTorus 𝒦 𝒦' h Q ct Sd)
    (hprep : Section34VertexPreparation U 𝒦 𝒦' h src Q ends
      Cp CpBd Cc CcBd Kcore Sn Tn Aa Ab₀ Ab₁ Bb Bb₀ Bb₁ Bc Bc₀ Bc₁ ε)
    (hpack : Section34ConfinedTubePiercingConditions U 𝒦 𝒦' h Q ends Cp CpBd Cc Sn Tn Aa Ab₀
      Ab₁ Bb Bb₀ Bb₁ Sp Tp cnt Pg G)
    (hDvdef : ∀ w, Dv w = G w '' Cp w \
      ⋃ (e : Section34EdgeIndex 𝒦 𝒦') (_ : (ends e).2 = w),
        interior (G (ends e).1 '' Cp (ends e).1))
    (hDv : ∀ w, IsPLCellOn 3 (Dv w) (DvBd w))
    (hDd : ∀ e, IsPLCellOn 2 (Dd e) (DdBd e))
    (hDmeet : ∀ e, Dv (ends e).1 ∩ Dv (ends e).2 = Dd e)
    (hDdBd : ∀ e, Dd e ⊆ DvBd (ends e).1 ∩ DvBd (ends e).2)
    (hDadj : ∀ w w', w ≠ w' → (Dv w ∩ Dv w').Nonempty →
      ∃ e : Section34EdgeIndex 𝒦 𝒦',
        (w = (ends e).1 ∧ w' = (ends e).2) ∨ (w = (ends e).2 ∧ w' = (ends e).1))
    (hDddisj : ∀ e d, e ≠ d → Disjoint (Dd e) (Dd d))
    (hDvQ : ∀ w, Dv w ⊆ Q w)
    (hQlf : ∀ y ∈ ⋃ w, Q w, ∃ V ∈ 𝓝 y, {w | (Q w ∩ V).Nonempty}.Finite)
    (hDnbhd : (⋃ w, Dv w) ∈ nhdsSet (h '' graphSkeletonSpace 𝒦)) :
    ∃ F : Section34VertexIndex 𝒦 𝒦' → M₁ → M₂,
      (∀ w, IsPLHomeomorphInto 3 (F w) (src (.vertexBall w))) ∧
      (∀ w, F w '' src (.vertexBall w) = Dv w) ∧
      (∀ w w', EqOn (F w) (F w') (src (.vertexBall w) ∩ src (.vertexBall w'))) ∧
      (∀ w w', F w '' (src (.vertexBall w) ∩ src (.vertexBall w')) = Dv w ∩ Dv w') ∧
      ∀ w e, (w = (ends e).1 ∨ w = (ends e).2) → F w '' src (.splitDisk e) = Dd e := by
  classical
  obtain ⟨R, δ, hR, hRim, hRD, hδ⟩ := exists_section34_positive_reference_maps
    hU hh hframe htor hprep hpack hDvdef hDv hDd hDmeet hDdBd hDddisj hDvQ hQlf hDnbhd
  obtain ⟨-, -, -, -, -, -, -, -, hends, -⟩ := id hprep
  choose b hb hbQ using exists_section34_vertex_chart hframe htor
  let θ := fun (w : Section34VertexIndex 𝒦 𝒦') (e : Section34EdgeIndex 𝒦 𝒦') =>
    if w = (ends e).1 then id else δ e
  have hθ (w : Section34VertexIndex 𝒦 𝒦') (e : Section34EdgeIndex 𝒦 𝒦') :
      IsPLHomeomorphInto 3 (θ w e) (Dd e) ∧ θ w e '' Dd e = Dd e := by
    by_cases he : w = (ends e).1
    · simpa only [θ, ite_eq_left he, image_id] using
        (show IsPLHomeomorphInto 3 (id : M₂ → M₂) (Dd e) ∧ Dd e = Dd e from
          ⟨isPLHomeomorphInto_id_of_cell (hDd e), rfl⟩)
    · simpa only [θ, ite_eq_right he] using ⟨(hδ e).1, (hδ e).2.1⟩
  have hNpoint (w : Section34VertexIndex 𝒦 𝒦') :
      ∃ N : M₂ → M₂, IsPLHomeomorphInto 3 N (Dv w) ∧ N '' Dv w = Dv w ∧
        ∀ e, (w = (ends e).1 ∨ w = (ends e).2) → EqOn N (θ w e) (Dd e) := by
    let I := {e : Section34EdgeIndex 𝒦 𝒦' // w = (ends e).1 ∨ w = (ends e).2}
    have _ : Finite I := section34_incident_edges_finite (fun e => (hends e).2.1) w
    obtain ⟨hDi, hDBi, hdisi⟩ := section34_target_vertex_boundary_disks hDd hDdBd hDddisj w
    have hpos (i : I) : IsPLCirclePositive (b w '' DdBd i.1) (b w ∘ θ w i.1 ∘ (b w).symm) := by
      have hDib : Dd i.1 ⊆ (b w).source :=
        ((hDBi i).trans (hDv w).boundary_subset).trans ((hDvQ w).trans (hbQ w))
      have hJib := (hDd i.1).boundary_subset.trans hDib
      by_cases hi : w = (ends i.1).1
      · obtain ⟨r, hr, hJ⟩ := (hDd i.1).exists_isPLHomeomorphOn_image_chart (hb w) hDib
        have hS : IsPLSphere 1 (b w '' DdBd i.1) := by
          rw [hJ]
          exact hr.isPLSphere_image_stdSimplexBoundary (n := 1)
        apply (isPLCirclePositive_id hS).of_eqOn
        rintro _ ⟨x, hx, rfl⟩
        simp only [θ, ite_eq_left hi, Function.comp_apply, id_eq]
        exact (b w).right_inv ((b w).map_source (hJib hx))
      · simpa only [θ, ite_eq_right hi] using (hδ i.1).2.2.2 (b w) hJib
    obtain ⟨N, hN, hNim, hND⟩ := (hDv w).exists_extension_of_positive_disk_family
      (fun i : I => hDi i) (fun i : I => hDBi i) (fun i j hij => hdisi hij)
      (hb w) ((hDvQ w).trans (hbQ w)) (fun i : I => (hθ w i.1).1)
      (fun i : I => (hθ w i.1).2) hpos
    exact ⟨N, hN, hNim, fun e he => hND ⟨e, he⟩⟩
  choose N hN hNim hND using hNpoint
  let F := fun w => N w ∘ R w
  have hF (w : Section34VertexIndex 𝒦 𝒦') :
      IsPLHomeomorphInto 3 (F w) (src (.vertexBall w)) :=
    (hR w).comp_of_image_eq (by rw [hRim w]; exact hN w)
  have hFim (w : Section34VertexIndex 𝒦 𝒦') : F w '' src (.vertexBall w) = Dv w := by
    change (N w ∘ R w) '' src (.vertexBall w) = _
    rw [image_comp, hRim w, hNim w]
  have hFD (w : Section34VertexIndex 𝒦 𝒦') (e : Section34EdgeIndex 𝒦 𝒦')
      (he : w = (ends e).1 ∨ w = (ends e).2) : F w '' src (.splitDisk e) = Dd e := by
    change (N w ∘ R w) '' src (.splitDisk e) = _
    rw [image_comp, hRD w e he, (hND w e he).image_eq, (hθ w e).2]
  have hedge (e : Section34EdgeIndex 𝒦 𝒦') :
      EqOn (F (ends e).1) (F (ends e).2) (src (.splitDisk e)) := by
    intro x hx
    have hx₁ : R (ends e).1 x ∈ Dd e :=
      hRD (ends e).1 e (Or.inl rfl) ▸ mem_image_of_mem (R (ends e).1) hx
    have hx₂ : R (ends e).2 x ∈ Dd e :=
      hRD (ends e).2 e (Or.inr rfl) ▸ mem_image_of_mem (R (ends e).2) hx
    have h₁ := hND (ends e).1 e (Or.inl rfl) hx₁
    have h₂ := hND (ends e).2 e (Or.inr rfl) hx₂
    simp only [θ, ite_eq_left rfl, id_eq] at h₁
    simp only [θ, ite_eq_right (hends e).1.symm] at h₂
    exact h₁.trans (((hδ e).2.2.1 hx).symm.trans h₂.symm)
  have hcompat (w w' : Section34VertexIndex 𝒦 𝒦') :
      EqOn (F w) (F w') (src (.vertexBall w) ∩ src (.vertexBall w')) := by
    by_cases hww : w = w'
    · subst w'
      exact eqOn_refl _ _
    · intro x hx
      obtain ⟨e, he, horder⟩ := exists_section34Edge_of_vertex_inter_nonempty
        hframe ends (fun e => (hends e).2.1) hww ⟨x, hx⟩
      have hxD : x ∈ src (.splitDisk e) := he.symm ▸ hx
      rcases horder with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hedge e hxD
      · exact (hedge e hxD).symm
  refine ⟨F, hF, hFim, hcompat, ?_, hFD⟩
  intro w w'
  apply Subset.antisymm
  · rintro y ⟨x, hx, rfl⟩
    refine ⟨hFim w ▸ mem_image_of_mem (F w) hx.1, ?_⟩
    rw [hcompat w w' hx]
    exact hFim w' ▸ mem_image_of_mem (F w') hx.2
  · intro y hy
    by_cases hww : w = w'
    · subst w'
      simpa only [inter_self, hFim] using hy.1
    · obtain ⟨e, horder⟩ := hDadj w w' hww ⟨y, hy⟩
      rcases horder with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rw [← (hends e).2.2, hFD _ e (Or.inl rfl), ← hDmeet e]
        exact hy
      · rw [inter_comm (src (.vertexBall (ends e).2)), ← (hends e).2.2,
          hFD _ e (Or.inr rfl), ← hDmeet e]
        exact ⟨hy.2, hy.1⟩

end DifferentialGeometry.Topology.PiecewiseLinear
