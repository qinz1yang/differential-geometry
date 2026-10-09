import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarOverlapCover
import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarGlobalHeight
import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.TwoCollarGlue
import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarOverlapApplications

/-!
# Row BCP03: actual collar overlap is the whole torus product

Blueprint 207B, BCP03 (`B:8323–8441`), with the enlarged collars `B_i⁺ = e_i{z < 92}` taken in
the original heights. Route R-V (replacing the blueprint's intrinsic-geodesic argument on the
level torus `T_i`): for overlapping collars the `i`-verticals cross the `j`-levels downward
(`NearlyCuspidalBoundary.vertical_transversal`), the two collars cover `W`
(`NearlyCuspidalBoundary.overlap_cover`), and the global heights `G_i`, `G_j` of
`CuspEmbedding.exists_global_height` satisfy every hypothesis of E7
(`CuspEmbedding.exists_diffeomorph_torus_Icc_of_two_collars`) with the band `92 ≤ G_i ≤ 93`.

* `NearlyCuspidalBoundary.bcp03_product` (product alternative): if `e_i{z < 92}` and
  `e_j{z < 92}` meet (`i ≠ j`, `W` connected, `K ≥ 1`, `0 ≤ δ ≤ 1/1000`), then `W ≅ T² × [a, b]`
  through a regular smooth height `u`, with `T² × {a}` onto `∂_i W` and `T² × {b}` onto `∂_j W`.
* `NearlyCuspidalBoundary.bcp03` (row BCP03): either some two components give the product
  above, or all enlarged collars are pairwise disjoint and then the BCP01.c inner collars
  `B̄_i = {F_i ≤ 90}` are pairwise disjoint at distance `≥ 1` (BCP03.b).
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic GC.Endpoint
  DifferentialGeometry.Topology.Manifold DifferentialGeometry.Geometry.Connection
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.Geometry.Collapse

universe u

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ} {δ : ℝ}

/-- If `G = η` near `e p`, the derivative of `G` along `De c` is the chart derivative of
`η ∘ e` along `c`. -/
theorem CuspEmbedding.mfderiv_apply_of_eventuallyEq {X : Set W.Carrier}
    (e : CuspEmbedding W g K δ X) {G η : W.Carrier → ℝ} (hη : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ η)
    {p : CuspHalfSpace} (hp : p ∈ cuspDomain) (heq : G =ᶠ[𝓝 (e.toFun p)] η)
    (c : TangentSpace halfCollarModel p) :
    (show ℝ from mfderiv W.model 𝓘(ℝ, ℝ) G (e.toFun p)
        (mfderiv halfCollarModel W.model e.toFun p c)) =
      (show ℝ from mfderiv halfCollarModel 𝓘(ℝ, ℝ) (η ∘ e.toFun) p c) := by
  have hed : MDifferentiableAt halfCollarModel W.model e.toFun p :=
    (e.contMDiffOn.contMDiffAt (isOpen_cuspDomain.mem_nhds hp)).mdifferentiableAt (by simp)
  have hηd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) η (e.toFun p) := (hη _).mdifferentiableAt (by simp)
  rw [mfderiv_comp p hηd hed, heq.mfderiv_eq]
  rfl

/-- **BCP03, product alternative.** -/
theorem NearlyCuspidalBoundary.bcp03_product [ConnectedSpace W.Carrier]
    (B : NearlyCuspidalBoundary W g K δ) (hK : 1 ≤ K) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 1000)
    {i j : Fin B.count} (hij : i ≠ j)
    (hover : ((B.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92} ∩
      (B.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}).Nonempty) :
    ∃ (u : W.Carrier → ℝ) (a b : ℝ) (hab : a < b), ContMDiff W.model 𝓘(ℝ, ℝ) ∞ u ∧
      (∀ x, mfderiv W.model 𝓘(ℝ, ℝ) u x ≠ 0) ∧
      haveI : Fact (a < b) := ⟨hab⟩
      ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) W.model (Torus × Icc a b) W.Carrier ∞,
        (∀ p, u (D p) = p.2.1) ∧ (∀ p, D p ∈ B.component i ↔ p.2.1 = a) ∧
          ∀ p, D p ∈ B.component j ↔ p.2.1 = b := by
  set ei := B.collar i with hei
  set ej := B.collar j with hej
  obtain ⟨ηi, Gi, ai, hai, hηi, hGi, hηiz, hηiv, hdηi, hHηi, hXi, hGiη, hGireg, hGi97, hGi93,
    -, hGiband⟩ := ei.exists_global_height hK hδ0 hδ (ε := 1 / 1000) (by norm_num) le_rfl
  obtain ⟨ηj, Gj, aj, -, hηj, hGj, hηjz, hηjv, hdηj, hHηj, hXj, hGjη, hGjreg, -, -, hGj96,
    -⟩ := ej.exists_global_height hK hδ0 hδ (ε := 1 / 1000) (by norm_num) le_rfl
  obtain ⟨y₀, ⟨pi, hpi, hpix⟩, ⟨pj, hpj, hpjx⟩⟩ := hover
  have hpi' : pi.2.val 0 < 92 := hpi
  have hpj' : pj.2.val 0 < 92 := hpj
  have hpid : pi ∈ cuspDomain := lt_trans hpi' (by unfold cuspDepth; norm_num)
  have hpjd : pj ∈ cuspDomain := lt_trans hpj' (by unfold cuspDepth; norm_num)
  have hp : ei.toFun pi = ej.toFun pj := hpix.trans hpjx.symm
  have hcover := B.overlap_cover hij hK hδ hηi hηj le_rfl hηiz hηiv hdηi hHηi hηjz hηjv hdηj
    hHηj hpid hpjd hpi' hpj' hp
  have hlev_ij := B.overlap_levels hij hK hδ hηj le_rfl hηjz hηjv hdηj hHηj hpjd hpi' hpj' hp
  have hlev_ji := B.overlap_levels hij.symm hK hδ hηi le_rfl hηiz hηiv hdηi hHηi hpid hpj' hpi'
    hp.symm
  obtain ⟨hs1, hs2⟩ := sqrt_one_sub_add_bounds hδ
  -- the hypotheses of E7
  have hXjc : ∀ x ∈ B.component j, 93 ≤ Gi x := by
    intro x hx
    by_contra hlt
    push Not at hlt
    obtain ⟨q, hq, rfl⟩ := hGi97 x (by linarith)
    exact B.not_mem_image_of_mem_component hij hx
      ⟨q, lt_trans (show q.2.val 0 < 98 from hq) (by unfold cuspDepth; norm_num), rfl⟩
  have hbd : ∀ x, W.model.IsBoundaryPoint x → x ∈ B.component i ∨ x ∈ B.component j := by
    intro x hx
    have hxb : x ∈ W.model.boundary W.Carrier := hx
    rcases hcover x with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · left
      have hqd : q ∈ cuspDomain := lt_trans (show q.2.val 0 < 97 from hq)
        (by unfold cuspDepth; norm_num)
      have hz := (ei.boundary_preimage hqd).mp hxb
      refine (Set.ext_iff.mp ei.boundary_image _).mp ⟨q.1, ?_⟩
      change ei.toFun (q.1, halfZero) = ei.toFun q
      rw [← cusp_eq_halfZero_of_height_eq_zero hz]
    · right
      have hqd : q ∈ cuspDomain := lt_trans (show q.2.val 0 < 97 from hq)
        (by unfold cuspDepth; norm_num)
      have hz := (ej.boundary_preimage hqd).mp hxb
      refine (Set.ext_iff.mp ej.boundary_image _).mp ⟨q.1, ?_⟩
      change ej.toFun (q.1, halfZero) = ej.toFun q
      rw [← cusp_eq_halfZero_of_height_eq_zero hz]
  have hregj : ∀ x, 93 < Gi x → mfderiv W.model 𝓘(ℝ, ℝ) Gj x ≠ 0 := by
    intro x hx
    refine hGjreg x ?_
    rcases hcover x with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
    · have hq' : q.2.val 0 < 97 := hq
      have hqd : q ∈ cuspDomain := lt_trans hq' (by unfold cuspDepth; norm_num)
      have hq93 : 9299 / 100 < q.2.val 0 := by
        by_contra hle
        push Not at hle
        linarith [hGi93 q hqd hle]
      obtain ⟨q', hq'd, hq'x, hq'z⟩ := hlev_ij q.1 (H := q.2.val 0) (by linarith) (by linarith)
      rw [← cusp_eq_lift] at hq'x
      rw [← hq'x]
      exact hGj96 q' hq'd (by linarith)
    · have hq' : q.2.val 0 < 97 := hq
      have hqd : q ∈ cuspDomain := lt_trans hq' (by unfold cuspDepth; norm_num)
      rcases lt_or_ge (q.2.val 0) (959 / 10) with hlt | hge
      · exact hGj96 q hqd hlt
      · exfalso
        obtain ⟨q', hq'd, hq'x, hq'z⟩ := hlev_ji q.1 (H := q.2.val 0) (by linarith)
          (by linarith)
        rw [← cusp_eq_lift] at hq'x
        rw [← hq'x] at hx
        linarith [hGi93 q' hq'd (by linarith)]
  have htr : ∀ x, 92 ≤ Gi x → Gi x ≤ 93 → ∃ v : TangentSpace W.model x,
      0 < (show ℝ from mfderiv W.model 𝓘(ℝ, ℝ) Gi x v) ∧
        (show ℝ from mfderiv W.model 𝓘(ℝ, ℝ) Gj x v) < 0 := by
    intro x hx1 hx2
    obtain ⟨p, hpd, rfl, hp1, hp2⟩ := hGiband x hx1 hx2
    refine ⟨mfderiv halfCollarModel W.model ei.toFun p cuspUnitVertical, ?_, ?_⟩
    · have h := ei.mfderiv_apply_of_eventuallyEq hηi hpd
        (hGiη p hpd (by linarith) (by linarith)) cuspUnitVertical
      have h2 := hηiv p hpd (by linarith) (by linarith)
      exact lt_of_lt_of_eq (lt_trans (by norm_num) h2) h.symm
    · obtain ⟨q, hqd, hqx, hqz⟩ := hlev_ij p.1 (H := p.2.val 0) (by linarith) (by linarith)
      rw [← cusp_eq_lift] at hqx
      -- the `j`-height of `q` is at least `3`
      have hq3 : 3 ≤ q.2.val 0 := by
        have hx' : ei.toFun (p.1, halfSpaceOneLift (p.2.val 0)) =
            ej.toFun (q.1, halfSpaceOneLift (q.2.val 0)) := by
          rw [← cusp_eq_lift, ← cusp_eq_lift, hqx]
        have h1 := B.height_lower_of_mem_two_collars hij p.2.2 (by linarith) q.2.2 hqd hx'
        have h2 := mul_le_mul_of_nonneg_right hs1 (by linarith : (0 : ℝ) ≤ 999 / 10 - p.2.val 0)
        have h3 := mul_le_mul_of_nonneg_right hs2 q.2.2
        nlinarith
      have hGjeq : Gj =ᶠ[𝓝 (ei.toFun p)] ηj := by
        rw [← hqx]
        exact hGjη q hqd hq3 (by linarith)
      have hηjd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) ηj (ei.toFun p) :=
        (hηj _).mdifferentiableAt (by simp)
      have hed : MDifferentiableAt halfCollarModel W.model ei.toFun p :=
        (ei.contMDiffOn.contMDiffAt (isOpen_cuspDomain.mem_nhds hpd)).mdifferentiableAt (by simp)
      have hval : (show ℝ from mfderiv W.model 𝓘(ℝ, ℝ) Gj (ei.toFun p)
          (mfderiv halfCollarModel W.model ei.toFun p cuspUnitVertical)) =
          (show ℝ from mfderiv halfCollarModel 𝓘(ℝ, ℝ) (ηj ∘ ei.toFun) p cuspUnitVertical) := by
        rw [mfderiv_comp p hηjd hed, hGjeq.mfderiv_eq]
        rfl
      rw [hval]
      have hx' : ei.toFun (p.1, halfSpaceOneLift (p.2.val 0)) =
          ej.toFun (q.1, halfSpaceOneLift (q.2.val 0)) := by
        rw [← cusp_eq_lift, ← cusp_eq_lift, hqx]
      have hB := B.vertical_transversal hij hK hδ hηj le_rfl hηjz hηjv hdηj hHηj (t := p.1)
        (h := p.2.val 0) (by linarith) (by linarith) q.2.2 (by linarith) hx'
      have hpq : (p.1, halfSpaceOneLift (p.2.val 0)) = p := (cusp_eq_lift p).symm
      have hB' : (show ℝ from mfderiv halfCollarModel 𝓘(ℝ, ℝ) (ηj ∘ ei.toFun) p
          cuspUnitVertical) ≤ -7 / 10 := by
        have h3 := hB
        rwa [hpq] at h3
      exact lt_of_le_of_lt hB' (by norm_num)
  obtain ⟨u, C, a, b, hab, hu, hureg, -, -, D, hDu, hDi, hDj⟩ :=
    ei.exists_diffeomorph_torus_Icc_of_two_collars ej (Fi := Gi) (Fj := Gj) (c₁ := 92) (c₂ := 93)
      (by norm_num) hGi hGj hXi (by linarith) hXj hXjc hbd
      (fun x hx => hGireg x (by linarith)) hregj htr
  exact ⟨u, a, b, hab, hu, hureg, D, hDu, hDi, hDj⟩

/-- **Row BCP03.** For a nearly cuspidal boundary on a connected carrier (`K ≥ 1`,
`0 ≤ δ ≤ 1/1000`): either two distinct components `i ≠ j` have overlapping enlarged collars and
`W ≅ T² × [a, b]` with `T² × {a}` onto `∂_i W` and `T² × {b}` onto `∂_j W`, or all enlarged
collars `e_i{z < 92}` are pairwise disjoint and the BCP01.c inner collars `{F_i ≤ 90}`, each
containing its boundary component, are pairwise disjoint at distance `≥ 1` (BCP03.b). -/
theorem NearlyCuspidalBoundary.bcp03 [ConnectedSpace W.Carrier]
    (B : NearlyCuspidalBoundary W g K δ) (hK : 1 ≤ K) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 1000) :
    (∃ (i j : Fin B.count), i ≠ j ∧ ∃ (u : W.Carrier → ℝ) (a b : ℝ) (hab : a < b),
      ContMDiff W.model 𝓘(ℝ, ℝ) ∞ u ∧ (∀ x, mfderiv W.model 𝓘(ℝ, ℝ) u x ≠ 0) ∧
      haveI : Fact (a < b) := ⟨hab⟩
      ∃ D : Diffeomorph (torusModel.prod (𝓡∂ 1)) W.model (Torus × Icc a b) W.Carrier ∞,
        (∀ p, u (D p) = p.2.1) ∧ (∀ p, D p ∈ B.component i ↔ p.2.1 = a) ∧
          ∀ p, D p ∈ B.component j ↔ p.2.1 = b) ∨
    ∀ i j : Fin B.count, i ≠ j →
      Disjoint ((B.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})
        ((B.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}) ∧
      ∃ Fi Fj : W.Carrier → ℝ, ContMDiff W.model 𝓘(ℝ, ℝ) ∞ Fi ∧
        ContMDiff W.model 𝓘(ℝ, ℝ) ∞ Fj ∧ (∀ x ∈ B.component i, Fi x ≤ 90) ∧
        (∀ x ∈ B.component j, Fj x ≤ 90) ∧ Disjoint {x | Fi x ≤ 90} {y | Fj y ≤ 90} ∧
        ∀ x y, Fi x ≤ 90 → Fj y ≤ 90 → ENNReal.ofReal 1 ≤ riemannianEDistOf g x y := by
  by_cases h : ∃ (i j : Fin B.count), i ≠ j ∧
      ((B.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92} ∩
        (B.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}).Nonempty
  · obtain ⟨i, j, hij, hover⟩ := h
    exact Or.inl ⟨i, j, hij, B.bcp03_product hK hδ0 hδ hij hover⟩
  · refine Or.inr fun i j hij => ?_
    have hdisj : Disjoint ((B.collar i).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92})
        ((B.collar j).toFun '' {q : CuspHalfSpace | q.2.val 0 < 92}) := by
      rw [Set.disjoint_iff_inter_eq_empty, ← Set.not_nonempty_iff_eq_empty]
      exact fun hne => h ⟨i, j, hij, hne⟩
    exact ⟨hdisj, B.bcp03b_inner_collars hK hδ0 hδ hdisj⟩

end DifferentialGeometry.Geometry.Collapse
