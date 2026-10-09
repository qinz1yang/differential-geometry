/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import DifferentialGeometry.Geometry.Hyperbolic.LorentzModel.Orbifolds.Strata

noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.ProjectiveOrthogonalGroup
open scoped Topology

namespace DifferentialGeometry.FiniteStratumRadius

open Hyperbolic HyperbolicAction HyperbolicFaithful HyperbolicTransitive
open OrbifoldStrata

section FiniteGroup

variable {G : Type*} [Group G] [Finite G]

theorem length_le_card_mul (S : Set G) (hgen : Subgroup.closure S = ⊤)
    (hSinv : ∀ s ∈ S, s⁻¹ ∈ S) (d : G → ℝ) (hd1 : d 1 = 0)
    (hdmul : ∀ a b, d (a * b) ≤ d a + d b)
    {r : ℝ} (hr : 0 ≤ r) (hS : ∀ s ∈ S, d s ≤ r) (g : G) :
    d g ≤ (Nat.card G : ℝ) * r := by
  classical
  let : Fintype G := Fintype.ofFinite G
  by_contra hbad
  have hbad' : (Nat.card G : ℝ) * r < d g := lt_of_not_ge hbad
  have hsets : ∀ k : ℕ, k ≤ Nat.card G →
      ∃ F : Finset G, F.card = k + 1 ∧ ∀ a ∈ F, d a ≤ (k : ℝ) * r := by
    intro k
    induction k with
    | zero =>
      intro _
      exact ⟨{1}, by simp, by simp [hd1]⟩
    | succ k ih =>
      intro hk
      obtain ⟨F, hcard, hbound⟩ := ih (by omega)
      have hproper : g ∉ F := by
        intro hg
        have hle : (k : ℝ) * r ≤ (Nat.card G : ℝ) * r :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast (show k ≤ Nat.card G by omega)) hr
        exact (not_lt_of_ge ((hbound g hg).trans hle)) hbad'
      obtain ⟨s, hs, a, ha, hout⟩ :=
        CosetGrowth.exists_generator_exit S hgen hSinv F
          (Finset.card_pos.mp (by omega)) ⟨g, hproper⟩
      change s * a ∉ F at hout
      refine ⟨insert (s * a) F, by rw [Finset.card_insert_of_notMem hout, hcard], ?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · have h := (hdmul s a).trans (add_le_add (hS s hs) (hbound a ha))
        push_cast
        linarith
      · have h := hbound b hb
        push_cast
        nlinarith
  obtain ⟨F, hcard, _⟩ := hsets (Nat.card G) le_rfl
  have hle := Finset.card_le_card (Finset.subset_univ F)
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hcard] at hle
  omega

private theorem exists_pos_lt_all {ι : Type*} [Finite ι]
    (f : ι → ℝ) (hf : ∀ i, 0 < f i) : ∃ δ : ℝ, 0 < δ ∧ ∀ i, δ < f i := by
  have h : {t : ℝ | ∀ i, t < f i} ∈ 𝓝 0 :=
    eventually_all.mpr (fun i => isOpen_Iio.mem_nhds (hf i))
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp h
  refine ⟨δ / 2, half_pos hδ, hball ?_⟩
  rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
  linarith

theorem exists_small_generators_fix
    {X : Type*} [MetricSpace X] [CompactSpace X]
    [MulAction G X] [ContinuousConstSMul G X] :
    ∃ η : ℝ, 0 < η ∧ ∀ x : X, ∃ p : X,
      ∀ g : G, dist (g • x) x ≤ η → g • p = p := by
  classical
  let : Fintype G := Fintype.ofFinite G
  have hlocal (p : X) : ∃ U : Set X, IsOpen U ∧ p ∈ U ∧
      ∃ η : ℝ, 0 < η ∧ ∀ x ∈ U, ∀ g : G, dist (g • x) x ≤ η → g • p = p := by
    have hpos (g : {g : G // g • p ≠ p}) : 0 < dist (g.val • p) p :=
      dist_pos.mpr g.property
    obtain ⟨η, hη, hsmall⟩ : ∃ η : ℝ, 0 < η ∧
        ∀ g : {g : G // g • p ≠ p}, η < dist (g.val • p) p :=
      exists_pos_lt_all _ hpos
    let U : Set X := ⋂ g : {g : G // g • p ≠ p}, {x | η < dist (g.val • x) x}
    have hU : IsOpen U := isOpen_iInter_of_finite fun g =>
      isOpen_lt continuous_const ((continuous_const_smul g.val).dist continuous_id)
    refine ⟨U, hU, mem_iInter.mpr hsmall, η, hη, ?_⟩
    intro x hx g hg
    by_contra hnot
    exact (not_lt_of_ge hg) (mem_iInter.mp hx ⟨g, hnot⟩)
  choose U hU hp η hη hfix using hlocal
  obtain ⟨T, hT⟩ := isCompact_univ.elim_finite_subcover U hU (by
    intro x _
    exact mem_iUnion.mpr ⟨x, hp x⟩)
  obtain ⟨δ, hδ, hδle⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ p ∈ T, δ < η p := by
    obtain ⟨δ, hδ, hδle⟩ := exists_pos_lt_all (fun p : T => η p) (fun p => hη p)
    exact ⟨δ, hδ, fun p hp => hδle ⟨p, hp⟩⟩
  refine ⟨δ, hδ, fun x => ?_⟩
  obtain ⟨p, hpT, hx⟩ := mem_iUnion₂.mp (hT (mem_univ x))
  exact ⟨p, fun g hg => hfix p x hx g (hg.trans (hδle p hpT).le)⟩

theorem exists_small_subgroup_fix
    {X : Type*} [MetricSpace X] [CompactSpace X]
    [MulAction G X] [ContinuousConstSMul G X] :
    ∃ η : ℝ, 0 < η ∧ ∀ x : X, ∃ p : X,
      ∀ g ∈ Subgroup.closure {g : G | dist (g • x) x ≤ η}, g • p = p := by
  obtain ⟨η, hη, hfix⟩ := exists_small_generators_fix (G := G) (X := X)
  refine ⟨η, hη, fun x => ?_⟩
  obtain ⟨p, hp⟩ := hfix x
  have hle : Subgroup.closure {g : G | dist (g • x) x ≤ η} ≤
      MulAction.stabilizer G p :=
    (Subgroup.closure_le _).mpr (fun g hg => hp g hg)
  exact ⟨p, fun g hg => hle hg⟩

end FiniteGroup

variable {n : ℕ}

theorem exists_fixed_point_dist_le (hn : 1 ≤ n) (D : Subgroup (PO n 1))
    [Finite D] (x : HUpper n) {R : ℝ}
    (hR : ∀ γ : D, dist ((poMulAction hn).smul (γ : PO n 1) x) x ≤ R) :
    ∃ q ∈ fixedLocus hn D, dist x q ≤ R := by
  classical
  let := poMulAction hn
  obtain ⟨g, hg⟩ := exists_po_smul_basepoint hn x
  change g • basepointH = x at hg
  let E := D.map (MulAut.conj g⁻¹).toMonoidHom
  let : Finite E := EquivariantMap.finite_subgroupMap _ D
  let : Fintype E := Fintype.ofFinite E
  have hbound : EquivariantMap.orbitRadius hn E ≤ R := by
    apply Finset.sup'_le
    intro a _
    obtain ⟨b, hb, he⟩ := a.property
    change g⁻¹ * b * (g⁻¹)⁻¹ = (a : PO n 1) at he
    rw [inv_inv] at he
    change dist basepointH ((a : PO n 1) • basepointH) ≤ R
    rw [← he]
    calc
      dist basepointH ((g⁻¹ * b * g) • basepointH) =
          dist (g • basepointH) (g • ((g⁻¹ * b * g) • basepointH)) :=
        (po_dist_smul hn g _ _).symm
      _ = dist x (b • x) := by simp only [mul_smul, smul_inv_smul, hg]
      _ ≤ R := by rw [dist_comm]; exact hR ⟨b, hb⟩
  obtain ⟨q, hq, hdist⟩ := EquivariantMap.exists_fixed_point_of_finite_subgroup hn E
  refine ⟨g • q, ?_, ?_⟩
  · intro γ
    have hm : g⁻¹ * (γ : PO n 1) * g ∈ E := ⟨γ, γ.property, by simp⟩
    have he := hq _ hm
    change (γ : PO n 1) • (g • q) = g • q
    calc
      (γ : PO n 1) • (g • q) = g • ((g⁻¹ * (γ : PO n 1) * g) • q) := by
        simp only [mul_smul, smul_inv_smul]
      _ = g • q := by rw [he]
  · have hd : dist q basepointH ≤ EquivariantMap.orbitRadius hn E := by
      simpa only [Subgroup.coe_one, one_smul] using hdist 1
    rw [← hg, po_dist_smul hn, dist_comm]
    exact hd.trans hbound

theorem displacement_closedSmallSubgroup_le (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    {ε : ℝ} (hε : 0 ≤ ε) (x : HUpper n)
    [Finite (closedSmallSubgroup hn Γ ε x)] (γ : closedSmallSubgroup hn Γ ε x) :
    dist ((poMulAction hn).smul (γ : PO n 1) x) x ≤
      (Nat.card (closedSmallSubgroup hn Γ ε x) : ℝ) * ε := by
  let := poMulAction hn
  let D := closedSmallSubgroup hn Γ ε x
  let S : Set D := D.subtype ⁻¹' closedSmallElements hn Γ ε x
  have hSinv : ∀ a ∈ S, a⁻¹ ∈ S := by
    intro a ha
    change (a : PO n 1) ∈ Γ ∧ dist ((a : PO n 1) • x) x ≤ ε at ha
    change (a : PO n 1)⁻¹ ∈ Γ ∧ dist ((a : PO n 1)⁻¹ • x) x ≤ ε
    refine ⟨Γ.inv_mem ha.1, ?_⟩
    calc
      dist ((a : PO n 1)⁻¹ • x) x =
          dist ((a : PO n 1) • ((a : PO n 1)⁻¹ • x)) ((a : PO n 1) • x) :=
        (po_dist_smul hn _ _ _).symm
      _ = dist ((a : PO n 1) • x) x := by rw [smul_inv_smul, dist_comm]
      _ ≤ ε := ha.2
  apply length_le_card_mul S (Subgroup.closure_preimage_eq_top _) hSinv
    (fun a : D => dist ((a : PO n 1) • x) x)
    (by change dist ((1 : PO n 1) • x) x = 0; rw [one_smul, dist_self])
    ?_ hε (fun _ ha => ha.2) γ
  intro a b
  change dist (((a : PO n 1) * (b : PO n 1)) • x) x ≤ _
  rw [mul_smul]
  calc
    dist ((a : PO n 1) • ((b : PO n 1) • x)) x ≤
        dist ((a : PO n 1) • ((b : PO n 1) • x)) ((a : PO n 1) • x) +
          dist ((a : PO n 1) • x) x := dist_triangle _ _ _
    _ = dist ((a : PO n 1) • x) x + dist ((b : PO n 1) • x) x := by
      rw [po_dist_smul hn, add_comm]

theorem exists_radius_fixedStratum (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) {ε : ℝ} (hε : 0 ≤ ε)
    {σ : Set (HUpper n)} (hσ : σ.Nonempty) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x ∈ fixedStratum hn Γ ε σ,
      ∃ q ∈ σ, dist x q ≤ R := by
  obtain ⟨p, hp⟩ := hσ
  let := EquivariantMap.subAction hn Γ
  let G := MulAction.stabilizer Γ p
  let : Finite G := EquivariantMap.finite_stabilizer hn Γ hΓ p
  refine ⟨(Nat.card G : ℝ) * ε, mul_nonneg (Nat.cast_nonneg _) hε, ?_⟩
  intro x hx
  let D := closedSmallSubgroup hn Γ ε x
  have hpx : p ∈ fixedLocus hn D := by
    rw [show fixedLocus hn D = σ from hx]
    exact hp
  let ι : D → G := fun γ =>
    ⟨⟨γ, closedSmallSubgroup_le hn Γ ε x γ.property⟩, hpx γ⟩
  have hinj : Function.Injective ι := by
    intro a b he
    exact Subtype.ext (congrArg (fun u : G => ((u : Γ) : PO n 1)) he)
  let : Finite D := Finite.of_injective ι hinj
  have hcard : Nat.card D ≤ Nat.card G := Nat.card_le_card_of_injective ι hinj
  obtain ⟨q, hq, hd⟩ := exists_fixed_point_dist_le hn D x
    (R := (Nat.card G : ℝ) * ε) (fun γ =>
    (displacement_closedSmallSubgroup_le hn Γ hε x γ).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hε))
  exact ⟨q, (show fixedLocus hn D = σ from hx) ▸ hq, hd⟩

theorem exists_radius_closure_fixedStratum (hn : 1 ≤ n) (Γ : Subgroup (PO n 1))
    (hΓ : IsDiscrete (SetLike.coe Γ)) {ε : ℝ} (hε : 0 ≤ ε)
    {σ : Set (HUpper n)} (hσ : σ.Nonempty)
    (hF : (fixedStratum hn Γ ε σ).Nonempty) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ x ∈ closure (fixedStratum hn Γ ε σ),
      ∃ q ∈ σ, dist x q ≤ R := by
  obtain ⟨z, hz⟩ := hF
  have hclosed : IsClosed σ :=
    (show fixedLocus hn (closedSmallSubgroup hn Γ ε z) = σ from hz) ▸
      isClosed_fixedLocus hn _
  obtain ⟨R, hR, hbound⟩ := exists_radius_fixedStratum hn Γ hΓ hε hσ
  have hsub : fixedStratum hn Γ ε σ ⊆ {x | Metric.infDist x σ ≤ R} := by
    intro x hx
    obtain ⟨q, hq, hd⟩ := hbound x hx
    exact (Metric.infDist_le_dist_of_mem hq).trans hd
  have hc : IsClosed {x : HUpper n | Metric.infDist x σ ≤ R} :=
    isClosed_le (Metric.continuous_infDist_pt σ) continuous_const
  have hb := hc.closure_subset_iff.mpr hsub
  refine ⟨R, hR, fun x hx => ?_⟩
  obtain ⟨q, hq, he⟩ := hclosed.exists_infDist_eq_dist hσ x
  exact ⟨q, hq, he ▸ hb hx⟩

end DifferentialGeometry.FiniteStratumRadius
