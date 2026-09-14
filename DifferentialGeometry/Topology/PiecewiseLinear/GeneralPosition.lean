import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorph
import Mathlib.Topology.Algebra.AffineSubspace
import Mathlib.Topology.MetricSpace.Contracting

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem IsPiecewiseAffineWithinAt.affine_comp {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → F} {s : Set E} {x : E}
    (hf : IsPiecewiseAffineWithinAt f s x) (A : F →ᵃ[ℝ] G) :
    IsPiecewiseAffineWithinAt (A ∘ f) s x := by
  obtain ⟨ι, hι, C, B, hC, hCx⟩ := hf
  refine ⟨ι, hι, C, fun i => A.comp (B i), fun i => ⟨(hC i).1, (hC i).2.1, ?_⟩, hCx⟩
  intro y hy
  change A (f y) = A (B i y)
  rw [(hC i).2.2 hy]

theorem IsPiecewiseAffineOn.affine_comp {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → F} {s : Set E}
    (hf : IsPiecewiseAffineOn f s) (A : F →ᵃ[ℝ] G) : IsPiecewiseAffineOn (A ∘ f) s :=
  fun x hx => (hf x hx).affine_comp A

theorem IsPiecewiseAffineWithinAt.prod_mk {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → F} {g : E → G} {s : Set E} {x : E}
    (hf : IsPiecewiseAffineWithinAt f s x) (hg : IsPiecewiseAffineWithinAt g s x) :
    IsPiecewiseAffineWithinAt (fun y => (f y, g y)) s x := by
  obtain ⟨ι, hι, C, A, hC, hCx⟩ := hf
  obtain ⟨κ, hκ, D, B, hD, hDx⟩ := hg
  have := hι
  have := hκ
  refine ⟨ι × κ, inferInstance, fun p => C p.1 ∩ D p.2, fun p => (A p.1).prod (B p.2),
    fun p => ⟨(hC p.1).1.inter (hD p.2).1, inter_subset_left.trans (hC p.1).2.1, ?_⟩, ?_⟩
  · intro y hy
    exact Prod.ext ((hC p.1).2.2 hy.1) ((hD p.2).2.2 hy.2)
  · have heq : (⋃ p : ι × κ, C p.1 ∩ D p.2) = (⋃ i, C i) ∩ ⋃ j, D j := by
      ext y
      simp
    rw [heq]
    exact Filter.inter_mem hCx hDx

theorem IsPiecewiseAffineOn.prod_mk {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] {f : E → F} {g : E → G} {s : Set E}
    (hf : IsPiecewiseAffineOn f s) (hg : IsPiecewiseAffineOn g s) :
    IsPiecewiseAffineOn (fun x => (f x, g x)) s :=
  fun x hx => (hf x hx).prod_mk (hg x hx)

theorem IsPiecewiseAffineOn.add {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f g : E → F} {s : Set E} (hf : IsPiecewiseAffineOn f s) (hg : IsPiecewiseAffineOn g s) :
    IsPiecewiseAffineOn (fun x => f x + g x) s :=
  (hf.prod_mk hg).affine_comp ((LinearMap.fst ℝ F F + LinearMap.snd ℝ F F).toAffineMap)

theorem IsHPolytope.inter_affine_le [FiniteDimensional ℝ E] {C : Set E} (hC : IsHPolytope C)
    (A : E →ᵃ[ℝ] ℝ) (r : ℝ) : IsHPolytope (C ∩ {x | A x ≤ r}) := by
  obtain ⟨hCc, ι, hι, l, c, rfl⟩ := hC
  have := hι
  refine ⟨hCc.inter_right (isClosed_le A.continuous_of_finiteDimensional continuous_const),
    Unit ⊕ ι, inferInstance, Sum.elim (fun _ => A.linear) l,
    Sum.elim (fun _ => r - A 0) c, ?_⟩
  ext x
  have hAx : A x = A.linear x + A 0 := by simpa using A.map_vadd 0 x
  simp only [mem_inter_iff, mem_ofPred_eq, Sum.forall, Sum.elim_inl, Sum.elim_inr, forall_const]
  constructor
  · rintro ⟨h₀, h₁⟩
    exact ⟨by rw [hAx] at h₁; linarith, h₀⟩
  · rintro ⟨h₁, h₀⟩
    exact ⟨h₀, by rw [hAx]; linarith⟩

theorem isPiecewiseAffineOn_max :
    IsPiecewiseAffineOn (fun p : ℝ × ℝ => max p.1 p.2) univ := by
  intro p _
  obtain ⟨Q, hQ, _, hQp⟩ := exists_isHPolytope_subset_mem_nhds (x := p) (U := univ) Filter.univ_mem
  let A : (ℝ × ℝ) →ᵃ[ℝ] ℝ := (LinearMap.fst ℝ ℝ ℝ - LinearMap.snd ℝ ℝ ℝ).toAffineMap
  refine ⟨Bool, inferInstance,
    (fun b => if b then Q ∩ {z | (-A) z ≤ 0} else Q ∩ {z | A z ≤ 0}),
    (fun b => if b then (LinearMap.fst ℝ ℝ ℝ).toAffineMap else (LinearMap.snd ℝ ℝ ℝ).toAffineMap),
    ?_, ?_⟩
  · intro b
    cases b with
    | false =>
      refine ⟨hQ.inter_affine_le A 0, subset_univ _, ?_⟩
      rintro z ⟨_, hz⟩
      change z.1 - z.2 ≤ 0 at hz
      exact max_eq_right (by linarith)
    | true =>
      refine ⟨hQ.inter_affine_le (-A) 0, subset_univ _, ?_⟩
      rintro z ⟨_, hz⟩
      change -(z.1 - z.2) ≤ 0 at hz
      exact max_eq_left (by linarith)
  · apply mem_nhdsWithin_of_mem_nhds
    apply Filter.mem_of_superset hQp
    intro z hz
    rcases le_total z.1 z.2 with h | h
    · exact mem_iUnion.mpr ⟨false, hz, show A z ≤ 0 by change z.1 - z.2 ≤ 0; linarith⟩
    · exact mem_iUnion.mpr ⟨true, hz, show (-A) z ≤ 0 by change -(z.1 - z.2) ≤ 0; linarith⟩

theorem IsPiecewiseAffineOn.max [FiniteDimensional ℝ E] {f g : E → ℝ} {s : Set E}
    (hf : IsPiecewiseAffineOn f s) (hg : IsPiecewiseAffineOn g s) :
    IsPiecewiseAffineOn (fun x => max (f x) (g x)) s := by
  have h := isPiecewiseAffineOn_max.comp (hf.prod_mk hg)
  rw [preimage_univ, inter_univ] at h
  exact h.congr fun _ _ => rfl

theorem IsPiecewiseAffineOn.min [FiniteDimensional ℝ E] {f g : E → ℝ} {s : Set E}
    (hf : IsPiecewiseAffineOn f s) (hg : IsPiecewiseAffineOn g s) :
    IsPiecewiseAffineOn (fun x => min (f x) (g x)) s := by
  have h := ((hf.affine_comp (-AffineMap.id ℝ ℝ)).max (hg.affine_comp (-AffineMap.id ℝ ℝ))).affine_comp
    (-AffineMap.id ℝ ℝ)
  change IsPiecewiseAffineOn (fun x => -Max.max (-f x) (-g x)) s at h
  refine h.congr fun x _ => ?_
  change Min.min (f x) (g x) = -Max.max (-f x) (-g x)
  rcases le_total (f x) (g x) with hle | hle
  · rw [min_eq_left hle, max_eq_left (neg_le_neg hle), neg_neg]
  · rw [min_eq_right hle, max_eq_right (neg_le_neg hle), neg_neg]

theorem IsPiecewiseAffineOn.abs [FiniteDimensional ℝ E] {f : E → ℝ} {s : Set E}
    (hf : IsPiecewiseAffineOn f s) : IsPiecewiseAffineOn (fun x => |f x|) s := by
  have h := hf.max (hf.affine_comp (-AffineMap.id ℝ ℝ))
  change IsPiecewiseAffineOn (fun x => Max.max (f x) (-f x)) s at h
  refine h.congr fun x _ => ?_
  change |f x| = Max.max (f x) (-f x)
  rcases le_total 0 (f x) with hle | hle
  · rw [abs_of_nonneg hle, max_eq_left (by linarith)]
  · rw [abs_of_nonpos hle, max_eq_right (by linarith)]

theorem isPiecewiseAffineOn_norm_pi {ι : Type*} [Fintype ι] :
    IsPiecewiseAffineOn (fun p : ι → ℝ => ‖p‖) univ := by
  classical
  have hs : ∀ s : Finset ι,
      IsPiecewiseAffineOn (fun p : ι → ℝ => (((s.sup fun i => (‖p i‖₊ : NNReal)) : NNReal) : ℝ)) univ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      exact isPiecewiseAffineOn_of_affine (AffineMap.const ℝ (ι → ℝ) (0 : ℝ)) isOpen_univ
    | @insert i s hi ih =>
      have hcoord : IsPiecewiseAffineOn (fun p : ι → ℝ => p i) univ :=
        isPiecewiseAffineOn_of_affine
          (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ι => ℝ) i).toLinearMap.toAffineMap isOpen_univ
      have h := hcoord.abs.max ih
      refine h.congr fun p _ => ?_
      simp only [Finset.sup_insert, NNReal.coe_max, coe_nnnorm, Real.norm_eq_abs]
  exact (hs Finset.univ).congr fun p _ => Pi.norm_def p

theorem exists_piecewiseAffine_lipschitz_cutoff_at [FiniteDimensional ℝ E] {p : E} {U : Set E}
    (hU : U ∈ 𝓝 p) :
    ∃ (φ : E → ℝ) (k : NNReal), IsPiecewiseAffineOn φ univ ∧ LipschitzWith k φ ∧
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧ φ ⁻¹' {1} ∈ 𝓝 p ∧ EqOn φ (fun _ => 0) Uᶜ := by
  classical
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hU
  let L := (Module.finBasis ℝ E).equivFunL
  let S : ℝ := ‖L.symm.toContinuousLinearMap‖ + 1
  have hS : 0 < S := by dsimp [S]; positivity
  let r : ℝ := ε / (3 * S)
  have hr : 0 < r := div_pos hε (by positivity)
  let ψ : E → ℝ := fun x => ‖L (x - p)‖
  have hψpl : IsPiecewiseAffineOn ψ univ := by
    have hB : IsPiecewiseAffineOn (fun x => L (x - p)) univ :=
      isPiecewiseAffineOn_of_affine
        (L.toLinearMap.toAffineMap.comp (AffineMap.id ℝ E - AffineMap.const ℝ E p)) isOpen_univ
    have h := isPiecewiseAffineOn_norm_pi.comp hB
    rw [preimage_univ, inter_univ] at h
    exact h.congr fun _ _ => rfl
  have hψlip : LipschitzWith ‖L.toContinuousLinearMap‖₊ ψ := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have heq : L (x - p) - L (y - p) = L (x - y) := by
      rw [← map_sub]
      congr 1
      abel
    calc dist (ψ x) (ψ y) ≤ ‖L (x - p) - L (y - p)‖ := dist_norm_norm_le _ _
      _ = ‖L (x - y)‖ := by rw [heq]
      _ ≤ ‖L.toContinuousLinearMap‖ * ‖x - y‖ := L.toContinuousLinearMap.le_opNorm _
      _ = _ := by rw [dist_eq_norm]; rfl
  have hbound : ∀ x, ‖x - p‖ ≤ S * ψ x := by
    intro x
    have h := L.symm.toContinuousLinearMap.le_opNorm (L (x - p))
    change ‖L.symm (L (x - p))‖ ≤ ‖L.symm.toContinuousLinearMap‖ * ψ x at h
    rw [L.symm_apply_apply] at h
    have hψpos : 0 ≤ ψ x := norm_nonneg _
    dsimp [S]
    nlinarith
  let g : E → ℝ := fun x => 2 - ψ x / r
  have hgpl : IsPiecewiseAffineOn g univ := by
    have h := hψpl.affine_comp (AffineMap.const ℝ ℝ 2 - r⁻¹ • AffineMap.id ℝ ℝ)
    refine h.congr fun x _ => ?_
    change 2 - ψ x / r = 2 - r⁻¹ * ψ x
    ring
  let k : NNReal := ⟨‖L.toContinuousLinearMap‖ / r, by positivity⟩
  have hglip : LipschitzWith k g := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    have h := hψlip.dist_le_mul x y
    simp only [dist_eq_norm, Real.norm_eq_abs, coe_nnnorm] at h
    change |(2 - ψ x / r) - (2 - ψ y / r)| ≤ (‖L.toContinuousLinearMap‖ / r) * dist x y
    calc
      |(2 - ψ x / r) - (2 - ψ y / r)| = |ψ x - ψ y| / r := by
        rw [show (2 - ψ x / r) - (2 - ψ y / r) = -(ψ x - ψ y) / r by ring,
          abs_div, abs_neg, abs_of_pos hr]
      _ ≤ (‖L.toContinuousLinearMap‖ * ‖x - y‖) / r := div_le_div_of_nonneg_right h hr.le
      _ = (‖L.toContinuousLinearMap‖ / r) * dist x y := by rw [dist_eq_norm]; ring
  let φ : E → ℝ := fun x => min 1 (max 0 (g x))
  have hφpl : IsPiecewiseAffineOn φ univ :=
    (isPiecewiseAffineOn_of_affine (AffineMap.const ℝ E (1 : ℝ)) isOpen_univ).min
      ((isPiecewiseAffineOn_of_affine (AffineMap.const ℝ E (0 : ℝ)) isOpen_univ).max hgpl)
  have hφlip : LipschitzWith (max 0 (max 0 k)) φ :=
    (LipschitzWith.const 1).min ((LipschitzWith.const 0).max hglip)
  refine ⟨φ, max 0 (max 0 k), hφpl, hφlip, fun x => ⟨?_, min_le_left _ _⟩, ?_, ?_⟩
  · exact le_min (by norm_num) (le_max_left _ _)
  · have hneigh : {x | ψ x < r} ∈ 𝓝 p :=
      (isOpen_lt hψlip.continuous continuous_const).mem_nhds
        (by change ‖L (p - p)‖ < r; simpa using hr)
    apply Filter.mem_of_superset hneigh
    intro x hx
    change min 1 (max 0 (2 - ψ x / r)) = 1
    apply min_eq_left
    apply le_trans _ (le_max_right _ _)
    have hdiv : ψ x / r < 1 := (div_lt_one hr).mpr hx
    linarith
  · intro x hx
    have hlarge : 2 * r ≤ ψ x := by
      by_contra h
      have hψlt : ψ x < 2 * r := lt_of_not_ge h
      apply hx
      apply hball
      change dist x p < ε
      rw [dist_eq_norm]
      calc ‖x - p‖ ≤ S * ψ x := hbound x
        _ < S * (2 * r) := mul_lt_mul_of_pos_left hψlt hS
        _ < ε := by dsimp [r]; field_simp; nlinarith
    change min 1 (max 0 (2 - ψ x / r)) = 0
    have hg : 2 - ψ x / r ≤ 0 := by
      have hdiv : 2 ≤ ψ x / r := (le_div_iff₀ hr).mpr hlarge
      linarith
    rw [max_eq_left hg, min_eq_right (by norm_num)]

theorem exists_piecewiseAffine_lipschitz_cutoff [FiniteDimensional ℝ E] {C U : Set E}
    (hC : IsCompact C) (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ (φ : E → ℝ) (k : NNReal), IsPiecewiseAffineOn φ univ ∧ LipschitzWith k φ ∧
      (∀ x, 0 ≤ φ x ∧ φ x ≤ 1) ∧ EqOn φ (fun _ => 1) C ∧ EqOn φ (fun _ => 0) Uᶜ := by
  classical
  choose f k hf hk hb hn hz using fun p : C =>
    exists_piecewiseAffine_lipschitz_cutoff_at (hU.mem_nhds (hCU p.property))
  have hcover : C ⊆ ⋃ p : C, interior (f p ⁻¹' {1}) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.mpr (hn ⟨x, hx⟩)⟩
  obtain ⟨t, ht⟩ := hC.elim_finite_subcover (fun p : C => interior (f p ⁻¹' {1}))
    (fun _ => isOpen_interior) hcover
  have hfinite : ∀ s : Finset C, ∃ (g : E → ℝ) (kg : NNReal),
      IsPiecewiseAffineOn g univ ∧ LipschitzWith kg g ∧ (∀ x, 0 ≤ g x ∧ g x ≤ 1) ∧
        EqOn g (fun _ => 0) Uᶜ ∧ ∀ i ∈ s, ∀ x, f i x ≤ g x := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨fun _ => 0, 0,
        isPiecewiseAffineOn_of_affine (AffineMap.const ℝ E (0 : ℝ)) isOpen_univ,
        LipschitzWith.const 0, fun _ => ⟨le_refl _, by norm_num⟩, fun _ _ => rfl, ?_⟩
      simp
    | @insert i s hi ih =>
      obtain ⟨g, kg, hgpl, hglip, hgb, hgz, hgdom⟩ := ih
      refine ⟨fun x => max (f i x) (g x), max (k i) kg, (hf i).max hgpl, (hk i).max hglip,
        fun x => ⟨le_trans (hb i x).1 (le_max_left _ _), max_le (hb i x).2 (hgb x).2⟩, ?_, ?_⟩
      · intro x hx
        change max (f i x) (g x) = 0
        rw [hz i hx, hgz hx, max_self]
      · intro j hj x
        rcases Finset.mem_insert.mp hj with rfl | hj
        · exact le_max_left _ _
        · exact le_trans (hgdom j hj x) (le_max_right _ _)
  obtain ⟨g, kg, hgpl, hglip, hgb, hgz, hgdom⟩ := hfinite t
  refine ⟨g, kg, hgpl, hglip, hgb, ?_, hgz⟩
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp (ht hx)
  obtain ⟨hit, hix⟩ := mem_iUnion.mp hi
  have hfx : x ∈ f i ⁻¹' {1} := interior_subset hix
  change f i x = 1 at hfx
  apply le_antisymm (hgb x).2
  rw [← hfx]
  exact hgdom i hit x

theorem isPLHomeomorphOn_id_add_of_lipschitz [FiniteDimensional ℝ E] {f : E → E} {k : NNReal}
    (hf : IsPiecewiseAffineOn f univ) (hlip : LipschitzWith k f) (hk : k < 1) :
    IsPLHomeomorphOn (fun x => x + f x) univ univ := by
  have hcon : ∀ y : E, ContractingWith k (fun x => y - f x) := by
    intro y
    refine ⟨hk, LipschitzWith.of_dist_le_mul fun x z => ?_⟩
    have heq : (y - f x) - (y - f z) = -(f x - f z) := by abel
    rw [dist_eq_norm, heq, norm_neg]
    simpa only [dist_eq_norm] using hlip.dist_le_mul x z
  have hbij : Function.Bijective (fun x => x + f x) := by
    constructor
    · intro x y hxy
      change x + f x = y + f y at hxy
      apply (hcon (x + f x)).fixedPoint_unique'
      · change x + f x - f x = x
        abel
      · change x + f x - f y = y
        rw [hxy]
        abel
    · intro y
      let x := ContractingWith.fixedPoint (fun z => y - f z) (hcon y)
      refine ⟨x, ?_⟩
      exact eq_sub_iff_add_eq.mp (hcon y).fixedPoint_isFixedPt.symm
  let g := Equiv.ofBijective (fun x => x + f x) hbij
  have hkpos : (0 : ℝ) < 1 - k := sub_pos.mpr hk
  have hginv : LipschitzWith (⟨1 / (1 - k), by positivity⟩ : NNReal) g.symm := by
    apply LipschitzWith.of_dist_le_mul
    intro y z
    have hy : g.symm y + f (g.symm y) = y := g.apply_symm_apply y
    have hz : g.symm z + f (g.symm z) = z := g.apply_symm_apply z
    have heq : g.symm y - g.symm z = (y - z) - (f (g.symm y) - f (g.symm z)) := by
      calc g.symm y - g.symm z =
          ((g.symm y + f (g.symm y)) - (g.symm z + f (g.symm z))) -
            (f (g.symm y) - f (g.symm z)) := by abel
        _ = (y - z) - (f (g.symm y) - f (g.symm z)) := by rw [hy, hz]
    have htriangle := norm_sub_le (y - z) (f (g.symm y) - f (g.symm z))
    rw [← heq] at htriangle
    have hfbound := hlip.dist_le_mul (g.symm y) (g.symm z)
    simp only [dist_eq_norm] at hfbound ⊢
    change ‖g.symm y - g.symm z‖ ≤ 1 / (1 - (k : ℝ)) * ‖y - z‖
    calc ‖g.symm y - g.symm z‖ ≤ ‖y - z‖ / (1 - k) := (le_div_iff₀ hkpos).mpr (by nlinarith)
      _ = 1 / (1 - (k : ℝ)) * ‖y - z‖ := by ring
  let e : E ≃ₜ E :=
    { toEquiv := g
      continuous_toFun := continuous_id.add hlip.continuous
      continuous_invFun := hginv.continuous }
  have hpl : IsPiecewiseAffineOn (fun x => x + f x) univ :=
    (isPiecewiseAffineOn_id isOpen_univ).add hf
  have hplinv : IsPiecewiseAffineOn e.symm univ :=
    IsPiecewiseAffineOn.symm (e := e.toOpenPartialHomeomorph) hpl
  have hbijSet : BijOn (fun x => x + f x) univ univ := by
    refine ⟨mapsTo_univ _ _, fun x _ y _ hxy => hbij.1 hxy, fun y _ => ?_⟩
    obtain ⟨x, hx⟩ := hbij.2 y
    exact ⟨x, mem_univ _, hx⟩
  refine ⟨hbijSet, hpl, hplinv.congr fun y hy => ?_⟩
  apply hbij.1
  exact (hbijSet.invOn_invFunOn.2 hy).trans (g.apply_symm_apply y).symm

theorem interior_eq_empty_of_affineSubspace_ne_top (s : AffineSubspace ℝ E) (hs : s ≠ ⊤) :
    interior (s : Set E) = ∅ := by
  by_contra hne
  obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hne
  have hxs : x ∈ s := interior_subset hx
  have hcont : ContinuousAt (fun v : E => v + x) (0 : E) := by fun_prop
  have hpre : (fun v : E => v + x) ⁻¹' (s : Set E) ∈ 𝓝 (0 : E) :=
    hcont.preimage_mem_nhds
      (by simpa only [zero_add] using mem_interior_iff_mem_nhds.mp hx)
  have hdir : (s.direction : Set E) ∈ 𝓝 (0 : E) := by
    apply Filter.mem_of_superset hpre
    intro v hv
    change v ∈ s.direction
    have hmem := AffineSubspace.vsub_mem_direction hv hxs
    simpa only [vsub_eq_sub, add_sub_cancel_right] using hmem
  exact hs ((AffineSubspace.direction_eq_top_iff_of_nonempty ⟨x, hxs⟩).mp
    (s.direction.eq_top_of_nonempty_interior' ⟨0, mem_interior_iff_mem_nhds.mpr hdir⟩))

theorem exists_mem_ball_notMem_affineSubspaces [FiniteDimensional ℝ E] {ι : Type*} [Finite ι]
    (s : ι → AffineSubspace ℝ E) (hs : ∀ i, s i ≠ ⊤) {x : E} {ε : ℝ} (hε : 0 < ε) :
    ∃ y : E, dist y x < ε ∧ ∀ i, y ∉ s i := by
  classical
  have hclosed : ∀ i, IsClosed (s i : Set E) := fun i =>
    ((s i).isClosed_direction_iff).mp ((s i).direction.closed_of_finiteDimensional)
  have hint : interior (⋃ i, (s i : Set E)) = ∅ :=
    interior_iUnion_eq_empty_of_finite hclosed fun i =>
      interior_eq_empty_of_affineSubspace_ne_top (s i) (hs i)
  by_contra h
  have hsub : ball x ε ⊆ ⋃ i, (s i : Set E) := by
    intro y hy
    by_contra hyS
    apply h
    exact ⟨y, hy, fun i hi => hyS (mem_iUnion.mpr ⟨i, hi⟩)⟩
  have hx : x ∈ interior (⋃ i, (s i : Set E)) :=
    interior_maximal hsub isOpen_ball (mem_ball_self hε)
  rw [hint] at hx
  exact hx

theorem isPLHomeomorphOn_add_const [FiniteDimensional ℝ E] (a : E) :
    IsPLHomeomorphOn (fun x => x + a) univ univ := by
  have hbij : BijOn (fun x : E => x + a) univ univ :=
    ⟨mapsTo_univ _ _, fun _ _ _ _ h => add_right_cancel h,
      fun y _ => ⟨y - a, mem_univ _, sub_add_cancel _ _⟩⟩
  refine ⟨hbij, ?_, ?_⟩
  · exact isPiecewiseAffineOn_of_affine (AffineMap.id ℝ E + AffineMap.const ℝ E a) isOpen_univ
  · have hpl : IsPiecewiseAffineOn (fun y : E => y - a) univ :=
      isPiecewiseAffineOn_of_affine (AffineMap.id ℝ E - AffineMap.const ℝ E a) isOpen_univ
    refine hpl.congr fun y hy => ?_
    exact eq_sub_iff_add_eq.mpr (hbij.invOn_invFunOn.2 hy)

open Classical in
theorem exists_small_translation_transverse_faces [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    {ε : ℝ} (hε : 0 < ε) :
    ∃ a : E, ‖a‖ < ε ∧ IsPLHomeomorphOn (fun x => x + a) univ univ ∧
      ∀ s ∈ K.faces, ∀ t ∈ L.faces,
        ((fun x => x + a) '' convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)).Nonempty →
          vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) = ⊤ := by
  let I := {p : K.faces × L.faces //
    vectorSpan ℝ (p.1.val : Set E) ⊔ vectorSpan ℝ (p.2.val : Set E) ≠ ⊤}
  let B : I → AffineSubspace ℝ E := fun p =>
    AffineSubspace.mk' (p.val.2.val.centroid ℝ id - p.val.1.val.centroid ℝ id)
      (vectorSpan ℝ (p.val.1.val : Set E) ⊔ vectorSpan ℝ (p.val.2.val : Set E))
  have hB : ∀ p, B p ≠ ⊤ := by
    intro p h
    apply p.property
    have hdir := congrArg AffineSubspace.direction h
    simpa only [B, AffineSubspace.direction_mk', AffineSubspace.direction_top] using hdir
  obtain ⟨a, ha, havoid⟩ := exists_mem_ball_notMem_affineSubspaces B hB (x := 0) hε
  refine ⟨a, by simpa only [dist_zero_right] using ha, isPLHomeomorphOn_add_const a, ?_⟩
  intro s hs t ht hinter
  by_contra hdir
  let p : I := ⟨(⟨s, hs⟩, ⟨t, ht⟩), hdir⟩
  obtain ⟨y, ⟨x, hx, rfl⟩, hy⟩ := hinter
  have hsC : s.centroid ℝ id ∈ affineSpan ℝ (s : Set E) :=
    convexHull_subset_affineSpan _ (s.centroid_mem_convexHull (K.nonempty_of_mem_faces hs))
  have htC : t.centroid ℝ id ∈ affineSpan ℝ (t : Set E) :=
    convexHull_subset_affineSpan _ (t.centroid_mem_convexHull (L.nonempty_of_mem_faces ht))
  have hxdir : x - s.centroid ℝ id ∈ vectorSpan ℝ (s : Set E) := by
    simpa only [vsub_eq_sub, direction_affineSpan] using
      AffineSubspace.vsub_mem_direction (convexHull_subset_affineSpan _ hx) hsC
  have hydir : x + a - t.centroid ℝ id ∈ vectorSpan ℝ (t : Set E) := by
    simpa only [vsub_eq_sub, direction_affineSpan] using
      AffineSubspace.vsub_mem_direction (convexHull_subset_affineSpan _ hy) htC
  apply havoid p
  change a ∈ AffineSubspace.mk' (t.centroid ℝ id - s.centroid ℝ id)
    (vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E))
  rw [AffineSubspace.mem_mk', vsub_eq_sub]
  have heq : a - (t.centroid ℝ id - s.centroid ℝ id) =
      (x + a - t.centroid ℝ id) - (x - s.centroid ℝ id) := by abel
  rw [heq]
  exact Submodule.sub_mem _ (Submodule.mem_sup_right hydir) (Submodule.mem_sup_left hxdir)

open Classical in
theorem exists_small_homeomorph_transverse_faces [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    {U : Set E} (hU : IsOpen U) (hKU : K.space ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ (a : E) (h : E → E), ‖a‖ < ε ∧ IsPLHomeomorphOn h univ univ ∧
      (∀ x, dist (h x) x < ε) ∧ EqOn h id Uᶜ ∧ EqOn h (fun x => x + a) K.space ∧
      ∀ s ∈ K.faces, ∀ t ∈ L.faces,
        (h '' convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)).Nonempty →
          vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) = ⊤ := by
  obtain ⟨φ, k, hφpl, hφlip, hφb, hφK, hφU⟩ :=
    exists_piecewiseAffine_lipschitz_cutoff (isPolyhedron_space K).isCompact hU hKU
  obtain ⟨δ, hδ, hkδ⟩ := exists_pos_mul_lt (a := (1 : ℝ)) zero_lt_one (k : ℝ)
  obtain ⟨a, ha, _, htrans⟩ := exists_small_translation_transverse_faces K L (lt_min hε hδ)
  have haε : ‖a‖ < ε := lt_of_lt_of_le ha (min_le_left _ _)
  have haδ : ‖a‖ < δ := lt_of_lt_of_le ha (min_le_right _ _)
  let f : E → E := fun x => φ x • a
  have hfpl : IsPiecewiseAffineOn f univ :=
    hφpl.affine_comp (LinearMap.toSpanSingleton ℝ E a).toAffineMap
  have hflip : LipschitzWith (k * ‖a‖₊) f := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    rw [dist_eq_norm]
    change ‖φ x • a - φ y • a‖ ≤ (↑(k * ‖a‖₊) : ℝ) * dist x y
    rw [← sub_smul, norm_smul, NNReal.coe_mul, coe_nnnorm]
    have h := hφlip.dist_le_mul x y
    rw [dist_eq_norm] at h
    calc ‖φ x - φ y‖ * ‖a‖ ≤ ((k : ℝ) * dist x y) * ‖a‖ :=
        mul_le_mul_of_nonneg_right h (norm_nonneg _)
      _ = (k : ℝ) * ‖a‖ * dist x y := by ring
  have hsmall : k * ‖a‖₊ < 1 := by
    change (k : ℝ) * ‖a‖ < 1
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left haδ.le k.coe_nonneg) hkδ
  let h : E → E := fun x => x + f x
  have heq : EqOn h (fun x => x + a) K.space := by
    intro x hx
    change x + φ x • a = x + a
    rw [hφK hx, one_smul]
  refine ⟨a, h, haε, isPLHomeomorphOn_id_add_of_lipschitz hfpl hflip hsmall, ?_, ?_, heq, ?_⟩
  · intro x
    change dist (x + φ x • a) x < ε
    rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg (hφb x).1]
    exact lt_of_le_of_lt (by nlinarith [(hφb x).2, norm_nonneg a]) haε
  · intro x hx
    change x + φ x • a = x
    rw [hφU hx, zero_smul, add_zero]
  · intro s hs t ht hinter
    apply htrans s hs t ht
    obtain ⟨y, ⟨x, hx, rfl⟩, hy⟩ := hinter
    refine ⟨h x, ⟨x, hx, (heq (K.convexHull_subset_space hs hx)).symm⟩, hy⟩

end DifferentialGeometry.Topology.PiecewiseLinear
