import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorph
import DifferentialGeometry.Topology.PiecewiseLinear.Triangulation
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubdivision
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

open Classical in
theorem card_add_finrank_le_of_subset_transverse_faces [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) {s t u : Finset E} (hs : s ∈ K.faces)
    (ht : t ∈ L.faces) (hu : AffineIndependent ℝ ((↑) : u → E)) (hune : u.Nonempty)
    (a : E) (hsub : (u : Set E) ⊆ (fun x => x + a) '' convexHull ℝ (s : Set E) ∩
      convexHull ℝ (t : Set E))
    (htrans : vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) = ⊤) :
    u.card + Module.finrank ℝ E + 1 ≤ s.card + t.card := by
  have hspan : vectorSpan ℝ (u : Set E) ≤
      vectorSpan ℝ (s : Set E) ⊓ vectorSpan ℝ (t : Set E) := by
    rw [vectorSpan_def, Submodule.span_le]
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_vsub.mp hz
    obtain ⟨⟨x', hx', hxx'⟩, hxt⟩ := hsub hx
    obtain ⟨⟨y', hy', hyy'⟩, hyt⟩ := hsub hy
    constructor
    · have hmem := AffineSubspace.vsub_mem_direction
        (convexHull_subset_affineSpan _ hx') (convexHull_subset_affineSpan _ hy')
      rw [direction_affineSpan] at hmem
      change x - y ∈ vectorSpan ℝ (s : Set E)
      rw [← hxx', ← hyy']
      simpa only [vsub_eq_sub, add_sub_add_right_eq_sub] using hmem
    · change x -ᵥ y ∈ vectorSpan ℝ (t : Set E)
      simpa only [direction_affineSpan] using AffineSubspace.vsub_mem_direction
        (convexHull_subset_affineSpan _ hxt) (convexHull_subset_affineSpan _ hyt)
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (vectorSpan ℝ (s : Set E)) (vectorSpan ℝ (t : Set E))
  rw [htrans] at hdim
  have hdim' : Module.finrank ℝ E +
      Module.finrank ℝ (vectorSpan ℝ (s : Set E) ⊓ vectorSpan ℝ (t : Set E) : Submodule ℝ E) =
        Module.finrank ℝ (vectorSpan ℝ (s : Set E)) +
          Module.finrank ℝ (vectorSpan ℝ (t : Set E)) := by simpa using hdim
  have hmono := Submodule.finrank_mono hspan
  obtain ⟨sv, hsv⟩ := K.nonempty_of_mem_faces hs
  obtain ⟨tv, htv⟩ := L.nonempty_of_mem_faces ht
  obtain ⟨uv, huv⟩ := hune
  have : Nonempty s := ⟨⟨sv, hsv⟩⟩
  have : Nonempty t := ⟨⟨tv, htv⟩⟩
  have : Nonempty u := ⟨⟨uv, huv⟩⟩
  have hrange : ∀ v : Finset E, Set.range ((↑) : v → E) = (v : Set E) := by
    intro v
    ext x
    simp
  have hscard : Module.finrank ℝ (vectorSpan ℝ (s : Set E)) + 1 = s.card := by
    have h := (K.indep hs).finrank_vectorSpan_add_one
    change Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : s → E))) + 1 = Fintype.card s at h
    rw [hrange s] at h
    simpa only [Fintype.card_coe] using h
  have htcard : Module.finrank ℝ (vectorSpan ℝ (t : Set E)) + 1 = t.card := by
    have h := (L.indep ht).finrank_vectorSpan_add_one
    change Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → E))) + 1 = Fintype.card t at h
    rw [hrange t] at h
    simpa only [Fintype.card_coe] using h
  have hucard : Module.finrank ℝ (vectorSpan ℝ (u : Set E)) + 1 = u.card := by
    have h := hu.finrank_vectorSpan_add_one
    change Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : u → E))) + 1 = Fintype.card u at h
    rw [hrange u] at h
    simpa only [Fintype.card_coe] using h
  omega

open Classical in
theorem exists_triangulation_inter_of_transverse_faces [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces] (a : E)
    (htrans : ∀ s ∈ K.faces, ∀ t ∈ L.faces,
      ((fun x => x + a) '' convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)).Nonempty →
        vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) = ⊤) :
    ∃ G : Geometry.SimplicialComplex ℝ E, G.faces.Finite ∧
      G.space = (fun x => x + a) '' K.space ∩ L.space ∧
      ∀ u ∈ G.faces, ∃ s ∈ K.faces, ∃ t ∈ L.faces,
        convexHull ℝ (u : Set E) ⊆
          (fun x => x + a) '' convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ∧
        u.card + Module.finrank ℝ E + 1 ≤ s.card + t.card := by
  let C : K.faces × L.faces → Set E := fun p =>
    (fun x => x + a) '' convexHull ℝ (p.1.val : Set E) ∩ convexHull ℝ (p.2.val : Set E)
  have hC : ∀ p, IsHPolytope (C p) := by
    intro p
    have h := (isHPolytope_convexHull_of_affineIndependent p.1.val (K.indep p.1.property)).image_affineEquiv
      (AffineEquiv.constVAdd ℝ E a)
    have heq : (⇑(AffineEquiv.constVAdd ℝ E a) : E → E) = fun x => x + a := by
      funext x
      change a + x = x + a
      exact add_comm _ _
    rw [heq] at h
    exact h.inter (isHPolytope_convexHull_of_affineIndependent p.2.val (L.indep p.2.property))
  obtain ⟨G, hfin, hspace, hcover⟩ := exists_simplicialComplex_of_forall_isHPolytope C hC
  have hspace' : G.space = (fun x => x + a) '' K.space ∩ L.space := by
    rw [hspace]
    ext x
    constructor
    · intro hx
      obtain ⟨p, ⟨y, hy, rfl⟩, hyt⟩ := mem_iUnion.mp hx
      exact ⟨⟨y, K.convexHull_subset_space p.1.property hy, rfl⟩,
        L.convexHull_subset_space p.2.property hyt⟩
    · rintro ⟨⟨y, hy, rfl⟩, hxL⟩
      obtain ⟨s, hs, hys⟩ := K.mem_space_iff.mp hy
      obtain ⟨t, ht, hxt⟩ := L.mem_space_iff.mp hxL
      exact mem_iUnion.mpr ⟨(⟨s, hs⟩, ⟨t, ht⟩), ⟨y, hys, rfl⟩, hxt⟩
  refine ⟨G, hfin, hspace', fun u hu => ?_⟩
  have huc : u.centroid ℝ id ∈ openSimplex u := centroid_mem_openSimplex (G.nonempty_of_mem_faces hu)
  have hucG : u.centroid ℝ id ∈ G.space :=
    G.convexHull_subset_space hu (openSimplex_subset_convexHull u huc)
  obtain ⟨p, hp⟩ := mem_iUnion.mp (hspace ▸ hucG)
  have hpne : (C p).Nonempty := ⟨_, hp⟩
  rw [hcover p] at hp
  obtain ⟨v, ⟨hv, hvC⟩, hcv⟩ := mem_iUnion₂.mp hp
  have huv : u ⊆ v := face_subset_of_mem_openSimplex_of_mem_convexHull G hu hv huc hcv
  have huC : convexHull ℝ (u : Set E) ⊆ C p :=
    (convexHull_mono (Finset.coe_subset.mpr huv)).trans hvC
  refine ⟨p.1.val, p.1.property, p.2.val, p.2.property, huC, ?_⟩
  exact card_add_finrank_le_of_subset_transverse_faces K L p.1.property p.2.property
    (G.indep hu) (G.nonempty_of_mem_faces hu) a ((subset_convexHull ℝ _).trans huC)
    (htrans p.1.val p.1.property p.2.val p.2.property hpne)

open Classical in
theorem exists_small_homeomorph_inter_dimension_le [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces] {m n : ℕ}
    (hK : ∀ s ∈ K.faces, s.card ≤ m + 1) (hL : ∀ t ∈ L.faces, t.card ≤ n + 1)
    {U : Set E} (hU : IsOpen U) (hKU : K.space ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ (h : E → E) (G : Geometry.SimplicialComplex ℝ E), IsPLHomeomorphOn h univ univ ∧
      (∀ x, dist (h x) x < ε) ∧ EqOn h id Uᶜ ∧ G.faces.Finite ∧
      G.space = h '' K.space ∩ L.space ∧
      ∀ u ∈ G.faces, u.card + Module.finrank ℝ E + 1 ≤ m + n + 2 := by
  obtain ⟨a, h, _, hpl, hclose, hout, heq, htrans⟩ :=
    exists_small_homeomorph_transverse_faces K L hU hKU hε
  have htrans' : ∀ s ∈ K.faces, ∀ t ∈ L.faces,
      ((fun x => x + a) '' convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)).Nonempty →
        vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) = ⊤ := by
    intro s hs t ht hinter
    obtain ⟨z, ⟨x, hx, rfl⟩, hz⟩ := hinter
    exact htrans s hs t ht ⟨x + a, ⟨x, hx, heq (K.convexHull_subset_space hs hx)⟩, hz⟩
  obtain ⟨G, hfin, hspace, hdim⟩ := exists_triangulation_inter_of_transverse_faces K L a htrans'
  have himage : h '' K.space = (fun x => x + a) '' K.space := by
    apply image_congr
    exact heq
  refine ⟨h, G, hpl, hclose, hout, hfin, ?_, fun u hu => ?_⟩
  · rw [himage]
    exact hspace
  · obtain ⟨s, hs, t, ht, _, hcard⟩ := hdim u hu
    have hsbound := hK s hs
    have htbound := hL t ht
    omega

theorem isPLBall_zero_iff [FiniteDimensional ℝ E] {P : Set E} :
    IsPLBall 0 P ↔ ∃ p, P = {p} := by
  constructor
  · rintro ⟨f, hf⟩
    refine ⟨f (fun _ => 1), ?_⟩
    have himage : f '' stdSimplex ℝ (Fin 1) = P := hf.bijOn.image_eq
    rw [← himage, stdSimplex_unique ℝ (Fin 1), image_singleton]
  · rintro ⟨p, rfl⟩
    classical
    have : Subsingleton ({p} : Finset E) :=
      ⟨fun a b => Subtype.ext ((Finset.mem_singleton.mp a.property).trans
        (Finset.mem_singleton.mp b.property).symm)⟩
    have h := isPLBall_convexHull_of_affineIndependent ({p} : Finset E)
      (affineIndependent_of_subsingleton ℝ _) (n := 0) (by simp)
    simpa only [Finset.coe_singleton, convexHull_singleton] using h

theorem stdSimplexBoundary_one_eq_pair :
    stdSimplexBoundary 1 = {(![1, 0] : Fin 2 → ℝ), (![0, 1] : Fin 2 → ℝ)} := by
  have hleft : (![1, 0] : Fin 2 → ℝ) ∈ stdSimplexBoundary 1 := by
    change (![1, 0] : Fin 2 → ℝ) ∈ stdSimplex ℝ (Fin 2) ∧ ∃ i : Fin 2, (![1, 0] : Fin 2 → ℝ) i = 0
    refine ⟨⟨fun i => ?_, ?_⟩, 1, by norm_num⟩
    · fin_cases i <;> norm_num
    · norm_num [Fin.sum_univ_two]
  have hright : (![0, 1] : Fin 2 → ℝ) ∈ stdSimplexBoundary 1 := by
    change (![0, 1] : Fin 2 → ℝ) ∈ stdSimplex ℝ (Fin 2) ∧ ∃ i : Fin 2, (![0, 1] : Fin 2 → ℝ) i = 0
    refine ⟨⟨fun i => ?_, ?_⟩, 0, by norm_num⟩
    · fin_cases i <;> norm_num
    · norm_num [Fin.sum_univ_two]
  ext x
  constructor
  · rintro ⟨⟨_, hsum⟩, i, hi⟩
    rw [Fin.sum_univ_two] at hsum
    fin_cases i
    · change x 0 = 0 at hi
      apply mem_insert_of_mem
      apply mem_singleton_iff.mpr
      funext j
      fin_cases j
      · simpa using hi
      · change x 1 = 1
        linarith
    · change x 1 = 0 at hi
      apply mem_insert_iff.mpr
      left
      funext j
      fin_cases j
      · change x 0 = 1
        linarith
      · simpa using hi
  · intro hx
    rcases mem_insert_iff.mp hx with rfl | hx
    · exact hleft
    · rw [mem_singleton_iff] at hx
      exact hx ▸ hright

theorem isPLSphere_zero_iff [FiniteDimensional ℝ E] {P : Set E} :
    IsPLSphere 0 P ↔ ∃ a b, a ≠ b ∧ P = {a, b} := by
  constructor
  · rintro ⟨f, hf⟩
    have hleft : (![1, 0] : Fin 2 → ℝ) ∈ stdSimplexBoundary 1 := by
      rw [stdSimplexBoundary_one_eq_pair]
      exact mem_insert _ _
    have hright : (![0, 1] : Fin 2 → ℝ) ∈ stdSimplexBoundary 1 := by
      rw [stdSimplexBoundary_one_eq_pair]
      exact mem_insert_of_mem _ (mem_singleton _)
    refine ⟨f ![1, 0], f ![0, 1], ?_, ?_⟩
    · intro h
      have hvec := hf.bijOn.injOn hleft hright h
      have hzero := congrFun hvec 0
      norm_num at hzero
    · rw [← hf.bijOn.image_eq, stdSimplexBoundary_one_eq_pair, image_pair]
  · rintro ⟨a, b, hab, rfl⟩
    classical
    have hrange : Set.range (![a, b] : Fin 2 → E) = (({a, b} : Finset E) : Set E) := by
      ext x
      simp [or_comm]
    have hi := (affineIndependent_of_ne ℝ hab).range
    change AffineIndependent ℝ ((↑) : Set.range (![a, b] : Fin 2 → E) → E) at hi
    rw [hrange] at hi
    have h := isPLSphere_biUnion_erase ({a, b} : Finset E) hi (n := 0) (by simp [hab])
    simpa [hab, hab.symm, Set.pair_comm] using h

open Classical in
theorem geometricLink_space_eq_coface_vertices_of_card_le (K : Geometry.SimplicialComplex ℝ E)
    (s : Finset E) (hK : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card + 1) :
    (SimplicialComplex.geometricLink K s).space = {w | w ∉ s ∧ insert w s ∈ K.faces} := by
  ext x
  constructor
  · intro hx
    obtain ⟨t, ht, hxt⟩ := (SimplicialComplex.geometricLink K s).mem_space_iff.mp hx
    obtain ⟨htne, hdis, hunion⟩ := (mem_geometricLink_faces_iff K).mp ht
    have hcard := hK (s ∪ t) hunion Finset.subset_union_left
    rw [Finset.card_union_of_disjoint hdis] at hcard
    have htcard : t.card = 1 := by
      have hpos := Finset.card_pos.mpr htne
      omega
    obtain ⟨w, rfl⟩ := Finset.card_eq_one.mp htcard
    rw [Finset.coe_singleton, convexHull_singleton] at hxt
    have hxw : x = w := hxt
    subst x
    refine ⟨fun hw => Finset.disjoint_left.mp hdis hw (Finset.mem_singleton_self w), ?_⟩
    simpa only [Finset.union_singleton] using hunion
  · rintro ⟨hxs, hface⟩
    have ht : ({x} : Finset E) ∈ (SimplicialComplex.geometricLink K s).faces := by
      refine (mem_geometricLink_faces_iff K).mpr ⟨Finset.singleton_nonempty x, ?_, ?_⟩
      · exact Finset.disjoint_left.mpr fun y hy hyx => hxs (Finset.mem_singleton.mp hyx ▸ hy)
      · simpa only [Finset.union_singleton] using hface
    exact (SimplicialComplex.geometricLink K s).convexHull_subset_space ht (by simp)

open Classical in
theorem geometricLink_space_eq_neighbors_of_card_le (G : Geometry.SimplicialComplex ℝ E)
    (hG : ∀ s ∈ G.faces, s.card ≤ 2) (v : E) :
    (SimplicialComplex.geometricLink G {v}).space = {w | w ≠ v ∧ {v, w} ∈ G.faces} := by
  have hbound : ∀ u ∈ G.faces, ({v} : Finset E) ⊆ u → u.card ≤ ({v} : Finset E).card + 1 := by
    intro u hu _
    simpa only [Finset.card_singleton] using hG u hu
  rw [geometricLink_space_eq_coface_vertices_of_card_le G {v} hbound]
  ext w
  change (w ∉ ({v} : Finset E) ∧ insert w {v} ∈ G.faces) ↔ w ≠ v ∧ {v, w} ∈ G.faces
  simp only [Finset.mem_singleton, Finset.pair_comm]

open Classical in
theorem isCombinatorialManifoldWithBoundary_one_iff [FiniteDimensional ℝ E]
    (G : Geometry.SimplicialComplex ℝ E) [Finite G.faces] :
    IsCombinatorialManifoldWithBoundary 1 G ↔ (∀ s ∈ G.faces, s.card ≤ 2) ∧
      ∀ v, {v} ∈ G.faces →
        (∃ a, {w | w ≠ v ∧ {v, w} ∈ G.faces} = {a}) ∨
        ∃ a b, a ≠ b ∧ {w | w ≠ v ∧ {v, w} ∈ G.faces} = {a, b} := by
  constructor
  · intro hG
    have hcard : ∀ s ∈ G.faces, s.card ≤ 2 := fun s hs => hG.card_le G hs
    refine ⟨hcard, fun v hv => ?_⟩
    have hlink : IsPLSphere 0 (SimplicialComplex.geometricLink G {v}).space ∨
        IsPLBall 0 (SimplicialComplex.geometricLink G {v}).space := hG v hv
    rw [geometricLink_space_eq_neighbors_of_card_le G hcard v] at hlink
    exact hlink.symm.imp isPLBall_zero_iff.mp isPLSphere_zero_iff.mp
  · rintro ⟨hcard, hneighbors⟩ v hv
    change IsPLSphere 0 (SimplicialComplex.geometricLink G {v}).space ∨
      IsPLBall 0 (SimplicialComplex.geometricLink G {v}).space
    rw [geometricLink_space_eq_neighbors_of_card_le G hcard v]
    exact ((hneighbors v hv).imp isPLBall_zero_iff.mpr isPLSphere_zero_iff.mpr).symm

open Classical in
theorem exists_weights_zero_of_mem_vectorSpan {s : Finset E} {d : E}
    (hd : d ∈ vectorSpan ℝ (s : Set E)) :
    ∃ c : E → ℝ, ∑ v ∈ s, c v = 0 ∧ ∑ v ∈ s, c v • v = d := by
  have hrange : Set.range ((↑) : s → E) = (s : Set E) := by ext x; simp
  rw [← hrange] at hd
  obtain ⟨t, w, hw, hwd⟩ := (mem_vectorSpan_iff_eq_weightedVSub ℝ).mp hd
  rw [Finset.weightedVSub_eq_linear_combination t hw] at hwd
  let c : E → ℝ := fun v => if hv : v ∈ s then if (⟨v, hv⟩ : s) ∈ t then w ⟨v, hv⟩ else 0 else 0
  have hc : ∀ v : s, c v = if v ∈ t then w v else 0 := by
    intro v
    simp only [c, dif_pos v.property, Subtype.coe_eta]
  refine ⟨c, ?_, ?_⟩
  · rw [← Finset.sum_coe_sort s c]
    simp only [hc, Finset.sum_ite_mem, Finset.univ_inter]
    exact hw
  · rw [← Finset.sum_coe_sort s (fun v => c v • v)]
    simp only [hc, ite_smul, zero_smul, Finset.sum_ite_mem, Finset.univ_inter]
    exact hwd.symm

theorem eventually_mem_openSimplex_of_mem_vectorSpan {s : Finset E} {x d : E}
    (hx : x ∈ openSimplex s) (hd : d ∈ vectorSpan ℝ (s : Set E)) :
    ∀ᶠ t : ℝ in 𝓝 0, x + t • d ∈ openSimplex s := by
  classical
  obtain ⟨α, hαpos, hαsum, hαx⟩ := hx
  obtain ⟨β, hβsum, hβd⟩ := exists_weights_zero_of_mem_vectorSpan hd
  have hopen : IsOpen (⋂ v : s, {t : ℝ | 0 < α v + t * β v}) :=
    isOpen_iInter_of_finite fun _ => isOpen_lt continuous_const (by fun_prop)
  have hzero : (0 : ℝ) ∈ ⋂ v : s, {t : ℝ | 0 < α v + t * β v} := by
    apply mem_iInter.mpr
    intro v
    simpa using hαpos v v.property
  apply Filter.mem_of_superset (hopen.mem_nhds hzero)
  intro t ht
  refine ⟨fun v => α v + t * β v, fun v hv => mem_iInter.mp ht ⟨v, hv⟩, ?_, ?_⟩
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, hαsum, hβsum, mul_zero, add_zero]
  · simp_rw [add_smul, mul_smul]
    rw [Finset.sum_add_distrib, ← Finset.smul_sum, hαx, hβd]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.codimension_one_cofaces [FiniteDimensional ℝ E]
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) {s : Finset E} (hs : s ∈ K.faces)
    (hcard : s.card = n + 1) :
    (∃ a, {w | w ∉ s ∧ insert w s ∈ K.faces} = {a}) ∨
      ∃ a b, a ≠ b ∧ {w | w ∉ s ∧ insert w s ∈ K.faces} = {a, b} := by
  have hlink := hK.isPLSphere_or_isPLBall_geometricLink K hs hcard le_rfl
  rw [Nat.sub_self] at hlink
  have hbound : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card + 1 := by
    intro u hu _
    rw [hcard]
    exact hK.card_le K hu
  rw [geometricLink_space_eq_coface_vertices_of_card_le K s hbound] at hlink
  exact hlink.symm.imp isPLBall_zero_iff.mp isPLSphere_zero_iff.mp

open Classical in
theorem eventually_mem_openSimplex_insert_of_mem_vectorSpan {s : Finset E} {x d w : E}
    (hx : x ∈ openSimplex s) (hd : d ∈ vectorSpan ℝ (s : Set E)) (hw : w ∉ s) :
    ∀ᶠ t : ℝ in 𝓝 0, 0 < t → x + t • (w - x + d) ∈ openSimplex (insert w s) := by
  obtain ⟨α, hαpos, hαsum, hαx⟩ := hx
  obtain ⟨β, hβsum, hβd⟩ := exists_weights_zero_of_mem_vectorSpan hd
  have hopen : IsOpen (⋂ v : s, {t : ℝ | 0 < α v + t * (β v - α v)}) :=
    isOpen_iInter_of_finite fun _ => isOpen_lt continuous_const (by fun_prop)
  have hzero : (0 : ℝ) ∈ ⋂ v : s, {t : ℝ | 0 < α v + t * (β v - α v)} := by
    apply mem_iInter.mpr
    intro v
    simpa using hαpos v v.property
  apply Filter.mem_of_superset (hopen.mem_nhds hzero)
  intro t ht htpos
  let c : E → ℝ := fun v => if v = w then t else α v + t * (β v - α v)
  have hcw : c w = t := if_pos rfl
  have hcs : ∀ v ∈ s, c v = α v + t * (β v - α v) :=
    fun v hv => if_neg (ne_of_mem_of_not_mem hv hw)
  refine ⟨c, ?_, ?_, ?_⟩
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · rw [hcw]
      exact htpos
    · rw [hcs v hv]
      exact mem_iInter.mp ht ⟨v, hv⟩
  · rw [Finset.sum_insert hw, hcw, Finset.sum_congr rfl hcs, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_sub_distrib, hαsum, hβsum]
    ring
  · rw [Finset.sum_insert hw, hcw,
      Finset.sum_congr rfl (fun v hv => by rw [hcs v hv])]
    simp_rw [add_smul, mul_smul, sub_smul]
    rw [Finset.sum_add_distrib, ← Finset.smul_sum, Finset.sum_sub_distrib, hαx, hβd]
    module

open Classical in
theorem exists_direction_into_simplex_of_transverse_submodule {s : Finset E} {x w : E}
    (hx : x ∈ openSimplex s) (hw : w ∉ affineSpan ℝ (s : Set E)) (V : Submodule ℝ E)
    (htrans : vectorSpan ℝ (s : Set E) ⊔ V = ⊤) :
    ∃ d ∈ V, d ≠ 0 ∧
      ∀ᶠ t : ℝ in 𝓝 0, 0 < t → x + t • d ∈ openSimplex (insert w s) := by
  have hmem : w - x ∈ vectorSpan ℝ (s : Set E) ⊔ V := htrans ▸ Submodule.mem_top
  obtain ⟨u, hu, d, hd, hud⟩ := Submodule.mem_sup.mp hmem
  have hdne : d ≠ 0 := by
    intro hd0
    rw [hd0, add_zero] at hud
    have hdir : w - x ∈ (affineSpan ℝ (s : Set E)).direction := by
      rw [direction_affineSpan, ← hud]
      exact hu
    have hxp : x ∈ affineSpan ℝ (s : Set E) :=
      convexHull_subset_affineSpan _ (openSimplex_subset_convexHull s hx)
    have hwspan := AffineSubspace.vadd_mem_of_mem_direction hdir hxp
    apply hw
    simpa only [vadd_eq_add, sub_add_cancel] using hwspan
  have hws : w ∉ s := fun h => hw (mem_affineSpan ℝ (Finset.mem_coe.mpr h))
  have heq : w - x + -u = d := by rw [← hud]; abel
  have hray := eventually_mem_openSimplex_insert_of_mem_vectorSpan hx
    (Submodule.neg_mem _ hu) hws
  rw [heq] at hray
  exact ⟨d, hd, hdne, hray⟩

open Classical in
theorem exists_ray_into_transverse_face {s t : Finset E} {x w a : E}
    (hx : x ∈ openSimplex s) (hy : x + a ∈ openSimplex t)
    (hw : w ∉ affineSpan ℝ (s : Set E))
    (htrans : vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) = ⊤) :
    ∃ d, d ≠ 0 ∧ ∀ᶠ r : ℝ in 𝓝 0, 0 < r →
      x + r • d ∈ openSimplex (insert w s) ∧ x + a + r • d ∈ openSimplex t := by
  obtain ⟨d, hd, hdne, hs⟩ :=
    exists_direction_into_simplex_of_transverse_submodule hx hw (vectorSpan ℝ (t : Set E)) htrans
  have ht := eventually_mem_openSimplex_of_mem_vectorSpan hy hd
  refine ⟨d, hdne, ?_⟩
  filter_upwards [hs, ht] with r hrs hrt
  exact fun hr => ⟨hrs hr, hrt⟩

open Classical in
theorem exists_ray_mem_geometricLink_space_of_eventually (G : Geometry.SimplicialComplex ℝ E)
    [Finite G.faces] {x d : E} (hx : {x} ∈ G.faces) (hd : d ≠ 0)
    (hG : ∀ᶠ r : ℝ in 𝓝 0, 0 < r → x + r • d ∈ G.space) :
    ∃ c : ℝ, 0 < c ∧ x + c • d ∈ (SimplicialComplex.geometricLink G {x}).space := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hG
  let y := x + (ε / 2) • d
  have hy : y ≠ x := by
    intro h
    have hzero : (ε / 2) • d = 0 := by
      have heq : x + (ε / 2) • d = x + 0 := h.trans (add_zero x).symm
      exact add_left_cancel heq
    exact hd ((smul_eq_zero.mp hzero).resolve_left (by positivity))
  have hseg : ∀ t : ℝ, 0 < t → t ≤ 1 → x + t • (y - x) ∈ G.space := by
    intro t ht ht1
    have hpos : 0 < t * (ε / 2) := mul_pos ht (by positivity)
    have hlt : t * (ε / 2) < ε := by nlinarith
    have hmem : t * (ε / 2) ∈ ball (0 : ℝ) ε := by
      simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hpos] using hlt
    have h := hball hmem hpos
    have heq : x + t • (y - x) = x + (t * (ε / 2)) • d := by
      dsimp [y]
      rw [add_sub_cancel_left, smul_smul]
    rwa [heq]
  obtain ⟨c, hc, hclink⟩ := exists_ray_mem_geometricLink_space G hx hseg hy
  refine ⟨c * (ε / 2), mul_pos hc (by positivity), ?_⟩
  simpa only [y, add_sub_cancel_left, smul_smul] using hclink

open Classical in
theorem exists_neighbor_on_ray_of_eventually (G : Geometry.SimplicialComplex ℝ E) [Finite G.faces]
    (hcard : ∀ s ∈ G.faces, s.card ≤ 2) {x d : E} (hx : {x} ∈ G.faces) (hd : d ≠ 0)
    (hG : ∀ᶠ r : ℝ in 𝓝 0, 0 < r → x + r • d ∈ G.space) :
    ∃ c : ℝ, 0 < c ∧ x + c • d ≠ x ∧ {x, x + c • d} ∈ G.faces := by
  obtain ⟨c, hc, hclink⟩ := exists_ray_mem_geometricLink_space_of_eventually G hx hd hG
  rw [geometricLink_space_eq_neighbors_of_card_le G hcard x] at hclink
  exact ⟨c, hc, hclink⟩

open Classical in
theorem exists_pos_smul_sub_eq_of_mem_transverse_cone {s : Finset E} {x w y z : E}
    (hx : x ∈ convexHull ℝ (s : Set E))
    (hy : y ∈ convexHull ℝ ((insert w s : Finset E) : Set E))
    (hz : z ∈ convexHull ℝ ((insert w s : Finset E) : Set E)) (hyx : y ≠ x) (hzx : z ≠ x)
    (V : Submodule ℝ E) (hyV : y - x ∈ V) (hzV : z - x ∈ V)
    (hdis : Disjoint (vectorSpan ℝ (s : Set E)) V) :
    ∃ c : ℝ, 0 < c ∧ y - x = c • (z - x) := by
  have hnot : ∀ q, q - x ∈ V → q ≠ x → q ∉ convexHull ℝ (s : Set E) := by
    intro q hqV hqx hq
    have hdir : q - x ∈ vectorSpan ℝ (s : Set E) := by
      simpa only [direction_affineSpan, vsub_eq_sub] using AffineSubspace.vsub_mem_direction
        (convexHull_subset_affineSpan _ hq) (convexHull_subset_affineSpan _ hx)
    exact hqx (sub_eq_zero.mp (Submodule.disjoint_def.mp hdis _ hdir hqV))
  have hw : w ∉ s := by
    intro hws
    rw [Finset.insert_eq_of_mem hws] at hy
    exact hnot y hyV hyx hy
  have hcombo : ∀ q ∈ convexHull ℝ ((insert w s : Finset E) : Set E), q - x ∈ V → q ≠ x →
      ∃ p ∈ convexHull ℝ (s : Set E), ∃ c : ℝ, 0 < c ∧
        q - x = c • (w - x) + (1 - c) • (p - x) := by
    intro q hq hqV hqx
    rcases exists_combo_of_mem_convexHull_insert hw hq with rfl | ⟨p, hp, c, hc, hc1, hqc⟩
    · exact ⟨x, hx, 1, one_pos, by simp⟩
    · have hclt : c < 1 := lt_of_le_of_ne hc1 (by
        intro hcEq
        rw [hcEq, one_smul, add_sub_cancel] at hqc
        exact hnot q hqV hqx (hqc ▸ hp))
      refine ⟨p, hp, 1 - c, by linarith, ?_⟩
      rw [hqc]
      module
  obtain ⟨p, hp, α, hα, hyp⟩ := hcombo y hy hyV hyx
  obtain ⟨q, hq, β, hβ, hzq⟩ := hcombo z hz hzV hzx
  have hpdir : p - x ∈ vectorSpan ℝ (s : Set E) := by
    simpa only [direction_affineSpan, vsub_eq_sub] using AffineSubspace.vsub_mem_direction
      (convexHull_subset_affineSpan _ hp) (convexHull_subset_affineSpan _ hx)
  have hqdir : q - x ∈ vectorSpan ℝ (s : Set E) := by
    simpa only [direction_affineSpan, vsub_eq_sub] using AffineSubspace.vsub_mem_direction
      (convexHull_subset_affineSpan _ hq) (convexHull_subset_affineSpan _ hx)
  have heq : β • (y - x) - α • (z - x) =
      (β * (1 - α)) • (p - x) - (α * (1 - β)) • (q - x) := by
    rw [hyp, hzq]
    module
  have hdir : β • (y - x) - α • (z - x) ∈ vectorSpan ℝ (s : Set E) := by
    rw [heq]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hpdir) (Submodule.smul_mem _ _ hqdir)
  have hV : β • (y - x) - α • (z - x) ∈ V :=
    Submodule.sub_mem _ (Submodule.smul_mem _ _ hyV) (Submodule.smul_mem _ _ hzV)
  have hzero : β • (y - x) = α • (z - x) :=
    sub_eq_zero.mp (Submodule.disjoint_def.mp hdis _ hdir hV)
  refine ⟨α / β, div_pos hα hβ, ?_⟩
  calc y - x = β⁻¹ • (β • (y - x)) := by rw [smul_smul, inv_mul_cancel₀ hβ.ne', one_smul]
    _ = β⁻¹ • (α • (z - x)) := by rw [hzero]
    _ = (α / β) • (z - x) := by rw [smul_smul, div_eq_inv_mul]

open Classical in
theorem notMem_affineSpan_of_affineIndependent_insert {s : Finset E} {w : E} (hw : w ∉ s)
    (hs : AffineIndependent ℝ ((↑) : ↥(insert w s : Finset E) → E)) :
    w ∉ affineSpan ℝ (s : Set E) := by
  let I : Set ↥(insert w s : Finset E) := {v | (v : E) ∈ s}
  have himage : ((↑) : ↥(insert w s : Finset E) → E) '' I = (s : Set E) := by
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro hy
      exact ⟨⟨y, Finset.mem_insert_of_mem hy⟩, hy, rfl⟩
  have hiff := hs.mem_affineSpan_iff (⟨w, Finset.mem_insert_self _ _⟩ : ↥(insert w s : Finset E)) I
  rw [himage] at hiff
  exact fun h => hw (hiff.mp h)

open Classical in
theorem exists_neighbor_mem_convexHull_of_eventually (K G : Geometry.SimplicialComplex ℝ E)
    [Finite G.faces] (hcard : ∀ u ∈ G.faces, u.card ≤ 2)
    (hcarrier : ∀ u ∈ G.faces, ∃ v ∈ K.faces,
      convexHull ℝ (u : Set E) ⊆ convexHull ℝ (v : Set E))
    {s : Finset E} (hs : s ∈ K.faces)
    (hmax : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card) {x d : E}
    (hx : {x} ∈ G.faces) (hd : d ≠ 0)
    (hray : ∀ᶠ r : ℝ in 𝓝 0, 0 < r →
      x + r • d ∈ G.space ∧ x + r • d ∈ openSimplex s) :
    ∃ y, y ≠ x ∧ {x, y} ∈ G.faces ∧ y ∈ convexHull ℝ (s : Set E) := by
  have hrayG : ∀ᶠ r : ℝ in 𝓝 0, 0 < r → x + r • d ∈ G.space := by
    filter_upwards [hray] with r hr
    exact fun hpos => (hr hpos).1
  obtain ⟨c, hc, hyx, hyface⟩ := exists_neighbor_on_ray_of_eventually G hcard hx hd hrayG
  obtain ⟨u, hu, hsub⟩ := hcarrier _ hyface
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hray
  let r : ℝ := min (ε / 2) (c / 2)
  have hr : 0 < r := lt_min (by positivity) (by positivity)
  have hrε : r < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hrc : r ≤ c := le_trans (min_le_right _ _) (by linarith)
  have hmem : r ∈ ball (0 : ℝ) ε := by
    simpa only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hr] using hrε
  have hqs : x + r • d ∈ openSimplex s := (hball hmem hr).2
  have hqedge : x + r • d ∈ convexHull ℝ (({x, x + c • d} : Finset E) : Set E) := by
    rw [Finset.coe_pair, convexHull_pair, segment_eq_image]
    refine ⟨r / c, ⟨div_nonneg hr.le hc.le, (div_le_one hc).mpr hrc⟩, ?_⟩
    change (1 - r / c) • x + (r / c) • (x + c • d) = x + r • d
    rw [← add_smul_sub_eq_combo, add_sub_cancel_left, smul_smul, div_mul_cancel₀ _ hc.ne']
  have hsu := face_subset_of_mem_openSimplex_of_mem_convexHull K hs hu hqs (hsub hqedge)
  have hueq : u = s := (Finset.eq_of_subset_of_card_le hsu (hmax u hu hsu)).symm
  refine ⟨x + c • d, hyx, hyface, ?_⟩
  rw [← hueq]
  exact hsub (subset_convexHull ℝ _ (by simp))

open Classical in
theorem existsUnique_neighbor_mem_transverse_coface (K L G : Geometry.SimplicialComplex ℝ E)
    [Finite G.faces] (hcard : ∀ u ∈ G.faces, u.card ≤ 2)
    (hspace : G.space = K.space ∩ L.space)
    (hcarrier : ∀ u ∈ G.faces, ∃ v ∈ K.faces, ∃ z ∈ L.faces,
      convexHull ℝ (u : Set E) ⊆ convexHull ℝ (v : Set E) ∩ convexHull ℝ (z : Set E))
    {s t : Finset E} (ht : t ∈ L.faces)
    (hsbound : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card + 1)
    (htmax : ∀ u ∈ L.faces, t ⊆ u → u.card ≤ t.card) {x w : E}
    (hx : x ∈ openSimplex s) (hxt : x ∈ openSimplex t) (hxG : {x} ∈ G.faces)
    (hw : w ∉ s) (hws : insert w s ∈ K.faces)
    (htrans : IsCompl (vectorSpan ℝ (s : Set E)) (vectorSpan ℝ (t : Set E))) :
    ∃! y, y ≠ x ∧ {x, y} ∈ G.faces ∧
      y ∈ convexHull ℝ ((insert w s : Finset E) : Set E) := by
  have hwspan := notMem_affineSpan_of_affineIndependent_insert hw (K.indep hws)
  have hxt0 : x + 0 ∈ openSimplex t := by simpa only [add_zero] using hxt
  obtain ⟨d, hd, hray⟩ := exists_ray_into_transverse_face hx hxt0 hwspan htrans.sup_eq_top
  have hcoface : ∀ u ∈ K.faces, insert w s ⊆ u → u.card ≤ (insert w s).card := by
    intro u hu hsub
    rw [Finset.card_insert_of_notMem hw]
    exact hsbound u hu (Finset.subset_insert _ _ |>.trans hsub)
  have hrayG : ∀ᶠ r : ℝ in 𝓝 0, 0 < r →
      x + r • d ∈ G.space ∧ x + r • d ∈ openSimplex (insert w s) := by
    filter_upwards [hray] with r hr hpos
    have h := hr hpos
    have hLt : x + r • d ∈ openSimplex t := by simpa only [add_zero] using h.2
    refine ⟨?_, h.1⟩
    rw [hspace]
    exact ⟨K.convexHull_subset_space hws (openSimplex_subset_convexHull _ h.1),
      L.convexHull_subset_space ht (openSimplex_subset_convexHull _ hLt)⟩
  have hcarrierK : ∀ u ∈ G.faces, ∃ v ∈ K.faces,
      convexHull ℝ (u : Set E) ⊆ convexHull ℝ (v : Set E) := by
    intro u hu
    obtain ⟨v, hv, z, _, hsub⟩ := hcarrier u hu
    exact ⟨v, hv, fun q hq => (hsub hq).1⟩
  obtain ⟨y, hyx, hyface, hyws⟩ := exists_neighbor_mem_convexHull_of_eventually K G hcard
    hcarrierK hws hcoface hxG hd hrayG
  have hdir : ∀ q, {x, q} ∈ G.faces → q - x ∈ vectorSpan ℝ (t : Set E) := by
    intro q hq
    obtain ⟨u, _, v, hv, hsub⟩ := hcarrier _ hq
    have hxv : x ∈ convexHull ℝ (v : Set E) := (hsub (subset_convexHull ℝ _ (by simp))).2
    have htv := face_subset_of_mem_openSimplex_of_mem_convexHull L ht hv hxt hxv
    have hvt : v = t := (Finset.eq_of_subset_of_card_le htv (htmax v hv htv)).symm
    have hqv : q ∈ convexHull ℝ (v : Set E) := (hsub (subset_convexHull ℝ _ (by simp))).2
    rw [hvt] at hqv
    simpa only [direction_affineSpan, vsub_eq_sub] using AffineSubspace.vsub_mem_direction
      (convexHull_subset_affineSpan _ hqv)
      (convexHull_subset_affineSpan _ (openSimplex_subset_convexHull _ hxt))
  refine ⟨y, ⟨hyx, hyface, hyws⟩, ?_⟩
  rintro z ⟨hzx, hzface, hzws⟩
  obtain ⟨c, hc, heq⟩ := exists_pos_smul_sub_eq_of_mem_transverse_cone
    (openSimplex_subset_convexHull _ hx) hzws hyws hzx hyx (vectorSpan ℝ (t : Set E))
    (hdir z hzface) (hdir y hyface) htrans.disjoint
  have hylink : y ∈ (SimplicialComplex.geometricLink G {x}).space := by
    rw [geometricLink_space_eq_neighbors_of_card_le G hcard x]
    exact ⟨hyx, hyface⟩
  have hzlink : z ∈ (SimplicialComplex.geometricLink G {x}).space := by
    rw [geometricLink_space_eq_neighbors_of_card_le G hcard x]
    exact ⟨hzx, hzface⟩
  apply isRadiallyInjective_geometricLink G y hylink z hzlink c hc
  calc
    z = x + (z - x) := by abel
    _ = x + c • (y - x) := by rw [heq]

open Classical in
theorem existsUnique_transverse_coface_of_neighbor (K L G : Geometry.SimplicialComplex ℝ E)
    (hcarrier : ∀ u ∈ G.faces, ∃ v ∈ K.faces, ∃ z ∈ L.faces,
      convexHull ℝ (u : Set E) ⊆ convexHull ℝ (v : Set E) ∩ convexHull ℝ (z : Set E))
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ L.faces)
    (hsbound : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card + 1)
    (htmax : ∀ u ∈ L.faces, t ⊆ u → u.card ≤ t.card) {x y : E}
    (hx : x ∈ openSimplex s) (hxt : x ∈ openSimplex t) (hyx : y ≠ x)
    (hyface : {x, y} ∈ G.faces)
    (htrans : Disjoint (vectorSpan ℝ (s : Set E)) (vectorSpan ℝ (t : Set E))) :
    ∃! w, w ∉ s ∧ insert w s ∈ K.faces ∧
      y ∈ convexHull ℝ ((insert w s : Finset E) : Set E) := by
  obtain ⟨u, hu, v, hv, hsub⟩ := hcarrier _ hyface
  have hxuv := hsub (subset_convexHull ℝ _ (show x ∈ (({x, y} : Finset E) : Set E) by simp))
  have hyuv := hsub (subset_convexHull ℝ _ (show y ∈ (({x, y} : Finset E) : Set E) by simp))
  have htv := face_subset_of_mem_openSimplex_of_mem_convexHull L ht hv hxt hxuv.2
  have hvt : v = t := (Finset.eq_of_subset_of_card_le htv (htmax v hv htv)).symm
  have hyt : y ∈ convexHull ℝ (t : Set E) := hvt ▸ hyuv.2
  have hyV : y - x ∈ vectorSpan ℝ (t : Set E) := by
    simpa only [direction_affineSpan, vsub_eq_sub] using AffineSubspace.vsub_mem_direction
      (convexHull_subset_affineSpan _ hyt)
      (convexHull_subset_affineSpan _ (openSimplex_subset_convexHull _ hxt))
  have hynot : y ∉ convexHull ℝ (s : Set E) := by
    intro hys
    have hyS : y - x ∈ vectorSpan ℝ (s : Set E) := by
      simpa only [direction_affineSpan, vsub_eq_sub] using AffineSubspace.vsub_mem_direction
        (convexHull_subset_affineSpan _ hys)
        (convexHull_subset_affineSpan _ (openSimplex_subset_convexHull _ hx))
    exact hyx (sub_eq_zero.mp (Submodule.disjoint_def.mp htrans _ hyS hyV))
  have hsu := face_subset_of_mem_openSimplex_of_mem_convexHull K hs hu hx hxuv.1
  have hlt : s.card < u.card := Finset.card_lt_card
    (Finset.ssubset_iff_subset_ne.mpr ⟨hsu, fun h => hynot (h.symm ▸ hyuv.1)⟩)
  have hbound := hsbound u hu hsu
  have hcard : s.card + 1 = u.card := by omega
  obtain ⟨w, hw, hwu⟩ := Finset.exists_eq_insert_iff.mpr ⟨hsu, hcard⟩
  have hws : insert w s ∈ K.faces := hwu.symm ▸ hu
  have hyw : y ∈ convexHull ℝ ((insert w s : Finset E) : Set E) := hwu.symm ▸ hyuv.1
  refine ⟨w, ⟨hw, hws, hyw⟩, ?_⟩
  rintro z ⟨_, hzs, hyz⟩
  by_contra hzw
  have hinter : (insert z s ∩ insert w s : Finset E) = s := by
    ext q
    simp only [Finset.mem_inter, Finset.mem_insert]
    constructor
    · rintro ⟨rfl | hqs, hqw | hqs⟩
      · exact (hzw hqw).elim
      · exact hqs
      · exact hqs
      · exact hqs
    · exact fun hqs => ⟨Or.inr hqs, Or.inr hqs⟩
  have hys := K.inter_subset_convexHull hzs hws ⟨hyz, hyw⟩
  rw [← Finset.coe_inter, hinter] at hys
  exact hynot hys

open Classical in
theorem neighbors_singleton_or_pair_of_transverse_codimension_one [FiniteDimensional ℝ E]
    (K L G : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite G.faces] {n : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K)
    (hcard : ∀ u ∈ G.faces, u.card ≤ 2) (hspace : G.space = K.space ∩ L.space)
    (hcarrier : ∀ u ∈ G.faces, ∃ v ∈ K.faces, ∃ z ∈ L.faces,
      convexHull ℝ (u : Set E) ⊆ convexHull ℝ (v : Set E) ∩ convexHull ℝ (z : Set E))
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ L.faces) (hscard : s.card = n + 1)
    (htmax : ∀ u ∈ L.faces, t ⊆ u → u.card ≤ t.card) {x : E}
    (hx : x ∈ openSimplex s) (hxt : x ∈ openSimplex t) (hxG : {x} ∈ G.faces)
    (htrans : IsCompl (vectorSpan ℝ (s : Set E)) (vectorSpan ℝ (t : Set E))) :
    (∃ a, {y | y ≠ x ∧ {x, y} ∈ G.faces} = {a}) ∨
      ∃ a b, a ≠ b ∧ {y | y ≠ x ∧ {x, y} ∈ G.faces} = {a, b} := by
  have hsbound : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card + 1 := by
    intro u hu _
    rw [hscard]
    exact hK.card_le K hu
  have hforward := fun w hw hws => existsUnique_neighbor_mem_transverse_coface K L G
    hcard hspace hcarrier ht hsbound htmax hx hxt hxG (w := w) hw hws htrans
  have hreverse := fun y hyx hyface => existsUnique_transverse_coface_of_neighbor K L G
    hcarrier hs ht hsbound htmax hx hxt (y := y) hyx hyface htrans.disjoint
  rcases hK.codimension_one_cofaces K hs hscard with ⟨a, ha⟩ | ⟨a, b, hab, habset⟩
  · have hac : a ∉ s ∧ insert a s ∈ K.faces := by
      change a ∈ {w | w ∉ s ∧ insert w s ∈ K.faces}
      rw [ha]
      exact Set.mem_singleton a
    obtain ⟨y, hy, huniq⟩ := hforward a hac.1 hac.2
    left
    refine ⟨y, ?_⟩
    ext z
    change (z ≠ x ∧ {x, z} ∈ G.faces) ↔ z = y
    constructor
    · rintro ⟨hzx, hzface⟩
      obtain ⟨w, hw, _⟩ := hreverse z hzx hzface
      have hwa : w = a := by
        have hwm : w ∈ {v | v ∉ s ∧ insert v s ∈ K.faces} := ⟨hw.1, hw.2.1⟩
        rw [ha] at hwm
        exact hwm
      subst w
      exact huniq z ⟨hzx, hzface, hw.2.2⟩
    · rintro rfl
      exact ⟨hy.1, hy.2.1⟩
  · have hac : a ∉ s ∧ insert a s ∈ K.faces := by
      change a ∈ {w | w ∉ s ∧ insert w s ∈ K.faces}
      rw [habset]
      exact Set.mem_insert a _
    have hbc : b ∉ s ∧ insert b s ∈ K.faces := by
      change b ∈ {w | w ∉ s ∧ insert w s ∈ K.faces}
      rw [habset]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true]
    obtain ⟨y, hy, hyuniq⟩ := hforward a hac.1 hac.2
    obtain ⟨z, hz, hzuniq⟩ := hforward b hbc.1 hbc.2
    have hyz : y ≠ z := by
      intro heq
      obtain ⟨w, _, hwuniq⟩ := hreverse y hy.1 hy.2.1
      have hya := hwuniq a ⟨hac.1, hac.2, hy.2.2⟩
      have hyb := hwuniq b ⟨hbc.1, hbc.2, heq.symm ▸ hz.2.2⟩
      exact hab (hya.trans hyb.symm)
    right
    refine ⟨y, z, hyz, ?_⟩
    ext q
    change (q ≠ x ∧ {x, q} ∈ G.faces) ↔ q = y ∨ q = z
    constructor
    · rintro ⟨hqx, hqface⟩
      obtain ⟨w, hw, _⟩ := hreverse q hqx hqface
      have hwm : w ∈ {v | v ∉ s ∧ insert v s ∈ K.faces} := ⟨hw.1, hw.2.1⟩
      rw [habset] at hwm
      rcases hwm with rfl | hwb
      · exact Or.inl (hyuniq q ⟨hqx, hqface, hw.2.2⟩)
      · have hwb' : w = b := hwb
        subst w
        exact Or.inr (hzuniq q ⟨hqx, hqface, hw.2.2⟩)
    · rintro (rfl | rfl)
      · exact ⟨hy.1, hy.2.1⟩
      · exact ⟨hz.1, hz.2.1⟩

end DifferentialGeometry.Topology.PiecewiseLinear
