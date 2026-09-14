import DifferentialGeometry.Topology.PiecewiseLinear.PLHomeomorph
import DifferentialGeometry.Topology.PiecewiseLinear.Triangulation
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldInvariance
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
theorem exists_triangulation_inter_add_const [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces] (a : E) :
    ∃ G : Geometry.SimplicialComplex ℝ E, G.faces.Finite ∧
      G.space = (fun x => x + a) '' K.space ∩ L.space ∧
      ∀ u ∈ G.faces, ∃ s ∈ K.faces, ∃ t ∈ L.faces,
        convexHull ℝ (u : Set E) ⊆
          (fun x => x + a) '' convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) := by
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
  rw [hcover p] at hp
  obtain ⟨v, ⟨hv, hvC⟩, hcv⟩ := mem_iUnion₂.mp hp
  have huv : u ⊆ v := face_subset_of_mem_openSimplex_of_mem_convexHull G hu hv huc hcv
  have huC : convexHull ℝ (u : Set E) ⊆ C p :=
    (convexHull_mono (Finset.coe_subset.mpr huv)).trans hvC
  exact ⟨p.1.val, p.1.property, p.2.val, p.2.property, huC⟩

open Classical in
theorem exists_triangulation_inter [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces] :
    ∃ G : Geometry.SimplicialComplex ℝ E, G.faces.Finite ∧ G.space = K.space ∩ L.space ∧
      ∀ u ∈ G.faces, ∃ s ∈ K.faces, ∃ t ∈ L.faces,
        convexHull ℝ (u : Set E) ⊆ convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) := by
  simpa only [add_zero, Set.image_id'] using exists_triangulation_inter_add_const K L (0 : E)

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
  obtain ⟨G, hfin, hspace, hcarrier⟩ := exists_triangulation_inter_add_const K L a
  refine ⟨G, hfin, hspace, fun u hu => ?_⟩
  obtain ⟨s, hs, t, ht, hsub⟩ := hcarrier u hu
  obtain ⟨x, hx⟩ := G.nonempty_of_mem_faces hu
  have hinter := hsub (subset_convexHull ℝ _ hx)
  exact ⟨s, hs, t, ht, hsub, card_add_finrank_le_of_subset_transverse_faces K L hs ht
    (G.indep hu) (G.nonempty_of_mem_faces hu) a ((subset_convexHull ℝ _).trans hsub)
    (htrans s hs t ht ⟨x, hinter⟩)⟩

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
    ∃ d ∈ V, d ≠ 0 ∧ w - x - d ∈ vectorSpan ℝ (s : Set E) ∧
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
  have hproj : w - x - d ∈ vectorSpan ℝ (s : Set E) := by
    rw [← hud, add_sub_cancel_right]
    exact hu
  exact ⟨d, hd, hdne, hproj, hray⟩

open Classical in
theorem exists_ray_into_transverse_face {s t : Finset E} {x w a : E}
    (hx : x ∈ openSimplex s) (hy : x + a ∈ openSimplex t)
    (hw : w ∉ affineSpan ℝ (s : Set E))
    (htrans : vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) = ⊤) :
    ∃ d, d ≠ 0 ∧ ∀ᶠ r : ℝ in 𝓝 0, 0 < r →
      x + r • d ∈ openSimplex (insert w s) ∧ x + a + r • d ∈ openSimplex t := by
  obtain ⟨d, hd, hdne, _, hs⟩ :=
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
theorem neighbors_eq_pair_of_transverse_cofaces [FiniteDimensional ℝ E]
    (K L G : Geometry.SimplicialComplex ℝ E) [Finite G.faces]
    (hcard : ∀ u ∈ G.faces, u.card ≤ 2) (hspace : G.space = K.space ∩ L.space)
    (hcarrier : ∀ u ∈ G.faces, ∃ v ∈ K.faces, ∃ z ∈ L.faces,
      convexHull ℝ (u : Set E) ⊆ convexHull ℝ (v : Set E) ∩ convexHull ℝ (z : Set E))
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ L.faces)
    (hsbound : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card + 1)
    (htmax : ∀ u ∈ L.faces, t ⊆ u → u.card ≤ t.card) {x : E}
    (hx : x ∈ openSimplex s) (hxt : x ∈ openSimplex t) (hxG : {x} ∈ G.faces)
    (htrans : IsCompl (vectorSpan ℝ (s : Set E)) (vectorSpan ℝ (t : Set E)))
    {a b : E} (hab : a ≠ b) (habset : {w | w ∉ s ∧ insert w s ∈ K.faces} = {a, b}) :
    ∃ y z, y ≠ z ∧ {q | q ≠ x ∧ {x, q} ∈ G.faces} = {y, z} := by
  have hforward := fun w hw hws => existsUnique_neighbor_mem_transverse_coface K L G
    hcard hspace hcarrier ht hsbound htmax hx hxt hxG (w := w) hw hws htrans
  have hreverse := fun y hyx hyface => existsUnique_transverse_coface_of_neighbor K L G
    hcarrier hs ht hsbound htmax hx hxt (y := y) hyx hyface htrans.disjoint
  have hac : a ∉ s ∧ insert a s ∈ K.faces := by
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
  · exact Or.inr (neighbors_eq_pair_of_transverse_cofaces K L G hcard hspace hcarrier
      hs ht hsbound htmax hx hxt hxG htrans hab habset)

open Classical in
theorem neighbors_eq_pair_of_finrank_inter_eq_one (K L G : Geometry.SimplicialComplex ℝ E)
    [Finite G.faces] (hcard : ∀ u ∈ G.faces, u.card ≤ 2)
    (hspace : G.space = K.space ∩ L.space)
    (hcarrier : ∀ u ∈ G.faces, ∃ v ∈ K.faces, ∃ z ∈ L.faces,
      convexHull ℝ (u : Set E) ⊆ convexHull ℝ (v : Set E) ∩ convexHull ℝ (z : Set E))
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ L.faces)
    (hsmax : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card)
    (htmax : ∀ u ∈ L.faces, t ⊆ u → u.card ≤ t.card) {x : E}
    (hx : x ∈ openSimplex s) (hxt : x ∈ openSimplex t) (hxG : {x} ∈ G.faces)
    (hdim : Module.finrank ℝ
      (vectorSpan ℝ (s : Set E) ⊓ vectorSpan ℝ (t : Set E) : Submodule ℝ E) = 1) :
    ∃ a b, a ≠ b ∧ {y | y ≠ x ∧ {x, y} ∈ G.faces} = {a, b} := by
  let V : Submodule ℝ E := vectorSpan ℝ (s : Set E) ⊓ vectorSpan ℝ (t : Set E)
  obtain ⟨B⟩ := (finrank_eq_one_iff (K := ℝ) (V := V) (Fin 1)).mp hdim
  let d : E := B 0
  have hdV : d ∈ V := (B 0).property
  have hd : d ≠ 0 := fun h => B.ne_zero 0 (Subtype.ext h)
  have hmultiple : ∀ q ∈ V, ∃ c : ℝ, c • d = q := by
    intro q hq
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' (B 0) (B.ne_zero 0)).mp hdim ⟨q, hq⟩
    exact ⟨c, congrArg Subtype.val hc⟩
  have hray : ∀ q ∈ V, ∀ᶠ r : ℝ in 𝓝 0, 0 < r → x + r • q ∈ G.space := by
    intro q hq
    have hrs := eventually_mem_openSimplex_of_mem_vectorSpan hx hq.1
    have hrt := eventually_mem_openSimplex_of_mem_vectorSpan hxt hq.2
    filter_upwards [hrs, hrt] with r hrs hrt
    intro _
    rw [hspace]
    exact ⟨K.convexHull_subset_space hs (openSimplex_subset_convexHull _ hrs),
      L.convexHull_subset_space ht (openSimplex_subset_convexHull _ hrt)⟩
  obtain ⟨a, ha, hyx, hyface⟩ := exists_neighbor_on_ray_of_eventually G hcard hxG hd (hray d hdV)
  obtain ⟨b, hb, hzx, hzface⟩ := exists_neighbor_on_ray_of_eventually G hcard hxG
    (neg_ne_zero.mpr hd) (hray (-d) (V.neg_mem hdV))
  let y := x + a • d
  let z := x + b • (-d)
  have hyz : y ≠ z := by
    intro heq
    have hsmul : a • d = b • (-d) := add_left_cancel heq
    rw [smul_neg] at hsmul
    have hzero : (a + b) • d = 0 := by rw [add_smul, hsmul, neg_add_cancel]
    have hab := (smul_eq_zero.mp hzero).resolve_right hd
    linarith
  have hdir : ∀ q, {x, q} ∈ G.faces → q - x ∈ V := by
    intro q hq
    obtain ⟨u, hu, v, hv, hsub⟩ := hcarrier _ hq
    have hxuv := hsub (subset_convexHull ℝ _ (show x ∈ (({x, q} : Finset E) : Set E) by simp))
    have hquv := hsub (subset_convexHull ℝ _ (show q ∈ (({x, q} : Finset E) : Set E) by simp))
    have hsu := face_subset_of_mem_openSimplex_of_mem_convexHull K hs hu hx hxuv.1
    have htv := face_subset_of_mem_openSimplex_of_mem_convexHull L ht hv hxt hxuv.2
    have hus : u = s := (Finset.eq_of_subset_of_card_le hsu (hsmax u hu hsu)).symm
    have hvt : v = t := (Finset.eq_of_subset_of_card_le htv (htmax v hv htv)).symm
    rw [hus, hvt] at hquv
    constructor
    · change q - x ∈ vectorSpan ℝ (s : Set E)
      simpa only [direction_affineSpan, vsub_eq_sub] using AffineSubspace.vsub_mem_direction
        (convexHull_subset_affineSpan _ hquv.1)
        (convexHull_subset_affineSpan _ (openSimplex_subset_convexHull _ hx))
    · change q - x ∈ vectorSpan ℝ (t : Set E)
      simpa only [direction_affineSpan, vsub_eq_sub] using AffineSubspace.vsub_mem_direction
        (convexHull_subset_affineSpan _ hquv.2)
        (convexHull_subset_affineSpan _ (openSimplex_subset_convexHull _ hxt))
  have hlink : ∀ q, q ≠ x → {x, q} ∈ G.faces →
      q ∈ (SimplicialComplex.geometricLink G {x}).space := by
    intro q hqx hqface
    rw [geometricLink_space_eq_neighbors_of_card_le G hcard x]
    exact ⟨hqx, hqface⟩
  refine ⟨y, z, hyz, ?_⟩
  ext q
  change (q ≠ x ∧ {x, q} ∈ G.faces) ↔ q = y ∨ q = z
  constructor
  · rintro ⟨hqx, hqface⟩
    obtain ⟨c, hc⟩ := hmultiple (q - x) (hdir q hqface)
    have hcne : c ≠ 0 := by
      intro hc0
      rw [hc0, zero_smul] at hc
      exact hqx (sub_eq_zero.mp hc.symm)
    rcases lt_or_gt_of_ne hcne with hcneg | hcpos
    · right
      apply isRadiallyInjective_geometricLink G z (hlink z hzx hzface) q (hlink q hqx hqface)
        (-c / b) (div_pos (neg_pos.mpr hcneg) hb)
      change q = x + (-c / b) • (x + b • (-d) - x)
      rw [add_sub_cancel_left, smul_smul, div_mul_cancel₀ _ hb.ne', neg_smul_neg, hc, add_sub_cancel]
    · left
      apply isRadiallyInjective_geometricLink G y (hlink y hyx hyface) q (hlink q hqx hqface)
        (c / a) (div_pos hcpos ha)
      change q = x + (c / a) • (x + a • d - x)
      rw [add_sub_cancel_left, smul_smul, div_mul_cancel₀ _ ha.ne', hc, add_sub_cancel]
  · rintro (rfl | rfl)
    · exact ⟨hyx, hyface⟩
    · exact ⟨hzx, hzface⟩

open Classical in
theorem isCombinatorialManifoldWithBoundary_inter_of_transverse_faces [FiniteDimensional ℝ E]
    (K L G : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces] [Finite G.faces]
    {m n : ℕ} (hK : IsCombinatorialManifoldWithBoundary (m + 1) K)
    (hL : IsCombinatorialManifoldWithBoundary (n + 1) L)
    (hdimE : Module.finrank ℝ E = m + n + 1) (hspace : G.space = K.space ∩ L.space)
    (hcarrier : ∀ u ∈ G.faces, ∃ v ∈ K.faces, ∃ z ∈ L.faces,
      convexHull ℝ (u : Set E) ⊆ convexHull ℝ (v : Set E) ∩ convexHull ℝ (z : Set E))
    (htrans : ∀ s ∈ K.faces, ∀ t ∈ L.faces,
      (convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)).Nonempty →
        vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) = ⊤) :
    IsCombinatorialManifoldWithBoundary 1 G := by
  have hcard : ∀ u ∈ G.faces, u.card ≤ 2 := by
    intro u hu
    obtain ⟨s, hs, t, ht, hsub⟩ := hcarrier u hu
    have hune := G.nonempty_of_mem_faces hu
    obtain ⟨p, hp⟩ := hune
    have hpst := hsub (subset_convexHull ℝ _ hp)
    have hst := htrans s hs t ht ⟨p, hpst⟩
    have hsub' : (u : Set E) ⊆ (fun x : E => x + 0) '' convexHull ℝ (s : Set E) ∩
        convexHull ℝ (t : Set E) := by
      simpa only [add_zero, Set.image_id'] using (subset_convexHull ℝ (u : Set E)).trans hsub
    have hbound := card_add_finrank_le_of_subset_transverse_faces K L hs ht (G.indep hu)
      (G.nonempty_of_mem_faces hu) 0 hsub' hst
    have hsbound := hK.card_le K hs
    have htbound := hL.card_le L ht
    omega
  apply (isCombinatorialManifoldWithBoundary_one_iff G).mpr
  refine ⟨hcard, fun x hxG => ?_⟩
  have hxspace : x ∈ G.space := G.subset_space hxG (Finset.mem_singleton_self _)
  rw [hspace] at hxspace
  obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex K hxspace.1
  obtain ⟨t, ht, hxt⟩ := exists_face_mem_openSimplex L hxspace.2
  have hst := htrans s hs t ht ⟨x, openSimplex_subset_convexHull _ hxs,
    openSimplex_subset_convexHull _ hxt⟩
  have hfaceRank : ∀ (P : Geometry.SimplicialComplex ℝ E) (u : Finset E), u ∈ P.faces →
      Module.finrank ℝ (vectorSpan ℝ (u : Set E)) + 1 = u.card := by
    intro P u hu
    obtain ⟨v, hv⟩ := P.nonempty_of_mem_faces hu
    have : Nonempty u := ⟨⟨v, hv⟩⟩
    have hrange : Set.range ((↑) : u → E) = (u : Set E) := by ext q; simp
    have h := (P.indep hu).finrank_vectorSpan_add_one
    change Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : u → E))) + 1 = Fintype.card u at h
    rw [hrange] at h
    simpa only [Fintype.card_coe] using h
  have hsRank := hfaceRank K s hs
  have htRank := hfaceRank L t ht
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (vectorSpan ℝ (s : Set E)) (vectorSpan ℝ (t : Set E))
  rw [hst] at hdim
  have hdim' : Module.finrank ℝ E +
      Module.finrank ℝ (vectorSpan ℝ (s : Set E) ⊓ vectorSpan ℝ (t : Set E) : Submodule ℝ E) =
        Module.finrank ℝ (vectorSpan ℝ (s : Set E)) +
          Module.finrank ℝ (vectorSpan ℝ (t : Set E)) := by simpa using hdim
  have hsbound := hK.card_le K hs
  have htbound := hL.card_le L ht
  have hcases : (s.card = m + 1 ∧ t.card = n + 2) ∨
      (s.card = m + 2 ∧ t.card = n + 1) ∨ (s.card = m + 2 ∧ t.card = n + 2) := by omega
  rcases hcases with ⟨hsc, htc⟩ | ⟨hsc, htc⟩ | ⟨hsc, htc⟩
  · have hinf : Module.finrank ℝ
        (vectorSpan ℝ (s : Set E) ⊓ vectorSpan ℝ (t : Set E) : Submodule ℝ E) = 0 := by omega
    have hcompl : IsCompl (vectorSpan ℝ (s : Set E)) (vectorSpan ℝ (t : Set E)) :=
      IsCompl.of_eq (Submodule.finrank_eq_zero.mp hinf) hst
    have htmax : ∀ u ∈ L.faces, t ⊆ u → u.card ≤ t.card := by
      intro u hu _
      rw [htc]
      exact hL.card_le L hu
    exact neighbors_singleton_or_pair_of_transverse_codimension_one K L G hK hcard hspace
      hcarrier hs ht hsc htmax hxs hxt hxG hcompl
  · have hinf : Module.finrank ℝ
        (vectorSpan ℝ (s : Set E) ⊓ vectorSpan ℝ (t : Set E) : Submodule ℝ E) = 0 := by omega
    have hcompl : IsCompl (vectorSpan ℝ (s : Set E)) (vectorSpan ℝ (t : Set E)) :=
      IsCompl.of_eq (Submodule.finrank_eq_zero.mp hinf) hst
    have hsmax : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card := by
      intro u hu _
      rw [hsc]
      exact hK.card_le K hu
    have hspace' : G.space = L.space ∩ K.space := hspace.trans (Set.inter_comm _ _)
    have hcarrier' : ∀ u ∈ G.faces, ∃ v ∈ L.faces, ∃ z ∈ K.faces,
        convexHull ℝ (u : Set E) ⊆ convexHull ℝ (v : Set E) ∩ convexHull ℝ (z : Set E) := by
      intro u hu
      obtain ⟨v, hv, z, hz, hsub⟩ := hcarrier u hu
      exact ⟨z, hz, v, hv, fun q hq => (hsub hq).symm⟩
    exact neighbors_singleton_or_pair_of_transverse_codimension_one L K G hL hcard hspace'
      hcarrier' ht hs htc hsmax hxt hxs hxG hcompl.symm
  · have hinf : Module.finrank ℝ
        (vectorSpan ℝ (s : Set E) ⊓ vectorSpan ℝ (t : Set E) : Submodule ℝ E) = 1 := by omega
    have hsmax : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card := by
      intro u hu _
      rw [hsc]
      exact hK.card_le K hu
    have htmax : ∀ u ∈ L.faces, t ⊆ u → u.card ≤ t.card := by
      intro u hu _
      rw [htc]
      exact hL.card_le L hu
    exact Or.inr (neighbors_eq_pair_of_finrank_inter_eq_one K L G hcard hspace hcarrier
      hs ht hsmax htmax hxs hxt hxG hinf)

open Classical in
theorem exists_isCombinatorialManifoldWithBoundary_inter_of_transverse_faces [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces] {m n : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary (m + 1) K)
    (hL : IsCombinatorialManifoldWithBoundary (n + 1) L)
    (hdimE : Module.finrank ℝ E = m + n + 1)
    (htrans : ∀ s ∈ K.faces, ∀ t ∈ L.faces,
      (convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)).Nonempty →
        vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) = ⊤) :
    ∃ G : Geometry.SimplicialComplex ℝ E, G.faces.Finite ∧ G.space = K.space ∩ L.space ∧
      IsCombinatorialManifoldWithBoundary 1 G := by
  have htrans' : ∀ s ∈ K.faces, ∀ t ∈ L.faces,
      ((fun x : E => x + 0) '' convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)).Nonempty →
        vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) = ⊤ := by
    simpa only [add_zero, Set.image_id'] using htrans
  obtain ⟨G, hGfin, hGspace, hGfaces⟩ := exists_triangulation_inter_of_transverse_faces K L 0 htrans'
  have : Finite G.faces := hGfin.to_subtype
  have hspace : G.space = K.space ∩ L.space := by
    simpa only [add_zero, Set.image_id'] using hGspace
  refine ⟨G, hGfin, hspace, ?_⟩
  apply isCombinatorialManifoldWithBoundary_inter_of_transverse_faces K L G hK hL hdimE hspace
    (htrans := htrans)
  intro u hu
  obtain ⟨s, hs, t, ht, hsub, _⟩ := hGfaces u hu
  exact ⟨s, hs, t, ht, by simpa only [add_zero, Set.image_id'] using hsub⟩

theorem simplicialMap_eqOn_affine {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Geometry.SimplicialComplex ℝ E) (A : E →ᵃ[ℝ] F) :
    EqOn (simplicialMap K A) A K.space := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
  rw [simplicialMap_eq_of_mem K A hs hxs,
    ← affineMap_apply_sum_smul A (sum_weights hxs), sum_weights_smul hxs]

noncomputable def affineImage {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Geometry.SimplicialComplex ℝ E) (A : E ≃ᵃ[ℝ] F) : Geometry.SimplicialComplex ℝ F := by
  classical
  refine simplicialImage K A.toAffineMap (fun s hs =>
    affineIndependent_image_of_injOn_convexHull A.toAffineMap (K.indep hs) A.injective.injOn) ?_
  intro x hx y hy hxy
  apply A.injective
  exact ((simplicialMap_eqOn_affine K A.toAffineMap) hx).symm.trans
    (hxy.trans ((simplicialMap_eqOn_affine K A.toAffineMap) hy))

open Classical in
theorem mem_affineImage_faces_iff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Geometry.SimplicialComplex ℝ E) (A : E ≃ᵃ[ℝ] F) {t : Finset F} :
    t ∈ (affineImage K A).faces ↔ ∃ s ∈ K.faces, t = s.image A := Iff.rfl

theorem affineImage_faces_finite {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (A : E ≃ᵃ[ℝ] F) :
    (affineImage K A).faces.Finite := by
  classical
  exact simplicialImage_faces_finite _ _ _ _

theorem affineImage_space {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Geometry.SimplicialComplex ℝ E) (A : E ≃ᵃ[ℝ] F) :
    (affineImage K A).space = A '' K.space := by
  classical
  exact (simplicialImage_space K A.toAffineMap _ _).trans
    (image_congr (simplicialMap_eqOn_affine K A.toAffineMap))

theorem isPLHomeomorphOn_affineImage {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] (K : Geometry.SimplicialComplex ℝ E)
    [Finite K.faces] (A : E ≃ᵃ[ℝ] F) : IsPLHomeomorphOn A K.space (affineImage K A).space := by
  classical
  unfold affineImage
  exact (isPLHomeomorphOn_simplicialImage _ _ _ _).congr
    (simplicialMap_eqOn_affine K A.toAffineMap).symm

open Classical in
theorem exists_small_homeomorph_transverse_affineImage [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    {U : Set E} (hU : IsOpen U) (hKU : K.space ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ (a : E) (h : E → E), ‖a‖ < ε ∧ IsPLHomeomorphOn h univ univ ∧
      (∀ x, dist (h x) x < ε) ∧ EqOn h id Uᶜ ∧
      (affineImage K (AffineEquiv.constVAdd ℝ E a)).space = h '' K.space ∧
      ∀ s ∈ (affineImage K (AffineEquiv.constVAdd ℝ E a)).faces, ∀ t ∈ L.faces,
        (convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)).Nonempty →
          vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) = ⊤ := by
  obtain ⟨a, h, ha, hh, hclose, hfix, heq, htrans⟩ :=
    exists_small_homeomorph_transverse_faces K L hU hKU hε
  let A := AffineEquiv.constVAdd ℝ E a
  have hA : (A : E → E) = fun x => x + a := by
    funext x
    change a + x = x + a
    exact add_comm _ _
  have hKA : (affineImage K A).space = h '' K.space := by
    rw [affineImage_space, hA]
    exact image_congr heq.symm
  refine ⟨a, h, ha, hh, hclose, hfix, hKA, ?_⟩
  have hspan : ∀ s : Finset E, vectorSpan ℝ ((s.image A : Finset E) : Set E) =
      vectorSpan ℝ (s : Set E) := by
    intro s
    rw [Finset.coe_image]
    change vectorSpan ℝ (A.toAffineMap '' (s : Set E)) = vectorSpan ℝ (s : Set E)
    rw [← A.toAffineMap.map_vectorSpan]
    change Submodule.map (LinearMap.id : E →ₗ[ℝ] E) (vectorSpan ℝ (s : Set E)) =
      vectorSpan ℝ (s : Set E)
    exact Submodule.map_id _
  intro s hs t ht hinter
  obtain ⟨u, hu, rfl⟩ := (mem_affineImage_faces_iff K A).mp hs
  rw [hspan]
  apply htrans u hu t ht
  have hhull : convexHull ℝ ((u.image A : Finset E) : Set E) =
      h '' convexHull ℝ (u : Set E) := by
    rw [Finset.coe_image]
    change convexHull ℝ (A.toAffineMap '' (u : Set E)) = h '' convexHull ℝ (u : Set E)
    rw [← A.toAffineMap.image_convexHull]
    apply image_congr
    intro x hx
    change A x = h x
    rw [hA]
    exact (heq (K.convexHull_subset_space hu hx)).symm
  rwa [hhull] at hinter

open Classical in
theorem exists_small_homeomorph_inter_isCombinatorialManifoldWithBoundary [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces] {m n : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary (m + 1) K)
    (hL : IsCombinatorialManifoldWithBoundary (n + 1) L)
    (hdimE : Module.finrank ℝ E = m + n + 1) {U : Set E}
    (hU : IsOpen U) (hKU : K.space ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ (h : E → E) (G : Geometry.SimplicialComplex ℝ E),
      IsPLHomeomorphOn h univ univ ∧ (∀ x, dist (h x) x < ε) ∧ EqOn h id Uᶜ ∧
        G.faces.Finite ∧ G.space = h '' K.space ∩ L.space ∧
          IsCombinatorialManifoldWithBoundary 1 G := by
  obtain ⟨a, h, _, hh, hclose, hfix, hKA, htrans⟩ :=
    exists_small_homeomorph_transverse_affineImage K L hU hKU hε
  let A := AffineEquiv.constVAdd ℝ E a
  let K' := affineImage K A
  have : Finite K'.faces := (affineImage_faces_finite K A).to_subtype
  have hK' : IsCombinatorialManifoldWithBoundary (m + 1) K' :=
    hK.of_isPLHomeomorphOn (isPLHomeomorphOn_affineImage K A)
  obtain ⟨G, hGfin, hGspace, hGman⟩ :=
    exists_isCombinatorialManifoldWithBoundary_inter_of_transverse_faces K' L hK' hL hdimE htrans
  rw [hKA] at hGspace
  exact ⟨h, G, hh, hclose, hfix, hGfin, hGspace, hGman⟩

theorem isPLHomeomorphOn_shear [FiniteDimensional ℝ E] (ℓ : E →ₗ[ℝ] ℝ) {v : E}
    (hv : ℓ v = 0) {φ : ℝ → ℝ} (hφ : IsPiecewiseAffineOn φ univ) :
    IsPLHomeomorphOn (fun x => x + φ (ℓ x) • v) univ univ := by
  have hℓ : IsPiecewiseAffineOn ℓ univ :=
    isPiecewiseAffineOn_of_affine ℓ.toAffineMap isOpen_univ
  have hcomp : IsPiecewiseAffineOn (fun x => φ (ℓ x)) univ := by
    change IsPiecewiseAffineOn (φ ∘ ℓ) univ
    simpa only [preimage_univ, inter_self] using hφ.comp hℓ
  have hpl : ∀ w : E, IsPiecewiseAffineOn (fun x => x + φ (ℓ x) • w) univ := by
    intro w
    exact (isPiecewiseAffineOn_id isOpen_univ).add
      (hcomp.affine_comp (LinearMap.toSpanSingleton ℝ E w).toAffineMap)
  let f : E → E := fun x => x + φ (ℓ x) • v
  let g : E → E := fun x => x + φ (ℓ x) • (-v)
  have hleft : Function.LeftInverse g f := by
    intro x
    change x + φ (ℓ x) • v + φ (ℓ (x + φ (ℓ x) • v)) • (-v) = x
    rw [map_add, map_smul, hv, smul_eq_mul, mul_zero, add_zero, smul_neg, add_neg_cancel_right]
  have hright : Function.RightInverse g f := by
    intro x
    change x + φ (ℓ x) • (-v) + φ (ℓ (x + φ (ℓ x) • (-v))) • v = x
    rw [map_add, map_smul, map_neg, hv, neg_zero, smul_eq_mul, mul_zero, add_zero, smul_neg]
    abel
  have hbij : BijOn f univ univ :=
    ⟨mapsTo_univ _ _, fun _ _ _ _ h => hleft.injective h,
      fun y _ => ⟨g y, mem_univ _, hright y⟩⟩
  refine ⟨hbij, hpl v, (hpl (-v)).congr fun y hy => ?_⟩
  exact hleft.injective ((hbij.invOn_invFunOn.2 hy).trans (hright y).symm)

open Classical in
theorem exists_isPLHomeomorphOn_straighten_rays [FiniteDimensional ℝ E]
    (ℓ : E →ₗ[ℝ] ℝ) {u v : E} (hu : 0 < ℓ u) (hv : ℓ v < 0) :
    ∃ h : E → E, IsPLHomeomorphOn h univ univ ∧ EqOn h id (LinearMap.ker ℓ : Set E) ∧
      (∀ r : ℝ, 0 ≤ r → h (r • u) = r • u) ∧
      (∀ r : ℝ, 0 ≤ r → h (r • v) = (r * (ℓ v / ℓ u)) • u) ∧
      (∀ x y, ℓ x = 0 → h (x + y) = x + h y) ∧
      ∀ W : Submodule ℝ E, u ∈ W → v ∈ W → h '' (W : Set E) = (W : Set E) := by
  let w : E := (ℓ u)⁻¹ • u - (ℓ v)⁻¹ • v
  have hw : ℓ w = 0 := by
    dsimp [w]
    rw [map_sub, map_smul, map_smul]
    change (ℓ u)⁻¹ * ℓ u - (ℓ v)⁻¹ * ℓ v = 0
    rw [inv_mul_cancel₀ hu.ne', inv_mul_cancel₀ hv.ne, sub_self]
  have hmin : IsPiecewiseAffineOn (fun r : ℝ => min r 0) univ :=
    (isPiecewiseAffineOn_id isOpen_univ).min
      (isPiecewiseAffineOn_of_affine (AffineMap.const ℝ ℝ 0) isOpen_univ)
  let h : E → E := fun x => x + min (ℓ x) 0 • w
  have hh : IsPLHomeomorphOn h univ univ := isPLHomeomorphOn_shear ℓ hw hmin
  refine ⟨h, hh, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    have hx0 : ℓ x = 0 := hx
    change x + min (ℓ x) 0 • w = x
    rw [hx0, min_self, zero_smul, add_zero]
  · intro r hr
    change r • u + min (ℓ (r • u)) 0 • w = r • u
    rw [map_smul]
    change r • u + min (r * ℓ u) 0 • w = r • u
    rw [min_eq_right (mul_nonneg hr hu.le), zero_smul, add_zero]
  · intro r hr
    change r • v + min (ℓ (r • v)) 0 • w = (r * (ℓ v / ℓ u)) • u
    rw [map_smul]
    change r • v + min (r * ℓ v) 0 • w = (r * (ℓ v / ℓ u)) • u
    rw [min_eq_left (mul_nonpos_of_nonneg_of_nonpos hr hv.le)]
    dsimp [w]
    simp only [smul_sub, smul_smul, mul_assoc, mul_inv_cancel₀ hv.ne, mul_one, div_eq_mul_inv]
    abel
  · intro x y hx
    change x + y + min (ℓ (x + y)) 0 • w = x + (y + min (ℓ y) 0 • w)
    rw [map_add, hx, zero_add, add_assoc]
  · intro W huW hvW
    have hwW : w ∈ W := W.sub_mem (W.smul_mem _ huW) (W.smul_mem _ hvW)
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact W.add_mem hx (W.smul_mem _ hwW)
    · intro y hy
      obtain ⟨x, _, hxy⟩ := hh.bijOn.surjOn (mem_univ y)
      have hxW : x ∈ W := by
        have hy' : x + min (ℓ x) 0 • w ∈ W := by
          change x + min (ℓ x) 0 • w = y at hxy
          rw [hxy]
          exact hy
        exact (W.add_mem_iff_left (W.smul_mem (min (ℓ x) 0) hwW)).mp hy'
      exact ⟨x, hxW, hxy⟩

theorem exists_linearMap_eq_one_neg_of_disjoint {V : Type*} [AddCommGroup V] [Module ℝ V]
    {S T : Submodule ℝ V} (hdis : Disjoint S T) {u v : V} (huT : u ∈ T) (hvT : v ∈ T)
    (hu : u ≠ 0) (hv : v ≠ 0) (hnot : ∀ c : ℝ, 0 < c → v ≠ c • u) :
    ∃ ℓ : V →ₗ[ℝ] ℝ, S ≤ LinearMap.ker ℓ ∧ ℓ u = 1 ∧ ℓ v < 0 := by
  classical
  have huS : u ∉ S := fun hus => hu (Submodule.disjoint_def.mp hdis _ hus huT)
  obtain ⟨f, hf, hfu⟩ := LinearMap.exists_extend_of_notMem (0 : S →ₗ[ℝ] ℝ) huS 1
  have hfS : S ≤ LinearMap.ker f := by
    intro x hx
    have h := congrArg (fun L : S →ₗ[ℝ] ℝ => L ⟨x, hx⟩) hf
    change f x = 0 at h
    exact h
  let P : Submodule ℝ V := S ⊔ Submodule.span ℝ {u}
  by_cases hvP : v ∈ P
  · obtain ⟨s, hs, w, hw, hswv⟩ := Submodule.mem_sup.mp hvP
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    have hsT : s ∈ T := by
      have heq : s = v - c • u := by rw [← hswv]; abel
      rw [heq]
      exact T.sub_mem hvT (T.smul_mem _ huT)
    have hs0 := Submodule.disjoint_def.mp hdis _ hs hsT
    rw [hs0, zero_add] at hswv
    have hcne : c ≠ 0 := by
      intro hc0
      rw [hc0, zero_smul] at hswv
      exact hv hswv.symm
    have hcle : c ≤ 0 := le_of_not_gt fun hc => hnot c hc hswv.symm
    refine ⟨f, hfS, hfu, ?_⟩
    rw [← hswv, map_smul, hfu]
    change c * 1 < 0
    simpa only [mul_one] using lt_of_le_of_ne hcle hcne
  · obtain ⟨g, hg, hgv⟩ := LinearMap.exists_extend_of_notMem (f.domRestrict P) hvP (-1)
    have hgP : ∀ x ∈ P, g x = f x := by
      intro x hx
      exact congrArg (fun L : P →ₗ[ℝ] ℝ => L ⟨x, hx⟩) hg
    refine ⟨g, ?_, ?_, by rw [hgv]; norm_num⟩
    · intro x hx
      have hfx : f x = 0 := hfS hx
      change g x = 0
      rw [hgP x (Submodule.mem_sup_left hx), hfx]
    · rw [hgP u (Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton u))), hfu]

open Classical in
theorem exists_isPLHomeomorphOn_straighten_two_halfSpaces [FiniteDimensional ℝ E]
    {S T : Submodule ℝ E} (hdis : Disjoint S T) {u v : E} (huT : u ∈ T) (hvT : v ∈ T)
    (hu : u ≠ 0) (hv : v ≠ 0) (hnot : ∀ c : ℝ, 0 < c → v ≠ c • u) :
    ∃ h : E → E, IsPLHomeomorphOn h univ univ ∧ EqOn h id (S : Set E) ∧
      h '' (T : Set E) = (T : Set E) ∧
      h '' ({x | ∃ s ∈ S, ∃ r : ℝ, 0 ≤ r ∧ x = s + r • u} ∪
        {x | ∃ s ∈ S, ∃ r : ℝ, 0 ≤ r ∧ x = s + r • v}) =
          (S ⊔ Submodule.span ℝ {u} : Submodule ℝ E) := by
  obtain ⟨ℓ, hℓS, hℓu, hℓv⟩ := exists_linearMap_eq_one_neg_of_disjoint hdis huT hvT hu hv hnot
  have hℓupos : 0 < ℓ u := by rw [hℓu]; norm_num
  obtain ⟨h, hh, hfix, hru, hrv, hadd, hsubspace⟩ :=
    exists_isPLHomeomorphOn_straighten_rays ℓ hℓupos hℓv
  have huform : ∀ s ∈ S, ∀ r : ℝ, 0 ≤ r → h (s + r • u) = s + r • u := by
    intro s hs r hr
    rw [hadd s (r • u) (hℓS hs), hru r hr]
  have hvform : ∀ s ∈ S, ∀ r : ℝ, 0 ≤ r → h (s + r • v) = s + (r * ℓ v) • u := by
    intro s hs r hr
    rw [hadd s (r • v) (hℓS hs), hrv r hr, hℓu, div_one]
  refine ⟨h, hh, hfix.mono hℓS, hsubspace T huT hvT, ?_⟩
  have huP : u ∈ S ⊔ Submodule.span ℝ {u} :=
    Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton u))
  apply Subset.antisymm
  · rintro _ ⟨x, hx, rfl⟩
    rcases hx with ⟨s, hs, r, hr, rfl⟩ | ⟨s, hs, r, hr, rfl⟩
    · rw [huform s hs r hr]
      exact Submodule.add_mem _ (Submodule.mem_sup_left hs) (Submodule.smul_mem _ _ huP)
    · rw [hvform s hs r hr]
      exact Submodule.add_mem _ (Submodule.mem_sup_left hs) (Submodule.smul_mem _ _ huP)
  · intro x hx
    obtain ⟨s, hs, w, hw, hsw⟩ := Submodule.mem_sup.mp hx
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hw
    by_cases hr : 0 ≤ r
    · exact ⟨s + r • u, Or.inl ⟨s, hs, r, hr, rfl⟩, (huform s hs r hr).trans hsw⟩
    · have hrc : 0 ≤ r / ℓ v := div_nonneg_of_nonpos (le_of_not_ge hr) hℓv.le
      refine ⟨s + (r / ℓ v) • v, Or.inr ⟨s, hs, r / ℓ v, hrc, rfl⟩, ?_⟩
      rw [hvform s hs _ hrc, div_mul_cancel₀ _ hℓv.ne]
      exact hsw

theorem eventually_mem_halfSpaces_iff_exists_pos_smul_mem [FiniteDimensional ℝ E]
    {ι : Type*} [Finite ι] (ℓ : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) {x : E}
    (hx : ∀ i, ℓ i x ≤ b i) :
    ∀ᶠ y in 𝓝 x, (∀ i, ℓ i y ≤ b i) ↔
      ∃ r : ℝ, 0 < r ∧ ∀ i, ℓ i (x + r • (y - x)) ≤ b i := by
  have hopen : IsOpen (⋂ i : {j // ℓ j x < b j}, {y | ℓ i.val y < b i.val}) :=
    isOpen_iInter_of_finite fun i => isOpen_lt (ℓ i.val).continuous_of_finiteDimensional continuous_const
  have hxin : x ∈ ⋂ i : {j // ℓ j x < b j}, {y | ℓ i.val y < b i.val} :=
    mem_iInter.mpr fun i => i.property
  apply Filter.mem_of_superset (hopen.mem_nhds hxin)
  intro y hy
  constructor
  · intro hyall
    exact ⟨1, one_pos, by simpa only [one_smul, add_sub_cancel] using hyall⟩
  · rintro ⟨r, hr, hmem⟩ i
    rcases lt_or_eq_of_le (hx i) with hi | hi
    · exact (mem_iInter.mp hy ⟨i, hi⟩).le
    · have hbound := hmem i
      rw [map_add, map_smul, map_sub, hi] at hbound
      change b i + r * (ℓ i y - b i) ≤ b i at hbound
      nlinarith

theorem IsHPolytope.eventually_mem_iff_exists_pos_smul_mem [FiniteDimensional ℝ E]
    {P : Set E} (hP : IsHPolytope P) {x : E} (hx : x ∈ P) :
    ∀ᶠ y in 𝓝 x, y ∈ P ↔ ∃ r : ℝ, 0 < r ∧ x + r • (y - x) ∈ P := by
  obtain ⟨_, ι, hι, ℓ, b, rfl⟩ := hP
  have := hι
  exact eventually_mem_halfSpaces_iff_exists_pos_smul_mem ℓ b hx

theorem exists_pos_smul_mem_convexHull_iff_mem_vectorSpan {s : Finset E} {x d : E}
    (hx : x ∈ openSimplex s) :
    (∃ r : ℝ, 0 < r ∧ x + r • d ∈ convexHull ℝ (s : Set E)) ↔
      d ∈ vectorSpan ℝ (s : Set E) := by
  constructor
  · rintro ⟨r, hr, hmem⟩
    have hdir : r • d ∈ vectorSpan ℝ (s : Set E) := by
      simpa only [direction_affineSpan, vsub_eq_sub, add_sub_cancel_left] using
        AffineSubspace.vsub_mem_direction (convexHull_subset_affineSpan _ hmem)
          (convexHull_subset_affineSpan _ (openSimplex_subset_convexHull _ hx))
    have h := Submodule.smul_mem _ r⁻¹ hdir
    simpa only [smul_smul, inv_mul_cancel₀ hr.ne', one_smul] using h
  · intro hd
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
      (eventually_mem_openSimplex_of_mem_vectorSpan hx hd)
    have hpos : 0 < ε / 2 := by positivity
    have hmem : ε / 2 ∈ ball (0 : ℝ) ε := by
      simp only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hpos]
      linarith
    exact ⟨ε / 2, hpos, openSimplex_subset_convexHull _ (hball hmem)⟩

theorem eventually_mem_convexHull_iff_sub_mem_vectorSpan [FiniteDimensional ℝ E]
    {s : Finset E} (hs : AffineIndependent ℝ ((↑) : s → E)) {x : E} (hx : x ∈ openSimplex s) :
    ∀ᶠ y in 𝓝 x, y ∈ convexHull ℝ (s : Set E) ↔ y - x ∈ vectorSpan ℝ (s : Set E) := by
  have hlocal := (isHPolytope_convexHull_of_affineIndependent s hs).eventually_mem_iff_exists_pos_smul_mem
    (openSimplex_subset_convexHull _ hx)
  filter_upwards [hlocal] with y hy
  exact hy.trans (exists_pos_smul_mem_convexHull_iff_mem_vectorSpan hx)

open Classical in
theorem exists_pos_smul_mem_convexHull_insert_iff {s : Finset E} {x w d : E}
    (hx : x ∈ openSimplex s) (hw : w ∉ s) :
    (∃ r : ℝ, 0 < r ∧ x + r • d ∈ convexHull ℝ ((insert w s : Finset E) : Set E)) ↔
      ∃ z ∈ vectorSpan ℝ (s : Set E), ∃ t : ℝ, 0 ≤ t ∧ d = z + t • (w - x) := by
  constructor
  · rintro ⟨r, hr, hmem⟩
    rcases exists_combo_of_mem_convexHull_insert hw hmem with hq | ⟨p, hp, c, hc, hc1, hq⟩
    · refine ⟨0, Submodule.zero_mem _, r⁻¹, (inv_pos.mpr hr).le, ?_⟩
      have hrd : r • d = w - x := by rw [← hq, add_sub_cancel_left]
      rw [zero_add, ← hrd, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    · have hpdir : p - x ∈ vectorSpan ℝ (s : Set E) := by
        simpa only [direction_affineSpan, vsub_eq_sub] using AffineSubspace.vsub_mem_direction
          (convexHull_subset_affineSpan _ hp)
          (convexHull_subset_affineSpan _ (openSimplex_subset_convexHull _ hx))
      have hrd : r • d = c • (p - x) + (1 - c) • (w - x) := by
        calc
          r • d = (x + r • d) - x := by abel
          _ = (w + c • (p - w)) - x := by rw [hq]
          _ = c • (p - x) + (1 - c) • (w - x) := by module
      refine ⟨(c / r) • (p - x), Submodule.smul_mem _ _ hpdir,
        (1 - c) / r, div_nonneg (sub_nonneg.mpr hc1) hr.le, ?_⟩
      calc
        d = r⁻¹ • (r • d) := by rw [smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
        _ = (c / r) • (p - x) + ((1 - c) / r) • (w - x) := by
          rw [hrd]
          simp only [smul_add, smul_smul, div_eq_inv_mul]
  · rintro ⟨z, hz, t, ht, hd⟩
    rcases eq_or_lt_of_le ht with ht0 | htpos
    · have hdz : d = z := by rw [← ht0, zero_smul, add_zero] at hd; exact hd
      obtain ⟨r, hr, hmem⟩ := (exists_pos_smul_mem_convexHull_iff_mem_vectorSpan hx).mpr (hdz ▸ hz)
      refine ⟨r, hr, convexHull_mono ?_ hmem⟩
      exact Finset.coe_subset.mpr (Finset.subset_insert _ _)
    · have hray := eventually_mem_openSimplex_insert_of_mem_vectorSpan hx
        (Submodule.smul_mem _ t⁻¹ hz) hw
      obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hray
      have hpos : 0 < ε / 2 := by positivity
      have hmem : ε / 2 ∈ ball (0 : ℝ) ε := by
        simp only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hpos]
        linarith
      have hq := openSimplex_subset_convexHull _ (hball hmem hpos)
      have hd' : d = t • (w - x + t⁻¹ • z) := by
        rw [smul_add, smul_smul, mul_inv_cancel₀ htpos.ne', one_smul, add_comm]
        exact hd
      refine ⟨(ε / 2) / t, div_pos hpos htpos, ?_⟩
      rw [hd', smul_smul, div_mul_cancel₀ _ htpos.ne']
      exact hq

open Classical in
theorem eventually_mem_convexHull_insert_iff [FiniteDimensional ℝ E] {s : Finset E} {w x : E}
    (hs : AffineIndependent ℝ ((↑) : ↥(insert w s : Finset E) → E))
    (hx : x ∈ openSimplex s) (hw : w ∉ s) :
    ∀ᶠ y in 𝓝 x, y ∈ convexHull ℝ ((insert w s : Finset E) : Set E) ↔
      ∃ z ∈ vectorSpan ℝ (s : Set E), ∃ t : ℝ, 0 ≤ t ∧ y - x = z + t • (w - x) := by
  have hxmem : x ∈ convexHull ℝ ((insert w s : Finset E) : Set E) :=
    convexHull_mono (Finset.coe_subset.mpr (Finset.subset_insert _ _))
      (openSimplex_subset_convexHull _ hx)
  have hlocal := (isHPolytope_convexHull_of_affineIndependent (insert w s) hs).eventually_mem_iff_exists_pos_smul_mem hxmem
  filter_upwards [hlocal] with y hy
  exact hy.trans (exists_pos_smul_mem_convexHull_insert_iff hx hw)

theorem eventually_mem_space_iff_mem_coface (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {s : Finset E} (hs : s ∈ K.faces) {x : E} (hx : x ∈ openSimplex s) :
    ∀ᶠ y in 𝓝 x, y ∈ K.space ↔
      ∃ u ∈ K.faces, s ⊆ u ∧ y ∈ convexHull ℝ (u : Set E) := by
  obtain ⟨U, hU, hUsub⟩ := mem_nhdsWithin_iff_exists_mem_nhds_inter.mp (closedStar_mem_nhdsWithin K x)
  filter_upwards [hU] with y hy
  constructor
  · intro hyK
    have hstar := hUsub ⟨hy, hyK⟩
    obtain ⟨u, ⟨hu, hxu⟩, hyu⟩ := mem_iUnion₂.mp hstar
    exact ⟨u, hu, face_subset_of_mem_openSimplex_of_mem_convexHull K hs hu hx hxu, hyu⟩
  · rintro ⟨u, hu, _, hyu⟩
    exact K.convexHull_subset_space hu hyu

theorem eventually_mem_space_iff_sub_mem_vectorSpan [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {s : Finset E} (hs : s ∈ K.faces)
    (hmax : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card) {x : E} (hx : x ∈ openSimplex s) :
    ∀ᶠ y in 𝓝 x, y ∈ K.space ↔ y - x ∈ vectorSpan ℝ (s : Set E) := by
  filter_upwards [eventually_mem_space_iff_mem_coface K hs hx,
    eventually_mem_convexHull_iff_sub_mem_vectorSpan (K.indep hs) hx] with y hcoface hsimplex
  constructor
  · intro hy
    obtain ⟨u, hu, hsu, hyu⟩ := hcoface.mp hy
    have hus : u = s := (Finset.eq_of_subset_of_card_le hsu (hmax u hu hsu)).symm
    exact hsimplex.mp (hus ▸ hyu)
  · intro hy
    exact K.convexHull_subset_space hs (hsimplex.mpr hy)

open Classical in
theorem eventually_mem_space_iff_mem_codimension_one_cone [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {s : Finset E} (hs : s ∈ K.faces)
    (hbound : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card + 1)
    (hcoface : ∃ w, w ∉ s ∧ insert w s ∈ K.faces) {x : E} (hx : x ∈ openSimplex s) :
    ∀ᶠ y in 𝓝 x, y ∈ K.space ↔ ∃ w, w ∉ s ∧ insert w s ∈ K.faces ∧
      ∃ z ∈ vectorSpan ℝ (s : Set E), ∃ r : ℝ, 0 ≤ r ∧ y - x = z + r • (w - x) := by
  let A : Set E := {w | w ∉ s ∧ insert w s ∈ K.faces}
  have hAfin : A.Finite := by
    apply ((Set.toFinite K.faces).biUnion fun u _ => u.finite_toSet).subset
    intro w hw
    exact mem_biUnion hw.2 (Finset.mem_insert_self _ _)
  have : Finite A := hAfin.to_subtype
  have hall : ∀ᶠ y in 𝓝 x, ∀ w : A,
      y ∈ convexHull ℝ ((insert (w : E) s : Finset E) : Set E) ↔
        ∃ z ∈ vectorSpan ℝ (s : Set E), ∃ r : ℝ, 0 ≤ r ∧ y - x = z + r • ((w : E) - x) :=
    Filter.eventually_all.mpr fun w => eventually_mem_convexHull_insert_iff
      (K.indep w.property.2) hx w.property.1
  filter_upwards [eventually_mem_space_iff_mem_coface K hs hx,
    eventually_mem_convexHull_iff_sub_mem_vectorSpan (K.indep hs) hx, hall] with y hlocal hbase hall
  constructor
  · intro hy
    obtain ⟨u, hu, hsu, hyu⟩ := hlocal.mp hy
    by_cases hus : u = s
    · obtain ⟨w, hw, hws⟩ := hcoface
      refine ⟨w, hw, hws, y - x, hbase.mp (hus ▸ hyu), 0, le_rfl, ?_⟩
      rw [zero_smul, add_zero]
    · have hlt : s.card < u.card :=
        Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hsu, Ne.symm hus⟩)
      have hubound := hbound u hu hsu
      have hcard : s.card + 1 = u.card := by omega
      obtain ⟨w, hw, hwu⟩ := Finset.exists_eq_insert_iff.mpr ⟨hsu, hcard⟩
      have hws : insert w s ∈ K.faces := hwu.symm ▸ hu
      exact ⟨w, hw, hws, (hall ⟨w, hw, hws⟩).mp (hwu.symm ▸ hyu)⟩
  · rintro ⟨w, hw, hws, hcone⟩
    exact K.convexHull_subset_space hws ((hall ⟨w, hw, hws⟩).mpr hcone)

theorem not_pos_smul_of_eventually_mem_distinct_openSimplex (K : Geometry.SimplicialComplex ℝ E)
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hst : s ≠ t) {x u v : E}
    (hu : ∀ᶠ r : ℝ in 𝓝 0, 0 < r → x + r • u ∈ openSimplex s)
    (hv : ∀ᶠ r : ℝ in 𝓝 0, 0 < r → x + r • v ∈ openSimplex t) :
    ∀ c : ℝ, 0 < c → v ≠ c • u := by
  intro c hc heq
  have htend : Filter.Tendsto (fun r : ℝ => r / c) (𝓝 0) (𝓝 0) := by
    simpa only [id_eq, zero_div] using (continuous_id.div_const c).tendsto 0
  have hfalse : ∀ᶠ r : ℝ in 𝓝 0, 0 < r → False := by
    filter_upwards [hu, htend.eventually hv] with r hru hrv hr
    have hvt := hrv (div_pos hr hc)
    rw [heq, smul_smul, div_mul_cancel₀ _ hc.ne'] at hvt
    exact hst (face_eq_of_mem_openSimplex K hs ht (hru hr) hvt)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hfalse
  have hpos : 0 < ε / 2 := by positivity
  have hmem : ε / 2 ∈ ball (0 : ℝ) ε := by
    simp only [mem_ball, dist_zero_right, Real.norm_eq_abs, abs_of_pos hpos]
    linarith
  exact hball hmem hpos

theorem halfSpace_eq_of_sub_mem {V : Type*} [AddCommGroup V] [Module ℝ V]
    (S : Submodule ℝ V) {u v : V} (huv : u - v ∈ S) :
    {x | ∃ s ∈ S, ∃ r : ℝ, 0 ≤ r ∧ x = s + r • u} =
      {x | ∃ s ∈ S, ∃ r : ℝ, 0 ≤ r ∧ x = s + r • v} := by
  ext x
  constructor
  · rintro ⟨s, hs, r, hr, rfl⟩
    refine ⟨s + r • (u - v), S.add_mem hs (S.smul_mem _ huv), r, hr, ?_⟩
    module
  · rintro ⟨s, hs, r, hr, rfl⟩
    refine ⟨s - r • (u - v), S.sub_mem hs (S.smul_mem _ huv), r, hr, ?_⟩
    module

open Classical in
theorem exists_isPLHomeomorphOn_linearize_coface_pair [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {s : Finset E} (hs : s ∈ K.faces)
    (hbound : ∀ t ∈ K.faces, s ⊆ t → t.card ≤ s.card + 1) {x a b : E}
    (hx : x ∈ openSimplex s) (hab : a ≠ b)
    (hpair : {w | w ∉ s ∧ insert w s ∈ K.faces} = {a, b}) (T : Submodule ℝ E)
    (hcompl : IsCompl (vectorSpan ℝ (s : Set E)) T) :
    ∃ (u : E) (h : E → E), u ∈ T ∧ u ≠ 0 ∧ IsPLHomeomorphOn h univ univ ∧ h x = 0 ∧
      (∀ y, y - x ∈ T ↔ h y ∈ T) ∧
      ∀ᶠ y in 𝓝 x, y ∈ K.space ↔ h y ∈ vectorSpan ℝ (s : Set E) ⊔ Submodule.span ℝ {u} := by
  have ha : a ∉ s ∧ insert a s ∈ K.faces := by
    change a ∈ {w | w ∉ s ∧ insert w s ∈ K.faces}
    rw [hpair]
    exact Set.mem_insert a _
  have hb : b ∉ s ∧ insert b s ∈ K.faces := by
    change b ∈ {w | w ∉ s ∧ insert w s ∈ K.faces}
    rw [hpair]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, or_true]
  obtain ⟨u, huT, hu, hau, hru⟩ := exists_direction_into_simplex_of_transverse_submodule hx
    (notMem_affineSpan_of_affineIndependent_insert ha.1 (K.indep ha.2)) T hcompl.sup_eq_top
  obtain ⟨v, hvT, hv, hbv, hrv⟩ := exists_direction_into_simplex_of_transverse_submodule hx
    (notMem_affineSpan_of_affineIndependent_insert hb.1 (K.indep hb.2)) T hcompl.sup_eq_top
  have hfaces : insert a s ≠ insert b s := by
    intro heq
    have hamem : a ∈ insert b s := heq ▸ Finset.mem_insert_self a s
    rcases Finset.mem_insert.mp hamem with heq | has
    · exact hab heq
    · exact ha.1 has
  have hnot := not_pos_smul_of_eventually_mem_distinct_openSimplex K ha.2 hb.2 hfaces hru hrv
  obtain ⟨F, hF, hfix, hFT, hFcone⟩ := exists_isPLHomeomorphOn_straighten_two_halfSpaces
    hcompl.disjoint huT hvT hu hv hnot
  let C : E → Set E := fun d =>
    {q | ∃ z ∈ vectorSpan ℝ (s : Set E), ∃ r : ℝ, 0 ≤ r ∧ q = z + r • d}
  have hCa : C (a - x) = C u := halfSpace_eq_of_sub_mem _ hau
  have hCb : C (b - x) = C v := halfSpace_eq_of_sub_mem _ hbv
  have hlocal : ∀ᶠ y in 𝓝 x, y ∈ K.space ↔ y - x ∈ C u ∪ C v := by
    filter_upwards [eventually_mem_space_iff_mem_codimension_one_cone K hs hbound ⟨a, ha⟩ hx]
      with y hy
    constructor
    · intro hyK
      obtain ⟨w, hws, hwface, hcone⟩ := hy.mp hyK
      have hwm : w ∈ {z | z ∉ s ∧ insert z s ∈ K.faces} := ⟨hws, hwface⟩
      rw [hpair] at hwm
      rcases hwm with rfl | hwb
      · exact Or.inl (hCa ▸ hcone)
      · have hwb' : w = b := hwb
        subst w
        exact Or.inr (hCb ▸ hcone)
    · intro hyC
      apply hy.mpr
      rcases hyC with hyu | hyv
      · refine ⟨a, ha.1, ha.2, ?_⟩
        change y - x ∈ C (a - x)
        rwa [hCa]
      · refine ⟨b, hb.1, hb.2, ?_⟩
        change y - x ∈ C (b - x)
        rwa [hCb]
  have hFinj : Function.Injective F := fun p q hpq => hF.bijOn.injOn (mem_univ p) (mem_univ q) hpq
  have hmem : ∀ (P : Set E) (y : E), F y ∈ F '' P ↔ y ∈ P := by
    intro P y
    constructor
    · rintro ⟨z, hz, heq⟩
      exact hFinj heq ▸ hz
    · exact fun hy => ⟨y, hy, rfl⟩
  let h : E → E := fun y => F (y - x)
  have hh : IsPLHomeomorphOn h univ univ := by
    have hcomp := (isPLHomeomorphOn_add_const (-x)).trans hF
    apply hcomp.congr
    intro y _
    change F (y - x) = F (y + -x)
    rw [sub_eq_add_neg]
  refine ⟨u, h, huT, hu, hh, ?_, ?_, ?_⟩
  · change F (x - x) = 0
    rw [sub_self]
    exact hfix (Submodule.zero_mem _)
  · intro y
    change y - x ∈ T ↔ F (y - x) ∈ T
    have hm := hmem (T : Set E) (y - x)
    rw [hFT] at hm
    exact hm.symm
  · filter_upwards [hlocal] with y hy
    change (y ∈ K.space) ↔ F (y - x) ∈ vectorSpan ℝ (s : Set E) ⊔ Submodule.span ℝ {u}
    have hFcone' : F '' (C u ∪ C v) =
        (vectorSpan ℝ (s : Set E) ⊔ Submodule.span ℝ {u} : Submodule ℝ E) := hFcone
    have hm := hmem (C u ∪ C v) (y - x)
    rw [hFcone'] at hm
    exact hy.trans hm.symm

open Classical in
theorem exists_isPLHomeomorphOn_linearize_codimension_one [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {n : ℕ}
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) {s : Finset E} (hs : s ∈ K.faces)
    (hcard : s.card = n + 1) {x : E} (hx : x ∈ openSimplex s) (T : Submodule ℝ E)
    (hcompl : IsCompl (vectorSpan ℝ (s : Set E)) T) :
    ∃ (u : E) (h : E → E), u ∈ T ∧ u ≠ 0 ∧ IsPLHomeomorphOn h univ univ ∧ h x = 0 ∧
      (∀ y, y - x ∈ T ↔ h y ∈ T) ∧
      ((∀ᶠ y in 𝓝 x, y ∈ K.space ↔ h y ∈ vectorSpan ℝ (s : Set E) ⊔ Submodule.span ℝ {u}) ∨
        ∀ᶠ y in 𝓝 x, y ∈ K.space ↔ ∃ z ∈ vectorSpan ℝ (s : Set E),
          ∃ r : ℝ, 0 ≤ r ∧ h y = z + r • u) := by
  have hbound : ∀ t ∈ K.faces, s ⊆ t → t.card ≤ s.card + 1 := by
    intro t ht _
    rw [hcard]
    exact hK.card_le K ht
  rcases hK.codimension_one_cofaces K hs hcard with ⟨a, ha⟩ | ⟨a, b, hab, habset⟩
  · have hac : a ∉ s ∧ insert a s ∈ K.faces := by
      change a ∈ {w | w ∉ s ∧ insert w s ∈ K.faces}
      rw [ha]
      exact Set.mem_singleton a
    obtain ⟨u, huT, hu, hau, _⟩ := exists_direction_into_simplex_of_transverse_submodule hx
      (notMem_affineSpan_of_affineIndependent_insert hac.1 (K.indep hac.2)) T hcompl.sup_eq_top
    let C : E → Set E := fun d =>
      {q | ∃ z ∈ vectorSpan ℝ (s : Set E), ∃ r : ℝ, 0 ≤ r ∧ q = z + r • d}
    have hCa : C (a - x) = C u := halfSpace_eq_of_sub_mem _ hau
    have hh : IsPLHomeomorphOn (fun y : E => y - x) univ univ := by
      simpa only [sub_eq_add_neg] using isPLHomeomorphOn_add_const (-x)
    refine ⟨u, fun y => y - x, huT, hu, hh, sub_self x, fun _ => Iff.rfl, Or.inr ?_⟩
    filter_upwards [eventually_mem_space_iff_mem_codimension_one_cone K hs hbound ⟨a, hac⟩ hx]
      with y hy
    change (y ∈ K.space) ↔ y - x ∈ C u
    rw [← hCa]
    constructor
    · intro hyK
      obtain ⟨w, hw, hwface, hcone⟩ := hy.mp hyK
      have hwm : w ∈ {z | z ∉ s ∧ insert z s ∈ K.faces} := ⟨hw, hwface⟩
      rw [ha] at hwm
      have hwa : w = a := hwm
      subst w
      exact hcone
    · intro hcone
      exact hy.mpr ⟨a, hac.1, hac.2, hcone⟩
  · obtain ⟨u, h, huT, hu, hh, hhx, hT, hlocal⟩ :=
      exists_isPLHomeomorphOn_linearize_coface_pair K hs hbound hx hab habset T hcompl
    exact ⟨u, h, huT, hu, hh, hhx, hT, Or.inl hlocal⟩

theorem exists_linearMap_eq_one_halfSpace {V : Type*} [AddCommGroup V] [Module ℝ V]
    (S : Submodule ℝ V) {u : V} (hu : u ∉ S) :
    ∃ ℓ : V →ₗ[ℝ] ℝ, S ≤ LinearMap.ker ℓ ∧ ℓ u = 1 ∧
      ∀ x, (∃ z ∈ S, ∃ r : ℝ, 0 ≤ r ∧ x = z + r • u) ↔
        x ∈ S ⊔ Submodule.span ℝ {u} ∧ 0 ≤ ℓ x := by
  obtain ⟨ℓ, hℓ, hℓu⟩ := LinearMap.exists_extend_of_notMem (0 : S →ₗ[ℝ] ℝ) hu 1
  have hker : S ≤ LinearMap.ker ℓ := by
    intro x hx
    exact congrArg (fun L : S →ₗ[ℝ] ℝ => L ⟨x, hx⟩) hℓ
  have heval : ∀ z ∈ S, ∀ r : ℝ, ℓ (z + r • u) = r := by
    intro z hz r
    have hz0 : ℓ z = 0 := hker hz
    rw [map_add, map_smul, hz0, hℓu, smul_eq_mul, mul_one, zero_add]
  refine ⟨ℓ, hker, hℓu, fun x => ?_⟩
  constructor
  · rintro ⟨z, hz, r, hr, rfl⟩
    refine ⟨Submodule.add_mem _ (Submodule.mem_sup_left hz)
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton u)))), ?_⟩
    rw [heval z hz r]
    exact hr
  · rintro ⟨hx, hpos⟩
    obtain ⟨z, hz, w, hw, hzw⟩ := Submodule.mem_sup.mp hx
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hw
    have hr : 0 ≤ r := by rwa [← hzw, heval z hz r] at hpos
    exact ⟨z, hz, r, hr, hzw.symm⟩

def HasPLCrossingAt (A B : Set E) (x : E) : Prop :=
  ∃ (U V : Set E) (h : E → E) (P Q : Submodule ℝ E) (α β : E →ₗ[ℝ] ℝ),
    IsOpen U ∧ IsOpen V ∧ x ∈ U ∧ IsPLHomeomorphOn h U V ∧ h x = 0 ∧
      Module.finrank ℝ P = 2 ∧ Module.finrank ℝ Q = 2 ∧
      Module.finrank ℝ (P ⊓ Q : Submodule ℝ E) = 1 ∧ P ⊔ Q = ⊤ ∧
      (α = 0 ∨ ∃ u ∈ P ⊓ Q, α u ≠ 0) ∧ (β = 0 ∨ ∃ u ∈ P ⊓ Q, β u ≠ 0) ∧
      (α = 0 ∨ β = 0) ∧ ∀ᶠ y in 𝓝 x,
        (y ∈ A ↔ h y ∈ P ∧ 0 ≤ α (h y)) ∧ (y ∈ B ↔ h y ∈ Q ∧ 0 ≤ β (h y))

theorem HasPLCrossingAt.symm {A B : Set E} {x : E} (hAB : HasPLCrossingAt A B x) :
    HasPLCrossingAt B A x := by
  obtain ⟨U, V, h, P, Q, α, β, hU, hV, hxU, hh, hhx, hP, hQ, hI, hsup, hα, hβ, hzero, hlocal⟩ := hAB
  refine ⟨U, V, h, Q, P, β, α, hU, hV, hxU, hh, hhx, hQ, hP, ?_, ?_, ?_, ?_, hzero.symm, ?_⟩
  · exact (congrArg (fun R : Submodule ℝ E => Module.finrank ℝ R) (inf_comm Q P)).trans hI
  · simpa only [sup_comm] using hsup
  · simpa only [inf_comm] using hβ
  · simpa only [inf_comm] using hα
  · filter_upwards [hlocal] with y hy
    exact hy.symm

open Classical in
theorem hasPLCrossingAt_of_codimension_one [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hL : IsCombinatorialManifoldWithBoundary 2 L)
    (hdimE : Module.finrank ℝ E = 3) {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ L.faces)
    (hsc : s.card = 2) (htc : t.card = 3) {x : E} (hxs : x ∈ openSimplex s)
    (hxt : x ∈ openSimplex t)
    (hcompl : IsCompl (vectorSpan ℝ (s : Set E)) (vectorSpan ℝ (t : Set E))) :
    HasPLCrossingAt K.space L.space x := by
  let S := vectorSpan ℝ (s : Set E)
  let T := vectorSpan ℝ (t : Set E)
  have hSdim : Module.finrank ℝ S = 1 := by
    have h := (K.indep hs).finrank_vectorSpan (show Fintype.card s = 1 + 1 by
      simpa only [Fintype.card_coe] using hsc)
    have hrange : Set.range ((↑) : s → E) = (s : Set E) := by ext y; simp
    change Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : s → E))) = 1 at h
    rwa [hrange] at h
  have hTdim : Module.finrank ℝ T = 2 := by
    have h := (L.indep ht).finrank_vectorSpan (show Fintype.card t = 2 + 1 by
      simpa only [Fintype.card_coe] using htc)
    have hrange : Set.range ((↑) : t → E) = (t : Set E) := by ext y; simp
    change Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → E))) = 2 at h
    rwa [hrange] at h
  have htmax : ∀ u ∈ L.faces, t ⊆ u → u.card ≤ t.card := by
    intro u hu _
    rw [htc]
    exact hL.card_le L hu
  obtain ⟨u, h, huT, hu, hh, hhx, hT, hmodel⟩ :=
    exists_isPLHomeomorphOn_linearize_codimension_one K hK hs hsc hxs T hcompl
  have huS : u ∉ S := fun h => hu (Submodule.disjoint_def.mp hcompl.disjoint _ h huT)
  let P : Submodule ℝ E := S ⊔ Submodule.span ℝ {u}
  have huP : u ∈ P := Submodule.mem_sup_right (Submodule.subset_span (Set.mem_singleton u))
  have hspan1 : Module.finrank ℝ (Submodule.span ℝ ({u} : Set E)) = 1 := finrank_span_singleton hu
  have hI0 : Module.finrank ℝ (S ⊓ Submodule.span ℝ {u} : Submodule ℝ E) = 0 :=
    Submodule.finrank_eq_zero.mpr (disjoint_iff.mp (Submodule.disjoint_span_singleton_of_notMem huS))
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq S (Submodule.span ℝ {u})
  have hPdim : Module.finrank ℝ P = 2 := by
    change Module.finrank ℝ P + Module.finrank ℝ (S ⊓ Submodule.span ℝ {u} : Submodule ℝ E) =
      Module.finrank ℝ S + Module.finrank ℝ (Submodule.span ℝ ({u} : Set E)) at hdim
    omega
  have hPQT : P ⊔ T = ⊤ := by
    apply top_unique
    rw [← hcompl.sup_eq_top]
    exact sup_le_sup le_sup_left le_rfl
  have hdimPT := Submodule.finrank_sup_add_finrank_inf_eq P T
  rw [hPQT] at hdimPT
  have hIdim : Module.finrank ℝ (P ⊓ T : Submodule ℝ E) = 1 := by
    have hdim' : Module.finrank ℝ E + Module.finrank ℝ (P ⊓ T : Submodule ℝ E) =
        Module.finrank ℝ P + Module.finrank ℝ T := by simpa using hdimPT
    omega
  have hLmodel : ∀ᶠ y in 𝓝 x, y ∈ L.space ↔ h y ∈ T := by
    filter_upwards [eventually_mem_space_iff_sub_mem_vectorSpan L ht htmax hxt] with y hy
    exact hy.trans (hT y)
  rcases hmodel with hfull | hhalf
  · refine ⟨univ, univ, h, P, T, 0, 0, isOpen_univ, isOpen_univ, mem_univ x,
      hh, hhx, hPdim, hTdim, hIdim, hPQT, Or.inl rfl, Or.inl rfl, Or.inl rfl, ?_⟩
    filter_upwards [hfull, hLmodel] with y hyK hyL
    constructor
    · simpa only [LinearMap.zero_apply, le_refl, and_true] using hyK
    · simpa only [LinearMap.zero_apply, le_refl, and_true] using hyL
  · obtain ⟨ℓ, _, hℓu, hℓmodel⟩ := exists_linearMap_eq_one_halfSpace S huS
    have hℓne : ℓ u ≠ 0 := by rw [hℓu]; norm_num
    refine ⟨univ, univ, h, P, T, ℓ, 0, isOpen_univ, isOpen_univ, mem_univ x,
      hh, hhx, hPdim, hTdim, hIdim, hPQT, Or.inr ⟨u, ⟨huP, huT⟩, hℓne⟩,
        Or.inl rfl, Or.inr rfl, ?_⟩
    filter_upwards [hhalf, hLmodel] with y hyK hyL
    constructor
    · exact hyK.trans (hℓmodel (h y))
    · simpa only [LinearMap.zero_apply, le_refl, and_true] using hyL

open Classical in
theorem hasPLCrossingAt_of_transverse_face [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hL : IsCombinatorialManifoldWithBoundary 2 L)
    (hdimE : Module.finrank ℝ E = 3) {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ L.faces)
    {x : E} (hxs : x ∈ openSimplex s) (hxt : x ∈ openSimplex t)
    (hst : vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) = ⊤) :
    HasPLCrossingAt K.space L.space x := by
  have hfaceRank : ∀ (P : Geometry.SimplicialComplex ℝ E) (u : Finset E), u ∈ P.faces →
      Module.finrank ℝ (vectorSpan ℝ (u : Set E)) + 1 = u.card := by
    intro P u hu
    obtain ⟨v, hv⟩ := P.nonempty_of_mem_faces hu
    have : Nonempty u := ⟨⟨v, hv⟩⟩
    have hrange : Set.range ((↑) : u → E) = (u : Set E) := by ext y; simp
    have h := (P.indep hu).finrank_vectorSpan_add_one
    change Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : u → E))) + 1 = Fintype.card u at h
    rw [hrange] at h
    simpa only [Fintype.card_coe] using h
  have hsRank := hfaceRank K s hs
  have htRank := hfaceRank L t ht
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (vectorSpan ℝ (s : Set E)) (vectorSpan ℝ (t : Set E))
  rw [hst] at hdim
  have hdim' : Module.finrank ℝ E +
      Module.finrank ℝ (vectorSpan ℝ (s : Set E) ⊓ vectorSpan ℝ (t : Set E) : Submodule ℝ E) =
        Module.finrank ℝ (vectorSpan ℝ (s : Set E)) +
          Module.finrank ℝ (vectorSpan ℝ (t : Set E)) := by simpa using hdim
  have hsbound := hK.card_le K hs
  have htbound := hL.card_le L ht
  have hcases : (s.card = 2 ∧ t.card = 3) ∨ (s.card = 3 ∧ t.card = 2) ∨
      (s.card = 3 ∧ t.card = 3) := by omega
  rcases hcases with ⟨hsc, htc⟩ | ⟨hsc, htc⟩ | ⟨hsc, htc⟩
  · have hinf : Module.finrank ℝ
        (vectorSpan ℝ (s : Set E) ⊓ vectorSpan ℝ (t : Set E) : Submodule ℝ E) = 0 := by omega
    exact hasPLCrossingAt_of_codimension_one K L hK hL hdimE hs ht hsc htc hxs hxt
      (IsCompl.of_eq (Submodule.finrank_eq_zero.mp hinf) hst)
  · have hinf : Module.finrank ℝ
        (vectorSpan ℝ (s : Set E) ⊓ vectorSpan ℝ (t : Set E) : Submodule ℝ E) = 0 := by omega
    exact (hasPLCrossingAt_of_codimension_one L K hL hK hdimE ht hs htc hsc hxt hxs
      (IsCompl.of_eq (Submodule.finrank_eq_zero.mp hinf) hst).symm).symm
  · have hSdim : Module.finrank ℝ (vectorSpan ℝ (s : Set E)) = 2 := by omega
    have hTdim : Module.finrank ℝ (vectorSpan ℝ (t : Set E)) = 2 := by omega
    have hIdim : Module.finrank ℝ
        (vectorSpan ℝ (s : Set E) ⊓ vectorSpan ℝ (t : Set E) : Submodule ℝ E) = 1 := by omega
    have hsmax : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card := by
      intro u hu _
      rw [hsc]
      exact hK.card_le K hu
    have htmax : ∀ u ∈ L.faces, t ⊆ u → u.card ≤ t.card := by
      intro u hu _
      rw [htc]
      exact hL.card_le L hu
    have hh : IsPLHomeomorphOn (fun y : E => y - x) univ univ := by
      simpa only [sub_eq_add_neg] using isPLHomeomorphOn_add_const (-x)
    refine ⟨univ, univ, fun y => y - x, vectorSpan ℝ (s : Set E), vectorSpan ℝ (t : Set E),
      0, 0, isOpen_univ, isOpen_univ, mem_univ x, hh, sub_self x, hSdim, hTdim, hIdim, hst,
        Or.inl rfl, Or.inl rfl, Or.inl rfl, ?_⟩
    filter_upwards [eventually_mem_space_iff_sub_mem_vectorSpan K hs hsmax hxs,
      eventually_mem_space_iff_sub_mem_vectorSpan L ht htmax hxt] with y hyK hyL
    constructor
    · simpa only [LinearMap.zero_apply, le_refl, and_true] using hyK
    · simpa only [LinearMap.zero_apply, le_refl, and_true] using hyL

open Classical in
theorem hasPLCrossingAt_of_transverse_faces [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hL : IsCombinatorialManifoldWithBoundary 2 L)
    (hdimE : Module.finrank ℝ E = 3)
    (htrans : ∀ s ∈ K.faces, ∀ t ∈ L.faces,
      (convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)).Nonempty →
        vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) = ⊤)
    {x : E} (hx : x ∈ K.space ∩ L.space) : HasPLCrossingAt K.space L.space x := by
  obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex K hx.1
  obtain ⟨t, ht, hxt⟩ := exists_face_mem_openSimplex L hx.2
  have hst := htrans s hs t ht ⟨x, openSimplex_subset_convexHull _ hxs,
    openSimplex_subset_convexHull _ hxt⟩
  exact hasPLCrossingAt_of_transverse_face K L hK hL hdimE hs ht hxs hxt hst

open Classical in
theorem exists_small_homeomorph_generalPosition [FiniteDimensional ℝ E]
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hL : IsCombinatorialManifoldWithBoundary 2 L)
    (hdimE : Module.finrank ℝ E = 3) {U : Set E} (hU : IsOpen U) (hKU : K.space ⊆ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (h : E → E) (G : Geometry.SimplicialComplex ℝ E),
      IsPLHomeomorphOn h univ univ ∧ (∀ x, dist (h x) x < ε) ∧ EqOn h id Uᶜ ∧
        G.faces.Finite ∧ G.space = h '' K.space ∩ L.space ∧
          IsCombinatorialManifoldWithBoundary 1 G ∧
          ∀ x ∈ h '' K.space ∩ L.space, HasPLCrossingAt (h '' K.space) L.space x := by
  obtain ⟨a, h, _, hh, hclose, hfix, hKA, htrans⟩ :=
    exists_small_homeomorph_transverse_affineImage K L hU hKU hε
  let A := AffineEquiv.constVAdd ℝ E a
  let K' := affineImage K A
  have : Finite K'.faces := (affineImage_faces_finite K A).to_subtype
  have hK' : IsCombinatorialManifoldWithBoundary 2 K' :=
    hK.of_isPLHomeomorphOn (isPLHomeomorphOn_affineImage K A)
  obtain ⟨G, hGfin, hGspace, hGman⟩ :=
    exists_isCombinatorialManifoldWithBoundary_inter_of_transverse_faces K' L hK' hL hdimE htrans
  rw [hKA] at hGspace
  refine ⟨h, G, hh, hclose, hfix, hGfin, hGspace, hGman, ?_⟩
  intro x hx
  have hx' : x ∈ K'.space ∩ L.space := by rw [hKA]; exact hx
  have hcross := hasPLCrossingAt_of_transverse_faces K' L hK' hL hdimE htrans hx'
  rwa [hKA] at hcross

open Classical in
theorem exists_continuousLinearMap_injOn [FiniteDimensional ℝ E] {A : Set E}
    (hA : A.Finite) (ℓ₀ : E →L[ℝ] ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ℓ : E →L[ℝ] ℝ, dist ℓ ℓ₀ < ε ∧ Set.InjOn ℓ A := by
  have : Finite A := hA.to_subtype
  let I := {p : A × A // p.1 ≠ p.2}
  let B : I → AffineSubspace ℝ (E →L[ℝ] ℝ) := fun i =>
    (LinearMap.ker ((ContinuousLinearMap.apply ℝ ℝ
      ((i.1.1 : E) - (i.1.2 : E))).toLinearMap)).toAffineSubspace
  have hB : ∀ i, B i ≠ ⊤ := by
    intro i hi
    have hd : (i.1.1 : E) - (i.1.2 : E) ≠ 0 := fun h =>
      i.2 (Subtype.ext (sub_eq_zero.mp h))
    obtain ⟨f, _, hf⟩ := LinearMap.exists_extend_of_notMem
      (0 : (⊥ : Submodule ℝ E) →ₗ[ℝ] ℝ) (by simpa using hd) 1
    have hmem : LinearMap.toContinuousLinearMap f ∈ B i := by rw [hi]; trivial
    change f ((i.1.1 : E) - (i.1.2 : E)) = 0 at hmem
    rw [hf] at hmem
    exact one_ne_zero hmem
  obtain ⟨ℓ, hclose, havoid⟩ := exists_mem_ball_notMem_affineSubspaces B hB hε
  refine ⟨ℓ, hclose, fun x hx y hy hxy => ?_⟩
  by_contra hne
  let i : I := ⟨(⟨x, hx⟩, ⟨y, hy⟩), fun h => hne (congrArg Subtype.val h)⟩
  apply havoid i
  change ℓ (x - y) = 0
  rw [map_sub, hxy, sub_self]

theorem add_smul_sub_mem_openSimplex {s : Finset E} {x y : E}
    (hx : x ∈ openSimplex s) (hy : y ∈ convexHull ℝ (s : Set E))
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) : x + r • (y - x) ∈ openSimplex s := by
  obtain ⟨α, hαpos, hαsum, hαx⟩ := hx
  obtain ⟨β, hβpos, hβsum, hβy⟩ := mem_convexHull_iff_exists_weights.mp hy
  refine ⟨fun v => (1 - r) * α v + r * β v, fun v hv => ?_, ?_, ?_⟩
  · exact add_pos_of_pos_of_nonneg (mul_pos (sub_pos.mpr hr1) (hαpos v hv))
      (mul_nonneg hr (hβpos v hv))
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hαsum, hβsum]
    ring
  · simp_rw [add_smul, mul_smul]
    rw [Finset.sum_add_distrib, ← Finset.smul_sum, ← Finset.smul_sum, hαx, hβy]
    simp only [sub_smul, one_smul, smul_sub]
    abel

open Classical in
theorem exists_affineIndependent_openSimplex_superset [FiniteDimensional ℝ E]
    (n : ℕ) (hn : Module.finrank ℝ E = n) {C : Set E} (hC : Bornology.IsBounded C) :
    ∃ T : Finset E, AffineIndependent ℝ ((↑) : T → E) ∧ T.card = n + 1 ∧
      C ⊆ openSimplex T := by
  obtain ⟨S, hS, hScard, h0, _, hnhds⟩ := exists_openSimplex_nhds n hn (0 : E) Filter.univ_mem
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnhds
  obtain ⟨R, hR⟩ := hC.subset_ball (0 : E)
  let a : ℝ := 2 * (|R| + 1) / r
  have ha : 0 < a := by dsimp [a]; positivity
  let A : E →ᵃ[ℝ] E := a • AffineMap.id ℝ E
  have hA : ∀ x, A x = a • x := fun _ => rfl
  have hAinj : Function.Injective A := fun _ _ h => smul_right_injective E ha.ne' h
  refine ⟨S.image A, affineIndependent_image_of_injOn_convexHull A hS hAinj.injOn, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hAinj, hScard]
  · intro y hy
    have hyR : ‖y‖ < |R| + 1 := by
      have hy' : ‖y‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hR hy
      linarith [le_abs_self R]
    have hnorm : ‖(2 : ℝ) • (a⁻¹ • y)‖ < r := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        Real.norm_of_nonneg (inv_nonneg.mpr ha.le)]
      have haeq : a * r = 2 * (|R| + 1) := by dsimp [a]; exact div_mul_cancel₀ _ hr.ne'
      apply (mul_lt_mul_iff_right₀ ha).mp
      calc a * (2 * (a⁻¹ * ‖y‖)) = 2 * ‖y‖ := by field_simp
        _ < 2 * (|R| + 1) := by linarith
        _ = a * r := haeq.symm
    have hz : a⁻¹ • y ∈ openSimplex S := by
      have h := add_smul_sub_mem_openSimplex h0
        (hball (by simpa only [Metric.mem_ball, dist_zero_right] using hnorm))
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 : ℝ) / 2 < 1)
      simpa only [sub_zero, zero_add, smul_smul, show (1 : ℝ) / 2 * (2 * a⁻¹) = a⁻¹ by ring] using h
    obtain ⟨w, hwpos, hwsum, hwy⟩ := hz
    rw [mem_openSimplex_image_iff hAinj.injOn]
    refine ⟨w, hwpos, hwsum, ?_⟩
    rw [← affineMap_apply_sum_smul_comp A (fun v => v) hwsum, hwy, hA, smul_smul,
      mul_inv_cancel₀ ha.ne', one_smul]

theorem sup_ker_eq_top_of_apply_ne_zero {V : Type*} [AddCommGroup V] [Module ℝ V]
    (S : Submodule ℝ V) (ℓ : V →ₗ[ℝ] ℝ) {w : V} (hw : w ∈ S) (hℓw : ℓ w ≠ 0) :
    S ⊔ LinearMap.ker ℓ = ⊤ := by
  apply top_unique
  intro z _
  refine Submodule.mem_sup.mpr ⟨(ℓ z / ℓ w) • w, S.smul_mem _ hw,
    z - (ℓ z / ℓ w) • w, ?_, by abel⟩
  change ℓ (z - (ℓ z / ℓ w) • w) = 0
  rw [map_sub, map_smul, smul_eq_mul, div_mul_cancel₀ _ hℓw, sub_self]

open Classical in
theorem exists_affineIndependent_openSimplex_superset_of_subset_fiber [FiniteDimensional ℝ E]
    {n : ℕ} (hn : Module.finrank ℝ E = n + 1) (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    {r : ℝ} {C : Set E} (hC : Bornology.IsBounded C) (hCr : C ⊆ {x | ℓ x = r}) :
    ∃ T : Finset E, AffineIndependent ℝ ((↑) : T → E) ∧ T.card = n + 1 ∧
      C ⊆ openSimplex T ∧ convexHull ℝ (T : Set E) ⊆ {x | ℓ x = r} ∧
        vectorSpan ℝ (T : Set E) = LinearMap.ker ℓ := by
  obtain ⟨x₀, hx₀⟩ := DFunLike.ne_iff.mp hℓ
  rw [LinearMap.zero_apply] at hx₀
  let v : E := (ℓ x₀)⁻¹ • x₀
  have hv : ℓ v = 1 := by dsimp [v]; rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hx₀]
  have hrange : LinearMap.range ℓ = ⊤ := LinearMap.range_eq_top.mpr fun c =>
    ⟨c • v, by rw [map_smul, hv, smul_eq_mul, mul_one]⟩
  have hdim : Module.finrank ℝ (LinearMap.ker ℓ) = n := by
    have h := LinearMap.finrank_range_add_finrank_ker ℓ
    rw [hrange, finrank_top, Module.finrank_self, hn] at h
    omega
  let π : E →ₗ[ℝ] LinearMap.ker ℓ :=
    { toFun := fun x => ⟨x - ℓ x • v, by
        rw [LinearMap.mem_ker, map_sub, map_smul, hv, smul_eq_mul, mul_one, sub_self]⟩
      map_add' := fun x y => by
        apply Subtype.ext
        change x + y - ℓ (x + y) • v = (x - ℓ x • v) + (y - ℓ y • v)
        rw [map_add, add_smul]
        abel
      map_smul' := fun c x => by
        apply Subtype.ext
        change c • x - ℓ (c • x) • v = c • (x - ℓ x • v)
        simp only [map_smul, smul_eq_mul, smul_sub, smul_smul, v, mul_assoc] }
  obtain ⟨S, hS, hScard, hCS⟩ := exists_affineIndependent_openSimplex_superset n hdim
    ((LinearMap.toContinuousLinearMap π).lipschitz.isBounded_image hC)
  let A : LinearMap.ker ℓ →ᵃ[ℝ] E :=
    (LinearMap.ker ℓ).subtype.toAffineMap + AffineMap.const ℝ (LinearMap.ker ℓ) (r • v)
  have hA : ∀ w, A w = (w : E) + r • v := fun _ => rfl
  have hAinj : Function.Injective A := fun _ _ h => Subtype.ext (add_right_cancel h)
  let T : Finset E := S.image A
  have hT : AffineIndependent ℝ ((↑) : T → E) :=
    affineIndependent_image_of_injOn_convexHull A hS hAinj.injOn
  have hTcard : T.card = n + 1 := by
    dsimp [T]
    rw [Finset.card_image_of_injective _ hAinj, hScard]
  have hTlevel : ∀ w ∈ T, ℓ w = r := by
    intro w hw
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hw
    rw [hA, map_add, map_smul, hv, smul_eq_mul, mul_one,
      show ℓ (z : E) = 0 from z.2, zero_add]
  have hspan : vectorSpan ℝ (T : Set E) ≤ LinearMap.ker ℓ := by
    rw [vectorSpan_def]
    apply Submodule.span_le.mpr
    rintro _ ⟨y, hy, z, hz, rfl⟩
    change ℓ (y - z) = 0
    rw [map_sub, hTlevel y hy, hTlevel z hz, sub_self]
  refine ⟨T, hT, hTcard, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨w, hwpos, hwsum, hwx⟩ := hCS ⟨x, hx, rfl⟩
    rw [mem_openSimplex_image_iff hAinj.injOn]
    refine ⟨w, hwpos, hwsum, ?_⟩
    rw [← affineMap_apply_sum_smul_comp A (fun z => z) hwsum, hwx, hA]
    change x - ℓ x • v + r • v = x
    rw [hCr hx, sub_add_cancel]
  · intro x hx
    obtain ⟨w, _, hwsum, hwx⟩ := mem_convexHull_iff_exists_weights.mp hx
    change ℓ x = r
    rw [← hwx, map_sum]
    simp_rw [map_smul, smul_eq_mul]
    calc ∑ y ∈ T, w y * ℓ y = ∑ y ∈ T, w y * r :=
        Finset.sum_congr rfl fun y hy => by rw [hTlevel y hy]
      _ = r := by rw [← Finset.sum_mul, hwsum, one_mul]
  · apply Submodule.eq_of_le_of_finrank_eq hspan
    have h := hT.finrank_vectorSpan (show Fintype.card T = n + 1 by
      simpa only [Fintype.card_coe] using hTcard)
    have hrangeT : Set.range ((↑) : T → E) = (T : Set E) := by ext x; simp
    change Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : T → E))) = n at h
    rw [hrangeT] at h
    exact h.trans hdim.symm

theorem HasPLCrossingAt.congr {A B A' B' : Set E} {x : E} (hAB : HasPLCrossingAt A B x)
    (hA : ∀ᶠ y in 𝓝 x, y ∈ A ↔ y ∈ A') (hB : ∀ᶠ y in 𝓝 x, y ∈ B ↔ y ∈ B') :
    HasPLCrossingAt A' B' x := by
  obtain ⟨U, V, h, P, Q, α, β, hU, hV, hxU, hh, hhx, hP, hQ, hI, hsup, hα, hβ, hzero, hlocal⟩ := hAB
  refine ⟨U, V, h, P, Q, α, β, hU, hV, hxU, hh, hhx, hP, hQ, hI, hsup, hα, hβ, hzero, ?_⟩
  filter_upwards [hlocal, hA, hB] with y hy hyA hyB
  exact ⟨hyA.symm.trans hy.1, hyB.symm.trans hy.2⟩

theorem vectorSpan_sup_ker_eq_top_of_mem_fiber (K : Geometry.SimplicialComplex ℝ E)
    (ℓ : E →ₗ[ℝ] ℝ) {r : ℝ} (hr : ∀ v, {v} ∈ K.faces → ℓ v ≠ r)
    {s : Finset E} (hs : s ∈ K.faces) {x : E} (hx : x ∈ convexHull ℝ (s : Set E))
    (hxr : ℓ x = r) : vectorSpan ℝ (s : Set E) ⊔ LinearMap.ker ℓ = ⊤ := by
  obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs
  have hvface := K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
  have hd : x - v ∈ vectorSpan ℝ (s : Set E) := by
    have h := AffineSubspace.vsub_mem_direction (convexHull_subset_affineSpan _ hx)
      (subset_affineSpan ℝ (s : Set E) hv)
    simpa only [direction_affineSpan, vsub_eq_sub] using h
  refine sup_ker_eq_top_of_apply_ne_zero _ ℓ hd ?_
  rw [map_sub, hxr]
  exact sub_ne_zero.mpr (Ne.symm (hr v hvface))

open Classical in
theorem exists_simplex_containing_fiber [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {n : ℕ}
    (hdimE : Module.finrank ℝ E = n + 1) (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (r : ℝ) :
    ∃ T : Finset E, AffineIndependent ℝ ((↑) : T → E) ∧ T.card = n + 1 ∧
      K.space ∩ convexHull ℝ (T : Set E) = K.space ∩ {x | ℓ x = r} ∧
      K.space ∩ {x | ℓ x = r} ⊆ openSimplex T ∧
      convexHull ℝ (T : Set E) ⊆ {x | ℓ x = r} ∧
      vectorSpan ℝ (T : Set E) = LinearMap.ker ℓ := by
  have hcompact : IsCompact (K.space ∩ {x | ℓ x = r}) :=
    (isPolyhedron_space K).isCompact.inter_right
      (isClosed_eq ℓ.continuous_of_finiteDimensional continuous_const)
  obtain ⟨T, hT, hTcard, hKT, hTlevel, hspan⟩ :=
    exists_affineIndependent_openSimplex_superset_of_subset_fiber hdimE ℓ hℓ hcompact.isBounded inter_subset_right
  have hspace : K.space ∩ convexHull ℝ (T : Set E) = K.space ∩ {x | ℓ x = r} :=
    Set.Subset.antisymm (fun _ hx => ⟨hx.1, hTlevel hx.2⟩)
      (fun _ hx => ⟨hx.1, openSimplex_subset_convexHull _ (hKT hx)⟩)
  exact ⟨T, hT, hTcard, hspace, hKT, hTlevel, hspan⟩

open Classical in
theorem exists_simplex_transverse_fiber [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {n : ℕ}
    (hdimE : Module.finrank ℝ E = n + 1) (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    {r : ℝ} (hr : ∀ v, {v} ∈ K.faces → ℓ v ≠ r) :
    ∃ (T : Finset E) (hT : AffineIndependent ℝ ((↑) : T → E)), T.card = n + 1 ∧
      K.space ∩ convexHull ℝ (T : Set E) = K.space ∩ {x | ℓ x = r} ∧
      K.space ∩ {x | ℓ x = r} ⊆ openSimplex T ∧
      vectorSpan ℝ (T : Set E) = LinearMap.ker ℓ ∧
      ∀ s ∈ K.faces, ∀ t ∈ (simplexComplex T hT).faces,
        (convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)).Nonempty →
          vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) = ⊤ := by
  obtain ⟨T, hT, hTcard, hspace, hKT, hTlevel, hspan⟩ :=
    exists_simplex_containing_fiber K hdimE ℓ hℓ r
  refine ⟨T, hT, hTcard, hspace, hKT, hspan, ?_⟩
  intro s hs t ht ⟨x, hxs, hxt⟩
  have hxT : x ∈ convexHull ℝ (T : Set E) :=
    convexHull_mono (Finset.coe_subset.mpr ht.2) hxt
  have hxr : ℓ x = r := hTlevel hxT
  have hxopen := hKT ⟨K.convexHull_subset_space hs hxs, hxr⟩
  have hTne : T.Nonempty := nonempty_of_mem_openSimplex hxopen
  have hTt := face_subset_of_mem_openSimplex_of_mem_convexHull (simplexComplex T hT)
    ⟨hTne, Finset.Subset.refl T⟩ ht hxopen hxt
  have htT : t = T := Finset.Subset.antisymm ht.2 hTt
  rw [htT, hspan]
  exact vectorSpan_sup_ker_eq_top_of_mem_fiber K ℓ hr hs hxs hxr

open Classical in
theorem exists_isCombinatorialManifoldWithBoundary_fiber [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) {n : ℕ}
    (hdimE : Module.finrank ℝ E = n + 2) (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    {r : ℝ} (hr : ∀ v, {v} ∈ K.faces → ℓ v ≠ r) :
    ∃ G : Geometry.SimplicialComplex ℝ E, G.faces.Finite ∧
      G.space = K.space ∩ {x | ℓ x = r} ∧ IsCombinatorialManifoldWithBoundary 1 G := by
  obtain ⟨T, hT, hTcard, hspace, _, _, htrans⟩ :=
    exists_simplex_transverse_fiber K (show Module.finrank ℝ E = (n + 1) + 1 by omega) ℓ hℓ hr
  let L := simplexComplex T hT
  have : Finite L.faces := (simplexComplex_faces_finite T hT).to_subtype
  have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
  have hLspace : L.space = convexHull ℝ (T : Set E) := simplexComplex_space T hT hTne
  have hLball : IsPLBall (n + 1) L.space := by
    rw [hLspace]
    exact isPLBall_convexHull_of_affineIndependent _ hT hTcard
  obtain ⟨G, hGfin, hGspace, hGman⟩ :=
    exists_isCombinatorialManifoldWithBoundary_inter_of_transverse_faces K L hK
      hLball.isCombinatorialManifoldWithBoundary (show Module.finrank ℝ E = 1 + n + 1 by omega) htrans
  rw [hLspace, hspace] at hGspace
  exact ⟨G, hGfin, hGspace, hGman⟩

open Classical in
theorem exists_generalPosition_fiber [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) {r : ℝ} (hr : ∀ v, {v} ∈ K.faces → ℓ v ≠ r) :
    ∃ G : Geometry.SimplicialComplex ℝ E, G.faces.Finite ∧
      G.space = K.space ∩ {x | ℓ x = r} ∧ IsCombinatorialManifoldWithBoundary 1 G ∧
      ∀ x ∈ K.space ∩ {y | ℓ y = r}, HasPLCrossingAt K.space {y | ℓ y = r} x := by
  obtain ⟨T, hT, hTcard, hspace, hKT, hspan, htrans⟩ :=
    exists_simplex_transverse_fiber K hdimE ℓ hℓ hr
  let L := simplexComplex T hT
  have : Finite L.faces := (simplexComplex_faces_finite T hT).to_subtype
  have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
  have hLspace : L.space = convexHull ℝ (T : Set E) := simplexComplex_space T hT hTne
  have hLball : IsPLBall 2 L.space := by
    rw [hLspace]
    exact isPLBall_convexHull_of_affineIndependent _ hT hTcard
  have hL := hLball.isCombinatorialManifoldWithBoundary
  have hKL : K.space ∩ L.space = K.space ∩ {x | ℓ x = r} := by rw [hLspace, hspace]
  obtain ⟨G, hGfin, hGspace, hGman⟩ :=
    exists_isCombinatorialManifoldWithBoundary_inter_of_transverse_faces K L hK hL hdimE htrans
  refine ⟨G, hGfin, hGspace.trans hKL, hGman, ?_⟩
  intro x hx
  have hxKL : x ∈ K.space ∩ L.space := by rw [hKL]; exact hx
  have hcross := hasPLCrossingAt_of_transverse_faces K L hK hL hdimE htrans hxKL
  apply hcross.congr (Filter.Eventually.of_forall fun _ => Iff.rfl)
  filter_upwards [eventually_mem_convexHull_iff_sub_mem_vectorSpan hT (hKT hx)] with y hy
  rw [hLspace]
  refine hy.trans ?_
  rw [hspan]
  change ℓ (y - x) = 0 ↔ ℓ y = r
  rw [map_sub, hx.2, sub_eq_zero]

open Classical in
theorem isCombinatorialManifold_one_iff [FiniteDimensional ℝ E]
    (G : Geometry.SimplicialComplex ℝ E) [Finite G.faces] :
    IsCombinatorialManifold 1 G ↔ (∀ s ∈ G.faces, s.card ≤ 2) ∧
      ∀ v, {v} ∈ G.faces → ∃ a b, a ≠ b ∧ {w | w ≠ v ∧ {v, w} ∈ G.faces} = {a, b} := by
  constructor
  · intro hG
    have hcard : ∀ s ∈ G.faces, s.card ≤ 2 := fun s hs => hG.card_le G hs
    refine ⟨hcard, fun v hv => ?_⟩
    have hlink : IsPLSphere 0 (SimplicialComplex.geometricLink G {v}).space := hG v hv
    rw [geometricLink_space_eq_neighbors_of_card_le G hcard v] at hlink
    exact isPLSphere_zero_iff.mp hlink
  · rintro ⟨hcard, hneighbors⟩ v hv
    change IsPLSphere 0 (SimplicialComplex.geometricLink G {v}).space
    rw [geometricLink_space_eq_neighbors_of_card_le G hcard v]
    exact isPLSphere_zero_iff.mpr (hneighbors v hv)

open Classical in
theorem IsCombinatorialManifold.codimension_one_cofaces [FiniteDimensional ℝ E]
    {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold (n + 1) K) {s : Finset E} (hs : s ∈ K.faces)
    (hcard : s.card = n + 1) :
    ∃ a b, a ≠ b ∧ {w | w ∉ s ∧ insert w s ∈ K.faces} = {a, b} := by
  have hlink := hK.isPLSphere_geometricLink K hs hcard le_rfl
  rw [Nat.sub_self] at hlink
  have hbound : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card + 1 := by
    intro u hu _
    rw [hcard]
    exact hK.card_le K hu
  rw [geometricLink_space_eq_coface_vertices_of_card_le K s hbound] at hlink
  exact isPLSphere_zero_iff.mp hlink

open Classical in
theorem neighbors_eq_pair_of_transverse_codimension_one [FiniteDimensional ℝ E]
    (K L G : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite G.faces] {n : ℕ}
    (hK : IsCombinatorialManifold (n + 1) K)
    (hcard : ∀ u ∈ G.faces, u.card ≤ 2) (hspace : G.space = K.space ∩ L.space)
    (hcarrier : ∀ u ∈ G.faces, ∃ v ∈ K.faces, ∃ z ∈ L.faces,
      convexHull ℝ (u : Set E) ⊆ convexHull ℝ (v : Set E) ∩ convexHull ℝ (z : Set E))
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ L.faces) (hscard : s.card = n + 1)
    (htmax : ∀ u ∈ L.faces, t ⊆ u → u.card ≤ t.card) {x : E}
    (hx : x ∈ openSimplex s) (hxt : x ∈ openSimplex t) (hxG : {x} ∈ G.faces)
    (htrans : IsCompl (vectorSpan ℝ (s : Set E)) (vectorSpan ℝ (t : Set E))) :
    ∃ a b, a ≠ b ∧ {y | y ≠ x ∧ {x, y} ∈ G.faces} = {a, b} := by
  have hsbound : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card + 1 := by
    intro u hu _
    rw [hscard]
    exact hK.card_le K hu
  obtain ⟨a, b, hab, habset⟩ := hK.codimension_one_cofaces K hs hscard
  exact neighbors_eq_pair_of_transverse_cofaces K L G hcard hspace hcarrier
    hs ht hsbound htmax hx hxt hxG htrans hab habset

open Classical in
theorem neighbors_eq_pair_of_transverse_maximal_face [FiniteDimensional ℝ E]
    (K L G : Geometry.SimplicialComplex ℝ E) [Finite K.faces] [Finite G.faces] {m n : ℕ}
    (hK : IsCombinatorialManifold (m + 1) K) (hdimE : Module.finrank ℝ E = m + n + 1)
    (hcard : ∀ u ∈ G.faces, u.card ≤ 2) (hspace : G.space = K.space ∩ L.space)
    (hcarrier : ∀ u ∈ G.faces, ∃ v ∈ K.faces, ∃ z ∈ L.faces,
      convexHull ℝ (u : Set E) ⊆ convexHull ℝ (v : Set E) ∩ convexHull ℝ (z : Set E))
    {s t : Finset E} (hs : s ∈ K.faces) (ht : t ∈ L.faces) (htcard : t.card = n + 2)
    (htmax : ∀ u ∈ L.faces, t ⊆ u → u.card ≤ t.card) {x : E}
    (hxs : x ∈ openSimplex s) (hxt : x ∈ openSimplex t) (hxG : {x} ∈ G.faces)
    (hst : vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) = ⊤) :
    ∃ a b, a ≠ b ∧ {y | y ≠ x ∧ {x, y} ∈ G.faces} = {a, b} := by
  obtain ⟨v, hv⟩ := K.nonempty_of_mem_faces hs
  have : Nonempty s := ⟨⟨v, hv⟩⟩
  have hrange : Set.range ((↑) : s → E) = (s : Set E) := by ext y; simp
  have hsRank := (K.indep hs).finrank_vectorSpan_add_one
  change Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : s → E))) + 1 = Fintype.card s at hsRank
  rw [hrange] at hsRank
  have hsRank' : Module.finrank ℝ (vectorSpan ℝ (s : Set E)) + 1 = s.card := by
    simpa only [Fintype.card_coe] using hsRank
  have htRank := (L.indep ht).finrank_vectorSpan (show Fintype.card t = (n + 1) + 1 by
    simpa only [Fintype.card_coe] using htcard)
  have hranget : Set.range ((↑) : t → E) = (t : Set E) := by ext y; simp
  change Module.finrank ℝ (vectorSpan ℝ (Set.range ((↑) : t → E))) = n + 1 at htRank
  rw [hranget] at htRank
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq
    (vectorSpan ℝ (s : Set E)) (vectorSpan ℝ (t : Set E))
  rw [hst] at hdim
  have hdim' : Module.finrank ℝ E +
      Module.finrank ℝ (vectorSpan ℝ (s : Set E) ⊓ vectorSpan ℝ (t : Set E) : Submodule ℝ E) =
        Module.finrank ℝ (vectorSpan ℝ (s : Set E)) + n + 1 := by
    simpa only [finrank_top, htRank, add_assoc] using hdim
  have hsbound := hK.card_le K hs
  have hcases : s.card = m + 1 ∨ s.card = m + 2 := by omega
  rcases hcases with hsc | hsc
  · have hinf : Module.finrank ℝ
        (vectorSpan ℝ (s : Set E) ⊓ vectorSpan ℝ (t : Set E) : Submodule ℝ E) = 0 := by omega
    exact neighbors_eq_pair_of_transverse_codimension_one K L G hK hcard hspace hcarrier
      hs ht hsc htmax hxs hxt hxG (IsCompl.of_eq (Submodule.finrank_eq_zero.mp hinf) hst)
  · have hinf : Module.finrank ℝ
        (vectorSpan ℝ (s : Set E) ⊓ vectorSpan ℝ (t : Set E) : Submodule ℝ E) = 1 := by omega
    have hsmax : ∀ u ∈ K.faces, s ⊆ u → u.card ≤ s.card := by
      intro u hu _
      rw [hsc]
      exact hK.card_le K hu
    exact neighbors_eq_pair_of_finrank_inter_eq_one K L G hcard hspace hcarrier
      hs ht hsmax htmax hxs hxt hxG hinf

open Classical in
theorem exists_isCombinatorialManifold_fiber [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold 2 K)
    {n : ℕ} (hdimE : Module.finrank ℝ E = n + 2) (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    {r : ℝ} (hr : ∀ v, {v} ∈ K.faces → ℓ v ≠ r) :
    ∃ G : Geometry.SimplicialComplex ℝ E, G.faces.Finite ∧
      G.space = K.space ∩ {x | ℓ x = r} ∧ IsCombinatorialManifold 1 G := by
  obtain ⟨T, hT, hTcard, hspace, hKT, _, htrans⟩ :=
    exists_simplex_transverse_fiber K (show Module.finrank ℝ E = (n + 1) + 1 by omega) ℓ hℓ hr
  let L := simplexComplex T hT
  have : Finite L.faces := (simplexComplex_faces_finite T hT).to_subtype
  have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
  have ht : T ∈ L.faces := ⟨hTne, Finset.Subset.refl T⟩
  have hLspace : L.space = convexHull ℝ (T : Set E) := simplexComplex_space T hT hTne
  have htrans' : ∀ s ∈ K.faces, ∀ t ∈ L.faces,
      ((fun x : E => x + 0) '' convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)).Nonempty →
        vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) = ⊤ := by
    simpa only [add_zero, Set.image_id'] using htrans
  obtain ⟨G, hGfin, hGspace, hGfaces⟩ := exists_triangulation_inter_of_transverse_faces K L 0 htrans'
  have : Finite G.faces := hGfin.to_subtype
  have hGKL : G.space = K.space ∩ L.space := by
    simpa only [add_zero, Set.image_id'] using hGspace
  have hGlevel : G.space = K.space ∩ {x | ℓ x = r} := by rw [hGKL, hLspace, hspace]
  have hcard : ∀ u ∈ G.faces, u.card ≤ 2 := by
    intro u hu
    obtain ⟨s, hs, t, ht', _, hdim⟩ := hGfaces u hu
    have hscard := hK.card_le K hs
    have htcard : t.card ≤ T.card := Finset.card_le_card ht'.2
    omega
  have hcarrier : ∀ u ∈ G.faces, ∃ v ∈ K.faces, ∃ z ∈ L.faces,
      convexHull ℝ (u : Set E) ⊆ convexHull ℝ (v : Set E) ∩ convexHull ℝ (z : Set E) := by
    intro u hu
    obtain ⟨s, hs, t, ht', hsub, _⟩ := hGfaces u hu
    exact ⟨s, hs, t, ht', by simpa only [add_zero, Set.image_id'] using hsub⟩
  refine ⟨G, hGfin, hGlevel, (isCombinatorialManifold_one_iff G).mpr ⟨hcard, ?_⟩⟩
  intro x hxG
  have hxspace : x ∈ G.space := G.subset_space hxG (Finset.mem_singleton_self x)
  have hxlevel : x ∈ K.space ∩ {x | ℓ x = r} := by rwa [← hGlevel]
  obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex K hxlevel.1
  have hxt := hKT hxlevel
  have htmax : ∀ u ∈ L.faces, T ⊆ u → u.card ≤ T.card := fun _ hu _ => Finset.card_le_card hu.2
  have hst := htrans s hs T ht ⟨x, openSimplex_subset_convexHull _ hxs,
    openSimplex_subset_convexHull _ hxt⟩
  exact neighbors_eq_pair_of_transverse_maximal_face K L G hK
    (show Module.finrank ℝ E = 1 + n + 1 by omega) hcard hGKL hcarrier
    hs ht hTcard htmax hxs hxt hxG hst

open Classical in
theorem exists_continuousLinearMap_ne_zero_injOn [FiniteDimensional ℝ E] [Nontrivial E]
    {A : Set E} (hA : A.Finite) (ℓ₀ : E →L[ℝ] ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ℓ : E →L[ℝ] ℝ, dist ℓ ℓ₀ < ε ∧ ℓ ≠ 0 ∧ Set.InjOn ℓ A := by
  obtain ⟨v, hv⟩ := exists_ne (0 : E)
  obtain ⟨ℓ, hclose, hinj⟩ := exists_continuousLinearMap_injOn ((hA.insert v).insert 0) ℓ₀ hε
  refine ⟨ℓ, hclose, ?_, hinj.mono (by intro x hx; exact Or.inr (Or.inr hx))⟩
  intro hzero
  apply hv
  apply hinj (show v ∈ insert 0 (insert v A) by simp) (Set.mem_insert 0 _)
  rw [hzero]
  rfl

open Classical in
theorem exists_generalPosition_height [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hdimE : Module.finrank ℝ E = 3)
    (ℓ₀ : E →L[ℝ] ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ℓ : E →L[ℝ] ℝ, dist ℓ ℓ₀ < ε ∧ ℓ ≠ 0 ∧ Set.InjOn ℓ K.vertices ∧
      (ℓ '' K.vertices).Finite ∧ ∀ r ∉ ℓ '' K.vertices,
        ∃ G : Geometry.SimplicialComplex ℝ E, G.faces.Finite ∧
          G.space = K.space ∩ {x | ℓ x = r} ∧ IsCombinatorialManifoldWithBoundary 1 G ∧
          ∀ x ∈ K.space ∩ {y | ℓ y = r}, HasPLCrossingAt K.space {y | ℓ y = r} x := by
  have : Nontrivial E := Module.nontrivial_of_finrank_pos (by omega : 0 < Module.finrank ℝ E)
  have hvertices : K.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn (Set.toFinite K.faces)
  obtain ⟨ℓ, hclose, hℓ, hinj⟩ := exists_continuousLinearMap_ne_zero_injOn hvertices ℓ₀ hε
  refine ⟨ℓ, hclose, hℓ, hinj, hvertices.image ℓ, fun r hr => ?_⟩
  have hℓlin : ℓ.toLinearMap ≠ 0 := by
    intro hz
    apply hℓ
    ext x
    exact DFunLike.congr_fun hz x
  exact exists_generalPosition_fiber K hK hdimE ℓ.toLinearMap hℓlin
    (fun v hv hvr => hr ⟨v, hv, hvr⟩)

open Classical in
theorem exists_generalPosition_height_of_isCombinatorialManifold [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hdimE : Module.finrank ℝ E = 3)
    (ℓ₀ : E →L[ℝ] ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ℓ : E →L[ℝ] ℝ, dist ℓ ℓ₀ < ε ∧ ℓ ≠ 0 ∧ Set.InjOn ℓ K.vertices ∧
      (ℓ '' K.vertices).Finite ∧ ∀ r ∉ ℓ '' K.vertices,
        ∃ G : Geometry.SimplicialComplex ℝ E, G.faces.Finite ∧
          G.space = K.space ∩ {x | ℓ x = r} ∧ IsCombinatorialManifold 1 G ∧
          ∀ x ∈ K.space ∩ {y | ℓ y = r}, HasPLCrossingAt K.space {y | ℓ y = r} x := by
  obtain ⟨ℓ, hclose, hℓ, hinj, hfin, hlevels⟩ :=
    exists_generalPosition_height K hK.isCombinatorialManifoldWithBoundary hdimE ℓ₀ hε
  refine ⟨ℓ, hclose, hℓ, hinj, hfin, fun r hr => ?_⟩
  have hℓlin : ℓ.toLinearMap ≠ 0 := by
    intro hz
    apply hℓ
    ext x
    exact DFunLike.congr_fun hz x
  obtain ⟨G, hGfin, hGspace, hGman⟩ := exists_isCombinatorialManifold_fiber K hK hdimE
    ℓ.toLinearMap hℓlin (fun v hv hvr => hr ⟨v, hv, hvr⟩)
  obtain ⟨_, _, _, _, hcross⟩ := hlevels r hr
  exact ⟨G, hGfin, hGspace, hGman, hcross⟩

theorem vectorSpan_sup_ker_eq_top_of_injOn {V : Type*} [AddCommGroup V] [Module ℝ V]
    {s : Finset V} (ℓ : V →ₗ[ℝ] ℝ) (hℓ : Set.InjOn ℓ (s : Set V)) (hs : 1 < s.card) :
    vectorSpan ℝ (s : Set V) ⊔ LinearMap.ker ℓ = ⊤ := by
  obtain ⟨v, hv, w, hw, hvw⟩ := Finset.one_lt_card.mp hs
  apply sup_ker_eq_top_of_apply_ne_zero _ ℓ
    (show v - w ∈ vectorSpan ℝ (s : Set V) from vsub_mem_vectorSpan ℝ hv hw)
  rw [map_sub]
  exact sub_ne_zero.mpr fun h => hvw (hℓ hv hw h)

open Classical in
theorem exists_triangulation_fiber_of_injOn_vertices [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {m n : ℕ}
    (hK : ∀ s ∈ K.faces, s.card ≤ m + 2) (hdimE : Module.finrank ℝ E = n + 1)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : Set.InjOn ℓ K.vertices) (r : ℝ) :
    ∃ G : Geometry.SimplicialComplex ℝ E, G.faces.Finite ∧
      G.space = K.space ∩ {x | ℓ x = r} ∧ (∀ u ∈ G.faces, u.card ≤ m + 1) ∧
      ∀ u ∈ G.faces, ∃ s ∈ K.faces, convexHull ℝ (u : Set E) ⊆ convexHull ℝ (s : Set E) := by
  obtain ⟨T, hT, hTcard, hspace, _, _, hspan⟩ := exists_simplex_containing_fiber K hdimE ℓ hℓ r
  let L := simplexComplex T hT
  have : Finite L.faces := (simplexComplex_faces_finite T hT).to_subtype
  have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
  have ht : T ∈ L.faces := ⟨hTne, Finset.Subset.refl T⟩
  have hLspace : L.space = convexHull ℝ (T : Set E) := simplexComplex_space T hT hTne
  obtain ⟨G, hGfin, hGspace, hcarrier⟩ := exists_triangulation_inter K L
  have hGlevel : G.space = K.space ∩ {x | ℓ x = r} := by rw [hGspace, hLspace, hspace]
  refine ⟨G, hGfin, hGlevel, ?_, ?_⟩
  · intro u hu
    obtain ⟨s, hs, t, ht', hsub⟩ := hcarrier u hu
    have hus : (u : Set E) ⊆ convexHull ℝ (s : Set E) :=
      (subset_convexHull ℝ _).trans (hsub.trans inter_subset_left)
    by_cases hs1 : s.card ≤ 1
    · have hsc : s.card = 1 := by have := Finset.card_pos.mpr (K.nonempty_of_mem_faces hs); omega
      obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp hsc
      have hu1 : u.card ≤ 1 := by
        have hup : u ⊆ {p} := by
          intro v hv
          have h := hus hv
          simpa only [Finset.coe_singleton, convexHull_singleton, Set.mem_singleton_iff,
            Finset.mem_singleton] using h
        simpa only [Finset.card_singleton] using Finset.card_le_card hup
      omega
    · have htrans : vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (T : Set E) = ⊤ := by
        rw [hspan]
        apply vectorSpan_sup_ker_eq_top_of_injOn ℓ (hinj.mono ?_) (by omega)
        intro v hv
        exact K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
      have huT : (u : Set E) ⊆ convexHull ℝ (T : Set E) :=
        ((subset_convexHull ℝ _).trans (hsub.trans inter_subset_right)).trans
          (convexHull_mono (Finset.coe_subset.mpr ht'.2))
      have hsub' : (u : Set E) ⊆ (fun x : E => x + 0) '' convexHull ℝ (s : Set E) ∩
          convexHull ℝ (T : Set E) := by
        simpa only [add_zero, Set.image_id'] using Set.subset_inter hus huT
      have hbound := card_add_finrank_le_of_subset_transverse_faces K L hs ht
        (G.indep hu) (G.nonempty_of_mem_faces hu) 0 hsub' htrans
      have hsbound := hK s hs
      omega
  · intro u hu
    obtain ⟨s, hs, t, ht', hsub⟩ := hcarrier u hu
    exact ⟨s, hs, hsub.trans inter_subset_left⟩

theorem one_lt_card_of_mem_openSimplex_of_notMem_vertices
    (K : Geometry.SimplicialComplex ℝ E) {s : Finset E} (hs : s ∈ K.faces)
    {x : E} (hx : x ∈ openSimplex s) (hxv : x ∉ K.vertices) : 1 < s.card := by
  by_contra h
  have hspos := Finset.card_pos.mpr (K.nonempty_of_mem_faces hs)
  have hsc : s.card = 1 := by omega
  obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hsc
  have hxv' : x = v := by
    have h := openSimplex_subset_convexHull _ hx
    simpa only [Finset.coe_singleton, convexHull_singleton, Set.mem_singleton_iff] using h
  subst x
  exact hxv hs

theorem vectorSpan_sup_ker_eq_top_of_mem_openSimplex
    (K : Geometry.SimplicialComplex ℝ E) (ℓ : E →ₗ[ℝ] ℝ) (hinj : Set.InjOn ℓ K.vertices)
    {s : Finset E} (hs : s ∈ K.faces) {x : E} (hx : x ∈ openSimplex s) (hxv : x ∉ K.vertices) :
    vectorSpan ℝ (s : Set E) ⊔ LinearMap.ker ℓ = ⊤ := by
  apply vectorSpan_sup_ker_eq_top_of_injOn ℓ (hinj.mono ?_)
    (one_lt_card_of_mem_openSimplex_of_notMem_vertices K hs hx hxv)
  intro v hv
  exact K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)

open Classical in
theorem exists_triangulation_fiber_of_isCombinatorialManifold [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (hK : IsCombinatorialManifold 2 K)
    {n : ℕ} (hdimE : Module.finrank ℝ E = n + 2) (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0)
    (hinj : Set.InjOn ℓ K.vertices) (r : ℝ) :
    ∃ G : Geometry.SimplicialComplex ℝ E, G.faces.Finite ∧
      G.space = K.space ∩ {x | ℓ x = r} ∧ (∀ u ∈ G.faces, u.card ≤ 2) ∧
      ∀ x, {x} ∈ G.faces → x ∉ K.vertices →
        ∃ a b, a ≠ b ∧ {y | y ≠ x ∧ {x, y} ∈ G.faces} = {a, b} := by
  obtain ⟨G, hGfin, hGlevel, hcard, hGcarrier⟩ := exists_triangulation_fiber_of_injOn_vertices K
    (fun s hs => hK.card_le K hs) (show Module.finrank ℝ E = (n + 1) + 1 by omega) ℓ hℓ hinj r
  have : Finite G.faces := hGfin.to_subtype
  obtain ⟨T, hT, hTcard, hspace, hKT, _, hspan⟩ :=
    exists_simplex_containing_fiber K (show Module.finrank ℝ E = (n + 1) + 1 by omega) ℓ hℓ r
  let L := simplexComplex T hT
  have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
  have ht : T ∈ L.faces := ⟨hTne, Finset.Subset.refl T⟩
  have hLspace : L.space = convexHull ℝ (T : Set E) := simplexComplex_space T hT hTne
  have hGKL : G.space = K.space ∩ L.space := by rw [hLspace, hspace, hGlevel]
  have hcarrier : ∀ u ∈ G.faces, ∃ s ∈ K.faces, ∃ t ∈ L.faces,
      convexHull ℝ (u : Set E) ⊆ convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) := by
    intro u hu
    obtain ⟨s, hs, hsub⟩ := hGcarrier u hu
    refine ⟨s, hs, T, ht, fun y hy => ⟨hsub hy, ?_⟩⟩
    have hyG := G.convexHull_subset_space hu hy
    rw [hGlevel] at hyG
    exact openSimplex_subset_convexHull _ (hKT hyG)
  refine ⟨G, hGfin, hGlevel, hcard, fun x hxG hxv => ?_⟩
  have hxlevel : x ∈ K.space ∩ {x | ℓ x = r} := by
    rw [← hGlevel]
    exact G.subset_space hxG (Finset.mem_singleton_self x)
  obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex K hxlevel.1
  have hxt := hKT hxlevel
  have htmax : ∀ u ∈ L.faces, T ⊆ u → u.card ≤ T.card := fun _ hu _ => Finset.card_le_card hu.2
  have hst : vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (T : Set E) = ⊤ := by
    rw [hspan]
    exact vectorSpan_sup_ker_eq_top_of_mem_openSimplex K ℓ hinj hs hxs hxv
  exact neighbors_eq_pair_of_transverse_maximal_face K L G hK
    (show Module.finrank ℝ E = 1 + n + 1 by omega) hcard hGKL hcarrier
    hs ht hTcard htmax hxs hxt hxG hst

open Classical in
theorem hasPLCrossingAt_fiber_of_notMem_vertices [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) (hdimE : Module.finrank ℝ E = 3)
    (ℓ : E →ₗ[ℝ] ℝ) (hℓ : ℓ ≠ 0) (hinj : Set.InjOn ℓ K.vertices) {r : ℝ} {x : E}
    (hx : x ∈ K.space ∩ {y | ℓ y = r}) (hxv : x ∉ K.vertices) :
    HasPLCrossingAt K.space {y | ℓ y = r} x := by
  obtain ⟨T, hT, hTcard, _, hKT, _, hspan⟩ := exists_simplex_containing_fiber K hdimE ℓ hℓ r
  let L := simplexComplex T hT
  have : Finite L.faces := (simplexComplex_faces_finite T hT).to_subtype
  have hTne : T.Nonempty := Finset.card_pos.mp (by omega)
  have ht : T ∈ L.faces := ⟨hTne, Finset.Subset.refl T⟩
  have hLspace : L.space = convexHull ℝ (T : Set E) := simplexComplex_space T hT hTne
  have hLball : IsPLBall 2 L.space := by
    rw [hLspace]
    exact isPLBall_convexHull_of_affineIndependent _ hT hTcard
  obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex K hx.1
  have hxt := hKT hx
  have hst : vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (T : Set E) = ⊤ := by
    rw [hspan]
    exact vectorSpan_sup_ker_eq_top_of_mem_openSimplex K ℓ hinj hs hxs hxv
  have hcross := hasPLCrossingAt_of_transverse_face K L hK hLball.isCombinatorialManifoldWithBoundary
    hdimE hs ht hxs hxt hst
  apply hcross.congr (Filter.Eventually.of_forall fun _ => Iff.rfl)
  filter_upwards [eventually_mem_convexHull_iff_sub_mem_vectorSpan hT hxt] with y hy
  rw [hLspace]
  refine hy.trans ?_
  rw [hspan]
  change ℓ (y - x) = 0 ↔ ℓ y = r
  rw [map_sub, hx.2, sub_eq_zero]

open Classical in
theorem exists_generalPosition_height_fibers [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hdimE : Module.finrank ℝ E = 3)
    (ℓ₀ : E →L[ℝ] ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ ℓ : E →L[ℝ] ℝ, dist ℓ ℓ₀ < ε ∧ ℓ ≠ 0 ∧ Set.InjOn ℓ K.vertices ∧
      (ℓ '' K.vertices).Finite ∧ (∀ r, (K.vertices ∩ {x | ℓ x = r}).Subsingleton) ∧
      ∀ r, ∃ G : Geometry.SimplicialComplex ℝ E, G.faces.Finite ∧
        G.space = K.space ∩ {x | ℓ x = r} ∧ (∀ u ∈ G.faces, u.card ≤ 2) ∧
        (∀ x, {x} ∈ G.faces → x ∉ K.vertices →
          ∃ a b, a ≠ b ∧ {y | y ≠ x ∧ {x, y} ∈ G.faces} = {a, b}) ∧
        (r ∉ ℓ '' K.vertices → IsCombinatorialManifold 1 G) ∧
        ∀ x ∈ K.space ∩ {y | ℓ y = r}, x ∉ K.vertices →
          HasPLCrossingAt K.space {y | ℓ y = r} x := by
  obtain ⟨ℓ, hclose, hℓ, hinj, hfin, _⟩ :=
    exists_generalPosition_height_of_isCombinatorialManifold K hK hdimE ℓ₀ hε
  have hℓlin : ℓ.toLinearMap ≠ 0 := by
    intro hz
    apply hℓ
    ext x
    exact DFunLike.congr_fun hz x
  refine ⟨ℓ, hclose, hℓ, hinj, hfin, ?_, fun r => ?_⟩
  · intro r x hx y hy
    exact hinj hx.1 hy.1 (hx.2.trans hy.2.symm)
  · obtain ⟨G, hGfin, hGspace, hcard, hneighbors⟩ :=
      exists_triangulation_fiber_of_isCombinatorialManifold K hK hdimE ℓ.toLinearMap hℓlin hinj r
    change G.space = K.space ∩ {x | ℓ x = r} at hGspace
    have : Finite G.faces := hGfin.to_subtype
    refine ⟨G, hGfin, hGspace, hcard, hneighbors, ?_, ?_⟩
    · intro hr
      apply (isCombinatorialManifold_one_iff G).mpr
      refine ⟨hcard, fun x hxG => hneighbors x hxG ?_⟩
      intro hxv
      have hxlevel : x ∈ K.space ∩ {x | ℓ x = r} := by
        rw [← hGspace]
        exact G.subset_space hxG (Finset.mem_singleton_self x)
      exact hr ⟨x, hxv, hxlevel.2⟩
    · intro x hx hxv
      exact hasPLCrossingAt_fiber_of_notMem_vertices K hK.isCombinatorialManifoldWithBoundary
        hdimE ℓ.toLinearMap hℓlin hinj hx hxv

theorem dist_simplicialMap_le_of_dist_vertices_le {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (K : Geometry.SimplicialComplex ℝ E)
    {φ ψ : E → F} {ε : ℝ} (h : ∀ v ∈ K.vertices, dist (φ v) (ψ v) ≤ ε)
    {x : E} (hx : x ∈ K.space) : dist (simplicialMap K φ x) (simplicialMap K ψ x) ≤ ε := by
  obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
  have hsum : ∑ v ∈ s, weights s x v • (φ v - ψ v) ∈ closedBall (0 : F) ε :=
    (convex_closedBall (0 : F) ε).sum_mem (fun v hv => weights_nonneg hxs hv) (sum_weights hxs)
      fun v hv => by
        have hvK := K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
        simpa only [Metric.mem_closedBall, dist_zero_right, dist_eq_norm, sub_zero] using h v hvK
  rw [simplicialMap_eq_of_mem K φ hs hxs, simplicialMap_eq_of_mem K ψ hs hxs, dist_eq_norm]
  simpa only [Metric.mem_closedBall, dist_zero_right, smul_sub, Finset.sum_sub_distrib] using hsum

theorem dist_simplicialMap_lt_of_dist_vertices_lt {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (K : Geometry.SimplicialComplex ℝ E)
    {φ ψ : E → F} {ε : ℝ} (h : ∀ v ∈ K.vertices, dist (φ v) (ψ v) < ε)
    {x : E} (hx : x ∈ K.space) : dist (simplicialMap K φ x) (simplicialMap K ψ x) < ε := by
  obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
  have hsum : ∑ v ∈ s, weights s x v • (φ v - ψ v) ∈ ball (0 : F) ε :=
    (convex_ball (0 : F) ε).sum_mem (fun v hv => weights_nonneg hxs hv) (sum_weights hxs)
      fun v hv => by
        have hvK := K.down_closed hs (Finset.singleton_subset_iff.mpr hv) (Finset.singleton_nonempty v)
        simpa only [Metric.mem_ball, dist_zero_right, dist_eq_norm, sub_zero] using h v hvK
  rw [simplicialMap_eq_of_mem K φ hs hxs, simplicialMap_eq_of_mem K ψ hs hxs, dist_eq_norm]
  simpa only [Metric.mem_ball, dist_zero_right, smul_sub, Finset.sum_sub_distrib] using hsum

theorem simplicialMap_eqOn_of_eqOn_vertices {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K : Geometry.SimplicialComplex ℝ E) {φ ψ : E → F} (h : EqOn φ ψ K.vertices) :
    EqOn (simplicialMap K φ) (simplicialMap K ψ) K.space := by
  intro x hx
  apply dist_le_zero.mp
  exact dist_simplicialMap_le_of_dist_vertices_le K
    (fun v hv => by rw [h hv, dist_self]) hx

theorem simplicialMap_eqOn_of_faces_subset {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (K L : Geometry.SimplicialComplex ℝ E) (hLK : L.faces ⊆ K.faces) (φ : E → F) :
    EqOn (simplicialMap K φ) (simplicialMap L φ) L.space := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := L.mem_space_iff.mp hx
  rw [simplicialMap_eq_of_mem K φ (hLK hs) hxs, simplicialMap_eq_of_mem L φ hs hxs]

theorem simplicialMap_eqOn_subcomplex_of_eqOn_vertices {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] (K L : Geometry.SimplicialComplex ℝ E)
    (hLK : L.faces ⊆ K.faces) {φ ψ : E → F} (h : EqOn φ ψ L.vertices) :
    EqOn (simplicialMap K φ) (simplicialMap K ψ) L.space :=
  (simplicialMap_eqOn_of_faces_subset K L hLK φ).trans
    ((simplicialMap_eqOn_of_eqOn_vertices L h).trans (simplicialMap_eqOn_of_faces_subset K L hLK ψ).symm)

open Classical in
theorem convexHull_insert_inter_affineSubspace {s : Finset E} {p : E}
    (A : AffineSubspace ℝ E) (hs : (s : Set E) ⊆ A) (hp : p ∉ A) :
    convexHull ℝ ((insert p s : Finset E) : Set E) ∩ (A : Set E) = convexHull ℝ (s : Set E) := by
  have hsA : convexHull ℝ (s : Set E) ⊆ A := convexHull_min hs A.convex
  apply Set.Subset.antisymm
  · rintro x ⟨hx, hxA⟩
    have hps : p ∉ s := fun h => hp (hs h)
    rcases exists_combo_of_mem_convexHull_insert hps hx with rfl | ⟨z, hz, c, _, _, hxc⟩
    · exact False.elim (hp hxA)
    by_cases hc : c = 1
    · rw [hc, one_smul, add_sub_cancel] at hxc
      rwa [hxc]
    · have hzA := hsA hz
      have hdir : x - z ∈ A.direction := AffineSubspace.vsub_mem_direction hxA hzA
      have heq : x - z = (1 - c) • (p - z) := by
        rw [hxc]
        simp only [smul_sub, sub_smul, one_smul]
        abel
      have hpd := A.direction.smul_mem (1 - c)⁻¹ hdir
      rw [heq, smul_smul, inv_mul_cancel₀ (sub_ne_zero.mpr (Ne.symm hc)), one_smul] at hpd
      exact False.elim (hp ((AffineSubspace.vsub_right_mem_direction_iff_mem hzA p).mp hpd))
  · intro x hx
    exact ⟨convexHull_mono (by intro y hy; exact Finset.mem_insert_of_mem hy) hx, hsA hx⟩

open Classical in
theorem convexHull_insert_inter_eq_of_notMem_affineSpan {s t : Finset E} {p : E}
    (hp : p ∉ affineSpan ℝ ((s : Set E) ∪ (t : Set E))) :
    convexHull ℝ ((insert p s : Finset E) : Set E) ∩ convexHull ℝ (t : Set E) =
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) := by
  let A := affineSpan ℝ ((s : Set E) ∪ (t : Set E))
  have hsA : (s : Set E) ⊆ A := fun x hx => subset_affineSpan ℝ _ (Or.inl hx)
  have htA : convexHull ℝ (t : Set E) ⊆ A :=
    convexHull_min (fun x hx => subset_affineSpan ℝ _ (Or.inr hx)) A.convex
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨(convexHull_insert_inter_affineSubspace A hsA hp).subset ⟨hx.1, htA hx.2⟩, hx.2⟩
  · intro x hx
    exact ⟨convexHull_mono (by intro y hy; exact Finset.mem_insert_of_mem hy) hx.1, hx.2⟩

open Classical in
theorem exists_affineSubspace_insert_transverse [FiniteDimensional ℝ E] (s t : Finset E)
    (htrans : (convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E)).Nonempty →
      vectorSpan ℝ (s : Set E) ⊔ vectorSpan ℝ (t : Set E) = ⊤) :
    ∃ A : AffineSubspace ℝ E, A ≠ ⊤ ∧ ∀ p ∉ A,
      (convexHull ℝ ((insert p s : Finset E) : Set E) ∩ convexHull ℝ (t : Set E)).Nonempty →
        vectorSpan ℝ ((insert p s : Finset E) : Set E) ⊔ vectorSpan ℝ (t : Set E) = ⊤ := by
  let S := vectorSpan ℝ (s : Set E)
  let T := vectorSpan ℝ (t : Set E)
  have hgrow : ∀ p, S ⊔ T ≤ vectorSpan ℝ ((insert p s : Finset E) : Set E) ⊔ T := fun p =>
    sup_le_sup (vectorSpan_mono ℝ (by intro x hx; exact Finset.mem_insert_of_mem hx)) le_rfl
  have hbot : (⊥ : AffineSubspace ℝ E) ≠ ⊤ := by
    intro h
    have hz : (0 : E) ∈ (⊥ : AffineSubspace ℝ E) := by rw [h]; trivial
    exact hz
  by_cases hST : S ⊔ T = ⊤
  · refine ⟨⊥, hbot, fun p _ _ => top_unique ?_⟩
    rw [← hST]
    exact hgrow p
  let U := affineSpan ℝ ((s : Set E) ∪ (t : Set E))
  by_cases hU : U ≠ ⊤
  · refine ⟨U, hU, fun p hp hinter => top_unique ?_⟩
    rw [convexHull_insert_inter_eq_of_notMem_affineSpan hp] at hinter
    rw [← htrans hinter]
    exact hgrow p
  have hUtop : U = ⊤ := not_ne_iff.mp hU
  have hsne : s.Nonempty := by
    by_contra hs
    have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    have hdir := congrArg AffineSubspace.direction hUtop
    apply hST
    simpa only [U, S, T, hs0, Finset.coe_empty, Set.empty_union, direction_affineSpan,
      vectorSpan_empty, bot_sup_eq, AffineSubspace.direction_top] using hdir
  have htne : t.Nonempty := by
    by_contra ht
    have ht0 : t = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
    have hdir := congrArg AffineSubspace.direction hUtop
    apply hST
    simpa only [U, S, T, ht0, Finset.coe_empty, Set.union_empty, direction_affineSpan,
      vectorSpan_empty, sup_bot_eq, AffineSubspace.direction_top] using hdir
  obtain ⟨a, ha⟩ := hsne
  obtain ⟨b, hb⟩ := htne
  have hdir : (S ⊔ T) ⊔ Submodule.span ℝ {b - a} = ⊤ := by
    have h := congrArg AffineSubspace.direction hUtop
    dsimp [U] at h
    rw [AffineSubspace.span_union, AffineSubspace.direction_sup
      (subset_affineSpan ℝ (s : Set E) ha) (subset_affineSpan ℝ (t : Set E) hb),
      direction_affineSpan, direction_affineSpan, AffineSubspace.direction_top] at h
    exact h
  have hba : b - a ∉ S ⊔ T := by
    intro h
    have hsub : Submodule.span ℝ {b - a} ≤ S ⊔ T := Submodule.span_le.mpr (Set.singleton_subset_iff.mpr h)
    rw [sup_eq_left.mpr hsub] at hdir
    exact hST hdir
  let A := AffineSubspace.mk' a (S ⊔ T)
  have hA : A ≠ ⊤ := by
    intro h
    have h' := congrArg AffineSubspace.direction h
    rw [AffineSubspace.direction_mk', AffineSubspace.direction_top] at h'
    exact hST h'
  refine ⟨A, hA, fun p hp _ => ?_⟩
  have hpa : p - a ∉ S ⊔ T := by
    intro h
    apply hp
    exact AffineSubspace.mem_mk'.mpr h
  have htop : (S ⊔ T) ⊔ Submodule.span ℝ {p - a} = ⊤ :=
    (Submodule.sup_span_singleton_eq_top_iff hpa).mpr
      ((Submodule.sup_span_singleton_eq_top_iff hba).mp hdir)
  apply top_unique
  rw [← htop]
  refine sup_le (hgrow p) (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr ?_))
  exact Submodule.mem_sup_left (vsub_mem_vectorSpan ℝ
    (show p ∈ ((insert p s : Finset E) : Set E) from Finset.mem_insert_self p s)
    (show a ∈ ((insert p s : Finset E) : Set E) from Finset.mem_insert_of_mem ha))

open Classical in
theorem affineIndependent_insert_of_notMem_affineSpan {s : Finset E}
    (hs : AffineIndependent ℝ ((↑) : s → E)) {p : E} (hp : p ∉ affineSpan ℝ (s : Set E)) :
    AffineIndependent ℝ ((↑) : ↥(insert p s : Finset E) → E) := by
  apply (affineIndependent_insert_iff (fun h => hp (subset_affineSpan ℝ _ h)) hs).mpr
  rintro ⟨w, hw, hwp⟩
  apply hp
  have hmem := affineCombination_mem_affineSpan_image hw
    (s' := (s : Set E)) (fun v hv hnot => False.elim (hnot hv)) (id : E → E)
  rw [Finset.affineCombination_eq_linear_combination s id w hw] at hmem
  simpa only [id_eq, Set.image_id', hwp] using hmem

open Classical in
theorem exists_small_point_affineIndependent_insert_transverse [FiniteDimensional ℝ E]
    {ι κ : Type*} [Finite ι] [Finite κ] (s : ι → Finset E) (t : κ → Finset E)
    (hs : ∀ i, AffineIndependent ℝ ((↑) : s i → E))
    (hcard : ∀ i, (s i).card ≤ Module.finrank ℝ E)
    (htrans : ∀ i j, (convexHull ℝ (s i : Set E) ∩ convexHull ℝ (t j : Set E)).Nonempty →
      vectorSpan ℝ (s i : Set E) ⊔ vectorSpan ℝ (t j : Set E) = ⊤)
    (p₀ : E) {ε : ℝ} (hε : 0 < ε) :
    ∃ p : E, dist p p₀ < ε ∧
      (∀ i, p ∉ affineSpan ℝ (s i : Set E) ∧
        AffineIndependent ℝ ((↑) : ↥(insert p (s i) : Finset E) → E)) ∧
      ∀ i j, (convexHull ℝ ((insert p (s i) : Finset E) : Set E) ∩
        convexHull ℝ (t j : Set E)).Nonempty →
          vectorSpan ℝ ((insert p (s i) : Finset E) : Set E) ⊔ vectorSpan ℝ (t j : Set E) = ⊤ := by
  have hspan : ∀ i, affineSpan ℝ (s i : Set E) ≠ ⊤ := by
    intro i htop
    have hrange : Set.range ((↑) : s i → E) = (s i : Set E) := by ext x; simp
    have htop' : affineSpan ℝ (Set.range ((↑) : s i → E)) = ⊤ := by rwa [hrange]
    have h := (hs i).affineSpan_eq_top_iff_card_eq_finrank_add_one.mp htop'
    simp only [Fintype.card_coe] at h
    have hi := hcard i
    omega
  choose B hB hgood using fun q : ι × κ => exists_affineSubspace_insert_transverse
    (s q.1) (t q.2) (htrans q.1 q.2)
  let A : ι ⊕ (ι × κ) → AffineSubspace ℝ E := Sum.elim (fun i => affineSpan ℝ (s i : Set E)) B
  have hA : ∀ q, A q ≠ ⊤ := by
    rintro (i | q)
    · exact hspan i
    · exact hB q
  obtain ⟨p, hp, havoid⟩ := exists_mem_ball_notMem_affineSubspaces A hA hε
  exact ⟨p, hp, fun i => ⟨havoid (Sum.inl i),
      affineIndependent_insert_of_notMem_affineSpan (hs i) (havoid (Sum.inl i))⟩,
    fun i j => hgood (i, j) p (havoid (Sum.inr (i, j)))⟩

end DifferentialGeometry.Topology.PiecewiseLinear
