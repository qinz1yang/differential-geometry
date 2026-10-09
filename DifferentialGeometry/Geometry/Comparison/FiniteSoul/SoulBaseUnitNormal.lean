import DifferentialGeometry.Geometry.Comparison.FiniteSoul.NormalTubeLocal
import DifferentialGeometry.Geometry.Collapse.DistanceSmoothing.Finite.ChartMetric

/-!
# Local unit normal fields of a codimension-one finite-order slice (lane CMS3-FLOW, BASE-2, G3)

Design `docs/geometrization/chapter13/design-finite-soul-three-20261004.md` §3 "BASE" (the tube data for
W-SUB over the unit normals of a `C^r` hypersurface).

* `exists_local_unitNormal_field`: near every point of a `C^r` slice `S` of codimension one there is a
  `C^(r−1)` field `ν` of `g`-unit vectors, normal to `S` along `S`, spanning the normal line:
  every normal vector `v` based in the chart domain is `g(v, ν) ν`. In the slice chart, `ν` is
  `dc⁻¹ (κ^{-1/2} N e)` with `e` spanning `D^⊥`, `N` the raise of `c^* g` and `κ = ⟪e, N e⟫`.
* `exists_local_unitNormal_field_through`: the same field through a prescribed unit normal vector.
* `unit_normal_eq_or_neg`: two unit normal vectors at the same point agree up to sign.
* helpers: `contMDiffAt_smul_tube` (fibrewise scaling along a map into `TM`) and
  `contMDiffAt_inner_field_tube` (the metric on two fields along a map).
-/

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set Filter Function Metric
open scoped Manifold ContDiff Topology InnerProductSpace

namespace DifferentialGeometry.Geometry.FiniteSoul

section Helpers

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {X : Type*} [TopologicalSpace X] [ChartedSpace G X]

/-- **Fibrewise scaling along a map into `TM`** is `C^m`. -/
theorem contMDiffAt_smul_tube {m : ℕ∞ω} {φ : X → TangentBundle I M} {f : X → ℝ} {x : X}
    (hφ : ContMDiffAt J I.tangent m φ x) (hf : ContMDiffAt J 𝓘(ℝ, ℝ) m f x) :
    ContMDiffAt J I.tangent m (fun y => (⟨(φ y).proj, f y • (φ y).snd⟩ : TangentBundle I M)) x := by
  rw [contMDiffAt_totalSpace] at hφ ⊢
  refine ⟨hφ.1, ?_⟩
  set e := trivializationAt E (TangentSpace I : M → Type _) (φ x).proj with he
  have hbase : ∀ᶠ y in 𝓝 x, (φ y).proj ∈ e.baseSet :=
    hφ.1.continuousAt.preimage_mem_nhds
      (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' (φ x).proj))
  refine (hf.smul hφ.2).congr_of_eventuallyEq ?_
  filter_upwards [hbase] with y hy
  exact (e.linear ℝ hy).2 (f y) (φ y).snd

/-- **The metric on two fields along a map** is `C^m` (`m ≤ n`). -/
theorem contMDiffAt_inner_field_tube {n m : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (hmn : m ≤ n)
    {b : X → M} {v w : (y : X) → TangentSpace I (b y)} {x : X}
    (hv : ContMDiffAt J I.tangent m (fun y => (⟨b y, v y⟩ : TangentBundle I M)) x)
    (hw : ContMDiffAt J I.tangent m (fun y => (⟨b y, w y⟩ : TangentBundle I M)) x) :
    ContMDiffAt J 𝓘(ℝ, ℝ) m (fun y => g.inner (b y) (v y) (w y)) x := by
  have hb : ContMDiffAt J I m b x :=
    (Bundle.contMDiff_proj (TangentSpace I)).contMDiffAt.comp x hv
  have hG : ContMDiffAt J (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) m
      (fun y => TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun z : M => TangentSpace I z →L[ℝ] TangentSpace I z →L[ℝ] Bundle.Trivial M ℝ z)
        (b y) (g.inner (b y))) x :=
    (g.contMDiff.of_le hmn).contMDiffAt.comp x hb
  have h := ContMDiffAt.clm_bundle_apply₂ (E₁ := TangentSpace I) (E₂ := TangentSpace I)
    (E₃ := Bundle.Trivial M ℝ) (b := b) (ψ := fun y => g.inner (b y)) (v := v) (w := w) hG hv hw
  exact (contMDiffAt_totalSpace.mp h).2

end Helpers

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

variable {r : ℕ∞}

omit [FiniteDimensional ℝ E] in
/-- The metric is symmetric and bilinear: `g(λ v, v) = λ g(v, v)` in the form used below. -/
theorem inner_smul_self_left_tube {n : ℕ∞ω}
    (g : ContMDiffRiemannianMetric I n E (TangentSpace I : M → Type _)) (x : M) (a : ℝ)
    (v w : TangentSpace I x) : g.inner x (a • v) w = a * g.inner x v w := by
  rw [map_smul, smul_apply, smul_eq_mul]

/-- **Local unit normal fields of a codimension-one slice.** -/
theorem exists_local_unitNormal_field
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r) {S : Set M} {d : ℕ} (hcodim : Module.finrank ℝ E = d + 1)
    (hS : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) d S) {s₀ : M} (hs₀ : s₀ ∈ S) :
    ∃ O : Set M, IsOpen O ∧ s₀ ∈ O ∧ ∃ ν : (x : M) → TangentSpace I x,
      ContMDiffOn I I.tangent ((r - 1 : ℕ∞) : ℕ∞ω) (fun x => (⟨x, ν x⟩ : TangentBundle I M)) O ∧
      (∀ x ∈ O, g.inner x (ν x) (ν x) = 1) ∧
      (∀ x ∈ O ∩ S, (⟨x, ν x⟩ : TangentBundle I M) ∈ normalSetFinite g S) ∧
      ∀ v ∈ normalSetFinite g S, v.proj ∈ O →
        v.snd = g.inner v.proj v.snd (ν v.proj) • ν v.proj := by
  classical
  have hr1 : 1 ≤ r := one_le_two.trans hr
  have hk0 : ((r : ℕ∞) : ℕ∞ω) ≠ 0 := by exact_mod_cast (zero_lt_one.trans_le hr1).ne'
  set m : ℕ∞ω := ((r - 1 : ℕ∞) : ℕ∞ω) with hm
  have hm1 : m + 1 ≤ (r : ℕ∞ω) := coe_sub_one_add_one_le_tube hr1
  have hmn : m ≤ (r : ℕ∞ω) + 1 := coe_sub_one_le_add_one_tube
  have hmr : m ≤ (r : ℕ∞ω) := (le_add_of_nonneg_right zero_le_one).trans hm1
  obtain ⟨c, A, hA, hs₀c, hdimA, himage⟩ := hS s₀ hs₀
  set D : Submodule ℝ E := A.direction with hD
  -- a unit generator of the normal line `D^⊥`
  have hDperp : Module.finrank ℝ Dᗮ = 1 := by
    have h := Submodule.finrank_add_finrank_orthogonal D
    rw [hdimA, hcodim] at h
    omega
  obtain ⟨e₀, he₀, hspan⟩ := finrank_eq_one_iff'.mp hDperp
  set e : E := (e₀ : E) with he
  have heD : e ∈ Dᗮ := e₀.2
  have he0 : e ≠ 0 := fun h => he₀ (Subtype.ext h)
  have hline : ∀ w ∈ Dᗮ, ∃ μ : ℝ, w = μ • e := by
    intro w hw
    obtain ⟨μ, hμ⟩ := hspan ⟨w, hw⟩
    exact ⟨μ, (congrArg Subtype.val hμ).symm⟩
  set B : E → E →L[ℝ] E →L[ℝ] ℝ := slicePullbackFinite g c with hB
  set N : E → E →L[ℝ] E := fun y => normalRaiseFinite (B y) with hN
  have hBco : ∀ y ∈ c.target, IsCoercive (B y) := fun y hy =>
    isCoercive_slicePullbackFinite g hk0 hy
  set κ : E → ℝ := fun y => B y (N y e) (N y e) with hκ
  have hκe : ∀ y ∈ c.target, κ y = ⟪e, N y e⟫_ℝ := fun y hy =>
    apply_normalRaiseFinite (hBco y hy) e (N y e)
  have hκpos : ∀ y ∈ c.target, 0 < κ y := by
    intro y hy
    obtain ⟨b, hb, hcoer⟩ := hBco y hy
    have hNe : N y e ≠ 0 := by
      intro h0
      apply he0
      have h := gramOpFinite_normalRaiseFinite (hBco y hy) e
      change gramOpFinite (B y) (N y e) = e at h
      rw [h0, map_zero] at h
      exact h.symm
    have hpos : 0 < ‖N y e‖ := norm_pos_iff.mpr hNe
    have := hcoer (N y e)
    change b * ‖N y e‖ * ‖N y e‖ ≤ κ y at this
    nlinarith [mul_pos (mul_pos hb hpos) hpos]
  set a : E → E := fun y => (Real.sqrt (κ y))⁻¹ • N y e with ha
  -- smoothness of the coefficient field on the chart target
  have hBc := contDiffOn_slicePullbackFinite g c hmn hm1
  have hNc := contDiffOn_normalRaiseFinite hBc hBco
  have hac : ContDiffOn ℝ m a c.target := by
    have hNe : ContDiffOn ℝ m (fun y => N y e) c.target := hNc.clm_apply contDiffOn_const
    have hκc : ContDiffOn ℝ m κ c.target := (hBc.clm_apply hNe).clm_apply hNe
    have hsq : ContDiffOn ℝ m (fun y => Real.sqrt (κ y)) c.target := fun y hy =>
      ((hκc y hy).sqrt (hκpos y hy).ne')
    have hinv : ContDiffOn ℝ m (fun y => (Real.sqrt (κ y))⁻¹) c.target := fun y hy =>
      (hsq y hy).inv (Real.sqrt_pos.mpr (hκpos y hy)).ne'
    exact hinv.smul hNe
  set ν : (x : M) → TangentSpace I x := fun x => mfderiv 𝓘(ℝ, E) I c.symm (c x) (a (c x)) with hν
  have hunit : ∀ x ∈ c.source, g.inner x (ν x) (ν x) = 1 := by
    intro x hx
    have hxt : c x ∈ c.target := c.toPartialEquiv.map_source hx
    have key : ∀ x' : M, x' = c.symm (c x) → g.inner x' (ν x) (ν x) =
        B (c x) (a (c x)) (a (c x)) := by
      rintro x' rfl
      rfl
    rw [key x (c.toPartialEquiv.left_inv hx).symm]
    change B (c x) ((Real.sqrt (κ (c x)))⁻¹ • N (c x) e) ((Real.sqrt (κ (c x)))⁻¹ • N (c x) e) = 1
    simp only [map_smul, smul_apply, smul_eq_mul]
    change (Real.sqrt (κ (c x)))⁻¹ * ((Real.sqrt (κ (c x)))⁻¹ * κ (c x)) = 1
    have hs := Real.sq_sqrt (hκpos (c x) hxt).le
    have hs0 := (Real.sqrt_pos.mpr (hκpos (c x) hxt)).ne'
    field_simp
    nlinarith [hs]
  refine ⟨c.source, c.open_source, hs₀c, ν, ?_, hunit, ?_, ?_⟩
  · -- smoothness
    intro x hx
    have hxt : c x ∈ c.target := c.toPartialEquiv.map_source hx
    have hcs : ContMDiffAt 𝓘(ℝ, E) I (r : ℕ∞ω) c.symm (c x) :=
      c.symm.contMDiffOn.contMDiffAt (c.open_target.mem_nhds hxt)
    have hcx : ContMDiffAt I 𝓘(ℝ, E) m c x :=
      (c.contMDiffOn.contMDiffAt (c.open_source.mem_nhds hx)).of_le hmr
    have hax : ContMDiffAt I 𝓘(ℝ, E) m (fun x => a (c x)) x :=
      ((hac.contDiffAt (c.open_target.mem_nhds hxt)).contMDiffAt).comp x hcx
    have h := contMDiffAt_mk_mfderiv_apply hcs hm1 hcx hax
    refine (h.congr_of_eventuallyEq ?_).contMDiffWithinAt
    filter_upwards [c.open_source.mem_nhds hx] with x' hx'
    exact tangentBundle_mk_eq (c.toPartialEquiv.left_inv hx').symm rfl
  · -- normal along `S`
    rintro x ⟨hx, hxS⟩
    refine ⟨hxS, fun w hw => ?_⟩
    have hxt : c x ∈ c.target := c.toPartialEquiv.map_source hx
    have ht : (mfderiv I 𝓘(ℝ, E) c x w : E) ∈ D :=
      (mem_sliceTangent_chart_iff_ofOrder hk0 hxS hA hx himage).1 hw
    have hw' : (w : E) = mfderiv 𝓘(ℝ, E) I c.symm (c x) (mfderiv I 𝓘(ℝ, E) c x w) :=
      (mfderiv_symm_apply_mfderiv_ofOrder hk0 hx w).symm
    set t : E := mfderiv I 𝓘(ℝ, E) c x w with htdef
    have ht' : t ∈ D := ht
    have hB0 : B (c x) (a (c x)) t = 0 := by
      change B (c x) ((Real.sqrt (κ (c x)))⁻¹ • N (c x) e) t = 0
      rw [map_smul, smul_apply, apply_normalRaiseFinite (hBco _ hxt),
        Submodule.inner_left_of_mem_orthogonal ht' heD, smul_zero]
    have key : ∀ x' : M, x' = c.symm (c x) → ∀ X Y : E,
        g.inner (c.symm (c x)) X Y = 0 → g.inner x' X Y = 0 := by
      rintro x' rfl X Y h
      exact h
    have h2 := key x (c.toPartialEquiv.left_inv hx).symm _ _ hB0
    change g.inner x (ν x) w = 0
    rw [hw']
    exact h2
  · -- the normal line is spanned by `ν`
    intro v hv hvO
    set x : M := v.proj with hx
    have hxS : x ∈ S := hv.1
    have hxt : c x ∈ c.target := c.toPartialEquiv.map_source hvO
    set α : E := mfderiv I 𝓘(ℝ, E) c x v.snd with hα
    have hdα : mfderiv 𝓘(ℝ, E) I c.symm (c x) α = v.snd :=
      mfderiv_symm_apply_mfderiv_ofOrder hk0 hvO v.snd
    have hcx : c.symm (c x) = x := c.toPartialEquiv.left_inv hvO
    have hnormal : ∀ t ∈ D, B (c x) α t = 0 := by
      intro t ht
      have hxS' : c.symm (c x) ∈ S := by rw [hcx]; exact hxS
      have hxc' : c.symm (c x) ∈ c.source := c.toPartialEquiv.map_target hxt
      have htan : (mfderiv 𝓘(ℝ, E) I c.symm (c x) t : TangentSpace I (c.symm (c x))) ∈
          sliceTangent I S (c.symm (c x)) := by
        refine (mem_sliceTangent_chart_iff_ofOrder hk0 hxS' hA hxc' himage).2 ?_
        rw [mfderiv_apply_mfderiv_symm_tube hk0 hxt t]
        exact ht
      have key : ∀ x' : M, x' = x → ∀ X : E, X ∈ sliceTangent I S x' →
          g.inner x' v.snd X = 0 := by
        rintro x' rfl X hX
        exact hv.2 X hX
      rw [hB, slicePullbackFinite_apply, hdα]
      exact key _ hcx _ htan
    have hGα : gramOpFinite (B (c x)) α ∈ Dᗮ := by
      rw [Submodule.mem_orthogonal]
      intro t ht
      rw [real_inner_comm, inner_gramOpFinite]
      exact hnormal t ht
    obtain ⟨μ, hμ⟩ := hline _ hGα
    have hαe : α = μ • N (c x) e := by
      have h := normalRaiseFinite_gramOpFinite (hBco _ hxt) α
      rw [hμ, map_smul] at h
      exact h.symm
    have hs0 := (Real.sqrt_pos.mpr (hκpos (c x) hxt)).ne'
    have hNa : N (c x) e = Real.sqrt (κ (c x)) • a (c x) := by
      change _ = Real.sqrt (κ (c x)) • ((Real.sqrt (κ (c x)))⁻¹ • N (c x) e)
      rw [smul_smul, mul_inv_cancel₀ hs0, one_smul]
    have hv' : v.snd = (μ * Real.sqrt (κ (c x))) • ν x := by
      rw [← hdα, hαe, hNa, smul_smul]
      exact map_smul _ _ _
    have hcoef : g.inner x v.snd (ν x) = μ * Real.sqrt (κ (c x)) := by
      rw [hv', inner_smul_self_left_tube, hunit x hvO, mul_one]
    rw [hcoef]
    exact hv'

/-- **Two unit normal vectors at the same point agree up to sign** (codimension one). -/
theorem unit_normal_eq_or_neg
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r) {S : Set M} {d : ℕ} (hcodim : Module.finrank ℝ E = d + 1)
    (hS : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) d S) {v w : TangentBundle I M}
    (hv : v ∈ normalSetFinite g S) (hw : w ∈ normalSetFinite g S) (hvw : v.proj = w.proj)
    (hv1 : g.inner v.proj v.snd v.snd = 1) (hw1 : g.inner w.proj w.snd w.snd = 1) :
    (w.snd : E) = v.snd ∨ (w.snd : E) = -v.snd := by
  obtain ⟨O, -, hvO, ν, -, hunit, -, hlineν⟩ := exists_local_unitNormal_field g hr hcodim hS hv.1
  have hwO : w.proj ∈ O := hvw ▸ hvO
  set a : ℝ := g.inner v.proj v.snd (ν v.proj) with ha
  set b : ℝ := g.inner w.proj w.snd (ν w.proj) with hb
  have hva : v.snd = a • ν v.proj := hlineν v hv hvO
  have hwb : w.snd = b • ν w.proj := hlineν w hw hwO
  have hsq : ∀ (x : M) (l : ℝ), x ∈ O → g.inner x (l • ν x) (l • ν x) = l * l := by
    intro x l hx
    simp only [map_smul, smul_apply, smul_eq_mul, hunit x hx]
    ring
  have ha2 : a * a = 1 := by
    have h := hv1
    rw [hva, hsq _ _ hvO] at h
    exact h
  have hb2 : b * b = 1 := by
    have h := hw1
    rw [hwb, hsq _ _ hwO] at h
    exact h
  have hνeq : (ν w.proj : E) = ν v.proj := by rw [hvw]
  have hw' : (w.snd : E) = b • (ν v.proj : E) := by rw [← hνeq]; exact hwb
  have hv' : (v.snd : E) = a • (ν v.proj : E) := hva
  rcases mul_self_eq_one_iff.mp ha2 with ha1 | ha1 <;>
    rcases mul_self_eq_one_iff.mp hb2 with hb1 | hb1
  · left; rw [hw', hv', ha1, hb1]
  · right; rw [hw', hv', ha1, hb1, neg_smul]
  · right; rw [hw', hv', ha1, hb1, neg_smul, neg_neg]
  · left; rw [hw', hv', ha1, hb1]

/-- **A local unit normal field through a prescribed unit normal vector.** -/
theorem exists_local_unitNormal_field_through
    (g : ContMDiffRiemannianMetric I ((r : ℕ∞ω) + 1) E (TangentSpace I : M → Type _))
    (hr : 2 ≤ r) {S : Set M} {d : ℕ} (hcodim : Module.finrank ℝ E = d + 1)
    (hS : IsEmbeddedSliceOfOrder I (r : ℕ∞ω) d S) {v₀ : TangentBundle I M}
    (hv₀ : v₀ ∈ normalSetFinite g S) (hv₀1 : g.inner v₀.proj v₀.snd v₀.snd = 1) :
    ∃ O : Set M, IsOpen O ∧ v₀.proj ∈ O ∧ ∃ ν : (x : M) → TangentSpace I x,
      ContMDiffOn I I.tangent ((r - 1 : ℕ∞) : ℕ∞ω) (fun x => (⟨x, ν x⟩ : TangentBundle I M)) O ∧
      (∀ x ∈ O, g.inner x (ν x) (ν x) = 1) ∧
      (∀ x ∈ O ∩ S, (⟨x, ν x⟩ : TangentBundle I M) ∈ normalSetFinite g S) ∧
      (∀ v ∈ normalSetFinite g S, v.proj ∈ O →
        v.snd = g.inner v.proj v.snd (ν v.proj) • ν v.proj) ∧
      ν v₀.proj = v₀.snd := by
  obtain ⟨O, hO, hv₀O, ν, hνs, hunit, hnormal, hlineν⟩ :=
    exists_local_unitNormal_field g hr hcodim hS hv₀.1
  set a : ℝ := g.inner v₀.proj v₀.snd (ν v₀.proj) with ha
  have hva : v₀.snd = a • ν v₀.proj := hlineν v₀ hv₀ hv₀O
  have ha2 : a * a = 1 := by
    have h := hv₀1
    rw [hva] at h
    simp only [map_smul, smul_apply, smul_eq_mul, hunit _ hv₀O] at h
    linarith
  rcases mul_self_eq_one_iff.mp ha2 with ha1 | ha1
  · refine ⟨O, hO, hv₀O, ν, hνs, hunit, hnormal, hlineν, ?_⟩
    rw [hva, ha1, one_smul]
  · refine ⟨O, hO, hv₀O, fun x => -ν x, ?_, fun x hx => ?_, fun x hx => ?_, fun v hv hvO => ?_, ?_⟩
    · intro x hx
      exact ((hνs x hx).neg_section)
    · change g.inner x (-ν x) (-ν x) = 1
      rw [map_neg, map_neg, neg_apply, neg_neg]
      exact hunit x hx
    · refine ⟨hx.2, fun w hw => ?_⟩
      have h := (hnormal x hx).2 w hw
      change g.inner x (-ν x) w = 0
      change g.inner x (ν x) w = 0 at h
      rw [map_neg, neg_apply, h, neg_zero]
    · change v.snd = g.inner v.proj v.snd (-ν v.proj) • (-ν v.proj)
      rw [map_neg, neg_smul_neg]
      exact hlineν v hv hvO
    · change -ν v₀.proj = v₀.snd
      rw [hva, ha1, neg_one_smul]

end DifferentialGeometry.Geometry.FiniteSoul
