import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.SaddleSlabProof.Glue

/-!
# The glued maps are inverse to each other

Lane RG03c. Let `ψ` be an increasing level matching, a translation near the critical values, with
inverse `ψ'`, and let `h`, `h'` map the lower levels to each other, inverse to each other and
matching the attaching arcs. For a point `x` of the slab `f ⁻¹' [a, b]`, `glue_spec` gives
`f' (glue x) = ψ (f x)` and `glue' (glue x) = x` for the glued map `glue'` built from `ψ'`, `h'`.
The three regions are treated separately; in the lower region the upward flow line from `h z`
avoids the box, otherwise `z = h' (h z)` would be the foot of an attaching arc.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Topology DifferentialGeometry.Topology.Morse
open DifferentialGeometry.Topology.Morse.CellAttachment (morseNorm morseNormalForm)

namespace GC.Seifert.SaddleSlabProof

variable {H H' : Type} [TopologicalSpace H] [TopologicalSpace H'] {M M' : Type*}
  [TopologicalSpace M] [ChartedSpace H M] [TopologicalSpace M'] [ChartedSpace H' M']
  {I : ModelWithCorners ℝ (MorseModel 2) H} {I' : ModelWithCorners ℝ (MorseModel 2) H'}
  [IsManifold I ∞ M] [IsManifold I' ∞ M'] {f : M → ℝ} {f' : M' → ℝ} {a b a' b' : ℝ} {p : M}
  {p' : M'} [T2Space M] [T2Space M'] [I.Boundaryless] [I'.Boundaryless]

theorem f_π_of_lowDomain (D : GradientLikeStrip I f a b {p}) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    {x : M} (hx : f x ∈ Icc a b) (hIII : x ∈ lowDomain D) : f (D.π a x) = a := by
  have h := GradientLikeStrip.f_flow_eq_sub_of_avoid_uIcc (D := D) hf (x := x) (T := f x - a) hx
    ⟨by linarith, by linarith [hx.1, hx.2]⟩
    (fun v hv q hq hvq => by
      obtain rfl := Finset.mem_singleton.mp hq
      exact hIII v hv (smallBall_subset_boxSet D hq hvq))
    (f x - a) right_mem_uIcc
  change f (D.flow (f x - a) x) = a
  rw [h]
  ring

theorem glue_spec (D : GradientLikeStrip I f a b {p})
    (D' : GradientLikeStrip I' f' a' b' {p'}) (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f)
    (hf' : ContMDiff I' 𝓘(ℝ, ℝ) ∞ f')
    (hk : (ch D).k = 1) (hk' : (ch D').k = 1) (hr : (ch D').r₀ = (ch D).r₀)
    (hrm : 8 * (ch D).r₀ ≤ rmD D) (hrm' : 8 * (ch D').r₀ ≤ rmD D')
    (ha : a < f p - 2 * eps D) (hb : f p + 2 * eps D < b)
    (ha' : a' < f' p' - 2 * eps D) (hb' : f' p' + 2 * eps D < b')
    {ψ ψ' : ℝ → ℝ} (hψm : StrictMono ψ) (hψa : ψ a = a') (hψb : ψ b = b')
    (hψ : ∀ t ∈ Icc (f p - 2 * eps D) (f p + 2 * eps D), ψ t = t - f p + f' p')
    (hψ'ψ : ∀ t, ψ' (ψ t) = t)
    (hψ' : ∀ t ∈ Icc (f' p' - 2 * eps D) (f' p' + 2 * eps D), ψ' t = t - f' p' + f p)
    {h : M → M'} {h' : M' → M} (hL : ∀ z, f z = a → f' (h z) = a')
    (hh : ∀ z, f z = a → h' (h z) = z)
    (hH : ∀ σ t, σ ^ 2 = 1 → t ^ 2 ≤ 2 * eps D → h (arc D σ t) = arc D' σ t)
    (hH' : ∀ σ t, σ ^ 2 = 1 → t ^ 2 ≤ 2 * eps D → h' (arc D' σ t) = arc D σ t)
    {x : M} (hx : f x ∈ Icc a b) :
    f' (glue D D' ψ h x) = ψ (f x) ∧ glue D' D ψ' h' (glue D D' ψ h x) = x := by
  have hε := eps_pos D
  have hεr : (ch D).r₀ ^ 2 = eps D := rfl
  have hε' := eps_eq D D' hr
  have hr' : (ch D).r₀ = (ch D').r₀ := hr.symm
  have hψ'' : ∀ t ∈ Icc (f' p' - 2 * eps D') (f' p' + 2 * eps D'), ψ' t = t - f' p' + f p := by
    rw [hε']
    exact hψ'
  have hH'' : ∀ σ t, σ ^ 2 = 1 → t ^ 2 ≤ 2 * eps D' → h' (arc D' σ t) = arc D σ t := by
    rw [hε']
    exact hH'
  have hψI : ψ (f x) ∈ Icc a' b' :=
    ⟨hψa ▸ hψm.monotone hx.1, hψb ▸ hψm.monotone hx.2⟩
  rcases mem_regions D hf hk hrm (by linarith) (by linarith) hx with hI | hII | hIII
  · obtain ⟨y, hy, rfl⟩ := hI
    have hyb := bounds_of_openBox hy
    have hyb' : |saddleQ y| + |saddleK y| < 8 * eps D' := by rw [hε']; exact hyb
    have hQ := abs_lt.mp hy.1
    have hF : glue D D' ψ h ((ch D).χ y) = (ch D').χ y := by
      rw [glue_eq_mapI D D' ψ h ⟨y, hy, rfl⟩]
      unfold mapI
      rw [chart_symm_chart D hrm hyb]
    rw [hF]
    refine ⟨?_, ?_⟩
    · rw [f_chart_of_bounds D' hk' hrm' hyb', f_chart_of_bounds D hk hrm hyb,
        hψ _ ⟨by linarith, by linarith⟩]
      ring
    · have hy' : y ∈ openBox (2 * eps D') := by rw [hε']; exact hy
      rw [glue_eq_mapI D' D ψ' h' ⟨y, hy', rfl⟩]
      unfold mapI
      rw [chart_symm_chart D' hrm' hyb']
  · obtain ⟨w, hw, hwq, hwx⟩ := regII_data D hf hk hrm hb ha hx hII
    have hwb := bounds_of_topBox hε hw
    have hwb' : |saddleQ w| + |saddleK w| < 8 * eps D' := by rw [hε']; exact hwb
    have hfx := hII.1
    have hψx : f' p' + eps D / 2 < ψ (f x) := by
      have h1 := hψm hfx
      rwa [hψ _ ⟨by linarith, by linarith⟩, show f p + eps D / 2 - f p + f' p' =
        f' p' + eps D / 2 by ring] at h1
    set q := (ch D').χ w with hq
    have hfq : f' q = f' p' + eps D := by
      rw [hq, f_chart_of_bounds D' hk' hrm' hwb', hwq]
    have hF : glue D D' ψ h x = D'.flow (-(ψ (f x) - (f' p' + eps D))) q := by
      rw [glue_eq_mapII D D' hk hk' hr hrm hrm' hψ h hII]
      unfold mapII mapI
      rw [hwx, chart_symm_chart D hrm hwb, hε']
    have hlev : f' (glue D D' ψ h x) = ψ (f x) := by
      have h1 := f_flow_to_level D' hf' hk' (x := q) (ℓ := ψ (f x))
        ⟨by rw [hfq]; linarith, by rw [hfq]; linarith⟩ hψI
        (by rw [hfq, hε']; linarith) (by rw [hε']; linarith)
        (f' q - ψ (f x)) right_mem_uIcc
      rw [hF, show -(ψ (f x) - (f' p' + eps D)) = f' q - ψ (f x) by rw [hfq]; ring, h1]
      ring
    refine ⟨hlev, ?_⟩
    have hback : D'.flow (f' (glue D D' ψ h x) - (f' p' + eps D')) (glue D D' ψ h x) = q := by
      rw [hlev, hF, GradientLikeStrip.flow_flow, hε', neg_add_cancel,
        GradientLikeStrip.flow_zero]
    have hII' : glue D D' ψ h x ∈ regII D' :=
      ⟨by rw [hlev, hε']; exact hψx, by rw [hback, hε']; exact ⟨w, hw, rfl⟩⟩
    have hψ'' : ∀ t ∈ Icc (f' p' - 2 * eps D') (f' p' + 2 * eps D'), ψ' t = t - f' p' + f p :=
      hψ''
    rw [glue_eq_mapII D' D hk' hk hr' hrm' hrm hψ'' h' hII']
    unfold mapII mapI
    rw [hback, hq, chart_symm_chart D' hrm' hwb', hlev, hψ'ψ, ← hwx, ← eps_eq D D' hr,
      GradientLikeStrip.flow_neg_flow]
  · set z := D.π a x with hz
    have hfz : f z = a := f_π_of_lowDomain D hf hx hIII
    have hxz : x = D.flow (-(f x - a)) z := by
      rw [hz]
      exact (GradientLikeStrip.flow_neg_flow D x (f x - a)).symm
    set s' := ψ (f x) - a' with hs'
    have hs'0 : 0 ≤ s' := by linarith [hψI.1]
    have hfhz : f' (h z) = a' := hL z hfz
    have havoid : ∀ u ∈ Icc 0 s', D'.flow (-u) (h z) ∉ boxSet D' := by
      intro u hu hmem
      obtain ⟨σ, t, hσ, ht, hzt, hs⟩ := eq_arc_of_flow_mem_boxSet D' hf' hk' hrm'
        (by rw [hε']; linarith) hfhz (s := s') (by linarith [hψI.2]) hu hmem
      have ht2 : t ^ 2 ≤ 2 * eps D' := sq_le_of_abs_saddleK_footPt (eps_pos D') hσ
        (ht.trans (by linarith [eps_pos D']))
      have hzarc : z = arc D σ t := by
        rw [← hh z hfz, hzt, hH'' σ t hσ ht2]
      have hfx' : f p - eps D ≤ f x := by
        by_contra hcon
        push Not at hcon
        have h1 := hψm hcon
        rw [hψ (f p - eps D) ⟨by linarith, by linarith⟩] at h1
        rw [hε'] at hs
        linarith
      apply hIII (f x - (f p - eps D))
      · rw [uIcc_of_le (by linarith [hx.1])]
        exact ⟨by linarith, by linarith⟩
      · have hfl : D.flow (-(f p - eps D - a)) z = D.flow (f x - (f p - eps D)) x := by
          change D.flow _ (D.flow (f x - a) x) = _
          rw [GradientLikeStrip.flow_flow]
          congr 1
          ring
        rw [← hfl, hzarc]
        unfold arc
        rw [GradientLikeStrip.flow_neg_flow]
        have ht2' : t ^ 2 ≤ 2 * eps D := by rw [← hε']; exact ht2
        refine ⟨footPt (eps D) σ t, ⟨?_, ?_⟩, rfl⟩
        · rw [saddleQ_footPt hε.le hσ, abs_neg, abs_of_pos hε, hεr]
        · rw [hεr, ← hε']
          exact ht
    have hunit : ∀ u ∈ Icc 0 s', f' (D'.flow (-u) (h z)) = a' + u := by
      intro u hu
      have h1 := GradientLikeStrip.f_flow_eq_sub_of_avoid_uIcc (D := D') hf' (x := h z)
        (T := -s') ⟨hfhz.ge, by rw [hfhz]; linarith [hψI.2, hs'0]⟩
        ⟨by linarith, by linarith [hψI.2]⟩
        (fun v hv q hq hvq => by
          obtain rfl := Finset.mem_singleton.mp hq
          rw [uIcc_of_ge (by linarith)] at hv
          refine havoid (-v) ⟨by linarith [hv.2], by linarith [hv.1]⟩ ?_
          rw [neg_neg]
          exact smallBall_subset_boxSet D' hq hvq)
        (-u) (by rw [uIcc_of_ge (by linarith)]; exact ⟨by linarith [hu.2], by linarith [hu.1]⟩)
      rw [h1, hfhz]
      ring
    have hF : glue D D' ψ h x = D'.flow (-s') (h z) := by
      rw [glue_eq_mapIII D D' hf hk hk' hr hrm hrm' ha hb hψ hH hx hIII]
      rfl
    have hlev : f' (glue D D' ψ h x) = ψ (f x) := by
      rw [hF, hunit s' ⟨hs'0, le_rfl⟩, hs']
      ring
    refine ⟨hlev, ?_⟩
    have hlow' : glue D D' ψ h x ∈ lowDomain D' := by
      intro u hu
      rw [hlev, ← hs', uIcc_of_le hs'0] at hu
      rw [hF, GradientLikeStrip.flow_flow, show -s' + u = -(s' - u) by ring]
      exact havoid (s' - u) ⟨by linarith [hu.2], by linarith [hu.1]⟩
    have hx' : f' (glue D D' ψ h x) ∈ Icc a' b' := hlev ▸ hψI
    have ha'' : a' < f' p' - 2 * eps D' := by rw [hε']; exact ha'
    have hb'' : f' p' + 2 * eps D' < b' := by rw [hε']; exact hb'
    rw [glue_eq_mapIII D' D hf' hk' hk hr' hrm' hrm ha'' hb'' hψ'' hH'' hx' hlow']
    unfold mapIII
    have hπ' : D'.π a' (glue D D' ψ h x) = h z := by
      change D'.flow (f' (glue D D' ψ h x) - a') (glue D D' ψ h x) = h z
      rw [hlev, ← hs', hF, GradientLikeStrip.flow_flow, neg_add_cancel,
        GradientLikeStrip.flow_zero]
    rw [hπ', hh z hfz, hlev, hψ'ψ, ← hxz]

end GC.Seifert.SaddleSlabProof
