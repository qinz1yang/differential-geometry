import DifferentialGeometry.Geometry.Neck.OverlapBand

noncomputable section
open Set DifferentialGeometry
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Operator

namespace Poincare.Geometry.Neck

private abbrev S := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private theorem raw_between_iff_signed (σ u v z : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (horder : σ * u < σ * v) :
    min u v ≤ z ∧ z ≤ max u v ↔ σ * u ≤ σ * z ∧ σ * z ≤ σ * v := by
  rcases hσ with rfl | rfl
  · simp only [one_mul] at horder ⊢
    rw [min_eq_left horder.le, max_eq_right horder.le]
  · have hvu : v ≤ u := by linarith
    rw [min_eq_right hvu, max_eq_left hvu]
    simp only [neg_one_mul]
    constructor <;> rintro ⟨h₀, h₁⟩ <;> constructor <;> linarith only [h₀, h₁]

theorem cylindricalChart.exists_raw_graph_band_of_gradient_close
    {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    (C₀ C₁ : cylindricalChart J (M := M)) (g : SmoothRiemannianMetric J M)
    (a b : ℝ) (hab : a < b)
    (hcollar : ∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc a b,
      (x.1, (x.2 : ℝ)) ∈ C₀.domain)
    (htarget : ∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc a b,
      (C₀.chart ⟨(x.1, (x.2 : ℝ)), hcollar x⟩ : M) ∈ C₁.target)
    {U : Set C₁.domain} (ε : ℝ) (hε : ε < 1) (hsmall : C₁.metricCloseOn g ε U)
    (hU : ∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc a b,
      C₁.chart.symm ⟨(C₀.chart ⟨(x.1, (x.2 : ℝ)), hcollar x⟩ : M), htarget x⟩ ∈ U)
    (σ c δ B : ℝ) (hσ : σ = 1 ∨ σ = -1) (hδ : δ * Real.sqrt (1 + ε) < 1)
    (hgrad : ∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc a b,
      let y : M := C₀.chart ⟨(x.1, (x.2 : ℝ)), hcollar x⟩
      Real.sqrt (g.inner y (gradFun g C₀.axial y - σ • gradFun g C₁.axial y)
        (gradFun g C₀.axial y - σ • gradFun g C₁.axial y)) ≤ δ)
    (hvalue : ∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc a b,
      let y : M := C₀.chart ⟨(x.1, (x.2 : ℝ)), hcollar x⟩
      |C₀.axial y - σ * C₁.axial y - c| ≤ B)
    (hsep : 2 * B < (Real.sqrt C₀.scale)⁻¹ * (b - a)) :
    ∃ u v : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ,
      Continuous u ∧ Continuous v ∧ (∀ p, σ * u p < σ * v p) ∧
      ∃ hu : ∀ p, (p, u p) ∈ C₁.domain,
      ∃ hv : ∀ p, (p, v p) ∈ C₁.domain,
        range (fun p ↦ (C₁.chart ⟨(p, u p), hu p⟩ : M)) =
          range (fun p ↦ (C₀.chart ⟨(p, a), hcollar (p, ⟨a, le_rfl, hab.le⟩)⟩ : M)) ∧
        range (fun p ↦ (C₁.chart ⟨(p, v p), hv p⟩ : M)) =
          range (fun p ↦ (C₀.chart ⟨(p, b), hcollar (p, ⟨b, hab.le, le_rfl⟩)⟩ : M)) ∧
        let A := {x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ |
          min (u x.1) (v x.1) ≤ x.2 ∧ x.2 ≤ max (u x.1) (v x.1)}
        A ⊆ C₁.domain ∧
        range (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc a b ↦
          (C₀.chart ⟨(x.1, (x.2 : ℝ)), hcollar x⟩ : M)) =
            C₁.region ((Subtype.val : C₁.domain →
              Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) ⁻¹' A) := by
  let ψ : S × Icc a b → S × ℝ := fun x ↦
    (C₁.chart.symm ⟨(C₀.chart ⟨(x.1, (x.2 : ℝ)), hcollar x⟩ : M), htarget x⟩ : S × ℝ)
  let s : ℝ := (Real.sqrt C₁.scale)⁻¹
  have hs : 0 < s := inv_pos.mpr (Real.sqrt_pos.mpr C₁.scale_pos)
  let aligned : ℝ → ℝ := fun z ↦ σ * (s * z) + c
  let raw : ℝ → ℝ := fun z ↦ σ * (z - c) / s
  have har (z : ℝ) : aligned (raw z) = z := by
    dsimp [aligned, raw]
    rcases hσ with hσ | hσ <;> rw [hσ] <;> field_simp <;> ring
  have hra (z : ℝ) : raw (aligned z) = z := by
    dsimp [aligned, raw]
    rcases hσ with hσ | hσ <;> rw [hσ] <;> field_simp <;> ring
  have haligned : Function.Injective aligned := by
    intro x y hxy
    simpa only [hra] using congrArg raw hxy
  let e : S × Icc a b → S × ℝ := fun x ↦ ((ψ x).1, aligned (ψ x).2)
  obtain ⟨G, hgraph, hmono, hrange, hsub⟩ :=
    C₀.exists_ordered_graph_band_of_gradient_close C₁ g a b hab.le hcollar htarget
      ε hε hsmall hU σ c δ B hσ hδ hgrad hvalue hsep
  let lo : Icc a b := ⟨a, le_rfl, hab.le⟩
  let hi : Icc a b := ⟨b, hab.le, le_rfl⟩
  change range e = {y | G (y.1, lo) ≤ y.2 ∧ y.2 ≤ G (y.1, hi)} at hrange
  change (∀ x, e x = ((e x).1, G ((e x).1, x.2))) at hgraph
  change (∀ s t : Icc a b, e '' ((univ : Set S) ×ˢ Icc s t) =
    {y | G (y.1, s) ≤ y.2 ∧ y.2 ≤ G (y.1, t)}) at hsub
  let R : S × Icc a b → ℝ := fun x ↦ raw (G x)
  let u : S → ℝ := fun p ↦ R (p, lo)
  let v : S → ℝ := fun p ↦ R (p, hi)
  have hraw : Continuous raw := (continuous_const.mul (continuous_id.sub continuous_const)).div_const s
  have hucont : Continuous u := hraw.comp (G.continuous.comp (continuous_id.prodMk continuous_const))
  have hvcont : Continuous v := hraw.comp (G.continuous.comp (continuous_id.prodMk continuous_const))
  have hau (p : S) : aligned (u p) = G (p, lo) := har _
  have hav (p : S) : aligned (v p) = G (p, hi) := har _
  have horder (p : S) : σ * u p < σ * v p := by
    have hlt := hmono p (show lo < hi from hab)
    have hu' := hau p
    have hv' := hav p
    apply (mul_lt_mul_iff_right₀ hs).mp
    dsimp [aligned] at hu' hv'
    nlinarith only [hlt, hu', hv']
  have hbetween (p : S) (z : ℝ) :
      min (u p) (v p) ≤ z ∧ z ≤ max (u p) (v p) ↔
        G (p, lo) ≤ aligned z ∧ aligned z ≤ G (p, hi) := by
    rw [raw_between_iff_signed σ (u p) (v p) z hσ (horder p)]
    have hu' := hau p
    have hv' := hav p
    dsimp [aligned] at hu' hv' ⊢
    constructor
    · rintro ⟨hz₀, hz₁⟩
      have h₀ := mul_le_mul_of_nonneg_left hz₀ hs.le
      have h₁ := mul_le_mul_of_nonneg_left hz₁ hs.le
      constructor <;> nlinarith only [h₀, h₁, hu', hv']
    · rintro ⟨hz₀, hz₁⟩
      constructor <;> apply (mul_le_mul_iff_right₀ hs).mp <;>
        nlinarith only [hz₀, hz₁, hu', hv']
  let A : Set (S × ℝ) := {x | min (u x.1) (v x.1) ≤ x.2 ∧ x.2 ≤ max (u x.1) (v x.1)}
  have hrawrange : range ψ = A := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      apply (hbetween _ _).mpr
      have hx : e x ∈ range e := ⟨x, rfl⟩
      rw [hrange] at hx
      exact hx
    · intro hy
      have hey : (y.1, aligned y.2) ∈ range e :=
        hrange.symm ▸ (hbetween y.1 y.2).mp hy
      obtain ⟨x, hx⟩ := hey
      have hfirst := congrArg Prod.fst hx
      have hsecond := congrArg Prod.snd hx
      exact ⟨x, Prod.ext hfirst (haligned hsecond)⟩
  have hdom (x : S × Icc a b) : ψ x ∈ C₁.domain :=
    (C₁.chart.symm ⟨(C₀.chart ⟨(x.1, (x.2 : ℝ)), hcollar x⟩ : M), htarget x⟩).property
  have hA : A ⊆ C₁.domain := by
    intro y hy
    obtain ⟨x, rfl⟩ := hrawrange.symm ▸ hy
    exact hdom x
  have hpoint (p : S) (t : Icc a b) : ∃ q : S, ψ (q, t) = (p, R (p, t)) := by
    have hy : (p, G (p, t)) ∈ {y | G (y.1, t) ≤ y.2 ∧ y.2 ≤ G (y.1, t)} := ⟨le_rfl, le_rfl⟩
    rw [← hsub t t] at hy
    obtain ⟨x, hx, he⟩ := hy
    have hxt : x.2 = t := le_antisymm hx.2.2 hx.2.1
    have hxψ : ψ x = (p, R (p, t)) := by
      have hfirst := congrArg Prod.fst he
      have hsecond := congrArg Prod.snd he
      exact Prod.ext hfirst ((hra _).symm.trans (congrArg raw hsecond))
    refine ⟨x.1, ?_⟩
    have hxt' : (x.1, t) = x := Prod.ext rfl hxt.symm
    rw [hxt']
    exact hxψ
  have hRdom (p : S) (t : Icc a b) : (p, R (p, t)) ∈ C₁.domain := by
    obtain ⟨q, hq⟩ := hpoint p t
    exact hq ▸ hdom (q, t)
  have hcomm (x : S × Icc a b) :
      (C₁.chart ⟨ψ x, hdom x⟩ : M) =
        (C₀.chart ⟨(x.1, (x.2 : ℝ)), hcollar x⟩ : M) := by
    exact congrArg Subtype.val (C₁.chart.apply_symm_apply
      ⟨(C₀.chart ⟨(x.1, (x.2 : ℝ)), hcollar x⟩ : M), htarget x⟩)
  have hfaces (t : Icc a b) :
      range (fun p ↦ (C₁.chart ⟨(p, R (p, t)), hRdom p t⟩ : M)) =
        range (fun p ↦ (C₀.chart ⟨(p, (t : ℝ)), hcollar (p, t)⟩ : M)) := by
    ext y
    constructor
    · rintro ⟨p, rfl⟩
      obtain ⟨q, hq⟩ := hpoint p t
      refine ⟨q, ?_⟩
      exact (hcomm (q, t)).symm.trans
        (congrArg (fun z : C₁.domain ↦ (C₁.chart z : M)) (Subtype.ext hq))
    · rintro ⟨q, rfl⟩
      have hg := congrArg Prod.snd (hgraph (q, t))
      have hψeq : ψ (q, t) = ((ψ (q, t)).1, R ((ψ (q, t)).1, t)) := by
        refine Prod.ext ?_ ?_
        · rfl
        · exact (hra _).symm.trans (congrArg raw hg)
      refine ⟨(ψ (q, t)).1, ?_⟩
      exact (congrArg (fun z : C₁.domain ↦ (C₁.chart z : M))
        (Subtype.ext hψeq)).symm.trans (hcomm (q, t))
  refine ⟨u, v, hucont, hvcont, horder, (fun p ↦ hRdom p lo),
    (fun p ↦ hRdom p hi), hfaces lo, hfaces hi, hA, ?_⟩
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨C₁.chart ⟨ψ x, hdom x⟩, ⟨⟨ψ x, hdom x⟩, ?_, rfl⟩, hcomm x⟩
    change ψ x ∈ A
    rw [← hrawrange]
    exact ⟨x, rfl⟩
  · rintro ⟨z, ⟨w, hw, rfl⟩, rfl⟩
    change (w : S × ℝ) ∈ A at hw
    rw [← hrawrange] at hw
    obtain ⟨x, hx⟩ := hw
    refine ⟨x, ?_⟩
    exact (hcomm x).symm.trans
      (congrArg (fun z : C₁.domain ↦ (C₁.chart z : M)) (Subtype.ext hx))

end Poincare.Geometry.Neck
