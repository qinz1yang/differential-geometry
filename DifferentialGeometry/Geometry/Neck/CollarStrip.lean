import DifferentialGeometry.Geometry.Neck.OverlapBand
import DifferentialGeometry.Geometry.Neck.CrossSectionStrip

noncomputable section
open Set DifferentialGeometry
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Operator

namespace Poincare.Geometry.Neck

private abbrev S := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private theorem between_of_affine_bounds (k c a z b : ℝ) (hk : k ≠ 0)
    (hlo : k * a + c ≤ k * z + c) (hhi : k * z + c ≤ k * b + c) :
    min a b ≤ z ∧ z ≤ max a b := by
  rcases lt_or_gt_of_ne hk with hk | hk
  · have hza : z ≤ a := (mul_le_mul_left_of_neg hk).mp ((add_le_add_iff_right c).mp hlo)
    have hbz : b ≤ z := (mul_le_mul_left_of_neg hk).mp ((add_le_add_iff_right c).mp hhi)
    exact ⟨(min_le_right _ _).trans hbz, hza.trans (le_max_left _ _)⟩
  · have haz : a ≤ z := (mul_le_mul_iff_right₀ hk).mp ((add_le_add_iff_right c).mp hlo)
    have hzb : z ≤ b := (mul_le_mul_iff_right₀ hk).mp ((add_le_add_iff_right c).mp hhi)
    exact ⟨(min_le_left _ _).trans haz, hzb.trans (le_max_right _ _)⟩

theorem cylindricalChart.exists_strip_containing_full_collar_of_gradient_close
    {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    (C₀ C₁ : cylindricalChart J (M := M)) (g : SmoothRiemannianMetric J M)
    (a b t₁ l r : ℝ) (hab : a ≤ b)
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
    (hsep : 2 * B < (Real.sqrt C₀.scale)⁻¹ * (b - a))
    (htrunc : ∀ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      ∀ t ∈ Icc l r, (p, t) ∈ C₁.domain)
    (ht₁ : t₁ ∈ Icc l r)
    (hcoord : ∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc a b,
      ((C₁.chart.symm ⟨(C₀.chart ⟨(x.1, (x.2 : ℝ)), hcollar x⟩ : M), htarget x⟩ :
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ)).2 ∈ Icc l r)
    (τ : ℝ) (hτ : τ = 1 ∨ τ = -1)
    (hother : ∀ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
      let t : Icc a b := if τ = 1 then ⟨b, hab, le_rfl⟩ else ⟨a, le_rfl, hab⟩
      (τ * σ) * ((C₁.chart.symm
        ⟨(C₀.chart ⟨(p, (t : ℝ)), hcollar (p, t)⟩ : M), htarget (p, t)⟩ :
          Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ)).2 < (τ * σ) * t₁) :
    let t₀ : Icc a b := if τ = 1 then ⟨a, le_rfl, hab⟩ else ⟨b, hab, le_rfl⟩
    ∃ (η : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₘ⟮𝓡 2, 𝓡 2⟯
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
      (h : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ),
      ContMDiff (𝓡 2) 𝓘(ℝ) ∞ h ∧
      ∃ hmem : ∀ p, (p, h p) ∈ C₁.domain,
        (∀ p, (C₁.chart ⟨(p, h p), hmem p⟩ : M) =
          (C₀.chart ⟨(η p, (t₀ : ℝ)), hcollar (η p, t₀)⟩ : M)) ∧
        (∀ p, |(Real.sqrt C₀.scale)⁻¹ * (t₀ : ℝ) -
          σ * ((Real.sqrt C₁.scale)⁻¹ * h p) - c| ≤ B) ∧
        let A := {x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ |
          min (h x.1) t₁ ≤ x.2 ∧ x.2 ≤ max (h x.1) t₁}
        A ⊆ C₁.domain ∧
        ∃ D : Set M, D = C₁.region ((Subtype.val : C₁.domain →
          Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) ⁻¹' A) ∧
          IsCompact D ∧ closure (interior D) = D ∧ IsPreconnected (interior D) ∧
          frontier D =
            range (fun p ↦ (C₀.chart ⟨(p, (t₀ : ℝ)), hcollar (p, t₀)⟩ : M)) ∪
            range (fun p ↦ (C₁.chart ⟨(p, t₁), htrunc p t₁ ht₁⟩ : M)) ∧
          D ⊆ C₁.region ((Subtype.val : C₁.domain →
            Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) ⁻¹'
              ((univ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) ×ˢ Icc l r)) ∧
          range (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc a b ↦
            (C₀.chart ⟨(x.1, (x.2 : ℝ)), hcollar x⟩ : M)) ⊆ D := by
  classical
  let t₀ : Icc a b := if τ = 1 then ⟨a, le_rfl, hab⟩ else ⟨b, hab, le_rfl⟩
  let t₂ : Icc a b := if τ = 1 then ⟨b, hab, le_rfl⟩ else ⟨a, le_rfl, hab⟩
  let ψ : S × Icc a b → S × ℝ := fun x ↦
    (C₁.chart.symm ⟨(C₀.chart ⟨(x.1, (x.2 : ℝ)), hcollar x⟩ : M), htarget x⟩ : S × ℝ)
  let v : ℝ → ℝ := fun z ↦ σ * ((Real.sqrt C₁.scale)⁻¹ * z) + c
  let e : S × Icc a b → S × ℝ := fun x ↦ ((ψ x).1, v (ψ x).2)
  obtain ⟨H, hgraph, _, hrange, hsub⟩ :=
    C₀.exists_ordered_graph_band_of_gradient_close C₁ g a b hab hcollar htarget
      ε hε hsmall hU σ c δ B hσ hδ hgrad hvalue hsep
  have hendpoint (p : S) (t : Icc a b) : ∃ q : S, e (q, t) = (p, H (p, t)) := by
    have hy : (p, H (p, t)) ∈ {y | H (y.1, t) ≤ y.2 ∧ y.2 ≤ H (y.1, t)} :=
      ⟨le_rfl, le_rfl⟩
    rw [← hsub t t] at hy
    rcases hy with ⟨x, hx, hxe⟩
    have hxt : x.2 = t := le_antisymm hx.2.2 hx.2.1
    exact ⟨x.1, by simpa only [hxt] using hxe⟩
  have hs : 0 < (Real.sqrt C₁.scale)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr C₁.scale_pos)
  have hotherBound (p : S) : τ * H (p, t₂) < τ * v t₁ := by
    obtain ⟨q, hq⟩ := hendpoint p t₂
    have hq₂ : v (ψ (q, t₂)).2 = H (p, t₂) := congrArg Prod.snd hq
    rw [← hq₂]
    have hscaled := mul_lt_mul_of_pos_left (hother q) hs
    change (Real.sqrt C₁.scale)⁻¹ * ((τ * σ) * (ψ (q, t₂)).2) <
      (Real.sqrt C₁.scale)⁻¹ * ((τ * σ) * t₁) at hscaled
    dsimp only [v]
    nlinarith only [hscaled]
  have hbetween (x : S × Icc a b) :
      τ * H ((ψ x).1, t₀) ≤ τ * v (ψ x).2 ∧
        τ * v (ψ x).2 ≤ τ * H ((ψ x).1, t₂) := by
    have hx : e x ∈ range e := ⟨x, rfl⟩
    rw [hrange] at hx
    change H ((ψ x).1, ⟨a, le_rfl, hab⟩) ≤ v (ψ x).2 ∧
      v (ψ x).2 ≤ H ((ψ x).1, ⟨b, hab, le_rfl⟩) at hx
    rcases hτ with hτ | hτ
    · simpa only [t₀, t₂, hτ, ite_true, one_mul] using hx
    · simpa only [t₀, t₂, hτ, show (-1 : ℝ) ≠ 1 by norm_num, if_false, neg_one_mul]
        using And.intro (neg_le_neg hx.2) (neg_le_neg hx.1)
  have hne (p : S) : (ψ (p, t₀)).2 ≠ t₁ := by
    have hlt := (hbetween (p, t₀)).2.trans_lt (hotherBound (ψ (p, t₀)).1)
    intro heq
    rw [heq] at hlt
    exact lt_irrefl _ hlt
  obtain ⟨η, h, hh, hmem, heq, herr, hAO, D, hD, hcompact, hreg, hconn, hfront, hDtrunc⟩ :=
    C₀.exists_strip_of_full_cross_sections_and_gradient_close C₁ g (t₀ : ℝ) t₁ l r
      (fun p ↦ hcollar (p, t₀)) (fun p ↦ htarget (p, t₀)) ε hε hsmall
      (fun p ↦ hU (p, t₀)) σ c δ B hσ hδ (fun p ↦ hgrad (p, t₀))
      (fun p ↦ hvalue (p, t₀)) htrunc ht₁ (fun p ↦ hcoord (p, t₀)) hne
  have hinverse (p : S) : ψ (η p, t₀) = (p, h p) := by
    have hv : (⟨(C₀.chart ⟨(η p, (t₀ : ℝ)), hcollar (η p, t₀)⟩ : M),
        htarget (η p, t₀)⟩ : C₁.target) = C₁.chart ⟨(p, h p), hmem p⟩ :=
      Subtype.ext (heq p).symm
    change (C₁.chart.symm _ : S × ℝ) = _
    rw [hv, C₁.chart.symm_apply_apply]
  have hHouter (p : S) : H (p, t₀) = v (h p) := by
    have hp := congrArg Prod.snd (hgraph (η p, t₀))
    change v (ψ (η p, t₀)).2 = H ((ψ (η p, t₀)).1, t₀) at hp
    rw [hinverse p] at hp
    exact hp.symm
  have hband (x : S × Icc a b) :
      min (h (ψ x).1) t₁ ≤ (ψ x).2 ∧ (ψ x).2 ≤ max (h (ψ x).1) t₁ := by
    have hlo := (hbetween x).1
    rw [hHouter] at hlo
    have hhi := ((hbetween x).2.trans_lt (hotherBound (ψ x).1)).le
    have hτ₀ : τ ≠ 0 := by rcases hτ with rfl | rfl <;> norm_num
    have hσ₀ : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
    apply between_of_affine_bounds (τ * σ * (Real.sqrt C₁.scale)⁻¹) (τ * c)
      _ _ _ (mul_ne_zero (mul_ne_zero hτ₀ hσ₀) hs.ne')
    · simpa only [v, mul_add, mul_assoc] using hlo
    · simpa only [v, mul_add, mul_assoc] using hhi
  refine ⟨η, h, hh, hmem, heq, herr, hAO, D, hD, hcompact, hreg, hconn,
    hfront, hDtrunc, ?_⟩
  rintro y ⟨x, rfl⟩
  rw [hD]
  exact ⟨⟨(C₀.chart ⟨(x.1, (x.2 : ℝ)), hcollar x⟩ : M), htarget x⟩,
    ⟨C₁.chart.symm ⟨(C₀.chart ⟨(x.1, (x.2 : ℝ)), hcollar x⟩ : M), htarget x⟩,
      hband x, C₁.chart.apply_symm_apply _⟩, rfl⟩

end Poincare.Geometry.Neck
