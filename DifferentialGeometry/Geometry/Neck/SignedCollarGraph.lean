import DifferentialGeometry.Geometry.Neck.CollarGraphBand

noncomputable section
open Set DifferentialGeometry
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Operator

namespace Poincare.Geometry.Neck

private abbrev S := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private theorem between_signed (σ u v z : ℝ) (hσ : σ = 1 ∨ σ = -1)
    (horder : σ * u < σ * v) :
    min u v ≤ z ∧ z ≤ max u v ↔ σ * u ≤ σ * z ∧ σ * z ≤ σ * v := by
  rcases hσ with rfl | rfl
  · simp only [one_mul] at horder ⊢
    rw [min_eq_left horder.le, max_eq_right horder.le]
  · have hvu : v ≤ u := by linarith
    rw [min_eq_right hvu, max_eq_left hvu]
    simp only [neg_one_mul]
    constructor <;> rintro ⟨h₀, h₁⟩ <;> constructor <;> linarith only [h₀, h₁]

theorem cylindricalChart.exists_signed_graph_band_of_gradient_close
    {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    (C₀ C₁ : cylindricalChart J (M := M)) (g : SmoothRiemannianMetric J M)
    (τ₀ τ₁ : ℝ) (hτ₀ : τ₀ = 1 ∨ τ₀ = -1) (hτ₁ : τ₁ = 1 ∨ τ₁ = -1)
    (l r : ℝ) (hlr : l < r)
    (hcollar : ∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc l r,
      (x.1, τ₀ * (x.2 : ℝ)) ∈ C₀.domain)
    (htarget : ∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc l r,
      (C₀.chart ⟨(x.1, τ₀ * (x.2 : ℝ)), hcollar x⟩ : M) ∈ C₁.target)
    {U : Set C₁.domain} (ε : ℝ) (hε : ε < 1) (hsmall : C₁.metricCloseOn g ε U)
    (hU : ∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc l r,
      C₁.chart.symm ⟨(C₀.chart ⟨(x.1, τ₀ * (x.2 : ℝ)), hcollar x⟩ : M), htarget x⟩ ∈ U)
    (c δ B : ℝ) (hδ : δ * Real.sqrt (1 + ε) < 1)
    (hgrad : ∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc l r,
      let y : M := C₀.chart ⟨(x.1, τ₀ * (x.2 : ℝ)), hcollar x⟩
      Real.sqrt (g.inner y (gradFun g C₀.axial y - (τ₀ * τ₁) • gradFun g C₁.axial y)
        (gradFun g C₀.axial y - (τ₀ * τ₁) • gradFun g C₁.axial y)) ≤ δ)
    (hvalue : ∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc l r,
      let y : M := C₀.chart ⟨(x.1, τ₀ * (x.2 : ℝ)), hcollar x⟩
      |C₀.axial y - (τ₀ * τ₁) * C₁.axial y - c| ≤ B)
    (hsep : 2 * B < (Real.sqrt C₀.scale)⁻¹ * (r - l)) :
    ∃ a b : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ,
      Continuous a ∧ Continuous b ∧ (∀ p, a p < b p) ∧
      ∃ ha : ∀ p, (p, τ₁ * a p) ∈ C₁.domain,
      ∃ hb : ∀ p, (p, τ₁ * b p) ∈ C₁.domain,
        range (fun p ↦ (C₁.chart ⟨(p, τ₁ * a p), ha p⟩ : M)) =
          range (fun p ↦ (C₀.chart ⟨(p, τ₀ * l), hcollar (p, ⟨l, le_rfl, hlr.le⟩)⟩ : M)) ∧
        range (fun p ↦ (C₁.chart ⟨(p, τ₁ * b p), hb p⟩ : M)) =
          range (fun p ↦ (C₀.chart ⟨(p, τ₀ * r), hcollar (p, ⟨r, hlr.le, le_rfl⟩)⟩ : M)) ∧
        let A := {x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ |
          a x.1 ≤ τ₁ * x.2 ∧ τ₁ * x.2 ≤ b x.1}
        A ⊆ C₁.domain ∧
        range (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc l r ↦
          (C₀.chart ⟨(x.1, τ₀ * (x.2 : ℝ)), hcollar x⟩ : M)) =
            C₁.region ((Subtype.val : C₁.domain →
              Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) ⁻¹' A) := by
  let L : ℝ := if τ₀ = 1 then l else -r
  let R : ℝ := if τ₀ = 1 then r else -l
  have hneg : (-1 : ℝ) ≠ 1 := by norm_num
  have hLR : L < R := by
    rcases hτ₀ with rfl | rfl
    · simpa only [L, R, if_pos rfl] using hlr
    · simpa only [L, R, if_neg hneg] using neg_lt_neg hlr
  have hsquare₀ : τ₀ * τ₀ = 1 := by rcases hτ₀ with rfl | rfl <;> norm_num
  have hsquare₁ : τ₁ * τ₁ = 1 := by rcases hτ₁ with rfl | rfl <;> norm_num
  have hinterval (t : Icc L R) : τ₀ * (t : ℝ) ∈ Icc l r := by
    rcases hτ₀ with rfl | rfl
    · simpa only [L, R, if_pos rfl, one_mul] using t.property
    · have ht : -r ≤ (t : ℝ) ∧ (t : ℝ) ≤ -l := by
        simpa only [L, R, if_neg hneg, mem_Icc] using t.property
      constructor <;> linarith only [ht.1, ht.2]
  let ρ : S × Icc L R → S × Icc l r := fun x ↦ (x.1, ⟨τ₀ * (x.2 : ℝ), hinterval x.2⟩)
  have hpoint (x : S × Icc L R) : (x.1, (x.2 : ℝ)) = ((ρ x).1, τ₀ * ((ρ x).2 : ℝ)) := by
    refine Prod.ext ?_ ?_
    · rfl
    change (x.2 : ℝ) = τ₀ * (τ₀ * (x.2 : ℝ))
    rw [← mul_assoc, hsquare₀, one_mul]
  have hc (x : S × Icc L R) : (x.1, (x.2 : ℝ)) ∈ C₀.domain :=
    hpoint x ▸ hcollar (ρ x)
  let e : S × Icc l r → M := fun x ↦ C₀.chart ⟨(x.1, τ₀ * (x.2 : ℝ)), hcollar x⟩
  have he (x : S × Icc L R) : (C₀.chart ⟨(x.1, (x.2 : ℝ)), hc x⟩ : M) = e (ρ x) :=
    congrArg (fun z : C₀.domain ↦ (C₀.chart z : M)) (Subtype.ext (hpoint x))
  have ht (x : S × Icc L R) : (C₀.chart ⟨(x.1, (x.2 : ℝ)), hc x⟩ : M) ∈ C₁.target := by
    rw [he]
    exact htarget (ρ x)
  have hρ : Function.Surjective ρ := by
    intro x
    have hx : τ₀ * (x.2 : ℝ) ∈ Icc L R := by
      have hx := x.2.property
      rcases hτ₀ with rfl | rfl
      · simpa only [L, R, if_pos rfl, one_mul] using hx
      · simp only [L, R, if_neg hneg, mem_Icc]
        constructor <;> linarith only [hx.1, hx.2]
    refine ⟨(x.1, ⟨τ₀ * (x.2 : ℝ), hx⟩), Prod.ext rfl (Subtype.ext ?_)⟩
    change τ₀ * (τ₀ * (x.2 : ℝ)) = (x.2 : ℝ)
    rw [← mul_assoc, hsquare₀, one_mul]
  have herange : range (fun x : S × Icc L R ↦ (C₀.chart ⟨(x.1, (x.2 : ℝ)), hc x⟩ : M)) =
      range e := by
    have hf : (fun x : S × Icc L R ↦ (C₀.chart ⟨(x.1, (x.2 : ℝ)), hc x⟩ : M)) = e ∘ ρ :=
      funext he
    rw [hf, range_comp, hρ.range_eq, image_univ]
  have hσ : τ₀ * τ₁ = 1 ∨ τ₀ * τ₁ = -1 := by
    rcases hτ₀ with rfl | rfl <;> rcases hτ₁ with rfl | rfl <;> norm_num
  have hwidth : R - L = r - l := by
    rcases hτ₀ with rfl | rfl
    · simp only [L, R, if_pos rfl]
    · simp only [L, R, if_neg hneg]
      ring
  obtain ⟨u, v, hucont, hvcont, horder, hu, hv, huface, hvface, hband, hrange⟩ :=
    C₀.exists_raw_graph_band_of_gradient_close C₁ g L R hLR hc ht ε hε hsmall
      (by intro x; simpa only [he] using hU (ρ x))
      (τ₀ * τ₁) c δ B hσ hδ
      (by intro x; dsimp only; rw [he]; exact hgrad (ρ x))
      (by intro x; simpa only [he] using hvalue (ρ x))
      (by rw [hwidth]; exact hsep)
  rw [herange] at hrange
  rcases hτ₀ with rfl | rfl
  · have ha (p : S) : (p, τ₁ * (τ₁ * u p)) ∈ C₁.domain := by
      simpa only [← mul_assoc, hsquare₁, one_mul] using hu p
    have hb (p : S) : (p, τ₁ * (τ₁ * v p)) ∈ C₁.domain := by
      simpa only [← mul_assoc, hsquare₁, one_mul] using hv p
    have hord (p : S) : τ₁ * u p < τ₁ * v p := by simpa only [one_mul] using horder p
    have hset : {x : S × ℝ | τ₁ * u x.1 ≤ τ₁ * x.2 ∧ τ₁ * x.2 ≤ τ₁ * v x.1} =
        {x : S × ℝ | min (u x.1) (v x.1) ≤ x.2 ∧ x.2 ≤ max (u x.1) (v x.1)} := by
      ext x
      exact (between_signed τ₁ _ _ _ hτ₁ (hord x.1)).symm
    refine ⟨fun p ↦ τ₁ * u p, fun p ↦ τ₁ * v p, continuous_const.mul hucont,
      continuous_const.mul hvcont, hord, ha, hb, ?_, ?_, ?_, ?_⟩
    · simpa only [L, if_pos rfl, ← mul_assoc, hsquare₁, one_mul] using huface
    · simpa only [R, if_pos rfl, ← mul_assoc, hsquare₁, one_mul] using hvface
    · simpa only [hset] using hband
    · simpa only [hset] using hrange
  · have ha (p : S) : (p, τ₁ * (τ₁ * v p)) ∈ C₁.domain := by
      simpa only [← mul_assoc, hsquare₁, one_mul] using hv p
    have hb (p : S) : (p, τ₁ * (τ₁ * u p)) ∈ C₁.domain := by
      simpa only [← mul_assoc, hsquare₁, one_mul] using hu p
    have hord (p : S) : τ₁ * v p < τ₁ * u p := by
      have h := horder p
      simp only [neg_mul] at h
      linarith
    have hset : {x : S × ℝ | τ₁ * v x.1 ≤ τ₁ * x.2 ∧ τ₁ * x.2 ≤ τ₁ * u x.1} =
        {x : S × ℝ | min (u x.1) (v x.1) ≤ x.2 ∧ x.2 ≤ max (u x.1) (v x.1)} := by
      ext x
      simpa only [mem_ofPred_eq, min_comm, max_comm] using
        (between_signed τ₁ _ _ _ hτ₁ (hord x.1)).symm
    refine ⟨fun p ↦ τ₁ * v p, fun p ↦ τ₁ * u p, continuous_const.mul hvcont,
      continuous_const.mul hucont, hord, ha, hb, ?_, ?_, ?_, ?_⟩
    · simpa only [R, show (-1 : ℝ) ≠ 1 by norm_num, if_false, ← mul_assoc, hsquare₁,
        one_mul, neg_one_mul] using hvface
    · simpa only [L, show (-1 : ℝ) ≠ 1 by norm_num, if_false, ← mul_assoc, hsquare₁,
        one_mul, neg_one_mul] using huface
    · simpa only [hset] using hband
    · simpa only [hset] using hrange

end Poincare.Geometry.Neck
