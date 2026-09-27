import DifferentialGeometry.Geometry.Neck.CrossSectionGraph
import DifferentialGeometry.Topology.FiberwiseHomeomorph
import DifferentialGeometry.Geometry.Affine.Interval
import DifferentialGeometry.Topology.OrderedCollar

noncomputable section
open Set DifferentialGeometry
open scoped Manifold ContDiff
open DifferentialGeometry.Geometry.Operator

namespace DifferentialGeometry.Geometry.Neck

private abbrev S := Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private theorem transition_properties_of_gradient_close
    {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    (C₀ C₁ : cylindricalChart J (M := M)) (g : SmoothRiemannianMetric J M)
    (a b : ℝ)
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
      |C₀.axial y - σ * C₁.axial y - c| ≤ B) :
    let ψ := fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc a b ↦
      (C₁.chart.symm ⟨(C₀.chart ⟨(x.1, (x.2 : ℝ)), hcollar x⟩ : M), htarget x⟩ :
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ)
    Continuous ψ ∧ Function.Injective ψ ∧
      (∀ t, Function.Bijective (fun p ↦ (ψ (p, t)).1)) ∧
      ∀ x, |(Real.sqrt C₀.scale)⁻¹ * (x.2 : ℝ) -
        (σ * ((Real.sqrt C₁.scale)⁻¹ * (ψ x).2) + c)| ≤ B := by
  let ι : S × Icc a b → C₀.domain := fun x ↦ ⟨(x.1, (x.2 : ℝ)), hcollar x⟩
  have hι : Continuous ι :=
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).subtype_mk _
  let f : S × Icc a b → C₁.target := fun x ↦ ⟨(C₀.chart (ι x) : M), htarget x⟩
  have hf : Continuous f :=
    (continuous_subtype_val.comp (C₀.chart.continuous.comp hι)).subtype_mk _
  let ψ : S × Icc a b → S × ℝ := fun x ↦ (C₁.chart.symm (f x) : S × ℝ)
  have hψ : Continuous ψ := continuous_subtype_val.comp (C₁.chart.symm.continuous.comp hf)
  have hbij (t : Icc a b) : Function.Bijective (fun p : S ↦ (ψ (p, t)).1) := by
    obtain ⟨η, h, -, hmem, heq, -⟩ :=
      C₀.exists_graph_of_full_cross_section_and_gradient_close C₁ g t
        (fun p ↦ hcollar (p, t)) (fun p ↦ htarget (p, t))
        ε hε hsmall (fun p ↦ hU (p, t)) σ c δ B hσ hδ
        (fun p ↦ hgrad (p, t)) (fun p ↦ hvalue (p, t))
    have hright (p : S) : (ψ (η p, t)).1 = p := by
      have hy : f (η p, t) = C₁.chart ⟨(p, h p), hmem p⟩ :=
        Subtype.ext (heq p).symm
      change (C₁.chart.symm (f (η p, t)) : S × ℝ).1 = p
      rw [hy, C₁.chart.symm_apply_apply]
    constructor
    · intro p q hpq
      obtain ⟨p, rfl⟩ := η.surjective p
      obtain ⟨q, rfl⟩ := η.surjective q
      change (ψ (η p, t)).1 = (ψ (η q, t)).1 at hpq
      rw [hright, hright] at hpq
      exact congrArg η hpq
    · intro p
      exact ⟨η p, hright p⟩
  have hψinj : Function.Injective ψ := by
    intro x y hxy
    have hdom : C₁.chart.symm (f x) = C₁.chart.symm (f y) := Subtype.ext hxy
    have hfxy := C₁.chart.symm.injective hdom
    have hval := congrArg Subtype.val hfxy
    have hchart : C₀.chart (ι x) = C₀.chart (ι y) := Subtype.ext hval
    have hprod := congrArg Subtype.val (C₀.chart.injective hchart)
    have hfirst := congrArg Prod.fst hprod
    have hsecond := congrArg Prod.snd hprod
    exact Prod.ext hfirst (Subtype.ext hsecond)
  have hbound (x : S × Icc a b) :
      |(Real.sqrt C₀.scale)⁻¹ * (x.2 : ℝ) - (σ * ((Real.sqrt C₁.scale)⁻¹ * (ψ x).2) + c)| ≤ B := by
    have h := hvalue x
    dsimp only at h
    have h₀ := C₀.axial_chart (ι x)
    have h₁ := C₁.axial_chart (C₁.chart.symm (f x))
    rw [C₁.chart.apply_symm_apply] at h₁
    change C₁.axial (C₀.chart (ι x) : M) = (Real.sqrt C₁.scale)⁻¹ * (ψ x).2 at h₁
    change |C₀.axial (C₀.chart (ι x) : M) - σ * C₁.axial (C₀.chart (ι x) : M) - c| ≤ B at h
    rw [h₀, h₁] at h
    simpa only [sub_sub] using h
  exact ⟨hψ, hψinj, hbij, hbound⟩

theorem cylindricalChart.full_band_subset_transition_range_of_gradient_close
    {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    (C₀ C₁ : cylindricalChart J (M := M)) (g : SmoothRiemannianMetric J M)
    (a b : ℝ) (hab : a ≤ b)
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
      |C₀.axial y - σ * C₁.axial y - c| ≤ B) :
    (univ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) ×ˢ
      ((fun z : ℝ ↦ σ * ((Real.sqrt C₁.scale)⁻¹ * z) + c) ⁻¹'
        Icc ((Real.sqrt C₀.scale)⁻¹ * a + B) ((Real.sqrt C₀.scale)⁻¹ * b - B)) ⊆
      range (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc a b ↦
        (C₁.chart.symm ⟨(C₀.chart ⟨(x.1, (x.2 : ℝ)), hcollar x⟩ : M), htarget x⟩ :
          Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ)) := by
  let ι : S × Icc a b → C₀.domain := fun x ↦ ⟨(x.1, (x.2 : ℝ)), hcollar x⟩
  let f : S × Icc a b → C₁.target := fun x ↦ ⟨(C₀.chart (ι x) : M), htarget x⟩
  let ψ : S × Icc a b → S × ℝ := fun x ↦ (C₁.chart.symm (f x) : S × ℝ)
  obtain ⟨hψ, -, hbij, hbound⟩ := transition_properties_of_gradient_close C₀ C₁ g a b
    hcollar htarget ε hε hsmall hU σ c δ B hσ hδ hgrad hvalue
  let v : ℝ → ℝ := fun z ↦ σ * ((Real.sqrt C₁.scale)⁻¹ * z) + c
  let e : S × Icc a b → S × ℝ := fun x ↦ ((ψ x).1, v (ψ x).2)
  have he : Continuous e := hψ.fst.prodMk
    ((continuous_const.mul (continuous_const.mul hψ.snd)).add continuous_const)
  have herror (x : S × Icc a b) :
      |(Real.sqrt C₀.scale)⁻¹ * (x.2 : ℝ) - (e x).2| ≤ B := hbound x
  let t₀ : Icc a b := ⟨a, le_rfl, hab⟩
  let t₁ : Icc a b := ⟨b, hab, le_rfl⟩
  let : PreconnectedSpace (Icc a b) := isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hband := DifferentialGeometry.Topology.prod_Icc_subset_range_of_fiberwise_bijective e he hbij
    t₀ t₁ ((Real.sqrt C₀.scale)⁻¹ * a + B) ((Real.sqrt C₀.scale)⁻¹ * b - B)
    (fun p ↦ by have h := (abs_le.mp (herror (p, t₀))).1; dsimp only [t₀] at h; linarith only [h])
    (fun p ↦ by have h := (abs_le.mp (herror (p, t₁))).2; dsimp only [t₁] at h; linarith only [h])
  have hv : Function.Injective v := by
    intro x y hxy
    have hσ₀ : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
    have hs : (Real.sqrt C₁.scale)⁻¹ ≠ 0 :=
      inv_ne_zero (Real.sqrt_pos.mpr C₁.scale_pos).ne'
    exact (mul_left_cancel₀ hs) (mul_left_cancel₀ hσ₀ (add_right_cancel hxy))
  rintro ⟨p, z⟩ ⟨-, hz⟩
  obtain ⟨x, hx⟩ := hband (show (p, v z) ∈ (univ : Set S) ×ˢ _ from ⟨mem_univ _, hz⟩)
  change ((ψ x).1, v (ψ x).2) = (p, v z) at hx
  change ∃ x, ψ x = (p, z)
  have hfirst := congrArg Prod.fst hx
  have hsecond := congrArg Prod.snd hx
  exact ⟨x, Prod.ext hfirst (hv hsecond)⟩

theorem cylindricalChart.exists_full_overlap_band_of_gradient_close
    {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    (C₀ C₁ : cylindricalChart J (M := M)) (g : SmoothRiemannianMetric J M)
    (a b : ℝ)
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
    (hwidth : 1 ≤ b - a) (herror : B ≤ (Real.sqrt C₀.scale)⁻¹ / 4)
    (hratio : |C₀.scale / C₁.scale - 1| ≤ 1 / 2) :
    ∃ l r : ℝ, 1 / 4 ≤ r - l ∧
      (univ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) ×ˢ Icc l r ⊆
        range (fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc a b ↦
          (C₁.chart.symm ⟨(C₀.chart ⟨(x.1, (x.2 : ℝ)), hcollar x⟩ : M), htarget x⟩ :
            Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ)) := by
  have hab : a ≤ b := by linarith only [hwidth]
  have hband := C₀.full_band_subset_transition_range_of_gradient_close C₁ g a b hab
    hcollar htarget ε hε hsmall hU σ c δ B hσ hδ hgrad hvalue
  have hratio' : C₀.scale / C₁.scale ≤ 3 / 2 := by
    have h := (abs_le.mp hratio).2
    linarith only [h]
  have hQ : C₀.scale ≤ 4 * C₁.scale := by
    have h := (div_le_iff₀ C₁.scale_pos).mp hratio'
    linarith only [h, C₁.scale_pos]
  have hroot : Real.sqrt C₀.scale ≤ 2 * Real.sqrt C₁.scale := by
    calc
      _ ≤ Real.sqrt (4 * C₁.scale) := Real.sqrt_le_sqrt hQ
      _ = _ := by
        rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
          Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
  have hscale : (Real.sqrt C₁.scale)⁻¹ ≤ 2 * (Real.sqrt C₀.scale)⁻¹ := by
    rw [← one_div, ← one_div, mul_one_div]
    apply (div_le_div_iff₀ (Real.sqrt_pos.mpr C₁.scale_pos)
      (Real.sqrt_pos.mpr C₀.scale_pos)).mpr
    simpa only [one_mul] using hroot
  obtain ⟨l, r, heq, hlen⟩ := DifferentialGeometry.Geometry.Affine.exists_Icc_of_comparable_scales
    (Real.sqrt C₀.scale)⁻¹ (Real.sqrt C₁.scale)⁻¹ a b B σ c
    (inv_pos.mpr (Real.sqrt_pos.mpr C₁.scale_pos)) hscale hwidth herror hσ
  exact ⟨l, r, hlen, by rw [← heq]; exact hband⟩

theorem cylindricalChart.exists_ordered_graph_band_of_gradient_close
    {F H M : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold J ∞ M] [T2Space M]
    (C₀ C₁ : cylindricalChart J (M := M)) (g : SmoothRiemannianMetric J M)
    (a b : ℝ) (hab : a ≤ b)
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
    let ψ := fun x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc a b ↦
      (C₁.chart.symm ⟨(C₀.chart ⟨(x.1, (x.2 : ℝ)), hcollar x⟩ : M), htarget x⟩ :
        Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ)
    let e := fun x ↦ ((ψ x).1, σ * ((Real.sqrt C₁.scale)⁻¹ * (ψ x).2) + c)
    ∃ h : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × Icc a b, ℝ),
      (∀ x, e x = ((e x).1, h ((e x).1, x.2))) ∧
      (∀ p, StrictMono (fun t ↦ h (p, t))) ∧
      range e = {y | h (y.1, ⟨a, le_rfl, hab⟩) ≤ y.2 ∧
        y.2 ≤ h (y.1, ⟨b, hab, le_rfl⟩)} ∧
      ∀ s t : Icc a b,
        e '' ((univ : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)) ×ˢ Icc s t) =
          {y | h (y.1, s) ≤ y.2 ∧ y.2 ≤ h (y.1, t)} := by
  let ι : S × Icc a b → C₀.domain := fun x ↦ ⟨(x.1, (x.2 : ℝ)), hcollar x⟩
  let f : S × Icc a b → C₁.target := fun x ↦ ⟨(C₀.chart (ι x) : M), htarget x⟩
  let ψ : S × Icc a b → S × ℝ := fun x ↦ (C₁.chart.symm (f x) : S × ℝ)
  obtain ⟨hψ, hψinj, hbij, hbound⟩ := transition_properties_of_gradient_close C₀ C₁ g a b
    hcollar htarget ε hε hsmall hU σ c δ B hσ hδ hgrad hvalue
  let v : ℝ → ℝ := fun z ↦ σ * ((Real.sqrt C₁.scale)⁻¹ * z) + c
  let e : S × Icc a b → S × ℝ := fun x ↦ ((ψ x).1, v (ψ x).2)
  have he : Continuous e := hψ.fst.prodMk
    ((continuous_const.mul (continuous_const.mul hψ.snd)).add continuous_const)
  have herror (x : S × Icc a b) :
      |(Real.sqrt C₀.scale)⁻¹ * (x.2 : ℝ) - (e x).2| ≤ B := hbound x
  have hv : Function.Injective v := by
    intro x y hxy
    have hσ₀ : σ ≠ 0 := by rcases hσ with rfl | rfl <;> norm_num
    have hs : (Real.sqrt C₁.scale)⁻¹ ≠ 0 :=
      inv_ne_zero (Real.sqrt_pos.mpr C₁.scale_pos).ne'
    exact (mul_left_cancel₀ hs) (mul_left_cancel₀ hσ₀ (add_right_cancel hxy))
  have hei : Function.Injective e := by
    intro x y hxy
    have hfirst := congrArg Prod.fst hxy
    have hsecond := congrArg Prod.snd hxy
    exact hψinj (Prod.ext hfirst (hv hsecond))
  exact DifferentialGeometry.Topology.exists_ordered_graph_band_of_fiberwise_bijective a b hab e he hei hbij
    (fun p q _ ↦ by
      have h₀ := (abs_le.mp (herror (p, ⟨a, le_rfl, hab⟩))).1
      have h₁ := (abs_le.mp (herror (q, ⟨b, hab, le_rfl⟩))).2
      dsimp only at h₀ h₁
      linarith only [h₀, h₁, hsep])

end DifferentialGeometry.Geometry.Neck
