import DifferentialGeometry.Geometry.Neck.InwardCurve
import DifferentialGeometry.Geometry.Neck.BoundaryFiber
import DifferentialGeometry.Topology.Ehresmann.BoundaryCompletion
import DifferentialGeometry.Topology.Manifold.BoundaryOrder

noncomputable section
open Set Filter Topology
open scoped Manifold ContDiff
open Poincare.Geometry.Boundary Poincare.Topology.Ehresmann
open DifferentialGeometry.Integral.DivergenceTheorem.WithBoundary

namespace Poincare.Geometry.Neck

theorem exists_regular_endpoints_of_extreme_neck_sections
    {E H W : Type} {F H' M : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace W] [ChartedSpace H W] [hI : HasSmoothBoundary E H I]
    [IsManifold I ∞ W] [CompactSpace W] [PreconnectedSpace W]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
    [TopologicalSpace M] [ChartedSpace H' M] [IsManifold J ∞ M]
    (ι : W → M) (hι : ContMDiff I J ∞ ι) (hemb : IsEmbedding ι)
    (hinj : ∀ w, Function.Injective (mfderiv I J ι w))
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F)
    (C₀ C₁ : cylindricalChart J (M := M)) (t₀ t₁ τ₀ τ₁ c₀ c₁ : ℝ)
    (hτ₀ : τ₀ = 1 ∨ τ₀ = -1)
    (S₀ S₁ : Set W) (hboundary : I.boundary W = S₀ ∪ S₁)
    (hsection₀ : ∀ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, (p, t₀) ∈ C₀.domain)
    (hsection₁ : ∀ p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1, (p, t₁) ∈ C₁.domain)
    (himage₀ : ι '' S₀ = range (fun p ↦ (C₀.chart ⟨(p, t₀), hsection₀ p⟩ : M)))
    (himage₁ : ι '' S₁ = range (fun p ↦ (C₁.chart ⟨(p, t₁), hsection₁ p⟩ : M)))
    (u : W → ℝ) (hu : ContMDiff I 𝓘(ℝ) ∞ u) (hreg : ∀ w, mvfderiv I u w ≠ 0)
    (hlocal₀ : ∀ᶠ w in 𝓝ˢ S₀, u w = τ₀ * C₀.axial (ι w) + c₀)
    (hlocal₁ : ∀ᶠ w in 𝓝ˢ S₁, u w = τ₁ * C₁.axial (ι w) + c₁)
    (r : ℝ) (hr : 0 < r)
    (hcollar : ∀ (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) s,
      s ∈ Icc 0 r → (p, t₀ + τ₀ * s) ∈ C₀.domain)
    (hinward : ∀ (p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) s (hs : s ∈ Icc 0 r),
      (C₀.chart ⟨(p, t₀ + τ₀ * s), hcollar p s hs⟩ : M) ∈ range ι) :
    let a := τ₀ * (Real.sqrt C₀.scale)⁻¹ * t₀ + c₀
    let b := τ₁ * (Real.sqrt C₁.scale)⁻¹ * t₁ + c₁
    ∃ (hab : a < b) (hbdy : ∀ w, I.IsBoundaryPoint w → u w = a ∨ u w = b),
      RegularIntervalDatum I u a b ∧
      u ⁻¹' ({a} : Set ℝ) = S₀ ∧ u ⁻¹' ({b} : Set ℝ) = S₁ ∧
      ∃ η : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 ≃ₘ⟮𝓡 2, hI.boundaryI⟯
          boundaryLevel u a b hab.ne hu.continuous hbdy,
        ∀ p, ι (η p).1.1 = (C₀.chart ⟨(p, t₀), hsection₀ p⟩ : M) := by
  let a := τ₀ * (Real.sqrt C₀.scale)⁻¹ * t₀ + c₀
  let b := τ₁ * (Real.sqrt C₁.scale)⁻¹ * t₁ + c₁
  have hval₀ (w : W) (hw : w ∈ S₀) : u w = a := by
    have hx : ι w ∈ ι '' S₀ := ⟨w, hw, rfl⟩
    rw [himage₀] at hx
    obtain ⟨p, hp⟩ := hx
    rw [subset_of_mem_nhdsSet hlocal₀ hw, ← hp, C₀.axial_chart]
    dsimp only [a, Prod.snd]
    ring
  have hval₁ (w : W) (hw : w ∈ S₁) : u w = b := by
    have hx : ι w ∈ ι '' S₁ := ⟨w, hw, rfl⟩
    rw [himage₁] at hx
    obtain ⟨p, hp⟩ := hx
    rw [subset_of_mem_nhdsSet hlocal₁ hw, ← hp, C₁.axial_chart]
    dsimp only [b, Prod.snd]
    ring
  have hbdy (w : W) (hw : I.IsBoundaryPoint w) : u w = a ∨ u w = b := by
    have hs : w ∈ S₀ ∪ S₁ := hboundary ▸ hw
    exact hs.elim (fun h ↦ Or.inl (hval₀ w h)) (fun h ↦ Or.inr (hval₁ w h))
  let p : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 :=
    ⟨EuclideanSpace.single 0 1, by simp⟩
  obtain ⟨γ, hγ, hγeq, hcoord, hk⟩ := C₀.exists_inward_affine_curve
    ι hemb p t₀ τ₀ c₀ r hτ₀ hr (hcollar p) (hinward p)
  have hγ₀ : γ 0 ∈ S₀ := by
    have hpoint : ι (γ 0) = (C₀.chart ⟨(p, t₀), hsection₀ p⟩ : M) := by
      rw [hγeq 0 ⟨le_rfl, hr.le⟩]
      congr 2
      apply Subtype.ext
      simp
    have hx : ι (γ 0) ∈ ι '' S₀ := by
      rw [himage₀, hpoint]
      exact mem_range_self p
    obtain ⟨w, hw, heq⟩ := hx
    exact hemb.injective heq ▸ hw
  have hab : a < b := Poincare.Topology.Manifold.boundary_value_lt_of_inward_coordinate
    hreg hbdy γ hγ.continuousWithinAt (mem_nhdsSet_iff_forall.mp hlocal₀ _ hγ₀) hk hcoord
  have ha : a ∈ range u := ⟨γ 0, hval₀ _ hγ₀⟩
  have hb : b ∈ range u := by
    have hx : (C₁.chart ⟨(p, t₁), hsection₁ p⟩ : M) ∈ ι '' S₁ := by
      rw [himage₁]
      exact mem_range_self p
    obtain ⟨w, hw, _⟩ := hx
    exact ⟨w, hval₁ w hw⟩
  have hdata := regularIntervalDatum_of_boundary_values hab hu hreg hbdy ha hb
  have hfiber₀ : u ⁻¹' ({a} : Set ℝ) = S₀ := by
    ext w
    change u w = a ↔ w ∈ S₀
    refine ⟨?_, hval₀ w⟩
    intro hw
    have hb : w ∈ I.boundary W := hdata.boundary_eq.symm ▸ Or.inl hw
    have hs : w ∈ S₀ ∪ S₁ := hboundary ▸ hb
    exact hs.elim id (fun h ↦ (hab.ne (hw.symm.trans (hval₁ w h))).elim)
  have hfiber₁ : u ⁻¹' ({b} : Set ℝ) = S₁ := by
    ext w
    change u w = b ↔ w ∈ S₁
    refine ⟨?_, hval₁ w⟩
    intro hw
    have hb : w ∈ I.boundary W := hdata.boundary_eq.symm ▸ Or.inr hw
    have hs : w ∈ S₀ ∪ S₁ := hboundary ▸ hb
    exact hs.elim (fun h ↦ (hab.ne ((hval₀ w h).symm.trans hw)).elim) id
  refine ⟨hab, hbdy, hdata, hfiber₀, hfiber₁, ?_⟩
  apply C₀.exists_boundaryLevel_sphere_parametrization ι hι hemb hinj hdim
    t₀ hsection₀ u a b hab.ne hu.continuous hbdy
  have hset : {w : W | I.IsBoundaryPoint w ∧ u w = a} = S₀ := by
    rw [← hfiber₀]
    ext w
    change (I.IsBoundaryPoint w ∧ u w = a) ↔ u w = a
    exact ⟨And.right, fun hw ↦ ⟨show w ∈ I.boundary W from hdata.boundary_eq.symm ▸ Or.inl hw, hw⟩⟩
  rw [hset]
  exact himage₀

end Poincare.Geometry.Neck
