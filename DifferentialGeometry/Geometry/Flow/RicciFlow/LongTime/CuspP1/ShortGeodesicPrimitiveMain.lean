import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspP1.ShortGeodesicPrimitive

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology Set Function GC.Endpoint
open scoped Manifold ContDiff ContinuousMap
namespace GC.LongTime.CuspP1

/-- **Primitive closed geodesic of a flat torus.** For every flat smooth metric on `Circle × Circle`
there is an embedded smooth closed geodesic whose degree-one class is a basis element
`(1, 0)` of `π₁(T²) ≅ ℤ²` for a suitable identification. -/
theorem exists_primitive_closed_geodesic_CPA2 (g : SmoothRiemannianMetric torusModel Torus)
    (hflat : ∀ (x : Torus) (v w : TangentSpace torusModel x),
      DifferentialGeometry.Geometry.Curvature.metricRm04StandardAt g x v w w v = 0) :
    ∃ loop : freeLoop Torus,
      _root_.Topology.IsEmbedding loop ∧
      ContMDiff 𝓘(ℝ, ℝ) torusModel ∞ (loopLift loop) ∧
      DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesic (I := torusModel) g
        (loopLift loop) ∧
      ∃ e : FundamentalGroup Torus (loop 0) ≃* Multiplicative ℤ × Multiplicative ℤ,
        e (loopDegreeClass loop 1) = (Multiplicative.ofAdd 1, 1) := by
  obtain ⟨F, v₁, v₂, hFc, hFs, hli, hfib, -, hsm, hgeo⟩ :=
    exists_exp_lattice_torus_CPA2 g hflat ((1 : Circle), (1 : Circle))
  obtain ⟨h, hh⟩ := exists_homeo_of_lattice_cover_CPA2 F v₁ v₂ hFc hFs hli hfib
  let φC : C(loopCircle, Circle) := (phiC : C(loopCircle, Circle))
  let sl : C(Circle, Torus) := Circle.slopeContinuousMap ![1, 0]
  let hC : C(Torus, Torus) := (h : C(Torus, Torus))
  let loop : freeLoop Torus := hC.comp (sl.comp φC)
  have hloop : ∀ s : ℝ, loop (s : loopCircle) = F (s • v₁) := by
    intro s
    rw [← hh s]
    change h (sl (phiC (s : AddCircle (1 : ℝ)))) = _
    congr 1
    simp [sl, Circle.slopeContinuousMap, Circle.slopeMap]
  have hlift : (⇑(loopLift loop) : ℝ → Torus) = fun s : ℝ => F (s • v₁) :=
    funext fun s => hloop s
  have hφ0 : φC 0 = 1 := phiC_zero
  have hs1 : sl 1 = ((1 : Circle), (1 : Circle)) := Circle.slopeContinuousMap_one _
  have hbase : sl (φC 0) = ((1 : Circle), (1 : Circle)) := by rw [hφ0, hs1]
  have hh' : hC ((1 : Circle), (1 : Circle)) = loop 0 := by
    change h _ = h (sl (φC 0))
    rw [hbase]
  refine ⟨loop, ?_, ?_, ?_, ?_⟩
  · -- embedding
    have hin : Function.Injective (sl.comp φC) := by
      intro x y hxy
      have := congrArg Prod.fst hxy
      simpa [sl, φC, Circle.slopeContinuousMap, Circle.slopeMap] using this
    have hemb : _root_.Topology.IsEmbedding (sl.comp φC) :=
      ((sl.comp φC).continuous.isClosedEmbedding hin).isEmbedding
    exact h.isEmbedding.comp hemb
  · rw [hlift]; exact hsm
  · rw [hlift]; exact hgeo
  · have ha₀ : fundamentalGroupUnitAddCircleEquivInt
        (loopDegreeClass (ContinuousMap.id loopCircle) 1) = Multiplicative.ofAdd (1 : ℤ) := by
      have hgen : loopDegreeClass (ContinuousMap.id loopCircle) 1 =
          FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk circleGeneratorPath) := by
        unfold loopDegreeClass
        change Path.Homotopic.Quotient.mk _ = Path.Homotopic.Quotient.mk _
        congr 1
        ext t
        change ((((1 : ℤ) : ℝ) * (t : ℝ) : ℝ) : loopCircle) = ((t : ℝ) : loopCircle)
        simp
      rw [hgen]
      exact fundamentalGroupUnitAddCircleEquivInt_generator
    let b : FundamentalGroup Circle 1 :=
      FundamentalGroup.mapOfEq φC hφ0 (loopDegreeClass (ContinuousMap.id loopCircle) 1)
    have hdeg : fundamentalGroupCircleEquivInt b = Multiplicative.ofAdd (1 : ℤ) := by
      have h1 := fundamentalGroupCircleEquivInt_map_addCircle
        (loopDegreeClass (ContinuousMap.id loopCircle) 1)
      rw [ha₀] at h1
      exact h1
    let e₁ : FundamentalGroup Torus ((1 : Circle), (1 : Circle)) ≃* FundamentalGroup Torus (loop 0) :=
      fundamentalGroupMulEquivOfHomotopyEquiv h.toHomotopyEquiv ((1 : Circle), (1 : Circle))
        (loop 0) hh'
    refine ⟨e₁.symm.trans GC.Topology.torusFundamentalGroup, ?_⟩
    have c1 := fundamentalGroup_mapOfEq_comp φC sl hφ0 hs1
    have c2 := fundamentalGroup_mapOfEq_comp (sl.comp φC) hC
      ((congrArg sl hφ0).trans hs1) hh'
    have hcl : loopDegreeClass loop 1 =
        FundamentalGroup.mapOfEq loop rfl (loopDegreeClass (ContinuousMap.id loopCircle) 1) :=
      loopDegreeClass_comp_CPA2 loop (ContinuousMap.id loopCircle)
    have key : loopDegreeClass loop 1 =
        e₁ (FundamentalGroup.mapOfEq sl hs1 b) := by
      refine hcl.trans ?_
      change _ = FundamentalGroup.mapOfEq hC hh' (FundamentalGroup.mapOfEq sl hs1 b)
      have : FundamentalGroup.mapOfEq loop (rfl : loop 0 = loop 0) =
          (FundamentalGroup.mapOfEq hC hh').comp
            ((FundamentalGroup.mapOfEq sl hs1).comp (FundamentalGroup.mapOfEq φC hφ0)) := by
        rw [← c1, ← c2]
      have h2 := congrArg (fun f : FundamentalGroup loopCircle (0 : loopCircle) →*
        FundamentalGroup Torus (loop 0) =>
          f (loopDegreeClass (ContinuousMap.id loopCircle) 1)) this
      exact h2
    rw [key]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    rw [GC.Topology.torusFundamentalGroup_map_slope, hdeg]
    simp

end GC.LongTime.CuspP1
