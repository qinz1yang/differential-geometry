import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyNormRP3Pieces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39CarrierTransport74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Base
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.TorusIntervalPiece74
import DifferentialGeometry.Topology.Ehresmann.SurfaceIntervalProductEFE

/-!
# Draft 74, D74-10 / package S0 on the member: the `S² × [0, 1]` slim piece of an interval product

Lane C14-REG-CHAIN (by S-REG-CHAIN2), G29 (kernel). A smooth injective full-rank map
`m : S² × [0, 1] → X` into a closed three-manifold `X` (model `𝓡 3`; the output of the interval
product kernel `exists_standard_surface_interval_product_EFE`) carried by the closed-route
identification `e : X ≃ₘ W` (`M.ψ`) is a slim piece of `W` with the model
`SlimModel.sphereInterval`:

* `sphereArcPiece74 e m …`: the piece `sphereIntervalPiece (e ∘ m)` (the product atlas
  transported to the half-space model); the differential of `e ∘ m` is bijective because `dm` is
  injective between spaces of equal dimension `3` (`sphereArc_bijective_mfderiv_R74`);
* `sphereArcModel74`: its `SlimModel.sphereInterval`, with `range_sphereArcPiece74` (`e (range m)`)
  and `image_end_sphereArcModel74` (the two end slices are `e` of the end fibres `m (·, b)`);
* the same for `T² × [0, 1]` (`torusArcPiece74`, `torusArcModel74`, `SlimModel.torusInterval`)
  through `torusIntervalPiece` (`TorusIntervalPiece74`).

Universe: the piece types `ClosureSphere.{0}`, `Torus : Type 0`, so `W : CompactCarrier.{0}`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.GraphManifold.Assembly.FC39P0 (slimModelEnd slimModelIsInterval slimModelEndShape FaceShape)
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Sphere

variable {W : CompactCarrier.{0}} {X : Type*} [TopologicalSpace X] [ChartedSpace E3 X]


/-- A full-rank map from the three-dimensional product model into `X` has bijective differential
(dimensions `2 + 1 = 3`). -/
theorem sphereArc_bijective_mfderiv_R74 {m : ClosureSphere.{0} × Icc (0 : ℝ) 1 → X}
    (hmi : ∀ z, Injective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) m z))
    (z : ClosureSphere.{0} × Icc (0 : ℝ) 1) :
    Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) m z) :=
  ⟨hmi z, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
    change Module.finrank ℝ (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 1)) =
      Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))
    simp)).mp (hmi z)⟩

/-- The differential of `e ∘ m` is bijective. -/
theorem sphereArc_bijective_comp_R74 (e : X ≃ₘ⟮𝓡 3, W.model⟯ W.Carrier)
    {m : ClosureSphere.{0} × Icc (0 : ℝ) 1 → X}
    (hm : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞ m)
    (hmi : ∀ z, Injective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) m z))
    (z : ClosureSphere.{0} × Icc (0 : ℝ) 1) :
    Bijective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) W.model (e ∘ m) z) := by
  have hd : MDifferentiableAt ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) m z :=
    (hm z).mdifferentiableAt (by simp)
  have he : MDifferentiableAt (𝓡 3) W.model e (m z) := e.mdifferentiable (by simp) _
  rw [mfderiv_comp z he hd]
  exact (mfderiv_diffeo_bijective_R74 e (m z)).comp (sphereArc_bijective_mfderiv_R74 hmi z)

/-- **The slim piece of an `S² × [0, 1]` product map** carried to `W` by `e`. -/
def sphereArcPiece74 (e : X ≃ₘ⟮𝓡 3, W.model⟯ W.Carrier)
    (m : ClosureSphere.{0} × Icc (0 : ℝ) 1 → X)
    (hm : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞ m)
    (hmi : ∀ z, Injective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) m z)) (hinj : Injective m) :
    PieceEmbedding W :=
  sphereIntervalPiece (e ∘ m) (e.contMDiff.comp hm) (sphereArc_bijective_comp_R74 e hm hmi)
    (e.injective.comp hinj)

/-- The slim model `sphereInterval` of the carried product piece. -/
def sphereArcModel74 (e : X ≃ₘ⟮𝓡 3, W.model⟯ W.Carrier)
    (m : ClosureSphere.{0} × Icc (0 : ℝ) 1 → X)
    (hm : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞ m)
    (hmi : ∀ z, Injective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) m z)) (hinj : Injective m) :
    SlimModel (sphereArcPiece74 e m hm hmi hinj) :=
  .sphereInterval (sphereIntervalPieceDiffeo (e ∘ m) (e.contMDiff.comp hm)
    (sphereArc_bijective_comp_R74 e hm hmi) (e.injective.comp hinj))

/-- The carried piece has range `e (range m)`. -/
theorem range_sphereArcPiece74 (e : X ≃ₘ⟮𝓡 3, W.model⟯ W.Carrier)
    (m : ClosureSphere.{0} × Icc (0 : ℝ) 1 → X)
    (hm : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞ m)
    (hmi : ∀ z, Injective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) m z)) (hinj : Injective m) :
    range (sphereArcPiece74 e m hm hmi hinj).map = e '' range m :=
  range_comp e m

/-- The end slices of the carried piece are the `e`-images of the end fibres of `m`. -/
theorem image_end_sphereArcModel74 (e : X ≃ₘ⟮𝓡 3, W.model⟯ W.Carrier)
    (m : ClosureSphere.{0} × Icc (0 : ℝ) 1 → X)
    (hm : ContMDiff ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) ∞ m)
    (hmi : ∀ z, Injective (mfderiv ((𝓡 2).prod (𝓡∂ 1)) (𝓡 3) m z)) (hinj : Injective m)
    (b : Bool) :
    (sphereArcPiece74 e m hm hmi hinj).map '' slimModelEnd (sphereArcModel74 e m hm hmi hinj) b =
      e '' range fun x => m (x, iccEnd b) := by
  refine (range_comp (sphereArcPiece74 e m hm hmi hinj).map
    (fun z => sphereIntervalPieceDiffeo (e ∘ m) (e.contMDiff.comp hm)
      (sphereArc_bijective_comp_R74 e hm hmi) (e.injective.comp hinj) (z, iccEnd b))).symm.trans ?_
  exact range_comp e fun x => m (x, iccEnd b)

end Sphere

section Torus

variable {W : CompactCarrier.{0}} {X : Type*} [TopologicalSpace X] [ChartedSpace E3 X]


/-- A full-rank map from the three-dimensional torus-interval model into `X` has bijective
differential (dimensions `1 + 1 + 1 = 3`). -/
theorem torusArc_bijective_mfderiv_R74 {m : Torus × Icc (0 : ℝ) 1 → X}
    (hmi : ∀ z, Injective (mfderiv (torusModel.prod (𝓡∂ 1)) (𝓡 3) m z))
    (z : Torus × Icc (0 : ℝ) 1) :
    Bijective (mfderiv (torusModel.prod (𝓡∂ 1)) (𝓡 3) m z) :=
  ⟨hmi z, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
    change Module.finrank ℝ ((EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) ×
      EuclideanSpace ℝ (Fin 1)) = Module.finrank ℝ (EuclideanSpace ℝ (Fin 3))
    simp)).mp (hmi z)⟩

/-- The differential of `e ∘ m` is bijective. -/
theorem torusArc_bijective_comp_R74 (e : X ≃ₘ⟮𝓡 3, W.model⟯ W.Carrier)
    {m : Torus × Icc (0 : ℝ) 1 → X}
    (hm : ContMDiff (torusModel.prod (𝓡∂ 1)) (𝓡 3) ∞ m)
    (hmi : ∀ z, Injective (mfderiv (torusModel.prod (𝓡∂ 1)) (𝓡 3) m z))
    (z : Torus × Icc (0 : ℝ) 1) :
    Bijective (mfderiv (torusModel.prod (𝓡∂ 1)) W.model (e ∘ m) z) := by
  have hd : MDifferentiableAt (torusModel.prod (𝓡∂ 1)) (𝓡 3) m z :=
    (hm z).mdifferentiableAt (by simp)
  have he : MDifferentiableAt (𝓡 3) W.model e (m z) := e.mdifferentiable (by simp) _
  rw [mfderiv_comp z he hd]
  exact (mfderiv_diffeo_bijective_R74 e (m z)).comp (torusArc_bijective_mfderiv_R74 hmi z)

/-- **The slim piece of a `T² × [0, 1]` product map** carried to `W` by `e`. -/
def torusArcPiece74 (e : X ≃ₘ⟮𝓡 3, W.model⟯ W.Carrier) (m : Torus × Icc (0 : ℝ) 1 → X)
    (hm : ContMDiff (torusModel.prod (𝓡∂ 1)) (𝓡 3) ∞ m)
    (hmi : ∀ z, Injective (mfderiv (torusModel.prod (𝓡∂ 1)) (𝓡 3) m z)) (hinj : Injective m) :
    PieceEmbedding W :=
  torusIntervalPiece (e ∘ m) (e.contMDiff.comp hm) (torusArc_bijective_comp_R74 e hm hmi)
    (e.injective.comp hinj)

/-- The slim model `torusInterval` of the carried product piece. -/
def torusArcModel74 (e : X ≃ₘ⟮𝓡 3, W.model⟯ W.Carrier) (m : Torus × Icc (0 : ℝ) 1 → X)
    (hm : ContMDiff (torusModel.prod (𝓡∂ 1)) (𝓡 3) ∞ m)
    (hmi : ∀ z, Injective (mfderiv (torusModel.prod (𝓡∂ 1)) (𝓡 3) m z)) (hinj : Injective m) :
    SlimModel (torusArcPiece74 e m hm hmi hinj) :=
  .torusInterval (torusIntervalPieceDiffeo (e ∘ m) (e.contMDiff.comp hm)
    (torusArc_bijective_comp_R74 e hm hmi) (e.injective.comp hinj))

/-- The carried piece has range `e (range m)`. -/
theorem range_torusArcPiece74 (e : X ≃ₘ⟮𝓡 3, W.model⟯ W.Carrier) (m : Torus × Icc (0 : ℝ) 1 → X)
    (hm : ContMDiff (torusModel.prod (𝓡∂ 1)) (𝓡 3) ∞ m)
    (hmi : ∀ z, Injective (mfderiv (torusModel.prod (𝓡∂ 1)) (𝓡 3) m z)) (hinj : Injective m) :
    range (torusArcPiece74 e m hm hmi hinj).map = e '' range m :=
  range_comp e m

/-- The end slices of the carried piece are the `e`-images of the end fibres of `m`. -/
theorem image_end_torusArcModel74 (e : X ≃ₘ⟮𝓡 3, W.model⟯ W.Carrier)
    (m : Torus × Icc (0 : ℝ) 1 → X) (hm : ContMDiff (torusModel.prod (𝓡∂ 1)) (𝓡 3) ∞ m)
    (hmi : ∀ z, Injective (mfderiv (torusModel.prod (𝓡∂ 1)) (𝓡 3) m z)) (hinj : Injective m)
    (b : Bool) :
    (torusArcPiece74 e m hm hmi hinj).map '' slimModelEnd (torusArcModel74 e m hm hmi hinj) b =
      e '' range fun x => m (x, iccEnd b) := by
  refine (range_comp (torusArcPiece74 e m hm hmi hinj).map
    (fun z => torusIntervalPieceDiffeo (e ∘ m) (e.contMDiff.comp hm)
      (torusArc_bijective_comp_R74 e hm hmi) (e.injective.comp hinj) (z, iccEnd b))).symm.trans ?_
  exact range_comp e fun x => m (x, iccEnd b)

end Torus


end GC.GraphManifold.Assembly

namespace DifferentialGeometry.Topology.Ehresmann

open GC.GraphManifold.Assembly

local notation "E3" => EuclideanSpace ℝ (Fin 3)

section Product

variable {W : CompactCarrier.{0}} {X : Type*} [TopologicalSpace X] [ChartedSpace E3 X]
  {ι : Type*} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  {Bs : Set H} {Pr : ProperSmoothSurfaceSubmersion_EFE (𝓡 3) X ι Bs}
  {γ : SmoothEmbeddedBaseArc_EFE Bs}

/-- **The slim piece of a whole `S² × I` interval product** (the output contract of D74-10 /
`exists_standard_surface_interval_product_EFE`) carried to `W` by `e`: the piece with the model
`sphereInterval`, range the `e`-image of the whole preimage of the arc, and the two end slices the
`e`-images of the WHOLE end fibres over `γ 0`, `γ 1`. -/
theorem WholeSurfaceIntervalProduct_EFE.exists_slimPiece_sphere74
    {F₀ : StandardWholeSurfaceFibre_EFE Pr (𝓡 2) ClosureSphere.{0} (γ.toFun 0)}
    (Wp : WholeSurfaceIntervalProduct_EFE Pr γ F₀) (e : X ≃ₘ⟮𝓡 3, W.model⟯ W.Carrier) :
    ∃ (Pc : PieceEmbedding W) (mo : SlimModel Pc), slimModelIsInterval mo ∧
      slimModelEndShape mo = FaceShape.sphere ∧
      range Pc.map = e '' (Pr.toFun ⁻¹' (γ.toFun '' Icc 0 1)) ∧
      ∀ b : Bool, Pc.map '' slimModelEnd mo b = e '' (Pr.toFun ⁻¹' {γ.toFun (iccEnd b)}) := by
  refine ⟨sphereArcPiece74 e Wp.map Wp.smooth Wp.fullRank Wp.injective,
    sphereArcModel74 e Wp.map Wp.smooth Wp.fullRank Wp.injective, trivial, rfl, ?_, fun b => ?_⟩
  · rw [range_sphereArcPiece74, Wp.range_eq]
  · rw [image_end_sphereArcModel74]
    congr 1
    cases b
    · change range (fun x => Wp.map (x, ⟨0, left_mem_Icc.mpr zero_le_one⟩)) = _
      rw [funext Wp.start_eq]
      exact F₀.range_eq
    · exact Wp.end_range

/-- **The slim piece of a whole `T² × I` interval product** carried to `W` by `e`. -/
theorem WholeSurfaceIntervalProduct_EFE.exists_slimPiece_torus74
    {F₀ : StandardWholeSurfaceFibre_EFE Pr torusModel Torus (γ.toFun 0)}
    (Wp : WholeSurfaceIntervalProduct_EFE Pr γ F₀) (e : X ≃ₘ⟮𝓡 3, W.model⟯ W.Carrier) :
    ∃ (Pc : PieceEmbedding W) (mo : SlimModel Pc), slimModelIsInterval mo ∧
      slimModelEndShape mo = FaceShape.torus ∧
      range Pc.map = e '' (Pr.toFun ⁻¹' (γ.toFun '' Icc 0 1)) ∧
      ∀ b : Bool, Pc.map '' slimModelEnd mo b = e '' (Pr.toFun ⁻¹' {γ.toFun (iccEnd b)}) := by
  refine ⟨torusArcPiece74 e Wp.map Wp.smooth Wp.fullRank Wp.injective,
    torusArcModel74 e Wp.map Wp.smooth Wp.fullRank Wp.injective, trivial, rfl, ?_, fun b => ?_⟩
  · rw [range_torusArcPiece74, Wp.range_eq]
  · rw [image_end_torusArcModel74]
    congr 1
    cases b
    · change range (fun x => Wp.map (x, ⟨0, left_mem_Icc.mpr zero_le_one⟩)) = _
      rw [funext Wp.start_eq]
      exact F₀.range_eq
    · exact Wp.end_range

end Product

end DifferentialGeometry.Topology.Ehresmann
