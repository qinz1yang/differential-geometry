import DifferentialGeometry.External.CanonicalTopology.Topology.LoopSpace.Basic
import Mathlib.Geometry.Manifold.MFDeriv.SpecificFunctions
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv

section


noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

abbrev CurveMap (M : Type*) := AddCircle (1 : ℝ) → ℝ → M

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

end

section


noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace CurveMap


def lift (c : CurveMap M) (x t : ℝ) : M := c (x : AddCircle (1 : ℝ)) t

def X (c : CurveMap M) (x t : ℝ) : TangentSpace I (c.lift x t) :=
  mfderiv 𝓘(ℝ, ℝ) I (fun y => c.lift y t) x (1 : ℝ)

def velocity (c : CurveMap M) (J : Set ℝ) (x t : ℝ) :
    TangentSpace I (c.lift x t) :=
  mfderivWithin 𝓘(ℝ, ℝ) I (c.lift x) J t (1 : ℝ)

abbrev Field (c : CurveMap M) := (x t : ℝ) → TangentSpace I (c.lift x t)

def SmoothOn (c : CurveMap M) (J : Set ℝ) : Prop :=
  ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I ∞ (fun p => c.lift p.1 p.2) (univ ×ˢ J)

def ImmersedOn (c : CurveMap M) (J : Set ℝ) : Prop :=
  ∀ x t, t ∈ J → c.X (I := I) x t ≠ 0

end CurveMap

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

end

section


noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [SigmaCompactSpace M] [T2Space M]

namespace CurveMap


omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [T2Space M] in
theorem time_slice_contMDiffWithinAt (c : CurveMap M) (J : Set ℝ)
    (hc : c.SmoothOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    ContMDiffWithinAt 𝓘(ℝ, ℝ) I ∞ (fun s => c.lift x s) J t := by
  have hmem : (x, t) ∈ (univ : Set ℝ) ×ˢ J := ⟨mem_univ x, ht⟩
  have hz : ContMDiffWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun s : ℝ => (x, s)) J t := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact contMDiffWithinAt_const.prodMk contMDiffWithinAt_id
  have hto : Set.MapsTo (fun s : ℝ => (x, s)) J ((univ : Set ℝ) ×ˢ J) :=
    fun s _ => ⟨mem_univ x, by assumption⟩
  exact (hc (x, t) hmem).comp t hz hto

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [T2Space M] in
theorem time_slice_contMDiffOn (c : CurveMap M) (J : Set ℝ)
    (hc : c.SmoothOn (I := I) J) (x : ℝ) :
    ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (fun s => c.lift x s) J :=
  fun t ht => time_slice_contMDiffWithinAt c J hc x t ht

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [T2Space M] in
theorem space_slice_contMDiffWithinAt (c : CurveMap M) (J : Set ℝ)
    (hc : c.SmoothOn (I := I) J) (x t : ℝ) (ht : t ∈ J) :
    ContMDiffWithinAt 𝓘(ℝ, ℝ) I ∞ (fun z => c.lift z t) univ x := by
  have hmem : (x, t) ∈ (univ : Set ℝ) ×ˢ J := ⟨mem_univ x, ht⟩
  have hz : ContMDiffWithinAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun z : ℝ => (z, t)) univ x := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact contMDiffWithinAt_id.prodMk contMDiffWithinAt_const
  have hto : Set.MapsTo (fun z : ℝ => (z, t)) univ ((univ : Set ℝ) ×ˢ J) :=
    fun z _ => ⟨mem_univ z, ht⟩
  exact (hc (x, t) hmem).comp x hz hto

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] [SigmaCompactSpace M]
  [T2Space M] in
theorem space_slice_contMDiffOn (c : CurveMap M) (J : Set ℝ)
    (hc : c.SmoothOn (I := I) J) (t : ℝ) (ht : t ∈ J) :
    ContMDiffOn 𝓘(ℝ, ℝ) I ∞ (fun z => c.lift z t) univ :=
  fun x _ => space_slice_contMDiffWithinAt c J hc x t ht

end CurveMap

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

end


section


noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] in
theorem CurveMap.smooth_slice (c : CurveMap M) {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) {t : ℝ} (ht : t ∈ J) :
    ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun x => c.lift x t) := by
  have hp : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (fun x : ℝ => (x, t)) :=
    (contDiff_id.prodMk contDiff_const).contMDiff
  exact contMDiffOn_univ.mp (hc.comp hp.contMDiffOn (fun _ _ => ⟨mem_univ _, ht⟩))

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

end


section


noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

def curveOfLoopFamily (γ : ℝ → DifferentialGeometry.Topology.freeLoop M) : CurveMap M := fun z t => γ t z

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

end


section


noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [hBoundary : I.Boundaryless] [hT2 : T2Space M] [hCompact : CompactSpace M]
  [hNonempty : Nonempty M] [SigmaCompactSpace M]
  {a b : ℝ}

namespace CurveMap


omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] hBoundary hT2 hCompact
  hNonempty [SigmaCompactSpace M] in
theorem smoothOn_mono {c : CurveMap M} {J J' : Set ℝ} (h : c.SmoothOn (I := I) J)
    (hsub : J' ⊆ J) : c.SmoothOn (I := I) J' :=
  h.mono fun _ hp => ⟨hp.1, hsub hp.2⟩

omit [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M] hBoundary hT2 hCompact
  hNonempty [SigmaCompactSpace M] in
theorem immersedOn_mono {c : CurveMap M} {J J' : Set ℝ} (h : c.ImmersedOn (I := I) J)
    (hsub : J' ⊆ J) : c.ImmersedOn (I := I) J' :=
  fun x t ht => h x t (hsub ht)

end CurveMap

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

end


section


noncomputable section

open Bundle Manifold Set Filter Function
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] in
theorem smoothOn_constLoopFamily (m : M) (a b : ℝ) :
    (curveOfLoopFamily (fun _ : ℝ => DifferentialGeometry.Topology.FreeLoop.constants m)).SmoothOn (I := I) (Icc a b) :=
  contMDiffOn_const

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

end


section


noncomputable section

open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {a b : ℝ}

omit [FiniteDimensional ℝ E] in
theorem contDiffOn_loopFamily_swap {γ : ℝ → DifferentialGeometry.Topology.freeLoop E} {J : Set ℝ}
    (h : (curveOfLoopFamily γ).SmoothOn (I := 𝓘(ℝ, E)) J) :
    ContDiffOn ℝ ∞ (fun q : ℝ × ℝ => γ q.1 (q.2 : DifferentialGeometry.Topology.loopCircle))
      (J ×ˢ univ) := by
  have hbase : ContDiffOn ℝ ∞ (fun p : ℝ × ℝ => γ p.2 (p.1 : DifferentialGeometry.Topology.loopCircle))
      (univ ×ˢ J) := by
    simpa only [CurveMap.SmoothOn, CurveMap.lift, curveOfLoopFamily] using h.contDiffOn
  have hswap : ContDiff ℝ ∞ (fun q : ℝ × ℝ => (q.2, q.1)) := by fun_prop
  have hmaps : MapsTo (fun q : ℝ × ℝ => (q.2, q.1)) (J ×ˢ univ) (univ ×ˢ J) :=
    fun q hq => ⟨trivial, hq.1⟩
  have hcomp := hbase.comp hswap.contDiffOn hmaps
  simpa only [Function.comp_def] using hcomp

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

end

end

