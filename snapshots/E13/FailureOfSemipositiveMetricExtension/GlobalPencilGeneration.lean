import FailureOfSemipositiveMetricExtension.GlobalPencilDivision
import FailureOfSemipositiveMetricExtension.GlobalFiberSections

/-! Base-point freeness of the actual analytic pencil on every noncentral fibre. -/
namespace FailureOfSemipositiveMetricExtension.GlobalLineBundle
noncomputable section
open Set FailureOfSemipositiveMetricExtension.GlobalIncidence
open scoped Manifold ContDiff

theorem pencilLocalCoefficient_exceptional_nonzero (r : Fin 4) (e : Fin 2) (t s : ℂ) (ht : t ≠ 0) :
    ∃ k, pencilLocalCoefficient r e k ((0,s),t) ≠ 0 := by
  by_contra h
  push_neg at h
  have h0 := h 0
  have h1 := h 1
  fin_cases r <;> fin_cases e
  all_goals simp [pencilLocalCoefficient,FailureOfSemipositiveMetricExtension.PencilSections.x₁,FailureOfSemipositiveMetricExtension.PencilSections.y₁,
    FailureOfSemipositiveMetricExtension.PencilSections.x₂,FailureOfSemipositiveMetricExtension.PencilSections.y₂,
    FailureOfSemipositiveMetricExtension.PencilSections.x₃,FailureOfSemipositiveMetricExtension.PencilSections.y₃,
    FailureOfSemipositiveMetricExtension.PencilSections.x₄,FailureOfSemipositiveMetricExtension.PencilSections.y₄] at h0 h1
  all_goals simp_all

theorem pencilHomogeneous_common_zero (t : ℂ) (ht : t ≠ 0) (v : Fin 3 → ℂ) (hv : v ≠ 0)
    (h : ∀ k, (pencilHomogeneous k).value (t,v) = 0) :
    ∃ r, Projectivization.mk ℂ v hv = centre r t := by
  have h0 : FailureOfSemipositiveMetricExtension.Coordinates.F₁ t (v 0) (v 1) (v 2) = 0 := by
    simpa [pencilHomogeneous] using h 0
  have h1 : FailureOfSemipositiveMetricExtension.Coordinates.F₂ t (v 0) (v 1) (v 2) = 0 := by
    simpa [pencilHomogeneous] using h 1
  rcases (FailureOfSemipositiveMetricExtension.Coordinates.projective_common_zero_locus t ht v hv).mp ⟨h0,h1⟩ with
    h | h | h | h
  · exact ⟨0,h⟩
  · exact ⟨1,h⟩
  · exact ⟨2,h⟩
  · exact ⟨3,h⟩

/-- Both the nonexceptional and all exceptional points are included. -/
theorem pencilLocalCoefficient_no_basepoint (r : Fin 4) (e : Fin 2) (q : ChartCoord)
    (hq : q ∈ chartDomain r e) (ht : q.2 ≠ 0) :
    ∃ k, pencilLocalCoefficient r e k q ≠ 0 := by
  by_cases hr : q.1.1 = 0
  · have heq : q = ((0,q.1.2),q.2) := by ext <;> simp_all
    rw [heq]
    exact pencilLocalCoefficient_exceptional_nonzero r e q.2 q.1.2 ht
  · by_contra hn
    push_neg at hn
    have hvan : ∀ k, (pencilHomogeneous k).value
        (q.2,baseVector r q.2 (FailureOfSemipositiveMetricExtension.Blowup.projection (localParam e q.1))) = 0 := by
      intro k
      rw [pencil_divided_pullback,hn k,mul_zero]
    obtain ⟨j,hj⟩ := pencilHomogeneous_common_zero q.2 ht _ (baseVector_ne_zero r q.2 _) hvan
    have haway := (chartParam_mem_awayCentres_iff r e q hq).mpr hr
    exact haway j hj

/-- At every point over a nonzero parameter, one genuine fibre vector is nonzero. -/
theorem liftedPencil_no_basepoint (p : Total) (ht : projection p ≠ 0) :
    ∃ k, sectionValue (liftedPencil k) p ≠ 0 := by
  obtain ⟨d,hp⟩ := divisionPatch_cover p
  let q := chartCoordinates d.1 d.2.1 p
  have hq : q ∈ chartDomain d.1 d.2.1 := (partialChart d.1 d.2.1).map_source hp.1
  have htq : q.2 ≠ 0 := by
    have heq := congrArg projection (chartParam_coordinates d.1 d.2.1 p hp.1)
    exact fun h => ht (heq.symm.trans h)
  obtain ⟨k,hk⟩ := pencilLocalCoefficient_no_basepoint d.1 d.2.1 q hq htq
  refine ⟨k,?_⟩
  rw [ne_eq,sectionValue_zero_iff (liftedPencil k) (divisionFrame d) p hp.2,liftedPencil_coefficient k d p hp]
  exact div_ne_zero hk (pencilOtherDenominator_ne_zero d p hp)

/-- The two global sections span the actual one-dimensional complex fibre. -/
theorem liftedPencil_generates (p : Total) (ht : projection p ≠ 0) :
    Submodule.span ℂ (Set.range (fun k => sectionValue (liftedPencil k) p)) = ⊤ := by
  obtain ⟨k,hk⟩ := liftedPencil_no_basepoint p ht
  apply top_unique
  intro v _
  have hs : sectionValue (liftedPencil k) p ∈
      Submodule.span ℂ (Set.range (fun k => sectionValue (liftedPencil k) p)) :=
    Submodule.subset_span ⟨k,rfl⟩
  let c : ℂ := (show ℂ from v) / (show ℂ from sectionValue (liftedPencil k) p)
  have heq : c • sectionValue (liftedPencil k) p = v := by
    change (show ℂ from v) / (show ℂ from sectionValue (liftedPencil k) p) *
      (show ℂ from sectionValue (liftedPencil k) p) = (show ℂ from v)
    exact div_mul_cancel₀ _ hk
  rw [← heq]
  exact Submodule.smul_mem _ c hs

/-- Restriction gives two actual analytic sections of the actual line bundle on every fibre. -/
def fibrePencil (t : ℂ) (k : Fin 2) :
    FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.SectionData t (-2) (fun _ => 1) :=
  FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.pullback t (liftedPencil k)

theorem fibrePencil_no_basepoint (t : ℂ) (ht : t ≠ 0) (p : Fiber t) :
    ∃ k, FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.sectionValue (fibrePencil t k) p ≠ 0 := by
  simpa only [fibrePencil,FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.pullback_zero_iff] using
    liftedPencil_no_basepoint (FixedFiber.inclusion t p) ht
end
end FailureOfSemipositiveMetricExtension.GlobalLineBundle
