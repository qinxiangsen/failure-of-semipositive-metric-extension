import FailureOfSemipositiveMetricExtension.CentralAuxiliaryZeroSets
import FailureOfSemipositiveMetricExtension.CentralQSubmersion

/-! A focused literal-support and reduced-equation certificate for the actual
ell and Q sections. Only accepted stage9 and increment5 artifacts are imported.
No historical strict-transform module or its unknown build is imported or
restarted. The proof works directly in the actual fibre topology. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.PaperStrictTransforms
noncomputable section
open Set Topology

def lineZero (f : (Fin 3 → ℂ) →ₗ[ℂ] ℂ) : Set PlanePoint :=
  {p | p.submodule ≤ LinearMap.ker f}

def ellForm : (Fin 3 → ℂ) →ₗ[ℂ] ℂ := LinearMap.proj 2

def qForm (k : Fin 3) : (Fin 3 → ℂ) →ₗ[ℂ] ℂ where
  toFun v := ![v 1,v 0,v 0-v 1] k
  map_add' v w := by fin_cases k <;> simp <;> ring
  map_smul' a v := by fin_cases k <;> simp <;> ring

/-- Literal closure of the original inverse image outside ALL four centres. -/
def strictTransform (f : (Fin 3 → ℂ) →ₗ[ℂ] ℂ) : Set (Fiber 0) :=
  closure (FixedFiber.blowdown 0 ⁻¹' lineZero f ∩ FixedFiber.awayCentres 0)

theorem lineZero_mk (f : (Fin 3 → ℂ) →ₗ[ℂ] ℂ) (v : Fin 3 → ℂ) (hv : v ≠ 0) :
    Projectivization.mk ℂ v hv ∈ lineZero f ↔ f v = 0 := by
  change (Projectivization.mk ℂ v hv).submodule ≤ LinearMap.ker f ↔ _
  rw [Projectivization.submodule_mk,Submodule.span_singleton_le_iff_mem]
  rfl

theorem lineZero_normalized (f : (Fin 3 → ℂ) →ₗ[ℂ] ℂ)
    (a : Fin 3) (p : PlanePoint) (hp : p ∈ ProjectivePlane.chartSet a) :
    p ∈ lineZero f ↔ f (ProjectivePlane.vector a (ProjectivePlane.coordinates a p)) = 0 := by
  conv_lhs => rw [← ProjectivePlane.param_coordinates a p hp]
  exact lineZero_mk f _ _

/-- Each actual equation is nonzero; the three Q equations join precisely the
named pairs of centres, not arbitrary suggestively named lines. -/
theorem named_projective_lines :
    ellForm ≠ 0 ∧ (∀ k, qForm k ≠ 0) ∧
      ∀ k : Fin 3, centre k.castSucc 0 ∈ lineZero (qForm k) ∧
        centre 3 0 ∈ lineZero (qForm k) := by
  refine ⟨?_,?_,?_⟩
  · intro h
    have he := congrArg (fun f : (Fin 3 → ℂ) →ₗ[ℂ] ℂ => f ![0,0,1]) h
    change (1:ℂ) = 0 at he
    exact one_ne_zero he
  · intro k h
    have he := congrArg (fun f : (Fin 3 → ℂ) →ₗ[ℂ] ℂ => f ![1,2,0]) h
    fin_cases k <;> norm_num [qForm] at he
  · intro k
    rw [← centre_mk k.castSucc 0,← centre_mk 3 0,lineZero_mk,lineZero_mk]
    fin_cases k <;> simp [qForm,centreVector,Coordinates.p₁,Coordinates.p₂,
      Coordinates.p₃,Coordinates.p₄]

private theorem zero_away_numerator {a c : ℤ} {b d : Fin 4 → ℤ}
    (D : WeightedDivisionData a c b d) (p : Fiber 0) (hp : p ∈ FixedFiber.awayCentres 0)
    (i : Index) (hi : p ∈ baseSet 0 i) :
    sectionValue D.quotientSection p = 0 ↔ D.numerator.coefficient i p = 0 := by
  rw [sectionValue_zero_iff D.quotientSection i p hi,← D.quotientSection_division i p hi]
  simp only [mul_eq_zero,D.denominator_ne_zero p hp i hi,or_false]

theorem ell_away_equation (p : Fiber 0) (hp : p ∈ FixedFiber.awayCentres 0) :
    sectionValue ellSection p = 0 ↔ FixedFiber.blowdown 0 p ∈ lineZero ellForm := by
  let i := (core 0 (-2) ellDegree).indexAt p
  have hi := (core 0 (-2) ellDegree).mem_baseSet_at p
  change sectionValue ellDivisionData.quotientSection p = 0 ↔ _
  rw [zero_away_numerator ellDivisionData p hp i hi,lineZero_normalized ellForm i.1 (FixedFiber.blowdown 0 p) hi.1]
  rfl

theorem Q_away_equations (p : Fiber 0) (hp : p ∈ FixedFiber.awayCentres 0) :
    sectionValue qSection p = 0 ↔
      FixedFiber.blowdown 0 p ∈ lineZero (qForm 0) ∨
      FixedFiber.blowdown 0 p ∈ lineZero (qForm 1) ∨
      FixedFiber.blowdown 0 p ∈ lineZero (qForm 2) := by
  let i := (core 0 (-3) qDegree).indexAt p
  have hi := (core 0 (-3) qDegree).mem_baseSet_at p
  change sectionValue qDivisionData.quotientSection p = 0 ↔ _
  rw [zero_away_numerator qDivisionData p hp i hi,
    lineZero_normalized (qForm 0) i.1 (FixedFiber.blowdown 0 p) hi.1,
    lineZero_normalized (qForm 1) i.1 (FixedFiber.blowdown 0 p) hi.1,
    lineZero_normalized (qForm 2) i.1 (FixedFiber.blowdown 0 p) hi.1]
  let v := ProjectivePlane.vector i.1 (ProjectivePlane.coordinates i.1 (FixedFiber.blowdown 0 p))
  change Cubics.g₄ (v 0) (v 1) (v 2) = 0 ↔ _
  simp [v,Cubics.g₄,qForm,mul_eq_zero,or_assoc,or_left_comm]

/-- A zero on the exceptional radial origin is approached by zeros at nonzero
radial parameters. The open-domain condition ensures these are actual points. -/
private theorem radial_zeros_dense {a c : ℤ} {b d : Fin 4 → ℤ}
    (D : WeightedDivisionData a c b d)
    (hzero : ∀ r e v, D.localCoefficient r e (0,v) = 0 →
      ∀ u, D.localCoefficient r e (u,v) = 0) :
    {p : Fiber 0 | sectionValue D.quotientSection p = 0} =
      closure ({p : Fiber 0 | sectionValue D.quotientSection p = 0} ∩ FixedFiber.awayCentres 0) := by
  apply Subset.antisymm
  · intro p hp
    obtain ⟨⟨r,e⟩,hc⟩ := FixedFiber.charts_cover 0 p
    let q := FixedFiber.coordinates 0 r e p
    have hq : q ∈ FixedFiber.domain 0 r e := (FixedFiber.chart 0 r e).map_source hc
    have heq : FixedFiber.param 0 r e q = p := FixedFiber.param_coordinates 0 r e p hc
    have hz : D.localCoefficient r e q = 0 :=
      (D.quotientSection_zero_iff_coordinates r e p hc).mp hp
    by_cases hq0 : q.1 = 0
    · apply mem_closure_iff.mpr
      intro U hU hpU
      let W := FixedFiber.domain 0 r e ∩ FixedFiber.param 0 r e ⁻¹' U
      have hW : IsOpen W := (FixedFiber.param_continuousOn 0 r e).isOpen_inter_preimage
        (FixedFiber.domain_isOpen 0 r e) hU
      have h0 : (0,q.2) ∈ W := by
        have hqq : (0,q.2) = q := by ext <;> simp [hq0]
        rw [hqq]
        exact ⟨hq,by change FixedFiber.param 0 r e q ∈ U; rwa [heq]⟩
      obtain ⟨u,hu,hu0⟩ := (dense_compl_singleton (0:ℂ)).inter_open_nonempty _
        (hW.preimage (continuous_id.prodMk (continuous_const (y := q.2)))) ⟨0,h0⟩
      refine ⟨FixedFiber.param 0 r e (u,q.2),hu.2,?_,?_⟩
      · apply (D.quotientSection_zero_iff_param r e (u,q.2) hu.1).mpr
        exact hzero r e q.2 (by simpa [← hq0] using hz) u
      · exact (FixedFiber.param_mem_awayCentres_iff 0 r e (u,q.2) hu.1).mpr hu0
    · apply subset_closure
      refine ⟨hp,?_⟩
      rw [← heq]
      exact (FixedFiber.param_mem_awayCentres_iff 0 r e q hq).mpr hq0
  · exact closure_minimal inter_subset_left (section_zeroSet_isClosed D.quotientSection)

theorem ell_is_literal_strict_transform :
    {p : Fiber 0 | sectionValue ellSection p = 0} = strictTransform ellForm := by
  have hd := radial_zeros_dense ellDivisionData (fun _ _ _ h _ => h)
  calc
    _ = closure ({p : Fiber 0 | sectionValue ellSection p = 0} ∩ FixedFiber.awayCentres 0) := hd
    _ = strictTransform ellForm := by
      apply congrArg closure
      ext p
      exact and_congr_left (fun hp => ell_away_equation p hp)

theorem Q_is_three_literal_strict_transforms :
    {p : Fiber 0 | sectionValue qSection p = 0} =
      strictTransform (qForm 0) ∪ strictTransform (qForm 1) ∪ strictTransform (qForm 2) := by
  have hd := radial_zeros_dense qDivisionData (by
    intro r e v h u
    change qLocalCoefficient r e (0,v) = 0 at h
    change qLocalCoefficient r e (u,v) = 0
    fin_cases r <;> fin_cases e <;> simp [qLocalCoefficient] at h ⊢ <;> simp_all)
  let S (k : Fin 3) := FixedFiber.blowdown 0 ⁻¹' lineZero (qForm k) ∩ FixedFiber.awayCentres 0
  calc
    _ = closure ({p : Fiber 0 | sectionValue qSection p = 0} ∩ FixedFiber.awayCentres 0) := hd
    _ = closure (S 0 ∪ S 1 ∪ S 2) := by
      apply congrArg closure
      ext p
      by_cases hp : p ∈ FixedFiber.awayCentres 0
      · simp only [S,mem_inter_iff,mem_setOf_eq,hp,and_true,mem_union,mem_preimage]
        exact (Q_away_equations p hp).trans (or_assoc.symm)
      · simp [S,hp]
    _ = _ := by rw [closure_union,closure_union]; rfl

/-- The Q section is represented by a genuine local holomorphic equation with
surjective complex derivative, divided by an everywhere nonzero denominator.
This is the reduced multiplicity input, not merely a support equality. -/
theorem Q_reduced_local_equation (p : Fiber 0) (hz : sectionValue qSection p = 0) :
    ∃ d : DivisionIndex, p ∈ divisionPatch 0 d ∧
      (∀ x ∈ divisionPatch 0 d, qDivisionData.otherDenominator d x ≠ 0 ∧
        qSection.coefficient (divisionFrame d) x =
          qLocalCoefficient d.1 d.2.1 (FixedFiber.coordinates 0 d.1 d.2.1 x) /
            qDivisionData.otherDenominator d x) ∧
      Function.Surjective (fderiv ℂ (qLocalCoefficient d.1 d.2.1)
        (FixedFiber.coordinates 0 d.1 d.2.1 p)) := by
  obtain ⟨d,hd⟩ := divisionPatch_cover 0 p
  refine ⟨d,hd,?_,?_⟩
  · intro x hx
    exact ⟨qDivisionData.otherDenominator_ne_zero d x hx,
      qDivisionData.quotientSection_coefficient d x hx⟩
  · apply qLocalCoefficient_fderiv_surjective_at_zero
    exact (qDivisionData.quotientSection_zero_iff_local d p hd).mp hz

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle.PaperStrictTransforms
