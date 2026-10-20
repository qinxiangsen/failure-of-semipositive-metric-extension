import FailureOfSemipositiveMetricExtension.GlobalBlowdownZariskiCharts

/-! The localized affine incidence chart has exactly the coordinate ring of its
base Zariski open. This is a genuine quotient-ring isomorphism and its induced
prime-spectrum homeomorphism, with the equations connected to the original
projective incidence relation. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.BlowdownComplement
noncomputable section
open Set MvPolynomial

abbrev GraphPolynomial (a : Fin 3) (e : Fin 4 → Fin 2) := MvPolynomial (Fin 4) (ChartRing a e)

instance graphPolynomialCommRing (a : Fin 3) (e : Fin 4 → Fin 2) :
    CommRing (GraphPolynomial a e) := inferInstance

def graphRelation (a : Fin 3) (e : Fin 4 → Fin 2) (r : Fin 4) : GraphPolynomial a e :=
  X r - C (localizedDirectionCoordinate a e r)

def graphIdeal (a : Fin 3) (e : Fin 4 → Fin 2) : Ideal (GraphPolynomial a e) :=
  Ideal.span (range (graphRelation a e))

abbrev GraphRing (a : Fin 3) (e : Fin 4 → Fin 2) := GraphPolynomial a e ⧸ graphIdeal a e

def graphEvaluation (a : Fin 3) (e : Fin 4 → Fin 2) : GraphPolynomial a e →+* ChartRing a e :=
  eval (localizedDirectionCoordinate a e)

theorem graphIdeal_le_kernel (a : Fin 3) (e : Fin 4 → Fin 2) :
    graphIdeal a e ≤ RingHom.ker (graphEvaluation a e) := by
  apply Ideal.span_le.mpr
  rintro _ ⟨r,rfl⟩
  change graphEvaluation a e (graphRelation a e r) = 0
  simp [graphEvaluation,graphRelation]

def graphToBase (a : Fin 3) (e : Fin 4 → Fin 2) : GraphRing a e →+* ChartRing a e :=
  Ideal.Quotient.lift (graphIdeal a e) (graphEvaluation a e) (fun _ h => graphIdeal_le_kernel a e h)

def baseToGraph (a : Fin 3) (e : Fin 4 → Fin 2) : ChartRing a e →+* GraphRing a e :=
  (Ideal.Quotient.mk (graphIdeal a e)).comp C

@[simp] theorem graphToBase_mk (a : Fin 3) (e : Fin 4 → Fin 2) (p : GraphPolynomial a e) :
    graphToBase a e (Ideal.Quotient.mk (graphIdeal a e) p) = graphEvaluation a e p := rfl

@[simp] theorem graphToBase_baseToGraph (a : Fin 3) (e : Fin 4 → Fin 2) (c : ChartRing a e) :
    graphToBase a e (baseToGraph a e c) = c := by
  change eval (localizedDirectionCoordinate a e) (C c) = c
  simp

theorem graph_mk_X (a : Fin 3) (e : Fin 4 → Fin 2) (r : Fin 4) :
    Ideal.Quotient.mk (graphIdeal a e) (X r) =
      baseToGraph a e (localizedDirectionCoordinate a e r) := by
  have h : graphRelation a e r ∈ graphIdeal a e := Ideal.subset_span ⟨r,rfl⟩
  have hz := (Ideal.Quotient.eq_zero_iff_mem).mpr h
  simpa only [graphRelation,map_sub,sub_eq_zero,baseToGraph,RingHom.comp_apply] using hz

theorem baseToGraph_graphToBase (a : Fin 3) (e : Fin 4 → Fin 2) (p : GraphRing a e) :
    baseToGraph a e (graphToBase a e p) = p := by
  have hhom : ((baseToGraph a e).comp (graphToBase a e)).comp
      (Ideal.Quotient.mk (graphIdeal a e)) = Ideal.Quotient.mk (graphIdeal a e) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [baseToGraph,graphToBase,graphEvaluation]
    · intro r
      simpa [graphEvaluation] using (graph_mk_X a e r).symm
  obtain ⟨f,rfl⟩ := Ideal.Quotient.mk_surjective p
  exact RingHom.congr_fun hhom f

/-- A verified two-sided isomorphism of the actual affine coordinate rings. -/
def graphRingEquiv (a : Fin 3) (e : Fin 4 → Fin 2) : GraphRing a e ≃+* ChartRing a e :=
  RingEquiv.ofHomInv (graphToBase a e) (baseToGraph a e)
    (RingHom.ext (baseToGraph_graphToBase a e)) (RingHom.ext (graphToBase_baseToGraph a e))

/-- The corresponding homeomorphism for mathlib's actual Zariski topologies. -/
def graphSpectrumHomeomorph (a : Fin 3) (e : Fin 4 → Fin 2) :
    PrimeSpectrum (GraphRing a e) ≃ₜ PrimeSpectrum (ChartRing a e) :=
  PrimeSpectrum.homeomorphOfRingEquiv (graphRingEquiv a e)

/-- The original affine incidence equations after localization and direction normalization. -/
def dehomogenizedEquation (a : Fin 3) (e : Fin 4 → Fin 2) (r : Fin 4) : GraphPolynomial a e :=
  C (algebraMap AffinePolynomial (ChartRing a e) (affinePair a r (e r))) * X r -
    C (algebraMap AffinePolynomial (ChartRing a e) (affinePair a r (e r).rev))

theorem dehomogenizedEquation_eq_unit_mul (a : Fin 3) (e : Fin 4 → Fin 2) (r : Fin 4) :
    dehomogenizedEquation a e r =
      C (algebraMap AffinePolynomial (ChartRing a e) (affinePair a r (e r))) * graphRelation a e r := by
  have h := localizedDirectionCoordinate_mul_denominator a e r
  rw [mul_comm] at h
  unfold dehomogenizedEquation graphRelation
  rw [_root_.mul_sub,← map_mul,h]

def incidenceChartIdeal (a : Fin 3) (e : Fin 4 → Fin 2) : Ideal (GraphPolynomial a e) :=
  Ideal.span (range (dehomogenizedEquation a e))

/-- Dividing these equations by their proved unit coefficients does not change the ideal. -/
theorem incidenceChartIdeal_eq_graphIdeal (a : Fin 3) (e : Fin 4 → Fin 2) :
    incidenceChartIdeal a e = graphIdeal a e := by
  apply le_antisymm
  · apply Ideal.span_le.mpr
    rintro _ ⟨r,rfl⟩
    rw [dehomogenizedEquation_eq_unit_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨r,rfl⟩)
  · apply Ideal.span_le.mpr
    rintro _ ⟨r,rfl⟩
    have hu : IsUnit (C (algebraMap AffinePolynomial (ChartRing a e) (affinePair a r (e r))) :
        GraphPolynomial a e) := (denominator_isUnit a e r).map C
    have h := (Ideal.subset_span (show dehomogenizedEquation a e r ∈ range (dehomogenizedEquation a e)
      from ⟨r,rfl⟩) : dehomogenizedEquation a e r ∈ incidenceChartIdeal a e)
    rw [dehomogenizedEquation_eq_unit_mul] at h
    obtain ⟨u,hu⟩ := hu
    rw [← hu] at h
    have hh := Ideal.mul_mem_left (incidenceChartIdeal a e) (↑u⁻¹) h
    simpa only [← mul_assoc,Units.inv_mul,one_mul] using hh

/-- The quotient by the original dehomogenized incidence equations is the
actual localization of the affine base ring. -/
def incidenceChartRingEquiv (a : Fin 3) (e : Fin 4 → Fin 2) :
    GraphPolynomial a e ⧸ incidenceChartIdeal a e ≃+* ChartRing a e :=
  (Ideal.quotEquivOfEq (incidenceChartIdeal_eq_graphIdeal a e)).trans (graphRingEquiv a e)

/-- Exact incidence equation in complex chart coordinates; the sign is fixed
uniformly by multiplying the selected component by the slope. -/
theorem incidence_affine_direction_iff (a : Fin 3) (r : Fin 4) (e : Fin 2)
    (q : ℂ × ℂ) (t s : ℂ) :
    Incidence (ProjectivePlane.param a q) (ProjectiveLine.param e s) r t ↔
      eval ![q.1,q.2,t] (affinePair a r e) * s -
        eval ![q.1,q.2,t] (affinePair a r e.rev) = 0 := by
  rw [ProjectivePlane.param,incidence_mk_iff]
  simp only [affinePair_eval]
  fin_cases e
  · change _ ∈ (Blowup.lineX s).submodule ↔ _
    rw [ProjectiveIncidence.mem_lineX_iff]
    exact eq_comm.trans sub_eq_zero.symm
  · change _ ∈ (Blowup.lineY s).submodule ↔ _
    rw [ProjectiveIncidence.mem_lineY_iff]
    exact eq_comm.trans sub_eq_zero.symm

/-- Evaluation of the actual localized polynomial is the original incidence
condition, without replacing the total space or its projective coordinates. -/
theorem incidence_iff_localized_equation_zero (a : Fin 3) (e : Fin 4 → Fin 2) (r : Fin 4)
    (q : ℂ × ℂ) (t : ℂ) (s : Fin 4 → ℂ)
    (hq : evaluationPoint ![q.1,q.2,t] ∈ zariskiChart a e) :
    Incidence (ProjectivePlane.param a q) (ProjectiveLine.param (e r) (s r)) r t ↔
      eval₂ (evaluateChartRing a e ![q.1,q.2,t] hq) s (dehomogenizedEquation a e r) = 0 := by
  rw [incidence_affine_direction_iff]
  simp [dehomogenizedEquation,evaluateChartRing_algebraMap]

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.BlowdownComplement
