import FailureOfSemipositiveMetricExtension.RelativeProjectiveFunctorPoints
import FailureOfSemipositiveMetricExtension.FieldPointClosedSubscheme

/-! Genuine field-valued morphisms into the global incidence scheme, with
compatibility with its relative parameter and the original complex points. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.RelativeSegre
noncomputable section
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial Set HomogeneousLocalization

/-- The actual complex-valued point of the parameter affine line. -/
def parameterFunctorPoint (t : ℂ) : complexScheme ⟶ parameterScheme :=
  Spec.map (CommRingCat.ofHom (Polynomial.evalRingHom t))

theorem chartEvaluation_fromZero (t : ℂ) (z : Vector) (p : Index) (hp : z p ≠ 0)
    (c : Coefficient) :
    chartEvaluation t z p hp (fromZeroRingHom grading (Submonoid.powers (X p))
      (coefficientToDegreeZero c)) = Polynomial.eval t c := by
  have h : fromZeroRingHom grading (Submonoid.powers (X p)) (coefficientToDegreeZero c) =
      Away.mk grading (isHomogeneous_X Coefficient p) 0 (C c) (isHomogeneous_C Index c) := by
    apply HomogeneousLocalization.val_injective
    rfl
  rw [h,chartEvaluation_mk]
  simp [evaluate]

/-- Equality of actual scheme morphisms over the parameter, not merely equality
of underlying point maps. -/
theorem projectiveFunctorPoint_projection (t : ℂ) (z : Vector) (p : Index) (hp : z p ≠ 0) :
    projectiveFunctorPoint t z p hp ≫ projectiveProjection = parameterFunctorPoint t := by
  unfold projectiveFunctorPoint projectiveProjection parameterFunctorPoint
  rw [Category.assoc,← Category.assoc (Proj.awayι _ _ _ _),Proj.awayι_toSpecZero]
  rw [← Spec.map_comp,← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (chartEvaluation_fromZero t z p hp)

theorem exists_totalVector_pivot (q : Total) : ∃ p, totalVector q p ≠ 0 := by
  by_contra h
  push_neg at h
  exact totalVector_nonzero q (funext h)

def totalPivot (q : Total) : Index := (exists_totalVector_pivot q).choose

theorem totalPivot_nonzero (q : Total) : totalVector q (totalPivot q) ≠ 0 :=
  (exists_totalVector_pivot q).choose_spec

def totalProjectiveFunctorPoint (q : Total) : complexScheme ⟶ projectiveScheme :=
  projectiveFunctorPoint (projection q) (totalVector q) (totalPivot q) (totalPivot_nonzero q)

theorem totalProjectiveFunctorPoint_base (q : Total) :
    (totalProjectiveFunctorPoint q).base complexFieldPoint = totalPrime q :=
  projectiveFunctorPoint_base _ _ _ _ _

theorem exists_incidenceFunctorPoint (q : Total) :
    ∃ g : complexScheme ⟶ incidenceScheme, g ≫ incidenceInclusion = totalProjectiveFunctorPoint q := by
  apply IdealSheafGluedSubscheme.exists_fieldPoint_lift closedLocus (totalProjectiveFunctorPoint q)
  change (totalProjectiveFunctorPoint q).base complexFieldPoint ∈ closedLocus
  rw [totalProjectiveFunctorPoint_base]
  exact incidenceInclusion_range.le (totalPrime_mem_range q)

/-- Every original analytic point gives a genuine `Spec ℂ`-valued point of the
actual global incidence scheme. -/
def incidenceFunctorPoint (q : Total) : complexScheme ⟶ incidenceScheme :=
  (exists_incidenceFunctorPoint q).choose

@[simp,reassoc] theorem incidenceFunctorPoint_inclusion (q : Total) :
    incidenceFunctorPoint q ≫ incidenceInclusion = totalProjectiveFunctorPoint q :=
  (exists_incidenceFunctorPoint q).choose_spec

@[simp] theorem incidenceFunctorPoint_base (q : Total) :
    (incidenceFunctorPoint q).base complexFieldPoint = toIncidenceScheme q := by
  apply incidenceInclusion_injective
  change (incidenceFunctorPoint q ≫ incidenceInclusion).base complexFieldPoint = _
  rw [incidenceFunctorPoint_inclusion,totalProjectiveFunctorPoint_base,toIncidenceScheme_inclusion]

@[simp,reassoc] theorem incidenceFunctorPoint_projection (q : Total) :
    incidenceFunctorPoint q ≫ incidenceProjection = parameterFunctorPoint (projection q) := by
  rw [incidenceProjection,← Category.assoc,incidenceFunctorPoint_inclusion]
  exact projectiveFunctorPoint_projection _ _ _ _

theorem incidenceFunctorPoint_injective : Function.Injective incidenceFunctorPoint := by
  intro p q h
  apply toIncidenceScheme_injective
  simpa only [incidenceFunctorPoint_base] using congrArg (fun f : complexScheme ⟶ incidenceScheme =>
    f.base complexFieldPoint) h

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.RelativeSegre
