import FailureOfSemipositiveMetricExtension.CentralWeightedDivision

/-! The actual central sections ℓ and Q obtained from z and xy(x-y) by the
specified exceptional division.  Their underlying bundles have verified ambient
multidegrees; no identification with a canonical bundle is assumed here. -/
namespace FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
noncomputable section
open Set Bundle IsManifold
open scoped Manifold ContDiff

def ellMultiplicity (r : Fin 4) : ℕ := if r = 3 then 0 else 1
def qMultiplicity (r : Fin 4) : ℕ := if r = 3 then 3 else 1
def ellDegree (r : Fin 4) : ℤ := ellMultiplicity r
def qDegree (r : Fin 4) : ℤ := qMultiplicity r

def ellHomogeneous : FailureOfSemipositiveMetricExtension.GlobalLineBundle.HomogeneousData 1 where
  value q := q.2 2
  analytic := by fun_prop
  homogeneous t c v := by simp [Pi.smul_apply,smul_eq_mul]

def ellDenominator : SectionData 0 3 (fun r => -ellDegree r) where
  coefficient := (multiplySections (multiplySections (exceptionalSection 0 0)
    (exceptionalSection 0 1)) (exceptionalSection 0 2)).coefficient
  analytic := (multiplySections (multiplySections (exceptionalSection 0 0)
    (exceptionalSection 0 1)) (exceptionalSection 0 2)).analytic
  compatible i j p hp := by
    have h := (multiplySections (multiplySections (exceptionalSection 0 0)
      (exceptionalSection 0 1)) (exceptionalSection 0 2)).compatible i j p hp
    have hb : (fun r => (FailureOfSemipositiveMetricExtension.GlobalLineBundle.exceptionalDegree 0 r +
      FailureOfSemipositiveMetricExtension.GlobalLineBundle.exceptionalDegree 1 r) +
      FailureOfSemipositiveMetricExtension.GlobalLineBundle.exceptionalDegree 2 r) = (fun r => -ellDegree r) := by
      funext r
      fin_cases r <;> decide
    change gain 0 3 _ i j p * _ = _ at h
    conv at h => lhs; arg 1; rw [hb]
    exact h

theorem ellDenominator_coefficient (i : Index) (p : Fiber 0) :
    ellDenominator.coefficient i p = ∏ r, exceptionalCoefficient 0 r i p ^ ellMultiplicity r := by
  change (exceptionalCoefficient 0 0 i p * exceptionalCoefficient 0 1 i p) *
    exceptionalCoefficient 0 2 i p = _
  simp [ellMultiplicity,Fin.prod_univ_succ,mul_assoc]

def qDenominator : SectionData 0 6 (fun r => -qDegree r) where
  coefficient := (multiplySections centralDenominator (exceptionalSection 0 3)).coefficient
  analytic := (multiplySections centralDenominator (exceptionalSection 0 3)).analytic
  compatible i j p hp := by
    have h := (multiplySections centralDenominator (exceptionalSection 0 3)).compatible i j p hp
    have hb : (fun r => -centralADegree r + FailureOfSemipositiveMetricExtension.GlobalLineBundle.exceptionalDegree 3 r) =
        (fun r => -qDegree r) := by
      funext r
      fin_cases r <;> decide
    change gain 0 6 _ i j p * _ = _ at h
    conv at h => lhs; arg 1; rw [hb]
    exact h

theorem qDenominator_coefficient (i : Index) (p : Fiber 0) :
    qDenominator.coefficient i p = ∏ r, exceptionalCoefficient 0 r i p ^ qMultiplicity r := by
  change centralDenominator.coefficient i p * exceptionalCoefficient 0 3 i p = _
  rw [centralDenominator_coefficient]
  simp [centralMultiplicity,qMultiplicity,Fin.prod_univ_succ,pow_succ,mul_assoc]

def ellNumerator : SectionData 0 ((-2:ℤ)+3) (fun r => ellDegree r + -ellDegree r) where
  coefficient := (homogeneousSection 0 ellHomogeneous).coefficient
  analytic := (homogeneousSection 0 ellHomogeneous).analytic
  compatible i j p hp := by convert (homogeneousSection 0 ellHomogeneous).compatible i j p hp using 1

def qNumerator : SectionData 0 ((-3:ℤ)+6) (fun r => qDegree r + -qDegree r) where
  coefficient := (centralCubicSections 3).coefficient
  analytic := (centralCubicSections 3).analytic
  compatible i j p hp := by convert (centralCubicSections 3).compatible i j p hp using 1

def ellLocalCoefficient (r : Fin 4) (e : Fin 2) (q : FixedFiber.Coord) : ℂ :=
  if r = 3 then 1 else if e = 0 then q.2 else 1

def qLocalCoefficient (r : Fin 4) (e : Fin 2) (q : FixedFiber.Coord) : ℂ :=
  match r with
  | 0 => if e = 0 then 1-q.1 else q.2*(1-q.1*q.2)
  | 1 => if e = 0 then q.1-1 else q.2*(q.1*q.2-1)
  | 2 => if e = 0 then -1-q.1 else -q.2-q.1*q.2^2
  | 3 => if e = 0 then q.2*(1-q.2) else q.2*(q.2-1)

theorem ellLocalCoefficient_contDiff (r : Fin 4) (e : Fin 2) :
    ContDiff ℂ ω (ellLocalCoefficient r e) := by
  change ContDiff ℂ ω (fun q => ellLocalCoefficient r e q)
  fin_cases r <;> fin_cases e <;> dsimp [ellLocalCoefficient] <;> fun_prop

theorem qLocalCoefficient_contDiff (r : Fin 4) (e : Fin 2) :
    ContDiff ℂ ω (qLocalCoefficient r e) := by
  change ContDiff ℂ ω (fun q => qLocalCoefficient r e q)
  fin_cases r <;> fin_cases e <;> dsimp [qLocalCoefficient] <;> fun_prop

theorem ell_divided_pullback (r : Fin 4) (e : Fin 2) (q : FixedFiber.Coord) :
    ellHomogeneous.value (0,baseVector r 0 (Blowup.projection (localParam e q))) =
      q.1 ^ ellMultiplicity r * ellLocalCoefficient r e q := by
  fin_cases r <;> fin_cases e <;>
    dsimp [ellHomogeneous,baseVector,localParam,Blowup.projection,Blowup.X,Blowup.Y,
      ellMultiplicity,ellLocalCoefficient] <;> ring

theorem q_divided_pullback (r : Fin 4) (e : Fin 2) (q : FixedFiber.Coord) :
    (FailureOfSemipositiveMetricExtension.GlobalLineBundle.cubicGenerators 3).value
      (0,baseVector r 0 (Blowup.projection (localParam e q))) =
      q.1 ^ qMultiplicity r * qLocalCoefficient r e q := by
  fin_cases r <;> fin_cases e <;>
    dsimp [FailureOfSemipositiveMetricExtension.GlobalLineBundle.cubicGenerators,FailureOfSemipositiveMetricExtension.Cubics.g₄,
      baseVector,localParam,Blowup.projection,Blowup.X,Blowup.Y,qMultiplicity,qLocalCoefficient] <;> ring

def ellDivisionData : WeightedDivisionData (-2) 3 ellDegree (fun r => -ellDegree r) where
  multiplicity := ellMultiplicity
  denominator := ellDenominator
  numerator := ellNumerator
  denominator_coefficient := ellDenominator_coefficient
  localCoefficient := ellLocalCoefficient
  localCoefficient_analytic := ellLocalCoefficient_contDiff
  pullback_identity j q := by
    change (homogeneousSection 0 ellHomogeneous).coefficient _ _ = _
    rw [homogeneousSection_coefficient_param 0 ellHomogeneous j.1 j.2.1 q (divisionFrame j) rfl]
    exact ell_divided_pullback _ _ _

def qDivisionData : WeightedDivisionData (-3) 6 qDegree (fun r => -qDegree r) where
  multiplicity := qMultiplicity
  denominator := qDenominator
  numerator := qNumerator
  denominator_coefficient := qDenominator_coefficient
  localCoefficient := qLocalCoefficient
  localCoefficient_analytic := qLocalCoefficient_contDiff
  pullback_identity j q := by
    change (homogeneousSection 0 (FailureOfSemipositiveMetricExtension.GlobalLineBundle.cubicGenerators 3)).coefficient _ _ = _
    rw [homogeneousSection_coefficient_param 0 _ j.1 j.2.1 q (divisionFrame j) rfl]
    exact q_divided_pullback _ _ _

/-- The genuine analytic section ℓ of multidegree (-2;1,1,1,0). -/
def ellSection : SectionData 0 (-2) ellDegree := ellDivisionData.quotientSection

/-- The genuine analytic section Q of multidegree (-3;1,1,1,3). -/
def qSection : SectionData 0 (-3) qDegree := qDivisionData.quotientSection

theorem ellSection_analytic :
    ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (sectionMap ellSection) := sectionMap_contMDiff _

theorem qSection_analytic :
    ContMDiff 𝓘(ℂ,FixedFiber.Coord) (𝓘(ℂ,FixedFiber.Coord).prod 𝓘(ℂ)) ω
      (sectionMap qSection) := sectionMap_contMDiff _

theorem ellSection_division_sectionMap :
    sectionMap (multiplySections ellSection ellDenominator) = sectionMap ellNumerator :=
  ellDivisionData.quotientSection_division_sectionMap

theorem qSection_division_sectionMap :
    sectionMap (multiplySections qSection qDenominator) = sectionMap qNumerator :=
  qDivisionData.quotientSection_division_sectionMap

end
end FailureOfSemipositiveMetricExtension.GlobalIncidence.FixedFiberBundle
