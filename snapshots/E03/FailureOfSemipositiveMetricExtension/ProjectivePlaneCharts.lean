import FailureOfSemipositiveMetricExtension.ProjectivePoints

/-! The three standard affine charts of the actual complex projective plane.
The definitions and proofs in this file are algebraic: no topology is assumed. -/
noncomputable section

namespace FailureOfSemipositiveMetricExtension.ProjectivePlane

abbrev Point := Projectivization ℂ (Fin 3 → ℂ)

/-- Homogeneous coordinates normalized in the selected standard chart. -/
def vector : Fin 3 → (ℂ × ℂ) → (Fin 3 → ℂ)
  | 0, q => ![1, q.1, q.2]
  | 1, q => ![q.1, 1, q.2]
  | 2, q => ![q.1, q.2, 1]

@[simp] theorem vector_self (i : Fin 3) (q : ℂ × ℂ) : vector i q i = 1 := by
  fin_cases i <;> simp [vector]

theorem vector_nonzero (i : Fin 3) (q : ℂ × ℂ) : vector i q ≠ 0 := by
  intro h
  have hi := congrFun h i
  simp at hi

/-- Standard affine parametrization with values in mathlib's projectivization. -/
def param (i : Fin 3) (q : ℂ × ℂ) : Point :=
  Projectivization.mk ℂ (vector i q) (vector_nonzero i q)

/-- The standard affine-chart subset of the projective plane. -/
def chartSet (i : Fin 3) : Set Point := Set.range (param i)

/-- The source-coordinate domain of the transition from chart `i` to chart `j`. -/
def overlap (i j : Fin 3) : Set (ℂ × ℂ) := {q | vector i q j ≠ 0}

/-- The nine coordinate changes, including the three identity changes. -/
def transition : Fin 3 → Fin 3 → (ℂ × ℂ) → (ℂ × ℂ)
  | 0, 0, q => q
  | 0, 1, q => (q.1⁻¹, q.2 / q.1)
  | 0, 2, q => (q.2⁻¹, q.1 / q.2)
  | 1, 0, q => (q.1⁻¹, q.2 / q.1)
  | 1, 1, q => q
  | 1, 2, q => (q.1 / q.2, q.2⁻¹)
  | 2, 0, q => (q.2 / q.1, q.1⁻¹)
  | 2, 1, q => (q.1 / q.2, q.2⁻¹)
  | 2, 2, q => q

@[simp] theorem transition_self (i : Fin 3) (q : ℂ × ℂ) : transition i i q = q := by
  fin_cases i <;> rfl

@[simp] theorem overlap_self (i : Fin 3) : overlap i i = Set.univ := by
  ext q
  simp [overlap]

@[simp] theorem overlap_zero_one : overlap 0 1 = {q | q.1 ≠ 0} := rfl
@[simp] theorem overlap_zero_two : overlap 0 2 = {q | q.2 ≠ 0} := rfl
@[simp] theorem overlap_one_zero : overlap 1 0 = {q | q.1 ≠ 0} := rfl
@[simp] theorem overlap_one_two : overlap 1 2 = {q | q.2 ≠ 0} := rfl
@[simp] theorem overlap_two_zero : overlap 2 0 = {q | q.1 ≠ 0} := rfl
@[simp] theorem overlap_two_one : overlap 2 1 = {q | q.2 ≠ 0} := rfl

@[simp] theorem transition_zero_one (q : ℂ × ℂ) :
    transition 0 1 q = (q.1⁻¹, q.2 / q.1) := rfl
@[simp] theorem transition_zero_two (q : ℂ × ℂ) :
    transition 0 2 q = (q.2⁻¹, q.1 / q.2) := rfl
@[simp] theorem transition_one_zero (q : ℂ × ℂ) :
    transition 1 0 q = (q.1⁻¹, q.2 / q.1) := rfl
@[simp] theorem transition_one_two (q : ℂ × ℂ) :
    transition 1 2 q = (q.1 / q.2, q.2⁻¹) := rfl
@[simp] theorem transition_two_zero (q : ℂ × ℂ) :
    transition 2 0 q = (q.2 / q.1, q.1⁻¹) := rfl
@[simp] theorem transition_two_one (q : ℂ × ℂ) :
    transition 2 1 q = (q.1 / q.2, q.2⁻¹) := rfl

/-- Normalized homogeneous coordinates uniquely determine affine coordinates. -/
theorem vector_injective (i : Fin 3) : Function.Injective (vector i) := by
  intro q r h
  apply Prod.ext
  · fin_cases i
    · exact congrFun h 1
    · exact congrFun h 0
    · exact congrFun h 0
  · fin_cases i
    · exact congrFun h 2
    · exact congrFun h 2
    · exact congrFun h 1

theorem param_injective (i : Fin 3) : Function.Injective (param i) := by
  intro q r h
  rcases (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h with ⟨a, ha⟩
  have ha1 : a = 1 := by
    have hi := congrFun ha i
    simpa using hi
  apply vector_injective i
  simpa [ha1] using ha.symm

/-- Equal projective points have reciprocal normalized cross-coordinates. -/
theorem cross_ratio_eq_one (i j : Fin 3) (q q' : ℂ × ℂ)
    (h : param i q = param j q') : vector i q j * vector j q' i = 1 := by
  rcases (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp h with ⟨a, ha⟩
  have hj : a = vector i q j := by simpa using congrFun ha j
  simpa only [Pi.smul_apply, smul_eq_mul, vector_self, hj] using congrFun ha i

/-- The normalization identity underlying every coordinate transition. -/
theorem vector_transition (i j : Fin 3) (q : ℂ × ℂ) (hq : q ∈ overlap i j) :
    (vector i q j) • vector j (transition i j q) = vector i q := by
  fin_cases i <;> fin_cases j <;> simp [overlap, vector, transition] at hq ⊢
  all_goals
    ext k
    fin_cases k <;> simp <;> field_simp [hq]


/-- Coordinate change preserves the point of the actual projective quotient. -/
theorem param_transition (i j : Fin 3) (q : ℂ × ℂ) (hq : q ∈ overlap i j) :
    param i q = param j (transition i j q) := by
  apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
  exact ⟨vector i q j, vector_transition i j q hq⟩

/-- Affine coordinates obtained by dividing by the selected homogeneous coordinate. -/
def normalize : Fin 3 → (Fin 3 → ℂ) → (ℂ × ℂ)
  | 0, v => (v 1 / v 0, v 2 / v 0)
  | 1, v => (v 0 / v 1, v 2 / v 1)
  | 2, v => (v 0 / v 2, v 1 / v 2)

theorem vector_normalize (i : Fin 3) (v : Fin 3 → ℂ) (hi : v i ≠ 0) :
    (v i) • vector i (normalize i v) = v := by
  fin_cases i <;> dsimp at hi <;> ext k <;> fin_cases k <;>
    simp [vector, normalize] <;> field_simp [hi]


/-- Every projective point belongs to one of the three standard affine charts. -/
theorem charts_cover (p : Point) : ∃ i q, p = param i q := by
  induction p using Projectivization.ind with
  | h v hv =>
    have hex : ∃ i, v i ≠ 0 := by
      by_contra h
      apply hv
      ext i
      simpa using not_exists.mp h i
    obtain ⟨i, hi⟩ := hex
    refine ⟨i, normalize i v, ?_⟩
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    exact ⟨v i, vector_normalize i v hi⟩

/-- The algebraic overlap criterion: the target homogeneous coordinate is nonzero. -/
theorem param_mem_chartSet_iff (i j : Fin 3) (q : ℂ × ℂ) :
    param i q ∈ chartSet j ↔ q ∈ overlap i j := by
  constructor
  · rintro ⟨r, hr⟩
    rcases (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp hr with ⟨a, ha⟩
    change vector i q j ≠ 0
    intro hj
    have h := congrFun ha j
    simp [hj] at h
  · intro hq
    exact ⟨transition i j q, (param_transition i j q hq).symm⟩

/-- The point specified by an affine coordinate always lies in its chart. -/
theorem param_mem_chartSet (i : Fin 3) (q : ℂ × ℂ) : param i q ∈ chartSet i :=
  ⟨q, rfl⟩

/-- Standard affine-chart membership is the nonvanishing of a representative coordinate. -/
theorem mk_mem_chartSet_iff (i : Fin 3) (v : Fin 3 → ℂ) (hv : v ≠ 0) :
    Projectivization.mk ℂ v hv ∈ chartSet i ↔ v i ≠ 0 := by
  constructor
  · rintro ⟨q, hq⟩ hi
    rcases (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mp hq with ⟨a, ha⟩
    have h := congrFun ha i
    simp [hi] at h
  · intro hi
    refine ⟨normalize i v, ?_⟩
    symm
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).mpr
    exact ⟨v i, vector_normalize i v hi⟩

/-- A valid coordinate change lands in the inverse-overlap domain. -/
theorem transition_mem_overlap (i j : Fin 3) (q : ℂ × ℂ)
    (hq : q ∈ overlap i j) : transition i j q ∈ overlap j i := by
  rw [← param_mem_chartSet_iff, ← param_transition i j q hq]
  exact param_mem_chartSet i q

/-- Coordinate changes in opposite directions are inverse on their overlap domains. -/
theorem transition_inverse (i j : Fin 3) (q : ℂ × ℂ)
    (hq : q ∈ overlap i j) : transition j i (transition i j q) = q := by
  apply param_injective i
  calc
    param i (transition j i (transition i j q)) = param j (transition i j q) :=
      (param_transition j i _ (transition_mem_overlap i j q hq)).symm
    _ = param i q := (param_transition i j q hq).symm

/-- Membership in a third chart is preserved under a valid change of coordinates. -/
theorem transition_mem_overlap_iff (i j k : Fin 3) (q : ℂ × ℂ)
    (hq : q ∈ overlap i j) :
    transition i j q ∈ overlap j k ↔ q ∈ overlap i k := by
  rw [← param_mem_chartSet_iff, ← param_mem_chartSet_iff,
    ← param_transition i j q hq]

/-- The standard coordinate changes obey the cocycle identity on triple overlaps. -/
theorem transition_cocycle (i j k : Fin 3) (q : ℂ × ℂ)
    (hij : q ∈ overlap i j) (hik : q ∈ overlap i k) :
    transition j k (transition i j q) = transition i k q := by
  apply param_injective k
  calc
    param k (transition j k (transition i j q)) = param j (transition i j q) :=
      (param_transition j k _ ((transition_mem_overlap_iff i j k q hij).mpr hik)).symm
    _ = param i q := (param_transition i j q hij).symm
    _ = param k (transition i k q) := param_transition i k q hik

/-- The three standard chart subsets cover all of complex projective two-space. -/
theorem iUnion_chartSet : (⋃ i, chartSet i) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro p
  obtain ⟨i, q, rfl⟩ := charts_cover p
  exact Set.mem_iUnion.mpr ⟨i, param_mem_chartSet i q⟩

end FailureOfSemipositiveMetricExtension.ProjectivePlane
